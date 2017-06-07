open Instr
open Types

(*
 * Constant folding.
 *
 * This optimization combines constant propagation and constant folding.
 *
 * A variable is constant if
 *   (1) It is defined as `var x = l` where `l` is a literal
 *   (2) It is defined as `var x = op(se)` where `op(se)` is a primop involving
 *       literals or constant variables
 *
 * Then, whenever `x` is used in an expression (while x is still in scope), it
 * is replaced by its constant value. Afterwards, the variable `x` is no longer
 * used, and the declaration can be removed by running `minimize_lifetimes`.
 *)
let const_fold : transform_instructions = fun {formals; instrs} ->
  let module VarMap = Map.Make(Variable) in
  let module Approx = struct
    type t = Unknown | Value of value
    let equal a1 a2 = match a1, a2 with
      | Unknown, Unknown -> true
      | Unknown, Value _ | Value _, Unknown -> false
      | Value v1, Value v2 -> Eval.value_eq v1 v2
  end in

  (* constant-fold by evaluating expressions
     that become closed after approximation-environment substitution *)
  let fold env = object
    inherit Instr.map as super

    method! expression exp =
      let all_propagated = ref true in
      let propagate x e =
        match VarMap.find x env with
        | exception Not_found -> all_propagated := false; e
        | Approx.Unknown -> all_propagated := false; e
        | Approx.Value l -> (Edit.replace_var x (Constant l))#expression e
      in
      let eval_closed exp =
        Eval.eval Eval.Heap.empty Eval.Env.empty exp in
      let exp = VarSet.fold propagate (expr_vars exp) exp in
      if not !all_propagated
      then exp
      else
        (* A closed expression might still fail to evaluate (eg. 1+true) *)
        try Simple (Constant (eval_closed exp)) with
        | _ -> exp
  end in

  (* for each instruction, what is the set of variables that are constant? *)
  let constants =
    let open Analysis in
    let open Approx in

    let merge pc cur incom =
      let merge_approx x mv1 mv2 = match mv1, mv2 with
        | Some Unknown, _ | _, Some Unknown -> Some Unknown
        | Some (Value v1), Some (Value v2) ->
          if Eval.value_eq v1 v2 then Some (Value v1) else Some Unknown
        | None, _ | _, None -> (*BISECT-IGNORE*) failwith "scope error?"
      in
      if VarMap.equal Approx.equal cur incom then None
      else Some (VarMap.merge merge_approx cur incom)
    in

    let update pc cur =
      let approx env exp = match (fold env)#expression exp with
        | Simple (Constant l) -> Value l
        | Simple (Var _)
        | Unop _ | Binop _ | Array_index _ | Array_length _ -> Unknown
      in
      match[@warning "-4"] instrs.(pc) with
      | Decl_var (x, e)
      | Assign (x, e) ->
        VarMap.add x (approx cur e) cur
      | Decl_array (x, _) ->
        (* this case could be improved with approximation for arrays so
           that, eg., length(x) could be constant-folded *)
        VarMap.add x Unknown cur
      | Call (x, _, _) as call ->
        let mark_unknown x cur = VarMap.add x Unknown cur in
        cur
        |> VarSet.fold mark_unknown (changed_vars call)
        |> VarMap.add x Unknown
      | Drop x ->
        VarMap.remove x cur
      | Array_assign (x, _, _) | Read x ->
        assert (VarMap.mem x cur);
        (* the array case could be improved with approximation for
           arrays *)
        VarMap.add x Unknown cur
      | ( Branch _ | Label _ | Goto _ | Return _
        | Print _ | Assert _ | Stop _ | Osr _ | Comment _)
        as instr ->
        begin
          assert (VarSet.is_empty (changed_vars instr));
          assert (VarSet.is_empty (dropped_vars instr));
          assert (VarSet.is_empty (defined_vars instr));
        end;
        cur
    in

    let initial_state =
      let add_formal x st = VarMap.add x Unknown st in
      VarSet.fold add_formal formals VarMap.empty
    in

    let next = Analysis.successors instrs in
    let program_state = Array.map (fun _ -> None) instrs in
    let rec work = function
    | [] -> ()
    | (in_state, pc) :: rest ->
        let merged =
          match program_state.(pc) with
          | None -> Some in_state
          | Some cur_state -> merge pc cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some new_state ->
            program_state.(pc) <- merged;
            let updated = update pc new_state in
            let continue = match instrs.(pc) with
              | Branch (e, l1, l2) ->
                let e_opt = (fold new_state)#expression e in
                if e <> e_opt then prerr_endline
                  (Disasm.disassemble_instrs_s
                     [| Return (Simple (Constant (Int pc)));
                        Return e;
                        Return e_opt |]);
                begin match e_opt with
                  | Simple (Constant (Bool b)) ->
                    [Instr.resolve instrs (BranchLabel (if b then l1 else l2))]
                  | _ -> next.(pc)
                end
              | _ -> next.(pc) in
            let new_work = List.map (fun pc' -> (updated, pc')) continue in
            work (new_work @ rest)
        end
    in
    let starts = Analysis.starts instrs in
    work (List.map (fun pc -> (initial_state, pc)) starts);
    (fun pc ->
       match program_state.(pc) with
       | None -> VarMap.empty
       | Some env -> env)
  in

  let transform_instr pc instr =
    let env = constants pc in
    (fold env)#instruction instr in

  let new_instrs = Array.mapi transform_instr instrs in
  if new_instrs = instrs
  then None
  else Some new_instrs
