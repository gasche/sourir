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
    type t = Unknown | Value of value | Array of t array
    let rec equal a1 a2 = match a1, a2 with
      | Unknown, Unknown -> true
      | Unknown, _ | _, Unknown -> false
      | Value v1, Value v2 -> Eval.value_eq v1 v2
      | Value _, _ | _, Value _ -> false
      | Array v1s, Array v2s ->
        if Array.length v1s <> Array.length v2s then false
        else begin
          try
            for i = 0 to Array.length v1s - 1 do
              if not (equal v1s.(i) v2s.(i)) then raise Exit
            done; true
          with Exit -> false
        end

    let rec merge ap1 ap2 = match ap1, ap2 with
      | Value v1, Value v2 ->
        if Eval.value_eq v1 v2 then Value v1 else Unknown
      | Array ap1s, Array ap2s ->
        if Array.length ap1s <> Array.length ap2s then Unknown
        else Array (Array.mapi (fun i _ -> merge ap1s.(i) ap2s.(i)) ap1s)
      | Value _, Array _ | Array _, Value _ -> Unknown
      | Unknown, _ | _, Unknown -> Unknown
  end in

  let lookup x env = try VarMap.find x env with Not_found -> Approx.Unknown in

  (* constant-fold by evaluating expressions
     that become closed after approximation-environment substitution *)
  let fold env = object (self)
    inherit Instr.map as super

    method array_opts exp = match[@warning "-4"] exp with
      | Array_index (x, e) ->
        begin match[@warning "-4"] lookup x env, self#simple_expression e with
          | Approx.Array approxs, Constant (Int n) ->
            begin match approxs.(n) with
            | exception _ -> exp
            | Approx.Value v -> Simple (Constant v)
            | Approx.Array _ | Approx.Unknown -> exp
            end
          | _, _ -> exp
        end
      | Array_length (Var x) ->
        begin match lookup x env with
          | Approx.Array approxs -> Simple (Constant (Int (Array.length approxs)))
          | Approx.Value _ | Approx.Unknown -> exp
        end
      | _ -> exp

    method try_eval_closed exp =
      let all_propagated = ref true in
      let propagate x e =
        match lookup x env with
        | Approx.Unknown | Approx.Array _ -> all_propagated := false; e
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

    method approximate_equalities = function
      | Binop ((Eq | Neq) as op, e1, e2) as exp ->
        let open Approx in
        let approx se = match self#simple_expression se with
          | Constant v -> Value v
          | Var x -> lookup x env
        in
        begin match approx e1, approx e2 with
        | Unknown, _ | _, Unknown -> exp
        | Value _, Value _ ->
          (* this case will be optimized by try_eval_closed *)
          exp
        | Value (Array _), Array _
        | Array _, Value (Array _)
        | Array _, Array _
          -> exp
        | Array _, Value (Nil | Bool _ | Int _ | Fun_ref _)
        | Value (Nil | Bool _ | Int _ | Fun_ref _), Array _
          -> Simple (Constant (Bool (op <> Eq)))
        end
      | exp -> exp

    method! simple_expression = function
      | Constant v -> Constant v
      | Var x ->
        begin match lookup x env with
          | Approx.Unknown -> Var x
          | Approx.Value v -> Constant v
          | Approx.Array _ -> Var x
        end

    method! expression exp =
      exp
      |> self#try_eval_closed
      |> self#array_opts
      |> self#approximate_equalities
  end in

  (* for each instruction, what is the set of variables that are constant? *)
  let constants =
    let open Analysis in
    let open Approx in

    let merge pc cur incom =
      let merge_approx x m1 m2 = match m1, m2 with
        | None, _ | _, None -> None
        | Some ap1, Some ap2 -> Some (Approx.merge ap1 ap2) in
      if VarMap.equal Approx.equal cur incom then None
      else Some (VarMap.merge merge_approx cur incom)
    in

    let approx env exp = match (fold env)#expression exp with
      | Simple (Constant l) -> Value l
      | Simple (Var x) -> lookup x env
      | Unop _ | Binop _ | Array_index _ | Array_length _ -> Unknown
    in
    let approx_array_by_decl env = function
      | Instr.Length e ->
        begin match approx env e with
          | Value (Int n) -> Array (Array.make n (Value Nil))
          | Value _ | Unknown | Array _ -> Unknown
        end
      | Instr.List es ->
        Array (Array.of_list (List.map (approx env) es))
    in

    let update pc cur =
      match[@warning "-4"] instrs.(pc) with
      | Decl_var (x, e)
      | Assign (x, e) ->
        VarMap.add x (approx cur e) cur
      | Decl_array (x, decl) ->
        VarMap.add x (approx_array_by_decl cur decl) cur
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
