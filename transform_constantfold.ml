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
  let module Env = Eval.Env in
  let module Heap = Eval.Heap in
  let module Approx = struct
    type 'a approx = 'a option
    type value = Instr.value
    type cell = value approx array
    type env = value approx Env.t
    type heap = cell approx Heap.t

    type state = { env : env; heap : heap; }

    let rec equal_ eq a1 a2 = match a1, a2 with
      | None, Some _ | Some _, None -> false
      | None, None -> true
      | Some v1, Some v2 -> eq v1 v2

    let equal_value_approx = equal_ Eval.value_eq
    let equal_cell_approx = equal_ (fun a1 a2 ->
        if Array.length a1 <> Array.length a2 then false
        else
          try
            for i = 0 to Array.length a1 - 1 do
              if not (equal_value_approx a1.(i) a2.(i)) then raise Exit
            done; true
          with Exit -> false
      )

    let equal_env = Env.equal equal_value_approx
    let equal_heap = Heap.equal equal_cell_approx

    let equal_state s1 s2 =
      equal_env s1.env s2.env
      && equal_heap s1.heap s2.heap

    let merge_ merge m1 m2 = match m1, m2 with
      | None, _ | _, None -> None
      | Some v1, Some v2 -> merge v1 v2

    let merge_value_approx = merge_ (fun v1 v2 ->
        if Eval.value_eq v1 v2 then Some v1 else None)

    let merge_cell_approx = merge_ (fun a1 a2 ->
        if Array.length a1 <> Array.length a2 then None
        else Some (Array.mapi (fun i _ -> merge_value_approx a1.(i) a2.(i)) a1))

    let join = function
      | None -> None
      | Some v -> v

    let merge_env =
      Env.merge (fun _k m1 m2 -> Some (merge_value_approx (join m1) (join m2)))

    let merge_heap =
      Heap.merge (fun _k a1 a2 -> Some (merge_cell_approx (join a1) (join a2)))

    let merge_state s1 s2 = {
      heap = merge_heap s1.heap s2.heap;
      env = merge_env s1.env s2.env;
    }

    let array_approx x heap env = match Env.find x env with
      | exception _ -> None
      | None -> None
      | Some (Array a) ->
        begin match Heap.find a heap with
          | exception _ -> None
          | approx -> approx
        end
      | Some (Nil | Int _ | Bool _ | Fun_ref _) -> None

    include struct
      let pr = Printf.bprintf

      let output_approx output buf = function
        | None -> pr buf "?"
        | Some v -> output buf v

      let output_value buf v =
        pr buf "%s" (IO.string_of_value v)

      let output_cell buf =
        pr buf "[%a]"
          (fun buf -> Array.iter (pr buf "%a " (output_approx output_value)))

      let output_heap buf =
        Heap.iter (fun k v ->
            pr buf "%d:%a " (k :> int) (output_approx output_cell) v)

      let output_env buf =
        Env.iter (fun k v ->
            pr buf "%s:%a " k (output_approx output_value) v)

      let output buf {heap; env} =
        pr buf "HEAP:%a\nENV:%a\n%!" output_heap heap output_env env
    end
  end in

  let lookup x env = try Env.find x env with Not_found -> None in

  (* constant-fold by evaluating expressions
     that become closed after approximation-environment substitution *)
  let fold ~fold_array Approx.{heap; env} = object (self)
    inherit Instr.map as super

    method array_opts exp = match[@warning "-4"] exp with
      | Array_index (x, e) ->
        begin match[@warning "-4"]
                     Approx.array_approx x heap env,
                   self#simple_expression e
          with
          | Some cell, Constant (Int n) ->
            begin match cell.(n) with
            | exception _ -> exp
            | None -> exp
            | Some v -> Simple (Constant v)
            end
          | _, _ -> exp
        end
      | Array_length (Var x) ->
        begin match Approx.array_approx x heap env with
          | Some cell -> Simple (Constant (Int (Array.length cell)))
          | None -> exp
        end
      | _ -> exp

    method try_eval_closed exp =
      let all_propagated = ref true in
      let propagate x e =
        match lookup x env with
        | None -> all_propagated := false; e
        | Some v -> (Edit.replace_var x (Constant v))#expression e
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
          | Constant v -> Some v
          | Var x -> lookup x env
        in
        begin match approx e1, approx e2 with
        | None, _ | _, None -> exp
        | Some v1, Some v2 ->
          match v1, v2 with
          | Array _, (Nil | Bool _ | Int _ | Fun_ref _)
          | (Nil | Bool _ | Int _ | Fun_ref _), Array _
            -> Simple (Constant (Bool (op <> Eq)))
          | _, _ ->
            (* closed cases are optimized in eval_closed *)
            exp
        end
      | exp -> exp

    method! simple_expression = function
      | Constant v -> Constant v
      | Var x ->
        begin match lookup x env with
          | None -> Var x
          | Some v -> Constant v
        end

    (* having Array value inlined in the source means that the
       resulting code cannot be printed and executed back; after all
       optimizations have been performed, we look at whether an Array
       value appeared in the result without beeing eliminated by
       further simplifications, and de-optimize in that case. *)

    method avoid_array_values initial_exp exp =
      let exit_on_array_value = object
        inherit Instr.map as super
        method! value = function
          | Array _ -> raise Exit
          | v -> super#value v
      end in
      if fold_array then exp
      else begin
        try ignore (exit_on_array_value#expression exp); exp
        with Exit -> initial_exp
      end

    method! expression exp =
      exp
      |> self#try_eval_closed
      |> self#array_opts
      |> self#approximate_equalities
      |> self#avoid_array_values exp
  end in

  (* for each instruction, what is the set of variables that are constant? *)
  let constants =
    let open Analysis in
    let open Approx in

    let merge pc cur incom =
      if Approx.equal_state cur incom then None
      else Some (Approx.merge_state cur incom)
    in

    let approx state exp = match (fold ~fold_array:true state)#expression exp with
      | Simple (Constant l) -> Some l
      | Simple (Var x) -> (try Env.find x state.env with Not_found -> None)
      | Unop _ | Binop _ | Array_index _ | Array_length _ -> None
    in
    let approx_array_decl state = function
      | Instr.Length e ->
        begin match approx state e with
          | Some (Int n) ->
            let a = Address.fresh () in
            let block : Approx.cell = Array.make n (Some Nil) in
            let heap = Heap.add a (Some block) state.heap in
            { state with heap }, Some (Array a)
          | Some _ | None ->
            state, None
        end
      | Instr.List es ->
        let a = Address.fresh () in
        let block : Approx.cell = Array.of_list (List.map (approx state) es) in
        let heap = Heap.add a (Some block) state.heap in
        { state with heap }, Some (Array a)
    in

    let update pc cur =
      begin
        let buf = Buffer.create 42 in
        Printf.bprintf buf "UPDATE:%d %t%a%!" pc
          (fun buf -> Disasm.disassemble_instrs buf [| instrs.(pc) |])
          Approx.output cur;
        Buffer.output_buffer stderr buf; flush stderr;
      end;
      match[@warning "-4"] instrs.(pc) with
      | Decl_var (x, e)
      | Assign (x, e) ->
        let env = Env.add x (approx cur e) cur.env in
        { cur with env }
      | Decl_array (x, decl) ->
        let cur, value = approx_array_decl cur decl in
        let env = Env.add x value cur.env in
        { cur with env }
      | Call (x, _, _) as call ->
        let mark_unknown x env = Env.add x None env in
        let env =
          cur.env
          |> VarSet.fold mark_unknown (changed_vars call)
          |> mark_unknown x in
        { cur with env }
      | Drop x ->
        { cur with env = Env.remove x cur.env }
      | Read x ->
        { cur with env = Env.add x None cur.env }
      | Array_assign (x, idx, e) ->
        let x_approx = try Env.find x cur.env with Not_found -> None in
        begin match x_approx with
          | None ->
            (* if we have no idea what heap cell may have been written
               to, we must assume (because of aliasing) that any heap
               cell may have been written. *)
            let heap = Heap.map (fun _ -> None) cur.heap in
            { cur with heap }
          | Some (Nil | Int _ | Bool _ | Fun_ref _) ->
            cur
          | Some (Array a) ->
            begin match Heap.find a cur.heap with
              | exception Not_found -> cur
              | None -> cur
              | Some blocks ->
                begin match approx cur idx with
                  | Some (Int n) ->
                    let blocks' = Array.copy blocks in
                    begin try blocks'.(n) <- approx cur e with _ -> () end;
                    let heap = Heap.add a (Some blocks') cur.heap in
                    { cur with heap }
                  | Some (Nil | Bool _ | Fun_ref _ | Array _) ->
                    cur
                  | None ->
                    let blocks' = Array.map (fun _ -> None) blocks in
                    let heap = Heap.add a (Some blocks') cur.heap in
                    { cur with heap }
                end
            end
        end
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
      let add_formal x st = Env.add x None st in
      let heap = Heap.empty in
      let env = VarSet.fold add_formal formals Env.empty in
      { heap; env }
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
                let e_opt = (fold ~fold_array:true new_state)#expression e in
                (* if e <> e_opt then  *)prerr_endline
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
       | None ->
         let env, heap = Env.empty, Heap.empty in
         { env; heap }
       | Some env -> env)
  in
(*
  let indirect_array state = object (self)
    inherit Instr.map as super

    method! simple_expression simple_exp = match simple_exp with
      | Var _ | Constant (Nil | Int _ | Bool _ | Fun_ref _) -> simple_exp
      | Constant (Array a) ->
        (* We cannot materialize arrays in source code,
           as the heap location is execution-dependent.

           Instead, look in the static environment for a path to this
           array value, and use this in the source code. We fail if
           a path does not exist.
        *)
        let exception Found of Instr.expression in
        let look x = function
          | Some (Array b) ->
            if Address.equal a b then raise (Found (Var x))
        let is_path x x_approx = Approx.equal_value_approx (Some (Array a)) x_approx in
        let paths = Env.filter is_path state.Approx.env in
        if Env.is_empty paths then simple_exp
        else begin
          let (x, _approx) = Env.choose paths in
          Var x
        end
  end in
*)


  let transform_instr pc instr =
    let state = constants pc in
    instr
    |> (fold ~fold_array:false state)#instruction in

  begin
    let buf = Buffer.create 42 in
    Disasm.disassemble_instrs buf ~format_pc:Disasm.line_number instrs;
    Buffer.output_buffer stderr buf; flush stderr
  end;

  let new_instrs = Array.mapi transform_instr instrs in
  if new_instrs = instrs
  then None
  else Some new_instrs
