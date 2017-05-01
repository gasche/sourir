open Instr

(*
 * Constant folding.
 *
 * This optimization combines constant propagation, copy propagation, and
 * constant folding. We assume the program is well-scoped.
 *
 * The strategy is to maintain a "propagation environment" mapping variables to
 * simple expressions (constants or variables) and apply the `normalize`
 * function to expressions.
 *
 * `normalize` will use the environment to perform as many substitutions as it
 * can. If this results in a new constant definition, then that definition is
 * added to the environment. `drop x` will remove `x` and its mapping from the
 * environment.
 *)
let const_fold (({formals; instrs} as inp) : analysis_input) : instructions option =
  let module Prop_env = Map.Make(Variable) in

  (* Perform constant and copy propagation on the expression `exp`, using
   * the mappings in `penv`.
   * Returns a pair of the updated expression and changed status. *)
  let propagate exp penv =
    let try_prop x (e, c) =
      if Prop_env.mem x penv
      then
        (Edit.replace_var_in_exp x (Prop_env.find x penv) e, true)
      else (e, c || false) in
    VarSet.fold try_prop (expr_vars exp) (exp, false)
  in

  (* Constant fold the expression `exp`.
   * Returns a pair of the updated expression and changed status. *)
  let fold exp =
    match[@warning "-4"] exp with
    | Simple _ -> (exp, false)
    | Op (op, [Constant(v1); Constant(v2)]) ->
      begin match op with
      | Eq -> (Simple (Constant (Bool (Eval.value_eq v1 v2))), true)
      | Neq -> (Simple (Constant (Bool (Eval.value_neq v1 v2))), true)
      | Plus -> (Simple (Constant (Int (Eval.value_plus v1 v2))), true)
      end
    | Op (_, _es) -> (exp, false)
  in

  (* Try to add a new mapping to the environment. `exp` is the simple expression
   * being bound to the constant variable `x`.
   * We need `pc` to infer the scope. *)
  let try_add x exp pc penv =
    match exp with
    | Simple (Constant v) -> Prop_env.add x (Constant v) penv
    | Simple (Var v) ->
      (* We have the declaration `const x = v`. Check if `v` is const or mut.
       * Normally, if `v` is const, at this point it would already be replaced
       * by a constant value. However, if `v` is a const parameter, then we
       * need to do the check here and copy propagate it. *)
      let scope = Scope.infer inp in
      begin match scope.(pc) with
      | DeadScope -> penv
      | Scope scope ->
        try
          (* If `v` is mut, we'll get an `Incomparable` exception. *)
          ignore (ModedVarSet.find (Const_var, v) scope);
          Prop_env.add x (Var v) penv
        with
        | Not_found -> assert(false)
        | Incomparable -> penv
      end
    | Op _ -> penv
  in

  (* Normalize all expressions within the instr at `pc`, given a propagation
   * environment. Perform propagation, then folding.
   * Returns a triple of the new env, new instruction, and changed status. *)
  let normalize pc penv =
    (* Propagate, then fold, keeping track of changed status. *)
    let prop_fold e =
      let (e', changed1) = propagate e penv in
      let (e', changed2) = fold e' in
      (e', changed1 || changed2)
    in
    let instr = instrs.(pc) in
    match instr with
    | Decl_const (x, e) ->
      let (e', changed) = prop_fold e in
      (* Constant declaration, so we might need to update the nevironment. *)
      (try_add x e' pc penv, Decl_const (x, e'), changed)
    | Decl_mut (x, Some e) ->
      let (e', changed) = prop_fold e in
      (penv, Decl_mut (x, Some e'), changed)
    | Call (x, e, args) ->
      let (e', status) = prop_fold e in
      let res = List.map (fun arg ->
        match arg with
        | Arg_by_val e ->
          let (e', status) = prop_fold e in
          (Arg_by_val e', status)
        | Arg_by_ref _ -> (arg, false)) args
      in
      let (args', statuses) = List.split res in
      let changed = List.exists (fun b -> b) (status :: statuses) in
      (penv, Call (x, e', args'), changed)
    | Return e ->
      let (e', changed) = prop_fold e in
      (penv, Return e', changed)
    | Assign (x, e) ->
      let (e', changed) = prop_fold e in
      (penv, Assign (x, e'), changed)
    | Branch (e, l1, l2) ->
      let (e', changed) = prop_fold e in
      (penv, Branch (e', l1, l2), changed)
    | Print e ->
      let (e', changed) = prop_fold e in
      (penv, Print e', changed)
    | Osr (e, tf, tv, tl, osr_env) ->
      let (e', status) = prop_fold e in
      let res = List.map (fun osr_def ->
        match osr_def with
        | Osr_const (y, e) ->
          let (e', status) = prop_fold e in
          (Osr_const (y, e'), status)
        | Osr_mut (y, e) ->
          let (e', status) = prop_fold e in
          (Osr_mut (y, e'), status)
        | Osr_mut_ref _ | Osr_mut_undef _ -> (osr_def, false)) osr_env
      in
      let (osr_env', statuses) = List.split res in
      let changed = List.exists (fun b -> b) (status :: statuses) in
      (penv, Osr (e', tf, tv, tl, osr_env'), changed)
    | Stop e ->
      let (e', changed) = prop_fold e in
      (penv, Stop e', changed)
    | Drop x ->
      (* `x` no longer in scope, so remove it from the environment. *)
      (Prop_env.remove x penv, instr, false)
    | Decl_mut (_, None) | Clear _ | Read _
    | Label _ | Goto _ | Comment _ -> (penv, instr, false)
  in

  (* Perform the optimization over the functions.
   * `instrs` is the instruction stream to optimize, `worklist` is the worklist,
   * `seen` is a PcSet that keeps track of PCs we already processed (to avoid
   * infinite looping), and `changed` tracks whether the instruction stream was
   * changed.
   *
   * `normalize` returns a pair of the new environment and new instruction.
   * That new environment must be used for all successors of the current
   * instruction, which is why it is included in the worklist.
   * *)
  let rec work instrs worklist seen changed =
    let open Analysis in
    match worklist with
    | [] -> if changed then Some instrs else None
    | (_, pc) :: rest when PcSet.mem pc seen -> work instrs rest seen changed
    | (penv, pc) :: rest ->
      let (penv, instr, changed') = normalize pc penv in
      (* Assume program is well-scoped,
       * i.e. we have the same vars on all successors. *)
      let succs = List.map (fun pc -> (penv, pc)) (successors_at instrs pc) in
      instrs.(pc) <- instr;
      work instrs (succs @ rest) (PcSet.add pc seen) (changed || changed')
  in

  work (Array.copy instrs) [(Prop_env.empty, 0)] Analysis.PcSet.empty false


open Transform_utils

let make_constant (({formals; instrs} as inp) : analysis_input) : instructions option =
  let required = Analysis.required inp in
  let constant var pc =
    match[@warning "-4"] instrs.(pc) with
    | Assign (x, _) when x = var -> false
    | Drop x when x = var -> false
    | Clear x when x = var -> false
    | Read x when x = var -> false
    | Call (_, _, exp) ->
      let is_passed_by_val = function
        | Arg_by_ref x when x = var -> false
        | _ -> true in
      List.for_all is_passed_by_val exp
    | _ -> true
  in

  let changes = Array.map (fun _ -> Unchanged) instrs in
  let rec apply pc =
    if Array.length instrs = pc then () else
    match[@warning "-4"] instrs.(pc) with
    | Decl_mut (var, Some exp) ->
      let required = required pc in
      if Analysis.PcSet.for_all (constant var) required
      then begin
        let fixup pc =
          let fixup_instr pc = function[@warning "-4"]
            | Osr (e, f, v, l, osr) ->
              let fixup_def = function[@warning "-4"]
                | Osr_mut_ref (x, y) when var = y -> Osr_mut (x, Simple (Var var))
                | d -> d in
              changes.(pc) <- Replace (Osr (e, f, v, l, List.map fixup_def osr))
            | _ -> () in
          match[@warning "-4"] changes.(pc) with
          | Unchanged -> fixup_instr pc instrs.(pc)
          | Replace i -> fixup_instr pc i
          | _ -> assert(false)
        in
        (* all uses keep this variable constant:
         * 1. Change the declaration to const
         * 2. Fixup osr uses: We need to materialize the heap value on osr-out *)
        changes.(pc) <- Replace (Decl_const (var, exp));
        Analysis.PcSet.iter fixup required;
      end;
      apply (pc+1)
    | _ ->
      apply (pc+1)
  in
  let () = apply 0 in
  change_instrs (fun pc -> changes.(pc)) inp
