open Instr

(*
 * Constant folding
 *
 * This optimization combines constant propagation, copy propagation, and
 * constant folding.
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
   * Returns an updated expression. *)
  let propagate exp penv =
    let try_prop x e =
      if Prop_env.mem x penv
      then Edit.replace_var_in_exp x (Prop_env.find x penv) e else e in
    VarSet.fold try_prop (expr_vars exp) exp
  in

  (* Constant fold the expression `exp`.
   * Returns an updated expression. *)
  let fold exp =
    match[@warning "-4"] exp with
    | Simple _ -> exp
    | Op (op, [Constant(v1); Constant(v2)]) ->
      begin match op with
      | Eq -> Simple (Constant (Bool (Eval.value_eq v1 v2)))
      | Neq -> Simple (Constant (Bool (Eval.value_neq v1 v2)))
      | Plus -> Simple (Constant (Int (Eval.value_plus v1 v2)))
      end
    | Op (_, _es) -> exp
  in

  (* Try to add a new mapping to the environment. `exp` is the simple expression
   * being bound to the constant variable `x`. *)
  let try_add x exp scope penv =
    match exp with
    | Simple (Constant v) -> Prop_env.add x (Constant v) penv
    | Simple (Var v) ->
      (* `exp` is a variable v, need to check if `v` is const or mut. *)
      begin match scope with
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

  (* Normalize all expressions within `instr`, given a propagation environment.
   * Perform propagation, then folding.
   * Returns a pair of the new environment and the new instruction. *)
  let normalize instr scope penv =
    let prop_fold e = fold (propagate e penv) in
    match instr with
    | Decl_const (x, e) ->
      let e' = prop_fold e in
      (* Constant declaration, so we might need to update the nevironment. *)
      (try_add x e' scope penv, Decl_const (x, e'))
    | Decl_mut (x, Some e) -> (penv, Decl_mut (x, Some (prop_fold e)))
    | Call (x, e, args) ->
      let args' = List.map (fun arg ->
        match arg with
        | Arg_by_val e -> Arg_by_val (prop_fold e)
        | Arg_by_ref _ -> arg) args
      in
      (penv, Call (x, prop_fold e, args'))
    | Return e -> (penv, Return (prop_fold e))
    | Assign (x, e) -> (penv, Assign (x, prop_fold e))
    | Branch (e, l1, l2) -> (penv, Branch (prop_fold e, l1, l2))
    | Print e -> (penv, Print (prop_fold e))
    | Osr (e, tf, tv, tl, osr_env) ->
      let osr_env' = List.map (fun osr_def ->
        match osr_def with
        | Osr_const (y, e) -> Osr_const (y, prop_fold e)
        | Osr_mut (y, e) -> Osr_mut (y, prop_fold e)
        | Osr_mut_ref _ | Osr_mut_undef _ -> osr_def) osr_env
      in
      (penv, Osr (prop_fold e, tf, tv, tl, osr_env'))
    | Stop e -> (penv, Stop (prop_fold e))
    | Drop x ->
      (* `x` no longer in scope, so remove it from the environment. *)
      (Prop_env.remove x penv, instr)
    | Decl_mut (_, None) | Clear _ | Read _
    | Label _ | Goto _ | Comment _ -> (penv, instr)
  in

  (* Perform the optimization over the functions.
   * `instrs` is the instruction stream to optimize, `worklist` is the worklist,
   * and `seen` is a PcSet that keeps track of PCs we already processed (to
   * avoid infinite looping).
   *
   * `normalize` returns a pair of the new environment and new instruction.
   * That new environment must be used for all successors of the current
   * instruction, which is why it is included in the worklist.
   * *)
  let rec work instrs worklist seen =
    let open Analysis in
    match worklist with
    | [] -> Some instrs
    | (_, pc) :: rest when PcSet.mem pc seen -> work instrs rest seen
    | (penv, pc) :: rest ->
      let scope = Scope.infer inp in
      let (penv, instr) = normalize instrs.(pc) scope.(pc) penv in
      let succs = List.map (fun pc -> (penv, pc)) (successors_at instrs pc) in
      instrs.(pc) <- instr;
      work instrs (succs @ rest) (PcSet.add pc seen)
  in

  work (Array.copy instrs) [(Prop_env.empty, 0)] Analysis.PcSet.empty


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
