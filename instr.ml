module Variable = struct
  type t = string
  let compare = String.compare
end

module Label = struct
  type t = string
  let compare = String.compare
end

module Address : sig
  type t = private int
  val compare : t -> t -> int
  val fresh : unit -> t
end = struct
  type t = int
  let compare (x : int) y = Pervasives.compare x y
  let counter = ref (-1)
  let fresh () = incr counter; !counter
end

type variable = Variable.t
type label = Label.t

module Pc = struct
  type t = int
  let compare (x : int) y = Pervasives.compare x y
end

type pc = Pc.t

type instruction_stream = instruction array
and instruction =
  | Decl_const of variable * expression
  | Decl_mut of variable * (expression option)
  | Call of variable * label * (expression list)
  | Return of expression
  | Drop of variable
  | Assign of variable * expression
  | Clear of variable
  | Read of variable
  | Branch of expression * label * label
  | Label of label
  | Goto of label
  | Print of expression
  | Osr of expression * label * label * label * osr_def list
  | Stop of expression
  | Comment of string
and osr_def =
  | OsrConst of variable * expression
  | OsrMut of variable * variable
  | OsrMutUndef of variable
and expression =
  | Simple of simple_expression
  | Op of primop * simple_expression list
and simple_expression =
  | Lit of litteral
  | Var of variable
and litteral =
  | Nil
  | Bool of bool
  | Int of int
and primop =
  | Eq
  | Neq
  | Plus

type value =
  | Lit of litteral

type heap_value =
  | Undefined
  | Value of value

type address = Address.t

type binding =
  | Const of value
  | Mut of address

let string_of_litteral : litteral -> string = function
  | Nil -> "nil"
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n

let litteral_of_string : string -> litteral = function
  | "nil" -> Nil
  | "true" -> Bool true
  | "false" -> Bool false
  | n ->
    try Int (int_of_string n) with _ ->
      Printf.kprintf invalid_arg "litteral_of_string %S" n

let string_of_value (Lit lit) = string_of_litteral lit
let value_of_string str : value = Lit (litteral_of_string str)

exception Unbound_label of label

let resolve (code : instruction_stream) (label : string) =
  let rec loop i =
    if i >= Array.length code then raise (Unbound_label label)
    else if code.(i) = Label label then i
    else loop (i + 1)
  in loop 0

module VarSet = Set.Make(Variable)

type variable_type = Mut_var | Const_var

type moded_var = variable_type * variable

exception Incomparable

module ModedVar = struct
  type t = moded_var
  let compare (ma, a) (mb, b) =
    match String.compare a b with
    | 0 ->
      if ma = mb then 0 else raise Incomparable
    | c -> c
end

module ModedVarSet = struct
  include Set.Make(ModedVar)

  let vars set = List.map snd (elements set)
  let untyped set = VarSet.of_list (vars set)

  let muts set =
    let muts = filter (fun (m,v) -> m = Mut_var) set in
    untyped muts

  let diff_untyped typed untyped =
    filter (fun (_m, x) -> not (VarSet.mem x untyped)) typed

  let inter_untyped typed untyped =
    filter (fun (_m, x) -> VarSet.mem x untyped) typed
end

let simple_expr_vars = function
  | Var x -> VarSet.singleton x
  | Lit _ -> VarSet.empty

let expr_vars = function
  | Simple e -> simple_expr_vars e
  | Op (_op, xs) ->
    List.map simple_expr_vars xs
    |> List.fold_left VarSet.union VarSet.empty

let declared_vars = function
  | Call (x, _, _)
  | Decl_const (x, _) -> ModedVarSet.singleton (Const_var, x)
  | Decl_mut (x, _) -> ModedVarSet.singleton (Mut_var, x)
  | (Assign _
    | Drop _
    | Return _
    | Clear _
    | Branch _
    | Label _
    | Goto _
    | Read _
    | Print _
    | Osr _
    | Comment _
    | Stop _) -> ModedVarSet.empty

(* Which variables need to be in scope
 * Producer: declared_vars *)
let required_vars = function
  | Call (_x, f, es) ->
    let vs = List.map expr_vars es in
    List.fold_left VarSet.union VarSet.empty vs
  | Stop e
  | Return e -> expr_vars e
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, Some e) -> expr_vars e
  | Decl_mut (_x, None) -> VarSet.empty
  | Drop x | Clear x | Read x -> VarSet.singleton x
  | Assign (x, e) -> VarSet.union (VarSet.singleton x) (expr_vars e)
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Comment _ -> VarSet.empty
  | Print e -> expr_vars e
  | Osr (e, _, _, _, osr) ->
    let exps = List.map (function
        | OsrConst (_, e) -> e
        | OsrMut (_, x) -> Simple (Var x)
        | OsrMutUndef _ -> Simple (Lit Nil)) osr in
    let exps_vars = List.map expr_vars exps in
    List.fold_left VarSet.union (expr_vars e) exps_vars

let defined_vars = function
  | Call (x, _, _)
  | Decl_const (x, _) -> ModedVarSet.singleton (Const_var, x)
  | Decl_mut (x, Some _)
  | Assign (x ,_)
  | Read x -> ModedVarSet.singleton (Mut_var, x)
  | Decl_mut (_, None)
  | Return _
  | Drop _
  | Clear _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop _ -> ModedVarSet.empty

let dropped_vars = function
  | Drop x -> VarSet.singleton x
  | Return _
  | Call _
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Clear _
  | Read _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop _ -> VarSet.empty

let cleared_vars = function
  | Clear x -> VarSet.singleton x
  | Return _
  | Call _
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Drop _
  | Read _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Stop _ -> VarSet.empty

(* Which variables need to be defined
 * Producer: defined_vars *)
let used_vars = function
  | Call (_x, _f, es) ->
    let vs = List.map expr_vars es in
    List.fold_left VarSet.union VarSet.empty vs
  | Stop e
  | Return e -> expr_vars e
  | Decl_const (_x, e) -> expr_vars e
  | Decl_mut (_x, Some e) -> expr_vars e
  | Decl_mut (_x, None) -> VarSet.empty
  (* the assignee is only required to be in scope, but not used! *)
  | Assign (_, e)
  | Branch (e, _, _)
  | Print e -> expr_vars e
  | Drop _
  | Clear _
  | Label _
  | Goto _
  | Comment _
  | Read _ -> VarSet.empty
  | Osr (e, _, _, _, osr) ->
    let exps = List.map (function
        | OsrConst (_, e) -> e
        | OsrMut (_, x) -> Simple (Var x)
        | OsrMutUndef _ -> Simple (Lit Nil)) osr in
    let exps_vars = List.map expr_vars exps in
    List.fold_left VarSet.union (expr_vars e) exps_vars

module Identifier = struct
  type t = string
  let compare = String.compare
end
type identifier = Identifier.t

type scope_annotation =
  | ExactScope of VarSet.t
  | AtLeastScope of VarSet.t

type inferred_scope =
  | DeadScope
  | Scope of ModedVarSet.t

type annotations = scope_annotation option array

type formal_parameter =
  | ParamConst of variable
  | ParamMut of variable

type version = {
  label : label;
  instrs : instruction_stream;
  annotations : annotations option;
}
type afunction = {
  name : identifier;
  formals : formal_parameter list;
  body : version list;
}
type program = {
  main : afunction;
  functions : afunction list;
}

let get_fun (prog : program) (f : identifier) : afunction =
  if f = "main" then prog.main else
  List.find (fun {name} -> name = f) prog.functions

let get_version (func : afunction) (v : label) : version =
  List.find (fun {label} -> label = v) func.body

let active_version (func : afunction) : version =
  (List.hd func.body)

let replace_active_version (func : afunction) (repl : version) : afunction =
  { func with
    body = repl :: (List.tl func.body); }

module Value = struct
  let int n : value = Lit (Int n)
  let bool b : value = Lit (Bool b)
end
