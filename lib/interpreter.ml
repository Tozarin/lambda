(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast
open Utils

module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( >> ) : 'a t -> 'b t -> 'b t
end

module type MONADERROR = sig
  include MONAD

  val error : string -> 'a t
end

module Result = struct
  type 'a t = ('a, string) Result.t

  let ( >>= ) = Result.bind
  let ( >> ) x f = x >>= fun _ -> f
  let return = Result.ok
  let error = Result.error
end

module Interpreter (M : MONADERROR) = struct
  open M

  module FunMap = struct
    include Map.Make (String)

    let pp pp_v ppf m =
      Format.fprintf ppf "@[[@[";
      iter (fun k v -> Format.fprintf ppf "@[\"%s\": %a@],@\n" k pp_v v) m;
      Format.fprintf ppf "@]]@]"
  end

  type funs = expr FunMap.t [@@deriving show { with_path = false }]

  let f_list =
    [
      ( "if",
        Abs ("c", Abs ("t", Abs ("e", App (App (Var "c", Var "t"), Var "e"))))
      );
      ("true", Abs ("x", Abs ("y", Var "x")));
      ("false", Abs ("x", Abs ("y", Var "y")));
      ( "iszero",
        Abs ("n", App (App (Var "n", Abs ("x", Fun "false")), Fun "true")) );
      ( "y",
        Abs
          ( "f",
            App
              ( Abs ("x", App (Var "f", App (Var "x", Var "x"))),
                Abs ("x", App (Var "f", App (Var "x", Var "x"))) ) ) );
      ( "z",
        Abs
          ( "f",
            App
              ( Abs
                  ( "x",
                    App
                      (Var "f", Abs ("v", App (App (Var "x", Var "x"), Var "v")))
                  ),
                Abs
                  ( "x",
                    App
                      (Var "f", Abs ("v", App (App (Var "x", Var "x"), Var "v")))
                  ) ) ) );
      ( "dec",
        Abs
          ( "n",
            Abs
              ( "f",
                Abs
                  ( "x",
                    App
                      ( App
                          ( App
                              ( Var "n",
                                Abs
                                  ( "g",
                                    Abs
                                      ( "h",
                                        App (Var "h", App (Var "g", Var "f")) )
                                  ) ),
                            Abs ("u", Var "x") ),
                        Abs ("u", Var "u") ) ) ) ) );
      ( "sum",
        Abs
          ( "m",
            Abs
              ( "n",
                Abs
                  ( "f",
                    Abs
                      ( "x",
                        App
                          ( App (Var "m", Var "f"),
                            App (App (Var "n", Var "f"), Var "x") ) ) ) ) ) );
      ( "mul",
        Abs
          ( "m",
            Abs ("n", App (App (Var "m", App (Fun "sum", Var "n")), Fun "0")) )
      );
    ]

  let prep = function [] -> FunMap.empty | l -> FunMap.of_seq (List.to_seq l)
  let abs x y = return @@ Abs (x, y)
  let app x y = return @@ App (x, y)

  let dgen n =
    let rec helper acc = function
      | 0 -> acc
      | n -> helper (App (Var "s", acc)) (n - 1)
    in
    Abs ("s", Abs ("t", helper (Var "t") n))

  let free_vars term =
    let rec helper acc = function
      | Var x -> x :: acc
      | Abs (v, t) -> l_remove_str v (helper [] t)
      | App (a, b) -> helper (helper acc a) b
      | Fun _ -> acc
    in
    helper [] term

  let is_free_in x term = l_cont_str x (free_vars term)

  let rec new_name old restr =
    if l_cont_str old restr then new_name ("_" ^ old) restr else old

  let replace_name_in old n =
    let rec helper = function
      | Var x when String.equal x old -> Var n
      | Var x -> Var x
      | Fun x -> Fun x
      | App (a, b) -> App (helper a, helper b)
      | Abs (v, t) when String.equal v old -> Abs (n, helper t)
      | Abs (v, t) -> Abs (v, helper t)
    in
    helper

  (** [term -> x] expr *)
  let subset x term =
    let rec helper = function
      | Var y when String.equal x y -> term
      | Var y -> Var y
      | Fun x -> Fun x
      | App (a, b) -> App (helper a, helper b)
      | Abs (v, t) when String.equal v x -> Abs (v, t)
      | Abs (v, t) when is_free_in v term ->
          let w = new_name v (free_vars t @ free_vars term) in
          let abs = replace_name_in v w t in
          helper @@ Abs (w, abs)
      | Abs (v, t) -> Abs (v, helper t)
    in
    helper

  let rec small_step_cbn env = function
    | Var x -> return @@ Var x
    | Abs (x, y) -> return @@ Abs (x, y)
    | Fun x ->
        let e x =
          match int_of_string_opt x with
          | Some x -> return @@ dgen x
          | None -> (
              match FunMap.find_opt x env with
              | Some x -> return x
              | None -> error @@ "Can not find function " ^ x)
        in
        e x
    | App (e1, e2) -> (
        match e1 with
        | Abs (v, t) -> return @@ subset v e2 t
        | _ -> small_step_cbn env e1 >>= fun e1 -> return @@ App (e1, e2))

  (*TODO: make beauty*)
  let rec small_step_no env =
    let is_f_simp f e = f env e >>= fun e' -> return (0 = compare_expr e e') in
    function
    | Var x -> return @@ Var x
    | Abs (x, y) ->
        is_f_simp small_step_no y >>= fun c ->
        if c then abs x y else small_step_no env y >>= fun y -> abs x y
    | Fun x ->
        let e x =
          match int_of_string_opt x with
          | Some x -> return @@ dgen x
          | None -> (
              match FunMap.find_opt x env with
              | Some x -> return x
              | None -> error @@ "Can not find function " ^ x)
        in
        e x
    | App (e1, e2) -> (
        match e1 with
        | Abs (v, t) -> return @@ subset v e2 t
        | e1 ->
            let foo1 f e1 e2 k =
              is_f_simp f e1 >>= fun c ->
              if c then k e1 e2 else f env e1 >>= fun e1 -> app e1 e2
            in
            let foo2 f e1 e2 k =
              is_f_simp f e2 >>= fun c ->
              if c then k e1 e2 else f env e2 >>= fun e1 -> app e1 e2
            in
            foo1 small_step_cbn e1 e2 (fun e1 e2 ->
                foo1 small_step_no e1 e2 (fun e1 e2 ->
                    foo2 small_step_no e1 e2 (fun e1 e2 -> app e1 e2))))
end
