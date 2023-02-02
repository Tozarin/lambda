(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast

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
    ]

  let prep = function [] -> FunMap.empty | l -> FunMap.of_seq (List.to_seq l)

  let dgen n =
    let rec helper acc = function
      | 0 -> acc
      | n -> helper (App (Var "s", acc)) (n - 1)
    in
    Abs ("s", Abs ("t", helper (Var "t") n))

  let l_remove_str x list = List.filter (fun y -> not @@ String.equal x y) list
  let l_cont_str x list = List.exists (fun y -> String.equal x y) list

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
        e x >>= fun e -> small_step_cbn env e
    | App (e1, e2) -> (
        small_step_cbn env e1 >>= function
        | Abs (v, t) -> return @@ subset v e2 t
        | e1 -> return @@ App (e1, e2))
end