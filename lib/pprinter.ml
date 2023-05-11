(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast

let slen = 100000000000000000
let tab = "  "
let len s = String.length @@ String.concat "" s

let pp term =
  let rec helper = function
    | Var x -> [ x ]
    | Fun x -> [ Printf.sprintf "[%s]" x ]
    | App (a, b) ->
        let a = helper a in
        let b = helper b in
        let s = String.concat " " (a @ b) in
        if String.length s < slen then [ Printf.sprintf "(%s)" s ]
        else [ "(" ] @ List.map (( ^ ) tab) (a @ b) @ [ ")" ]
    | Abs (v, t) ->
        let t = helper t in
        let s = String.concat " " t in
        if String.length s < slen then [ Printf.sprintf "(λ %s.%s)" v s ]
        else [ Printf.sprintf "(λ %s." v ] @ List.map (( ^ ) tab) t @ [ ")" ]
  in
  String.concat "\n" (helper term)
