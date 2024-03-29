(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

let compare_string = String.compare

type expr =
  | Abs of string * expr
  | App of expr * expr
  | Var of string
  | Fun of string
[@@deriving compare, show { with_path = false }]

type out_f = Outf of string * expr [@@deriving show { with_path = false }]
type line = E of expr | F of out_f [@@deriving show { with_path = false }]

let abs s expr = Abs (s, expr)
let app e1 e2 = App (e1, e2)
let var s = Var s
let func s = Fun s
