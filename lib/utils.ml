(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

let l_remove_str x list = List.filter (fun y -> not @@ String.equal x y) list
let l_cont_str x list = List.exists (fun y -> String.equal x y) list

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let implode x = String.of_seq (List.to_seq x)
let is_char = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
let is_digit = function '0' .. '9' -> true | _ -> false
let is_ws = function ' ' | '\n' | '\t' | '\r' -> true | _ -> false
