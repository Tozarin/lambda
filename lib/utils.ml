(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

let l_remove_str x list = List.filter (fun y -> not @@ String.equal x y) list
let l_cont_str x list = List.exists (fun y -> String.equal x y) list
