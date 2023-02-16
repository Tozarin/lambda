(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Lambda.Parser
open Lambda.Ast
open Lambda.Interpreter
open Lambda.Pprinter
open Interpreter (Result)

let rec run_strat env code =
  match small_step_no env code with
  | Ok e ->
      Printf.printf "------------------------------------\n%s\n" (pp code);
      if 0 = compare_expr code e then Printf.printf "\nend\n"
      else run_strat env e
  | Error msg -> Printf.printf "\n%s\n" msg

let run_str env code =
  match eval code with
  | Parsed ast -> (
      match ast with
      | E e ->
          Printf.printf "\nstart\n";
          run_strat env e;
          env
      | F (Outf (name, f)) ->
          Printf.printf "\n";
          FunMap.add name f env)
  | Failed msg ->
      Printf.printf "\n%s\n" msg;
      env

let rec run_repl env =
  Printf.printf "~> ";
  let text = read_line () in
  run_repl @@ run_str env text

let () =
  print_endline "Welcome to λ REPL!";
  run_repl (prep f_list)
