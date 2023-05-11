(** Copyright 2023, Startsev Matvey *)

open Ast
(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Utils

module Parser : sig
  type input
  type 'a parse_rez = Failed of string | Parsed of 'a * input
  type 'a parser

  val string_to_input : string -> input
  val input_to_string : input -> string
end = struct
  type input = char list

  let string_to_input = explode
  let input_to_string = implode

  type 'a parse_rez = Failed of string | Parsed of 'a * input
  type 'a parser = input -> 'a parse_rez

  let return x : _ parser = fun s -> Parsed (x, s)
  let fail err _ = Failed err

  let parse_symb cond = function
    | h :: t when cond h -> return h t
    | h :: _ -> Failed (Format.asprintf "symbol \"%c\" not resolved" h)
    | _ -> Failed "unexpected EOF"

  let ( >>= ) p f s =
    match p s with Parsed (h, t) -> f h t | Failed err -> Failed err

  let ( let* ) x f = x >>= f
  let ( *> ) p1 p2 = p1 >>= fun _ -> p2
  let ( <* ) p1 p2 = p1 >>= fun h -> p2 *> return h
  let ( <|> ) p1 p2 s = match p1 s with Failed _ -> p2 s | suc -> suc
  let ( -/-> ) p msg s = match p s with Failed _ -> Failed msg | suc -> suc
  let ( >> ) p1 p2 s = match p1 s with Parsed (_, t) -> p2 t | _ -> p2 s

  let conde = function
    | [] -> fail "Empty condition"
    | h :: tl -> List.fold_left ( <|> ) h tl

  let parse_many p =
    let rec helper s =
      match p s with
      | Failed _ -> return [] s
      | Parsed (h, t) -> (helper >>= fun xs -> return (h :: xs)) t
    in
    helper

  let parse_many1 p s =
    match p s with Failed err -> Failed err | Parsed _ -> parse_many p s

  let parse_sequence seq code =
    let rec helper partseq = function
      | [] -> Failed ("expected " ^ implode seq)
      | codeh :: t1 -> (
          match partseq with
          | [] -> Parsed (seq, code)
          | [ seqh ] when seqh = codeh -> Parsed (seq, t1)
          | seqh :: t2 when seqh = codeh -> helper t2 t1
          | _ :: _ -> Failed ("expected " ^ implode seq))
    in
    helper seq code

  let parse_spaces =
    parse_many (parse_symb (fun x -> x = ' ' || x = '\t' || x = '\n'))
    >>= fun x -> return (implode x)

  (* let parse_l_p = parse_symb (fun x -> x = '(') *> return true *)
  let parse_st symb = parse_symb (fun s -> s = symb) *> return true
  let parse_l_p = parse_st '('
  let parse_r_p = parse_st ')'
  let parse_l_b = parse_st '['
  let parse_r_b = parse_st ']'
  let parse_fakelambda = parse_st '\\'
  let parse_dot = parse_st '.'
  let parse_varname = parse_many (parse_symb is_char)

  let parse_funname =
    parse_many (parse_symb (fun x -> is_char x || is_digit x || x = '_'))

  let parse_sequence seq code =
    let rec helper partseq = function
      | [] -> Failed ("expected " ^ implode seq)
      | codeh :: t1 -> (
          match partseq with
          | [] -> Parsed (seq, code)
          | [ seqh ] when seqh = codeh -> Parsed (seq, t1)
          | seqh :: t2 when seqh = codeh -> helper t2 t1
          | _ :: _ -> Failed ("expected " ^ implode seq))
    in
    helper seq code

  let parse_sequences = function
    | [] -> fail "Nothing was expected to be parsed"
    | h :: t ->
        List.fold_left
          (fun p1 s -> p1 <|> parse_sequence s)
          (parse_sequence h) t

  let fail_if_parsed p inp =
    match p inp with
    | Parsed (_, _) -> Failed "success"
    | Failed _ -> return () inp

  let parse_string ~begin_parser ~end_parser =
    begin_parser
    *> (parse_sequences
          (List.map explode [ "\\n"; "\\\""; "\\\'"; "\\[["; "\\" ])
       <|> parse_many
             (fail_if_parsed end_parser *> parse_symb (fun s -> s <> '\n')))
    <* end_parser
    >>= fun s -> return (implode s)

  let parse_ml_string ~begin_parser ~end_parser =
    begin_parser
    *> (parse_sequences
          (List.map explode [ "\\n"; "\\\""; "\\\'"; "\\[["; "\\" ])
       <|> parse_many (fail_if_parsed end_parser *> parse_symb (fun _ -> true))
       )
    <* end_parser
    >>= fun s -> return (implode s)

  let get_char_pos code pos =
    let util_str = String.sub code 0 pos in
    let splitted = String.split_on_char '\n' util_str in
    (List.length splitted, List.length (explode (List.hd @@ List.rev splitted)))

  let parse_useless_stuff =
    let parse_any_spaces =
      parse_spaces >>= function "" -> fail "no spaces" | s -> return s
    in
    parse_many parse_any_spaces

  let s_parse_dot = parse_useless_stuff >> parse_dot -/-> "Expected ."
  let s_parse_l_p = parse_useless_stuff >> parse_l_p -/-> "Expected ("
  let s_parse_r_p = parse_useless_stuff >> parse_r_p -/-> "Expected )"
  let s_parse_l_b = parse_useless_stuff >> parse_l_b -/-> "Expected ["
  let s_parse_r_b = parse_useless_stuff >> parse_r_b -/-> "Expected ]"

  let s_parse_varname =
    parse_useless_stuff >> parse_varname -/-> "Expected variable ident"

  let s_parse_funname =
    parse_useless_stuff
    >> (s_parse_l_b *> parse_funname <* s_parse_r_b)
       -/-> "Expected function ident [funname]"

  let s_parse_string =
    let pse s = parse_sequence (explode s) in
    parse_useless_stuff
    >> (parse_string ~begin_parser:(pse "'") ~end_parser:(pse "'")
       <|> parse_string ~begin_parser:(pse "\"") ~end_parser:(pse "\"")
       <|> parse_ml_string ~begin_parser:(pse "[[") ~end_parser:(pse "]]"))

  let s_parse_fakelabmda =
    parse_useless_stuff >> parse_fakelambda -/-> "Expected λ"

  let parse_lambda =
    s_parse_string >>= function "λ" -> return true | _ -> return false

  let parse_arrow =
    s_parse_string >>= function "->" -> return true | _ -> return false

  let s_parse_lambda = parse_useless_stuff >> parse_lambda -/-> "Expected λ"
  let s_parse_arr = parse_useless_stuff >> parse_arrow -/-> "Expected ->"
  let s_parse_fun = s_parse_lambda <|> s_parse_fakelabmda
  let s_parse_arrow = s_parse_arr <|> s_parse_dot
  let s_parse_parents p = s_parse_l_p *> p <* s_parse_r_p
end

open Angstrom

let conde = function
  | [] -> fail "Empty condition"
  | h :: tl -> List.fold_left ( <|> ) h tl

let is_ws = function ' ' | '\n' | '\t' | '\r' -> true | _ -> false
let ws = skip_while is_ws
let trim p = ws *> p <* ws
let parents p = char '(' *> trim p <* char ')'
let is_l = function 'a' .. 'z' -> true | _ -> false
let is_d = function '0' .. '9' -> true | _ -> false
let varname = take_while1 is_l
let fn = take_while1 (fun x -> is_d x || is_l x)

let funname =
  fn >>= fun name ->
  match int_of_string_opt name with
  | Some _ -> fail "Funname can not be a number"
  | None -> return name

let var = varname >>= fun v -> return @@ Var v
let lambda = string "λ" <|> string "\\"

(** <varname> ::= v
    <funname> ::= f
    <expr> ::= <varname> | (λ<varname> ... <varname>.<expr>) | (<expr> ... <expr>) | [<funname>]*)
let expr =
  fix (fun e ->
      let var = varname >>= fun v -> return @@ Var v in
      let abs =
        parents
          ( trim lambda *> sep_by ws varname <* trim (string "." <|> string "->")
          >>= fun vs ->
            e >>= fun e ->
            return @@ List.fold_right (fun x y -> Abs (x, y)) vs e )
      in
      let app =
        parents
          ( trim e >>= fun e1 ->
            many1 @@ trim e >>= fun es ->
            return @@ List.fold_left (fun x y -> App (x, y)) e1 es )
      in
      let foon = char '[' *> trim fn <* char ']' >>= fun f -> return @@ Fun f in
      trim @@ conde [ var; abs; app; foon ])

let foon =
  trim funname <* trim @@ string "=" >>= fun f ->
  trim expr >>= fun e -> return @@ F (Outf (f, e))

let ex = trim expr >>= fun e -> return @@ E e
let parser = parse_string ~consume:All (trim @@ conde [ ex; foon ])

type 'a parse_rezult = Parsed of 'a | Failed of string

let eval s = match parser s with Ok x -> Parsed x | Error msg -> Failed msg

(*****************************tests*****************************)
let parse_opt p s = Result.get_ok @@ parse_string ~consume:All p s
let parse_unopt p s = Result.get_error @@ parse_string ~consume:All p s
let test_ss p s = print_string @@ show_line (parse_opt p s)
let test_f p s = print_string @@ parse_unopt p s
let e_test_ss = test_ss ex
let e_test_f = test_f ex
let f_test_ss = test_ss foon
let f_test_f = test_f foon

let%expect_test _ =
  e_test_ss {|varname|};
  [%expect {| (E (Var "varname")) |}]

let%expect_test _ =
  e_test_ss {|  varname  |};
  [%expect {| (E (Var "varname")) |}]

let%expect_test _ =
  e_test_f {|(varname)|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_f {|(varname|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_f {|varname)|};
  [%expect {| : end_of_input |}]

let%expect_test _ =
  e_test_f {|  ( varname  )  |};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_f {|λvarname.varname|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_ss {|(λvarname.varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(\varname.varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname->varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(\varname->varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(λvarnameone varnametwo.varname)|};
  [%expect
    {| (E (Abs ("varnameone", (Abs ("varnametwo", (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|  (  λvarname.varname  )  |};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(  λ  varname.varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(λ    varname   .varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname  .  varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname.   varname   )|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|  (   λ   varname  .  varname  )  |};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(λvarnameone.varnametwo)|};
  [%expect {| (E (Abs ("varnameone", (Var "varnametwo")))) |}]

let%expect_test _ =
  e_test_ss {|(varname varname)|};
  [%expect {| (E (App ((Var "varname"), (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(varnameone varnametwo)|};
  [%expect {| (E (App ((Var "varnameone"), (Var "varnametwo")))) |}]

let%expect_test _ =
  e_test_ss {|  (  varname varname)|};
  [%expect {| (E (App ((Var "varname"), (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(varname varname  )   |};
  [%expect {| (E (App ((Var "varname"), (Var "varname")))) |}]

let%expect_test _ =
  e_test_f {|((varname) (varname))|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_f {|((varname) varname)|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_f {|(varname (varname))|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_f {|(λvarname.(varname))|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_ss {|[foo]|};
  [%expect {| (E (Fun "foo")) |}]

let%expect_test _ =
  e_test_ss {|  [ foo ]  |};
  [%expect {| (E (Fun "foo")) |}]

let%expect_test _ =
  e_test_ss {|[f1]|};
  [%expect {| (E (Fun "f1")) |}]

let%expect_test _ =
  e_test_ss {|[1f]|};
  [%expect {| (E (Fun "1f")) |}]

let%expect_test _ =
  e_test_ss {|[1]|};
  [%expect {| (E (Fun "1")) |}]

let%expect_test _ =
  e_test_ss {|((λvarname.varname) varname)|};
  [%expect
    {| (E (App ((Abs ("varname", (Var "varname"))), (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|((λvarnameone.varnametwo) varnamethree)|};
  [%expect
    {| (E (App ((Abs ("varnameone", (Var "varnametwo"))), (Var "varnamethree")))) |}]

let%expect_test _ =
  e_test_ss {|((λvarname.varname) (λvarname.varname))|};
  [%expect
    {|
    (E
       (App ((Abs ("varname", (Var "varname"))),
          (Abs ("varname", (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|(varname (λvarname.varname))|};
  [%expect
    {|
    (E (App ((Var "varname"), (Abs ("varname", (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname.(varname varname))|};
  [%expect
    {|
    (E (Abs ("varname", (App ((Var "varname"), (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname.(λvarname.varname))|};
  [%expect {|
    (E (Abs ("varname", (Abs ("varname", (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|(varnameone varnametwo varnamethree)|};
  [%expect
    {|
      (E
         (App ((App ((Var "varnameone"), (Var "varnametwo"))), (Var "varnamethree")
            ))) |}]

let%expect_test _ =
  e_test_ss {|((varname varname) varname)|};
  [%expect
    {|
    (E (App ((App ((Var "varname"), (Var "varname"))), (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(varname (varname varname))|};
  [%expect
    {|
    (E (App ((Var "varname"), (App ((Var "varname"), (Var "varname")))))) |}]

let%expect_test _ =
  e_test_f {|(varname (varname) varname)|};
  [%expect {| : char '[' |}]

let%expect_test _ =
  e_test_ss {|(\x y z -> (x y z))|};
  [%expect
    {|
    (E
       (Abs ("x",
          (Abs ("y", (Abs ("z", (App ((App ((Var "x"), (Var "y"))), (Var "z")))))
             ))
          ))) |}]

let%expect_test _ =
  e_test_ss {|(\x y z -> ((x y) z))|};
  [%expect
    {|
    (E
       (Abs ("x",
          (Abs ("y", (Abs ("z", (App ((App ((Var "x"), (Var "y"))), (Var "z")))))
             ))
          ))) |}]

let%expect_test _ =
  e_test_ss {|(\x -> [foo])|};
  [%expect {| (E (Abs ("x", (Fun "foo")))) |}]

let%expect_test _ =
  e_test_ss {|(\x -> ([foo] [foo]))|};
  [%expect {| (E (Abs ("x", (App ((Fun "foo"), (Fun "foo")))))) |}]

let%expect_test _ =
  f_test_ss {|foo=varname|};
  [%expect {| (F (Outf ("foo", (Var "varname")))) |}]

let%expect_test _ =
  f_test_ss {|     foo  =     varname      |};
  [%expect {| (F (Outf ("foo", (Var "varname")))) |}]

let%expect_test _ =
  f_test_ss {|foo = (\varname -> varname)|};
  [%expect {| (F (Outf ("foo", (Abs ("varname", (Var "varname")))))) |}]

let%expect_test _ =
  f_test_ss {|foo = (varname varname)|};
  [%expect {| (F (Outf ("foo", (App ((Var "varname"), (Var "varname")))))) |}]

let%expect_test _ =
  f_test_ss {|f1 = varname|};
  [%expect {| (F (Outf ("f1", (Var "varname")))) |}]

let%expect_test _ =
  f_test_ss {|1f = varname|};
  [%expect {| (F (Outf ("1f", (Var "varname")))) |}]

let%expect_test _ =
  f_test_f {|1 = varname|};
  [%expect {| : Funname can not be a number |}]
