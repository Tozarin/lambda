(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast
open Utils
open Angstrom

type symb = Getted | NotGetted

let parse_symb f =
  any_char >>= function
  | c when not @@ f c ->
      fail @@ Format.sprintf {|Symbol "%c" is not resolved|} c
  | c -> return c

let parse_spaces = take_while is_ws
let parse_st c = parse_symb (fun symb -> c = symb) *> return Getted
let parse_l_p = parse_st '('
let parse_r_p = parse_st ')'
let parse_l_b = parse_st '['
let parse_r_b = parse_st ']'
let parse_fakelambda = parse_st '\\'
let parse_dot = parse_st '.'
let parse_eq = parse_st '='

let parse_varname =
  take_while is_char >>= function
  | "" -> fail "Expected name of variable"
  | v -> return v

let parse_funname =
  take_while (fun x -> is_char x || is_digit x || x = '_') >>= function
  | "" -> fail "Expected name of function"
  | f -> return f

let get_char_pos code pos =
  let util_str = String.sub code 0 pos in
  let splitted = String.split_on_char '\n' util_str in
  (List.length splitted, List.length (explode (List.hd @@ List.rev splitted)))

let parse_useless_stuff =
  let parse_any_spaces =
    parse_spaces >>= function "" -> fail "Expected spaces" | s -> return s
  in
  many parse_any_spaces

let ( -/-> ) p msg =
  match p with Getted -> return Getted | NotGetted -> fail msg

let s_parse_dot = parse_useless_stuff >>= fun _ -> parse_dot
let s_parse_l_p = parse_useless_stuff >>= fun _ -> parse_l_p
let s_parse_r_p = parse_useless_stuff >>= fun _ -> parse_r_p
let s_parse_l_b = parse_useless_stuff >>= fun _ -> parse_l_b
let s_parse_r_b = parse_useless_stuff >>= fun _ -> parse_r_b
let s_parse_eq = parse_useless_stuff >>= fun _ -> parse_eq
let s_parse_varname = parse_useless_stuff >>= fun _ -> parse_varname

let s_parse_funname =
  parse_useless_stuff >>= fun _ -> parse_l_b *> parse_funname <* parse_r_b

let s_parse_lambda = parse_useless_stuff >>= fun _ -> parse_fakelambda
let s_parse_dot = parse_useless_stuff >>= fun _ -> parse_dot

let s_parse_parents p =
  parse_useless_stuff >>= fun _ -> s_parse_l_p *> p <* s_parse_r_p

let parse_many1 p =
  p >>= fun p1 ->
  many p >>= fun ps -> return (p1 :: ps)

let parse_expr =
  fix (fun expr ->
      let var = s_parse_varname >>= fun v -> return @@ var v in
      let foo = s_parse_funname >>= fun f -> return @@ func f in
      let abs =
        s_parse_parents
          ( s_parse_lambda *> parse_many1 s_parse_varname <* s_parse_dot
          >>= fun vs ->
            expr >>= fun e -> return @@ List.fold_right abs vs e )
      in
      let app =
        s_parse_parents
          ( expr >>= fun e1 ->
            parse_many1 expr >>= fun es -> return @@ List.fold_left app e1 es )
      in
      var <|> abs <|> app <|> foo)

let s_parse_expr =
  parse_useless_stuff >>= fun _ ->
  parse_expr >>= fun e ->
  parse_useless_stuff >>= fun _ -> return e

(** <varname> ::= v
    <funname> ::= f
    <expr> ::= <varname> | (λ<varname> ... <varname>.<expr>) | (<expr> ... <expr>) | [<funname>]*)
let foo =
  s_parse_funname <* s_parse_eq >>= fun f ->
  s_parse_expr >>= fun e -> return @@ F (Outf (f, e))

let expr = s_parse_expr >>= fun e -> return @@ E e
let parser = parse_string ~consume:All (expr <|> foo)

type 'a parse_rezult = Parsed of 'a | Failed of string

let eval s = match parser s with Ok x -> Parsed x | Error msg -> Failed msg

(*****************************tests*****************************)
let parse_opt p s = Result.get_ok @@ parse_string ~consume:All p s
let parse_unopt p s = Result.get_error @@ parse_string ~consume:All p s
let test_ss p s = print_string @@ show_line (parse_opt p s)
let test_f p s = print_string @@ parse_unopt p s
let e_test_ss = test_ss expr
let e_test_f = test_f expr
let f_test_ss = test_ss foo
let f_test_f = test_f foo

let%expect_test _ =
  e_test_ss {|varname|};
  [%expect {| (E (Var "varname")) |}]

let%expect_test _ =
  e_test_ss {|  varname  |};
  [%expect {| (E (Var "varname")) |}]

let%expect_test _ =
  e_test_f {|(varname)|};
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_f {|(varname|};
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_f {|varname)|};
  [%expect {| : end_of_input |}]

let%expect_test _ =
  e_test_f {|  ( varname  )  |};
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_f {|\varname.varname|};
  [%expect {| : Symbol "\" is not resolved |}]

let%expect_test _ =
  e_test_ss {|(\varname.varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(\varnameone varnametwo.varname)|};
  [%expect
    {| (E (Abs ("varnameone", (Abs ("varnametwo", (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|  (  \varname.varname  )  |};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(  \  varname.varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(\    varname   .varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(\varname  .  varname)|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(\varname.   varname   )|};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|  (   \   varname  .  varname  )  |};
  [%expect {| (E (Abs ("varname", (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|(\varnameone.varnametwo)|};
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
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_f {|((varname) varname)|};
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_f {|(varname (varname))|};
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_f {|(λvarname.(varname))|};
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_ss {|[foo]|};
  [%expect {| (E (Fun "foo")) |}]

let%expect_test _ =
  e_test_f {|  [ foo ]  |};
  [%expect {| : Expected name of function |}]

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
  e_test_ss {|((\varname.varname) varname)|};
  [%expect
    {| (E (App ((Abs ("varname", (Var "varname"))), (Var "varname")))) |}]

let%expect_test _ =
  e_test_ss {|((\varnameone.varnametwo) varnamethree)|};
  [%expect
    {| (E (App ((Abs ("varnameone", (Var "varnametwo"))), (Var "varnamethree")))) |}]

let%expect_test _ =
  e_test_ss {|((\varname.varname) (\varname.varname))|};
  [%expect
    {|
    (E
       (App ((Abs ("varname", (Var "varname"))),
          (Abs ("varname", (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|(varname (\varname.varname))|};
  [%expect
    {| (E (App ((Var "varname"), (Abs ("varname", (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|(\varname.(varname varname))|};
  [%expect
    {| (E (Abs ("varname", (App ((Var "varname"), (Var "varname")))))) |}]

let%expect_test _ =
  e_test_ss {|(\varname.(\varname.varname))|};
  [%expect {| (E (Abs ("varname", (Abs ("varname", (Var "varname")))))) |}]

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
  [%expect {| : Symbol "(" is not resolved |}]

let%expect_test _ =
  e_test_ss {|(\x y z . (x y z))|};
  [%expect
    {|
    (E
       (Abs ("x",
          (Abs ("y", (Abs ("z", (App ((App ((Var "x"), (Var "y"))), (Var "z")))))
             ))
          ))) |}]

let%expect_test _ =
  e_test_ss {|(\x y z . ((x y) z))|};
  [%expect
    {|
    (E
       (Abs ("x",
          (Abs ("y", (Abs ("z", (App ((App ((Var "x"), (Var "y"))), (Var "z")))))
             ))
          ))) |}]

let%expect_test _ =
  e_test_ss {|(\x . [foo])|};
  [%expect {| (E (Abs ("x", (Fun "foo")))) |}]

let%expect_test _ =
  e_test_ss {|(\x . ([foo] [foo]))|};
  [%expect {| (E (Abs ("x", (App ((Fun "foo"), (Fun "foo")))))) |}]

let%expect_test _ =
  f_test_ss {|[foo]=varname|};
  [%expect {| (F (Outf ("foo", (Var "varname")))) |}]

let%expect_test _ =
  f_test_ss {|     [foo]  =     varname      |};
  [%expect {| (F (Outf ("foo", (Var "varname")))) |}]

let%expect_test _ =
  f_test_ss {|[foo] = (\varname . varname)|};
  [%expect {| (F (Outf ("foo", (Abs ("varname", (Var "varname")))))) |}]

let%expect_test _ =
  f_test_ss {|[foo] = (varname varname)|};
  [%expect {| (F (Outf ("foo", (App ((Var "varname"), (Var "varname")))))) |}]

let%expect_test _ =
  f_test_ss {|[f1] = varname|};
  [%expect {| (F (Outf ("f1", (Var "varname")))) |}]

let%expect_test _ =
  f_test_ss {|[1f] = varname|};
  [%expect {| (F (Outf ("1f", (Var "varname")))) |}]

let%expect_test _ =
  f_test_ss {|[1] = varname|};
  [%expect {| (F (Outf ("1", (Var "varname")))) |}]

let%expect_test _ =
  f_test_f {|[ foo] = varname|};
  [%expect {| : Expected name of function |}]

let%expect_test _ =
  f_test_f {|[foo  ] = varname|};
  [%expect{| : Symbol " " is not resolved |}]

let%expect_test _ =
  f_test_f {|[  foo  ] = varname|};
  [%expect {| : Expected name of function |}]
