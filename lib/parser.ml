open Angstrom
open Ast

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

let funname =
  take_while1 (fun x -> is_d x || is_l x) >>= fun name ->
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
      let foon =
        char '[' *> trim funname <* char ']' >>= fun f -> return @@ Fun f
      in
      trim @@ conde [ var; abs; app; foon ])

let foon =
  trim funname <* trim @@ string "=" >>= fun f ->
  trim expr >>= fun e -> return @@ F (Outf (f, e))

let ex = expr >>= fun e -> return @@ E e
let parser = parse_string ~consume:All (trim @@ conde [ ex; foon ])

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
  e_test_f {|[1]|};
  [%expect {| : Funname can not be a number |}]

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
  [%expect
    {|
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
