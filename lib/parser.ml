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
let varname = take_while1 is_l
let var = varname >>= fun v -> return @@ Var v
let lambda = string "λ"

(** <varname> ::= v
    <expr> ::= <varname> | (λ<varname>.<expr>) | (<expr> <expr>) *)
let expr =
  fix (fun e ->
      let var = varname >>= fun v -> return @@ Var v in
      let abs =
        parents
          ( trim lambda *> sep_by ws varname <* trim @@ char '.' >>= fun vs ->
            e >>= fun e -> return @@ Abs (vs, e) )
      in
      let app =
        parents
          ( trim e >>= fun e1 ->
            trim e >>= fun e2 -> return @@ App (e1, e2) )
      in
      trim @@ conde [ var; abs; app ])

let parser = parse_string ~consume:All expr

(*****************************tests*****************************)
let parse_opt p s = Result.get_ok @@ parse_string ~consume:All p s
let parse_unopt p s = Result.get_error @@ parse_string ~consume:All p s
let e_test_ss s = print_string @@ show_expr (parse_opt expr s)
let e_test_f s = print_string @@ parse_unopt expr s

let%expect_test _ =
  e_test_ss {|varname|};
  [%expect {| (Var "varname") |}]

let%expect_test _ =
  e_test_ss {|  varname  |};
  [%expect {| (Var "varname") |}]

let%expect_test _ =
  e_test_f {|(varname)|};
  [%expect {| : char '(' |}]

let%expect_test _ =
  e_test_f {|(varname|};
  [%expect {| : not enough input |}]

let%expect_test _ =
  e_test_f {|varname)|};
  [%expect {| : end_of_input |}]

let%expect_test _ =
  e_test_f {|  ( varname  )  |};
  [%expect {| : char '(' |}]

let%expect_test _ =
  e_test_f {|λvarname.varname|};
  [%expect {| : char '(' |}]

let%expect_test _ =
  e_test_ss {|(λvarname.varname)|};
  [%expect {| (Abs (["varname"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(λvarnameone varnametwo.varname)|};
  [%expect{| (Abs (["varnameone"; "varnametwo"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|  (  λvarname.varname  )  |};
  [%expect {| (Abs (["varname"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(  λ  varname.varname)|};
  [%expect {| (Abs (["varname"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(λ    varname   .varname)|};
  [%expect {| (Abs (["varname"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname  .  varname)|};
  [%expect {| (Abs (["varname"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname.   varname   )|};
  [%expect {| (Abs (["varname"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|  (   λ   varname  .  varname  )  |};
  [%expect {| (Abs (["varname"], (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(λvarnameone.varnametwo)|};
  [%expect {| (Abs (["varnameone"], (Var "varnametwo"))) |}]

let%expect_test _ =
  e_test_ss {|(varname varname)|};
  [%expect {| (App ((Var "varname"), (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(varnameone varnametwo)|};
  [%expect {| (App ((Var "varnameone"), (Var "varnametwo"))) |}]

let%expect_test _ =
  e_test_ss {|  (  varname varname)|};
  [%expect {| (App ((Var "varname"), (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(varname varname  )   |};
  [%expect {| (App ((Var "varname"), (Var "varname"))) |}]

let%expect_test _ =
  e_test_f {|((varname) (varname))|};
  [%expect {| : char '(' |}]

let%expect_test _ =
  e_test_f {|((varname) varname)|};
  [%expect {| : char '(' |}]

let%expect_test _ =
  e_test_f {|(varname (varname))|};
  [%expect {| : char '(' |}]

let%expect_test _ =
  e_test_ss {|((λvarname.varname) varname)|};
  [%expect {| (App ((Abs (["varname"], (Var "varname"))), (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|((λvarnameone.varnametwo) varnamethree)|};
  [%expect
    {| (App ((Abs (["varnameone"], (Var "varnametwo"))), (Var "varnamethree"))) |}]

let%expect_test _ =
  e_test_ss {|((λvarname.varname) (λvarname.varname))|};
  [%expect
    {|
    (App ((Abs (["varname"], (Var "varname"))),
       (Abs (["varname"], (Var "varname"))))) |}]

let%expect_test _ =
  e_test_ss {|(varname (λvarname.varname))|};
  [%expect
    {|
    (App ((Var "varname"), (Abs (["varname"], (Var "varname"))))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname.(varname varname))|};
  [%expect
    {|
    (Abs (["varname"], (App ((Var "varname"), (Var "varname"))))) |}]

let%expect_test _ =
  e_test_ss {|(λvarname.(λvarname.varname))|};
  [%expect {|
    (Abs (["varname"], (Abs (["varname"], (Var "varname"))))) |}]

let%expect_test _ =
  e_test_f {|(varname varname varname)|};
  [%expect {|
    : char ')' |}]

let%expect_test _ =
  e_test_ss {|((varname varname) varname)|};
  [%expect
    {|
    (App ((App ((Var "varname"), (Var "varname"))), (Var "varname"))) |}]

let%expect_test _ =
  e_test_ss {|(varname (varname varname))|};
  [%expect
    {|
    (App ((Var "varname"), (App ((Var "varname"), (Var "varname"))))) |}]

let%expect_test _ =
  e_test_f {|(varname (varname) varname)|};
  [%expect {|
    : char '(' |}]