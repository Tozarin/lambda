type expr =
  | Abs of string * expr
  | App of expr * expr
  | Var of string
  | Fun of string
[@@deriving show { with_path = false }]

type out_f = Outf of string * expr [@@deriving show { with_path = false }]
type line = E of expr | F of out_f [@@deriving show { with_path = false }]
