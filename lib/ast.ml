type expr =
  | Abs of string * expr
  | App of expr * expr
  | Var of string
  | Fun of string * expr
[@@deriving show { with_path = false }]
