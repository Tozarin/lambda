type var = string [@@deriving show { with_path = false }]

type expr = Abs of var list * expr | App of expr * expr | Var of var
[@@deriving show { with_path = false }]
