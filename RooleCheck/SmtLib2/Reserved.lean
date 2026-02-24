module
public import RooleCheck.SmtLib2.String8


-- Reserved words in SMT-LIB2.
public inductive Reserved
  | Binary
  | Decimal
  | Hexadecimal
  | Numeral
  | String
  | Underscore
  | ExclamationMark
  | As
  | Lambda
  | Let
  | Exists
  | Forall
  | Match
  | Par
deriving Repr

public def Reserved.ofString? (str: _root_.String) : Option Reserved :=
  match str with
    | "BINARY" => Reserved.Binary
    | "DECIMAL" => some Reserved.Decimal
    | "HEXADECIMAL" => some Reserved.Hexadecimal
    | "NUMERAL" => some Reserved.Numeral
    | "STRING" => some Reserved.String
    | "_" => some Reserved.Underscore
    | "!" => some Reserved.ExclamationMark
    | "as" => some Reserved.As
    | "lambda" => some Reserved.Lambda
    | "let" => some Reserved.Let
    | "exists" => some Reserved.Exists
    | "forall" => some Reserved.Forall
    | "match" => some Reserved.Match
    | "par" => some Reserved.Par
    | _ => none

public def Reserved.ofString8? (str: String8) : Option Reserved :=
  if let some str := str.toString? then
    Reserved.ofString? str
  else
    none
