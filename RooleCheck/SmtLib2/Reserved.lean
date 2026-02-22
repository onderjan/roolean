module

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
