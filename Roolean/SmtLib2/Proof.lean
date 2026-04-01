module

public import Roolean.QfBv.BvTerm
public import Roolean.SmtLib2.Parser

public inductive Proof.SmtNode
  | Relevant
  | Irrelevant
  | Split (varIndex: Nat) (bitIndex: Nat)
    (left: SmtNode) (right: SmtNode)


public structure SmtProof where
  result: Bool
  root: Proof.SmtNode

namespace Proof

public inductive ProofParseError
  | ExpectedProof
  | ExpectedProofResult
  | ExpectedNode
  | ExpectedParenOpen
  | ExpectedParenClose
  | ExpectedEnd
deriving Repr, Nonempty, Inhabited

public inductive EProof where
  | Lexer (err: ELexer)
  | Parser (err: ProofParseError)
deriving Repr, Nonempty, Inhabited

def error (_parser: Parser) (err: ProofParseError) : EProof :=
  EProof.Parser err

def consumeParenOpen(parser: Parser): Except EProof (Parser) := do
  let (parser, token) ← parser.next
  match token with
  | Token.ParenOpen => pure parser
  | _ => Except.error (error parser ProofParseError.ExpectedParenClose)

def consumeParenClose(parser: Parser): Except EProof (Parser) := do
  let (parser, token) ← parser.next
  match token with
  | Token.ParenClose => pure parser
  | _ => Except.error (error parser ProofParseError.ExpectedParenClose)

def consumeEnd(parser: Parser): Except EProof (Parser) := do
  let (parser, token) ← parser.next
  match token with
  | Token.End => pure parser
  | _ => Except.error (error parser ProofParseError.ExpectedEnd)

partial def parseNode (parser: Parser) : Except EProof (Parser × SmtNode) := do
  let (parser, token) ← parser.next
  match token with
    | Token.Symbol name =>
      match name.toString? with
      | some "relevant" => pure (parser, SmtNode.Relevant)
      | some "irrelevant" => pure (parser, SmtNode.Irrelevant)
      | _ => Except.error (error parser ProofParseError.ExpectedNode)

    | Token.ParenOpen =>
      let (parser, token) ← parser.next
      if let Token.Symbol name := token then
        match name.toString? with
        | some "decision" =>
          let (parser, token) ← parser.next
          if let Token.Numeral varIndex _  := token then
            let (parser, token) ← parser.next
            if let Token.Numeral bitIndex _  := token then
              let (parser, left) ← parseNode parser
              let (parser, right) ← parseNode parser
              let parser ← consumeParenClose parser
              pure (parser, SmtNode.Split varIndex bitIndex left right)
            else
              Except.error (error parser ProofParseError.ExpectedNode)
          else
            Except.error (error parser ProofParseError.ExpectedNode)
        | _ => Except.error (error parser ProofParseError.ExpectedNode)
      else
        Except.error (error parser ProofParseError.ExpectedNode)

    | _ => Except.error (error parser ProofParseError.ExpectedNode)


partial def parseProof (parser: Parser) : Except EProof SmtProof := do
  let parser ← consumeParenOpen parser
  let (parser, token) ← parser.next
  match token with
  | Token.Symbol name =>
    let (parser, token) ← parser.next
      match token with
      | Token.Symbol result =>
        let _ ← match name.toString? with
          | "roole-proof" => pure ()
          | _ => Except.error (error parser ProofParseError.ExpectedProof)

        let result ← match result.toString? with
          | some "true" => pure true
          | some "false" => pure false
          | _ => Except.error (error parser ProofParseError.ExpectedProofResult)
        let (parser, root) ← parseNode parser
        let parser ← consumeParenClose parser
        let _ ← consumeEnd parser
        pure { result, root }
      | _ => Except.error (error parser ProofParseError.ExpectedProof)

  | _ => Except.error (error parser ProofParseError.ExpectedProof)

public def parse (filename: String): EIO EProof SmtProof := do
  let tokens ← (lex filename).adapt (λ e => EProof.Lexer e)
  let tokens := tokens.toList
  let parser : Parser := { tokens, initial := tokens }
  let parsed ← EIO.ofExcept (parseProof parser)
  pure parsed
