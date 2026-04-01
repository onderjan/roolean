module

public import Roolean.QfBv.BvTerm
public import Roolean.SmtLib2.Lexer

public inductive Proof.SmtNode
  | Relevant
  | Irrelevant
  | Split (varIndex: Nat) (bitIndex: Nat)
    (left: SmtNode) (right: SmtNode)


public structure SmtProof where
  result: Bool
  root: Proof.SmtNode

namespace Proof

public inductive ParserError
  | ExpectedProof
  | ExpectedProofResult
  | ExpectedNode
  | ExpectedParenOpen
  | ExpectedParenClose
deriving Repr, Nonempty, Inhabited

public structure Parser where
  tokens: List Token
  initial: List Token
deriving Repr, Nonempty, Inhabited

public inductive EParser where
  | Lexer (err: ELexer)
  | Parser (err: ParserError) (parser: Parser)
deriving Repr, Nonempty, Inhabited

def Parser.error (parser: Parser) (err: ParserError) : EParser :=
  EParser.Parser err parser

def Parser.with (parser: Parser) (tokens: List Token) : Parser :=
  { tokens := tokens, initial := parser.initial }

def Parser.next (parser: Parser) : Except EParser (Parser × Token) :=
  match parser.tokens with
  | token :: tokens =>
    pure (parser.with tokens, token)
  | [] => pure (parser, Token.End)

def Parser.skip (parser: Parser) : Except EParser Parser := do
  let (parser, _token) ← parser.next
  pure parser

def Parser.peek (parser: Parser) : Except EParser Token :=
  match parser.tokens with
  | token :: _ =>
    pure (token)
  | [] => pure Token.End

def consumeParenClose(parser: Parser): Except EParser (Parser) := do
  let (parser, token) ← parser.next
  match token with
  | Token.ParenClose => pure parser
  | _ => Except.error (parser.error ParserError.ExpectedParenClose)

partial def parseNode (parser: Parser) : Except EParser (Parser × SmtNode) := do
  let (parser, token) ← parser.next
  match token with
    | Token.Symbol name =>
      match name.toString? with
      | some "relevant" => pure (parser, SmtNode.Relevant)
      | some "irrelevant" => pure (parser, SmtNode.Irrelevant)
      | _ => Except.error (parser.error ParserError.ExpectedNode)

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
              Except.error (parser.error ParserError.ExpectedNode)
          else
            Except.error (parser.error ParserError.ExpectedNode)
        | _ => Except.error (parser.error ParserError.ExpectedNode)
      else
        Except.error (parser.error ParserError.ExpectedNode)

    | _ => Except.error (parser.error ParserError.ExpectedNode)


partial def parseProof (parser: Parser) : Except EParser SmtProof := do
  match parser.tokens with
    | Token.ParenOpen :: Token.Symbol name :: Token.Symbol result :: tokens =>
      let _ ← match name.toString? with
        | "roole-proof" => pure ()
        | _ => Except.error (parser.error ParserError.ExpectedProof)

      let result ← match result.toString? with
        | some "true" => pure true
        | some "false" => pure false
        | _ => Except.error (parser.error ParserError.ExpectedProofResult)
      let (parser, root) ← parseNode (parser.with tokens)
      let _ ← consumeParenClose parser
      pure { result, root }
    | _ => Except.error (parser.error ParserError.ExpectedProof)

public def parse (filename: String): EIO EParser SmtProof := do
  let tokens ← (lex filename).adapt (λ e => EParser.Lexer e)
  let tokens := tokens.toList
  let parser : Parser := { tokens, initial := tokens }
  let parsed ← EIO.ofExcept (parseProof parser)
  pure parsed
