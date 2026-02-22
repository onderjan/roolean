module

-- SMT-LIB supports arbitrary 8-bit encodings
-- Represent characters by 8-bit unsigned integers
public abbrev Char8 := UInt8

-- Represent strings by wrapping a byte array
public structure String8 where
  inner: ByteArray
deriving instance BEq, Hashable for String8

public def String8.push (s: String8) (c: Char8) : String8 :=
  { inner := (s.inner.push c) }

public def String8.toString? (s: String8) : Option String := do
  let mut string := ""
  let mut ascii := true
  for c in s.inner do
    if c < 128 then
      string := string.push (Char.ofUInt8 c)
    else
      ascii := false
  if ascii then
    some string
  else
    none

public def String8.fromUTF8 (s: String) : String8 :=
  { inner := s.toByteArray }

public def String8.isEmpty (s: String8) : Bool :=
  s.inner.isEmpty

public def String8.empty : String8 := { inner := ByteArray.empty }

public def String8.singleton (c: Char8) : String8 := { inner := ByteArray.mk #[c] }


public instance : Repr String8 where
  reprPrec x _ :=
    .nestD <| .group <|
      let folder (acc: String) (c: UInt8): String :=
        if c >= 32 && c < 128 then
            acc.push (Char.ofUInt8 c)
          else
            let hex := c.toBitVec.toHex
            acc ++ s!"\\x{hex}"
      let folded := x.inner.foldl folder ""
      .text s!"\"{folded}\""
