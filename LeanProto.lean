import Init.Data.ByteArray
import Init.Data.UInt
import AssertCmd
import LeanProtoNativeHelpers

-- TODO list:
-- ) It would be much easier if Int32/64 were wrapped
namespace LeanProto

namespace Utils

def byteArrayToHex(b: ByteArray) : String := 
  let parts := b.data.map (fun x => String.singleton (Nat.digitChar (x.toNat / 16)) ++ String.singleton (Nat.digitChar (x.toNat % 16)))
  String.join parts.toList

-- Adapted from Lean: lean4/src/Lean/Data/Json/Parser.lean
@[inline]
def hexChar (c: Char): Option Nat := do
  if '0' ≤ c ∧ c ≤ '9' then
    some $ c.val.toNat - '0'.val.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some $ c.val.toNat - 'a'.val.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some $ c.val.toNat - 'A'.val.toNat + 10
  else
    none

def hexToByteArray(s: String): Option ByteArray := do
  if s.length % 2 != 0 then none
  let mut res := ByteArray.mkEmpty $ s.length / 2
  for i in [:((s.length)/2)] do
    let v1 := hexChar (s[2*i])
    let v2 := hexChar (s[2*i+1])
    match (v1, v2) with 
    | (some v1, some v2) => res := res.push $ UInt8.ofNat ((16 * v1) + v2)
    | _ => return none
  return res

def hexToByteArray!(s: String): ByteArray := do
  if s.length % 2 != 0 then none
  let mut res := ByteArray.mkEmpty $ s.length / 2
  for i in [:((s.length)/2)] do
    let v1 := match hexChar (s[2*i]) with | Option.none => panic! "Bad hex" | Option.some x => x
    let v2 := match hexChar (s[2*i+1]) with | Option.none => panic! "Bad hex" | Option.some x => x
    res := res.push $ UInt8.ofNat ((16 * v1) + v2)
  return res

section
  def hexTest(x: String) : Option Bool := do
    match hexToByteArray x with
    | none => return none
    | some r => x == byteArrayToHex r

  #assert (some true) == (hexTest "")
  #assert (some true) == (hexTest "08ffffffffffffffffff0110feffffffffffffffff01180328013100000000000014403d000040c0420b68656c6c6f20776f726c644a01615001")
end

end Utils


-- High-level class definitions
-- I wanted to make this toUInt64/ofUInt64 but pattern matching on UInt64 seems to be broken
class ProtoEnum (α: Type u) where
  toInt : α -> Int
  ofInt : Int -> Option α

class ProtoSerialize (α: Type u) where
  serialize : α -> Except IO.Error ByteArray
  serializeToHex : α -> Except IO.Error String := fun a => Utils.byteArrayToHex <$> (serialize a)

class ProtoDeserialize (α: Type u) where
  deserialize : ByteArray -> Except IO.Error α
  deserializeFromHex : String -> Except IO.Error α := fun x => do
    match Utils.hexToByteArray x with
    | none => Except.error $ IO.userError "Failed to parse hex string"
    | some val => deserialize val 

-- HACKHACKHACK until we have our own Default class. Currently Float's Inhabited returns UInt 1, not 0,
-- so we override that here.
instance : Inhabited Float := ⟨ 0.0 ⟩ 
instance : BEq ByteArray where beq := fun a b => a.data == b.data

-- TODO: consider removing this, possibly too opinionated
instance : Repr ByteArray where reprPrec n x := reprPrec (Utils.byteArrayToHex n) x

deriving instance BEq, Repr for Std.AssocList
deriving instance BEq, Repr for IO.Error
deriving instance BEq, Repr for EStateM.Result

namespace EncDec

-- Definitions for testing
def UInt32Max : Nat := UInt32.size - 1
def UInt64Max : Nat := UInt64.size - 1
def Int32Max : Int := (Int.ofNat ((UInt32.size / 2))) - 1
def Int32Min : Int := -1*(Int.ofNat ((UInt32.size / 2)))
def Int64Max : Int := (Int.ofNat ((UInt64.size / 2))) - 1
def Int64Min : Int := -1*(Int.ofNat ((UInt64.size / 2)))

open Lean
open Lean.Elab

open Utils (hexToByteArray!)

-- Helper for testing
def SameEvalVal [BEq α] [BEq ε] (x y: EStateM.Result ε σ α) : Bool := match x, y with
| EStateM.Result.ok a _, EStateM.Result.ok b _  => a == b
| EStateM.Result.error a _, EStateM.Result.error b _  => a == b
| _, _=> false

inductive WireType where
| Varint : WireType
| t64Bit : WireType
| LengthDelimited : WireType
| t32Bit : WireType
  deriving BEq, Repr, Inhabited

def WireType.toNat: WireType -> Nat
| WireType.Varint => 0
| WireType.t64Bit => 1
| WireType.LengthDelimited => 2
| WireType.t32Bit => 5

-- TODO: Pattern matching on UInt8 doesn't seem to work :(
def WireType.ofNat (u: Nat) : Option WireType := 
if u == 0 then
  some WireType.Varint
else if u == 1 then
  some WireType.t64Bit
else if u == 2 then
  some WireType.LengthDelimited
else if u == 5 then
  some WireType.t32Bit
else
  none

-- Helper to ensure generated code correctness: the generated code contains
-- Nat constants representign WireType. To ensure we don't put invalid values, we codegen
-- `WireType.ofLit <wtNat> rfl`.
private def WireType.natIsValid (x: Nat) : Bool := x == 0 || x == 1 || x == 2 || x == 5
def WireType.ofLit : (u: Nat) -> WireType.natIsValid u = true -> WireType
| 0, _ => WireType.Varint
| 1, _ => WireType.t64Bit
| 2, _ => WireType.LengthDelimited
| 5, _ => WireType.t32Bit
| 3, prf => Bool.noConfusion prf 
| 4, prf => Bool.noConfusion prf 
| Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ _, prf => Bool.noConfusion prf 

-- Mini parsing monad
structure ParseState where
  d: ByteArray
  i: Nat := 0
  deriving Inhabited, Repr

abbrev ProtoParseM := EStateM IO.Error ParseState

def resultToExcept (v: EStateM.Result IO.Error ParseState α ) : Except IO.Error α := match v with 
| EStateM.Result.ok r _ => Except.ok r
| EStateM.Result.error r _ => Except.error r

def mkOkResult (v: α) : EStateM.Result ε ParseState α := EStateM.Result.ok v arbitrary

def parseAt (d: ByteArray) (idx: Nat) (f: ProtoParseM α) := EStateM.run f { d := d, i := idx } 

def parse (d: ByteArray) (f: ProtoParseM α) := parseAt d 0 f

def done: ProtoParseM Bool := do
  let s <- get
  return s.d.size <= s.i

#assert (parseAt (ByteArray.mkEmpty 0) 0 done) == (mkOkResult true) via SameEvalVal
#assert (parseAt (ByteArray.mk #[0x00]) 0 done) == (mkOkResult false) via SameEvalVal
#assert (parseAt (ByteArray.mk #[0x00, 0x00, 0x00]) 2 done) == (mkOkResult false) via SameEvalVal
#assert (parseAt (ByteArray.mk #[0x00, 0x00, 0x00]) 500 done) == (mkOkResult true) via SameEvalVal

def readByte: ProtoParseM UInt8 := do
  let s <- get
  unless s.i + 1 <= s.d.size do
    throw $ IO.userError "OOB"
  set {s with i := s.i + 1}
  s.d.get! s.i

def copyBytes (x: Nat): ProtoParseM ByteArray := do
  let s <- get  
  unless s.i + x <= s.d.size do
    throw $ IO.userError "OOB"
  set {s with i := s.i + x}
  -- TODO: return Byte Subarray once that's easy
  s.d.extract s.i (s.i+x)


-- Mini serialization monad
abbrev ProtoSerAction := EStateM IO.Error ByteArray Unit
def serialize (f: ProtoSerAction) := EStateM.run f (ByteArray.mkEmpty 0) 
def writeByte (b: UInt8): ProtoSerAction := do
  let s <- get
  set (s.push b)

def writeByteArray (b: ByteArray): ProtoSerAction := do
  let s <- get
  set (s.append b)

def mkOkSerResult (s: String) : EStateM.Result ε ByteArray Unit := EStateM.Result.ok () (hexToByteArray! s)

def serDeser [BEq α] [Repr α] (s: α -> ProtoSerAction) (d: ProtoParseM α) (a: α) : Option IO.Error := do
  let sRes ← serialize $ s a
  match sRes with
  | EStateM.Result.error e s => return some e
  | EStateM.Result.ok _ s =>
  let dRes ← parse s d
  match dRes with
  | EStateM.Result.error e s => return some e
  | EStateM.Result.ok a' _ => if a' == a then none else IO.userError s!"Ser {reprStr a}, deser {reprStr a'}"

-- TODO: make native
def parseFixedUInt64: ProtoParseM UInt64 := do
  let bytes ← copyBytes 8
  let v1: UInt64 := (UInt64.ofUInt8 $ bytes.get! 0).shiftLeft (8*0)
  let v2: UInt64 := (UInt64.ofUInt8 $ bytes.get! 1).shiftLeft (8*1)
  let v3: UInt64 := (UInt64.ofUInt8 $ bytes.get! 2).shiftLeft (8*2)
  let v4: UInt64 := (UInt64.ofUInt8 $ bytes.get! 3).shiftLeft (8*3)
  let v5: UInt64 := (UInt64.ofUInt8 $ bytes.get! 4).shiftLeft (8*4)
  let v6: UInt64 := (UInt64.ofUInt8 $ bytes.get! 5).shiftLeft (8*5)
  let v7: UInt64 := (UInt64.ofUInt8 $ bytes.get! 6).shiftLeft (8*6)
  let v8: UInt64 := (UInt64.ofUInt8 $ bytes.get! 7).shiftLeft (8*7)
  return (v1.lor (v2.lor (v3.lor (v4.lor (v5.lor (v6.lor (v7.lor v8)))))))

def parseFixedUInt32: ProtoParseM UInt32 := do
  let bytes ← copyBytes 4
  let v1: UInt32 := (UInt32.ofUInt8 $ bytes.get! 0).shiftLeft (8*0)
  let v2: UInt32 := (UInt32.ofUInt8 $ bytes.get! 1).shiftLeft (8*1)
  let v3: UInt32 := (UInt32.ofUInt8 $ bytes.get! 2).shiftLeft (8*2)
  let v4: UInt32 := (UInt32.ofUInt8 $ bytes.get! 3).shiftLeft (8*3)
  return (v1.lor (v2.lor (v3.lor v4)))

def serializeFixedUInt64 (v: UInt64) : ProtoSerAction := do
  writeByte (UInt64.toUInt8 (v.shiftRight (8*0)))
  writeByte (UInt64.toUInt8 (v.shiftRight (8*1)))
  writeByte (UInt64.toUInt8 (v.shiftRight (8*2)))
  writeByte (UInt64.toUInt8 (v.shiftRight (8*3)))
  writeByte (UInt64.toUInt8 (v.shiftRight (8*4)))
  writeByte (UInt64.toUInt8 (v.shiftRight (8*5)))
  writeByte (UInt64.toUInt8 (v.shiftRight (8*6)))
  writeByte (UInt64.toUInt8 (v.shiftRight (8*7)))

def serializeFixedUInt32 (v: UInt32) : ProtoSerAction := do
  writeByte (UInt32.toUInt8 (v.shiftRight (8*0)))
  writeByte (UInt32.toUInt8 (v.shiftRight (8*1)))
  writeByte (UInt32.toUInt8 (v.shiftRight (8*2)))
  writeByte (UInt32.toUInt8 (v.shiftRight (8*3)))


#assert none == serDeser serializeFixedUInt64 parseFixedUInt64 5
#assert none == serDeser serializeFixedUInt64 parseFixedUInt64 0
#assert none == serDeser serializeFixedUInt64 parseFixedUInt64 5555555

-- Verify endianness
#assert (serialize (serializeFixedUInt32 1)) == (mkOkSerResult "01000000")
#assert (serialize (serializeFixedUInt32 12345678)) == (mkOkSerResult "4E61BC00")
#assert none == serDeser serializeFixedUInt32 parseFixedUInt32 12345678
#assert none == serDeser serializeFixedUInt32 parseFixedUInt32 0
#assert none == serDeser serializeFixedUInt32 parseFixedUInt32 (UInt32.size.toUInt32)

-- Proto field numbers are limited to 64bit so we use UInt64 as a result type
partial def parseVarInt : ProtoParseM UInt64 := do
  let v <- readByte
  let msb := UInt8.shiftRight v 7
  let val := UInt64.ofUInt8 $ UInt8.land v 0x7F
  if msb == 0 then
    val
  else
    return UInt64.lor val (UInt64.shiftLeft (<- parseVarInt) 7)

#assert (parse (ByteArray.mk #[0x00]) parseVarInt) == (mkOkResult $ UInt64.ofNat 0) via SameEvalVal
#assert (parse (ByteArray.mk #[0x01]) parseVarInt) == (mkOkResult $ UInt64.ofNat 1) via SameEvalVal
#assert (parse (ByteArray.mk #[0x7F]) parseVarInt) == (mkOkResult $ UInt64.ofNat 127) via SameEvalVal
#assert (parseAt  (ByteArray.mk #[0x08, 0x96, 0x01]) 1 parseVarInt) == (mkOkResult $ UInt64.ofNat 150) via SameEvalVal
#assert (parseAt (ByteArray.mk #[0x08, 0x96, 0x01, 0x33]) 1 parseVarInt) == (mkOkResult $ UInt64.ofNat 150) via SameEvalVal


partial def serializeVarInt (v: UInt64) : ProtoSerAction := do
  if v < 128 then
    writeByte v.toUInt8
  else
    writeByte (UInt64.lor v 0x80).toUInt8
    serializeVarInt (v.shiftRight 7)

#assert (serialize (serializeVarInt 0)) == (mkOkSerResult "00")
#assert (serialize (serializeVarInt 5)) == (mkOkSerResult "05")
#assert (serialize (serializeVarInt 127)) == (mkOkSerResult "7F")
#assert (serialize (do let _ ← serializeVarInt 127; serializeVarInt 5)) == (mkOkSerResult "7F05")
#assert (serialize (serializeVarInt 150)) == (mkOkSerResult "9601")


def parseKey: ProtoParseM (WireType × Nat) := do
  let i := (<- parseVarInt).toNat
  -- make this faster via bit shift
  let wt := WireType.ofNat (Nat.mod i 8)
  match wt with
  | none => throw $ IO.userError s!"Invalid wire type {i}"
  | some x => (x, i/8)

#assert (parse (ByteArray.mk #[0x08]) parseKey) == mkOkResult ((WireType.Varint, 1)) via SameEvalVal

def serializeTag (args : (WireType × Nat)) : ProtoSerAction := serializeVarInt $ UInt64.ofNat $ args.snd * 8 + WireType.toNat args.fst
-- Avoids encoding and redecoding wiretype because we got a proof that it's correct
def serializeTagLit (d: ByteArray) (wt: Nat) (h: WireType.natIsValid wt = true) (idx: Nat) := serializeVarInt $ UInt64.ofNat $ idx * 8 + wt

#assert none == serDeser serializeTag parseKey (WireType.t32Bit, 5000)

def allOnes64 : UInt64 := 0xffffffffffffffff
def allOnes32 : UInt32 := 0xffffffff

-- Since integers aren't wrapped for now we use uintX and pretend they're intX
-- represented in twos complement
def UInt64.toInt2C (x: UInt64) : Int :=
  let pos := x.shiftRight 63 == 0
  if pos then Int.ofNat $ x.toNat else Int.negSucc $ (x.xor allOnes64).toNat

def UInt32.toInt2C (x: UInt32) : Int :=
  let pos := x.shiftRight 31 == 0
  if pos then Int.ofNat $ x.toNat else Int.negSucc $ (x.xor allOnes32).toNat


def Int.toUInt642C : Int -> UInt64
| Int.ofNat x => UInt64.ofNat x
| Int.negSucc x => (UInt64.ofNat x).xor allOnes64

def Int.toUInt322C : Int -> UInt32
| Int.ofNat x => UInt32.ofNat x
| Int.negSucc x => (UInt32.ofNat x).xor allOnes32

#assert (Int.toUInt322C (-1)) == UInt32.ofNat (UInt32.size - 1)
#assert (Int.toUInt322C Int32Min) == UInt32.ofNat (2^31)

#assert (Int.toUInt642C (-1)) == UInt64.ofNat (UInt64.size - 1)
#assert (Int.toUInt642C Int64Min) == UInt64.ofNat (2^63)

#assert (UInt64.toInt2C (Int.toUInt642C (0:Int))) == (0:Int)
#assert (UInt64.toInt2C (Int.toUInt642C Int64Max)) == Int64Max
#assert (UInt64.toInt2C (Int.toUInt642C (Int32Min))) == (Int32Min)
#assert (UInt64.toInt2C (Int.toUInt642C (Int64Min))) == (Int64Min)

#assert (UInt32.toInt2C (Int.toUInt322C (555:Int))) == (555:Int)
#assert (UInt32.toInt2C (Int.toUInt322C (-555))) == (-555)
#assert (UInt32.toInt2C (Int.toUInt322C Int32Min)) == Int32Min

-- def parseInt32AsInt: ProtoParseM Int := do UInt32.toInt2C (<- parseVarInt).toUInt32
def parseInt32AsInt: ProtoParseM Int := do UInt32.toInt2C (<- parseVarInt).toInt32Transmute
def parseInt64AsInt: ProtoParseM Int := do UInt64.toInt2C (<- parseVarInt)

-- def serializeIntAsInt32 (d: ByteArray) (v: Int) : ByteArray := serializeVarInt d $ UInt32.toUInt64 $ Int.toUInt322C v
-- TODO: clamp Ints or somehow make it obvious that what doesn't fit into int32/64 will be lost.
def serializeIntAsInt32 (v: Int) : ProtoSerAction := serializeVarInt $ Int.toUInt642C v
def serializeIntAsInt64 (v: Int) : ProtoSerAction := serializeVarInt $ Int.toUInt642C v


#assert none == serDeser serializeIntAsInt32 parseInt32AsInt 5
#assert none == serDeser serializeIntAsInt32 parseInt32AsInt Int32Max
#assert none == serDeser serializeIntAsInt32 parseInt32AsInt Int32Min
#assert none == serDeser serializeIntAsInt32 parseInt32AsInt 0
#assert none == serDeser serializeIntAsInt32 parseInt32AsInt (-15555)

#assert none == serDeser serializeIntAsInt64 parseInt64AsInt 5
#assert none == serDeser serializeIntAsInt64 parseInt64AsInt Int64Max
#assert none == serDeser serializeIntAsInt64 parseInt64AsInt Int64Min
#assert none == serDeser serializeIntAsInt64 parseInt64AsInt 0
#assert none == serDeser serializeIntAsInt64 parseInt64AsInt (-15555)

def parseUInt32AsNat: ProtoParseM Nat := do (← parseVarInt).toNat 
def parseUInt64AsNat: ProtoParseM Nat := do (← parseVarInt).toNat 

def serializeNatAsUInt32 (v: Nat) : ProtoSerAction := serializeVarInt $ UInt32.toUInt64 $ (v % UInt32.size).toUInt32
def serializeNatAsUInt64 (v: Nat) : ProtoSerAction := serializeVarInt $ (v % UInt64.size).toUInt64

#assert none == serDeser serializeNatAsUInt32 parseUInt32AsNat 5
#assert none == serDeser serializeNatAsUInt32 parseUInt32AsNat 0
#assert none == serDeser serializeNatAsUInt32 parseUInt32AsNat UInt32Max

#assert none == serDeser serializeNatAsUInt64 parseUInt64AsNat 5
#assert none == serDeser serializeNatAsUInt64 parseUInt64AsNat 0
#assert none == serDeser serializeNatAsUInt64 parseUInt64AsNat UInt64Max

-- Fixed size ints
def parseFixedInt32AsInt: ProtoParseM Int := do UInt32.toInt2C (<- parseFixedUInt32)
def parseFixedInt64AsInt: ProtoParseM Int := do UInt64.toInt2C (<- parseFixedUInt64)

def serializeIntAsFixedInt32 (v: Int) : ProtoSerAction := serializeFixedUInt32 $ Int.toUInt322C v
def serializeIntAsFixedInt64 (v: Int) : ProtoSerAction := serializeFixedUInt64 $ Int.toUInt642C v

#assert none == serDeser serializeIntAsFixedInt32 parseFixedInt32AsInt 5
#assert none == serDeser serializeIntAsFixedInt32 parseFixedInt32AsInt 0
#assert none == serDeser serializeIntAsFixedInt32 parseFixedInt32AsInt Int32Max
#assert none == serDeser serializeIntAsFixedInt32 parseFixedInt32AsInt Int32Min

#assert none == serDeser serializeIntAsFixedInt64 parseFixedInt64AsInt 5
#assert none == serDeser serializeIntAsFixedInt64 parseFixedInt64AsInt 0
#assert none == serDeser serializeIntAsFixedInt64 parseFixedInt64AsInt Int64Max
#assert none == serDeser serializeIntAsFixedInt64 parseFixedInt64AsInt Int64Min

-- sint{32,64}
def fixedparseSInt32(x: UInt32) : Int := UInt32.toInt2C ((x.shiftRight 1).xor (0 - (x.land 1)))
def fixedparseSInt64(x: UInt64) : Int := UInt64.toInt2C ((x.shiftRight 1).xor (0 - (x.land 1)))

def fixedserializeIntToSInt32(v: Int) : UInt32 := 
  let x := Int.toUInt322C v
  ((x.shiftLeft 1).xor (x.arithShiftRight 31))

def fixedserializeIntToSInt64(v: Int) : UInt64 :=
  let x := Int.toUInt642C v
  ((x.shiftLeft 1).xor (x.arithShiftRight 63))

#assert (fixedparseSInt32 $ fixedserializeIntToSInt32 (0:Int)) == (0:Int)
#assert (fixedparseSInt32 $ fixedserializeIntToSInt32 Int32Max) == Int32Max
#assert (fixedparseSInt32 $ fixedserializeIntToSInt32 Int32Min) == Int32Min
#assert (fixedparseSInt64 $ fixedserializeIntToSInt64 Int64Max) == Int64Max
#assert (fixedparseSInt64 $ fixedserializeIntToSInt64 (Int64Min / 2)) == (Int64Min / 2)
#assert (fixedparseSInt64 $ fixedserializeIntToSInt64 Int64Min) == Int64Min


def parseSInt32: ProtoParseM Int := do return fixedparseSInt32 (<- parseVarInt).toUInt32
def parseSInt64: ProtoParseM Int := do 
  let num ← parseVarInt
  pure $ fixedparseSInt64 num

def serializeIntAsSInt32 (v: Int) : ProtoSerAction := 
  serializeVarInt $ UInt32.toUInt64 $ fixedserializeIntToSInt32 v
def serializeIntAsSInt64 (v: Int) : ProtoSerAction := 
  serializeVarInt $ fixedserializeIntToSInt64 v

#assert none == serDeser serializeIntAsSInt32 parseSInt32 5
#assert none == serDeser serializeIntAsSInt32 parseSInt32 0
#assert none == serDeser serializeIntAsSInt32 parseSInt32 Int32Max
#assert none == serDeser serializeIntAsSInt32 parseSInt32 Int32Min

#assert none == serDeser serializeIntAsSInt64 parseSInt64 5
#assert none == serDeser serializeIntAsSInt64 parseSInt64 0
#assert none == serDeser serializeIntAsSInt64 parseSInt64 Int64Max
#assert none == serDeser serializeIntAsSInt64 parseSInt64 Int64Min

-- sfixed{32,64}
def parseSFixed32: ProtoParseM Int := do return fixedparseSInt32 $ (← parseFixedUInt32)
def parseSFixed64: ProtoParseM Int := do return fixedparseSInt64 $ (← parseFixedUInt64)

def serializeIntAsSFixed32 (v: Int) : ProtoSerAction := 
  serializeFixedUInt32 $ fixedserializeIntToSInt32 v

def serializeIntAsSFixed64 (v: Int) : ProtoSerAction := 
  serializeFixedUInt64 $ fixedserializeIntToSInt64 v


#assert none == serDeser serializeIntAsSFixed32 parseSFixed32 5
#assert none == serDeser serializeIntAsSFixed32 parseSFixed32 0
#assert none == serDeser serializeIntAsSFixed32 parseSFixed32 Int32Max
#assert none == serDeser serializeIntAsSFixed32 parseSFixed32 Int32Min

#assert none == serDeser serializeIntAsSFixed64 parseSFixed64 5
#assert none == serDeser serializeIntAsSFixed64 parseSFixed64 0
#assert none == serDeser serializeIntAsSFixed64 parseSFixed64 Int64Max
#assert none == serDeser serializeIntAsSFixed64 parseSFixed64 Int64Min

-- Bools
def parseBool : ProtoParseM Bool := do (<- parseVarInt) != 0
def serializeBool (v: Bool) : ProtoSerAction := serializeVarInt v.toUInt64

#assert none == serDeser serializeBool parseBool true
#assert none == serDeser serializeBool parseBool false

-- Floats
-- These four are not at all unsafe, why do you ask?
def parseFloat32AsFloat: ProtoParseM Float := do
  let uint32 ← parseFixedUInt32
  Float.ofUInt32Transmute uint32

def parseFloat64AsFloat: ProtoParseM Float := do
  let uint64 ← parseFixedUInt64
  Float.ofUInt64Transmute uint64

def serializeFloatAsFloat32 (v: Float) : ProtoSerAction := serializeFixedUInt32 $ v.toUInt32Transmute
def serializeFloatAsFloat64 (v: Float) : ProtoSerAction := serializeFixedUInt64 $ v.toUInt64Transmute

#assert (parse (hexToByteArray! "0000A040") parseFloat32AsFloat) == (mkOkResult 5.0) via SameEvalVal
#assert (parse (hexToByteArray! "000C73C6") parseFloat32AsFloat) == (mkOkResult (-15555.0)) via SameEvalVal
#assert none == serDeser serializeFloatAsFloat32 parseFloat32AsFloat 5.0
#assert none == serDeser serializeFloatAsFloat32 parseFloat32AsFloat 0.0
#assert none == serDeser serializeFloatAsFloat32 parseFloat32AsFloat (-15555.0)

#assert (parse (hexToByteArray! "0000000000001440") parseFloat64AsFloat) == (mkOkResult 5.0) via SameEvalVal
#assert (parse (hexToByteArray! "000000008061CEC0") parseFloat64AsFloat) == (mkOkResult (-15555.0)) via SameEvalVal
#assert none == serDeser serializeFloatAsFloat64 parseFloat64AsFloat 5.0
#assert none == serDeser serializeFloatAsFloat64 parseFloat64AsFloat 0.0
#assert none == serDeser serializeFloatAsFloat64 parseFloat64AsFloat (-15555.0)

-- Strings
def parseString : ProtoParseM String := do
  let len <- parseVarInt
  let bytes <- copyBytes len.toNat
  String.fromUTF8Unchecked bytes

def serializeString (s: String) : ProtoSerAction := do
  let s := s.toUTF8
  serializeVarInt s.size.toUInt64
  writeByteArray s

#assert none == serDeser serializeString parseString ""
#assert none == serDeser serializeString parseString "hellolongstring"
#assert none == serDeser serializeString parseString "おはようございます"

-- ByteArrays
def parseByteArray : ProtoParseM ByteArray := do
  let len <- parseVarInt
  copyBytes len.toNat

def serializeByteArray (s: ByteArray) : ProtoSerAction := do
  serializeVarInt s.size.toUInt64
  writeByteArray s

#assert none == serDeser serializeByteArray parseByteArray "".toUTF8
#assert none == serDeser serializeByteArray parseByteArray "hellolongstring".toUTF8

-- Enums
def parseEnum [ProtoEnum α] : ProtoParseM α := do
  let numVal ← parseInt32AsInt
  match ProtoEnum.ofInt (α:=α) numVal with
  | none => throw $ IO.userError s!"Invalid proto value received: {numVal}"
  | some x => x

def serializeEnum [ProtoEnum α] (s: α) : ProtoSerAction:= serializeIntAsInt32 $ ProtoEnum.toInt s

def serializeWithSize (s: ProtoSerAction) : ProtoSerAction := do
  match serialize s with
    | EStateM.Result.error e _ => throw e
    | EStateM.Result.ok _ b => 
      serializeVarInt b.size.toUInt64
      writeByteArray b

-- Packed arrays
def parsePackedArray (parseElem: ProtoParseM α) : ProtoParseM $ Array α := do
  let len := (← parseVarInt).toNat
  let mut res := #[]
  let endIdx := (← get).i + len
  -- would love to have a while loop here
  for i in [:len] do
    if (← get).i >= endIdx then return res
    res := res.push (← parseElem)
  res

def serializePackedArray (serializeElem: α -> ProtoSerAction) (s: Array α) : ProtoSerAction := 
  serializeWithSize $ s.forM serializeElem

#assert none == serDeser (serializePackedArray serializeNatAsUInt64) (parsePackedArray parseUInt64AsNat) #[]
#assert none == serDeser (serializePackedArray serializeNatAsUInt64) (parsePackedArray parseUInt64AsNat) #[1, 2, 3, 55555555555]
#assert none == serDeser (serializePackedArray serializeIntAsInt32) (parsePackedArray parseInt32AsInt) #[]
#assert none == serDeser (serializePackedArray serializeIntAsInt32) (parsePackedArray parseInt32AsInt) #[5, -25]

-- Messages
def parseMessage (rawparseFn: ProtoParseM α) : ProtoParseM $ α := do
  let len ← parseVarInt
  let data ← copyBytes len.toNat
  -- todo we don't have to copy here--replace with array view when that becomes easy
  match (parse data rawparseFn) with 
  | EStateM.Result.ok val _ => val
  | EStateM.Result.error r _ => throw r 

def serializeMessage (serializeFn: α -> ProtoSerAction) (s: α) : ProtoSerAction := do
  serializeWithSize $ serializeFn s


-- Composite functions that serialize whole fields (key + body)

def serializeWithTag (fn: α -> ProtoSerAction) (wt: WireType) (number: Nat) (val: α) : ProtoSerAction := do
  serializeTag (wt, number)
  fn val

def parseKeyAndMixedArray (parseElem: ProtoParseM α) (wt: WireType) (soFar: Array α): ProtoParseM $ Array α := do
  if (wt == WireType.LengthDelimited) then
    return soFar.append (← parsePackedArray parseElem)
  soFar.push (← parseElem)

def parseKeyAndNonPackedArray (parseElem: ProtoParseM α) (wt: WireType) (soFar: Array α): ProtoParseM $ Array α := do
  soFar.push (← parseElem)

-- Maps
-- A map entry is an autogenerated proto with two fields, key with idx 1 and value with idx 2
partial def parseMapEntryAux [Inhabited α] [Inhabited β] (parseMapKey: ProtoParseM α) 
  (parseMapVal: ProtoParseM β) (x: Option α) (y: Option β) : ProtoParseM $ (Option α × Option β) := do
  if (← done) then return (x, y)
  let (_, idx) ← parseKey
  if idx == 1 then
    let keyVal ← parseMapKey
    parseMapEntryAux parseMapKey parseMapVal (some keyVal) y
  else if idx == 2 then
    let valVal ← parseMapVal
    parseMapEntryAux parseMapKey parseMapVal x (some valVal)
  else
    parseMapEntryAux parseMapKey parseMapVal x y

def parseMapEntry [Inhabited α] [Inhabited β] (parseMapKey: ProtoParseM α) (parseMapVal: ProtoParseM β): ProtoParseM $ (α × β) := do
  let len ← parseVarInt
  let data ← copyBytes len.toNat
  match (parse data (parseMapEntryAux parseMapKey parseMapVal none none)) with
  | EStateM.Result.ok (f, s) _ => (f.getD arbitrary, s.getD arbitrary)
  | EStateM.Result.error r _ => throw r

def serializeMapWithTag (serializeMapKey: α -> ProtoSerAction) (serializeMapVal: β -> ProtoSerAction)
  (wtKey: WireType) (wtVal: WireType) (number: Nat)
  (map: Std.AssocList α β) : ProtoSerAction := do
  for (k, v) in map do    
    -- Each entry is a pseudo-proto where field 1 represents the key and field 2 the value.
    let serEntry : ProtoSerAction := do
      serializeTag (wtKey, 1) 
      serializeMapKey k
      serializeTag (wtVal, 2)
      serializeMapVal v

    serializeTag (WireType.LengthDelimited, number)
    serializeWithSize serEntry


def serializeSkipDefault [Inhabited α] [BEq α] (serializeFn: α -> ProtoSerAction) (val: α) : ProtoSerAction :=
  if val == arbitrary then () else serializeFn val

def serializeOptNotMsg [Inhabited α] [BEq α] (serializeFn: α -> ProtoSerAction) (val: Option α) : ProtoSerAction :=
  match val with | none => () | some x => if x == arbitrary then () else serializeFn x

def serializeOpt [Inhabited α] [BEq α] (serializeFn: α -> ProtoSerAction) (val: Option α) : ProtoSerAction :=
  match val with | none => () | some x => serializeFn x

def serializeOptDef [Inhabited α] (serializeFn: α -> ProtoSerAction) (val: Option α) : ProtoSerAction := 
  match val with | none => serializeFn arbitrary | some x => serializeFn x
  
def serializeIfNonempty [Inhabited α] (serializeFn: Array α -> ProtoSerAction) (val: Array α) : ProtoSerAction := 
  -- serializeFn b $ val.getD arbitrary
  match val.size with | 0 => () | _ => serializeFn val

def serializeUnpackedArrayWithTag [Inhabited α] [BEq α] (fn: α -> ProtoSerAction) (wt: WireType) (number: Nat) (vals: Array α) : ProtoSerAction := do
  for val in vals do
    serializeTag (wt, number)
    fn val

def withIgnoredState (x: ProtoParseM α) (_: α) : ProtoParseM α := x

-- Drop unknown fields for now
def parseUnknown (wt: WireType) : ProtoParseM Unit := do
  match wt with
  | WireType.Varint => let _ ← parseVarInt; ()
  | WireType.t64Bit => let _ ← parseFixedUInt64; ()
  | WireType.LengthDelimited => let _ ← parseString; ()
  | WireType.t32Bit => let _ ← parseFixedUInt32; ()

-- For debugging
-- partial def keepConsuming (ctr: Nat): ProtoParseM Nat := do
--   if (← LeanProto.EncDec.done) then return ctr
--   let (_type, key) ← LeanProto.EncDec.parseKey
--   let _ ← LeanProto.EncDec.parseUnknown _type
--   keepConsuming $ ctr+1

end EncDec

end LeanProto