import Lean.Data.Json
import Lean.Expr
import Lean.Elab.Term

import Init.Data.ByteArray
import Init.Data.UInt
import AssertCmd
import LeanProtoNativeHelpers


-- Lets us unwrap an option and throw an exception otherwise. There must be a fancy category theoretic name for this
-- that I don't know. 
namespace Option
private def unwrap (x: Option α) : (EStateM IO.Error σ) α := do
  match x with | some z => return z | none => throw $ IO.userError "Tried to unwrap Option.none" 

def unwrap! [Inhabited α] (x: Option α) : α := match x with | some xVal => xVal | none => panic! "Unwrapped none"

end Option

-- TODO list:
-- ) It would be much easier if Int32/64 were wrapped
namespace LeanProto

-- I wanted to make this toUInt64/ofUInt64 but pattern matching on UInt64 seems to be broken
class ProtoEnum (α: Type u) where
  toNat : α -> Nat
  ofNat : Nat -> Option α

class ProtoSerialize (α: Type u) where
  serialize : α -> ByteArray

class ProtoDeserialize (α: Type u) where
  deserialize : ByteArray -> Option α

namespace Utils

def byteArrayToHex(b: ByteArray) : String := 
  let parts := b.data.map (fun x => String.singleton (Nat.digitChar (x.toNat / 16)) ++ String.singleton (Nat.digitChar (x.toNat % 16)))
  String.join parts.toList

-- Adapted from Lean: lean4/src/Lean/Data/Json/Parser.lean
@[inline]
def hexChar (c: Char): Option Nat := do
  if '0' ≤ c ∧ c ≤ '9' then
    pure $ c.val.toNat - '0'.val.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    pure $ c.val.toNat - 'a'.val.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then
    pure $ c.val.toNat - 'A'.val.toNat + 10
  else
    none

def hexToByteArray(s: String): Option ByteArray := do
  if s.length % 2 != 0 then none
  let mut res := ByteArray.mkEmpty $ s.length / 2
  for i in [:((s.length)/2)] do
    let v1 ← hexChar (s[2*i])
    let v2 ← hexChar (s[2*i+1])
    res := res.push $ UInt8.ofNat ((16 * v1) + v2)
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
  let r ← hexToByteArray x
  let p := byteArrayToHex r
  p == x

end

#assert (some true) == (hexTest "")
#assert (some true) == (hexTest "08ffffffffffffffffff0110feffffffffffffffff01180328013100000000000014403d000040c0420b68656c6c6f20776f726c644a01615001")

end Utils

instance : BEq ByteArray where beq := fun a b => a.data == b.data
instance : Repr ByteArray where reprPrec n x := reprPrec (Utils.byteArrayToHex n) x

namespace EncDec

open Lean
open Lean.Elab

deriving instance BEq, Repr for Std.AssocList

deriving instance BEq, Repr for IO.Error
deriving instance Repr for EStateM.Result

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

-- TODO fix: Pattern matching on UInt8 doesn't seem to work :(
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

#print Bool.noConfusion
#print Bool.noConfusionType

private def WireType.natIsValid (x: Nat) : Bool := x == 0 || x == 1 || x == 2 || x == 5
def WireType.ofLit : (u: Nat) -> WireType.natIsValid u = true -> WireType
| 0, _ => WireType.Varint
| 1, _ => WireType.t64Bit
| 2, _ => WireType.LengthDelimited
| 5, _ => WireType.t32Bit
| 3, prf => Bool.noConfusion prf 
| 4, prf => Bool.noConfusion prf 
| Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ _, prf => Bool.noConfusion prf 

structure ParseState where
  d: ByteArray
  i: Nat := 0
  deriving Inhabited

abbrev ProtoParseM := EStateM IO.Error ParseState

def resultToOption (v: EStateM.Result ε ParseState α ) : Option α := match v with 
| EStateM.Result.ok r _ => some r
| EStateM.Result.error r _ => none

def mkOkResult (v: α) : EStateM.Result ε ParseState α := EStateM.Result.ok v (Inhabited.default : ParseState)

def decodeAt (d: ByteArray) (idx: Nat) (f: ProtoParseM α) := EStateM.run f { d := d, i := idx } 

def decode (d: ByteArray) (f: ProtoParseM α) := decodeAt d 0 f

-- macro "#testEncDec" enc:term dec:term val:term : stx => 
--   `(stx|#assert (decode ($enc (ByteArray.mkEmpty 0) $val) $dec) == (mkOkResult $ $val) via SameEvalVal)

def done: ProtoParseM Bool := do
  let s <- get
  return s.d.size <= s.i

#assert (decodeAt (ByteArray.mkEmpty 0) 0 done) == (mkOkResult true) via SameEvalVal
#assert (decodeAt (ByteArray.mk #[0x00]) 0 done) == (mkOkResult false) via SameEvalVal
#assert (decodeAt (ByteArray.mk #[0x00, 0x00, 0x00]) 2 done) == (mkOkResult false) via SameEvalVal
#assert (decodeAt (ByteArray.mk #[0x00, 0x00, 0x00]) 500 done) == (mkOkResult true) via SameEvalVal

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
  s.d.extract s.i (s.i+x)

-- could just do a memory cast in c? I have no idea how platform portability works :(
def decodeFixedUInt64: ProtoParseM UInt64 := do
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

def decodeFixedUInt32: ProtoParseM UInt32 := do
  let bytes ← copyBytes 4
  let v1: UInt32 := (UInt32.ofUInt8 $ bytes.get! 0).shiftLeft (8*0)
  let v2: UInt32 := (UInt32.ofUInt8 $ bytes.get! 1).shiftLeft (8*1)
  let v3: UInt32 := (UInt32.ofUInt8 $ bytes.get! 2).shiftLeft (8*2)
  let v4: UInt32 := (UInt32.ofUInt8 $ bytes.get! 3).shiftLeft (8*3)
  return (v1.lor (v2.lor (v3.lor v4)))

def encodeFixedUInt64 (d: ByteArray) (v: UInt64) : ByteArray := do
  let d := d.push (UInt64.toUInt8 (v.shiftRight (8*0)))
  let d := d.push (UInt64.toUInt8 (v.shiftRight (8*1)))
  let d := d.push (UInt64.toUInt8 (v.shiftRight (8*2)))
  let d := d.push (UInt64.toUInt8 (v.shiftRight (8*3)))
  let d := d.push (UInt64.toUInt8 (v.shiftRight (8*4)))
  let d := d.push (UInt64.toUInt8 (v.shiftRight (8*5)))
  let d := d.push (UInt64.toUInt8 (v.shiftRight (8*6)))
  d.push (UInt64.toUInt8 (v.shiftRight (8*7)))

def encodeFixedUInt32 (d: ByteArray) (v: UInt32) : ByteArray := do
  let d := d.push (UInt32.toUInt8 (v.shiftRight (8*0)))
  let d := d.push (UInt32.toUInt8 (v.shiftRight (8*1)))
  let d := d.push (UInt32.toUInt8 (v.shiftRight (8*2)))
  d.push (UInt32.toUInt8 (v.shiftRight (8*3)))

#assert (decode (encodeFixedUInt64 (ByteArray.mkEmpty 0) 5) decodeFixedUInt64) == (mkOkResult $ UInt64.ofNat 5) via SameEvalVal
#assert (decode (encodeFixedUInt64 (ByteArray.mkEmpty 0) 0) decodeFixedUInt64) == (mkOkResult $ UInt64.ofNat 0) via SameEvalVal
#assert (decode (encodeFixedUInt64 (ByteArray.mkEmpty 0) 5555555) decodeFixedUInt64) == (mkOkResult $ UInt64.ofNat 5555555) via SameEvalVal


#assert (decode (encodeFixedUInt32 (ByteArray.mkEmpty 0) 5) decodeFixedUInt32) == (mkOkResult $ UInt32.ofNat 5) via SameEvalVal
#assert (decode (encodeFixedUInt32 (ByteArray.mkEmpty 0) 0) decodeFixedUInt32) == (mkOkResult $ UInt32.ofNat 0) via SameEvalVal
#assert (decode (encodeFixedUInt32 (ByteArray.mkEmpty 0) 4294967295) decodeFixedUInt32) == (mkOkResult $ UInt32.ofNat 4294967295) via SameEvalVal

-- Proto field numbers are limited to 64bit so we use UInt64 as a result type
partial def decodeVarInt : ProtoParseM UInt64 := do
  let v <- readByte
  let msb := UInt8.shiftRight v 7
  let val := UInt64.ofUInt8 $ UInt8.land v 0x7F
  if msb == 0 then
    val
  else
    return UInt64.lor val (UInt64.shiftLeft (<- decodeVarInt) 7)


#assert (decode (ByteArray.mk #[0x00]) decodeVarInt) == (mkOkResult $ UInt64.ofNat 0) via SameEvalVal
#assert (decode (ByteArray.mk #[0x01]) decodeVarInt) == (mkOkResult $ UInt64.ofNat 1) via SameEvalVal
#assert (decode (ByteArray.mk #[0x7F]) decodeVarInt) == (mkOkResult $ UInt64.ofNat 127) via SameEvalVal
#assert (decodeAt  (ByteArray.mk #[0x08, 0x96, 0x01]) 1 decodeVarInt) == (mkOkResult $ UInt64.ofNat 150) via SameEvalVal
#assert (decodeAt (ByteArray.mk #[0x08, 0x96, 0x01, 0x33]) 1 decodeVarInt) == (mkOkResult $ UInt64.ofNat 150) via SameEvalVal

partial def encodeVarInt (d: ByteArray) (v: UInt64) :=
  if v < 128 then
    d.push $ v.toUInt8
  else
    encodeVarInt (d.push (UInt64.lor v 0x80).toUInt8) (v.shiftRight 7)

#assert (encodeVarInt (ByteArray.mkEmpty 0) 0) ==  (ByteArray.mk #[0x00])
#assert (encodeVarInt (ByteArray.mkEmpty 0) 5) ==  (ByteArray.mk #[0x05])
#assert (encodeVarInt (ByteArray.mkEmpty 0) 127) ==  (ByteArray.mk #[0x7F])
#assert (encodeVarInt (ByteArray.mk #[0xAC]) 5) ==  (ByteArray.mk #[0xAC, 0x05])
#assert (encodeVarInt (ByteArray.mk #[0x08]) 150) ==  (ByteArray.mk #[0x08, 0x96, 0x01])


def decodeKey: ProtoParseM (WireType × Nat) := do
  let i := (<- decodeVarInt).toNat
  -- make this faster via bit shift
  let wt := WireType.ofNat (Nat.mod i 8)
  match wt with
  | none => throw $ IO.userError "Invalid wire type {wt}"
  | some x => (x, i/8)

#assert (decode (ByteArray.mk #[0x08]) decodeKey) == mkOkResult ((WireType.Varint, 1)) via SameEvalVal

def encodeKey (d: ByteArray) (wt: WireType) (idx: Nat)  := encodeVarInt d $ UInt64.ofNat $ idx * 8 + WireType.toNat wt
def encodeKeyLit (d: ByteArray) (wt: Nat) (h: WireType.natIsValid wt = true) (idx: Nat)  := encodeVarInt d $ UInt64.ofNat $ idx * 8 + wt

#assert (decode (encodeKey (ByteArray.mkEmpty 0) WireType.t32Bit 5000) decodeKey) == mkOkResult (WireType.t32Bit, 5000) via SameEvalVal

def allOnes64 : UInt64 := 0xffffffffffffffff
def allOnes32 : UInt32 := 0xffffffff

def UInt64.toInt2C (x: UInt64) : Int :=
  let pos := x.shiftRight 63 == 0
  if pos then Int.ofNat $ x.toNat else Int.negSucc $ (x.xor allOnes64).toNat

def UInt32.toInt2C (x: UInt32) : Int :=
  let pos := x.shiftRight 31 == 0
  if pos then Int.ofNat $ x.toNat else Int.negSucc $ (x.xor allOnes32).toNat

def Int.toUInt64 : Int -> UInt64
| Int.ofNat x => UInt64.ofNat x
| Int.negSucc x => (UInt64.ofNat x).xor allOnes64

def Int.toUInt32 : Int -> UInt32
| Int.ofNat x => UInt32.ofNat x
| Int.negSucc x => (UInt32.ofNat x).xor allOnes32

#assert (UInt64.toInt2C (Int.toUInt64 (Int.ofNat 555))) == (Int.ofNat 555)
#assert (UInt64.toInt2C (Int.toUInt64 (Int.negSucc 555))) == (Int.negSucc 555)

#assert (UInt32.toInt2C (Int.toUInt32 (555:Int))) == (555:Int)
#assert (UInt32.toInt2C (Int.toUInt32 (-555))) == (-555)

def decodeInt32AsInt: ProtoParseM Int := do UInt32.toInt2C (<- decodeVarInt).toUInt32
def decodeInt64AsInt: ProtoParseM Int := do UInt64.toInt2C (<- decodeVarInt)

def encodeIntAsInt32 (d: ByteArray) (v: Int) : ByteArray := encodeVarInt d $ UInt32.toUInt64 $ Int.toUInt32 v
def encodeIntAsInt64 (d: ByteArray) (v: Int) : ByteArray := encodeVarInt d $ Int.toUInt64 v

#assert (decode (encodeIntAsInt32 (ByteArray.mkEmpty 0) 5) decodeInt32AsInt) == (mkOkResult (5:Int)) via SameEvalVal
#assert (decode (encodeIntAsInt32 (ByteArray.mkEmpty 0) 0) decodeInt32AsInt) == (mkOkResult (0:Int)) via SameEvalVal
#assert (decode (encodeIntAsInt32 (ByteArray.mkEmpty 0) (-15555)) decodeInt32AsInt) == (mkOkResult (-15555)) via SameEvalVal

#assert (decode (encodeIntAsInt64 (ByteArray.mkEmpty 0) 5) decodeInt64AsInt) == (mkOkResult (5:Int)) via SameEvalVal
#assert (decode (encodeIntAsInt64 (ByteArray.mkEmpty 0) 0) decodeInt64AsInt) == (mkOkResult (0:Int)) via SameEvalVal
#assert (decode (encodeIntAsInt64 (ByteArray.mkEmpty 0) (-15555)) decodeInt64AsInt) == (mkOkResult (-15555)) via SameEvalVal

def decodeUInt32AsNat: ProtoParseM Nat := do (← decodeVarInt).toNat 
def decodeUInt64AsNat: ProtoParseM Nat := do (← decodeVarInt).toNat 

def encodeNatAsUInt32 (d: ByteArray) (v: Nat) : ByteArray := encodeVarInt d $ UInt32.toUInt64 $ v.toUInt32
def encodeNatAsUInt64 (d: ByteArray) (v: Nat) : ByteArray := encodeVarInt d $ Int.toUInt64 v

#assert (decode (encodeNatAsUInt32 (ByteArray.mkEmpty 0) 5) decodeUInt32AsNat) == (mkOkResult 5) via SameEvalVal
#assert (decode (encodeNatAsUInt32 (ByteArray.mkEmpty 0) 0) decodeUInt32AsNat) == (mkOkResult 0) via SameEvalVal
#assert (decode (encodeNatAsUInt32 (ByteArray.mkEmpty 0) 44444) decodeUInt32AsNat) == (mkOkResult 44444) via SameEvalVal

#assert (decode (encodeNatAsUInt64 (ByteArray.mkEmpty 0) 5) decodeUInt64AsNat) == (mkOkResult 5) via SameEvalVal
#assert (decode (encodeNatAsUInt64 (ByteArray.mkEmpty 0) 0) decodeUInt64AsNat) == (mkOkResult 0) via SameEvalVal
#assert (decode (encodeNatAsUInt64 (ByteArray.mkEmpty 0) 44444) decodeUInt64AsNat) == (mkOkResult 44444) via SameEvalVal


-- Fixed size ints
def decodeFixedInt32AsInt: ProtoParseM Int := do UInt32.toInt2C (<- decodeFixedUInt32)
def decodeFixedInt64AsInt: ProtoParseM Int := do UInt64.toInt2C (<- decodeFixedUInt64)

def encodeIntAsFixedInt32 (d: ByteArray) (v: Int) : ByteArray := encodeFixedUInt32 d $ Int.toUInt32 v
def encodeIntAsFixedInt64 (d: ByteArray) (v: Int) : ByteArray := encodeFixedUInt64 d $ Int.toUInt64 v

#assert (decode (encodeIntAsFixedInt32 (ByteArray.mkEmpty 0) 5) decodeFixedInt32AsInt) == (mkOkResult (5:Int)) via SameEvalVal
#assert (decode (encodeIntAsFixedInt32 (ByteArray.mkEmpty 0) 0) decodeFixedInt32AsInt) == (mkOkResult (0:Int)) via SameEvalVal
#assert (decode (encodeIntAsFixedInt32 (ByteArray.mkEmpty 0) (-15555)) decodeFixedInt32AsInt) == (mkOkResult (-15555)) via SameEvalVal

#assert (decode (encodeIntAsFixedInt64 (ByteArray.mkEmpty 0) 5) decodeFixedInt64AsInt) == (mkOkResult (5:Int)) via SameEvalVal
#assert (decode (encodeIntAsFixedInt64 (ByteArray.mkEmpty 0) 0) decodeFixedInt64AsInt) == (mkOkResult (0:Int)) via SameEvalVal
#assert (decode (encodeIntAsFixedInt64 (ByteArray.mkEmpty 0) (-15555)) decodeFixedInt64AsInt) == (mkOkResult (-15555)) via SameEvalVal

-- Bools
def decodeBool : ProtoParseM Bool := do (<- decodeVarInt) != 0
def encodeBool (d: ByteArray) (v: Bool) : ByteArray := encodeVarInt d v.toUInt64

#assert (decode (encodeBool (ByteArray.mkEmpty 0) true) decodeBool) == (mkOkResult true) via SameEvalVal
#assert (decode (encodeBool (ByteArray.mkEmpty 0) false) decodeBool) == (mkOkResult false) via SameEvalVal

-- Floats
-- These four are not at all unsafe
def decodeFloat64AsFloat: ProtoParseM Float := do
  let uint64 ← decodeFixedUInt64
  Float.ofUInt64Transmute uint64

def decodeFloat32AsFloat: ProtoParseM Float := do
  let uint32 ← decodeFixedUInt32
  Float.ofUInt32Transmute uint32

def encodeFloatAsFloat64 (d: ByteArray) (v: Float) : ByteArray := encodeFixedUInt64 d $ v.toUInt64Transmute
def encodeFloatAsFloat32 (d: ByteArray) (v: Float) : ByteArray := encodeFixedUInt32 d $ v.toUInt32Transmute

#assert (decode (ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x14, 0x40]) decodeFloat64AsFloat) == (mkOkResult 5.0) via SameEvalVal
#assert (decode (encodeFloatAsFloat64 (ByteArray.mkEmpty 0) 5.0) decodeFloat64AsFloat) == (mkOkResult 5.0) via SameEvalVal
#assert (decode (encodeFloatAsFloat64 (ByteArray.mkEmpty 0) 0.0) decodeFloat64AsFloat) == (mkOkResult 0.0) via SameEvalVal
#assert (decode (encodeFloatAsFloat64 (ByteArray.mkEmpty 0) (-15555.0)) decodeFloat64AsFloat) == (mkOkResult (-15555.0)) via SameEvalVal

#assert (decode (encodeFloatAsFloat32 (ByteArray.mkEmpty 0) 5.0) decodeFloat32AsFloat) == (mkOkResult 5.0) via SameEvalVal
#assert (decode (encodeFloatAsFloat32 (ByteArray.mkEmpty 0) 0.0) decodeFloat32AsFloat) == (mkOkResult 0.0) via SameEvalVal
#assert (decode (encodeFloatAsFloat32 (ByteArray.mkEmpty 0) (-15555.0)) decodeFloat32AsFloat) == (mkOkResult (-15555.0)) via SameEvalVal

-- Strings

def decodeString : ProtoParseM String := do
  let len <- decodeVarInt
  let bytes <- copyBytes len.toNat
  String.fromUTF8Unchecked bytes

def encodeString (d: ByteArray) (s: String) :=
  let d := encodeVarInt d s.length.toUInt64
  d.append s.toUTF8

#assert (decode (encodeString (ByteArray.mkEmpty 0) "") decodeString) == (mkOkResult "") via SameEvalVal
#assert (decode (encodeString (ByteArray.mkEmpty 0) "transsubstantiation") decodeString) == (mkOkResult "transsubstantiation") via SameEvalVal


-- ByteArrays

def decodeByteArray : ProtoParseM ByteArray := do
  let len <- decodeVarInt
  copyBytes len.toNat

def encodeByteArray (d: ByteArray) (s: ByteArray) :=
  let d := encodeVarInt d s.size.toUInt64
  d.append s

#assert (decode (encodeByteArray (ByteArray.mkEmpty 0) (ByteArray.mk #[])) decodeByteArray) == (mkOkResult (ByteArray.mk #[])) via SameEvalVal
#assert (decode (encodeByteArray (ByteArray.mkEmpty 0) "transsubstantiation".toUTF8) decodeByteArray) == (mkOkResult "transsubstantiation".toUTF8) via SameEvalVal

-- Enums
def decodeEnum [ProtoEnum α] : ProtoParseM $ α := do
  let opt := ProtoEnum.ofNat (← decodeVarInt).toNat
  opt.unwrap
def encodeEnum [ProtoEnum α] (d: ByteArray) (s: α) := encodeVarInt d $ UInt64.ofNat $ ProtoEnum.toNat s

-- PackedArrays

def decodePackedArray (decodeElem: ProtoParseM α) : ProtoParseM $ Array α := do
  let len := (← decodeVarInt).toNat
  let mut res := #[]
  let endIdx := (← get).i + len
  -- would love to have a while loop here
  for i in [:len] do
    if (← get).i >= endIdx then return res
    res := res.push (← decodeElem)
  res

def encodePackedArray (encodeElem: ByteArray -> α -> ByteArray) (d: ByteArray) (s: Array α) : ByteArray := do
  let mut acc := ByteArray.mkEmpty 0
  for entry in s do
    acc := encodeElem acc entry   
  (encodeVarInt d acc.size.toUInt64).append acc

#assert (decode (encodePackedArray encodeNatAsUInt64 (ByteArray.mkEmpty 0) #[]) (decodePackedArray decodeUInt64AsNat))
  == (mkOkResult #[]) via SameEvalVal
#assert (decode (encodePackedArray encodeNatAsUInt64 (ByteArray.mkEmpty 0) #[1, 2, 3, 55555555555]) (decodePackedArray decodeUInt64AsNat))
  == (mkOkResult #[1, 2, 3, 55555555555]) via SameEvalVal
 
#assert (decode (encodePackedArray encodeIntAsInt32 (ByteArray.mkEmpty 0) #[]) (decodePackedArray decodeInt32AsInt))
  == (mkOkResult #[]) via SameEvalVal
#assert (decode (encodePackedArray encodeIntAsInt32 (ByteArray.mkEmpty 0) #[5, -25]) (decodePackedArray decodeInt32AsInt))
  == (mkOkResult #[5, -25]) via SameEvalVal

def decodeKeyAndMixedArray (decodeElem: ProtoParseM α) (wt: WireType) (soFar: Array α): ProtoParseM $ Array α := do
  if (wt == WireType.LengthDelimited) then
    return soFar.append (← decodePackedArray decodeElem)
  soFar.push (← decodeElem)

-- Messages
def decodeMessage [ProtoDeserialize α] : ProtoParseM $ α := do
  let len ← decodeVarInt
  let data ← copyBytes len.toNat
  -- todo we don't have to copy here--replace with array view when that becomes easy
  let proto := ProtoDeserialize.deserialize (α := α) data
  proto.unwrap

def encodeMessage [ProtoSerialize α] (d: ByteArray) (s: α) : ByteArray := do
  let acc := ProtoSerialize.serialize (α := α) s
  (encodeVarInt d acc.size.toUInt64).append acc

-- Maps
def decodeMapEntry (decodeMapKey: ProtoParseM α) (decodeMapVal: ProtoParseM β): ProtoParseM $ (α × β) := do
  let len ← decodeVarInt
  let starting := (← get).i
  let (_, idx1) ← decodeKey
  if idx1 == 1 then do
    let mapKey ← decodeMapKey
    let (_, idx2) ← decodeKey
    if idx2 != 2 then throw $ IO.userError "Unexpected entry index in map entry"
    return (mapKey, (← decodeMapVal))
  if idx1 != 2 then throw $ IO.userError "Unexpected entry index in map entry"
  let mapVal ← decodeMapVal
  let (_, idx2) ← decodeKey
  if idx2 != 1 then throw $ IO.userError "Unexpected entry index in map entry"
  return ((← decodeMapKey), mapVal) 

def encodeMapWithTag (encodeMapKey: ByteArray -> α -> ByteArray) (encodeMapVal: ByteArray -> β -> ByteArray)
  (wtKey: Nat) (h1: WireType.natIsValid wtKey = true) (wtVal: Nat) (h2: WireType.natIsValid wtVal = true) (number: Nat) (d: ByteArray)
  (map: Std.AssocList α β) : ByteArray := do
  let mut res := d
  for (k, v) in map do
    let mut acc := ByteArray.mkEmpty 0
    -- Acc contains a pseudo-proto where field 1 represents the key and field 2 the value
    acc := encodeKey acc (WireType.ofLit wtKey h1) 1 
    acc := encodeMapKey acc k
    acc := encodeKey acc (WireType.ofLit wtVal h2) 2 
    acc := encodeMapVal acc v
    -- First append tag
    res := encodeKey res WireType.LengthDelimited number 
    -- Then append length
    res := encodeVarInt res acc.size.toUInt64
    -- Then acc
    res := res.append acc
  return res

def encodeWithTag (fn: ByteArray -> α -> ByteArray) (wireType: Nat)
  (h: WireType.natIsValid wireType = true) (number: Nat) (d: ByteArray) (val: α) : ByteArray :=
  fn (encodeKey d (WireType.ofLit wireType h) number) val

-- TODO fix unwrap
def encodeIfNotNoneWithTag (fn: ByteArray -> α -> ByteArray) (wireType: Nat)
  (h: WireType.natIsValid wireType = true) (number: Nat) (d: ByteArray) : Option α -> ByteArray
| none => d
| some a => encodeWithTag fn wireType h number d a

def encodeUnpackedArrayWithTag (fn: ByteArray -> α -> ByteArray) (wireType: Nat)
  (h: WireType.natIsValid wireType = true) (number: Nat) (d: ByteArray) (vals: Array α) : ByteArray := do
  let mut res := d
  for val in vals do
    res := encodeWithTag fn wireType h number res val
  return res

def someM (f: ProtoParseM α) : ProtoParseM $ Option α := do return some (← f)

-- def encodeMapWithTag (encodeMapKey: ByteArray -> α -> ByteArray) (encodeMapVal: ByteArray -> β -> ByteArray)
--   (d: ByteArray) (wtKey: Nat) (h1: WireType.natIsValid wtKey = true) (wtVal: Nat) (h2: WireType.natIsValid wtVal = true) 
--   (map: AssocList α β) : ByteArray := do
--   let mut res := d
--   for val in vals do
--     res := encodeWithTag fn wireType h number res val
--   return res

end EncDec

end LeanProto

def main(x: List String): IO UInt32 := do return 0