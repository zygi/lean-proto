namespace Float

@[extern c inline "*(double*)(&#1)"]
constant ofUInt64Transmute (i: UInt64) : Float

@[extern c inline "(double)(*(float*)(&#1))"]
constant ofUInt32Transmute (i: UInt32) : Float

-- Too many casts to put inline
@[extern "proto_lean_transmute_double_to_uint32"]
constant toUInt32Transmute (i: Float) : UInt32

@[extern c inline "*(uint64_t*)(&#1)"]
constant toUInt64Transmute (i: Float) : UInt64

end Float


namespace UInt64

@[extern c inline "((uint64_t)#1)"]
def ofUInt8 (a : UInt8) : UInt64 := a.toNat.toUInt64
@[extern c inline "((uint64_t)#1)"]
def ofUInt16 (a : UInt16) : UInt64 := a.toNat.toUInt64
@[extern c inline "((uint64_t)#1)"]
def ofUInt32 (a : UInt32) : UInt64 := a.toNat.toUInt64

-- TODO: overflows are UB. Fix.
@[extern c inline "(int32_t)(*(int64_t*)(&#1))"]
constant toInt32Transmute (a: UInt64) : UInt32

-- Pretending `a` holds an Int64, do an arithmetic right shift
@[extern "arith_right_shift_64"]
constant arithShiftRight (a: UInt64) (b: UInt64) : UInt64 
end UInt64

namespace UInt32

@[extern c inline "((uint32_t)#1)"]
def ofUInt8 (a : UInt8) : UInt32 := a.toNat.toUInt32
@[extern c inline "((uint32_t)#1)"]
def ofUInt16 (a : UInt16) : UInt32 := a.toNat.toUInt32
@[extern c inline "((uint32_t)#1)"]
def ofUInt64Lossy (a : UInt64) : UInt32 := a.toNat.toUInt32

-- Pretending `a` holds an Int32, do an arithmetic right shift
@[extern "arith_right_shift_32"]
constant arithShiftRight (a: UInt32) (b: UInt32) : UInt32

-- Casts Int32 to Int64
-- This is getting awkward enough that I should probably just wrap Ints
@[extern c inline "(int64_t)(*(int32_t*)(&#1))"]
constant sextPretendingThisIsInt32 (a: UInt32) : UInt64

end UInt32