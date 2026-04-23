import Z80Emu.Types
import Z80Emu.State
import Z80Emu.Instr

/-!
# Z80 ALU Operations

Flag computation and arithmetic / logic primitives for the Z80.
-/

namespace Z80

-- ═══ 8-bit ALU core ═══

/-- 8-bit addition with carry-in.  Returns `(result, flags)`. -/
def add8 (a b : Byte) (cin : Bool) : Byte × Flags :=
  let ca : Nat := if cin then 1 else 0
  let full := a.toNat + b.toNat + ca
  let result := (full % 256).toUInt8
  let halfFull := (a.toNat &&& 0x0F) + (b.toNat &&& 0x0F) + ca
  let signedR := toSigned a + toSigned b + (ca : Int)
  let overflow := signedR > 127 || signedR < -128
  (result, {
    s  := testBit8 result 7,
    z  := result == 0,
    f5 := testBit8 result 5,
    h  := halfFull > 0x0F,
    f3 := testBit8 result 3,
    pv := overflow,
    n  := false,
    c  := full > 0xFF
  })

/-- 8-bit subtraction with borrow-in.  Returns `(result, flags)`. -/
def sub8 (a b : Byte) (bin : Bool) : Byte × Flags :=
  let ba : Nat := if bin then 1 else 0
  let full := a.toNat + 256 - b.toNat - ba
  let result := (full % 256).toUInt8
  let halfFull := (a.toNat &&& 0x0F) + 16 - (b.toNat &&& 0x0F) - ba
  let signedR := toSigned a - toSigned b - (ba : Int)
  let overflow := signedR > 127 || signedR < -128
  (result, {
    s  := testBit8 result 7,
    z  := result == 0,
    f5 := testBit8 result 5,
    h  := halfFull < 0x10,
    f3 := testBit8 result 3,
    pv := overflow,
    n  := true,
    c  := full < 256
  })

/-- Perform an 8-bit ALU operation. -/
def alu8 (op : ALUOp) (a b : Byte) (oldCarry : Bool) : Byte × Flags :=
  match op with
  | .ADD => add8 a b false
  | .ADC => add8 a b oldCarry
  | .SUB => sub8 a b false
  | .SBC => sub8 a b oldCarry
  | .AND =>
    let result := a &&& b
    (result, {
      s  := testBit8 result 7, z := result == 0,
      f5 := testBit8 result 5, h := true,
      f3 := testBit8 result 3, pv := parity8 result,
      n  := false, c := false })
  | .XOR =>
    let result := a ^^^ b
    (result, {
      s  := testBit8 result 7, z := result == 0,
      f5 := testBit8 result 5, h := false,
      f3 := testBit8 result 3, pv := parity8 result,
      n  := false, c := false })
  | .OR =>
    let result := a ||| b
    (result, {
      s  := testBit8 result 7, z := result == 0,
      f5 := testBit8 result 5, h := false,
      f3 := testBit8 result 3, pv := parity8 result,
      n  := false, c := false })
  | .CP =>
    -- Flags from subtraction but F5/F3 from operand b
    let (result, flags) := sub8 a b false
    (result, { flags with f5 := testBit8 b 5, f3 := testBit8 b 3 })

-- ═══ 8-bit INC / DEC ═══

/-- Increment an 8-bit value.  Carry flag is *not* affected. -/
def inc8 (v : Byte) : Byte × Flags :=
  let result := v + 1
  (result, {
    s  := testBit8 result 7, z := result == 0,
    f5 := testBit8 result 5,
    h  := (v &&& (0x0F : Byte)) == (0x0F : Byte),
    f3 := testBit8 result 3,
    pv := v == (0x7F : Byte),
    n  := false, c := false })

/-- Decrement an 8-bit value.  Carry flag is *not* affected. -/
def dec8 (v : Byte) : Byte × Flags :=
  let result := v - 1
  (result, {
    s  := testBit8 result 7, z := result == 0,
    f5 := testBit8 result 5,
    h  := (v &&& (0x0F : Byte)) == (0x00 : Byte),
    f3 := testBit8 result 3,
    pv := v == (0x80 : Byte),
    n  := true, c := false })

-- ═══ 16-bit addition / subtraction ═══

/-- 16-bit addition (ADD HL,rp).  Only C, H, F5, F3, N affected. -/
def add16 (a b : Word) (oldFlags : Flags) : Word × Flags :=
  let full := a.toNat + b.toNat
  let result := (full % 65536).toUInt16
  let halfFull := (a.toNat &&& 0x0FFF) + (b.toNat &&& 0x0FFF)
  let rhi := hi16 result
  (result, { oldFlags with
    f5 := testBit8 rhi 5,
    h  := halfFull > 0x0FFF,
    f3 := testBit8 rhi 3,
    n  := false,
    c  := full > 0xFFFF })

/-- 16-bit addition with carry (ADC HL,rp).  All flags affected. -/
def adc16 (a b : Word) (cin : Bool) : Word × Flags :=
  let ca : Nat := if cin then 1 else 0
  let full := a.toNat + b.toNat + ca
  let result := (full % 65536).toUInt16
  let halfFull := (a.toNat &&& 0x0FFF) + (b.toNat &&& 0x0FFF) + ca
  let signedA := if a.toNat < 32768 then (a.toNat : Int) else (a.toNat : Int) - 65536
  let signedB := if b.toNat < 32768 then (b.toNat : Int) else (b.toNat : Int) - 65536
  let signedR := signedA + signedB + (ca : Int)
  let rhi := hi16 result
  (result, {
    s  := testBit8 rhi 7, z := result == 0,
    f5 := testBit8 rhi 5,
    h  := halfFull > 0x0FFF,
    f3 := testBit8 rhi 3,
    pv := signedR > 32767 || signedR < -32768,
    n  := false,
    c  := full > 0xFFFF })

/-- 16-bit subtraction with borrow (SBC HL,rp).  All flags affected. -/
def sbc16 (a b : Word) (bin : Bool) : Word × Flags :=
  let ba : Nat := if bin then 1 else 0
  let full := a.toNat + 65536 - b.toNat - ba
  let result := (full % 65536).toUInt16
  let halfFull := (a.toNat &&& 0x0FFF) + 0x1000 - (b.toNat &&& 0x0FFF) - ba
  let signedA := if a.toNat < 32768 then (a.toNat : Int) else (a.toNat : Int) - 65536
  let signedB := if b.toNat < 32768 then (b.toNat : Int) else (b.toNat : Int) - 65536
  let signedR := signedA - signedB - (ba : Int)
  let rhi := hi16 result
  (result, {
    s  := testBit8 rhi 7, z := result == 0,
    f5 := testBit8 rhi 5,
    h  := halfFull < 0x1000,
    f3 := testBit8 rhi 3,
    pv := signedR > 32767 || signedR < -32768,
    n  := true,
    c  := full < 65536 })

-- ═══ Rotate and shift operations ═══

/-- Perform a CB-prefix rotate/shift operation. -/
def rotShift (op : RotOp) (v : Byte) (oldCarry : Bool) : Byte × Flags :=
  let (result, carry) : Byte × Bool :=
    match op with
    | .RLC =>
      let c := testBit8 v 7
      ((v <<< 1) ||| (if c then 1 else 0), c)
    | .RRC =>
      let c := testBit8 v 0
      ((v >>> 1) ||| (if c then (0x80 : Byte) else 0), c)
    | .RL =>
      let c := testBit8 v 7
      ((v <<< 1) ||| (if oldCarry then (1 : Byte) else 0), c)
    | .RR =>
      let c := testBit8 v 0
      ((v >>> 1) ||| (if oldCarry then (0x80 : Byte) else 0), c)
    | .SLA =>
      let c := testBit8 v 7
      (v <<< 1, c)
    | .SRA =>
      let c := testBit8 v 0
      ((v >>> 1) ||| (v &&& (0x80 : Byte)), c)
    | .SLL =>
      let c := testBit8 v 7
      ((v <<< 1) ||| 1, c)
    | .SRL =>
      let c := testBit8 v 0
      (v >>> 1, c)
  (result, {
    s  := testBit8 result 7, z := result == 0,
    f5 := testBit8 result 5, h := false,
    f3 := testBit8 result 3, pv := parity8 result,
    n  := false, c := carry })

-- ═══ DAA (Decimal Adjust Accumulator) ═══

/-- Decimal adjust the accumulator after a BCD addition or subtraction. -/
def daa (a : Byte) (oldFlags : Flags) : Byte × Flags :=
  let nf := oldFlags.n
  let cf := oldFlags.c
  let hf := oldFlags.h
  let loNibble := a.toNat &&& 0x0F
  let (correction, newC) : Nat × Bool :=
    if !nf then
      let (corLo, _) :=
        if hf || loNibble > 9 then (0x06, true) else (0x00, false)
      let corHi :=
        if cf || a.toNat > 0x99 then 0x60 else 0x00
      (corLo + corHi, cf || corHi != 0)
    else
      let corLo := if hf then 0x06 else 0x00
      let corHi := if cf then 0x60 else 0x00
      (corLo + corHi, cf)
  let result : Byte :=
    if !nf then ((a.toNat + correction) % 256).toUInt8
    else ((a.toNat + 256 - correction) % 256).toUInt8
  (result, {
    s  := testBit8 result 7, z := result == 0,
    f5 := testBit8 result 5,
    h  := if !nf then loNibble > 9 else hf && loNibble < 6,
    f3 := testBit8 result 3,
    pv := parity8 result,
    n  := nf, c := newC })

end Z80
