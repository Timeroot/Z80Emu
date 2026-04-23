/-!
# Z80 Basic Types

Fundamental type aliases, bit-manipulation helpers, and small
enumerations used throughout the Z80 model.
-/

namespace Z80

-- ═══ Type aliases ═══

/-- An 8-bit byte, the Z80's native data width. -/
abbrev Byte := UInt8

/-- A 16-bit word, used for addresses and register pairs. -/
abbrev Word := UInt16

-- ═══ Byte helpers ═══

/-- Test whether bit `n` (0 = LSB, 7 = MSB) of `b` is set. -/
@[inline] def testBit8 (b : Byte) (n : Nat) : Bool :=
  (b.toNat >>> n) &&& 1 != 0

/-- Set bit `n` of `b` to 1. -/
@[inline] def setBit8 (b : Byte) (n : Nat) : Byte :=
  b ||| (1 <<< n.toUInt8)

/-- Clear bit `n` of `b` to 0. -/
@[inline] def clearBit8 (b : Byte) (n : Nat) : Byte :=
  b &&& ~~~(1 <<< n.toUInt8)

/-- Return the parity of a byte (true = even number of 1-bits). -/
def parity8 (b : Byte) : Bool :=
  let n := b.toNat
  let n := (n ^^^ (n >>> 4)) &&& 0x0F
  let n := (n ^^^ (n >>> 2)) &&& 0x03
  let n := (n ^^^ (n >>> 1)) &&& 0x01
  n == 0

/-- Interpret a byte as a signed value and sign-extend to 16-bit word.
    Used for relative jump displacements. -/
def signExtend (b : Byte) : Word :=
  if b.toNat < 128 then b.toUInt16
  else b.toUInt16 ||| 0xFF00

/-- Interpret a byte as a signed integer (-128..127). -/
def toSigned (b : Byte) : Int :=
  if b.toNat < 128 then (b.toNat : Int) else (b.toNat : Int) - 256

-- ═══ Word helpers ═══

/-- Extract high byte of a 16-bit word. -/
@[inline] def hi16 (w : Word) : Byte := (w >>> 8).toUInt8

/-- Extract low byte of a 16-bit word. -/
@[inline] def lo16 (w : Word) : Byte := w.toUInt8

/-- Assemble two bytes into a 16-bit word (big-endian argument order: hi, lo). -/
@[inline] def mkWord (hi lo : Byte) : Word :=
  (hi.toUInt16 <<< 8) ||| lo.toUInt16

-- ═══ Opcode field extraction ═══
--
-- The standard "octal decode" used by 8080/Z80 decoders.
-- Given a byte with bits `b7 b6 b5 b4 b3 b2 b1 b0`:
-- - `x` = bits 7–6 (0–3)
-- - `y` = bits 5–3 (0–7)
-- - `z` = bits 2–0 (0–7)
-- - `p` = bits 5–4 (0–3), i.e. `y / 2`
-- - `q` = bit 3 (0–1), i.e. `y % 2`

@[inline] def opcX (b : Byte) : Nat := b.toNat >>> 6
@[inline] def opcY (b : Byte) : Nat := (b.toNat >>> 3) &&& 7
@[inline] def opcZ (b : Byte) : Nat := b.toNat &&& 7
@[inline] def opcP (b : Byte) : Nat := (b.toNat >>> 4) &&& 3
@[inline] def opcQ (b : Byte) : Nat := (b.toNat >>> 3) &&& 1

/-- `opcY` always returns a value < 8. -/
theorem opcY_lt (b : Byte) : opcY b < 8 := by
  simp only [opcY]
  have : (7 : Nat) < 2 ^ 3 := by omega
  exact Nat.and_lt_two_pow _ this

-- ═══ Interrupt mode ═══

/-- The Z80 supports three interrupt modes, selected by the `IM` instruction. -/
inductive IntMode where
  | im0   -- Mode 0: device places instruction on data bus
  | im1   -- Mode 1: CPU jumps to 0x0038
  | im2   -- Mode 2: vectored via I register
  deriving Repr, BEq, DecidableEq, Inhabited

end Z80
