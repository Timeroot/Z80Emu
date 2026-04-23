import Z80Emu.Types

/-!
# Z80 CPU State

Memory is backed by a flat `ByteArray` of 65 536 bytes so that reads
and writes are O(1).  Lean's reference-counting runtime mutates the
array in-place whenever the reference count is 1, which gives us
amortised O(1) writes during execution (assuming linear access
patterns — i.e. no extra live references to the `Memory` value).
-/

namespace Z80

-- ═══ Flag register ═══

/-- The Z80 flag register, broken out into individual fields.

| Bit | Name | Meaning                         |
|-----|------|---------------------------------|
|  7  |  S   | Sign (copy of bit 7 of result)  |
|  6  |  Z   | Zero (result == 0)              |
|  5  |  F5  | Undocumented (copy of bit 5)    |
|  4  |  H   | Half-carry (BCD)                |
|  3  |  F3  | Undocumented (copy of bit 3)    |
|  2  | P/V  | Parity or oVerflow              |
|  1  |  N   | Subtract (last op was subtract) |
|  0  |  C   | Carry / borrow                  |
-/
structure Flags where
  s  : Bool := false
  z  : Bool := false
  f5 : Bool := false
  h  : Bool := false
  f3 : Bool := false
  pv : Bool := false
  n  : Bool := false
  c  : Bool := false
  deriving Repr, BEq, Inhabited

/-- Pack a `Flags` record into a byte. -/
def Flags.toByte (f : Flags) : Byte :=
  let b : Nat :=
    (if f.s  then 128 else 0) |||
    (if f.z  then  64 else 0) |||
    (if f.f5 then  32 else 0) |||
    (if f.h  then  16 else 0) |||
    (if f.f3 then   8 else 0) |||
    (if f.pv then   4 else 0) |||
    (if f.n  then   2 else 0) |||
    (if f.c  then   1 else 0)
  b.toUInt8

/-- Unpack a byte into a `Flags` record. -/
def Flags.ofByte (b : Byte) : Flags where
  s  := testBit8 b 7
  z  := testBit8 b 6
  f5 := testBit8 b 5
  h  := testBit8 b 4
  f3 := testBit8 b 3
  pv := testBit8 b 2
  n  := testBit8 b 1
  c  := testBit8 b 0

-- ═══ Memory ═══

/-- A flat 64 KiB memory model backed by a `ByteArray`. -/
structure Memory where
  data : ByteArray
  deriving Inhabited

instance : Repr Memory where
  reprPrec _ _ := "<Memory>"

/-- Create a memory filled with zeroes. -/
@[inline] def Memory.zeros : Memory where
  data := ByteArray.mk (Array.replicate 65536 0)

/-- Read a single byte from memory. -/
@[inline] def Memory.read (m : Memory) (addr : Word) : Byte :=
  m.data.get! addr.toNat

/-- Write a single byte to memory, returning a new memory.
    O(1) when the `Memory` value is uniquely referenced (Lean mutates in place). -/
@[inline] def Memory.write (m : Memory) (addr : Word) (val : Byte) : Memory where
  data := m.data.set! addr.toNat val

/-- Read a 16-bit little-endian word from memory. -/
@[inline] def Memory.read16 (m : Memory) (addr : Word) : Word :=
  let lo := m.read addr
  let hi := m.read (addr + 1)
  mkWord hi lo

/-- Write a 16-bit little-endian word to memory. -/
@[inline] def Memory.write16 (m : Memory) (addr : Word) (val : Word) : Memory :=
  let m := m.write addr (lo16 val)
  m.write (addr + 1) (hi16 val)

/-- Load a list of bytes into memory starting at `base`. -/
def Memory.loadBytes (m : Memory) (base : Word) (bytes : List Byte) : Memory :=
  bytes.foldl (init := (m, base)) (fun (m, addr) b =>
    (m.write addr b, addr + 1)) |>.1

-- ═══ CPU State ═══

/-- Complete Z80 CPU state. -/
structure State where
  -- Main register file
  regA  : Byte := 0xFF
  regF  : Flags := Flags.ofByte 0xFF
  regB  : Byte := 0
  regC  : Byte := 0
  regD  : Byte := 0
  regE  : Byte := 0
  regH  : Byte := 0
  regL  : Byte := 0
  -- Shadow (alternate) register file
  regA' : Byte := 0xFF
  regF' : Flags := Flags.ofByte 0xFF
  regB' : Byte := 0
  regC' : Byte := 0
  regD' : Byte := 0
  regE' : Byte := 0
  regH' : Byte := 0
  regL' : Byte := 0
  -- Index registers
  regIX : Word := 0
  regIY : Word := 0
  -- Special-purpose registers
  regSP : Word := 0xFFFF
  regPC : Word := 0
  regI  : Byte := 0
  regR  : Byte := 0
  -- Interrupt and CPU control state
  iff1    : Bool := false
  iff2    : Bool := false
  intMode : IntMode := .im0
  halted  : Bool := false
  -- Memory
  mem : Memory := Memory.zeros
  -- Cycle counter
  cycles : Nat := 0
  -- Output port buffer (bytes written by OUT instructions)
  output : List Byte := []
  deriving Repr

-- ═══ Register-pair accessors ═══

def State.bc (s : State) : Word := mkWord s.regB s.regC
def State.de (s : State) : Word := mkWord s.regD s.regE
def State.hl (s : State) : Word := mkWord s.regH s.regL

def State.setBC (s : State) (v : Word) : State :=
  { s with regB := hi16 v, regC := lo16 v }
def State.setDE (s : State) (v : Word) : State :=
  { s with regD := hi16 v, regE := lo16 v }
def State.setHL (s : State) (v : Word) : State :=
  { s with regH := hi16 v, regL := lo16 v }

def State.af (s : State) : Word := mkWord s.regA s.regF.toByte
def State.setAF (s : State) (v : Word) : State :=
  { s with regA := hi16 v, regF := Flags.ofByte (lo16 v) }

-- ═══ Stack operations ═══

def State.push16 (s : State) (v : Word) : State :=
  let sp' := s.regSP - 2
  let mem' := s.mem.write16 sp' v
  { s with regSP := sp', mem := mem' }

def State.pop16 (s : State) : State × Word :=
  let v := s.mem.read16 s.regSP
  ({ s with regSP := s.regSP + 2 }, v)

end Z80
