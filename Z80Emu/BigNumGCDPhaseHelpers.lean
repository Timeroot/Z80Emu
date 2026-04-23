import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.MemoryModel

/-!
# BigNum GCD — Phase Proof Helpers

Infrastructure for proving the four Z80 phase lemmas (compare, subtract_a,
subtract_b, output) that connect the Z80 emulator to the pure algorithm.

## Key results

* Program byte extraction from `encodeProgram (bigGcdProgram n)`
* `MemRegion` read helpers
* One-step decode-execute lemmas for Z80 instructions
-/

namespace Z80.BigNumGCDPhaseHelpers

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness

-- ═══════════════════════════════════════════════════════
-- §1  Program byte extraction
-- ═══════════════════════════════════════════════════════

/-- The encoded program always has exactly progSize = 104 bytes. -/
theorem encodeProgram_length (n : Nat) :
    (encodeProgram (bigGcdProgram n)).length = progSize := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize]

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
/-- Output section bytes (positions 88-103). -/
theorem encodeProgram_drop_88 (n : Nat) :
    (encodeProgram (bigGcdProgram n)).drop 88 =
    [0x21, 0x68, 0x00, 0x01, lo16 n.toUInt16, hi16 n.toUInt16,
     0x7E, 0xD3, 0x00, 0x23, 0x0B, 0x78, 0xB1, 0x20, 0xF7, 0x76] := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode,
        List.drop, progSize, lo16, hi16]

-- ═══════════════════════════════════════════════════════
-- §2  MemRegion read helpers
-- ═══════════════════════════════════════════════════════

/-- Read from a MemRegion at a specific offset. -/
theorem MemRegion_read {m : Memory} {base : Nat} {bytes : List UInt8}
    (hmr : ∀ (i : Nat) (hi : i < bytes.length), m.read (base + i).toUInt16 = bytes[i])
    (i : Nat) (hi : i < bytes.length) :
    m.read (base + i).toUInt16 = bytes[i] :=
  hmr i hi

-- ═══════════════════════════════════════════════════════
-- §3  Step through a known instruction
-- ═══════════════════════════════════════════════════════

/-- `run s 0 = s` -/
@[simp] theorem run_zero (s : State) : run s 0 = s := rfl

/-- `run s (n+1)` unfolds to `step` then `run`. -/
theorem run_succ (s : State) (n : Nat) :
    run s (n + 1) = if s.halted then s else run (step s) n := by
  rfl

/-- `step` when not halted. -/
theorem step_not_halted (s : State) (hnh : s.halted = false) :
    step s = exec
      { s with regR := (s.regR &&& 0x80) ||| ((s.regR + 1) &&& 0x7F) }
      (decodeMem s.mem s.regPC).instr
      (decodeMem s.mem s.regPC).len := by
  simp [step, hnh]

-- ═══════════════════════════════════════════════════════
-- §4  run_add (step composition)
-- ═══════════════════════════════════════════════════════

theorem run_halted (s : State) (n : Nat) (h : s.halted = true) :
    run s n = s := by
  induction n with
  | zero => rfl
  | succ n _ => simp [run, h]

theorem run_add (s : State) (m n : Nat) :
    run s (m + n) = run (run s m) n := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add, run]
    split
    · rename_i hh; exact (run_halted s n hh).symm
    · exact ih (step s)

/-
═══════════════════════════════════════════════════════
§5  UInt16 roundtrip
═══════════════════════════════════════════════════════

Splitting a Word into hi/lo bytes and recombining gives the original.
-/
theorem mkWord_hi_lo (w : Word) : mkWord (hi16 w) (lo16 w) = w := by
  cases w;
  native_decide +revert

-- ═══════════════════════════════════════════════════════
-- §6  UInt16 hi/lo byte roundtrip
-- ═══════════════════════════════════════════════════════

theorem uint16_hilo_roundtrip (w : UInt16) :
    UInt8.toUInt16 (UInt16.toUInt8 (w >>> 8)) <<< 8 ||| UInt8.toUInt16 (UInt16.toUInt8 w) = w := by
  cases w; native_decide +revert

theorem uint16_hilo_or_eq_zero_iff (w : UInt16) :
    (UInt16.toUInt8 (w >>> 8) ||| UInt16.toUInt8 w) = 0 ↔ w = 0 := by
  cases w; native_decide +revert

-- After DEC16 BC, the new BC value
theorem dec16_bc_eq (b c : UInt8) :
    (UInt8.toUInt16 b <<< 8 ||| UInt8.toUInt16 c) - (1 : UInt16) =
    UInt8.toUInt16 (UInt16.toUInt8 (((UInt8.toUInt16 b <<< 8 ||| UInt8.toUInt16 c) - (1 : UInt16)) >>> 8)) <<< 8 |||
    UInt8.toUInt16 (UInt16.toUInt8 ((UInt8.toUInt16 b <<< 8 ||| UInt8.toUInt16 c) - (1 : UInt16))) := by
  exact (uint16_hilo_roundtrip _).symm

-- ═══════════════════════════════════════════════════════
-- §7  Extract program byte at a specific position
-- ═══════════════════════════════════════════════════════

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
/-- Output section fixed byte values (positions 94-103 are constant). -/
theorem output_fixed_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 94 0 = 0x7E ∧
    (encodeProgram (bigGcdProgram n)).getD 95 0 = 0xD3 ∧
    (encodeProgram (bigGcdProgram n)).getD 96 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 97 0 = 0x23 ∧
    (encodeProgram (bigGcdProgram n)).getD 98 0 = 0x0B ∧
    (encodeProgram (bigGcdProgram n)).getD 99 0 = 0x78 ∧
    (encodeProgram (bigGcdProgram n)).getD 100 0 = 0xB1 ∧
    (encodeProgram (bigGcdProgram n)).getD 101 0 = 0x20 ∧
    (encodeProgram (bigGcdProgram n)).getD 102 0 = 0xF7 ∧
    (encodeProgram (bigGcdProgram n)).getD 103 0 = 0x76 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize]

/-- Read a byte from memory at a position within the program region. -/
theorem read_prog_byte (m : Memory) (n pos : Nat) (hpos : pos < 104)
    (hprog : ∀ (i : Nat) (_ : i < (encodeProgram (bigGcdProgram n)).length),
      m.read (0 + i).toUInt16 = (encodeProgram (bigGcdProgram n))[i]) :
    m.read pos.toUInt16 = (encodeProgram (bigGcdProgram n)).getD pos 0 := by
  have hlen : (encodeProgram (bigGcdProgram n)).length = 104 := encodeProgram_length n
  have hlt : pos < (encodeProgram (bigGcdProgram n)).length := hlen ▸ hpos
  have h := hprog pos hlt
  simp at h
  rw [h]; simp [List.getD, List.getElem?_eq_getElem hlt]

end Z80.BigNumGCDPhaseHelpers
