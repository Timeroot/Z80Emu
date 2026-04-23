import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.MemoryModel
import Z80Emu.BigNumGCDPhaseHelpers

/-!
# Subtract Phase Proof

Proves that the subtract loop of the BigNum GCD Z80 program correctly
computes bigSub and returns to the main loop.
-/

namespace Z80.SubtractPhaseProof

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers

/-! ## §1 Memory helpers -/

theorem prog_byte_preserved (m : Memory) (addr : Word) (val : Byte)
    (pos : Nat) (hpos : pos < 104)
    (hmsz : m.data.data.size = 65536)
    (haddr : addr.toNat ≥ 104) :
    (m.write addr val).read pos.toUInt16 = m.read pos.toUInt16 := by
  apply Memory.read_write_diff _ _ _ _ hmsz
  simp [UInt16.ext_iff, UInt16.toNat_ofNat]; omega

theorem read_preserved_write16_stack (m : Memory) (val : Word)
    (addr : Word) (haddr : addr.toNat < 0x7FFE)
    (hmsz : m.data.data.size = 65536) :
    (m.write16 0x7FFE val).read addr = m.read addr := by
  unfold Memory.write16
  rw [Memory.read_write_diff _ _ _ _ (Memory.write_size _ _ _ hmsz)]
  · rw [Memory.read_write_diff _ _ _ _ hmsz]
    simp [UInt16.ext_iff, UInt16.toNat_ofNat]; omega
  · simp [UInt16.ext_iff, UInt16.toNat_ofNat]; omega

theorem write16_size (m : Memory) (addr : Word) (val : Word)
    (hmsz : m.data.data.size = 65536) :
    (m.write16 addr val).data.data.size = 65536 := by
  unfold Memory.write16
  exact Memory.write_size _ _ _ (Memory.write_size _ _ _ hmsz)

/-
Reading back from write16
-/
theorem read16_write16_same (m : Memory) (addr : Word) (val : Word)
    (hmsz : m.data.data.size = 65536)
    (hne : addr ≠ addr + 1) :
    (m.write16 addr val).read16 addr = val := by
  unfold Memory.write16 Memory.read16;
  grind +suggestions

/-! ## §2 Program byte extraction -/

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
theorem subtract_a_fixed_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 28 0 = 0x21 ∧
    (encodeProgram (bigGcdProgram n)).getD 29 0 = 0x68 ∧
    (encodeProgram (bigGcdProgram n)).getD 30 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 31 0 = 0x11 ∧
    (encodeProgram (bigGcdProgram n)).getD 34 0 = 0x01 ∧
    (encodeProgram (bigGcdProgram n)).getD 37 0 = 0xB7 ∧
    (encodeProgram (bigGcdProgram n)).getD 38 0 = 0x7E ∧
    (encodeProgram (bigGcdProgram n)).getD 39 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 40 0 = 0x9E ∧
    (encodeProgram (bigGcdProgram n)).getD 41 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 42 0 = 0x77 ∧
    (encodeProgram (bigGcdProgram n)).getD 43 0 = 0x23 ∧
    (encodeProgram (bigGcdProgram n)).getD 44 0 = 0x13 ∧
    (encodeProgram (bigGcdProgram n)).getD 45 0 = 0x0B ∧
    (encodeProgram (bigGcdProgram n)).getD 46 0 = 0xF5 ∧
    (encodeProgram (bigGcdProgram n)).getD 47 0 = 0x78 ∧
    (encodeProgram (bigGcdProgram n)).getD 48 0 = 0xB1 ∧
    (encodeProgram (bigGcdProgram n)).getD 49 0 = 0x28 ∧
    (encodeProgram (bigGcdProgram n)).getD 50 0 = 0x03 ∧
    (encodeProgram (bigGcdProgram n)).getD 51 0 = 0xF1 ∧
    (encodeProgram (bigGcdProgram n)).getD 52 0 = 0x18 ∧
    (encodeProgram (bigGcdProgram n)).getD 53 0 = 0xF0 ∧
    (encodeProgram (bigGcdProgram n)).getD 54 0 = 0xF1 ∧
    (encodeProgram (bigGcdProgram n)).getD 55 0 = 0xC3 ∧
    (encodeProgram (bigGcdProgram n)).getD 56 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 57 0 = 0x00 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize]

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
theorem subtract_a_param_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 32 0 = lo16 (104 + n).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 33 0 = hi16 (104 + n).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 35 0 = lo16 n.toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 36 0 = hi16 n.toUInt16 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize,
        lo16, hi16]

/-! ## §3 Instruction blocks -/

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
/-- Block A: LD A,(HL); EX DE,HL; SBC A,(HL); EX DE,HL (4 steps). -/
theorem sub_loop_block_a (s : State)
    (hpc : s.regPC = 38) (hnh : s.halted = false)
    (h38 : s.mem.read 38 = 0x7E) (h39 : s.mem.read 39 = 0xEB)
    (h40 : s.mem.read 40 = 0x9E) (h41 : s.mem.read 41 = 0xEB) :
    let s4 := run s 4
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    s4.regPC = 42 ∧ s4.regA = result ∧ s4.regF = flags ∧
    s4.mem = s.mem ∧ s4.halted = false ∧
    s4.regSP = s.regSP ∧ s4.output = s.output ∧
    s4.regH = s.regH ∧ s4.regL = s.regL ∧
    s4.regB = s.regB ∧ s4.regC = s.regC ∧
    s4.regD = s.regD ∧ s4.regE = s.regE := by
  simp only [show (4 : Nat) = 1 + 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h38, h39, h40, h41,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
/-- LD (HL),A (1 step from PC=42). -/
theorem sub_loop_write_step (s : State)
    (hpc : s.regPC = 42) (hnh : s.halted = false)
    (h42 : s.mem.read 42 = 0x77) :
    let s1 := run s 1
    s1.regPC = 43 ∧ s1.halted = false ∧
    s1.mem = s.mem.write s.hl s.regA ∧
    s1.regA = s.regA ∧ s1.regF = s.regF ∧
    s1.regSP = s.regSP ∧ s1.output = s.output ∧
    s1.regH = s.regH ∧ s1.regL = s.regL ∧
    s1.regB = s.regB ∧ s1.regC = s.regC ∧
    s1.regD = s.regD ∧ s1.regE = s.regE := by
  simp only [show (1 : Nat) = 1 from rfl, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h42, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
/-- INC HL; INC DE; DEC BC (3 steps from PC=43). -/
theorem sub_loop_inc_dec (s : State)
    (hpc : s.regPC = 43) (hnh : s.halted = false)
    (h43 : s.mem.read 43 = 0x23) (h44 : s.mem.read 44 = 0x13)
    (h45 : s.mem.read 45 = 0x0B) :
    let s3 := run s 3
    s3.regPC = 46 ∧ s3.halted = false ∧ s3.mem = s.mem ∧
    s3.regSP = s.regSP ∧ s3.output = s.output ∧
    s3.regA = s.regA ∧ s3.regF = s.regF ∧
    s3.regH = hi16 (s.hl + 1) ∧ s3.regL = lo16 (s.hl + 1) ∧
    s3.regB = hi16 (s.bc - 1) ∧ s3.regC = lo16 (s.bc - 1) ∧
    s3.regD = hi16 (s.de + 1) ∧ s3.regE = lo16 (s.de + 1) := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h43, h44, h45, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
/-- PUSH AF (1 step from PC=46). -/
theorem sub_loop_push_af (s : State)
    (hpc : s.regPC = 46) (hnh : s.halted = false)
    (h46 : s.mem.read 46 = 0xF5) (hsp : s.regSP = 0x8000) :
    let s1 := run s 1
    s1.regPC = 47 ∧ s1.halted = false ∧
    s1.regSP = 0x7FFE ∧ s1.output = s.output ∧
    s1.mem = s.mem.write16 0x7FFE s.af ∧
    s1.regA = s.regA ∧ s1.regF = s.regF ∧
    s1.regH = s.regH ∧ s1.regL = s.regL ∧
    s1.regB = s.regB ∧ s1.regC = s.regC ∧
    s1.regD = s.regD ∧ s1.regE = s.regE := by
  simp only [show (1 : Nat) = 1 from rfl, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h46, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                readReg16s, writeReg16s,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                State.push16,
                mkWord, lo16, hi16, Memory.read16, Memory.write16, evalCond, signExtend,
                hsp]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
/-- LD A,B; OR C (2 steps from PC=47). -/
theorem sub_loop_test_bc (s : State)
    (hpc : s.regPC = 47) (hnh : s.halted = false)
    (h47 : s.mem.read 47 = 0x78) (h48 : s.mem.read 48 = 0xB1) :
    let s2 := run s 2
    s2.regPC = 49 ∧ s2.halted = false ∧
    s2.regSP = s.regSP ∧ s2.output = s.output ∧ s2.mem = s.mem ∧
    s2.regH = s.regH ∧ s2.regL = s.regL ∧
    s2.regB = s.regB ∧ s2.regC = s.regC ∧
    s2.regD = s.regD ∧ s2.regE = s.regE ∧
    (s2.regF.z = (s.regB ||| s.regC == 0)) := by
  simp only [show (2 : Nat) = 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h47, h48, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
/-- JR Z (NZ); POP AF; JR -16 (3 steps from PC=49, continuing). -/
theorem sub_loop_pop_continue (s : State)
    (hpc : s.regPC = 49) (hnh : s.halted = false)
    (h49 : s.mem.read 49 = 0x28) (h50 : s.mem.read 50 = 0x03)
    (h51 : s.mem.read 51 = 0xF1)
    (h52 : s.mem.read 52 = 0x18) (h53 : s.mem.read 53 = 0xF0)
    (hfz : s.regF.z = false) (hsp : s.regSP = 0x7FFE) :
    let s3 := run s 3
    s3.regPC = 38 ∧ s3.halted = false ∧
    s3.regSP = 0x8000 ∧ s3.output = s.output ∧
    s3.regA = hi16 (s.mem.read16 0x7FFE) ∧
    s3.regF = Flags.ofByte (lo16 (s.mem.read16 0x7FFE)) ∧
    s3.regH = s.regH ∧ s3.regL = s.regL ∧
    s3.regB = s.regB ∧ s3.regC = s.regC ∧
    s3.regD = s.regD ∧ s3.regE = s.regE ∧
    s3.mem = s.mem := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h49, h50, h51, h52, h53,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                readReg16s, writeReg16s,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                State.pop16,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                hfz, hsp]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
/-- JR Z (Z); POP AF; JP 0 (3 steps from PC=49, done). -/
theorem sub_loop_pop_done (s : State)
    (hpc : s.regPC = 49) (hnh : s.halted = false)
    (h49 : s.mem.read 49 = 0x28) (h50 : s.mem.read 50 = 0x03)
    (h54 : s.mem.read 54 = 0xF1)
    (h55 : s.mem.read 55 = 0xC3) (h56 : s.mem.read 56 = 0x00) (h57 : s.mem.read 57 = 0x00)
    (hfz : s.regF.z = true) (hsp : s.regSP = 0x7FFE) :
    let s3 := run s 3
    s3.regPC = 0 ∧ s3.halted = false ∧
    s3.regSP = 0x8000 ∧ s3.output = s.output ∧
    s3.regA = hi16 (s.mem.read16 0x7FFE) ∧
    s3.regF = Flags.ofByte (lo16 (s.mem.read16 0x7FFE)) ∧
    s3.regH = s.regH ∧ s3.regL = s.regL ∧
    s3.regB = s.regB ∧ s3.regC = s.regC ∧
    s3.regD = s.regD ∧ s3.regE = s.regE ∧
    s3.mem = s.mem := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h49, h50, h54, h55, h56, h57,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                readReg16s, writeReg16s,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                State.pop16,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                hfz, hsp]

/-! ## §4 Roundtrip lemmas -/

theorem flags_roundtrip (f : Flags) : Flags.ofByte (Flags.toByte f) = f := by
  cases f
  cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;>
    cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> trivial

theorem af_roundtrip_hi (a : Byte) (f : Flags) :
    hi16 (mkWord a (Flags.toByte f)) = a := by
  cases a; cases f; native_decide +revert

theorem af_roundtrip_lo (a : Byte) (f : Flags) :
    Flags.ofByte (lo16 (mkWord a (Flags.toByte f))) = f := by
  convert flags_roundtrip f using 1
  have : ∀ (a : Byte) (f : Flags), lo16 (mkWord a f.toByte) = f.toByte := by
    intros a f; cases a; cases f; native_decide +revert
  rw [this]

end Z80.SubtractPhaseProof