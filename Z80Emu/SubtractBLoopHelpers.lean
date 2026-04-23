import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.MemoryModel
import Z80Emu.BigNumGCDPhaseHelpers
import Z80Emu.SubtractPhaseProof
import Z80Emu.SubtractLoopProof
import Z80Emu.CompareLoopHelpers
import Z80Emu.SubtractALoopProof

namespace Z80.SubtractBLoopHelpers

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers
open Z80.SubtractPhaseProof Z80.SubtractLoopProof Z80.CompareLoopHelpers
open Z80.SubtractALoopProof

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_loop_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 68 0 = 0x7E ∧
    (encodeProgram (bigGcdProgram n)).getD 69 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 70 0 = 0x9E ∧
    (encodeProgram (bigGcdProgram n)).getD 71 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 72 0 = 0x77 ∧
    (encodeProgram (bigGcdProgram n)).getD 73 0 = 0x23 ∧
    (encodeProgram (bigGcdProgram n)).getD 74 0 = 0x13 ∧
    (encodeProgram (bigGcdProgram n)).getD 75 0 = 0x0B ∧
    (encodeProgram (bigGcdProgram n)).getD 76 0 = 0xF5 ∧
    (encodeProgram (bigGcdProgram n)).getD 77 0 = 0x78 ∧
    (encodeProgram (bigGcdProgram n)).getD 78 0 = 0xB1 ∧
    (encodeProgram (bigGcdProgram n)).getD 79 0 = 0x28 ∧
    (encodeProgram (bigGcdProgram n)).getD 80 0 = 0x03 ∧
    (encodeProgram (bigGcdProgram n)).getD 81 0 = 0xF1 ∧
    (encodeProgram (bigGcdProgram n)).getD 82 0 = 0x18 ∧
    (encodeProgram (bigGcdProgram n)).getD 83 0 = 0xF0 ∧
    (encodeProgram (bigGcdProgram n)).getD 84 0 = 0xF1 ∧
    (encodeProgram (bigGcdProgram n)).getD 85 0 = 0xC3 ∧
    (encodeProgram (bigGcdProgram n)).getD 86 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 87 0 = 0x00 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize]

private theorem pb_b (m : Memory) (n pos : Nat) (val : UInt8)
    (hprog : ∀ p, p < 104 → m.read p.toUInt16 = (encodeProgram (bigGcdProgram n)).getD p 0)
    (hpos : pos < 104) (hval : (encodeProgram (bigGcdProgram n)).getD pos 0 = val) :
    m.read pos.toUInt16 = val := (hprog pos hpos).trans hval

set_option maxHeartbeats 1600000000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_first5 (s : State)
    (hpc : s.regPC = 68) (hnh : s.halted = false)
    (h68 : s.mem.read 68 = 0x7E) (h69 : s.mem.read 69 = 0xEB)
    (h70 : s.mem.read 70 = 0x9E) (h71 : s.mem.read 71 = 0xEB)
    (h72 : s.mem.read 72 = 0x77) :
    let s5 := run s 5
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    s5.regPC = 73 ∧ s5.halted = false ∧
    s5.regA = result ∧ s5.regF = flags ∧
    s5.regSP = s.regSP ∧ s5.output = s.output ∧
    s5.regH = s.regH ∧ s5.regL = s.regL ∧
    s5.regB = s.regB ∧ s5.regC = s.regC ∧
    s5.regD = s.regD ∧ s5.regE = s.regE ∧
    s5.mem = s.mem.write s.hl result := by
  simp only [show (5 : Nat) = 1+1+1+1+1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h68, h69, h70, h71, h72,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]

theorem sub_b_inc_dec (s : State)
    (hpc : s.regPC = 73) (hnh : s.halted = false)
    (h73 : s.mem.read 73 = 0x23) (h74 : s.mem.read 74 = 0x13)
    (h75 : s.mem.read 75 = 0x0B) :
    let s3 := run s 3
    s3.regPC = 76 ∧ s3.halted = false ∧ s3.mem = s.mem ∧
    s3.regSP = s.regSP ∧ s3.output = s.output ∧
    s3.regA = s.regA ∧ s3.regF = s.regF ∧
    s3.regH = hi16 (s.hl + 1) ∧ s3.regL = lo16 (s.hl + 1) ∧
    s3.regB = hi16 (s.bc - 1) ∧ s3.regC = lo16 (s.bc - 1) ∧
    s3.regD = hi16 (s.de + 1) ∧ s3.regE = lo16 (s.de + 1) := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h73, h74, h75, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend]

set_option maxHeartbeats 6400000 in
theorem sub_b_steps_5_3 (s : State) (n : Nat)
    (hpc : s.regPC = 68) (hnh : s.halted = false)
    (hhl_ge : s.hl.toNat ≥ 104)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536) :
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    let s8 := run s 8
    s8.regPC = 76 ∧ s8.halted = false ∧
    s8.regA = result ∧ s8.regF = flags ∧
    s8.regSP = s.regSP ∧ s8.output = s.output ∧
    s8.regH = hi16 (s.hl + 1) ∧ s8.regL = lo16 (s.hl + 1) ∧
    s8.regD = hi16 (s.de + 1) ∧ s8.regE = lo16 (s.de + 1) ∧
    s8.regB = hi16 (s.bc - 1) ∧ s8.regC = lo16 (s.bc - 1) ∧
    s8.mem = s.mem.write s.hl result ∧
    s8.mem.data.data.size = 65536 := by
  have LB := sub_b_loop_bytes n
  have SF5 := sub_b_first5 s hpc hnh
    (pb_b s.mem n 68 _ hprog (by decide) LB.1)
    (pb_b s.mem n 69 _ hprog (by decide) LB.2.1)
    (pb_b s.mem n 70 _ hprog (by decide) LB.2.2.1)
    (pb_b s.mem n 71 _ hprog (by decide) LB.2.2.2.1)
    (pb_b s.mem n 72 _ hprog (by decide) LB.2.2.2.2.1)
  have prog_read : ∀ pos, pos < 104 → (run s 5).mem.read pos.toUInt16 = s.mem.read pos.toUInt16 := by
    intro pos hpos; rw [SF5.2.2.2.2.2.2.2.2.2.2.2.2]
    exact prog_byte_preserved s.mem s.hl _ pos hpos hmsz hhl_ge
  have h73 : (run s 5).mem.read 73 = 0x23 := by
    convert prog_read 73 (by decide) ▸ pb_b s.mem n 73 _ hprog (by decide) LB.2.2.2.2.2.1
  have h74 : (run s 5).mem.read 74 = 0x13 := by
    convert prog_read 74 (by decide) ▸ pb_b s.mem n 74 _ hprog (by decide) LB.2.2.2.2.2.2.1
  have h75 : (run s 5).mem.read 75 = 0x0B := by
    convert prog_read 75 (by decide) ▸ pb_b s.mem n 75 _ hprog (by decide) LB.2.2.2.2.2.2.2.1
  have INC := sub_b_inc_dec (run s 5) SF5.1 SF5.2.1 h73 h74 h75
  rw [show run s 8 = run (run s 5) 3 from run_add' s 5 3]
  simp_all +decide [State.hl, State.de, State.bc]
  convert Memory.write_size s.mem (mkWord s.regH s.regL)
    (sub8 (s.mem.read (mkWord s.regH s.regL)) (s.mem.read (mkWord s.regD s.regE)) s.regF.c |>.1) hmsz using 1

/-! ## B-loop PUSH/test/POP building blocks at PC=76 -/

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_push_af (s : State)
    (hpc : s.regPC = 76) (hnh : s.halted = false)
    (h76 : s.mem.read 76 = 0xF5) (hsp : s.regSP = 0x8000) :
    let s1 := run s 1
    s1.regPC = 77 ∧ s1.halted = false ∧
    s1.regSP = 0x7FFE ∧ s1.output = s.output ∧
    s1.mem = s.mem.write16 0x7FFE s.af ∧
    s1.regA = s.regA ∧ s1.regF = s.regF ∧
    s1.regH = s.regH ∧ s1.regL = s.regL ∧
    s1.regB = s.regB ∧ s1.regC = s.regC ∧
    s1.regD = s.regD ∧ s1.regE = s.regE := by
  simp only [show (1 : Nat) = 1 from rfl, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h76, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                readReg16s, writeReg16s,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                State.push16,
                mkWord, lo16, hi16, Memory.read16, Memory.write16, evalCond, signExtend,
                hsp]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_test_bc (s : State)
    (hpc : s.regPC = 77) (hnh : s.halted = false)
    (h77 : s.mem.read 77 = 0x78) (h78 : s.mem.read 78 = 0xB1) :
    let s2 := run s 2
    s2.regPC = 79 ∧ s2.halted = false ∧
    s2.regSP = s.regSP ∧ s2.output = s.output ∧
    s2.mem = s.mem ∧
    s2.regA = s.regB ||| s.regC ∧
    s2.regH = s.regH ∧ s2.regL = s.regL ∧
    s2.regB = s.regB ∧ s2.regC = s.regC ∧
    s2.regD = s.regD ∧ s2.regE = s.regE ∧
    s2.regF.z = (s.regB ||| s.regC == 0) := by
  simp only [show (2 : Nat) = 1 + 1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h77, h78, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_pop_continue (s : State)
    (hpc : s.regPC = 79) (hnh : s.halted = false)
    (h79 : s.mem.read 79 = 0x28) (h80 : s.mem.read 80 = 0x03)
    (h81 : s.mem.read 81 = 0xF1) (h82 : s.mem.read 82 = 0x18)
    (h83 : s.mem.read 83 = 0xF0)
    (hfz : s.regF.z = false) (hsp : s.regSP = 0x7FFE) :
    let s3 := run s 3
    s3.regPC = 68 ∧ s3.halted = false ∧ s3.regSP = 0x8000 ∧
    s3.output = s.output ∧
    s3.regA = hi16 (s.mem.read16 0x7FFE) ∧
    s3.regF = Flags.ofByte (lo16 (s.mem.read16 0x7FFE)) ∧
    s3.regH = s.regH ∧ s3.regL = s.regL ∧
    s3.regB = s.regB ∧ s3.regC = s.regC ∧
    s3.regD = s.regD ∧ s3.regE = s.regE ∧
    s3.mem = s.mem := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h79, h80, h81, h82, h83, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                readReg16s, writeReg16s,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                State.pop16,
                mkWord, lo16, hi16, Memory.read16, Memory.write16, evalCond, signExtend,
                hfz, hsp]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_pop_done (s : State)
    (hpc : s.regPC = 79) (hnh : s.halted = false)
    (h79 : s.mem.read 79 = 0x28) (h80 : s.mem.read 80 = 0x03)
    (h84 : s.mem.read 84 = 0xF1)
    (h85 : s.mem.read 85 = 0xC3) (h86 : s.mem.read 86 = 0x00)
    (h87 : s.mem.read 87 = 0x00)
    (hfz : s.regF.z = true) (hsp : s.regSP = 0x7FFE) :
    let s3 := run s 3
    s3.regPC = 0 ∧ s3.halted = false ∧ s3.regSP = 0x8000 ∧
    s3.output = s.output ∧
    s3.regA = hi16 (s.mem.read16 0x7FFE) ∧
    s3.regF = Flags.ofByte (lo16 (s.mem.read16 0x7FFE)) ∧
    s3.regH = s.regH ∧ s3.regL = s.regL ∧
    s3.regB = s.regB ∧ s3.regC = s.regC ∧
    s3.regD = s.regD ∧ s3.regE = s.regE ∧
    s3.mem = s.mem := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h79, h80, h84, h85, h86, h87, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                readReg16s, writeReg16s,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                State.pop16,
                mkWord, lo16, hi16, Memory.read16, Memory.write16, evalCond, signExtend,
                hfz, hsp]

/-! ## B-loop combined push/test/pop helpers -/

set_option maxHeartbeats 6400000 in
theorem sub_b_push_test_pop_continue (s : State) (n : Nat)
    (hpc : s.regPC = 76) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536)
    (hbc_ne : s.regB ||| s.regC ≠ 0) :
    let s6 := run s 6
    s6.regPC = 68 ∧ s6.halted = false ∧ s6.regSP = 0x8000 ∧
    s6.output = s.output ∧
    s6.regA = s.regA ∧ s6.regF = s.regF ∧
    s6.regH = s.regH ∧ s6.regL = s.regL ∧
    s6.regD = s.regD ∧ s6.regE = s.regE ∧
    s6.regB = s.regB ∧ s6.regC = s.regC ∧
    s6.mem = s.mem.write16 0x7FFE s.af ∧
    s6.mem.data.data.size = 65536 := by
  have LB := sub_b_loop_bytes n
  have h1 := sub_b_push_af s hpc hnh (hprog 76 (by decide)) hsp
  have h2 := sub_b_test_bc (run s 1) h1.1 h1.2.1 (by
    rw [h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 77 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 78 (by decide)
    · decide +revert
    · exact hmsz)
  have h3 := sub_b_pop_continue (run (run s 1) 2) h2.1 h2.2.1 (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 79 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 80 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 81 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 82 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 83 (by decide)
    · decide +revert
    · exact hmsz) (by
    aesop) (by
    grind)
  simp_all +decide [← run_add']
  rw [read16_write16_same] <;> norm_num [hmsz]
  · exact ⟨af_roundtrip_hi _ _, af_roundtrip_lo _ _, write16_size _ _ _ hmsz⟩
  · decide +revert

set_option maxHeartbeats 6400000 in
theorem sub_b_push_test_pop_done (s : State) (n : Nat)
    (hpc : s.regPC = 76) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536)
    (hbc_eq : s.regB ||| s.regC = 0) :
    let s6 := run s 6
    s6.regPC = 0 ∧ s6.halted = false ∧ s6.regSP = 0x8000 ∧
    s6.output = s.output ∧
    s6.regA = s.regA ∧ s6.regF = s.regF ∧
    s6.regH = s.regH ∧ s6.regL = s.regL ∧
    s6.regD = s.regD ∧ s6.regE = s.regE ∧
    s6.regB = s.regB ∧ s6.regC = s.regC ∧
    s6.mem = s.mem.write16 0x7FFE s.af ∧
    s6.mem.data.data.size = 65536 := by
  have LB := sub_b_loop_bytes n
  have h1 := sub_b_push_af s hpc hnh (hprog 76 (by decide)) hsp
  have h2 := sub_b_test_bc (run s 1) h1.1 h1.2.1 (by
    rw [h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 77 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 78 (by decide)
    · decide +revert
    · exact hmsz)
  have h3 := sub_b_pop_done (run (run s 1) 2) h2.1 h2.2.1 (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 79 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 80 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 84 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 85 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 86 (by decide)
    · decide +revert
    · exact hmsz) (by
    rw [h2.2.2.2.2.1, h1.2.2.2.2.1]
    rw [read_preserved_write16_stack]
    · exact hprog 87 (by decide)
    · decide +revert
    · exact hmsz) (by
    aesop) (by
    grind)
  simp_all +decide [← run_add']
  rw [read16_write16_same] <;> norm_num [hmsz]
  · exact ⟨af_roundtrip_hi _ _, af_roundtrip_lo _ _, write16_size _ _ _ hmsz⟩
  · decide +revert

/-! ## B-loop one-iteration composed helpers -/

set_option maxHeartbeats 6400000 in
theorem sub_b_one_iter_continue (s : State) (n : Nat)
    (hpc : s.regPC = 68) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
    (hhl_ge : s.hl.toNat ≥ 104) (hhl_lt : s.hl.toNat < 0x7FFE)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536)
    (hbc_ne : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) ≠ 0) :
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    let s14 := run s 14
    s14.regPC = 68 ∧ s14.halted = false ∧ s14.regSP = 0x8000 ∧
    s14.output = s.output ∧
    s14.hl = s.hl + 1 ∧ s14.de = s.de + 1 ∧ s14.bc = s.bc - 1 ∧
    s14.regF.c = flags.c ∧
    s14.mem.read s.hl = result ∧
    (∀ addr : Word, addr ≠ s.hl → addr.toNat < 0x7FFE → s14.mem.read addr = s.mem.read addr) ∧
    (∀ pos, pos < 104 → s14.mem.read pos.toUInt16 = s.mem.read pos.toUInt16) ∧
    s14.mem.data.data.size = 65536 := by
  have := sub_b_steps_5_3 s n hpc hnh hhl_ge hprog hmsz;
  have := sub_b_push_test_pop_continue (run s 8) n this.1 this.2.1 ( by aesop ) ?_ ?_ ?_ <;> simp_all +decide [ State.hl, State.de, State.bc ];
  · rw [ show run s 14 = run ( run s 8 ) 6 by rw [ ← run_add' ] ] ; simp_all +decide [ State.hl, State.de, State.bc ] ;
    refine' ⟨ _, _, _, _, _, _, _ ⟩ <;> try exact mkWord_hi_lo _;
    · apply read_hl_through_writes;
      · exact hhl_lt;
      · exact hmsz;
    · intro addr haddr haddr_lt; apply read_data_through_writes; exact haddr; exact haddr_lt; exact hmsz;
    · intro pos hpos;
      rw [ ← hprog pos hpos ];
      apply read_prog_through_writes;
      · exact hpos;
      · exact hhl_ge;
      · exact hmsz;
    · grind;
  · intro pos hpos; rw [ ← hprog pos hpos ] ; apply prog_byte_preserved; exact hpos; exact hmsz; exact hhl_ge;
  · grind +splitIndPred

set_option maxHeartbeats 6400000 in
theorem sub_b_one_iter_done (s : State) (n : Nat)
    (hpc : s.regPC = 68) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
    (hhl_ge : s.hl.toNat ≥ 104) (hhl_lt : s.hl.toNat < 0x7FFE)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536)
    (hbc_eq : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) = 0) :
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    let s14 := run s 14
    s14.regPC = 0 ∧ s14.halted = false ∧ s14.regSP = 0x8000 ∧
    s14.output = s.output ∧
    s14.mem.read s.hl = result ∧
    (∀ addr : Word, addr ≠ s.hl → addr.toNat < 0x7FFE → s14.mem.read addr = s.mem.read addr) ∧
    (∀ pos, pos < 104 → s14.mem.read pos.toUInt16 = s.mem.read pos.toUInt16) ∧
    s14.mem.data.data.size = 65536 := by
  have := @sub_b_steps_5_3; specialize this s n hpc hnh hhl_ge hprog hmsz; ( have := @sub_b_push_test_pop_done; rename_i h; specialize this (run s 8) n; ( ( specialize this ( by aesop ) ( by aesop ) ( by aesop ) ) ) ) ; (
  have := @run_add' s 8 6; simp_all +decide [run_add'] ; (
  rename_i h';
  specialize h' (by
  intro pos hpos; rw [ ← hprog pos hpos ] ; apply read_prog_through_data_write; exact hpos; exact hhl_ge; exact hmsz;) (by
  grind);
  refine' ⟨ h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, _, _, _, h'.2.2.2.2.2.2.2.2.2.2.2.2.2 ⟩ <;> simp_all +decide [ Memory.write16 ];
  · apply read_hl_through_writes; exact hhl_lt; exact hmsz;
  · intros addr haddr haddr_lt
    apply read_data_through_writes s.mem s.hl (sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).1 (run s 8).af addr haddr haddr_lt hmsz;
  · intro pos hpos; rw [ ← hprog pos hpos ] ; apply read_prog_through_writes; exact hpos; exact hhl_ge; exact hmsz;))

/-! ## §7 Subtract-B loop -/

set_option maxHeartbeats 12800000 in
theorem subtract_b_loop
    (n : Nat) (aBytes bBytes : List UInt8)
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hfits : 104 + 2 * n < 0x8000)
    (rem : Nat) (borrow : Nat)
    (hrem : 0 < rem) (hremn : rem ≤ n) (hb : borrow ≤ 1) (hrem65 : rem ≤ 65535)
    (s : State)
    (hpc : s.regPC = 68) (hnh : s.halted = false) (hsp : s.regSP = 0x8000) (hout : s.output = [])
    (hhl : s.hl = (104 + n + (n - rem)).toUInt16)
    (hde : s.de = (104 + (n - rem)).toUInt16)
    (hbc : s.bc = rem.toUInt16)
    (hcarry : s.regF.c = decide (borrow = 1))
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hbRem : ∀ j, j < rem → s.mem.read (104 + n + (n - rem) + j).toUInt16 =
      bBytes.getD (n - rem + j) 0)
    (haAll : ∀ j, j < n → s.mem.read (104 + j).toUInt16 =
      aBytes.getD j 0)
    (hmsz : s.mem.data.data.size = 65536) :
    ∃ k,
      (run s k).regPC = 0 ∧ (run s k).regSP = 0x8000 ∧
      (run s k).halted = false ∧ (run s k).output = [] ∧
      (∀ j, j < rem → (run s k).mem.read (104 + n + (n - rem) + j).toUInt16 =
        (bigSub.go (List.drop (n - rem) bBytes) (List.drop (n - rem) aBytes) borrow).getD j 0) ∧
      (∀ j, j < n - rem → (run s k).mem.read (104 + n + j).toUInt16 =
        s.mem.read (104 + n + j).toUInt16) ∧
      (∀ j, j < n → (run s k).mem.read (104 + j).toUInt16 =
        aBytes.getD j 0) ∧
      (∀ pos, pos < 104 → (run s k).mem.read pos.toUInt16 =
        (encodeProgram (bigGcdProgram n)).getD pos 0) ∧
      (run s k).mem.data.data.size = 65536 := by
  revert hrem hremn hrem65 borrow hb s hpc hnh hsp hout hhl hde hbc hcarry hprog hbRem haAll hmsz;
  intro borrow hrem hremn hb hrem65 s hpc hnh hsp hout hhl hde hbc hcarry hprog hbRem haAll hmsz
  induction' rem with rem' ih generalizing borrow s;
  · contradiction;
  · by_cases hrem' : 0 < rem';
    · have hhl_ge : s.hl.toNat ≥ 104 := by
        rw [ hhl ] ; norm_num [ Nat.add_mod, Nat.mul_mod ] ; omega;
      have hhl_lt : s.hl.toNat < 0x7FFE := by
        rw [ hhl ] ; norm_num [ Nat.add_mod, Nat.mul_mod ] ; omega;
      have hbc_ne : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) ≠ 0 := by
        rw [ hbc ];
        convert hilo_or_ne_zero rem' hrem' ( by linarith ) using 1;
        norm_num [ hi16, lo16, Nat.toUInt16 ]
      have IT := sub_b_one_iter_continue s n hpc hnh hsp hhl_ge hhl_lt hprog hmsz hbc_ne
      simp_all +decide only [Nat.add_sub_assoc];
      obtain ⟨k', hk'⟩ := ih (if (sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).2.c then 1 else 0) trivial (by omega) (by
      split_ifs <;> norm_num) (by omega) (run s 14) IT.1 IT.2.1 IT.2.2.1 IT.2.2.2.1 (by
      convert IT.2.2.2.2.1 using 1;
      norm_num [ ← UInt16.toNat_inj ];
      grind) (by
      convert IT.2.2.2.2.2.1 using 1;
      norm_num [ ← UInt16.toNat_inj ];
      grind) (by
      rw [ IT.2.2.2.2.2.2.1 ];
      norm_num [ Nat.mod_eq_of_lt ( by linarith : rem' + 1 < 65536 ) ]) (by
      grind +extAll) (by
      exact IT.2.2.2.2.2.2.2.2.2.2.1) (by
      intro j hj;
      convert hbRem ( j + 1 ) ( by linarith ) using 1;
      · rw [ IT.2.2.2.2.2.2.2.2.2.1 ];
        · rw [ show n - rem' = n - ( rem' + 1 ) + 1 by omega ] ; ring;
        · norm_num [ UInt16.ext_iff ];
          omega;
        · simp +zetaDelta at *;
          omega;
      · rw [ show n - rem' = n - ( rem' + 1 ) + 1 by omega ] ; ring) (by
      intro j hj;
      convert haAll j hj using 1;
      apply IT.2.2.2.2.2.2.2.2.2.1;
      · norm_num [ ← UInt16.toNat_inj ];
        omega;
      · exact Nat.lt_of_le_of_lt ( Nat.mod_le _ _ ) ( by linarith )) (by
      exact IT.2.2.2.2.2.2.2.2.2.2.2);
      use 14 + k';
      rw [ run_add ];
      refine' ⟨ hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, _, _, hk'.2.2.2.2.2.2.1, hk'.2.2.2.2.2.2.2.1, hk'.2.2.2.2.2.2.2.2 ⟩;
      · intro j hj
        by_cases hj0 : j = 0;
        · convert IT.2.2.2.2.2.2.2.2.1 using 1;
          · rw [ hj0 ];
            grind;
          · rw [ sub8_eq_bigSub_byte ];
            · convert bigSub_go_drop_getD_zero _ _ _ _ _ _ using 1;
              rotate_left;
              exact bBytes;
              exact aBytes;
              exact n;
              exact n - ( rem' + 1 );
              exact borrow;
              · exact hbL;
              · simp +decide [ hj0, hbRem, haAll, hhl, hde ];
                rw [ show s.mem.read ( 104 + UInt16.ofNat n + UInt16.ofNat ( n - ( rem' + 1 ) ) ) = bBytes[n - ( rem' + 1 ) ]?.getD 0 from ?_, show s.mem.read ( 104 + UInt16.ofNat ( n - ( rem' + 1 ) ) ) = aBytes[n - ( rem' + 1 ) ]?.getD 0 from ?_ ];
                · grind;
                · convert haAll ( n - ( rem' + 1 ) ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) using 1;
                  norm_num [ UInt16.toNat_ofNat, Nat.mod_eq_of_lt ( show 104 + ( n - ( rem' + 1 ) ) < 65536 from by omega ) ];
                  norm_num [ UInt16.ofNat ];
                · convert hbRem 0 ( by linarith ) using 1;
                  norm_num [ add_assoc, Nat.add_mod, Nat.mod_eq_of_lt hfits ];
                  congr;
            · linarith;
        · convert hk'.2.2.2.2.1 ( j - 1 ) ( by omega ) using 1;
          · rw [ show n - rem' = n - ( rem' + 1 ) + 1 by omega ] ; ring;
            rw [ show 105 + n + ( n - ( 1 + rem' ) ) + ( j - 1 ) = 104 + n + ( n - ( 1 + rem' ) ) + j by omega ];
          · convert bigSub_go_drop_getD_succ _ _ _ _ _ _ using 1;
            rotate_left;
            exact bBytes;
            exact aBytes;
            exact n;
            exact n - ( rem' + 1 );
            exact borrow;
            exact j - 1;
            rw [ show s.mem.read s.hl = bBytes.getD ( n - ( rem' + 1 ) ) 0 from ?_, show s.mem.read s.de = aBytes.getD ( n - ( rem' + 1 ) ) 0 from ?_ ];
            · simp +decide [ sub8, hcarry ];
              grind;
            · grind;
            · convert hbRem 0 ( by linarith ) using 1;
              simp +decide [ hhl ];
      · intro j hj;
        convert hk'.2.2.2.2.2.1 j ( by omega ) using 1;
        rw [ IT.2.2.2.2.2.2.2.2.2.1 ];
        · norm_num [ ← UInt16.toNat_inj ];
          rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega;
        · exact Nat.lt_of_le_of_lt ( Nat.mod_le _ _ ) ( by omega );
    · have := sub_b_one_iter_done s n hpc hnh hsp ( by
        rw [ hhl ] ; simp +decide [ Nat.toUInt16 ] ; omega; ) ( by
        rw [ hhl ] ; norm_num [ Nat.add_mod, Nat.mul_mod ] ; omega; ) hprog hmsz ( by
        aesop );
      use 14;
      refine' ⟨ this.1, this.2.2.1, this.2.1, this.2.2.2.1.trans hout, _, _, _, _ ⟩;
      · intro j hj; specialize hbRem j hj; specialize haAll ( n - ( rem' + 1 ) + j ) ; simp_all +decide [ Nat.sub_add_comm ( by linarith : rem' + 1 ≤ n ) ] ;
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ List.drop ];
        · rcases aBytes with ( _ | ⟨ a, _ | ⟨ b, aBytes ⟩ ⟩ ) <;> rcases bBytes with ( _ | ⟨ c, _ | ⟨ d, bBytes ⟩ ⟩ ) <;> simp_all +decide [ sub8, bigSub.go ];
          all_goals norm_num at *;
          · contradiction;
          · contradiction;
          · interval_cases borrow <;> rfl;
        · rw [ List.drop_eq_getElem_cons ];
          rw [ List.drop_eq_nil_of_le ] <;> norm_num [ haL, hbL ];
          rw [ List.drop_eq_getElem_cons ];
          any_goals linarith;
          interval_cases borrow <;> simp +decide [ sub8, bigSub.go ];
      · intro j hj;
        convert this.2.2.2.2.2.1 _ _ _ using 1;
        · simp +decide [ hhl ];
          simp +decide [ UInt16.ext_iff ];
          rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega;
        · norm_num [ Nat.toUInt16 ];
          omega;
      · intro j hj;
        convert this.2.2.2.2.2.1 ( 104 + j |> Nat.toUInt16 ) _ _ using 1;
        · rw [ haAll j hj ];
        · rw [ hhl ];
          norm_num [ UInt16.ext_iff ];
          omega;
        · exact Nat.lt_of_le_of_lt ( Nat.mod_le _ _ ) ( by linarith );
      · grind

/-! ## §8 B-loop setup bytes -/

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_setup_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 58 0 = 0x21 ∧
    (encodeProgram (bigGcdProgram n)).getD 59 0 = lo16 (104 + n).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 60 0 = hi16 (104 + n).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 61 0 = 0x11 ∧
    (encodeProgram (bigGcdProgram n)).getD 62 0 = 0x68 ∧
    (encodeProgram (bigGcdProgram n)).getD 63 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 64 0 = 0x01 ∧
    (encodeProgram (bigGcdProgram n)).getD 65 0 = lo16 n.toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 66 0 = hi16 n.toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 67 0 = 0xB7 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize, lo16, hi16]

/-! ## §9 B-loop setup phase (PC 58 → 68) -/

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem sub_b_setup4 (s : State) (n : Nat)
    (hpc : s.regPC = 58) (hnh : s.halted = false)
    (h58 : s.mem.read 58 = 0x21) (h59 : s.mem.read 59 = lo16 (104 + n).toUInt16)
    (h60 : s.mem.read 60 = hi16 (104 + n).toUInt16) (h61 : s.mem.read 61 = 0x11)
    (h62 : s.mem.read 62 = 0x68)
    (h63 : s.mem.read 63 = 0x00) (h64 : s.mem.read 64 = 0x01)
    (h65 : s.mem.read 65 = lo16 n.toUInt16)
    (h66 : s.mem.read 66 = hi16 n.toUInt16) (h67 : s.mem.read 67 = 0xB7) :
    let s4 := run s 4
    s4.regPC = 68 ∧ s4.halted = false ∧
    s4.mem = s.mem ∧ s4.regSP = s.regSP ∧ s4.output = s.output ∧
    s4.regH = hi16 (104 + n).toUInt16 ∧ s4.regL = lo16 (104 + n).toUInt16 ∧
    s4.regD = 0x00 ∧ s4.regE = 0x68 ∧
    s4.regB = hi16 n.toUInt16 ∧ s4.regC = lo16 n.toUInt16 ∧
    s4.regF.c = false := by
  contrapose! h67;
  intro h; have := h67; simp_all +decide [ run ] ;
  unfold step at *; simp_all +decide [ decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ, exec, readLoc8, writeLoc8, readReg16, writeReg16, loc8of, reg8of, reg16of, reg16sof, aluOf, condOf, State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF, Memory.read16, evalCond, signExtend, alu8, sub8, add8, parity8, testBit8, Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned ] ;
  exact h67 ( by rw [ mkWord_hi_lo ] ) ( by rw [ mkWord_hi_lo ] ) ( by rw [ mkWord_hi_lo ] ) ( by rw [ mkWord_hi_lo ] )

/-! ## §10 Subtract-B phase = setup + loop -/

theorem subtract_b_phase_impl (s : State) (n : Nat)
    (aBytes bBytes : List UInt8)
    (hpc : s.regPC = 58) (hsp : s.regSP = 0x8000)
    (hnh : s.halted = false)
    (hprog : ∀ (i : Nat) (hi : i < (encodeProgram (bigGcdProgram n)).length),
      s.mem.read (0 + i).toUInt16 = (encodeProgram (bigGcdProgram n))[i])
    (haM : ∀ (i : Nat) (hi : i < aBytes.length),
      s.mem.read (104 + i).toUInt16 = aBytes[i])
    (hbM : ∀ (i : Nat) (hi : i < bBytes.length),
      s.mem.read (104 + n + i).toUInt16 = bBytes[i])
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hout : s.output = [])
    (hfits : 104 + 2 * n < 0x8000) (hnPos : 0 < n)
    (hge : decodeBigNum bBytes ≥ decodeBigNum aBytes)
    (hmsz : s.mem.data.data.size = 65536) :
    ∃ k : Nat,
      (run s k).regPC = 0 ∧ (run s k).regSP = 0x8000 ∧
      (run s k).halted = false ∧ (run s k).output = [] ∧
      (∀ (i : Nat) (hi : i < (encodeProgram (bigGcdProgram n)).length),
        (run s k).mem.read (0 + i).toUInt16 = (encodeProgram (bigGcdProgram n))[i]) ∧
      (∀ (i : Nat) (hi : i < aBytes.length),
        (run s k).mem.read (104 + i).toUInt16 = aBytes[i]) ∧
      (∀ (i : Nat) (hi : i < (bigSub bBytes aBytes).length),
        (run s k).mem.read (104 + n + i).toUInt16 = (bigSub bBytes aBytes)[i]) ∧
      (run s k).mem.data.data.size = 65536 := by
  have h_prog : (encodeProgram (bigGcdProgram n)).length = 104 := by
    unfold bigGcdProgram at * ; aesop ( simp_config := { decide := true } );
  have := sub_b_setup4 s n hpc hnh ( by convert hprog 58 ( by linarith ) using 1 ) ( by convert hprog 59 ( by linarith ) using 1 ) ( by convert hprog 60 ( by linarith ) using 1 ) ( by convert hprog 61 ( by linarith ) using 1 ) ( by convert hprog 62 ( by linarith ) using 1 ) ( by convert hprog 63 ( by linarith ) using 1 ) ( by convert hprog 64 ( by linarith ) using 1 ) ( by convert hprog 65 ( by linarith ) using 1 ) ( by convert hprog 66 ( by linarith ) using 1 ) ( by convert hprog 67 ( by linarith ) using 1 ) ;
  have := subtract_b_loop n aBytes bBytes haL hbL hfits n 0; simp_all +decide [ State.hl, State.de, State.bc ] ;
  specialize this ( by linarith ) ( run s 4 ) ; simp_all +decide [ State.hl, State.de, State.bc ];
  obtain ⟨ k, hk ⟩ := this ( by
    exact mkWord_hi_lo _ ) ( by
    apply mkWord_hi_lo ) ; use 4 + k; simp_all +decide [ run_add' ] ;
  intro i hi; specialize hk; have := hk.2.2.2.2.1 i ( by
    convert hi using 1;
    rw [ bigSub_length ] ; aesop ( simp_config := { decide := true } ) ;
    linarith ) ; simp_all +decide [ bigSub ] ;
  grind

end Z80.SubtractBLoopHelpers