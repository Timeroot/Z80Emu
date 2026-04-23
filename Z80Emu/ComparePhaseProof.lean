import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.MemoryModel
import Z80Emu.BigNumGCDPhaseHelpers
import Z80Emu.CompareLoopHelpers
import Z80Emu.CmpLoopProof

/-!
# Compare Phase Proof
-/

namespace Z80.ComparePhaseProof

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers

-- §1 Program byte extraction

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
theorem compare_fixed_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 9 0 = 0x7E ∧
    (encodeProgram (bigGcdProgram n)).getD 10 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 11 0 = 0xBE ∧
    (encodeProgram (bigGcdProgram n)).getD 12 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 13 0 = 0x20 ∧
    (encodeProgram (bigGcdProgram n)).getD 14 0 = 0x0A ∧
    (encodeProgram (bigGcdProgram n)).getD 15 0 = 0x2B ∧
    (encodeProgram (bigGcdProgram n)).getD 16 0 = 0x1B ∧
    (encodeProgram (bigGcdProgram n)).getD 17 0 = 0x0B ∧
    (encodeProgram (bigGcdProgram n)).getD 18 0 = 0x78 ∧
    (encodeProgram (bigGcdProgram n)).getD 19 0 = 0xB1 ∧
    (encodeProgram (bigGcdProgram n)).getD 20 0 = 0x20 ∧
    (encodeProgram (bigGcdProgram n)).getD 21 0 = 0xF3 ∧
    (encodeProgram (bigGcdProgram n)).getD 22 0 = 0xC3 ∧
    (encodeProgram (bigGcdProgram n)).getD 23 0 = 0x58 ∧
    (encodeProgram (bigGcdProgram n)).getD 24 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 25 0 = 0xDA ∧
    (encodeProgram (bigGcdProgram n)).getD 26 0 = 0x3A ∧
    (encodeProgram (bigGcdProgram n)).getD 27 0 = 0x00 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize]

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
theorem compare_param_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 0 0 = 0x21 ∧
    (encodeProgram (bigGcdProgram n)).getD 1 0 = lo16 (progSize + n - 1).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 2 0 = hi16 (progSize + n - 1).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 3 0 = 0x11 ∧
    (encodeProgram (bigGcdProgram n)).getD 4 0 = lo16 (progSize + n + n - 1).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 5 0 = hi16 (progSize + n + n - 1).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 6 0 = 0x01 ∧
    (encodeProgram (bigGcdProgram n)).getD 7 0 = lo16 n.toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 8 0 = hi16 n.toUInt16 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode,
        progSize, lo16, hi16]

-- §2 Setup

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem cmp_setup3 (s : State) (n : Nat)
    (hpc : s.regPC = 0) (hnh : s.halted = false)
    (h0 : s.mem.read 0 = 0x21)
    (h1 : s.mem.read 1 = lo16 (progSize + n - 1).toUInt16)
    (h2 : s.mem.read 2 = hi16 (progSize + n - 1).toUInt16)
    (h3 : s.mem.read 3 = 0x11)
    (h4 : s.mem.read 4 = lo16 (progSize + n + n - 1).toUInt16)
    (h5 : s.mem.read 5 = hi16 (progSize + n + n - 1).toUInt16)
    (h6 : s.mem.read 6 = 0x01)
    (h7 : s.mem.read 7 = lo16 n.toUInt16)
    (h8 : s.mem.read 8 = hi16 n.toUInt16) :
    let s3 := run s 3
    s3.regPC = 9 ∧ s3.halted = false ∧
    s3.mem = s.mem ∧ s3.regSP = s.regSP ∧ s3.output = s.output ∧
    s3.regH = hi16 (progSize + n - 1).toUInt16 ∧
    s3.regL = lo16 (progSize + n - 1).toUInt16 ∧
    s3.regD = hi16 (progSize + n + n - 1).toUInt16 ∧
    s3.regE = lo16 (progSize + n + n - 1).toUInt16 ∧
    s3.regB = hi16 n.toUInt16 ∧
    s3.regC = lo16 n.toUInt16 := by
  by_contra h_contra
  have h_run : run s 3 = run (step s) 2 := if_neg (by simp +decide [hnh])
  rw [h_run, run_succ, run_succ] at h_contra; simp_all +decide [decodeMem, exec]
  unfold step at *
  simp +decide [hpc, hnh, h0, h1, h2, h3, h4, h5, h6, h7, h8, decodeMem, decodeRoot,
    opcX, opcY, opcZ, opcP, opcQ, exec, readLoc8, writeLoc8, readReg16, writeReg16,
    loc8of, reg8of, reg16of, reg16sof, aluOf, condOf, State.hl, State.bc, State.de,
    State.af, State.setHL, State.setBC, State.setDE, State.setAF] at h_contra ⊢
  simp +decide [Memory.read16, h0, h1, h2, h3, h4, h5, h6, h7, h8] at h_contra ⊢
  exact h_contra (by rw [mkWord_hi_lo]) (by rw [mkWord_hi_lo]) (by rw [mkWord_hi_lo])
    (by rw [mkWord_hi_lo]) (by rw [mkWord_hi_lo]) (by rw [mkWord_hi_lo])

-- §3–§7: Instruction building blocks

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem cmp_compare4 (s : State)
    (hpc : s.regPC = 9) (hnh : s.halted = false)
    (h9 : s.mem.read 9 = 0x7E) (h10 : s.mem.read 10 = 0xEB)
    (h11 : s.mem.read 11 = 0xBE) (h12 : s.mem.read 12 = 0xEB) :
    let s4 := run s 4
    let (_, flags) := alu8 .CP (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    s4.regPC = 13 ∧ s4.halted = false ∧
    s4.mem = s.mem ∧ s4.regSP = s.regSP ∧ s4.output = s.output ∧
    s4.regH = s.regH ∧ s4.regL = s.regL ∧
    s4.regB = s.regB ∧ s4.regC = s.regC ∧
    s4.regD = s.regD ∧ s4.regE = s.regE ∧
    s4.regF = flags := by
  simp only [show (4 : Nat) = 1 + 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h9, h10, h11, h12, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem cmp_eq_dec4 (s : State)
    (hpc : s.regPC = 13) (hnh : s.halted = false)
    (h13 : s.mem.read 13 = 0x20) (h14 : s.mem.read 14 = 0x0A)
    (h15 : s.mem.read 15 = 0x2B) (h16 : s.mem.read 16 = 0x1B)
    (h17 : s.mem.read 17 = 0x0B)
    (hfz : s.regF.z = true) :
    let s4 := run s 4
    s4.regPC = 18 ∧ s4.halted = false ∧
    s4.mem = s.mem ∧ s4.regSP = s.regSP ∧ s4.output = s.output ∧
    s4.regH = hi16 (s.hl - 1) ∧ s4.regL = lo16 (s.hl - 1) ∧
    s4.regD = hi16 (s.de - 1) ∧ s4.regE = lo16 (s.de - 1) ∧
    s4.regB = hi16 (s.bc - 1) ∧ s4.regC = lo16 (s.bc - 1) := by
  simp only [show (4 : Nat) = 1 + 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h13, h14, h15, h16, h17, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend, hfz]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem cmp_test_loop3 (s : State)
    (hpc : s.regPC = 18) (hnh : s.halted = false)
    (h18 : s.mem.read 18 = 0x78) (h19 : s.mem.read 19 = 0xB1)
    (h20 : s.mem.read 20 = 0x20) (h21 : s.mem.read 21 = 0xF3)
    (hne : s.regB ||| s.regC ≠ 0) :
    let s3 := run s 3
    s3.regPC = 9 ∧ s3.halted = false ∧
    s3.mem = s.mem ∧ s3.regSP = s.regSP ∧ s3.output = s.output ∧
    s3.regH = s.regH ∧ s3.regL = s.regL ∧
    s3.regB = s.regB ∧ s3.regC = s.regC ∧
    s3.regD = s.regD ∧ s3.regE = s.regE := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h18, h19, h20, h21, exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]
  split_ifs <;> simp_all +decide

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem cmp_test_exit_jp4 (s : State)
    (hpc : s.regPC = 18) (hnh : s.halted = false)
    (h18 : s.mem.read 18 = 0x78) (h19 : s.mem.read 19 = 0xB1)
    (h20 : s.mem.read 20 = 0x20) (h21 : s.mem.read 21 = 0xF3)
    (h22 : s.mem.read 22 = 0xC3) (h23 : s.mem.read 23 = 0x58)
    (h24 : s.mem.read 24 = 0x00)
    (heq : s.regB ||| s.regC = 0) :
    let s4 := run s 4
    s4.regPC = 88 ∧ s4.halted = false ∧
    s4.mem = s.mem ∧ s4.regSP = s.regSP ∧ s4.output = s.output ∧
    s4.regH = s.regH ∧ s4.regL = s.regL ∧
    s4.regB = s.regB ∧ s4.regC = s.regC ∧
    s4.regD = s.regD ∧ s4.regE = s.regE := by
  simp only [show (4 : Nat) = 1 + 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h18, h19, h20, h21, h22, h23, h24, exec, readLoc8, writeLoc8,
                readReg16, writeReg16, loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned, heq]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem cmp_diff_branch2 (s : State)
    (hpc : s.regPC = 13) (hnh : s.halted = false)
    (h13 : s.mem.read 13 = 0x20) (h14 : s.mem.read 14 = 0x0A)
    (h25 : s.mem.read 25 = 0xDA) (h26 : s.mem.read 26 = 0x3A)
    (h27 : s.mem.read 27 = 0x00)
    (hfz : s.regF.z = false) :
    let s2 := run s 2
    s2.halted = false ∧
    s2.mem = s.mem ∧ s2.regSP = s.regSP ∧ s2.output = s.output ∧
    s2.regH = s.regH ∧ s2.regL = s.regL ∧
    s2.regB = s.regB ∧ s2.regC = s.regC ∧
    s2.regD = s.regD ∧ s2.regE = s.regE ∧
    (if s.regF.c then s2.regPC = 58 else s2.regPC = 28) := by
  contrapose! hfz; have := compare_fixed_bytes 1; simp_all +decide
  unfold run at hfz; simp_all +decide [step]
  unfold decodeMem at *; simp_all +decide [decodeRoot, opcX, opcY, opcZ, opcP, opcQ, exec, readLoc8, writeLoc8, readReg16, writeReg16, loc8of, reg8of, reg16of, reg16sof, aluOf, condOf]
  split_ifs at * <;> simp_all +decide [run]
  · unfold step at *; simp_all +decide [run]
    unfold exec at *; simp_all +decide [decodeMem, decodeRoot, opcX, opcY, opcZ, opcP, opcQ, evalCond, signExtend]
    unfold condOf at *; simp_all +decide [State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF, mkWord, lo16, hi16, Memory.read16]
  · unfold step at *; simp_all +decide [signExtend]
    unfold decodeMem at *; simp_all +decide [decodeRoot, opcX, opcY, opcZ, opcP, opcQ, exec, readLoc8, writeLoc8, readReg16, writeReg16, loc8of, reg8of, reg16of, reg16sof, aluOf, condOf]
    split_ifs at * <;> simp_all +decide [evalCond]
  · unfold step at *; simp_all +decide [State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF, mkWord, lo16, hi16, Memory.read16, evalCond, signExtend]
  · unfold step at *; simp_all +decide [evalCond]

/-
§8 BigCmp lemmas
-/

theorem cp_z_iff (a b : UInt8) (c : Bool) :
    (alu8 .CP a b c).2.z = (a == b) := by
  cases a ; cases b ; cases c ; simp +decide [ alu8 ];
  · native_decide +revert;
  · native_decide +revert

theorem cp_c_iff (a b : UInt8) (c : Bool) :
    ((alu8 .CP a b c).2.c = true) ↔ (a.toNat < b.toNat) := by
  unfold alu8; unfold sub8; lia

-- §9 Helper for reading program bytes from hprog

private theorem prog_byte (m : Memory) (n pos : Nat) (val : UInt8)
    (hprog : ∀ p, p < 104 → m.read p.toUInt16 = (encodeProgram (bigGcdProgram n)).getD p 0)
    (hpos : pos < 104)
    (hval : (encodeProgram (bigGcdProgram n)).getD pos 0 = val) :
    m.read pos.toUInt16 = val := (hprog pos hpos).trans hval

-- Helper: read program byte from state with mem = s.mem
private theorem read_prog (s : State) (n pos : Nat) (val : UInt8)
    (hmem_eq : s.mem = s.mem)  -- trivial, for the pattern
    (hprog : ∀ p, p < 104 → s.mem.read p.toUInt16 = (encodeProgram (bigGcdProgram n)).getD p 0)
    (hpos : pos < 104)
    (hval : (encodeProgram (bigGcdProgram n)).getD pos 0 = val) :
    s.mem.read pos.toUInt16 = val := (hprog pos hpos).trans hval

-- §10 Full compare loop by induction


set_option maxHeartbeats 6400000 in
theorem cmp_loop_complete
    (n : Nat) (aBytes bBytes : List UInt8)
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hfits : progSize + 2 * n < 0x8000)
    (hnPos : 0 < n) :
    ∀ (rem : Nat) (s : State),
    0 < rem → rem ≤ n → rem ≤ 65535 →
    s.regPC = 9 → s.halted = false → s.regSP = 0x8000 → s.output = [] →
    s.hl = (progSize + rem - 1).toUInt16 →
    s.de = (progSize + n + rem - 1).toUInt16 →
    s.bc = rem.toUInt16 →
    (∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0) →
    (∀ i (hi : i < n), s.mem.read (progSize + i).toUInt16 =
      aBytes[i]'(haL ▸ hi)) →
    (∀ i (hi : i < n), s.mem.read (progSize + n + i).toUInt16 =
      bBytes[i]'(hbL ▸ hi)) →
    (∀ i (hi₁ : rem ≤ i) (hi₂ : i < n),
      aBytes[i]'(haL ▸ hi₂) = bBytes[i]'(hbL ▸ hi₂)) →
    ∃ k, (run s k).halted = false ∧
         (run s k).output = [] ∧
         (run s k).mem = s.mem ∧
         (run s k).regSP = 0x8000 ∧
         (match bigCmp aBytes bBytes with
          | .lt => (run s k).regPC = 58
          | .eq => (run s k).regPC = 88
          | .gt => (run s k).regPC = 28) :=
  Z80.CmpLoopProof.cmp_loop_complete n aBytes bBytes haL hbL hfits hnPos

end Z80.ComparePhaseProof
