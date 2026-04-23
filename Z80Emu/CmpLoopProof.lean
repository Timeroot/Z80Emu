import Mathlib
import Z80Emu.Eval
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.BigNumGCDPhaseHelpers
import Z80Emu.CompareLoopHelpers

namespace Z80.CmpLoopProof

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers
open Z80.CompareLoopHelpers

private theorem pb (m : Memory) (n pos : Nat) (val : UInt8)
    (hprog : ∀ p, p < 104 → m.read p.toUInt16 = (encodeProgram (bigGcdProgram n)).getD p 0)
    (hpos : pos < 104) (hval : (encodeProgram (bigGcdProgram n)).getD pos 0 = val) :
    m.read pos.toUInt16 = val := (hprog pos hpos).trans hval

private theorem lift_read {m1 m2 : Memory} (h : m1 = m2) {addr : Word} {val : Byte}
    (hr : m2.read addr = val) : m1.read addr = val := h ▸ hr

theorem cp_z_iff' (a b : UInt8) (c : Bool) : (alu8 .CP a b c).2.z = (a == b) := by
  cases a; cases b; cases c <;> simp +decide [alu8] <;> native_decide +revert

theorem cp_c_iff' (a b : UInt8) (c : Bool) : ((alu8 .CP a b c).2.c = true) ↔ (a.toNat < b.toNat) := by
  unfold alu8; unfold sub8; lia

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
private theorem cfb (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 9 0 = 0x7E ∧ (encodeProgram (bigGcdProgram n)).getD 10 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 11 0 = 0xBE ∧ (encodeProgram (bigGcdProgram n)).getD 12 0 = 0xEB ∧
    (encodeProgram (bigGcdProgram n)).getD 13 0 = 0x20 ∧ (encodeProgram (bigGcdProgram n)).getD 14 0 = 0x0A ∧
    (encodeProgram (bigGcdProgram n)).getD 15 0 = 0x2B ∧ (encodeProgram (bigGcdProgram n)).getD 16 0 = 0x1B ∧
    (encodeProgram (bigGcdProgram n)).getD 17 0 = 0x0B ∧ (encodeProgram (bigGcdProgram n)).getD 18 0 = 0x78 ∧
    (encodeProgram (bigGcdProgram n)).getD 19 0 = 0xB1 ∧ (encodeProgram (bigGcdProgram n)).getD 20 0 = 0x20 ∧
    (encodeProgram (bigGcdProgram n)).getD 21 0 = 0xF3 ∧ (encodeProgram (bigGcdProgram n)).getD 22 0 = 0xC3 ∧
    (encodeProgram (bigGcdProgram n)).getD 23 0 = 0x58 ∧ (encodeProgram (bigGcdProgram n)).getD 24 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 25 0 = 0xDA ∧ (encodeProgram (bigGcdProgram n)).getD 26 0 = 0x3A ∧
    (encodeProgram (bigGcdProgram n)).getD 27 0 = 0x00 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize]

-- Building blocks
set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
private theorem bb4 (s : State) (hpc : s.regPC = 9) (hnh : s.halted = false)
    (h9 : s.mem.read 9 = 0x7E) (h10 : s.mem.read 10 = 0xEB)
    (h11 : s.mem.read 11 = 0xBE) (h12 : s.mem.read 12 = 0xEB) :
    (run s 4).regPC = 13 ∧ (run s 4).halted = false ∧ (run s 4).mem = s.mem ∧
    (run s 4).regSP = s.regSP ∧ (run s 4).output = s.output ∧
    (run s 4).regH = s.regH ∧ (run s 4).regL = s.regL ∧
    (run s 4).regB = s.regB ∧ (run s 4).regC = s.regC ∧
    (run s 4).regD = s.regD ∧ (run s 4).regE = s.regE ∧
    (run s 4).regF = (alu8 .CP (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).2 := by
  simp only [show (4 : Nat) = 1+1+1+1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
    h9, h10, h11, h12, exec, readLoc8, writeLoc8, readReg16, writeReg16,
    loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
    State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF,
    mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
    alu8, sub8, add8, parity8, testBit8, Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
private theorem bb_dec4 (s : State) (hpc : s.regPC = 13) (hnh : s.halted = false)
    (h13 : s.mem.read 13 = 0x20) (h14 : s.mem.read 14 = 0x0A) (h15 : s.mem.read 15 = 0x2B)
    (h16 : s.mem.read 16 = 0x1B) (h17 : s.mem.read 17 = 0x0B) (hfz : s.regF.z = true) :
    (run s 4).regPC = 18 ∧ (run s 4).halted = false ∧ (run s 4).mem = s.mem ∧
    (run s 4).regSP = s.regSP ∧ (run s 4).output = s.output ∧
    (run s 4).regH = hi16 (s.hl - 1) ∧ (run s 4).regL = lo16 (s.hl - 1) ∧
    (run s 4).regD = hi16 (s.de - 1) ∧ (run s 4).regE = lo16 (s.de - 1) ∧
    (run s 4).regB = hi16 (s.bc - 1) ∧ (run s 4).regC = lo16 (s.bc - 1) := by
  simp only [show (4 : Nat) = 1+1+1+1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
    h13, h14, h15, h16, h17, exec, readLoc8, writeLoc8, readReg16, writeReg16,
    loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
    State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF,
    mkWord, lo16, hi16, Memory.read16, evalCond, signExtend, hfz]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
private theorem bb_loop3 (s : State) (hpc : s.regPC = 18) (hnh : s.halted = false)
    (h18 : s.mem.read 18 = 0x78) (h19 : s.mem.read 19 = 0xB1)
    (h20 : s.mem.read 20 = 0x20) (h21 : s.mem.read 21 = 0xF3) (hne : s.regB ||| s.regC ≠ 0) :
    (run s 3).regPC = 9 ∧ (run s 3).halted = false ∧ (run s 3).mem = s.mem ∧
    (run s 3).regSP = s.regSP ∧ (run s 3).output = s.output ∧
    (run s 3).regH = s.regH ∧ (run s 3).regL = s.regL ∧
    (run s 3).regB = s.regB ∧ (run s 3).regC = s.regC ∧
    (run s 3).regD = s.regD ∧ (run s 3).regE = s.regE := by
  simp only [show (3 : Nat) = 1+1+1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
    h18, h19, h20, h21, exec, readLoc8, writeLoc8, readReg16, writeReg16,
    loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
    State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF,
    mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
    alu8, sub8, add8, parity8, testBit8, Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]
  split_ifs <;> simp_all +decide

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
private theorem bb_exit4 (s : State) (hpc : s.regPC = 18) (hnh : s.halted = false)
    (h18 : s.mem.read 18 = 0x78) (h19 : s.mem.read 19 = 0xB1) (h20 : s.mem.read 20 = 0x20)
    (h21 : s.mem.read 21 = 0xF3) (h22 : s.mem.read 22 = 0xC3) (h23 : s.mem.read 23 = 0x58)
    (h24 : s.mem.read 24 = 0x00) (heq : s.regB ||| s.regC = 0) :
    (run s 4).regPC = 88 ∧ (run s 4).halted = false ∧ (run s 4).mem = s.mem ∧
    (run s 4).regSP = s.regSP ∧ (run s 4).output = s.output := by
  simp only [show (4 : Nat) = 1+1+1+1 from by omega, run, hnh, step, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
    h18, h19, h20, h21, h22, h23, h24, exec, readLoc8, writeLoc8,
    readReg16, writeReg16, loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
    State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF,
    mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
    alu8, sub8, add8, parity8, testBit8, Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned, heq]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
private theorem bb_branch2 (s : State) (hpc : s.regPC = 13) (hnh : s.halted = false)
    (h13 : s.mem.read 13 = 0x20) (h14 : s.mem.read 14 = 0x0A) (h25 : s.mem.read 25 = 0xDA)
    (h26 : s.mem.read 26 = 0x3A) (h27 : s.mem.read 27 = 0x00) (hfz : s.regF.z = false) :
    (run s 2).halted = false ∧ (run s 2).mem = s.mem ∧ (run s 2).regSP = s.regSP ∧
    (run s 2).output = s.output ∧
    (if s.regF.c then (run s 2).regPC = 58 else (run s 2).regPC = 28) := by
  by_contra h_contra; simp only [not_and_or] at h_contra
  simp only [show (2 : Nat) = 1+1 from by omega, run, hnh, step, hpc] at h_contra ⊢
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
    h13, h14, h25, h26, h27, exec, readLoc8, writeLoc8, readReg16, writeReg16,
    loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
    State.hl, State.bc, State.de, State.af, State.setHL, State.setBC, State.setDE, State.setAF,
    mkWord, lo16, hi16, Memory.read16, evalCond, signExtend, hfz,
    alu8, sub8, add8, parity8, testBit8, Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned] at h_contra ⊢
  split_ifs at h_contra ⊢ <;> simp_all +decide

-- Helper for register pair equalities
private theorem hl_eq_of (s : State) (h1 : s.regH = a) (h2 : s.regL = b) :
    s.hl = mkWord a b := by unfold State.hl; rw [h1, h2]
private theorem de_eq_of (s : State) (h1 : s.regD = a) (h2 : s.regE = b) :
    s.de = mkWord a b := by unfold State.de; rw [h1, h2]
private theorem bc_eq_of (s : State) (h1 : s.regB = a) (h2 : s.regC = b) :
    s.bc = mkWord a b := by unfold State.bc; rw [h1, h2]

set_option maxHeartbeats 6400000 in
theorem cmp_loop_complete
    (n : Nat) (aBytes bBytes : List UInt8)
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hfits : progSize + 2 * n < 0x8000) (hnPos : 0 < n) :
    ∀ (rem : Nat) (s : State),
    0 < rem → rem ≤ n → rem ≤ 65535 →
    s.regPC = 9 → s.halted = false → s.regSP = 0x8000 → s.output = [] →
    s.hl = (progSize + rem - 1).toUInt16 → s.de = (progSize + n + rem - 1).toUInt16 →
    s.bc = rem.toUInt16 →
    (∀ pos, pos < 104 → s.mem.read pos.toUInt16 = (encodeProgram (bigGcdProgram n)).getD pos 0) →
    (∀ i (hi : i < n), s.mem.read (progSize + i).toUInt16 = aBytes[i]'(haL ▸ hi)) →
    (∀ i (hi : i < n), s.mem.read (progSize + n + i).toUInt16 = bBytes[i]'(hbL ▸ hi)) →
    (∀ i (hi₁ : rem ≤ i) (hi₂ : i < n), aBytes[i]'(haL ▸ hi₂) = bBytes[i]'(hbL ▸ hi₂)) →
    ∃ k, (run s k).halted = false ∧ (run s k).output = [] ∧
         (run s k).mem = s.mem ∧ (run s k).regSP = 0x8000 ∧
         (match bigCmp aBytes bBytes with
          | .lt => (run s k).regPC = 58
          | .eq => (run s k).regPC = 88
          | .gt => (run s k).regPC = 28) := by
  intro rem; induction rem with
  | zero => intro _ h; omega
  | succ rem' ih =>
  intro s hrp hrl hrl65 hpc hnh hsp hout hhl hde hbc hprog haM hbM hsuf
  have CF := cfb n
  -- Step 1: compare (4 steps)
  have S1 := bb4 s hpc hnh (pb s.mem n 9 _ hprog (by omega) CF.1) (pb s.mem n 10 _ hprog (by omega) CF.2.1)
    (pb s.mem n 11 _ hprog (by omega) CF.2.2.1) (pb s.mem n 12 _ hprog (by omega) CF.2.2.2.1)
  have RA : s.mem.read s.hl = aBytes[rem'] := by
    rw [hhl]; exact read_aBytes_at s.mem n (rem'+1) aBytes haL (by omega) hrl hfits haM
  have RB : s.mem.read s.de = bBytes[rem'] := by
    rw [hde]; exact read_bBytes_at s.mem n (rem'+1) bBytes hbL (by omega) hrl hfits hbM
  have HZ : (run s 4).regF.z = (aBytes[rem'] == bBytes[rem']) := by
    rw [S1.2.2.2.2.2.2.2.2.2.2.2, cp_z_iff', RA, RB]
  -- Register pair equalities for run s 4
  have HL4 : (run s 4).hl = s.hl := hl_eq_of _ S1.2.2.2.2.2.1 S1.2.2.2.2.2.2.1
  have DE4 : (run s 4).de = s.de := de_eq_of _ S1.2.2.2.2.2.2.2.2.2.1 S1.2.2.2.2.2.2.2.2.2.2.1
  have BC4 : (run s 4).bc = s.bc := bc_eq_of _ S1.2.2.2.2.2.2.2.1 S1.2.2.2.2.2.2.2.2.1
  by_cases HEQ : aBytes[rem']'(by rw [haL]; omega) = bBytes[rem']'(by rw [hbL]; omega)
  · -- EQUAL BYTES
    have HFZ : (run s 4).regF.z = true := by rw [HZ]; simp [HEQ]
    have S2 := bb_dec4 (run s 4) S1.1 S1.2.1
      (lift_read S1.2.2.1 (pb s.mem n 13 _ hprog (by omega) CF.2.2.2.2.1))
      (lift_read S1.2.2.1 (pb s.mem n 14 _ hprog (by omega) CF.2.2.2.2.2.1))
      (lift_read S1.2.2.1 (pb s.mem n 15 _ hprog (by omega) CF.2.2.2.2.2.2.1))
      (lift_read S1.2.2.1 (pb s.mem n 16 _ hprog (by omega) CF.2.2.2.2.2.2.2.1))
      (lift_read S1.2.2.1 (pb s.mem n 17 _ hprog (by omega) CF.2.2.2.2.2.2.2.2.1)) HFZ
    have R8 : run s 8 = run (run s 4) 4 := run_add s 4 4
    have M8 : (run s 8).mem = s.mem := by rw [R8, S2.2.2.1, S1.2.2.1]
    -- Register pair after dec
    have HL8 : (run s 8).hl = s.hl - 1 := by
      rw [R8, hl_eq_of _ S2.2.2.2.2.2.1 S2.2.2.2.2.2.2.1, mkWord_hi_lo, HL4]
    have DE8 : (run s 8).de = s.de - 1 := by
      rw [R8, de_eq_of _ S2.2.2.2.2.2.2.2.1 S2.2.2.2.2.2.2.2.2.1, mkWord_hi_lo, DE4]
    have BC8 : (run s 8).bc = s.bc - 1 := by
      rw [R8, bc_eq_of _ S2.2.2.2.2.2.2.2.2.2.1 S2.2.2.2.2.2.2.2.2.2.2, mkWord_hi_lo, BC4]
    -- Actual values
    have BC_dec : s.bc - 1 = rem'.toUInt16 := by rw [hbc]; exact bc_after_dec (rem'+1) (by omega) (by omega)
    by_cases HRP : 0 < rem'
    · -- CONTINUE: sorry'd for subagent
      have RB3 : (run s 8).regB ||| (run s 8).regC ≠ 0 := by
        rw [ R8, S2.2.2.2.2.2.2.2.2.2.1, S2.2.2.2.2.2.2.2.2.2.2, BC4, BC_dec ];
        have := hilo_or_ne_zero rem' ( by linarith ) ( by linarith );
        exact this;
      have BB3 : (run (run s 8) 3).regPC = 9 ∧ (run (run s 8) 3).halted = false ∧ (run (run s 8) 3).mem = (run s 8).mem ∧ (run (run s 8) 3).regSP = (run s 8).regSP ∧ (run (run s 8) 3).output = (run s 8).output ∧ (run (run s 8) 3).regH = (run s 8).regH ∧ (run (run s 8) 3).regL = (run s 8).regL ∧ (run (run s 8) 3).regB = (run s 8).regB ∧ (run (run s 8) 3).regC = (run s 8).regC ∧ (run (run s 8) 3).regD = (run s 8).regD ∧ (run (run s 8) 3).regE = (run s 8).regE := by
        apply_rules [ bb_loop3 ];
        all_goals norm_num [ R8, S2 ];
        · grind;
        · grind;
        · rw [ S1.2.2.1 ];
          exact hprog 20 ( by decide );
        · exact S1.2.2.1.symm ▸ hprog 21 ( by decide );
      have RP3 : (run (run s 8) 3).regPC = 9 ∧ (run (run s 8) 3).halted = false ∧ (run (run s 8) 3).mem = s.mem ∧ (run (run s 8) 3).regSP = 32768 ∧ (run (run s 8) 3).output = [] ∧ (run (run s 8) 3).hl = (progSize + rem' - 1).toUInt16 ∧ (run (run s 8) 3).de = (progSize + n + rem' - 1).toUInt16 ∧ (run (run s 8) 3).bc = rem'.toUInt16 := by
        simp_all +decide only [State.hl, State.de, State.bc];
        simp +decide [ UInt16.ext_iff ];
        norm_num [ UInt16.toNat_sub, UInt16.toNat_ofNat ];
        omega;
      specialize ih ( run ( run s 8 ) 3 ) HRP ( by linarith ) ( by linarith ) RP3.1 RP3.2.1 RP3.2.2.2.1 RP3.2.2.2.2.1 RP3.2.2.2.2.2.1 RP3.2.2.2.2.2.2.1 RP3.2.2.2.2.2.2.2;
      obtain ⟨ k, hk ⟩ := ih ( by
        grind ) ( by
        grind ) ( by
        grind ) ( by
        grind );
      use 8 + 3 + k;
      rw [ run_add, run_add ];
      grind
    · -- EXIT: rem' = 0
      norm_num [ show rem' = 0 by linarith ] at *;
      -- Since `aBytes[0] = bBytes[0]` and `aBytes[i] = bBytes[i]` for all `i ≥ 1`, we can conclude that `bigCmp aBytes bBytes = .eq`.
      have h_bigCmp_eq : bigCmp aBytes bBytes = .eq := by
        apply bigCmp_all_eq aBytes bBytes n haL hbL;
        exact fun i hi hi' => if hi'' : i = 0 then hi''.symm ▸ HEQ else hsuf i ( Nat.pos_of_ne_zero hi'' ) hi';
      use 12;
      rw [ show run s 12 = run ( run s 8 ) 4 from ?_ ];
      · have := bb_exit4 ( run s 8 ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide only [State.regPC,
                                                                                                           State.halted, State.mem, State.regSP, State.output];
        grind;
        grind;
        · grind;
        · convert hprog 20 ( by decide ) using 1;
        · grind;
        · grind;
        · grind;
      · rw [ ← run_add ]
  · -- DIFFERENT BYTES
    have HLT : bigCmp [aBytes[rem']] [bBytes[rem']] = if aBytes[rem'] < bBytes[rem'] then Ordering.lt else Ordering.gt := by
      simp +decide [ HEQ, bigCmp ];
      split_ifs <;> simp +decide [ *, compare ];
      · exact?;
      · simp +decide [ compareOfLessAndEq, *, lt_asymm ];
        exact ⟨ le_of_not_gt ‹_›, by simpa [ ← UInt8.toNat_inj ] using HEQ ⟩;
    have HLT : bigCmp aBytes bBytes = if aBytes[rem'] < bBytes[rem'] then Ordering.lt else Ordering.gt := by
      rw [ ← HLT ];
      convert bigCmp_determined_by_diff aBytes bBytes n (rem' + 1) haL hbL (by linarith) (by linarith) _ _ using 1;
      · finiteness;
      · exact HEQ;
    have := bb_branch2 ( run s 4 ) S1.1 S1.2.1 ( by
      rw [ S1.2.2.1 ];
      exact hprog 13 ( by decide ) ) ( by
      convert pb s.mem n 14 10 _ _ _ using 1;
      · exact S1.2.2.1.symm ▸ rfl;
      · finiteness;
      · decide +revert;
      · exact cfb n |>.2.2.2.2.2.1 ) ( by
      rw [ S1.2.2.1 ];
      exact pb _ _ _ _ hprog ( by decide ) rfl ) ( by
      convert pb s.mem n 26 58 _ _ _ using 1;
      · exact S1.2.2.1 ▸ rfl;
      · finiteness;
      · decide +revert;
      · exact cfb n |>.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ) ( by
      rw [ S1.2.2.1 ];
      exact hprog 27 ( by decide ) ) ( by
      exact HZ.trans ( by simp +decide [ HEQ ] ) );
    use 6;
    rw [ show run s 6 = run ( run s 4 ) 2 from ?_ ];
    · split_ifs at * <;> simp_all +decide only [if_true];
      · exact ‹¬ ( alu8 ALUOp.CP aBytes[rem'] bBytes[rem'] s.regF.c ).2.c = true› ( by simpa using cp_c_iff' _ _ _ |>.2 ‹_› );
      · have := cp_c_iff' aBytes[rem'] bBytes[rem'] s.regF.c; simp_all +decide only [if_true] ;
        exact ‹¬aBytes[rem'] < bBytes[rem']› ( by exact? );
    · rw [ ← run_add ]

end Z80.CmpLoopProof