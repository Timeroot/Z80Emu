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

/-!
# Subtract-A and Subtract-B Loop Proofs
-/

namespace Z80.SubtractALoopProof

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers
open Z80.SubtractPhaseProof Z80.SubtractLoopProof Z80.CompareLoopHelpers

/-! ## §1 Memory isolation helpers -/

theorem read_prog_through_data_write (m : Memory) (hl : Word) (result : Byte)
    (pos : Nat) (hpos : pos < 104) (hhl : hl.toNat ≥ 104)
    (hmsz : m.data.data.size = 65536) :
    (m.write hl result).read pos.toUInt16 = m.read pos.toUInt16 :=
  Memory.read_write_diff m pos.toUInt16 hl result hmsz (by
    intro h; have := congr_arg UInt16.toNat h
    simp [UInt16.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pos < 65536)] at this; omega)

theorem read_prog_through_writes (m : Memory) (hl : Word) (result : Byte) (af : Word)
    (pos : Nat) (hpos : pos < 104) (hhl : hl.toNat ≥ 104)
    (hmsz : m.data.data.size = 65536) :
    ((m.write hl result).write16 0x7FFE af).read pos.toUInt16 = m.read pos.toUInt16 := by
  rw [read_preserved_write16_stack _ af _
    (by simp [UInt16.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pos < 65536)]; omega)
    (Memory.write_size m hl result hmsz)]
  exact read_prog_through_data_write m hl result pos hpos hhl hmsz

theorem read_data_through_writes (m : Memory) (hl : Word) (result : Byte) (af : Word)
    (addr : Word) (hne : addr ≠ hl) (haddr : addr.toNat < 0x7FFE)
    (hmsz : m.data.data.size = 65536) :
    ((m.write hl result).write16 0x7FFE af).read addr = m.read addr := by
  rw [read_preserved_write16_stack _ af addr haddr (Memory.write_size m hl result hmsz)]
  exact Memory.read_write_diff m addr hl result hmsz hne

theorem read_hl_through_writes (m : Memory) (hl : Word) (result : Byte) (af : Word)
    (haddr : hl.toNat < 0x7FFE)
    (hmsz : m.data.data.size = 65536) :
    ((m.write hl result).write16 0x7FFE af).read hl = result := by
  rw [read_preserved_write16_stack _ af hl haddr (Memory.write_size m hl result hmsz)]
  exact Memory.read_write_same m hl result hmsz

/-! ## §2 Program byte extraction -/

set_option maxHeartbeats 12800000 in
set_option linter.unusedSimpArgs false in
theorem sub_a_setup_bytes (n : Nat) :
    (encodeProgram (bigGcdProgram n)).getD 28 0 = 0x21 ∧
    (encodeProgram (bigGcdProgram n)).getD 29 0 = 0x68 ∧
    (encodeProgram (bigGcdProgram n)).getD 30 0 = 0x00 ∧
    (encodeProgram (bigGcdProgram n)).getD 31 0 = 0x11 ∧
    (encodeProgram (bigGcdProgram n)).getD 32 0 = lo16 (104 + n).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 33 0 = hi16 (104 + n).toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 34 0 = 0x01 ∧
    (encodeProgram (bigGcdProgram n)).getD 35 0 = lo16 n.toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 36 0 = hi16 n.toUInt16 ∧
    (encodeProgram (bigGcdProgram n)).getD 37 0 = 0xB7 := by
  simp +decide [encodeProgram, bigGcdProgram, encode, List.flatMap, mkOpcode,
        Reg16.toCode, Reg16s.toCode, ALUOp.toCode, Cond.toCode, Reg8.toCode, progSize, lo16, hi16]

/-! ## §3 Setup phase (PC 28 → 38) -/

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem sub_a_setup4 (s : State) (n : Nat)
    (hpc : s.regPC = 28) (hnh : s.halted = false)
    (h28 : s.mem.read 28 = 0x21) (h29 : s.mem.read 29 = 0x68)
    (h30 : s.mem.read 30 = 0x00) (h31 : s.mem.read 31 = 0x11)
    (h32 : s.mem.read 32 = lo16 (104 + n).toUInt16)
    (h33 : s.mem.read 33 = hi16 (104 + n).toUInt16)
    (h34 : s.mem.read 34 = 0x01) (h35 : s.mem.read 35 = lo16 n.toUInt16)
    (h36 : s.mem.read 36 = hi16 n.toUInt16) (h37 : s.mem.read 37 = 0xB7) :
    let s4 := run s 4
    s4.regPC = 38 ∧ s4.halted = false ∧
    s4.mem = s.mem ∧ s4.regSP = s.regSP ∧ s4.output = s.output ∧
    s4.regH = 0x00 ∧ s4.regL = 0x68 ∧
    s4.regD = hi16 (104 + n).toUInt16 ∧ s4.regE = lo16 (104 + n).toUInt16 ∧
    s4.regB = hi16 n.toUInt16 ∧ s4.regC = lo16 n.toUInt16 ∧
    s4.regF.c = false := by
  contrapose! h37
  intro h; have := h37; simp_all +decide [run]
  unfold step at *; simp_all +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ,
    opcP, opcQ, exec, readLoc8, writeLoc8, readReg16, writeReg16, loc8of, reg8of, reg16of,
    reg16sof, aluOf, condOf, State.hl, State.bc, State.de, State.af, State.setHL, State.setBC,
    State.setDE, State.setAF, Memory.read16, evalCond, signExtend, alu8, sub8, add8, parity8,
    testBit8, Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]
  exact h37 (by rw [mkWord_hi_lo]) (by rw [mkWord_hi_lo]) (by rw [mkWord_hi_lo]) (by rw [mkWord_hi_lo])

/-! ## §4 bigSub.go helpers -/

theorem bigSub_go_length (a b : List UInt8) (borrow : Nat) (hlen : a.length = b.length) :
    (bigSub.go a b borrow).length = a.length := by
  induction a generalizing b borrow with
  | nil => cases b <;> simp_all [bigSub.go]
  | cons ah atl ih =>
    cases b with
    | nil => simp_all
    | cons bh bt => simp [bigSub.go]; exact ih bt _ (by simp_all)

/-! ## §4.5 Program byte helper -/

private theorem pb' (m : Memory) (n pos : Nat) (val : UInt8)
    (hprog : ∀ p, p < 104 → m.read p.toUInt16 = (encodeProgram (bigGcdProgram n)).getD p 0)
    (hpos : pos < 104) (hval : (encodeProgram (bigGcdProgram n)).getD pos 0 = val) :
    m.read pos.toUInt16 = val := (hprog pos hpos).trans hval

/-! ## §4.6 Composite A-loop iteration helpers -/

set_option maxHeartbeats 6400000 in
/-- First 8 steps of subtract-A iteration: SBC + write + INC HL + INC DE + DEC BC. -/
theorem sub_a_steps_5_3 (s : State) (n : Nat)
    (hpc : s.regPC = 38) (hnh : s.halted = false)
    (hhl_ge : s.hl.toNat ≥ 104)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536) :
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    let s8 := run s 8
    s8.regPC = 46 ∧ s8.halted = false ∧
    s8.regA = result ∧ s8.regF = flags ∧
    s8.regSP = s.regSP ∧ s8.output = s.output ∧
    s8.regH = hi16 (s.hl + 1) ∧ s8.regL = lo16 (s.hl + 1) ∧
    s8.regD = hi16 (s.de + 1) ∧ s8.regE = lo16 (s.de + 1) ∧
    s8.regB = hi16 (s.bc - 1) ∧ s8.regC = lo16 (s.bc - 1) ∧
    s8.mem = s.mem.write s.hl result ∧
    s8.mem.data.data.size = 65536 := by
  have h_sub_first5_ind : (encodeProgram (bigGcdProgram n)).getD 38 0 = 0x7E ∧ (encodeProgram (bigGcdProgram n)).getD 39 0 = 0xEB ∧ (encodeProgram (bigGcdProgram n)).getD 40 0 = 0x9E ∧ (encodeProgram (bigGcdProgram n)).getD 41 0 = 0xEB ∧ (encodeProgram (bigGcdProgram n)).getD 42 0 = 0x77 := by
    exact ⟨ by exact subtract_a_fixed_bytes n |>.2.2.2.2.2.2.1, by exact subtract_a_fixed_bytes n |>.2.2.2.2.2.2.2.1, by exact subtract_a_fixed_bytes n |>.2.2.2.2.2.2.2.2.1, by exact subtract_a_fixed_bytes n |>.2.2.2.2.2.2.2.2.2.1, by exact subtract_a_fixed_bytes n |>.2.2.2.2.2.2.2.2.2.2.1 ⟩;
  have := sub_first5 s hpc hnh ( hprog 38 ( by decide ) ▸ h_sub_first5_ind.1 ) ( hprog 39 ( by decide ) ▸ h_sub_first5_ind.2.1 ) ( hprog 40 ( by decide ) ▸ h_sub_first5_ind.2.2.1 ) ( hprog 41 ( by decide ) ▸ h_sub_first5_ind.2.2.2.1 ) ( hprog 42 ( by decide ) ▸ h_sub_first5_ind.2.2.2.2 ) ; simp_all +decide only ;
  have := sub_loop_inc_dec ( run s 5 ) this.1 this.2.1 ( by
    rw [ this.2.2.2.2.2.2.2.2.2.2.2.2 ];
    convert hprog 43 ( by decide ) using 1;
    apply read_prog_through_data_write; norm_num; norm_num; assumption;
    exact hmsz ) ( by
    rw [ this.2.2.2.2.2.2.2.2.2.2.2.2 ];
    convert hprog 44 ( by decide ) using 1;
    apply read_prog_through_data_write; norm_num; norm_num; assumption;
    exact hmsz ) ( by
    convert hprog 45 ( by decide ) using 1;
    rw [ this.2.2.2.2.2.2.2.2.2.2.2.2 ];
    apply read_prog_through_data_write; norm_num; norm_num; assumption;
    exact hmsz ) ; simp_all +decide [ run_add' ] ;
  rw [ show run s 8 = run ( run s 5 ) 3 from run_add' s 5 3 ] ; simp_all +decide [ run_add' ] ;
  simp_all +decide [ State.hl, State.de, State.bc ];
  convert Memory.write_size s.mem ( mkWord s.regH s.regL ) ( sub8 ( s.mem.read ( mkWord s.regH s.regL ) ) ( s.mem.read ( mkWord s.regD s.regE ) ) s.regF.c |>.1 ) hmsz using 1

set_option maxHeartbeats 6400000 in
/-- Last 6 steps of subtract-A iteration (continuing): PUSH AF + test BC + POP AF; JR back. -/
theorem sub_a_push_test_pop_continue (s : State) (n : Nat)
    (hpc : s.regPC = 46) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536)
    (hbc_ne : s.regB ||| s.regC ≠ 0) :
    let s6 := run s 6
    s6.regPC = 38 ∧ s6.halted = false ∧ s6.regSP = 0x8000 ∧
    s6.output = s.output ∧
    s6.regA = s.regA ∧ s6.regF = s.regF ∧
    s6.regH = s.regH ∧ s6.regL = s.regL ∧
    s6.regD = s.regD ∧ s6.regE = s.regE ∧
    s6.regB = s.regB ∧ s6.regC = s.regC ∧
    s6.mem = s.mem.write16 0x7FFE s.af ∧
    s6.mem.data.data.size = 65536 := by
  -- Apply the lemma sub_loop_push_af to get the state after 1 step.
  have h1 := sub_loop_push_af s hpc hnh (by
  convert hprog 46 ( by decide ) using 1) hsp;
  have h2 := sub_loop_test_bc (run s 1) h1.left h1.right.left (by
  have := hprog 47 ( by decide ) ; simp_all +decide [ Memory.read ] ;
  convert this using 1;
  convert read_preserved_write16_stack s.mem s.af 47 ( by decide ) hmsz using 1) (by
  rw [ h1.2.2.2.2.1 ];
  rw [ read_preserved_write16_stack ];
  · exact hprog 48 ( by decide );
  · decide;
  · exact hmsz);
  have h3 := sub_loop_pop_continue (run (run s 1) 2) (by
  exact h2.1) (by
  exact h2.2.1) (by
  rw [ h2.2.2.2.2.1, h1.2.2.2.2.1 ];
  rw [ read_preserved_write16_stack ];
  · exact hprog 49 ( by decide );
  · decide +revert;
  · exact hmsz) (by
  simp +decide [ h1, h2 ];
  rw [ read_preserved_write16_stack ] <;> norm_num [ hmsz ];
  · exact hprog 50 ( by decide );
  · decide +revert) (by
  rw [ h2.2.2.2.2.1 ];
  rw [ h1.2.2.2.2.1 ];
  rw [ read_preserved_write16_stack ];
  · exact hprog 51 ( by decide );
  · decide;
  · exact hmsz) (by
  rw [ h2.2.2.2.2.1, h1.2.2.2.2.1 ];
  rw [ read_preserved_write16_stack ] <;> norm_num [ hmsz ];
  · exact hprog 52 ( by decide );
  · decide +revert) (by
  convert hprog 53 ( by decide ) using 1;
  grind +suggestions) (by
  aesop) (by
  grind);
  simp_all +decide [ ← run_add' ];
  rw [ read16_write16_same ] <;> norm_num [ hmsz ];
  · exact ⟨ af_roundtrip_hi _ _, af_roundtrip_lo _ _, write16_size _ _ _ hmsz ⟩;
  · decide +revert

set_option maxHeartbeats 6400000 in
/-- Last 6 steps of subtract-A iteration (done): PUSH AF + test BC + POP AF; JP 0. -/
theorem sub_a_push_test_pop_done (s : State) (n : Nat)
    (hpc : s.regPC = 46) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
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
  have h_sub_a : (encodeProgram (bigGcdProgram n)).getD 47 0 = 0x78 ∧ (encodeProgram (bigGcdProgram n)).getD 48 0 = 0xB1 := by
    exact ⟨ by exact ( by exact ( by exact ( by exact ( by exact ( by exact by { exact ( by exact ( by exact by { have := subtract_a_fixed_bytes n; aesop } ) ) } ) ) ) ) ), by exact ( by exact ( by exact ( by exact ( by exact ( by exact by { exact ( by exact ( by exact by { have := subtract_a_fixed_bytes n; aesop } ) ) } ) ) ) ) ) ⟩;
  have := sub_loop_push_af s hpc hnh ( by
    have := subtract_a_fixed_bytes n; aesop; ) hsp;
  have := sub_loop_test_bc ( run s 1 ) ( by
    exact this.1 ) ( by
    exact this.2.1 ) ( by
    grind +suggestions ) ( by
    grind +suggestions );
  have := sub_loop_pop_done ( run ( run s 1 ) 2 ) ( by
    exact this.1 ) ( by
    exact this.2.1 ) ( by
    convert hprog 49 ( by decide ) using 1;
    convert read_preserved_write16_stack _ _ _ _ _ using 1;
    rotate_left;
    exact s.af;
    · decide +revert;
    · exact hmsz;
    · grind ) ( by
    simp_all +decide [ Nat.toUInt16 ];
    rw [ read_preserved_write16_stack ] ; aesop;
    · decide +revert;
    · exact hmsz ) ( by
    rw [ this.2.2.2.2.1 ];
    rw [ ‹have s1 := run s 1; s1.regPC = 47 ∧ s1.halted = false ∧ s1.regSP = 32766 ∧ s1.output = s.output ∧ s1.mem = s.mem.write16 32766 s.af ∧ s1.regA = s.regA ∧ s1.regF = s.regF ∧ s1.regH = s.regH ∧ s1.regL = s.regL ∧ s1.regB = s.regB ∧ s1.regC = s.regC ∧ s1.regD = s.regD ∧ s1.regE = s.regE›.2.2.2.2.1 ];
    rw [ read_preserved_write16_stack ];
    · exact hprog 54 ( by decide );
    · decide +revert;
    · exact hmsz ) ( by
    convert hprog 55 ( by decide ) using 1;
    simp +decide [ *, run_add' ];
    exact read_preserved_write16_stack _ _ _ ( by decide ) hmsz ) ( by
    have h_mem_56 : (run (run s 1) 2).mem = s.mem.write16 32766 s.af := by
      lia;
    rw [ h_mem_56 ];
    rw [ read_preserved_write16_stack ];
    · exact hprog 56 ( by decide );
    · decide;
    · exact hmsz ) ( by
    have h_mem_57 : (run (run s 1) 2).mem.read 57 = s.mem.read 57 := by
      simp_all +decide [ run_add' ];
      exact read_preserved_write16_stack _ _ _ ( by decide ) hmsz;
    exact h_mem_57.trans ( hprog 57 ( by decide ) ) ) ( by
    lia ) ( by
    aesop ) ; simp_all +decide [ run_add' ] ;
  rw [ show run s 6 = run ( run ( run s 1 ) 2 ) 3 from ?_ ];
  · have h_mem_size : (s.mem.write16 32766 s.af).data.data.size = 65536 := by
      apply_rules [ Z80.SubtractPhaseProof.write16_size ];
    have h_mem_size : (s.mem.write16 32766 s.af).read16 32766 = s.af := by
      apply read16_write16_same;
      · exact hmsz;
      · decide +revert;
    have := af_roundtrip_hi s.regA s.regF; have := af_roundtrip_lo s.regA s.regF; aesop;
  · rw [ ← run_add', ← run_add' ]

/-! ## §4.7 Single iteration helpers -/

set_option maxHeartbeats 6400000 in
theorem sub_a_one_iter_continue (s : State) (n : Nat)
    (hpc : s.regPC = 38) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
    (hhl_ge : s.hl.toNat ≥ 104) (hhl_lt : s.hl.toNat < 0x7FFE)
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (hmsz : s.mem.data.data.size = 65536)
    (hbc_ne : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) ≠ 0) :
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    let s14 := run s 14
    s14.regPC = 38 ∧ s14.halted = false ∧ s14.regSP = 0x8000 ∧
    s14.output = s.output ∧
    s14.hl = s.hl + 1 ∧ s14.de = s.de + 1 ∧ s14.bc = s.bc - 1 ∧
    s14.regF.c = flags.c ∧
    s14.mem.read s.hl = result ∧
    (∀ addr : Word, addr ≠ s.hl → addr.toNat < 0x7FFE → s14.mem.read addr = s.mem.read addr) ∧
    (∀ pos, pos < 104 → s14.mem.read pos.toUInt16 = s.mem.read pos.toUInt16) ∧
    s14.mem.data.data.size = 65536 := by
  -- By definition of `run`, we know that `run s 14 = run (run s 8) 6`.
  have h_run : run s 14 = run (run s 8) 6 := by
    rw [ ← run_add' ];
  have := sub_a_steps_5_3 s n hpc hnh hhl_ge hprog hmsz;
  have := sub_a_push_test_pop_continue ( run s 8 ) n ( this.1 ) ( this.2.1 ) ( by aesop ) ?_ ?_ ?_ <;> simp_all +decide [ State.hl, State.de, State.bc ];
  · refine' ⟨ _, _, _, _, _, _ ⟩ <;> try exact mkWord_hi_lo _;
    · apply_rules [ read_hl_through_writes ];
    · intros addr haddr haddr_lt
      apply read_data_through_writes;
      · exact haddr;
      · exact haddr_lt;
      · exact hmsz;
    · refine' ⟨ _, _ ⟩;
      · intro pos hpos
        have := read_prog_through_writes s.mem (mkWord s.regH s.regL) (sub8 (s.mem.read (mkWord s.regH s.regL)) (s.mem.read (mkWord s.regD s.regE)) s.regF.c).1 (run s 8).af pos hpos (by
        exact hhl_ge) (by
        exact hmsz);
        grind +splitIndPred;
      · grind;
  · intro pos hpos; rw [ ← hprog pos hpos ] ;
    apply prog_byte_preserved;
    · exact hpos;
    · exact hmsz;
    · exact hhl_ge;
  · grobner

set_option maxHeartbeats 6400000 in
theorem sub_a_one_iter_done (s : State) (n : Nat)
    (hpc : s.regPC = 38) (hnh : s.halted = false) (hsp : s.regSP = 0x8000)
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
  have := @sub_a_steps_5_3;
  specialize this s n hpc hnh hhl_ge hprog hmsz;
  have := @sub_a_push_test_pop_done;
  rename_i h;
  specialize this (run s 8) n;
  specialize this ( by aesop ) ( by aesop ) ( by aesop ) ( by
    intro pos hpos
    have h_mem : (run s 8).mem = s.mem.write s.hl (sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).1 := by
      exact h.2.2.2.2.2.2.2.2.2.2.2.2.1;
    rw [ h_mem, read_prog_through_data_write ];
    · exact hprog pos hpos;
    · exact hpos;
    · exact hhl_ge;
    · exact hmsz ) ( by
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2 ) ( by
    grind );
  have := @run_add' s 8 6; simp_all +decide ;
  refine' ⟨ _, _, _, _ ⟩;
  · rw [ read_hl_through_writes ];
    · exact hhl_lt;
    · exact hmsz;
  · intro addr haddr haddr_lt
    have := @read_data_through_writes s.mem s.hl (sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).1 (run s 8).af addr haddr haddr_lt hmsz
    simp_all +decide [ Memory.write16 ];
  · intro pos hpos;
    rw [ ← hprog pos hpos ];
    apply read_prog_through_writes;
    · exact hpos;
    · exact hhl_ge;
    · exact hmsz;
  · grind

/-! ## §5 Subtract-A loop (core induction)

The loop invariant: at each entry to PC=38, HL and DE point to
the current byte pair, BC holds remaining count, and carry holds
the current borrow. We process bytes from low address to high,
corresponding to bigSub.go on the remaining (dropped) sublists.
-/

theorem bigSub_go_drop_getD_zero (aBytes bBytes : List UInt8) (n k borrow : Nat)
    (haL : aBytes.length = n) (hbL : bBytes.length = n) (hk : k < n) :
    (bigSub.go (List.drop k aBytes) (List.drop k bBytes) borrow).getD 0 0 =
    (((aBytes.getD k 0).toNat + 256 - (bBytes.getD k 0).toNat - borrow) % 256).toUInt8 := by
  cases h : List.drop k aBytes <;> cases h' : List.drop k bBytes <;> simp_all +decide [ List.getElem?_eq_none ];
  · grind;
  · linarith;
  · grind;
  · replace h := congr_arg List.head? h; replace h' := congr_arg List.head? h'; simp_all +decide [ List.getElem?_eq_getElem, Nat.lt_succ_iff ] ;
    unfold bigSub.go; simp +decide [ h, h' ] ;

theorem bigSub_go_drop_getD_succ (aBytes bBytes : List UInt8) (n k borrow : Nat) (j : Nat)
    (haL : aBytes.length = n) (hbL : bBytes.length = n) (hk : k < n) :
    (bigSub.go (List.drop k aBytes) (List.drop k bBytes) borrow).getD (j + 1) 0 =
    (bigSub.go (List.drop (k + 1) aBytes) (List.drop (k + 1) bBytes)
      (if (aBytes.getD k 0).toNat + 256 - (bBytes.getD k 0).toNat - borrow ≥ 256 then 0 else 1)).getD j 0 := by
  rw [ show List.drop k aBytes = aBytes.getD k 0 :: List.drop ( k + 1 ) aBytes from ?_, show List.drop k bBytes = bBytes.getD k 0 :: List.drop ( k + 1 ) bBytes from ?_ ];
  · rfl;
  · rw [ List.drop_eq_getElem_cons ];
    grind;
    linarith;
  · aesop

theorem sub8_eq_bigSub_byte (a b : UInt8) (borrow : Nat) (hb : borrow ≤ 1) :
    (sub8 a b (decide (borrow = 1))).1 =
    ((a.toNat + 256 - b.toNat - borrow) % 256).toUInt8 := by
  interval_cases borrow <;> simp +decide [ sub8 ]

theorem sub8_carry_eq_bigSub_borrow (a b : UInt8) (borrow : Nat) (hb : borrow ≤ 1) :
    (if (sub8 a b (decide (borrow = 1))).2.c then 1 else 0) =
    (if a.toNat + 256 - b.toNat - borrow ≥ 256 then 0 else 1) := by
  unfold sub8; split_ifs <;> simp_all +decide ;
  · omega;
  · omega;
  · omega

set_option maxHeartbeats 12800000 in
theorem subtract_a_loop
    (n : Nat) (aBytes bBytes : List UInt8)
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hfits : 104 + 2 * n < 0x8000)
    (rem : Nat) (borrow : Nat)
    (hrem : 0 < rem) (hremn : rem ≤ n) (hb : borrow ≤ 1) (hrem65 : rem ≤ 65535)
    (s : State)
    (hpc : s.regPC = 38) (hnh : s.halted = false) (hsp : s.regSP = 0x8000) (hout : s.output = [])
    (hhl : s.hl = (104 + (n - rem)).toUInt16)
    (hde : s.de = (104 + n + (n - rem)).toUInt16)
    (hbc : s.bc = rem.toUInt16)
    (hcarry : s.regF.c = decide (borrow = 1))
    (hprog : ∀ pos, pos < 104 → s.mem.read pos.toUInt16 =
      (encodeProgram (bigGcdProgram n)).getD pos 0)
    (haRem : ∀ j, j < rem → s.mem.read (104 + (n - rem) + j).toUInt16 =
      aBytes.getD (n - rem + j) 0)
    (hbAll : ∀ j, j < n → s.mem.read (104 + n + j).toUInt16 =
      bBytes.getD j 0)
    (hmsz : s.mem.data.data.size = 65536) :
    ∃ k,
      (run s k).regPC = 0 ∧ (run s k).regSP = 0x8000 ∧
      (run s k).halted = false ∧ (run s k).output = [] ∧
      (∀ j, j < rem → (run s k).mem.read (104 + (n - rem) + j).toUInt16 =
        (bigSub.go (List.drop (n - rem) aBytes) (List.drop (n - rem) bBytes) borrow).getD j 0) ∧
      (∀ j, j < n - rem → (run s k).mem.read (104 + j).toUInt16 =
        s.mem.read (104 + j).toUInt16) ∧
      (∀ j, j < n → (run s k).mem.read (104 + n + j).toUInt16 =
        bBytes.getD j 0) ∧
      (∀ pos, pos < 104 → (run s k).mem.read pos.toUInt16 =
        (encodeProgram (bigGcdProgram n)).getD pos 0) ∧
      (run s k).mem.data.data.size = 65536 := by
  revert hrem hremn hrem65 borrow hb s hpc hnh hsp hout hhl hde hbc hcarry hprog haRem hbAll hmsz
  induction rem with
  | zero => intros; omega
  | succ rem' ih =>
    intro hrem hremn hrem65 borrow hb s hpc hnh hsp hout hhl hde hbc hcarry hprog haRem hbAll hmsz
    have hhl_ge : s.hl.toNat ≥ 104 := by rw [hhl]; simp; omega
    have hhl_lt : s.hl.toNat < 0x7FFE := by rw [hhl]; simp; omega
    by_cases hrem' : 0 < rem'
    · -- CONTINUING
      have hbc_ne : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) ≠ 0 := by
        rw [hbc, bc_after_dec (rem' + 1) (by omega) (by omega)]
        exact hilo_or_ne_zero rem' hrem' (by omega)
      have IT := sub_a_one_iter_continue s n hpc hnh hsp hhl_ge hhl_lt hprog hmsz hbc_ne
      set result := (sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).1 with hresult_def
      set flags := (sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).2 with hflags_def
      set newBorrow := if flags.c then 1 else 0 with hnewBorrow_def
      obtain ⟨hIT1, hIT2, hIT3, hIT4, hIT5, hIT6, hIT7, hIT8, hIT9, hIT10, hIT11, hIT12⟩ := IT
      -- Apply IH to run s 14
      have IH_hl : (run s 14).hl = (104 + (n - rem')).toUInt16 := by
        rw [hIT5, hhl]; apply UInt16.ext; simp [UInt16.toNat_add, UInt16.toNat_ofNat]; omega
      have IH_de : (run s 14).de = (104 + n + (n - rem')).toUInt16 := by
        rw [hIT6, hde]; apply UInt16.ext; simp [UInt16.toNat_add, UInt16.toNat_ofNat]; omega
      have IH_bc : (run s 14).bc = rem'.toUInt16 := by
        rw [hIT7, hbc]; apply UInt16.ext; simp [UInt16.toNat_ofNat]
      have newBorrow_le : newBorrow ≤ 1 := by
        simp only [hnewBorrow_def]; split_ifs <;> omega
      have IH_carry : (run s 14).regF.c = decide (newBorrow = 1) := by
        have : ∀ (c : Bool), c = decide ((if c = true then (1 : Nat) else 0) = 1) := by
          intro c; cases c <;> simp
        simp only [hnewBorrow_def, hflags_def] at this ⊢
        rw [hIT8]; exact this _
      have IH_prog : ∀ pos, pos < 104 → (run s 14).mem.read pos.toUInt16 =
          (encodeProgram (bigGcdProgram n)).getD pos 0 := by
        intro pos hpos; rw [hIT11 pos hpos]; exact hprog pos hpos
      have addr_eq_nat : ∀ j, 104 + (n - rem') + j = 104 + (n - (rem' + 1)) + (j + 1) := by omega
      have IH_aRem : ∀ j, j < rem' → (run s 14).mem.read (104 + (n - rem') + j).toUInt16 =
          aBytes.getD (n - rem' + j) 0 := by
        intro j hj
        rw [hIT10 (104 + (n - rem') + j).toUInt16
          (by rw [hhl]; simp [UInt16.ext_iff, UInt16.toNat_ofNat]; omega)
          (by simp [UInt16.toNat_ofNat]; omega)]
        rw [show (104 + (n - rem') + j).toUInt16 = (104 + (n - (rem' + 1)) + (j + 1)).toUInt16 from
          by congr 1; omega]
        rw [show aBytes.getD (n - rem' + j) 0 = aBytes.getD (n - (rem' + 1) + (j + 1)) 0 from
          by congr 1; omega]
        exact haRem (j + 1) (by omega)
      have IH_bAll : ∀ j, j < n → (run s 14).mem.read (104 + n + j).toUInt16 =
          bBytes.getD j 0 := by
        intro j hj
        rw [hIT10 (104 + n + j).toUInt16
          (by rw [hhl]; simp [UInt16.ext_iff, UInt16.toNat_ofNat]; omega)
          (by simp [UInt16.toNat_ofNat]; omega)]
        exact hbAll j hj
      obtain ⟨k', hk'⟩ := ih newBorrow hrem' (by omega) newBorrow_le (by omega)
        (run s 14) hIT1 hIT2 hIT3 (hIT4.trans hout)
        IH_hl IH_de IH_bc IH_carry IH_prog IH_aRem IH_bAll hIT12
      use 14 + k'
      rw [run_add]
      refine ⟨hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, ?_, ?_, hk'.2.2.2.2.2.2.1, ?_, hk'.2.2.2.2.2.2.2.2⟩
      -- Result bytes: ∀ j < rem'+1
      · intro j hj
        by_cases hj0 : j = 0
        · subst hj0; simp only [Nat.add_zero]
          have hprev : (run (run s 14) k').mem.read (104 + (n - (rem' + 1))).toUInt16 =
              (run s 14).mem.read (104 + (n - (rem' + 1))).toUInt16 :=
            hk'.2.2.2.2.2.1 (n - (rem' + 1)) (by omega)
          rw [hprev, show (104 + (n - (rem' + 1))).toUInt16 = s.hl from by rw [hhl], hIT9]
          rw [bigSub_go_drop_getD_zero aBytes bBytes n (n - (rem' + 1)) hrem haL hbL (by omega)]
          have ha_byte : s.mem.read s.hl = aBytes.getD (n - (rem' + 1)) 0 := by
            have h := haRem 0 (by omega)
            simp only [Nat.add_zero] at h; rwa [← hhl] at h
          have hb_byte : s.mem.read s.de = bBytes.getD (n - (rem' + 1)) 0 := by
            have h := hbAll (n - (rem' + 1)) (by omega); rwa [← hde] at h
          rw [ha_byte, hb_byte, hcarry]
          congr 1; congr 1
          interval_cases hrem <;> simp +decide
        · -- j = j'+1: use bigSub_go_drop_getD_succ + IH result
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have hj' : j' < rem' := by omega
          rw [show (104 + (n - (rem' + 1)) + (j' + 1)).toUInt16 =
            (104 + (n - rem') + j').toUInt16 from by congr 1; omega]
          rw [bigSub_go_drop_getD_succ aBytes bBytes n (n - (rem' + 1)) hrem j' haL hbL (by omega)]
          have hborrow_eq : newBorrow =
              (if (aBytes.getD (n - (rem' + 1)) 0).toNat + 256 -
                  (bBytes.getD (n - (rem' + 1)) 0).toNat - hrem ≥ 256 then 0 else 1) := by
            simp only [hnewBorrow_def, hflags_def]
            have ha_byte : s.mem.read s.hl = aBytes.getD (n - (rem' + 1)) 0 := by
              have h := haRem 0 (by omega)
              simp only [Nat.add_zero] at h; rwa [← hhl] at h
            have hb_byte : s.mem.read s.de = bBytes.getD (n - (rem' + 1)) 0 := by
              have h := hbAll (n - (rem' + 1)) (by omega); rwa [← hde] at h
            rw [← sub8_carry_eq_bigSub_borrow _ _ hrem (by exact borrow)]
            rw [ha_byte, hb_byte, hcarry]
          rw [← hborrow_eq, show n - (rem' + 1) + 1 = n - rem' from by omega]
          exact hk'.2.2.2.2.1 j' hj'
      -- Previously written bytes
      · intro j hj
        rw [hk'.2.2.2.2.2.1 j (by omega)]
        exact hIT10 _ (by rw [hhl]; simp [UInt16.ext_iff, UInt16.toNat_ofNat]; omega)
          (by simp [UInt16.toNat_ofNat]; omega)
      -- Prog bytes
      · intro pos hpos
        rw [hk'.2.2.2.2.2.2.2.1 pos hpos]
    · -- DONE (rem' = 0)
      have hrem0 : rem' = 0 := by omega
      subst hrem0
      have hbc_eq : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) = 0 := by
        rw [hbc]; native_decide +revert
      have IT := sub_a_one_iter_done s n hpc hnh hsp hhl_ge hhl_lt hprog hmsz hbc_eq
      set result := (sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c).1
      obtain ⟨hIT1, hIT2, hIT3, hIT4, hIT5, hIT6, hIT7, hIT8⟩ := IT
      use 14
      refine ⟨hIT1, hIT3, hIT2, hIT4.trans hout, ?_, ?_, ?_, ?_, hIT8⟩
      -- Result bytes (only j = 0)
      · intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simp only [Nat.add_zero]
        have hhl_eq : (104 + (n - (0 + 1))).toUInt16 = s.hl := by
          rw [hhl]
        rw [hhl_eq, hIT5]
        have hn1 : n - (0 + 1) = n - 1 := by omega
        rw [hn1, bigSub_go_drop_getD_zero aBytes bBytes n (n - 1) hrem haL hbL (by omega)]
        have hn1' : n - (0 + 1) = n - 1 := by omega
        have ha_byte : s.mem.read s.hl = aBytes.getD (n - 1) 0 := by
          have h := haRem 0 (by omega)
          simp only [Nat.add_zero, hn1'] at h
          rwa [← hhl] at h
        have hb_byte : s.mem.read s.de = bBytes.getD (n - 1) 0 := by
          have h := hbAll (n - 1) (by omega)
          rw [hn1'] at hde
          rwa [← hde] at h
        rw [ha_byte, hb_byte, hcarry]
        congr 1; congr 1
        interval_cases hrem <;> simp +decide
      -- Previously written bytes
      · intro j hj
        exact hIT6 _ (by rw [hhl]; simp [UInt16.ext_iff]; omega) (by simp; omega)
      -- B bytes
      · intro j hj
        rw [hIT6 _ (by rw [hhl]; simp [UInt16.ext_iff]; omega) (by simp; omega)]; exact hbAll j hj
      -- Program bytes
      · intro pos hpos; rw [hIT7 pos hpos]; exact hprog pos hpos

/-! ## §6 Subtract-A phase = setup + loop -/

theorem subtract_a_phase_impl (s : State) (n : Nat)
    (aBytes bBytes : List UInt8)
    (hpc : s.regPC = 28) (hsp : s.regSP = 0x8000)
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
    (hge : decodeBigNum aBytes ≥ decodeBigNum bBytes)
    (hmsz : s.mem.data.data.size = 65536) :
    ∃ k : Nat,
      (run s k).regPC = 0 ∧ (run s k).regSP = 0x8000 ∧
      (run s k).halted = false ∧ (run s k).output = [] ∧
      (∀ (i : Nat) (hi : i < (encodeProgram (bigGcdProgram n)).length),
        (run s k).mem.read (0 + i).toUInt16 = (encodeProgram (bigGcdProgram n))[i]) ∧
      (∀ (i : Nat) (hi : i < (bigSub aBytes bBytes).length),
        (run s k).mem.read (104 + i).toUInt16 = (bigSub aBytes bBytes)[i]) ∧
      (∀ (i : Nat) (hi : i < bBytes.length),
        (run s k).mem.read (104 + n + i).toUInt16 = bBytes[i]) ∧
      (run s k).mem.data.data.size = 65536 := by
  have h_prog : (encodeProgram (bigGcdProgram n)).length = 104 := by
    unfold bigGcdProgram at * ; aesop ( simp_config := { decide := true } ) ;
  have := sub_a_setup4 s n hpc hnh ( by
    convert hprog 28 ( by linarith ) using 1 ) ( by
    convert hprog 29 ( by linarith ) using 1 ) ( by
    convert hprog 30 ( by linarith ) using 1 ) ( by
    convert hprog 31 ( by linarith ) using 1 ) ( by
    convert hprog 32 ( by linarith ) using 1 ) ( by
    convert hprog 33 ( by linarith ) using 1 ) ( by
    convert hprog 34 ( by linarith ) using 1 ) ( by
    convert hprog 35 ( by linarith ) using 1 ) ( by
    convert hprog 36 ( by linarith ) using 1 ) ( by
    convert hprog 37 ( by linarith ) using 1 );
  have := subtract_a_loop n aBytes bBytes haL hbL hfits n 0; simp_all +decide ;
  specialize this ( by linarith ) ( run s 4 ) ; simp_all +decide [ State.hl, State.de, State.bc ] ;
  obtain ⟨ k, hk ⟩ := this ( by
    grind +suggestions ) ( by
    unfold hi16 lo16; simp +decide [ mkWord ] ;
    ext i; simp +decide [ Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq_mul_pow ] ;
    have h_mod : n % 65536 = (n % 256) + 256 * (n / 256 % 256) := by
      omega;
    rw [ h_mod ] ; norm_num [ Nat.add_mod, Nat.mul_mod ] ; ring;
    have h_mod : n % 256 < 256 ∧ n / 256 % 256 < 256 := by
      exact ⟨ Nat.mod_lt _ ( by decide ), Nat.mod_lt _ ( by decide ) ⟩;
    have h_mod : ∀ x y : ℕ, x < 256 → y < 256 → (x + y * 256) / 256 % 256 % 65536 % 65536 * 256 % 65536 ||| x = x + y * 256 := by
      intros x y hx hy; interval_cases x <;> ( revert y ; native_decide; );
    exact h_mod _ _ ( by tauto ) ( by tauto ) );
  use 4 + k; simp_all +decide [ run_add' ] ;
  intro i hi; specialize hk; have := hk.2.2.2.2.1 i; simp_all +decide [ bigSub ] ;
  convert hk.2.2.2.2.1 i _ using 1;
  · grind;
  · exact hi.trans_le ( by rw [ show bigSub aBytes bBytes = bigSub.go aBytes bBytes 0 from rfl ] ; exact bigSub_go_length aBytes bBytes 0 ( by linarith ) |> fun h => h.le.trans ( by simp +decide [ haL, hbL ] ) )

end Z80.SubtractALoopProof