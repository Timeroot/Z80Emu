import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.MemoryModel
import Z80Emu.BigNumGCDPhaseHelpers

/-!
# Output Phase Proof

Proves that the output section of the BigNum GCD Z80 program
correctly outputs all bytes of `aBytes` and halts.
-/

namespace Z80.OutputPhaseProof

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem output_loop_first4 (s : State)
    (hpc : s.regPC = 94) (hnh : s.halted = false)
    (h94 : s.mem.read 94 = 0x7E) (h95 : s.mem.read 95 = 0xD3)
    (h96 : s.mem.read 96 = 0x00) (h97 : s.mem.read 97 = 0x23)
    (h98 : s.mem.read 98 = 0x0B) :
    let s4 := run s 4
    s4.output = s.output ++ [s.mem.read s.hl] ∧
    s4.regPC = 99 ∧
    s4.mem = s.mem ∧
    s4.halted = false ∧
    s4.regSP = s.regSP ∧
    s4.regB = hi16 (s.bc - 1) ∧
    s4.regC = lo16 (s.bc - 1) ∧
    s4.regH = hi16 (s.hl + 1) ∧
    s4.regL = lo16 (s.hl + 1) := by
  simp only [show (4 : Nat) = 1 + 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h94, h95, h96, h97, h98,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem output_loop_last3 (s : State)
    (hpc : s.regPC = 99) (hnh : s.halted = false)
    (h99 : s.mem.read 99 = 0x78) (h100 : s.mem.read 100 = 0xB1)
    (h101 : s.mem.read 101 = 0x20) (h102 : s.mem.read 102 = 0xF7) :
    let s3 := run s 3
    s3.mem = s.mem ∧
    s3.halted = false ∧
    s3.regSP = s.regSP ∧
    s3.output = s.output ∧
    s3.regB = s.regB ∧
    s3.regC = s.regC ∧
    s3.regH = s.regH ∧
    s3.regL = s.regL ∧
    (if s.regB ||| s.regC = 0
     then s3.regPC = 103
     else s3.regPC = 94) := by
  simp only [show (3 : Nat) = 1 + 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h99, h100, h101, h102,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8]
  split_ifs <;> simp_all +decide

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem halt_step (s : State)
    (hpc : s.regPC = 103) (hnh : s.halted = false)
    (h103 : s.mem.read 103 = 0x76) :
    (step s).halted = true ∧ (step s).output = s.output ∧ (step s).mem = s.mem := by
  simp only [step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, h103, exec]

set_option maxHeartbeats 819200000 in
set_option linter.unusedSimpArgs false in
theorem output_setup (s : State) (nw : Word)
    (hpc : s.regPC = 88) (hnh : s.halted = false)
    (h88 : s.mem.read 88 = 0x21)
    (h89 : s.mem.read 89 = 0x68) (h90 : s.mem.read 90 = 0x00)
    (h91 : s.mem.read 91 = 0x01)
    (h92 : s.mem.read 92 = lo16 nw) (h93 : s.mem.read 93 = hi16 nw) :
    let s2 := run s 2
    s2.regPC = 94 ∧ s2.halted = false ∧
    s2.mem = s.mem ∧ s2.output = s.output ∧ s2.regSP = s.regSP ∧
    s2.regH = 0x00 ∧ s2.regL = 0x68 ∧
    s2.regB = hi16 nw ∧ s2.regC = lo16 nw := by
  simp only [show (2 : Nat) = 1 + 1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h88, h89, h90, h91, h92, h93,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                uint16_hilo_roundtrip]
  refine ⟨?_, ?_⟩ <;> {
    clear h88 h89 h90 h91 h92 h93 hpc hnh s
    cases nw; native_decide +revert }

theorem output_loop_body (s : State)
    (hpc : s.regPC = 94) (hnh : s.halted = false)
    (h94 : s.mem.read 94 = 0x7E) (h95 : s.mem.read 95 = 0xD3)
    (h96 : s.mem.read 96 = 0x00) (h97 : s.mem.read 97 = 0x23)
    (h98 : s.mem.read 98 = 0x0B) (h99 : s.mem.read 99 = 0x78)
    (h100 : s.mem.read 100 = 0xB1) (h101 : s.mem.read 101 = 0x20)
    (h102 : s.mem.read 102 = 0xF7) :
    let s7 := run s 7
    s7.output = s.output ++ [s.mem.read s.hl] ∧
    s7.mem = s.mem ∧
    s7.halted = false ∧
    s7.regSP = s.regSP ∧
    s7.regH = hi16 (s.hl + 1) ∧
    s7.regL = lo16 (s.hl + 1) ∧
    s7.regB = hi16 (s.bc - 1) ∧
    s7.regC = lo16 (s.bc - 1) ∧
    (if hi16 (s.bc - 1) ||| lo16 (s.bc - 1) = 0
     then s7.regPC = 103
     else s7.regPC = 94) := by
  have h7 : (7 : Nat) = 4 + 3 := by omega
  rw [h7, run_add]
  obtain ⟨hout4, hpc4, hmem4, hnh4, hsp4, hB4, hC4, hH4, hL4⟩ :=
    output_loop_first4 s hpc hnh h94 h95 h96 h97 h98
  obtain ⟨hmem7, hnh7, hsp7, hout7, hB7, hC7, hH7, hL7, hpc7⟩ :=
    output_loop_last3 (run s 4) hpc4 hnh4
      (by rw [hmem4]; exact h99) (by rw [hmem4]; exact h100)
      (by rw [hmem4]; exact h101) (by rw [hmem4]; exact h102)
  exact ⟨by rw [hout7, hout4], by rw [hmem7, hmem4], hnh7,
         by rw [hsp7, hsp4], by rw [hH7, hH4], by rw [hL7, hL4],
         by rw [hB7, hB4], by rw [hC7, hC4],
         by rw [hB4, hC4] at hpc7; exact hpc7⟩

-- ═══════════════════════════════════════════════════════
-- Full output loop by induction on remaining bytes
-- ═══════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
open BigNumGCDPhaseHelpers in
theorem output_loop_complete
    (remaining : List UInt8) :
    ∀ (s : State),
    remaining ≠ [] →
    remaining.length ≤ 65535 →
    s.regPC = 94 → s.halted = false →
    s.bc = remaining.length.toUInt16 →
    s.mem.read 94 = 0x7E → s.mem.read 95 = 0xD3 →
    s.mem.read 96 = 0x00 → s.mem.read 97 = 0x23 →
    s.mem.read 98 = 0x0B → s.mem.read 99 = 0x78 →
    s.mem.read 100 = 0xB1 → s.mem.read 101 = 0x20 →
    s.mem.read 102 = 0xF7 → s.mem.read 103 = 0x76 →
    (∀ (i : Nat) (hi : i < remaining.length),
      s.mem.read (s.hl + i.toUInt16) = remaining.get ⟨i, hi⟩) →
    ∃ k, (run s k).output = s.output ++ remaining ∧
         (run s k).halted = true ∧
         (run s k).mem = s.mem := by
  induction remaining with
  | nil => intro s hne; exact absurd rfl hne
  | cons b rest ih =>
    intro s _ hbound hpc hnh hbc h94 h95 h96 h97 h98 h99 h100 h101 h102 h103 hdata
    obtain ⟨hout7, hmem7, hnh7, _, hH7, hL7, hB7, hC7, hpc7⟩ :=
      output_loop_body s hpc hnh h94 h95 h96 h97 h98 h99 h100 h101 h102
    have hbyte : s.mem.read s.hl = b := by
      have h0 := hdata 0 (by simp); simpa using h0
    rw [hbyte] at hout7
    have hhl7 : (run s 7).hl = s.hl + 1 := by
      show mkWord (run s 7).regH (run s 7).regL = s.hl + 1
      rw [hH7, hL7]; exact mkWord_hi_lo _
    have hbc7 : (run s 7).bc = s.bc - 1 := by
      show mkWord (run s 7).regB (run s 7).regC = s.bc - 1
      rw [hB7, hC7]; exact mkWord_hi_lo _
    by_cases hrest : rest = []
    · -- Base case: remaining = [b]
      subst hrest
      have hbc_one : s.bc = 1 := by
        rw [hbc]; simp [Nat.toUInt16, UInt16.ext_iff, UInt16.toNat_ofNat]
      have hbc_zero : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) = 0 := by
        rw [hbc_one]; native_decide
      simp only [hbc_zero, ↓reduceIte] at hpc7
      have h103' : (run s 7).mem.read 103 = 0x76 := by rw [hmem7]; exact h103
      obtain ⟨hhalted_h, hout_h, hmem_h⟩ := halt_step (run s 7) hpc7 hnh7 h103'
      have hrun8 : run s (7 + 1) = step (run s 7) := by
        rw [run_add]; show run (run s 7) 1 = _
        show (if (run s 7).halted = true then _ else _) = _; simp [hnh7]
      exact ⟨7 + 1, by rw [hrun8, hout_h, hout7],
                    by rw [hrun8]; exact hhalted_h,
                    by rw [hrun8, hmem_h, hmem7]⟩
    · -- Inductive case: remaining = b :: rest with rest ≠ []
      have hbc_ne_zero : s.bc - 1 ≠ 0 := by
        rw [hbc]
        have hlen_pos : 0 < rest.length := by
          cases rest with | nil => exact absurd rfl hrest | cons _ _ => simp
        have hlen_bound : rest.length < 65536 := by simp at hbound; omega
        simp only [List.length_cons, Nat.toUInt16]
        simp [UInt16.ext_iff, UInt16.toNat_ofNat]
        omega
      have hbc_hilo_ne : hi16 (s.bc - 1) ||| lo16 (s.bc - 1) ≠ 0 :=
        mt (uint16_hilo_or_eq_zero_iff _).mp hbc_ne_zero
      have hpc7' : (run s 7).regPC = 94 := by
        simp only [if_neg hbc_hilo_ne] at hpc7; exact hpc7
      have hbc_rest : (run s 7).bc = rest.length.toUInt16 := by
        rw [hbc7, hbc]; simp [Nat.toUInt16]
      have hdata' : ∀ (i : Nat) (hi : i < rest.length),
          (run s 7).mem.read ((run s 7).hl + i.toUInt16) = rest.get ⟨i, hi⟩ := by
        intro i hi; rw [hmem7, hhl7]
        have h_addr : s.hl + 1 + i.toUInt16 = s.hl + (i + 1).toUInt16 := by
          simp [UInt16.ext_iff, UInt16.toNat_add, UInt16.toNat_ofNat]; omega
        rw [h_addr]
        have hi' : i + 1 < (b :: rest).length := by simp; omega
        have h := hdata (i + 1) hi'
        simp only [List.get, List.length_cons] at h
        convert h using 2
      have hRem_bound' : rest.length ≤ 65535 := by simp at hbound; omega
      obtain ⟨k', hout', hhalted', hmem'⟩ := ih (run s 7) hrest hRem_bound'
          hpc7' hnh7 hbc_rest
          (by rw [hmem7]; exact h94) (by rw [hmem7]; exact h95)
          (by rw [hmem7]; exact h96) (by rw [hmem7]; exact h97)
          (by rw [hmem7]; exact h98) (by rw [hmem7]; exact h99)
          (by rw [hmem7]; exact h100) (by rw [hmem7]; exact h101)
          (by rw [hmem7]; exact h102) (by rw [hmem7]; exact h103)
          hdata'
      exact ⟨7 + k',
             by rw [run_add, hout', hout7]; simp [List.append_assoc],
             by rw [run_add]; exact hhalted',
             by rw [run_add, hmem', hmem7]⟩

end Z80.OutputPhaseProof
