import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.MemoryModel
import Z80Emu.BigNumGCDPhaseHelpers
import Z80Emu.SubtractPhaseProof

/-!
# Subtract Loop — Composition Helpers

Helper lemmas for composing the instruction blocks from SubtractPhaseProof
into the full subtract loop iteration and phase proofs.

The iteration proof composes 6 building blocks (14 Z80 steps total):
1. sub_first5 (5 steps): SBC + write result to memory
2. sub_loop_inc_dec (3 steps): advance HL, DE; decrement BC
3. sub_loop_push_af (1 step): save AF to stack
4. sub_loop_test_bc (2 steps): test if BC = 0
5. sub_loop_pop_continue/done (3 steps): restore AF, jump back or exit
-/

namespace Z80.SubtractLoopProof

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers
open Z80.SubtractPhaseProof

theorem run_add' (s : State) (m n : Nat) : run s (m + n) = run (run s m) n := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add, run]; split
    · rename_i hh; symm; induction n with | zero => rfl | succ n _ => simp [run, hh]
    · exact ih (step s)

/-! ## sub8 ↔ bigSub.go correspondence -/

theorem sub8_result_eq (a b : UInt8) (carry : Bool) :
    (sub8 a b carry).1 =
      ((a.toNat + 256 - b.toNat - if carry then 1 else 0) % 256).toUInt8 := by
  unfold sub8; grind +qlia

theorem sub8_carry_eq (a b : UInt8) (carry : Bool) :
    ((sub8 a b carry).2.c = true) ↔
      (a.toNat + 256 - b.toNat - if carry then 1 else 0) < 256 := by
  simp +decide [sub8]

/-! ## Combined first 5 steps -/

set_option maxHeartbeats 1600000000 in
set_option linter.unusedSimpArgs false in
/-- SBC computation + write result to memory (5 Z80 steps from PC=38). -/
theorem sub_first5 (s : State)
    (hpc : s.regPC = 38) (hnh : s.halted = false)
    (h38 : s.mem.read 38 = 0x7E) (h39 : s.mem.read 39 = 0xEB)
    (h40 : s.mem.read 40 = 0x9E) (h41 : s.mem.read 41 = 0xEB)
    (h42 : s.mem.read 42 = 0x77) :
    let s5 := run s 5
    let (result, flags) := sub8 (s.mem.read s.hl) (s.mem.read s.de) s.regF.c
    s5.regPC = 43 ∧ s5.halted = false ∧
    s5.regA = result ∧ s5.regF = flags ∧
    s5.regSP = s.regSP ∧ s5.output = s.output ∧
    s5.regH = s.regH ∧ s5.regL = s.regL ∧
    s5.regB = s.regB ∧ s5.regC = s.regC ∧
    s5.regD = s.regD ∧ s5.regE = s.regE ∧
    s5.mem = s.mem.write s.hl result := by
  simp only [show (5 : Nat) = 1+1+1+1+1 from by omega, run, hnh, step, hnh, hpc]
  simp +decide [decodeMem, Nat.toUInt16, decodeRoot, opcX, opcY, opcZ, opcP, opcQ,
                h38, h39, h40, h41, h42,
                exec, readLoc8, writeLoc8, readReg16, writeReg16,
                loc8of, reg8of, reg16of, reg16sof, aluOf, condOf,
                State.hl, State.bc, State.de, State.af,
                State.setHL, State.setBC, State.setDE, State.setAF,
                mkWord, lo16, hi16, Memory.read16, evalCond, signExtend,
                alu8, sub8, add8, parity8, testBit8,
                Flags.toByte, Flags.ofByte, setBit8, clearBit8, toSigned]

end Z80.SubtractLoopProof
