import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.Demos
import Z80Emu.MemoryModel

/-!
# GCD Program Correctness

We prove that the Z80 GCD program computes `Nat.gcd` for all nonzero
byte inputs.  The proof proceeds in two layers:

1. **Algorithmic correctness** — We define the subtraction-based
   Euclidean algorithm (`subGcd`) on natural numbers and prove it
   equals `Nat.gcd` for positive inputs.  This is the mathematical
   heart of the proof.

2. **Program verification** — We verify exhaustively (via `native_decide`
   over `Fin 256 × Fin 256`) that the Z80 bytecode produced by
   `gcdBytecode` computes the same result.  Since `UInt8` has only
   256 values, this constitutes a complete proof — not mere testing.
-/

namespace Z80.GCDCorrectness

open Z80 Z80.Demos

/-! ## 1. Abstract subtraction-based GCD -/

/-- The subtraction-based Euclidean algorithm.

At each step:
- If `a = b`, the GCD is `a`.
- If `a > b`, replace `a` with `a − b`.
- If `b > a`, replace `b` with `b − a`.

This is exactly the logic implemented by the Z80 GCD program's
inner loop.
-/
def subGcd (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0
  else if a = b then a
  else if a > b then subGcd (a - b) b
  else subGcd a (b - a)
termination_by a + b
decreasing_by all_goals omega

/-
The subtraction-based GCD agrees with `Nat.gcd` on positive inputs.
-/
theorem subGcd_eq_gcd (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    subGcd a b = Nat.gcd a b := by
  induction' n : a + b using Nat.strong_induction_on with n ih generalizing a b;
  unfold subGcd;
  split_ifs <;> simp_all +decide;
  · convert ih ( a - b + b ) ( by omega ) ( a - b ) b ( Nat.sub_ne_zero_of_lt ‹_› ) hb rfl using 1;
    rw [ Nat.gcd_sub_self_left ( le_of_lt ‹_› ) ];
  · rw [ ih ( a + ( b - a ) ) ( by omega ) a ( b - a ) ha ( Nat.sub_ne_zero_of_lt ( lt_of_le_of_ne ‹_› ‹_› ) ) rfl, Nat.gcd_sub_self_right ( by omega ) ]

/-! ## 2. Byte-level GCD -/

/-- The GCD operation as performed by the Z80 program, at the byte level. -/
def byteGcd (a b : UInt8) : UInt8 :=
  (subGcd a.toNat b.toNat).toUInt8

/-
`byteGcd` computes the mathematical GCD (as a `Nat`) for nonzero byte inputs.
-/
theorem byteGcd_toNat_eq_gcd (a b : UInt8) (ha : a ≠ 0) (hb : b ≠ 0) :
    (byteGcd a b).toNat = Nat.gcd a.toNat b.toNat := by
  -- By definition of `byteGcd`, we have `byteGcd a b = subGcd a.toNat b.toNat`.
  simp [byteGcd];
  rw [ Nat.mod_eq_of_lt ];
  · apply subGcd_eq_gcd;
    · exact fun h => absurd (Eq.symm (UInt8.toNat_inj.mp (Eq.symm h))) ha;
    · exact fun h => hb <| by simpa [ UInt8.ext_iff ] using h;
  · -- Since `a` and `b` are `UInt8`, their values are between 0 and 255. The `subGcd` function will eventually reach a point where one of the numbers is zero, and the other is the gcd. Since the gcd of two numbers less than 256 will also be less than 256, this should hold.
    have h_subGcd_lt_256 : ∀ (a b : Nat), a < 256 → b < 256 → subGcd a b < 256 := by
      intros a b ha hb;
      interval_cases a <;> ( revert b ; native_decide; );
    exact h_subGcd_lt_256 _ _ ( a.toNat_lt ) ( b.toNat_lt )

/-! ## 3. Exhaustive verification of the Z80 program -/

/-- The Z80 GCD program produces the correct output for **all** nonzero byte inputs.

This is verified by exhaustive evaluation over all 255 × 255 = 65 025
input pairs.  Since `UInt8` has exactly 256 values, this constitutes a
*complete* proof — every possible nonzero input is checked.

The proof demonstrates genuine program correctness: the actual Z80
bytecode (produced by `gcdBytecode`, which encodes the instruction
sequence → loads it into a 64 KiB memory model → decodes and executes
it instruction by instruction) produces the mathematically correct GCD
for every valid input.
-/
theorem gcd_program_correct :
    ∀ a b : Fin 256, a.val ≠ 0 → b.val ≠ 0 →
    eval (gcdBytecode a.val.toUInt8 b.val.toUInt8) =
      [(Nat.gcd a.val b.val).toUInt8] := by
  native_decide

/-- The Z80 GCD program also correctly handles the case `a = b = 0`
    (outputs 0, since both registers start at 0 and the equality
    branch is taken immediately). -/
theorem gcd_program_zero_zero :
    eval (gcdBytecode 0 0) = [0] := by native_decide

end Z80.GCDCorrectness