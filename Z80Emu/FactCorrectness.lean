import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.Demos

/-!
# Factorial Program Correctness

We prove that the Z80 Factorial program computes `Nat.factorial` for all
inputs where the result fits in a byte (n ≤ 5, since 6! = 720 > 255).

The proof is by exhaustive verification via `native_decide` over
`Fin 6`, covering all valid inputs.  We also characterise the
multiply-by-repeated-addition algorithm used by the program.
-/

namespace Z80.FactCorrectness

open Z80 Z80.Demos

/-! ## 1. Abstract factorial by repeated addition -/

/-- Multiplication by repeated addition, as implemented by the Z80
    inner loop.  Computes `a * b` by adding `a` to itself `b` times. -/
def mulByAdd (a : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => a + mulByAdd a n

/-
`mulByAdd` agrees with multiplication.
-/
theorem mulByAdd_eq_mul (a b : Nat) : mulByAdd a b = a * b := by
  induction' b with n ih;
  · rfl;
  · exact show a + mulByAdd a n = a * ( n + 1 ) by linarith

/-- Iterative factorial using `mulByAdd`.  Computes `n!` by
    multiplying 1 × 2 × 3 × … × n, where each multiplication
    is performed by repeated addition. -/
def factIter (acc : Nat) : Nat → Nat
  | 0     => acc
  | n + 1 => factIter (mulByAdd acc (n + 1)) n -- wrong order, let me fix

/-- The iterative factorial starting from acc=1, counting from n down to 1,
    mirrors the Z80 program structure where B counts down from n. -/
def factLoop (acc : Nat) (k : Nat) : Nat :=
  match k with
  | 0     => acc
  | k + 1 => factLoop (acc * (k + 1)) k

theorem factLoop_eq (acc k : Nat) : factLoop acc k = acc * Nat.factorial k := by
  induction' k with k ih generalizing acc;
  · aesop;
  · exact ih ( acc * ( k + 1 ) ) ▸ by push_cast [ Nat.factorial_succ ] ; ring;

/-! ## 2. Exhaustive program verification -/

/-- The Z80 Factorial program produces the correct output for all
    inputs n ≤ 5 (the range where n! fits in a byte).

    For each n in 0..5, this checks that the full Z80 execution
    pipeline produces `[Nat.factorial n]`.
-/
theorem fact_program_correct :
    ∀ n : Fin 6,
    eval (factBytecode n.val.toUInt8) = [(Nat.factorial n.val).toUInt8] := by
  native_decide

/-- For n = 6, the result wraps modulo 256 since 6! = 720 > 255. -/
theorem fact_6_wraps : eval (factBytecode 6) = [208] := by native_decide
-- Note: 6! = 720, 720 mod 256 = 208

end Z80.FactCorrectness