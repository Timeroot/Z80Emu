import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.Demos

/-!
# Fibonacci Program Correctness

We prove that the Z80 Fibonacci program computes `Nat.fib` for all
inputs where the result fits in a byte (n ≤ 13, since fib(14) = 377 > 255).

The proof is by exhaustive verification via `native_decide` over
`Fin 14`, covering all valid inputs.  We also prove an abstract
characterisation of the loop-based Fibonacci computation at the
algorithm level.
-/

namespace Z80.FibCorrectness

open Z80 Z80.Demos

/-! ## 1. Abstract Fibonacci loop -/

/-- The iterative Fibonacci computation used by the Z80 program.
    Maintains two accumulators (prev, curr) and iterates `n` times.
    This mirrors the Z80 loop structure:
    - C = prev (fib(i-1))
    - A = curr (fib(i))
    - Loop body: (prev, curr) ← (curr, prev + curr) -/
def fibIter (prev curr : Nat) : Nat → Nat
  | 0     => curr
  | n + 1 => fibIter curr (prev + curr) n

/-
The iterative Fibonacci starting from fib(0)=0, fib(1)=1 agrees
    with `Nat.fib`.
-/
theorem fibIter_eq_fib (n : Nat) : fibIter 0 1 n = Nat.fib (n + 1) := by
  -- By induction on $n$, we can show that $fibIter (Nat.fib k) (Nat.fib (k + 1)) n = Nat.fib (k + n + 1)$.
  have h_ind : ∀ k n, fibIter (Nat.fib k) (Nat.fib (k + 1)) n = Nat.fib (k + n + 1) := by
    -- By definition of `fibIter`, we have `fibIter (Nat.fib k) (Nat.fib (k + 1)) (n + 1) = fibIter (Nat.fib (k + 1)) (Nat.fib k + Nat.fib (k + 1)) n`.
    have h_fibIter_succ : ∀ k n, fibIter (Nat.fib k) (Nat.fib (k + 1)) (n + 1) = fibIter (Nat.fib (k + 1)) (Nat.fib k + Nat.fib (k + 1)) n :=
      fun _ _ => rfl;
    intro k n; induction' n with n ih generalizing k <;> simp_all +arith +decide [ Nat.fib_add_two ] ;
    · rfl;
    · convert ih ( k + 1 ) using 1 ; simp +arith +decide [ Nat.fib_add_two ];
      simp +arith +decide [ Nat.fib_add_two ];
  simpa using h_ind 0 n

/-! ## 2. Exhaustive program verification -/

/-- The Z80 Fibonacci program produces the correct output for all
    inputs n ≤ 13 (the range where fib(n) fits in a byte).

    For each n in 0..13, this checks that the full pipeline
    (encode → load into 64 KiB memory → decode → execute → collect output)
    produces `[Nat.fib n]`.
-/
theorem fib_program_correct :
    ∀ n : Fin 14,
    eval (fibBytecode n.val.toUInt8) = [(Nat.fib n.val).toUInt8] := by
  native_decide

/-- For inputs beyond 13, the Z80 program still terminates but the
    result wraps due to 8-bit modular arithmetic at each addition step.
    Note: this is NOT simply `fib(n) mod 256` because the modular
    reduction happens at each addition, not just at the end. -/
theorem fib_14_wraps : eval (fibBytecode 14) = [121] := by native_decide
-- fib(14) = 377, and the Z80 8-bit computation gives 377 mod 256 = 121
-- (here wrapping hasn't cascaded yet since fib(13) = 233 < 256)

theorem fib_20_wraps : eval (fibBytecode 20) = [109] := by native_decide
-- The Z80 8-bit computation diverges from fib(20) mod 256 = 109
-- due to cascading modular reductions in intermediate steps

end Z80.FibCorrectness