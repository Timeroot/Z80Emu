import Mathlib
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.GCDCorrectness

/-!
# BigNum GCD — Pure Algorithm Correctness

We prove that the subtraction-based GCD algorithm, when implemented
on same-length byte lists using `bigSub` and `bigCmp`, correctly
computes `Nat.gcd` on the decoded values.

## Main results

* `bigGcdWf` — a well-founded (terminating) version of `bigGcdLoop`
  for same-length nonzero byte lists.
* `bigGcdWf_correct` — the decoded result equals `Nat.gcd`.
* `bigGcdWf_length` — the result has the same length as the inputs.
* `bigGcdWf_encodeBigNum` — the result equals
  `encodeBigNum (Nat.gcd ...) n`.
-/

namespace Z80.BigNumGCDAlgorithm

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.GCDCorrectness

/-!
## Well-founded byte-level GCD

The termination measure is `decodeBigNum a + decodeBigNum b`,
which strictly decreases at each recursive call because
`bigSub` correctly subtracts decoded values.
-/

/-- Well-founded byte-level subtraction GCD.
    Requires same-length, nonzero byte lists. -/
def bigGcdWf (a b : List UInt8)
    (hlen : a.length = b.length)
    (ha : 0 < decodeBigNum a) (hb : 0 < decodeBigNum b) : List UInt8 :=
  if heq : decodeBigNum a = decodeBigNum b then a
  else if hgt : decodeBigNum b < decodeBigNum a then
    bigGcdWf (bigSub a b) b
      ((bigSub_length a b hlen).trans hlen)
      (by rw [decodeBigNum_bigSub a b hlen (by omega)]; omega)
      hb
  else -- decodeBigNum a < decodeBigNum b
    bigGcdWf a (bigSub b a)
      (hlen.trans (bigSub_length b a hlen.symm).symm)
      ha
      (by rw [decodeBigNum_bigSub b a hlen.symm (by omega)]; omega)
termination_by decodeBigNum a + decodeBigNum b
decreasing_by
  · rw [decodeBigNum_bigSub a b hlen (by omega)]; omega
  · rw [decodeBigNum_bigSub b a hlen.symm (by omega)]; omega

/-!
## Correctness: decoded result equals `Nat.gcd`
-/

theorem bigGcdWf_correct (a b : List UInt8)
    (hlen : a.length = b.length)
    (ha : 0 < decodeBigNum a) (hb : 0 < decodeBigNum b) :
    decodeBigNum (bigGcdWf a b hlen ha hb) =
      Nat.gcd (decodeBigNum a) (decodeBigNum b) := by
  unfold bigGcdWf
  split_ifs with heq hgt
  · -- a = b: gcd(x, x) = x
    exact heq ▸ (Nat.gcd_self _).symm
  · -- a > b: gcd(a−b, b) = gcd(a, b)
    rw [bigGcdWf_correct]
    rw [decodeBigNum_bigSub a b hlen (by omega)]
    exact Nat.gcd_sub_self_left (by omega)
  · -- b > a: gcd(a, b−a) = gcd(a, b)
    rw [bigGcdWf_correct]
    rw [decodeBigNum_bigSub b a hlen.symm (by omega)]
    exact Nat.gcd_sub_self_right (by omega)
termination_by decodeBigNum a + decodeBigNum b
decreasing_by
  · rw [decodeBigNum_bigSub a b hlen (by omega)]; omega
  · rw [decodeBigNum_bigSub b a hlen.symm (by omega)]; omega

/-!
## Length preservation
-/

theorem bigGcdWf_length (a b : List UInt8)
    (hlen : a.length = b.length)
    (ha : 0 < decodeBigNum a) (hb : 0 < decodeBigNum b) :
    (bigGcdWf a b hlen ha hb).length = a.length := by
  unfold bigGcdWf
  split_ifs with heq hgt
  · rfl
  · rw [bigGcdWf_length]
    exact bigSub_length a b hlen
  · exact bigGcdWf_length _ _ _ _ _
termination_by decodeBigNum a + decodeBigNum b
decreasing_by
  · rw [decodeBigNum_bigSub a b hlen (by omega)]; omega
  · rw [decodeBigNum_bigSub b a hlen.symm (by omega)]; omega

/-!
## The result equals `encodeBigNum (Nat.gcd …) n`

Since the result is a byte list of the same length whose decoded
value is `Nat.gcd`, it must equal the encoding of that GCD.
-/

theorem bigGcdWf_eq_encodeBigNum (a b : List UInt8)
    (hlen : a.length = b.length)
    (ha : 0 < decodeBigNum a) (hb : 0 < decodeBigNum b) :
    bigGcdWf a b hlen ha hb =
      encodeBigNum (Nat.gcd (decodeBigNum a) (decodeBigNum b)) a.length := by
  have h1 := bigGcdWf_correct a b hlen ha hb
  have h2 := bigGcdWf_length a b hlen ha hb
  rw [← h2, ← h1]
  exact (encodeBigNum_decodeBigNum _).symm

end Z80.BigNumGCDAlgorithm
