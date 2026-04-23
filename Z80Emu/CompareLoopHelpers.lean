import Mathlib
import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.BigNumGCD
import Z80Emu.BigNumGCDCorrectness
import Z80Emu.MemoryModel
import Z80Emu.BigNumGCDPhaseHelpers

/-!
# Compare Loop — Helper Lemmas

Decomposes the compare loop induction into manageable pieces.
No dependency on ComparePhaseProof to avoid cycles.
-/

namespace Z80.CompareLoopHelpers

open Z80 Z80.BigNumGCD Z80.BigNumGCDCorrectness Z80.BigNumGCDPhaseHelpers

/-! ## §0 Pure bigCmp lemmas (moved from ComparePhaseProof to break cycle) -/

theorem bigCmp_append (a b : List UInt8) (x y : UInt8)
    (hlen : a.length = b.length) :
    bigCmp (a ++ [x]) (b ++ [y]) =
      match compare x.toNat y.toNat with
      | .eq => bigCmp a b
      | ord => ord := by
  induction' a with a a_ih generalizing b;
  · cases b <;> simp_all +decide;
    cases h : compare x.toNat y.toNat <;> simp_all +decide;
    · exact?;
    · cases x ; cases y ; simp_all +decide [ UInt8.toNat_inj ];
      native_decide +revert;
    · unfold bigCmp; aesop;
  · rcases b with ( _ | ⟨ b, b_ih ⟩ ) <;> simp_all +decide;
    rw [ show bigCmp ( a :: ( a_ih ++ [ x ] ) ) ( b :: ( b_ih ++ [ y ] ) ) = match bigCmp ( a_ih ++ [ x ] ) ( b_ih ++ [ y ] ) with | Ordering.eq => compare a.toNat b.toNat | ord => ord from rfl ];
    rw [ ‹∀ b : List UInt8, b_ih.length = b.length → bigCmp ( a_ih ++ [ x ] ) ( b ++ [ y ] ) = _› _ rfl ];
    rw [ show bigCmp ( a :: a_ih ) ( b :: b_ih ) = match bigCmp a_ih b_ih with | Ordering.eq => compare a.toNat b.toNat | ord => ord from rfl ];
    cases compare x.toNat y.toNat <;> cases bigCmp a_ih b_ih <;> rfl

theorem bigCmp_last_diff (a b : List UInt8) (x y : UInt8)
    (hlen : a.length = b.length) (hne : x ≠ y) :
    bigCmp (a ++ [x]) (b ++ [y]) = compare x.toNat y.toNat := by
  rw [bigCmp_append a b x y hlen]
  have : compare x.toNat y.toNat ≠ .eq := by
    intro h; rw [compare_eq_iff_eq] at h; exact hne (UInt8.ext (by omega))
  cases hc : compare x.toNat y.toNat <;> simp_all

theorem bigCmp_take_eq (a b : List UInt8) (rem : Nat)
    (hlen : a.length = b.length) (hrem : rem ≤ a.length)
    (hsuf : ∀ i (hi₁ : rem ≤ i) (hi₂ : i < a.length),
      a[i] = b[i]'(hlen ▸ hi₂)) :
    bigCmp a b = bigCmp (a.take rem) (b.take rem) := by
  revert hsuf hlen hrem;
  induction' rem with rem ih generalizing a b;
  · intro hlen _ hsuf;
    have h_eq : a = b := by
      refine' List.ext_get _ _ <;> aesop;
    grind +suggestions;
  · cases a <;> cases b <;> simp_all +decide [ Nat.succ_eq_add_one ];
    intro hlen hrem h; specialize ih _ _ hlen ( by linarith ) ( fun i hi₁ hi₂ => h ( i + 1 ) ( by linarith ) ( by linarith ) ) ; simp_all +decide [ bigCmp ] ;

/-! ## §1 UInt16 arithmetic helpers -/

/-- hi16 and lo16 of (rem.toUInt16) when OR'd together are nonzero iff rem > 0. -/
theorem hilo_or_ne_zero (rem : Nat) (hpos : 0 < rem) (hle : rem ≤ 65535) :
    hi16 rem.toUInt16 ||| lo16 rem.toUInt16 ≠ 0 := by
  have h_rem_pos : rem.toUInt16 ≠ 0 := by
    norm_num [ UInt16.ext_iff ]; omega
  convert uint16_hilo_or_eq_zero_iff ( rem.toUInt16 ) using 1;
  norm_num [ hi16, lo16, h_rem_pos ]

/-- hi16 0 ||| lo16 0 = 0 -/
theorem hilo_or_zero : hi16 (0 : UInt16) ||| lo16 (0 : UInt16) = 0 := by native_decide

/-! ## §2 Memory address correspondence -/

/-- Reading memory at (progSize + rem - 1).toUInt16 gives aBytes[rem-1]. -/
theorem read_aBytes_at (m : Memory) (n rem : Nat) (aBytes : List UInt8)
    (haL : aBytes.length = n) (hrem_pos : 0 < rem) (hrem_le : rem ≤ n)
    (hfits : progSize + 2 * n < 0x8000)
    (haM : ∀ i (hi : i < n), m.read (progSize + i).toUInt16 = aBytes[i]'(haL ▸ hi)) :
    m.read (progSize + rem - 1).toUInt16 =
      aBytes[rem - 1]'(by rw [haL]; omega) := by
  grind

/-- Reading memory at (progSize + n + rem - 1).toUInt16 gives bBytes[rem-1]. -/
theorem read_bBytes_at (m : Memory) (n rem : Nat) (bBytes : List UInt8)
    (hbL : bBytes.length = n) (hrem_pos : 0 < rem) (hrem_le : rem ≤ n)
    (hfits : progSize + 2 * n < 0x8000)
    (hbM : ∀ i (hi : i < n), m.read (progSize + n + i).toUInt16 = bBytes[i]'(hbL ▸ hi)) :
    m.read (progSize + n + rem - 1).toUInt16 =
      bBytes[rem - 1]'(by rw [hbL]; omega) := by
  grind

/-! ## §3 bigCmp helpers -/

/-
If all bytes from rem to n are equal and aBytes[rem-1] ≠ bBytes[rem-1],
    then bigCmp is determined by comparing those bytes.
-/
theorem bigCmp_determined_by_diff (aBytes bBytes : List UInt8) (n rem : Nat)
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hrem_pos : 0 < rem) (hrem_le : rem ≤ n)
    (hsuf : ∀ i (hi₁ : rem ≤ i) (hi₂ : i < n),
      aBytes[i]'(haL ▸ hi₂) = bBytes[i]'(hbL ▸ hi₂))
    (hne : aBytes[rem - 1]'(by rw [haL]; omega) ≠ bBytes[rem - 1]'(by rw [hbL]; omega)) :
    bigCmp aBytes bBytes =
      compare (aBytes[rem - 1]'(by rw [haL]; omega)).toNat
              (bBytes[rem - 1]'(by rw [hbL]; omega)).toNat := by
  -- Apply bigCmp_take_eq to reduce to take rem.
  have h_take_rem : bigCmp aBytes bBytes = bigCmp (aBytes.take rem) (bBytes.take rem) := by
    apply bigCmp_take_eq; aesop;
    grind;
    linarith;
  rcases rem <;> simp_all +decide [ List.take_add_one ];
  · contradiction;
  · rw [ List.getElem?_eq_getElem, List.getElem?_eq_getElem ];
    convert bigCmp_last_diff _ _ _ _ _ _;
    · aesop;
    · assumption

/-- Suffix equality extends by one byte when the current bytes are equal. -/
theorem suffix_eq_extend (aBytes bBytes : List UInt8) (n rem : Nat)
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hrem_pos : 0 < rem) (hrem_le : rem ≤ n)
    (hsuf : ∀ i (hi₁ : rem ≤ i) (hi₂ : i < n),
      aBytes[i]'(haL ▸ hi₂) = bBytes[i]'(hbL ▸ hi₂))
    (heq_byte : aBytes[rem - 1]'(by rw [haL]; omega) = bBytes[rem - 1]'(by rw [hbL]; omega)) :
    ∀ i (hi₁ : rem - 1 ≤ i) (hi₂ : i < n),
      aBytes[i]'(haL ▸ hi₂) = bBytes[i]'(hbL ▸ hi₂) := by
  grind

/-- If all bytes are equal, bigCmp = .eq. -/
theorem bigCmp_all_eq (aBytes bBytes : List UInt8) (n : Nat)
    (haL : aBytes.length = n) (hbL : bBytes.length = n)
    (hsuf : ∀ i (hi₁ : 0 ≤ i) (hi₂ : i < n),
      aBytes[i]'(haL ▸ hi₂) = bBytes[i]'(hbL ▸ hi₂)) :
    bigCmp aBytes bBytes = .eq := by
  convert bigCmp_take_eq aBytes bBytes 0 _ _ _ using 1;
  all_goals norm_num [haL, hbL, hsuf];
  exact fun i hi₂ => hsuf i (Nat.zero_le i) hi₂

/-! ## §4 Register pair arithmetic after DEC -/

theorem hl_after_dec (rem : Nat) (hrem : 1 < rem) (hle : progSize + 2 * rem ≤ 0x8000) :
    (progSize + rem - 1 : Nat).toUInt16 - 1 = (progSize + (rem - 1) - 1 : Nat).toUInt16 := by
  rcases rem with ( _ | _ | rem ) <;> simp_all +arith +decide [Nat.add_mod, Nat.sub_sub]

theorem de_after_dec (n rem : Nat) (hrem : 1 < rem) (hle : progSize + 2 * n < 0x8000)
    (hrem_le : rem ≤ n) :
    (progSize + n + rem - 1 : Nat).toUInt16 - 1 = (progSize + n + (rem - 1) - 1 : Nat).toUInt16 := by
  rw [Nat.add_sub_assoc];
  · rcases k : progSize + n + (rem - 1) with (_ | k) <;> simp_all +decide [toNat];
  · linarith

theorem bc_after_dec (rem : Nat) (hrem : 0 < rem) (hle : rem ≤ 65535) :
    rem.toUInt16 - 1 = (rem - 1 : Nat).toUInt16 := by
  rcases rem with (_ | _ | rem) <;> simp_all +decide [Nat.toUInt16]

end Z80.CompareLoopHelpers