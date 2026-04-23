import Mathlib
import Z80Emu.Types
import Z80Emu.State

/-!
# Memory Model Correctness

Foundational lemmas about the flat 64 KiB memory model:
read-after-write, write-size preservation, and zero-memory reads.
These form the correctness API for reasoning about Z80 memory operations.
-/

namespace Z80

/-! ## Memory size invariant -/

/-- The zero-initialized memory has exactly 65536 bytes. -/
theorem Memory.zeros_size : Memory.zeros.data.data.size = 65536 := by native_decide

/-! ## Read-after-write (same address) -/

/-
Writing a byte and reading it back at the same address yields the written value.
-/
theorem Memory.read_write_same (m : Memory) (addr : Word) (val : Byte)
    (hsz : m.data.data.size = 65536) :
    (m.write addr val).read addr = val := by
  -- Since `addr.toNat < 65536`, the set operation is effective, and thus the get operation returns `val`.
  have h_set_get : (ByteArray.set! m.data addr.toNat val).data[addr.toNat]? = some val := by
    have h_valid_index : addr.toNat < m.data.data.size := by
      exact hsz.symm ▸ Nat.lt_of_lt_of_le ( UInt16.toNat_lt _ ) ( by decide );
    unfold ByteArray.set!; aesop;
  simp +decide [ Memory.read, Memory.write ];
  simp +decide [ ByteArray.get! ];
  grind

/-! ## Read-after-write (different address) -/

/-
Writing at one address does not affect reads at a different address.
-/
theorem Memory.read_write_diff (m : Memory) (a1 a2 : Word) (val : Byte)
    (hsz : m.data.data.size = 65536)
    (hne : a1 ≠ a2) :
    (m.write a2 val).read a1 = m.read a1 := by
  unfold Memory.read; simp +decide [ Memory.write ] ;
  simp +decide [ ByteArray.get!, ByteArray.set! ];
  rw [ Array.setIfInBounds ];
  split_ifs <;> simp_all +decide [ Array.set ];
  rw [ List.getElem?_set ];
  simp_all +decide [ UInt16.toNat_inj ];
  grind

/-! ## Write preserves memory size -/

/-
Writing a byte preserves the memory array size.
-/
theorem Memory.write_size (m : Memory) (addr : Word) (val : Byte)
    (hsz : m.data.data.size = 65536) :
    (m.write addr val).data.data.size = 65536 := by
  rw [ ← hsz, Memory.write ];
  simp +decide [ ByteArray.set! ]

/-! ## Reading from zero memory -/

/-
Reading any address in freshly zeroed memory returns 0.
-/
theorem Memory.read_zeros (addr : Word) :
    Memory.zeros.read addr = 0 := by
  have h_zero : ∀ (addr : Nat), addr < 65536 → (ByteArray.get! (ByteArray.mk (Array.replicate 65536 0)) addr) = 0 := by
    intro addr haddr;
    simp +decide [ haddr, ByteArray.get! ];
  apply h_zero;
  exact addr.toNat_lt

/-! ## Memory size through loadBytes -/

theorem Memory.loadBytes_size (m : Memory) (base : Word) (bytes : List Byte)
    (hmsz : m.data.data.size = 65536) :
    (m.loadBytes base bytes).data.data.size = 65536 := by
  unfold loadBytes
  suffices h : ∀ (acc : Memory × Word), acc.1.data.data.size = 65536 →
      (bytes.foldl (fun (x : Memory × Word) b => (x.1.write x.2 b, x.2 + 1)) acc).1.data.data.size = 65536 from
    h (m, base) hmsz
  intro acc hacc
  induction bytes generalizing acc with
  | nil => exact hacc
  | cons hd tl ih => exact ih _ (Memory.write_size _ _ _ hacc)

end Z80
