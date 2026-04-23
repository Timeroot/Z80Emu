import Z80Emu.Eval
import Z80Emu.Encode

/-!
# Arbitrary-Size Integer GCD — Z80 Demo

A Z80 program that computes the GCD of two arbitrary-size integers
using the subtraction-based Euclidean algorithm, with multi-byte
arithmetic. Numbers are encoded as **little-endian byte arrays** of
a fixed length `N`, stored consecutively in memory after the program
code.

## Memory layout

```
  0x0000 .. 0x0067  — program code  (104 bytes, fixed)
  0x0068 .. 0x0068+N-1  — number A  (N bytes, little-endian)
  0x0068+N .. 0x0068+2N-1  — number B  (N bytes, little-endian)
```

## Algorithm

```
loop:
    compare A and B  (MSB → LSB, multi-byte)
    if A = B → output A, halt
    if A > B → A ← A − B  (multi-byte subtraction with borrow)
    if A < B → B ← B − A
    goto loop
```

The compare scans from MSB to LSB; the first differing byte
determines the ordering.  The subtraction processes LSB to MSB,
propagating borrow via `PUSH AF` / `POP AF` around the 16-bit
loop counter decrement (since `DEC BC` does not affect flags on
the Z80, but the zero-test `OR` does).

## Capacity

With the stack pointer at `0x8000` (default), each number can be
up to **16 331 bytes** (≈ 130 000 bits).  Moving SP to `0xFFFE`
allows up to **32 714 bytes** (≈ 262 000 bits).  The 16-bit `BC`
counter supports `N` up to 65 535.

## Encoding

A natural number is stored as `N` little-endian bytes:

    value = b₀ + 256 · b₁ + 256² · b₂ + ⋯ + 256^(N−1) · b_{N−1}
-/

namespace Z80.BigNumGCD

open Z80

-- ═══════════════════════════════════════════════════════
-- §1  Bignum encoding / decoding
-- ═══════════════════════════════════════════════════════

/-- Decode a little-endian byte list to a natural number.
    `decodeBigNum [b₀, b₁, …] = b₀ + 256 · b₁ + 256² · b₂ + ⋯` -/
def decodeBigNum : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeBigNum bs

/-- Encode a natural number as `n` little-endian bytes.
    The value is taken mod `256^n`. -/
def encodeBigNum : Nat → Nat → List UInt8
  | _, 0 => []
  | val, n + 1 => (val % 256).toUInt8 :: encodeBigNum (val / 256) n

-- ═══════════════════════════════════════════════════════
-- §2  Bignum operations (pure Lean, for testing/proofs)
-- ═══════════════════════════════════════════════════════

/-- Check whether all bytes are zero. -/
def bigIsZero : List UInt8 → Bool
  | [] => true
  | b :: bs => b == 0 && bigIsZero bs

/-- Compare two same-length little-endian bignums.
    Higher bytes (later in the list = more significant)
    are compared first. -/
def bigCmp : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | a :: as, b :: bs =>
    match bigCmp as bs with
    | .eq => compare a.toNat b.toNat
    | ord => ord
  | _, _ => .eq

/-- Multi-byte subtraction with borrow propagation (little-endian).
    Requires `a ≥ b` (as unsigned integers) and same length. -/
def bigSub (a b : List UInt8) : List UInt8 :=
  go a b 0
where
  go : List UInt8 → List UInt8 → Nat → List UInt8
    | [], [], _ => []
    | a :: as, b :: bs, borrow =>
      let diff := a.toNat + 256 - b.toNat - borrow
      (diff % 256).toUInt8 :: go as bs (if diff ≥ 256 then 0 else 1)
    | _, _, _ => []

/-- Subtraction-based Euclidean GCD on byte lists.
    Both inputs must have the same length and be nonzero.
    Returns a byte list of the same length.
    Marked `partial` since termination depends on the bigSub
    correctness lemma proved in `BigNumGCDCorrectness`. -/
partial def bigGcdLoop (a b : List UInt8) : List UInt8 :=
  if bigIsZero a then b
  else if bigIsZero b then a
  else match bigCmp a b with
    | .eq => a
    | .gt => bigGcdLoop (bigSub a b) b
    | .lt => bigGcdLoop a (bigSub b a)

-- ═══════════════════════════════════════════════════════
-- §3  Z80 multi-byte GCD program
-- ═══════════════════════════════════════════════════════

/-- Size of the multi-byte GCD program (bytes). -/
def progSize : Nat := 104

/-- The Z80 multi-byte GCD program for `N`-byte numbers.

    **Preconditions**: `N ≥ 1`, both inputs nonzero,
    `104 + 2·N ≤ 32 766` (or `≤ 65 534` if SP is moved).

    The program uses:
    - `HL`, `DE` as byte pointers during compare / subtract
    - `BC` as a 16-bit loop counter (supporting `N` up to 65 535)
    - `A` as accumulator
    - `PUSH AF` / `POP AF` to preserve the carry flag through
      the 16-bit counter zero-test in the subtraction loop.

    ```asm
    ; === COMPARE (MSB → LSB) ===
    main_loop:
        LD HL, msbA         ; point to MSB of A
        LD DE, msbB         ; point to MSB of B
        LD BC, N            ; byte counter
    cmp_loop:
        LD A, (HL)          ; byte from A
        EX DE, HL
        CP (HL)             ; compare with byte from B
        EX DE, HL
        JR NZ, cmp_done     ; first difference found
        DEC HL
        DEC DE
        DEC BC
        LD A, B
        OR C
        JR NZ, cmp_loop
        JP output           ; all equal → done

    cmp_done:
        JP C, b_bigger      ; A < B (carry set)

    ; === A = A − B (LSB → MSB) ===
        LD HL, addrA
        LD DE, addrB
        LD BC, N
        OR A                ; clear carry
    sub_a_loop:
        LD A, (HL)
        EX DE, HL
        SBC A, (HL)
        EX DE, HL
        LD (HL), A
        INC HL
        INC DE
        DEC BC              ; does NOT affect carry
        PUSH AF             ; save carry
        LD A, B
        OR C
        JR Z, sub_a_done
        POP AF              ; restore carry
        JR sub_a_loop
    sub_a_done:
        POP AF              ; clean stack
        JP main_loop

    ; === B = B − A (LSB → MSB) ===
    b_bigger:
        LD HL, addrB
        LD DE, addrA
        LD BC, N
        OR A
    sub_b_loop:
        LD A, (HL)
        EX DE, HL
        SBC A, (HL)
        EX DE, HL
        LD (HL), A
        INC HL
        INC DE
        DEC BC
        PUSH AF
        LD A, B
        OR C
        JR Z, sub_b_done
        POP AF
        JR sub_b_loop
    sub_b_done:
        POP AF
        JP main_loop

    ; === OUTPUT ===
    output:
        LD HL, addrA
        LD BC, N
    out_loop:
        LD A, (HL)
        OUT (0), A
        INC HL
        DEC BC
        LD A, B
        OR C
        JR NZ, out_loop
        HALT
    ```
-/
def bigGcdProgram (n : Nat) : List Instr :=
  let addrA  : Nat := progSize
  let addrB  : Nat := progSize + n
  let msbA   : Nat := addrA + n - 1
  let msbB   : Nat := addrB + n - 1
  let addrAw : Word := addrA.toUInt16
  let addrBw : Word := addrB.toUInt16
  let msbAw  : Word := msbA.toUInt16
  let msbBw  : Word := msbB.toUInt16
  let nw     : Word := n.toUInt16
  [
    -- ═══ COMPARE (MSB → LSB) ═══
    -- main_loop:  [0]
    .LD16imm .HL msbAw,               -- [0-2]
    .LD16imm .DE msbBw,               -- [3-5]
    .LD16imm .BC nw,                   -- [6-8]
    -- cmp_loop:   [9]
    .LD8 (.reg .A) .indHL,             -- [9]
    .EX_DE_HL,                         -- [10]
    .ALU .CP .indHL,                   -- [11]
    .EX_DE_HL,                         -- [12]
    .JR_cc .NZ 0x0A,                   -- [13-14]  → 25  (cmp_done)
    .DEC16 .HL,                        -- [15]
    .DEC16 .DE,                        -- [16]
    .DEC16 .BC,                        -- [17]
    .LD8 (.reg .A) (.reg .B),          -- [18]
    .ALU .OR (.reg .C),                -- [19]
    .JR_cc .NZ 0xF3,                   -- [20-21]  → 9   (cmp_loop)
    .JP 88,                            -- [22-24]  → 88  (output)

    -- ═══ BRANCH ═══
    -- cmp_done:   [25]
    .JP_cc .C 58,                      -- [25-27]  → 58  (b_bigger)

    -- ═══ A = A − B ═══
    .LD16imm .HL addrAw,               -- [28-30]
    .LD16imm .DE addrBw,               -- [31-33]
    .LD16imm .BC nw,                   -- [34-36]
    .ALU .OR (.reg .A),                -- [37]     OR A (clear carry)
    -- sub_a_loop: [38]
    .LD8 (.reg .A) .indHL,             -- [38]
    .EX_DE_HL,                         -- [39]
    .ALU .SBC .indHL,                  -- [40]
    .EX_DE_HL,                         -- [41]
    .LD8 .indHL (.reg .A),             -- [42]
    .INC16 .HL,                        -- [43]
    .INC16 .DE,                        -- [44]
    .DEC16 .BC,                        -- [45]
    .PUSH .AF,                         -- [46]
    .LD8 (.reg .A) (.reg .B),          -- [47]
    .ALU .OR (.reg .C),                -- [48]
    .JR_cc .Z 0x03,                    -- [49-50]  → 54  (sub_a_done)
    .POP .AF,                          -- [51]
    .JR 0xF0,                          -- [52-53]  → 38  (sub_a_loop)
    -- sub_a_done: [54]
    .POP .AF,                          -- [54]
    .JP 0,                             -- [55-57]  → 0   (main_loop)

    -- ═══ B = B − A ═══
    -- b_bigger:   [58]
    .LD16imm .HL addrBw,               -- [58-60]
    .LD16imm .DE addrAw,               -- [61-63]
    .LD16imm .BC nw,                   -- [64-66]
    .ALU .OR (.reg .A),                -- [67]     OR A (clear carry)
    -- sub_b_loop: [68]
    .LD8 (.reg .A) .indHL,             -- [68]
    .EX_DE_HL,                         -- [69]
    .ALU .SBC .indHL,                  -- [70]
    .EX_DE_HL,                         -- [71]
    .LD8 .indHL (.reg .A),             -- [72]
    .INC16 .HL,                        -- [73]
    .INC16 .DE,                        -- [74]
    .DEC16 .BC,                        -- [75]
    .PUSH .AF,                         -- [76]
    .LD8 (.reg .A) (.reg .B),          -- [77]
    .ALU .OR (.reg .C),                -- [78]
    .JR_cc .Z 0x03,                    -- [79-80]  → 84  (sub_b_done)
    .POP .AF,                          -- [81]
    .JR 0xF0,                          -- [82-83]  → 68  (sub_b_loop)
    -- sub_b_done: [84]
    .POP .AF,                          -- [84]
    .JP 0,                             -- [85-87]  → 0   (main_loop)

    -- ═══ OUTPUT ═══
    -- output:     [88]
    .LD16imm .HL addrAw,               -- [88-90]
    .LD16imm .BC nw,                   -- [91-93]
    -- out_loop:   [94]
    .LD8 (.reg .A) .indHL,             -- [94]
    .OUT_n_A 0,                        -- [95-96]
    .INC16 .HL,                        -- [97]
    .DEC16 .BC,                        -- [98]
    .LD8 (.reg .A) (.reg .B),          -- [99]
    .ALU .OR (.reg .C),                -- [100]
    .JR_cc .NZ 0xF7,                   -- [101-102] → 94  (out_loop)
    .HALT                              -- [103]
  ]

/-- Encoded program size is exactly `progSize` bytes (verified for specific sizes). -/
theorem bigGcdProgram_size_1 : (encodeProgram (bigGcdProgram 1)).length = progSize := by native_decide
theorem bigGcdProgram_size_2 : (encodeProgram (bigGcdProgram 2)).length = progSize := by native_decide
theorem bigGcdProgram_size_4 : (encodeProgram (bigGcdProgram 4)).length = progSize := by native_decide

/-- Assemble the full bytecode: program code ++ data A ++ data B.
    Both `a` and `b` must have the same length. -/
def bigGcdBytecode (a b : List UInt8) : List UInt8 :=
  encodeProgram (bigGcdProgram a.length) ++ a ++ b

-- ═══════════════════════════════════════════════════════
-- §4  Smoke tests
-- ═══════════════════════════════════════════════════════

section Tests

-- Encoding / decoding roundtrip
#eval decodeBigNum [0xE8, 0x03]       -- 1000
#eval decodeBigNum [0xEE, 0x02]       -- 750
#eval encodeBigNum 1000 2              -- [0xE8, 0x03]
#eval encodeBigNum 250 2               -- [0xFA, 0x00]

-- Pure-algorithm tests
#eval bigGcdLoop [12] [8]                                     -- [4]
#eval bigGcdLoop (encodeBigNum 1000 2) (encodeBigNum 750 2)   -- [250, 0]
#eval bigGcdLoop (encodeBigNum 60000 2) (encodeBigNum 36000 2)
  -- [0xE0, 0x2E] = 12000

-- ─── 1-byte (8-bit) ──────────────────────────────────
#eval eval (bigGcdBytecode [12] [8])                          -- [4]
#eval eval (bigGcdBytecode [15] [10])                         -- [5]
#eval eval (bigGcdBytecode [100] [75])                        -- [25]
#eval eval (bigGcdBytecode [17] [13])                         -- [1]
#eval eval (bigGcdBytecode [255] [255])                       -- [255]

-- ─── 2-byte (16-bit) ─────────────────────────────────
-- gcd(1000, 750) = 250
#eval eval (bigGcdBytecode [0xE8, 0x03] [0xEE, 0x02]) 50000
  -- expect [0xFA, 0x00]

-- gcd(60000, 36000) = 12000
#eval eval (bigGcdBytecode [0x60, 0xEA] [0xA0, 0x8C]) 200000
  -- expect [0xE0, 0x2E]

-- gcd(65535, 65535) = 65535  (trivial — one comparison)
#eval eval (bigGcdBytecode [0xFF, 0xFF] [0xFF, 0xFF]) 10000
  -- expect [0xFF, 0xFF]

-- ─── 4-byte (32-bit) ─────────────────────────────────
-- gcd(100_000_000, 75_000_000) = 25_000_000
-- Converges in 3 subtraction steps.
#eval eval (bigGcdBytecode
  (encodeBigNum 100000000 4) (encodeBigNum 75000000 4)) 200000
  -- expect encodeBigNum 25000000 4 = [0x40, 0x78, 0x7D, 0x01]

-- gcd(2^31, 2^30) = 2^30  (one subtraction step)
#eval eval (bigGcdBytecode
  (encodeBigNum (2^31) 4) (encodeBigNum (2^30) 4)) 10000
  -- expect encodeBigNum (2^30) 4 = [0x00, 0x00, 0x00, 0x40]

-- ─── 8-byte (64-bit) ─────────────────────────────────
-- gcd(10^18, 6 * 10^17) = 2 * 10^17
-- 10^18 − 6*10^17 = 4*10^17, then 6*10^17 − 4*10^17 = 2*10^17,
-- then 4*10^17 − 2*10^17 = 2*10^17. Three steps.
#eval eval (bigGcdBytecode
  (encodeBigNum (10^18) 8) (encodeBigNum (6 * 10^17) 8)) 200000
  -- expect encodeBigNum (2 * 10^17) 8

-- Verify the result
#eval decodeBigNum (eval (bigGcdBytecode
  (encodeBigNum (10^18) 8) (encodeBigNum (6 * 10^17) 8)) 200000)
  -- expect 200000000000000000

-- ─── 16-byte (128-bit) ───────────────────────────────
-- gcd(2^127, 2^126) = 2^126  (one step)
#eval decodeBigNum (eval (bigGcdBytecode
  (encodeBigNum (2^127) 16) (encodeBigNum (2^126) 16)) 50000)
  -- expect 2^126



end Tests

end Z80.BigNumGCD
