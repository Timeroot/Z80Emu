import Z80Emu.Eval
import Z80Emu.Encode
import Z80Emu.Asm

/-!
# Z80 Demo Programs

Three verified Z80 assembly programs:
1. **Fibonacci** — computes fib(n) for small n (8-bit result)
2. **Factorial** — computes n! for small n (8-bit result)
3. **Euclidean GCD** — computes gcd(a, b)

Each program is:
- Written as Z80 assembly (list of `Instr`)
- Encoded to bytecode
- Run via `CPU.eval`
- Verified to produce correct output via `native_decide`
- Verified to have valid (cleanly decodable) bytecode
-/

namespace Z80.Demos

open Z80

/-! ## 1. Fibonacci

Computes fib(n) where n is loaded into register B.
Uses registers: C = fib(i-1), A = fib(i), D = temp.
Outputs the result via OUT (0), A.

```
    LD B, n-1     ; loop counter
    LD C, 0       ; fib(0) = 0
    LD A, 1       ; fib(1) = 1
loop:
    LD D, A       ; save current
    ADD A, C      ; A = fib(i) + fib(i-1)
    LD C, D       ; C = old current
    DJNZ loop
    OUT (0), A
    HALT
```
-/

/-- Fibonacci program: computes fib(n) and outputs it via port 0. -/
def fibProgram (n : Byte) : List Instr :=
  if n == 0 then
    [ .LD8imm (.reg .A) 0,
      .OUT_n_A 0,
      .HALT ]
  else if n == 1 then
    [ .LD8imm (.reg .A) 1,
      .OUT_n_A 0,
      .HALT ]
  else
    -- Byte offsets:
    -- 0: LD B, n-1     (2 bytes)
    -- 2: LD C, 0       (2 bytes)
    -- 4: LD A, 1       (2 bytes)
    -- 6: LD D, A       (1 byte)  <- loop target
    -- 7: ADD A, C      (1 byte)
    -- 8: LD C, D       (1 byte)
    -- 9: DJNZ loop     (2 bytes)  rel = 6 - (9+2) = -5 = 0xFB
    -- 11: OUT (0), A   (2 bytes)
    -- 13: HALT         (1 byte)
    [ .LD8imm (.reg .B) (n - 1),
      .LD8imm (.reg .C) 0,
      .LD8imm (.reg .A) 1,
      .LD8 (.reg .D) (.reg .A),
      .ALU .ADD (.reg .C),
      .LD8 (.reg .C) (.reg .D),
      .DJNZ 0xFB,
      .OUT_n_A 0,
      .HALT ]

def fibBytecode (n : Byte) : List Byte := encodeProgram (fibProgram n)

-- Verify outputs
#eval eval (fibBytecode 0)    -- [0]
#eval eval (fibBytecode 1)    -- [1]
#eval eval (fibBytecode 5)    -- [5]
#eval eval (fibBytecode 10)   -- [55]
#eval eval (fibBytecode 13)   -- [233]

theorem fib_0_correct : eval (fibBytecode 0) = [0] := by native_decide
theorem fib_1_correct : eval (fibBytecode 1) = [1] := by native_decide
theorem fib_5_correct : eval (fibBytecode 5) = [5] := by native_decide
theorem fib_10_correct : eval (fibBytecode 10) = [55] := by native_decide
theorem fib_13_correct : eval (fibBytecode 13) = [233] := by native_decide

theorem fib_10_valid : bytecodeDecodesCleanly (fibBytecode 10) = true := by native_decide

/-! ## 2. Factorial

Computes n! (8-bit, so valid for n ≤ 5 since 6! = 720 > 255).
Multiplies by repeated addition.

```
    LD A, 1       ; result = 1
    LD B, n       ; counter
loop:
    LD E, A       ; E = current result
    LD A, 0       ; A = 0 (accumulator for multiplication)
    LD C, B       ; C = current multiplier
mulloop:
    ADD A, E      ; A += result
    DEC C         ; C--
    JR NZ, mulloop
    DJNZ loop     ; B--, if not zero, multiply by next
    OUT (0), A
    HALT
```
-/

def factProgram (n : Byte) : List Instr :=
  if n == 0 then
    [ .LD8imm (.reg .A) 1,
      .OUT_n_A 0,
      .HALT ]
  else
    -- Byte offsets:
    -- 0: LD A, 1        (2 bytes)
    -- 2: LD B, n        (2 bytes)
    -- 4: LD E, A        (1 byte)  <- loop
    -- 5: LD A, 0        (2 bytes)
    -- 7: LD C, B        (1 byte)
    -- 8: ADD A, E       (1 byte)  <- mulloop
    -- 9: DEC C          (1 byte)
    -- 10: JR NZ, mulloop (2 bytes) rel = 8 - 12 = -4 = 0xFC
    -- 12: DJNZ loop     (2 bytes)  rel = 4 - 14 = -10 = 0xF6
    -- 14: OUT (0), A    (2 bytes)
    -- 16: HALT          (1 byte)
    [ .LD8imm (.reg .A) 1,
      .LD8imm (.reg .B) n,
      .LD8 (.reg .E) (.reg .A),
      .LD8imm (.reg .A) 0,
      .LD8 (.reg .C) (.reg .B),
      .ALU .ADD (.reg .E),
      .DEC8 (.reg .C),
      .JR_cc .NZ 0xFC,
      .DJNZ 0xF6,
      .OUT_n_A 0,
      .HALT ]

def factBytecode (n : Byte) : List Byte := encodeProgram (factProgram n)

#eval eval (factBytecode 0)    -- [1]
#eval eval (factBytecode 1)    -- [1]
#eval eval (factBytecode 3)    -- [6]
#eval eval (factBytecode 5)    -- [120]

theorem fact_0_correct : eval (factBytecode 0) = [1] := by native_decide
theorem fact_1_correct : eval (factBytecode 1) = [1] := by native_decide
theorem fact_3_correct : eval (factBytecode 3) = [6] := by native_decide
theorem fact_5_correct : eval (factBytecode 5) = [120] := by native_decide

theorem fact_5_valid : bytecodeDecodesCleanly (factBytecode 5) = true := by native_decide

/-! ## 3. Euclidean Algorithm (GCD)

Computes gcd(a, b) using the subtraction-based Euclidean algorithm.

```
    LD B, a
    LD C, b
loop:
    LD A, B
    CP C          ; compare A with C
    JR Z, done    ; if equal, done
    JR C, b_bigger ; if A < C (carry set)
    SUB C         ; A = A - C
    LD B, A
    JR loop
b_bigger:
    LD A, C
    SUB B         ; A = C - B
    LD C, A
    JR loop
done:
    LD A, B       ; result
    OUT (0), A
    HALT
```
-/

def gcdProgram (a b : Byte) : List Instr :=
  -- Byte offsets:
  -- 0: LD B, a        (2)
  -- 2: LD C, b        (2)
  -- 4: LD A, B        (1)  <- loop
  -- 5: CP C           (1)
  -- 6: JR Z, done     (2)  rel = 19 - 8 = 11 = 0x0B
  -- 8: JR C, b_bigger (2)  rel = 14 - 10 = 4  = 0x04
  -- 10: SUB C         (1)
  -- 11: LD B, A       (1)
  -- 12: JR loop       (2)  rel = 4 - 14  = -10 = 0xF6
  -- 14: LD A, C       (1)  <- b_bigger
  -- 15: SUB B         (1)
  -- 16: LD C, A       (1)
  -- 17: JR loop       (2)  rel = 4 - 19  = -15 = 0xF1
  -- 19: LD A, B       (1)  <- done
  -- 20: OUT (0), A    (2)
  -- 22: HALT          (1)
  [ .LD8imm (.reg .B) a,
    .LD8imm (.reg .C) b,
    .LD8 (.reg .A) (.reg .B),
    .ALU .CP (.reg .C),
    .JR_cc .Z 0x0B,
    .JR_cc .C 0x04,
    .ALU .SUB (.reg .C),
    .LD8 (.reg .B) (.reg .A),
    .JR 0xF6,
    .LD8 (.reg .A) (.reg .C),
    .ALU .SUB (.reg .B),
    .LD8 (.reg .C) (.reg .A),
    .JR 0xF1,
    .LD8 (.reg .A) (.reg .B),
    .OUT_n_A 0,
    .HALT ]

def gcdBytecode (a b : Byte) : List Byte := encodeProgram (gcdProgram a b)

#eval eval (gcdBytecode 12 8)     -- [4]
#eval eval (gcdBytecode 15 10)    -- [5]
#eval eval (gcdBytecode 7 7)      -- [7]
#eval eval (gcdBytecode 100 75)   -- [25]
#eval eval (gcdBytecode 17 13)    -- [1]

theorem gcd_12_8_correct : eval (gcdBytecode 12 8) = [4] := by native_decide
theorem gcd_15_10_correct : eval (gcdBytecode 15 10) = [5] := by native_decide
theorem gcd_7_7_correct : eval (gcdBytecode 7 7) = [7] := by native_decide
theorem gcd_100_75_correct : eval (gcdBytecode 100 75) = [25] := by native_decide
theorem gcd_17_13_correct : eval (gcdBytecode 17 13) = [1] := by native_decide

theorem gcd_12_8_valid : bytecodeDecodesCleanly (gcdBytecode 12 8) = true := by native_decide

/-! ## 4. Assembler demos

The same programs written as assembly source strings and assembled. -/

/-- Fibonacci program as assembly source (computes fib(9) = 34). -/
def fibAsmSource : String :=
"    LD B, 8
    LD C, 0
    LD A, 1
loop:
    LD D, A
    ADD A, C
    LD C, D
    DJNZ loop
    OUT (0), A
    HALT"

/-- GCD program as assembly source (computes gcd(48, 36) = 12). -/
def gcdAsmSource : String :=
"    LD B, 48
    LD C, 36
loop:
    LD A, B
    CP C
    JR Z, done
    JR C, b_bigger
    SUB C
    LD B, A
    JR loop
b_bigger:
    LD A, C
    SUB B
    LD C, A
    JR loop
done:
    LD A, B
    OUT (0), A
    HALT"

-- Assemble and run
#eval assemble fibAsmSource |>.map (·.bytecode)
#eval match assemble fibAsmSource with
  | some result => eval result.bytecode
  | none => []

#eval assemble gcdAsmSource |>.map (·.bytecode)
#eval match assemble gcdAsmSource with
  | some result => eval result.bytecode
  | none => []

/-- The Fibonacci assembler succeeds. -/
theorem fib_asm_succeeds : (assemble fibAsmSource).isSome = true := by native_decide

/-- Concrete bytecode produced by the Fibonacci assembler. -/
def fibAsmBytes : List Byte := [6, 8, 14, 0, 62, 1, 87, 129, 74, 16, 251, 211, 0, 118]

/-- The assembler produces the expected bytecode. -/
theorem fib_asm_bytecode :
    (assemble fibAsmSource).map (·.bytecode) = some fibAsmBytes := by native_decide

/-- The assembled Fibonacci program (fib(9) = 34) produces correct output. -/
theorem fib_asm_correct : eval fibAsmBytes = [34] := by native_decide

/-- The assembled Fibonacci bytecode decodes cleanly. -/
theorem fib_asm_valid : bytecodeDecodesCleanly fibAsmBytes = true := by native_decide

/-- The GCD assembler succeeds. -/
theorem gcd_asm_succeeds : (assemble gcdAsmSource).isSome = true := by native_decide

/-- Concrete bytecode produced by the GCD assembler. -/
def gcdAsmBytes : List Byte :=
  [6, 48, 14, 36, 120, 185, 40, 11, 56, 4, 145, 71, 24, 246, 121, 144, 79, 24, 241, 120, 211, 0, 118]

/-- The assembled GCD program (gcd(48,36) = 12) produces correct output. -/
theorem gcd_asm_correct : eval gcdAsmBytes = [12] := by native_decide

/-- The assembled GCD bytecode decodes cleanly. -/
theorem gcd_asm_valid : bytecodeDecodesCleanly gcdAsmBytes = true := by native_decide

end Z80.Demos
