import Z80Emu.Types

/-!
# Z80 Instruction Set

A comprehensive algebraic data type modelling every documented Z80
instruction (plus the widely-used undocumented half-index-register
accesses IXH/IXL/IYH/IYL).

The instruction ADT represents *decoded* instructions: all register
selections, immediate operands, and displacements have been resolved.
The `Decode` module turns a raw byte stream into values of this type.
-/

namespace Z80

/-! ## Register and operand types -/

/-- 8-bit main registers. -/
inductive Reg8 where
  | A | B | C | D | E | H | L
  deriving Repr, BEq, DecidableEq, Inhabited

/-- 16-bit register pairs used in arithmetic / INC / DEC instructions. -/
inductive Reg16 where
  | BC | DE | HL | SP
  deriving Repr, BEq, DecidableEq, Inhabited

/-- 16-bit register pairs used in PUSH / POP (AF replaces SP). -/
inductive Reg16s where
  | BC | DE | HL | AF
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Index register selector. -/
inductive IdxReg where
  | IX | IY
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An 8-bit operand location: register, memory indirect, or
    half-index register (undocumented). -/
inductive Loc8 where
  /-- A main register. -/
  | reg  : Reg8 → Loc8
  /-- Memory at address HL: `(HL)`. -/
  | indHL : Loc8
  /-- Memory at index + signed displacement: `(IX+d)` or `(IY+d)`. -/
  | indIdx : IdxReg → Byte → Loc8
  /-- Undocumented high byte of index register (IXH or IYH). -/
  | idxH : IdxReg → Loc8
  /-- Undocumented low byte of index register (IXL or IYL). -/
  | idxL : IdxReg → Loc8
  deriving Repr, BEq, Inhabited

/-! ## Condition codes -/

/-- Condition codes for conditional jumps, calls, and returns.
    Encoded in bits 5–3 of the opcode. -/
inductive Cond where
  | NZ   -- Z flag clear
  | Z    -- Z flag set
  | NC   -- C flag clear
  | C    -- C flag set
  | PO   -- P/V flag clear (parity odd)
  | PE   -- P/V flag set (parity even)
  | P    -- S flag clear (positive)
  | M    -- S flag set (minus / negative)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## ALU operations -/

/-- The eight ALU operations that share the same encoding pattern. -/
inductive ALUOp where
  | ADD | ADC | SUB | SBC | AND | XOR | OR | CP
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Rotate / shift operations (CB prefix) -/

/-- Rotate and shift operations from the CB-prefixed instruction group. -/
inductive RotOp where
  | RLC   -- Rotate left circular
  | RRC   -- Rotate right circular
  | RL    -- Rotate left through carry
  | RR    -- Rotate right through carry
  | SLA   -- Shift left arithmetic
  | SRA   -- Shift right arithmetic (preserves sign bit)
  | SLL   -- Shift left logical (undocumented; bit 0 ← 1)
  | SRL   -- Shift right logical
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Block operation types -/

/-- Direction for block transfer / search / I-O instructions. -/
inductive BlockDir where
  | Inc   -- HL increments (LDI, CPI, INI, OUTI, …)
  | Dec   -- HL decrements (LDD, CPD, IND, OUTD, …)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The instruction type -/

/-- A fully-decoded Z80 instruction.

Instructions are grouped into categories following Zilog's own
classification.  For each constructor the comment gives the
standard mnemonic.

### Convention
* `nn` — 16-bit immediate (address or data)
* `n`  — 8-bit immediate
* `d`  — 8-bit signed displacement (stored as `Byte`, interpreted signed)
* `e`  — 8-bit signed relative-jump offset (stored as `Byte`)
-/
inductive Instr where

  -- ═══ CPU control ═══
  | NOP
  | HALT
  | DI
  | EI
  | IM   (mode : IntMode)

  -- ═══ 8-bit load group ═══
  /-- `LD dst, src` — register-to-register (or via (HL)/(IX+d)/(IY+d)). -/
  | LD8  (dst src : Loc8)
  /-- `LD dst, n` — load immediate byte. -/
  | LD8imm (dst : Loc8) (n : Byte)
  /-- `LD A, (BC)` or `LD A, (DE)`. -/
  | LDA_ind (rp : Reg16)     -- only BC or DE used
  /-- `LD (BC), A` or `LD (DE), A`. -/
  | LDind_A (rp : Reg16)     -- only BC or DE used
  /-- `LD A, (nn)`. -/
  | LDA_nn (nn : Word)
  /-- `LD (nn), A`. -/
  | LDnn_A (nn : Word)
  /-- `LD A, I`. -/
  | LDA_I
  /-- `LD A, R`. -/
  | LDA_R
  /-- `LD I, A`. -/
  | LDI_A
  /-- `LD R, A`. -/
  | LDR_A

  -- ═══ 16-bit load group ═══
  /-- `LD rp, nn` — load 16-bit immediate into register pair. -/
  | LD16imm  (rp : Reg16)  (nn : Word)
  /-- `LD IX, nn` or `LD IY, nn`. -/
  | LDIdx_nn (idx : IdxReg) (nn : Word)
  /-- `LD SP, HL`. -/
  | LDSP_HL
  /-- `LD SP, IX` or `LD SP, IY`. -/
  | LDSP_Idx (idx : IdxReg)
  /-- `LD (nn), HL`. -/
  | LDnn_HL (nn : Word)
  /-- `LD HL, (nn)`. -/
  | LDHL_nn (nn : Word)
  /-- `LD (nn), IX/IY`. -/
  | LDnn_Idx (idx : IdxReg) (nn : Word)
  /-- `LD IX/IY, (nn)`. -/
  | LDIdx_ind (idx : IdxReg) (nn : Word)
  /-- `LD (nn), rp` — ED-prefix 16-bit store. -/
  | LDnn_rp (rp : Reg16)  (nn : Word)
  /-- `LD rp, (nn)` — ED-prefix 16-bit load. -/
  | LDrp_nn (rp : Reg16)  (nn : Word)

  -- ═══ Stack (push / pop) ═══
  | PUSH   (rp : Reg16s)
  | POP    (rp : Reg16s)
  | PUSHi  (idx : IdxReg)
  | POPi   (idx : IdxReg)

  -- ═══ Exchange ═══
  /-- `EX AF, AF'` — swap AF with shadow AF. -/
  | EX_AF
  /-- `EXX` — swap BC/DE/HL with shadow set. -/
  | EXX
  /-- `EX DE, HL`. -/
  | EX_DE_HL
  /-- `EX (SP), HL`. -/
  | EX_SP_HL
  /-- `EX (SP), IX` or `EX (SP), IY`. -/
  | EX_SP_Idx (idx : IdxReg)

  -- ═══ 8-bit arithmetic / logic ═══
  /-- `ADD/ADC/SUB/SBC/AND/XOR/OR/CP A, src`. -/
  | ALU    (op : ALUOp) (src : Loc8)
  /-- `ADD/ADC/… A, n` (immediate operand). -/
  | ALUimm (op : ALUOp) (n : Byte)
  /-- `INC dst` (8-bit). -/
  | INC8   (dst : Loc8)
  /-- `DEC dst` (8-bit). -/
  | DEC8   (dst : Loc8)
  /-- `DAA` — decimal adjust accumulator. -/
  | DAA
  /-- `CPL` — complement accumulator. -/
  | CPL
  /-- `NEG` — negate accumulator (ED prefix). -/
  | NEG
  /-- `SCF` — set carry flag. -/
  | SCF
  /-- `CCF` — complement carry flag. -/
  | CCF

  -- ═══ 16-bit arithmetic ═══
  /-- `ADD HL, rp`. -/
  | ADD_HL  (rp : Reg16)
  /-- `ADD IX, rp` (with IX substituted for HL in rp). -/
  | ADD_Idx (idx : IdxReg) (rp : Reg16)
  /-- `ADC HL, rp` (ED prefix). -/
  | ADC_HL  (rp : Reg16)
  /-- `SBC HL, rp` (ED prefix). -/
  | SBC_HL  (rp : Reg16)
  /-- `INC rp` (16-bit). -/
  | INC16   (rp : Reg16)
  /-- `DEC rp` (16-bit). -/
  | DEC16   (rp : Reg16)
  /-- `INC IX/IY`. -/
  | INCIdx  (idx : IdxReg)
  /-- `DEC IX/IY`. -/
  | DECIdx  (idx : IdxReg)

  -- ═══ Rotate / shift — accumulator (root opcodes) ═══
  | RLCA | RRCA | RLA | RRA

  -- ═══ Rotate / shift / bit — CB prefix ═══
  /-- Rotate/shift operation on an 8-bit location. -/
  | ROT    (op : RotOp) (loc : Loc8)
  /-- `BIT b, loc` — test bit. -/
  | BIT    (b : Fin 8) (loc : Loc8)
  /-- `SET b, loc` — set bit. -/
  | SET    (b : Fin 8) (loc : Loc8)
  /-- `RES b, loc` — reset (clear) bit. -/
  | RES    (b : Fin 8) (loc : Loc8)

  -- ═══ BCD rotate-digit ═══
  /-- `RRD` — rotate right digit (ED prefix). -/
  | RRD
  /-- `RLD` — rotate left digit (ED prefix). -/
  | RLD

  -- ═══ Jump ═══
  /-- `JP nn` — unconditional absolute jump. -/
  | JP       (nn : Word)
  /-- `JP cc, nn` — conditional absolute jump. -/
  | JP_cc    (cc : Cond) (nn : Word)
  /-- `JR e` — unconditional relative jump. -/
  | JR       (e : Byte)
  /-- `JR cc, e` — conditional relative jump (NZ/Z/NC/C only). -/
  | JR_cc    (cc : Cond) (e : Byte)
  /-- `JP (HL)` — jump to address in HL. -/
  | JP_HL
  /-- `JP (IX)` or `JP (IY)`. -/
  | JP_Idx   (idx : IdxReg)
  /-- `DJNZ e` — decrement B and jump if not zero. -/
  | DJNZ     (e : Byte)

  -- ═══ Call and return ═══
  /-- `CALL nn`. -/
  | CALL     (nn : Word)
  /-- `CALL cc, nn`. -/
  | CALL_cc  (cc : Cond) (nn : Word)
  /-- `RET`. -/
  | RET
  /-- `RET cc`. -/
  | RET_cc   (cc : Cond)
  /-- `RETI` — return from interrupt. -/
  | RETI
  /-- `RETN` — return from NMI. -/
  | RETN
  /-- `RST n` — restart (n ∈ {0x00,0x08,…,0x38}). -/
  | RST      (vec : Byte)

  -- ═══ Input / output ═══
  /-- `IN A, (n)` — input from port (root). -/
  | IN_A_n   (n : Byte)
  /-- `OUT (n), A` — output to port (root). -/
  | OUT_n_A  (n : Byte)
  /-- `IN r, (C)` — input from port BC (ED prefix). -/
  | IN_r_C   (r : Reg8)
  /-- `OUT (C), r` — output to port BC (ED prefix). -/
  | OUT_C_r  (r : Reg8)

  -- ═══ Block transfer ═══
  /-- `LDI` / `LDD`. -/
  | LDblock  (dir : BlockDir)
  /-- `LDIR` / `LDDR`. -/
  | LDblockR (dir : BlockDir)

  -- ═══ Block search ═══
  /-- `CPI` / `CPD`. -/
  | CPblock  (dir : BlockDir)
  /-- `CPIR` / `CPDR`. -/
  | CPblockR (dir : BlockDir)

  -- ═══ Block I/O ═══
  /-- `INI` / `IND`. -/
  | INblock  (dir : BlockDir)
  /-- `INIR` / `INDR`. -/
  | INblockR (dir : BlockDir)
  /-- `OUTI` / `OUTD`. -/
  | OUTblock  (dir : BlockDir)
  /-- `OTIR` / `OTDR`. -/
  | OUTblockR (dir : BlockDir)

  deriving Repr, BEq, Inhabited

end Z80
