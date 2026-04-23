import Z80Emu.Types
import Z80Emu.State
import Z80Emu.Instr

/-!
# Z80 Instruction Encoder

Encodes `Instr` values into their byte representation.
This is the inverse of the decoder: `decode (encode instr) = instr`.
-/

namespace Z80

/-- Encode a `Reg8` to its 3-bit field value. -/
def Reg8.toCode : Reg8 → Nat
  | .B => 0 | .C => 1 | .D => 2 | .E => 3
  | .H => 4 | .L => 5 | .A => 7

/-- Encode a `Reg16` to its 2-bit field value. -/
def Reg16.toCode : Reg16 → Nat
  | .BC => 0 | .DE => 1 | .HL => 2 | .SP => 3

/-- Encode a `Reg16s` to its 2-bit field value. -/
def Reg16s.toCode : Reg16s → Nat
  | .BC => 0 | .DE => 1 | .HL => 2 | .AF => 3

/-- Encode a `Cond` to its 3-bit field value. -/
def Cond.toCode : Cond → Nat
  | .NZ => 0 | .Z => 1 | .NC => 2 | .C => 3
  | .PO => 4 | .PE => 5 | .P => 6 | .M => 7

/-- Encode an `ALUOp` to its 3-bit field value. -/
def ALUOp.toCode : ALUOp → Nat
  | .ADD => 0 | .ADC => 1 | .SUB => 2 | .SBC => 3
  | .AND => 4 | .XOR => 5 | .OR => 6 | .CP => 7

/-- Encode a `RotOp` to its 3-bit field value. -/
def RotOp.toCode : RotOp → Nat
  | .RLC => 0 | .RRC => 1 | .RL => 2 | .RR => 3
  | .SLA => 4 | .SRA => 5 | .SLL => 6 | .SRL => 7

/-- Build an opcode byte from x (2 bits), y (3 bits), z (3 bits). -/
def mkOpcode (x y z : Nat) : Byte :=
  ((x <<< 6) ||| (y <<< 3) ||| z).toUInt8

/-- The index register prefix byte. -/
def idxPrefix (idx : IdxReg) : Byte :=
  match idx with | .IX => 0xDD | .IY => 0xFD

/-- Encode a single Z80 instruction into bytes. -/
def encode : Instr → List Byte
  -- CPU control
  | .NOP  => [0x00]
  | .HALT => [0x76]
  | .DI   => [0xF3]
  | .EI   => [0xFB]
  | .IM m => match m with
    | .im0 => [0xED, 0x46]
    | .im1 => [0xED, 0x56]
    | .im2 => [0xED, 0x5E]

  -- 8-bit loads: LD reg, reg / LD reg, (HL)
  | .LD8 dst src =>
    match dst, src with
    | .reg rd, .reg rs =>
      [mkOpcode 1 rd.toCode rs.toCode]
    | .reg rd, .indHL =>
      [mkOpcode 1 rd.toCode 6]
    | .indHL, .reg rs =>
      [mkOpcode 1 6 rs.toCode]
    | .indIdx idx d, .reg rs =>
      [idxPrefix idx, mkOpcode 1 6 rs.toCode, d]
    | .reg rd, .indIdx idx d =>
      [idxPrefix idx, mkOpcode 1 rd.toCode 6, d]
    | _, _ => [0x00] -- fallback for undocumented combos

  -- LD reg, n (immediate)
  | .LD8imm dst n =>
    match dst with
    | .reg r  => [mkOpcode 0 r.toCode 6, n]
    | .indHL  => [0x36, n]
    | .indIdx idx d => [idxPrefix idx, 0x36, d, n]
    | _ => [0x00]

  | .LDA_ind rp => match rp with
    | .BC => [0x0A] | .DE => [0x1A] | _ => [0x00]
  | .LDind_A rp => match rp with
    | .BC => [0x02] | .DE => [0x12] | _ => [0x00]
  | .LDA_nn nn => [0x3A, lo16 nn, hi16 nn]
  | .LDnn_A nn => [0x32, lo16 nn, hi16 nn]
  | .LDA_I => [0xED, 0x57]
  | .LDA_R => [0xED, 0x5F]
  | .LDI_A => [0xED, 0x47]
  | .LDR_A => [0xED, 0x4F]

  -- 16-bit loads
  | .LD16imm rp nn => [mkOpcode 0 (rp.toCode * 2) 1, lo16 nn, hi16 nn]
  | .LDIdx_nn idx nn => [idxPrefix idx, 0x21, lo16 nn, hi16 nn]
  | .LDSP_HL => [0xF9]
  | .LDSP_Idx idx => [idxPrefix idx, 0xF9]
  | .LDnn_HL nn => [0x22, lo16 nn, hi16 nn]
  | .LDHL_nn nn => [0x2A, lo16 nn, hi16 nn]
  | .LDnn_Idx idx nn => [idxPrefix idx, 0x22, lo16 nn, hi16 nn]
  | .LDIdx_ind idx nn => [idxPrefix idx, 0x2A, lo16 nn, hi16 nn]
  | .LDnn_rp rp nn => [0xED, mkOpcode 1 (rp.toCode * 2) 3, lo16 nn, hi16 nn]
  | .LDrp_nn rp nn => [0xED, mkOpcode 1 (rp.toCode * 2 + 1) 3, lo16 nn, hi16 nn]

  -- Stack
  | .PUSH rp   => [mkOpcode 3 (rp.toCode * 2) 5]
  | .POP rp    => [mkOpcode 3 (rp.toCode * 2) 1]
  | .PUSHi idx => [idxPrefix idx, 0xE5]
  | .POPi idx  => [idxPrefix idx, 0xE1]

  -- Exchange
  | .EX_AF => [0x08]
  | .EXX => [0xD9]
  | .EX_DE_HL => [0xEB]
  | .EX_SP_HL => [0xE3]
  | .EX_SP_Idx idx => [idxPrefix idx, 0xE3]

  -- 8-bit ALU
  | .ALU op src =>
    match src with
    | .reg r  => [mkOpcode 2 op.toCode r.toCode]
    | .indHL  => [mkOpcode 2 op.toCode 6]
    | .indIdx idx d => [idxPrefix idx, mkOpcode 2 op.toCode 6, d]
    | _ => [0x00]
  | .ALUimm op n => [mkOpcode 3 op.toCode 6, n]

  -- INC/DEC 8-bit
  | .INC8 loc =>
    match loc with
    | .reg r  => [mkOpcode 0 r.toCode 4]
    | .indHL  => [0x34]
    | .indIdx idx d => [idxPrefix idx, 0x34, d]
    | _ => [0x00]
  | .DEC8 loc =>
    match loc with
    | .reg r  => [mkOpcode 0 r.toCode 5]
    | .indHL  => [0x35]
    | .indIdx idx d => [idxPrefix idx, 0x35, d]
    | _ => [0x00]

  -- Misc arithmetic
  | .DAA => [0x27]
  | .CPL => [0x2F]
  | .NEG => [0xED, 0x44]
  | .SCF => [0x37]
  | .CCF => [0x3F]

  -- 16-bit arithmetic
  | .ADD_HL rp  => [mkOpcode 0 (rp.toCode * 2 + 1) 1]
  | .ADD_Idx idx rp => [idxPrefix idx, mkOpcode 0 (rp.toCode * 2 + 1) 1]
  | .ADC_HL rp  => [0xED, mkOpcode 1 (rp.toCode * 2 + 1) 2]
  | .SBC_HL rp  => [0xED, mkOpcode 1 (rp.toCode * 2) 2]
  | .INC16 rp   => [mkOpcode 0 (rp.toCode * 2) 3]
  | .DEC16 rp   => [mkOpcode 0 (rp.toCode * 2 + 1) 3]
  | .INCIdx idx => [idxPrefix idx, 0x23]
  | .DECIdx idx => [idxPrefix idx, 0x2B]

  -- Rotate accumulator
  | .RLCA => [0x07]
  | .RRCA => [0x0F]
  | .RLA  => [0x17]
  | .RRA  => [0x1F]

  -- CB-prefix rotate/shift/bit
  | .ROT op (.reg r)  => [0xCB, mkOpcode 0 op.toCode r.toCode]
  | .ROT op .indHL    => [0xCB, mkOpcode 0 op.toCode 6]
  | .ROT op (.indIdx idx d) => [idxPrefix idx, 0xCB, d, mkOpcode 0 op.toCode 6]
  | .ROT _ _ => [0x00]
  | .BIT b (.reg r)  => [0xCB, mkOpcode 1 b.val r.toCode]
  | .BIT b .indHL    => [0xCB, mkOpcode 1 b.val 6]
  | .BIT b (.indIdx idx d) => [idxPrefix idx, 0xCB, d, mkOpcode 1 b.val 6]
  | .BIT _ _ => [0x00]
  | .SET b (.reg r)  => [0xCB, mkOpcode 3 b.val r.toCode]
  | .SET b .indHL    => [0xCB, mkOpcode 3 b.val 6]
  | .SET b (.indIdx idx d) => [idxPrefix idx, 0xCB, d, mkOpcode 3 b.val 6]
  | .SET _ _ => [0x00]
  | .RES b (.reg r)  => [0xCB, mkOpcode 2 b.val r.toCode]
  | .RES b .indHL    => [0xCB, mkOpcode 2 b.val 6]
  | .RES b (.indIdx idx d) => [idxPrefix idx, 0xCB, d, mkOpcode 2 b.val 6]
  | .RES _ _ => [0x00]

  -- BCD rotate digit
  | .RRD => [0xED, 0x67]
  | .RLD => [0xED, 0x6F]

  -- Jumps
  | .JP nn       => [0xC3, lo16 nn, hi16 nn]
  | .JP_cc cc nn => [mkOpcode 3 cc.toCode 2, lo16 nn, hi16 nn]
  | .JR e        => [0x18, e]
  | .JR_cc cc e  =>
    let code := match cc with
      | .NZ => 0 | .Z => 1 | .NC => 2 | .C => 3
      | _ => 0
    [(0x20 + code * 8).toUInt8, e]
  | .JP_HL       => [0xE9]
  | .JP_Idx idx  => [idxPrefix idx, 0xE9]
  | .DJNZ e      => [0x10, e]

  -- Calls and returns
  | .CALL nn       => [0xCD, lo16 nn, hi16 nn]
  | .CALL_cc cc nn => [mkOpcode 3 cc.toCode 4, lo16 nn, hi16 nn]
  | .RET           => [0xC9]
  | .RET_cc cc     => [mkOpcode 3 cc.toCode 0]
  | .RETI          => [0xED, 0x4D]
  | .RETN          => [0xED, 0x45]
  | .RST vec       => [mkOpcode 3 (vec.toNat / 8) 7]

  -- I/O
  | .IN_A_n n    => [0xDB, n]
  | .OUT_n_A n   => [0xD3, n]
  | .IN_r_C r    => [0xED, mkOpcode 1 r.toCode 0]
  | .OUT_C_r r   => [0xED, mkOpcode 1 r.toCode 1]

  -- Block transfer
  | .LDblock .Inc  => [0xED, 0xA0]
  | .LDblock .Dec  => [0xED, 0xA8]
  | .LDblockR .Inc => [0xED, 0xB0]
  | .LDblockR .Dec => [0xED, 0xB8]
  | .CPblock .Inc  => [0xED, 0xA1]
  | .CPblock .Dec  => [0xED, 0xA9]
  | .CPblockR .Inc => [0xED, 0xB1]
  | .CPblockR .Dec => [0xED, 0xB9]
  | .INblock .Inc  => [0xED, 0xA2]
  | .INblock .Dec  => [0xED, 0xAA]
  | .INblockR .Inc => [0xED, 0xB2]
  | .INblockR .Dec => [0xED, 0xBA]
  | .OUTblock .Inc  => [0xED, 0xA3]
  | .OUTblock .Dec  => [0xED, 0xAB]
  | .OUTblockR .Inc => [0xED, 0xB3]
  | .OUTblockR .Dec => [0xED, 0xBB]

/-- Encode a list of instructions into a flat byte list. -/
def encodeProgram (instrs : List Instr) : List Byte :=
  instrs.flatMap encode

end Z80
