import Z80Emu.Types
import Z80Emu.State
import Z80Emu.Instr

/-!
# Z80 Instruction Decoder

Turns a stream of bytes (read from memory starting at PC) into a
decoded `Instr` value plus the number of bytes consumed.

## Decoding algorithm

1. Check for an IX/IY prefix byte (0xDD / 0xFD).
2. Check for a CB or ED second prefix.
3. Decode the main opcode using the standard *octal decomposition*
   (`x`, `y`, `z`, `p`, `q` fields).
4. Read any trailing immediate operands.
-/

namespace Z80

-- ═══ Helpers: register lookup from 3-bit field ═══

/-- Map a 3-bit register code to a `Reg8` (for codes 0–5 and 7).
    Code 6 is `(HL)` and must be handled separately. -/
def reg8of (code : Nat) : Reg8 :=
  match code with
  | 0 => .B | 1 => .C | 2 => .D | 3 => .E
  | 4 => .H | 5 => .L | 7 => .A
  | _ => .A  -- unreachable for valid codes

/-- Map a 3-bit code to a `Loc8`, treating 6 as `(HL)`. -/
def loc8of (code : Nat) : Loc8 :=
  if code == 6 then .indHL
  else .reg (reg8of code)

/-- Like `loc8of` but when an IX/IY prefix is active. -/
def loc8ofIdx (idx : IdxReg) (code : Nat) (disp : Byte) : Loc8 :=
  match code with
  | 4 => .idxH idx
  | 5 => .idxL idx
  | 6 => .indIdx idx disp
  | _ => .reg (reg8of code)

/-- Map a 2-bit register-pair code to `Reg16`. -/
def reg16of (code : Nat) : Reg16 :=
  match code with
  | 0 => .BC | 1 => .DE | 2 => .HL | _ => .SP

/-- Map a 2-bit register-pair code to `Reg16s` (push/pop variant, 3=AF). -/
def reg16sof (code : Nat) : Reg16s :=
  match code with
  | 0 => .BC | 1 => .DE | 2 => .HL | _ => .AF

/-- Map a 3-bit condition code to `Cond`. -/
def condOf (code : Nat) : Cond :=
  match code with
  | 0 => .NZ | 1 => .Z | 2 => .NC | 3 => .C
  | 4 => .PO | 5 => .PE | 6 => .P  | _ => .M

/-- Map a 3-bit ALU operation code to `ALUOp`. -/
def aluOf (code : Nat) : ALUOp :=
  match code with
  | 0 => .ADD | 1 => .ADC | 2 => .SUB | 3 => .SBC
  | 4 => .AND | 5 => .XOR | 6 => .OR  | _ => .CP

/-- Map a 3-bit rotation/shift code to `RotOp`. -/
def rotOf (code : Nat) : RotOp :=
  match code with
  | 0 => .RLC | 1 => .RRC | 2 => .RL  | 3 => .RR
  | 4 => .SLA | 5 => .SRA | 6 => .SLL | _ => .SRL

-- ═══ CB-prefix decoder ═══

/-- Decode a CB-prefixed instruction. -/
def decodeCB (opc : Byte) (idxInfo : Option (IdxReg × Byte)) : Instr :=
  let x := opcX opc
  let y := opcY opc
  let z := opcZ opc
  let loc : Loc8 :=
    match idxInfo with
    | some (idx, d) => .indIdx idx d
    | none => loc8of z
  match x with
  | 0 => .ROT (rotOf y) loc
  | 1 => .BIT ⟨y % 8, by omega⟩ loc
  | 2 => .RES ⟨y % 8, by omega⟩ loc
  | _ => .SET ⟨y % 8, by omega⟩ loc

-- ═══ ED-prefix decoder ═══

/-- Decode an ED-prefixed instruction.
    Returns `(instr, extraBytes)`. -/
def decodeED (opc : Byte) : Instr × Nat :=
  let x := opcX opc
  let y := opcY opc
  let z := opcZ opc
  let p := opcP opc
  let q := opcQ opc
  match x with
  | 1 =>
    match z with
    | 0 => (.IN_r_C (reg8of y), 0)
    | 1 => (.OUT_C_r (reg8of y), 0)
    | 2 =>
      if q == 0 then (.SBC_HL (reg16of p), 0)
      else           (.ADC_HL (reg16of p), 0)
    | 3 =>
      -- The address word will be filled in by the top-level decoder
      if q == 0 then (.LDnn_rp (reg16of p) 0, 2)
      else           (.LDrp_nn (reg16of p) 0, 2)
    | 4 => (.NEG, 0)
    | 5 =>
      if q == 0 then (.RETN, 0)
      else           (.RETI, 0)
    | 6 =>
      let mode : IntMode :=
        match y with
        | 0 | 1 => .im0
        | 2     => .im1
        | _     => .im2
      (.IM mode, 0)
    | _ => -- z = 7
      match y with
      | 0 => (.LDI_A, 0)
      | 1 => (.LDR_A, 0)
      | 2 => (.LDA_I, 0)
      | 3 => (.LDA_R, 0)
      | 4 => (.RRD,   0)
      | 5 => (.RLD,   0)
      | _ => (.NOP,   0)
  | 2 =>
    if y >= 4 && z <= 3 then
      let dir : BlockDir := if (y &&& 1) == 0 then .Inc else .Dec
      let rep : Bool := y >= 6
      match z with
      | 0 => if rep then (.LDblockR dir, 0) else (.LDblock dir, 0)
      | 1 => if rep then (.CPblockR dir, 0) else (.CPblock dir, 0)
      | 2 => if rep then (.INblockR dir, 0) else (.INblock dir, 0)
      | _ => if rep then (.OUTblockR dir, 0) else (.OUTblock dir, 0)
    else
      (.NOP, 0)
  | _ => (.NOP, 0)

-- ═══ Root instruction decoder ═══

/-- Decode a root (unprefixed) instruction. -/
def decodeRoot (opc : Byte) (idxOpt : Option IdxReg)
    (fetch : Nat → Byte) (fetchWord : Nat → Word) : Instr × Nat :=
  let mkLoc (code : Nat) (dispOffset : Nat) : Loc8 :=
    match idxOpt with
    | some idx =>
      if code == 6 then .indIdx idx (fetch dispOffset)
      else if code == 4 then .idxH idx
      else if code == 5 then .idxL idx
      else .reg (reg8of code)
    | none => loc8of code

  let x := opcX opc
  let y := opcY opc
  let z := opcZ opc
  let p := opcP opc
  let q := opcQ opc

  match x with
  | 0 =>
    match z with
    | 0 =>
      match y with
      | 0 => (.NOP, 0)
      | 1 => (.EX_AF, 0)
      | 2 => (.DJNZ (fetch 0), 1)
      | 3 => (.JR (fetch 0), 1)
      | _ => (.JR_cc (condOf (y - 4)) (fetch 0), 1)
    | 1 =>
      if q == 0 then
        match idxOpt with
        | some idx =>
          if p == 2 then (.LDIdx_nn idx (fetchWord 0), 2)
          else (.LD16imm (reg16of p) (fetchWord 0), 2)
        | none => (.LD16imm (reg16of p) (fetchWord 0), 2)
      else
        match idxOpt with
        | some idx => (.ADD_Idx idx (reg16of p), 0)
        | none     => (.ADD_HL (reg16of p), 0)
    | 2 =>
      match q, p with
      | 0, 0 => (.LDind_A .BC, 0)
      | 0, 1 => (.LDind_A .DE, 0)
      | 0, 2 =>
        match idxOpt with
        | some idx => (.LDnn_Idx idx (fetchWord 0), 2)
        | none     => (.LDnn_HL (fetchWord 0), 2)
      | 0, _ => (.LDnn_A (fetchWord 0), 2)
      | _, 0 => (.LDA_ind .BC, 0)
      | _, 1 => (.LDA_ind .DE, 0)
      | _, 2 =>
        match idxOpt with
        | some idx => (.LDIdx_ind idx (fetchWord 0), 2)
        | none     => (.LDHL_nn (fetchWord 0), 2)
      | _, _ => (.LDA_nn (fetchWord 0), 2)
    | 3 =>
      if q == 0 then
        match idxOpt with
        | some idx => if p == 2 then (.INCIdx idx, 0) else (.INC16 (reg16of p), 0)
        | none     => (.INC16 (reg16of p), 0)
      else
        match idxOpt with
        | some idx => if p == 2 then (.DECIdx idx, 0) else (.DEC16 (reg16of p), 0)
        | none     => (.DEC16 (reg16of p), 0)
    | 4 =>
      let needsDisp := y == 6 && idxOpt.isSome
      let loc := mkLoc y 0
      (.INC8 loc, if needsDisp then 1 else 0)
    | 5 =>
      let needsDisp := y == 6 && idxOpt.isSome
      let loc := mkLoc y 0
      (.DEC8 loc, if needsDisp then 1 else 0)
    | 6 =>
      let needsDisp := y == 6 && idxOpt.isSome
      if needsDisp then
        let loc := mkLoc y 0
        (.LD8imm loc (fetch 1), 2)
      else
        let loc := mkLoc y 0
        (.LD8imm loc (fetch 0), 1)
    | _ =>
      match y with
      | 0 => (.RLCA, 0) | 1 => (.RRCA, 0)
      | 2 => (.RLA,  0) | 3 => (.RRA,  0)
      | 4 => (.DAA,  0) | 5 => (.CPL,  0)
      | 6 => (.SCF,  0) | _ => (.CCF,  0)

  | 1 =>
    if y == 6 && z == 6 then
      (.HALT, 0)
    else
      let needsDisp := (y == 6 || z == 6) && idxOpt.isSome
      if needsDisp then
        let dst := if y == 6 then mkLoc 6 0 else .reg (reg8of y)
        let src := if z == 6 then mkLoc 6 0 else .reg (reg8of z)
        (.LD8 dst src, 1)
      else
        let dst := mkLoc y 0
        let src := mkLoc z 0
        (.LD8 dst src, 0)

  | 2 =>
    let needsDisp := z == 6 && idxOpt.isSome
    let src := mkLoc z 0
    (.ALU (aluOf y) src, if needsDisp then 1 else 0)

  | _ =>
    match z with
    | 0 => (.RET_cc (condOf y), 0)
    | 1 =>
      if q == 0 then
        match idxOpt with
        | some idx => if p == 2 then (.POPi idx, 0) else (.POP (reg16sof p), 0)
        | none     => (.POP (reg16sof p), 0)
      else
        match p with
        | 0 => (.RET, 0)
        | 1 => (.EXX, 0)
        | 2 =>
          match idxOpt with
          | some idx => (.JP_Idx idx, 0)
          | none     => (.JP_HL, 0)
        | _ =>
          match idxOpt with
          | some idx => (.LDSP_Idx idx, 0)
          | none     => (.LDSP_HL, 0)
    | 2 => (.JP_cc (condOf y) (fetchWord 0), 2)
    | 3 =>
      match y with
      | 0 => (.JP (fetchWord 0), 2)
      | 1 => (.NOP, 0) -- CB prefix handled separately
      | 2 => (.OUT_n_A (fetch 0), 1)
      | 3 => (.IN_A_n (fetch 0), 1)
      | 4 =>
        match idxOpt with
        | some idx => (.EX_SP_Idx idx, 0)
        | none     => (.EX_SP_HL, 0)
      | 5 => (.EX_DE_HL, 0)
      | 6 => (.DI, 0)
      | _ => (.EI, 0)
    | 4 => (.CALL_cc (condOf y) (fetchWord 0), 2)
    | 5 =>
      if q == 0 then
        match idxOpt with
        | some idx => if p == 2 then (.PUSHi idx, 0) else (.PUSH (reg16sof p), 0)
        | none     => (.PUSH (reg16sof p), 0)
      else
        match p with
        | 0 => (.CALL (fetchWord 0), 2)
        | _ => (.NOP, 0)
    | 6 => (.ALUimm (aluOf y) (fetch 0), 1)
    | _ => (.RST (y * 8).toUInt8, 0)

-- ═══ Top-level decoder ═══

/-- Result of decoding one instruction. -/
structure DecodeResult where
  instr : Instr
  len   : Nat
  deriving Repr

/-- Decode one instruction from memory at the given PC.
    This function only borrows the memory (not the full state),
    so the caller can keep the state uniquely referenced. -/
def decodeMem (mem : Memory) (pc : Word) : DecodeResult :=
  let rd  (off : Nat) : Byte := mem.read (pc + off.toUInt16)
  let rdw (off : Nat) : Word := mem.read16 (pc + off.toUInt16)

  let b0 := rd 0

  -- Step 1: Check for DD / FD index prefix
  let (idxOpt, prefixLen) : Option IdxReg × Nat :=
    if b0 == 0xDD then (some .IX, 1)
    else if b0 == 0xFD then (some .IY, 1)
    else (none, 0)

  let mainByte := rd prefixLen

  -- Step 2: Check for CB or ED second prefix
  if mainByte == 0xCB then
    match idxOpt with
    | some idx =>
      let disp := rd (prefixLen + 1)
      let opc  := rd (prefixLen + 2)
      let instr := decodeCB opc (some (idx, disp))
      ⟨instr, prefixLen + 3⟩
    | none =>
      let opc := rd (prefixLen + 1)
      let instr := decodeCB opc none
      ⟨instr, prefixLen + 2⟩
  else if mainByte == 0xED then
    let opc := rd (prefixLen + 1)
    let (instr, extra) := decodeED opc
    let instr' :=
      match extra with
      | 2 =>
        let nn := rdw (prefixLen + 2)
        match instr with
        | .LDnn_rp rp _ => .LDnn_rp rp nn
        | .LDrp_nn rp _ => .LDrp_nn rp nn
        | _ => instr
      | _ => instr
    ⟨instr', prefixLen + 2 + extra⟩
  else
    let fetchBase := prefixLen + 1
    let fetch  (off : Nat) : Byte := rd (fetchBase + off)
    let fetchW (off : Nat) : Word := rdw (fetchBase + off)
    let (instr, extra) := decodeRoot mainByte idxOpt fetch fetchW
    ⟨instr, prefixLen + 1 + extra⟩

/-- Decode one instruction starting at the current PC.
    Convenience wrapper around `decodeMem`. -/
@[inline] def decode (s : State) : DecodeResult :=
  decodeMem s.mem s.regPC

end Z80
