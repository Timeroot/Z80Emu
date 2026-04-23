import Z80Emu.Types
import Z80Emu.State
import Z80Emu.Instr
import Z80Emu.ALU
import Z80Emu.Decode

/-!
# Z80 Instruction Execution

Port I/O is currently stubbed: `IN` returns `0xFF` and `OUT` is a
no-op. A full model would parameterise `step` over an I/O callback
or add ports to the state.
-/

namespace Z80

-- ═══ Operand read / write helpers ═══

/-- Read an 8-bit value from a `Loc8` operand. -/
def readLoc8 (s : State) (loc : Loc8) : Byte :=
  match loc with
  | .reg .A => s.regA
  | .reg .B => s.regB
  | .reg .C => s.regC
  | .reg .D => s.regD
  | .reg .E => s.regE
  | .reg .H => s.regH
  | .reg .L => s.regL
  | .indHL  => s.mem.read s.hl
  | .indIdx .IX d => s.mem.read (s.regIX + signExtend d)
  | .indIdx .IY d => s.mem.read (s.regIY + signExtend d)
  | .idxH .IX => hi16 s.regIX
  | .idxL .IX => lo16 s.regIX
  | .idxH .IY => hi16 s.regIY
  | .idxL .IY => lo16 s.regIY

/-- Write an 8-bit value to a `Loc8` operand. -/
def writeLoc8 (s : State) (loc : Loc8) (v : Byte) : State :=
  match loc with
  | .reg .A => { s with regA := v }
  | .reg .B => { s with regB := v }
  | .reg .C => { s with regC := v }
  | .reg .D => { s with regD := v }
  | .reg .E => { s with regE := v }
  | .reg .H => { s with regH := v }
  | .reg .L => { s with regL := v }
  | .indHL  => { s with mem := s.mem.write s.hl v }
  | .indIdx .IX d => { s with mem := s.mem.write (s.regIX + signExtend d) v }
  | .indIdx .IY d => { s with mem := s.mem.write (s.regIY + signExtend d) v }
  | .idxH .IX => { s with regIX := mkWord v (lo16 s.regIX) }
  | .idxL .IX => { s with regIX := mkWord (hi16 s.regIX) v }
  | .idxH .IY => { s with regIY := mkWord v (lo16 s.regIY) }
  | .idxL .IY => { s with regIY := mkWord (hi16 s.regIY) v }

/-- Read a 16-bit register pair. -/
def readReg16 (s : State) (rp : Reg16) : Word :=
  match rp with
  | .BC => s.bc | .DE => s.de | .HL => s.hl | .SP => s.regSP

/-- Write a 16-bit register pair. -/
def writeReg16 (s : State) (rp : Reg16) (v : Word) : State :=
  match rp with
  | .BC => s.setBC v | .DE => s.setDE v
  | .HL => s.setHL v | .SP => { s with regSP := v }

/-- Read a 16-bit push/pop register pair. -/
def readReg16s (s : State) (rp : Reg16s) : Word :=
  match rp with
  | .BC => s.bc | .DE => s.de | .HL => s.hl | .AF => s.af

/-- Write a 16-bit push/pop register pair. -/
def writeReg16s (s : State) (rp : Reg16s) (v : Word) : State :=
  match rp with
  | .BC => s.setBC v | .DE => s.setDE v
  | .HL => s.setHL v | .AF => s.setAF v

/-- Read an index register. -/
def readIdx (s : State) (idx : IdxReg) : Word :=
  match idx with | .IX => s.regIX | .IY => s.regIY

/-- Write an index register. -/
def writeIdx (s : State) (idx : IdxReg) (v : Word) : State :=
  match idx with
  | .IX => { s with regIX := v }
  | .IY => { s with regIY := v }

-- ═══ Condition evaluation ═══

/-- Evaluate a condition code against the current flags. -/
def evalCond (f : Flags) (cc : Cond) : Bool :=
  match cc with
  | .NZ => !f.z  | .Z  => f.z
  | .NC => !f.c  | .C  => f.c
  | .PO => !f.pv | .PE => f.pv
  | .P  => !f.s  | .M  => f.s

-- ═══ Instruction execution ═══

/-- Execute a single decoded instruction, returning the new state. -/
def exec (s : State) (instr : Instr) (instrLen : Nat) : State :=
  let pc' := s.regPC + instrLen.toUInt16
  let s := { s with regPC := pc' }

  match instr with

  -- CPU control
  | .NOP  => s
  | .HALT => { s with halted := true, regPC := s.regPC - instrLen.toUInt16 }
  | .DI   => { s with iff1 := false, iff2 := false }
  | .EI   => { s with iff1 := true,  iff2 := true  }
  | .IM m => { s with intMode := m }

  -- 8-bit loads
  | .LD8 dst src => writeLoc8 s dst (readLoc8 s src)
  | .LD8imm dst n => writeLoc8 s dst n
  | .LDA_ind rp => { s with regA := s.mem.read (readReg16 s rp) }
  | .LDind_A rp => { s with mem := s.mem.write (readReg16 s rp) s.regA }
  | .LDA_nn nn => { s with regA := s.mem.read nn }
  | .LDnn_A nn => { s with mem := s.mem.write nn s.regA }

  | .LDA_I =>
    let v := s.regI
    { s with regA := v,
             regF := { s.regF with
               s := testBit8 v 7, z := v == 0,
               f5 := testBit8 v 5, h := false,
               f3 := testBit8 v 3, pv := s.iff2, n := false } }

  | .LDA_R =>
    let v := s.regR
    { s with regA := v,
             regF := { s.regF with
               s := testBit8 v 7, z := v == 0,
               f5 := testBit8 v 5, h := false,
               f3 := testBit8 v 3, pv := s.iff2, n := false } }

  | .LDI_A => { s with regI := s.regA }
  | .LDR_A => { s with regR := s.regA }

  -- 16-bit loads
  | .LD16imm rp nn   => writeReg16 s rp nn
  | .LDIdx_nn idx nn  => writeIdx s idx nn
  | .LDSP_HL          => { s with regSP := s.hl }
  | .LDSP_Idx idx     => { s with regSP := readIdx s idx }
  | .LDnn_HL nn       => { s with mem := s.mem.write16 nn s.hl }
  | .LDHL_nn nn       => s.setHL (s.mem.read16 nn)
  | .LDnn_Idx idx nn  => { s with mem := s.mem.write16 nn (readIdx s idx) }
  | .LDIdx_ind idx nn => writeIdx s idx (s.mem.read16 nn)
  | .LDnn_rp rp nn    => { s with mem := s.mem.write16 nn (readReg16 s rp) }
  | .LDrp_nn rp nn    => writeReg16 s rp (s.mem.read16 nn)

  -- Stack
  | .PUSH rp  => s.push16 (readReg16s s rp)
  | .POP rp   => let (s', v) := s.pop16; writeReg16s s' rp v
  | .PUSHi idx => s.push16 (readIdx s idx)
  | .POPi idx  => let (s', v) := s.pop16; writeIdx s' idx v

  -- Exchange
  | .EX_AF =>
    { s with regA := s.regA', regF := s.regF',
             regA' := s.regA, regF' := s.regF }
  | .EXX =>
    { s with regB := s.regB', regC := s.regC',
             regD := s.regD', regE := s.regE',
             regH := s.regH', regL := s.regL',
             regB' := s.regB, regC' := s.regC,
             regD' := s.regD, regE' := s.regE,
             regH' := s.regH, regL' := s.regL }
  | .EX_DE_HL =>
    { s with regD := s.regH, regE := s.regL,
             regH := s.regD, regL := s.regE }
  | .EX_SP_HL =>
    let old := s.mem.read16 s.regSP
    let s := { s with mem := s.mem.write16 s.regSP s.hl }
    s.setHL old
  | .EX_SP_Idx idx =>
    let old := s.mem.read16 s.regSP
    let s := { s with mem := s.mem.write16 s.regSP (readIdx s idx) }
    writeIdx s idx old

  -- 8-bit ALU
  | .ALU op src =>
    let b := readLoc8 s src
    let (result, flags) := alu8 op s.regA b s.regF.c
    match op with
    | .CP => { s with regF := flags }
    | _   => { s with regA := result, regF := flags }

  | .ALUimm op n =>
    let (result, flags) := alu8 op s.regA n s.regF.c
    match op with
    | .CP => { s with regF := flags }
    | _   => { s with regA := result, regF := flags }

  | .INC8 loc =>
    let v := readLoc8 s loc
    let (result, flags) := inc8 v
    let flags := { flags with c := s.regF.c }
    writeLoc8 { s with regF := flags } loc result

  | .DEC8 loc =>
    let v := readLoc8 s loc
    let (result, flags) := dec8 v
    let flags := { flags with c := s.regF.c }
    writeLoc8 { s with regF := flags } loc result

  | .DAA =>
    let (result, flags) := daa s.regA s.regF
    { s with regA := result, regF := flags }

  | .CPL =>
    let result := ~~~s.regA
    { s with regA := result,
             regF := { s.regF with h := true, n := true,
                                   f5 := testBit8 result 5,
                                   f3 := testBit8 result 3 } }

  | .NEG =>
    let (result, flags) := sub8 0 s.regA false
    { s with regA := result, regF := flags }

  | .SCF =>
    { s with regF := { s.regF with h := false, n := false, c := true,
                                   f5 := testBit8 s.regA 5,
                                   f3 := testBit8 s.regA 3 } }

  | .CCF =>
    { s with regF := { s.regF with h := s.regF.c, n := false, c := !s.regF.c,
                                   f5 := testBit8 s.regA 5,
                                   f3 := testBit8 s.regA 3 } }

  -- 16-bit arithmetic
  | .ADD_HL rp =>
    let (result, flags) := add16 s.hl (readReg16 s rp) s.regF
    { (s.setHL result) with regF := flags }

  | .ADD_Idx idx rp =>
    let src := if rp == .HL then readIdx s idx else readReg16 s rp
    let (result, flags) := add16 (readIdx s idx) src s.regF
    { (writeIdx s idx result) with regF := flags }

  | .ADC_HL rp =>
    let (result, flags) := adc16 s.hl (readReg16 s rp) s.regF.c
    { (s.setHL result) with regF := flags }

  | .SBC_HL rp =>
    let (result, flags) := sbc16 s.hl (readReg16 s rp) s.regF.c
    { (s.setHL result) with regF := flags }

  | .INC16 rp => writeReg16 s rp (readReg16 s rp + 1)
  | .DEC16 rp => writeReg16 s rp (readReg16 s rp - 1)
  | .INCIdx idx => writeIdx s idx (readIdx s idx + 1)
  | .DECIdx idx => writeIdx s idx (readIdx s idx - 1)

  -- Rotate — accumulator (root)
  | .RLCA =>
    let bit7 := testBit8 s.regA 7
    let result := (s.regA <<< 1) ||| (if bit7 then 1 else 0)
    { s with regA := result,
             regF := { s.regF with h := false, n := false, c := bit7,
                                   f5 := testBit8 result 5,
                                   f3 := testBit8 result 3 } }
  | .RRCA =>
    let bit0 := testBit8 s.regA 0
    let result := (s.regA >>> 1) ||| (if bit0 then (0x80 : Byte) else 0)
    { s with regA := result,
             regF := { s.regF with h := false, n := false, c := bit0,
                                   f5 := testBit8 result 5,
                                   f3 := testBit8 result 3 } }
  | .RLA =>
    let bit7 := testBit8 s.regA 7
    let result := (s.regA <<< 1) ||| (if s.regF.c then (1 : Byte) else 0)
    { s with regA := result,
             regF := { s.regF with h := false, n := false, c := bit7,
                                   f5 := testBit8 result 5,
                                   f3 := testBit8 result 3 } }
  | .RRA =>
    let bit0 := testBit8 s.regA 0
    let result := (s.regA >>> 1) ||| (if s.regF.c then (0x80 : Byte) else 0)
    { s with regA := result,
             regF := { s.regF with h := false, n := false, c := bit0,
                                   f5 := testBit8 result 5,
                                   f3 := testBit8 result 3 } }

  -- Rotate / shift / bit — CB prefix
  | .ROT op loc =>
    let v := readLoc8 s loc
    let (result, flags) := rotShift op v s.regF.c
    writeLoc8 { s with regF := flags } loc result

  | .BIT b loc =>
    let v := readLoc8 s loc
    let tested := testBit8 v b.val
    { s with regF := { s.regF with
        z  := !tested,
        s  := b.val == 7 && tested,
        h  := true,
        pv := !tested,
        n  := false,
        f5 := testBit8 v 5,
        f3 := testBit8 v 3 } }

  | .SET b loc =>
    writeLoc8 s loc (setBit8 (readLoc8 s loc) b.val)

  | .RES b loc =>
    writeLoc8 s loc (clearBit8 (readLoc8 s loc) b.val)

  -- BCD rotate digit
  | .RRD =>
    let memVal := s.mem.read s.hl
    let aLo := s.regA &&& (0x0F : Byte)
    let result := (s.regA &&& (0xF0 : Byte)) ||| (memVal &&& (0x0F : Byte))
    let newMem := (aLo <<< 4) ||| (memVal >>> 4)
    { s with regA := result,
             regF := { s.regF with
               s := testBit8 result 7, z := result == 0,
               f5 := testBit8 result 5, h := false,
               f3 := testBit8 result 3, pv := parity8 result,
               n := false },
             mem := s.mem.write s.hl newMem }

  | .RLD =>
    let memVal := s.mem.read s.hl
    let aLo := s.regA &&& (0x0F : Byte)
    let result := (s.regA &&& (0xF0 : Byte)) ||| (memVal >>> 4)
    let newMem := (memVal <<< 4) ||| aLo
    { s with regA := result,
             regF := { s.regF with
               s := testBit8 result 7, z := result == 0,
               f5 := testBit8 result 5, h := false,
               f3 := testBit8 result 3, pv := parity8 result,
               n := false },
             mem := s.mem.write s.hl newMem }

  -- Jumps
  | .JP nn       => { s with regPC := nn }
  | .JP_cc cc nn => if evalCond s.regF cc then { s with regPC := nn } else s
  | .JR e        => { s with regPC := s.regPC + signExtend e }
  | .JR_cc cc e  =>
    if evalCond s.regF cc then { s with regPC := s.regPC + signExtend e } else s
  | .JP_HL       => { s with regPC := s.hl }
  | .JP_Idx idx  => { s with regPC := readIdx s idx }
  | .DJNZ e =>
    let b' := s.regB - 1
    let s := { s with regB := b' }
    if b' != 0 then { s with regPC := s.regPC + signExtend e } else s

  -- Calls and returns
  | .CALL nn =>
    let s := s.push16 s.regPC
    { s with regPC := nn }

  | .CALL_cc cc nn =>
    if evalCond s.regF cc then
      let s := s.push16 s.regPC
      { s with regPC := nn }
    else s

  | .RET =>
    let (s, addr) := s.pop16
    { s with regPC := addr }

  | .RET_cc cc =>
    if evalCond s.regF cc then
      let (s, addr) := s.pop16
      { s with regPC := addr }
    else s

  | .RETI =>
    let (s, addr) := s.pop16
    { s with regPC := addr, iff1 := s.iff2 }

  | .RETN =>
    let (s, addr) := s.pop16
    { s with regPC := addr, iff1 := s.iff2 }

  | .RST vec =>
    let s := s.push16 s.regPC
    { s with regPC := vec.toUInt16 }

  -- Input / Output (stubbed)
  | .IN_A_n _    => { s with regA := 0xFF }
  | .OUT_n_A _   => { s with output := s.output ++ [s.regA] }
  | .IN_r_C r    =>
    let v : Byte := 0xFF
    let flags := { s.regF with
      s := testBit8 v 7, z := v == 0,
      f5 := testBit8 v 5, h := false,
      f3 := testBit8 v 3, pv := parity8 v, n := false }
    writeLoc8 { s with regF := flags } (.reg r) v
  | .OUT_C_r r   => { s with output := s.output ++ [readLoc8 s (.reg r)] }

  -- Block transfer
  | .LDblock dir =>
    let v := s.mem.read s.hl
    let s := { s with mem := s.mem.write s.de v }
    let delta : Word := match dir with | .Inc => 1 | .Dec => (0xFFFF : Word)
    let s := s.setHL (s.hl + delta)
    let s := s.setDE (s.de + delta)
    let bc' : Word := s.bc - 1
    let s := s.setBC bc'
    let bv := v + s.regA
    { s with regF := { s.regF with h := false, pv := bc' != (0 : Word), n := false,
                                   f5 := testBit8 bv 1, f3 := testBit8 bv 3 } }

  | .LDblockR dir =>
    let v := s.mem.read s.hl
    let s := { s with mem := s.mem.write s.de v }
    let delta : Word := match dir with | .Inc => 1 | .Dec => (0xFFFF : Word)
    let s := s.setHL (s.hl + delta)
    let s := s.setDE (s.de + delta)
    let bc' : Word := s.bc - 1
    let s := s.setBC bc'
    let bv := v + s.regA
    let s := { s with regF := { s.regF with h := false, pv := bc' != (0 : Word), n := false,
                                            f5 := testBit8 bv 1, f3 := testBit8 bv 3 } }
    if bc' != (0 : Word) then
      { s with regPC := s.regPC - instrLen.toUInt16 }
    else s

  -- Block search
  | .CPblock dir =>
    let v := s.mem.read s.hl
    let (result, flags) := sub8 s.regA v false
    let delta : Word := match dir with | .Inc => 1 | .Dec => (0xFFFF : Word)
    let s := s.setHL (s.hl + delta)
    let bc' : Word := s.bc - 1
    let s := s.setBC bc'
    let adj := result - (if flags.h then (1 : Byte) else 0)
    { s with regF := { flags with pv := bc' != (0 : Word), c := s.regF.c,
                                  f5 := testBit8 adj 1, f3 := testBit8 adj 3 } }

  | .CPblockR dir =>
    let v := s.mem.read s.hl
    let (result, flags) := sub8 s.regA v false
    let delta : Word := match dir with | .Inc => 1 | .Dec => (0xFFFF : Word)
    let s := s.setHL (s.hl + delta)
    let bc' : Word := s.bc - 1
    let s := s.setBC bc'
    let adj := result - (if flags.h then (1 : Byte) else 0)
    let s := { s with regF := { flags with pv := bc' != (0 : Word), c := s.regF.c,
                                           f5 := testBit8 adj 1, f3 := testBit8 adj 3 } }
    if bc' != (0 : Word) && !flags.z then
      { s with regPC := s.regPC - instrLen.toUInt16 }
    else s

  -- Block I/O (stubbed)
  | .INblock _    => s
  | .INblockR _   => s
  | .OUTblock _   => s
  | .OUTblockR _  => s

-- ═══ Top-level step function ═══

/-- Execute one instruction: fetch → decode → execute. -/
def step (s : State) : State :=
  if s.halted then s
  else
    -- Decode using only memory and PC, so that `s` stays uniquely referenced.
    let dr := decodeMem s.mem s.regPC
    let r' := (s.regR &&& (0x80 : Byte)) ||| ((s.regR + 1) &&& (0x7F : Byte))
    let s := { s with regR := r' }
    exec s dr.instr dr.len

/-- Execute `n` instructions (or until halted). -/
def run (s : State) (n : Nat) : State :=
  match n with
  | 0 => s
  | n + 1 =>
    if s.halted then s
    else run (step s) n

end Z80
