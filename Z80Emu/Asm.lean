import Z80Emu.Types
import Z80Emu.Instr
import Z80Emu.Encode
import Z80Emu.Decode
import Z80Emu.State

/-!
# Z80 Assembler

A simple assembler that translates Z80 assembly mnemonics into bytecode.
Supports labels and the most common instructions.

## Validity

We define `bytecodeDecodesCleanly` which checks that assembled bytecode
can be decoded instruction-by-instruction with no gaps or undefined opcodes.
-/

namespace Z80

/-! ## String helpers -/

private def strDrop (s : String) (n : Nat) : String := (s.drop n).toString
private def strDropEnd (s : String) (n : Nat) : String :=
  (s.drop 0 |>.dropEnd n).toString
private def strDropBoth (s : String) (front back : Nat) : String :=
  ((s.drop front).dropEnd back).toString

/-! ## Assembly line representation -/

/-- An assembly line is either a label or an instruction. -/
inductive AsmLine where
  | label : String → AsmLine
  | instr : Instr → AsmLine
  deriving Repr, BEq, Inhabited

abbrev AsmProgram := List AsmLine

/-! ## Label resolution -/

def computeLabels (prog : AsmProgram) (base : Nat := 0) : List (String × Nat) :=
  let rec go : List AsmLine → Nat → List (String × Nat) → List (String × Nat)
    | [], _, acc => acc
    | .label name :: rest, offset, acc => go rest offset ((name, offset) :: acc)
    | .instr i :: rest, offset, acc =>
        go rest (offset + (encode i).length) acc
  go prog base []

def lookupLabel (labels : List (String × Nat)) (name : String) : Option Nat :=
  labels.find? (·.1 == name) |>.map (·.2)

/-! ## Parsing helpers -/

private def trimStr (s : String) : String := s.trimAscii.toString

private def splitComma (s : String) : List String :=
  (s.splitOn ",").map trimStr

private def parseDecimal? (s : String) : Option Int :=
  if s.isEmpty then none
  else
    let neg := s.front == '-'
    let digits := if neg then strDrop s 1 else s
    if digits.isEmpty then none
    else if digits.all (fun c => c.isDigit) then
      let n := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      some (if neg then -(n : Int) else (n : Int))
    else none

private def parseHex? (s : String) : Option Nat :=
  let s := s.toLower
  let hexStr :=
    if s.startsWith "0x" then some (strDrop s 2)
    else if s.endsWith "h" then some (strDropEnd s 1)
    else none
  match hexStr with
  | none => none
  | some hs =>
    if hs.isEmpty then none
    else if hs.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
      let n := hs.foldl (fun acc c =>
        acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                   else c.toNat - 'a'.toNat + 10) 0
      some n
    else none

private def parseNum? (s : String) : Option Int :=
  match parseHex? s with
  | some n => some (n : Int)
  | none => parseDecimal? s

private def parseByte? (s : String) : Option Byte :=
  match parseNum? s with
  | some n =>
    if 0 ≤ n && n < 256 then some (n.toNat.toUInt8)
    else if -128 ≤ n && n < 0 then some ((256 + n).toNat.toUInt8)
    else none
  | none => none

private def parseWord? (s : String) : Option Word :=
  match parseNum? s with
  | some n =>
    if 0 ≤ n && n < 65536 then some (n.toNat.toUInt16)
    else none
  | none => none

private def parseReg8? (s : String) : Option Reg8 :=
  match s.toLower with
  | "a" => some .A | "b" => some .B | "c" => some .C
  | "d" => some .D | "e" => some .E | "h" => some .H | "l" => some .L
  | _ => none

private def parseReg16? (s : String) : Option Reg16 :=
  match s.toLower with
  | "bc" => some .BC | "de" => some .DE | "hl" => some .HL | "sp" => some .SP
  | _ => none

private def parseReg16s? (s : String) : Option Reg16s :=
  match s.toLower with
  | "bc" => some .BC | "de" => some .DE | "hl" => some .HL | "af" => some .AF
  | _ => none

private def parseCond? (s : String) : Option Cond :=
  match s.toLower with
  | "nz" => some .NZ | "z" => some .Z
  | "nc" => some .NC | "c" => some .C
  | "po" => some .PO | "pe" => some .PE
  | "p" => some .P   | "m" => some .M
  | _ => none

private def parseLoc8? (s : String) : Option Loc8 :=
  match parseReg8? s with
  | some r => some (.reg r)
  | none =>
    if s.toLower == "(hl)" then some .indHL
    else none

/-- Extract inner content from parenthesized expression like "(42)". -/
private def parenInner? (s : String) : Option String :=
  if s.startsWith "(" && s.endsWith ")" then
    some (trimStr (strDropBoth s 1 1))
  else none

/-! ## Instruction parser -/

private def parseInstr? (line : String) (labels : List (String × Nat))
    (currentOffset : Nat) : Option Instr :=
  let line := trimStr line
  let line := match line.splitOn ";" with
    | part :: _ => trimStr part
    | [] => line
  if line.isEmpty then none
  else
    let parts := line.splitOn " "
    let mnemonic := trimStr (parts.head!)
    let operandStr := trimStr (String.intercalate " " (parts.drop 1))
    let operands := if operandStr.isEmpty then [] else splitComma operandStr
    let mnem := mnemonic.toUpper
    match mnem with
    | "NOP"  => some .NOP
    | "HALT" => some .HALT
    | "DI"   => some .DI
    | "EI"   => some .EI
    | "RET"  => some .RET
    | "RETI" => some .RETI
    | "RETN" => some .RETN
    | "RLCA" => some .RLCA
    | "RRCA" => some .RRCA
    | "RLA"  => some .RLA
    | "RRA"  => some .RRA
    | "DAA"  => some .DAA
    | "CPL"  => some .CPL
    | "NEG"  => some .NEG
    | "SCF"  => some .SCF
    | "CCF"  => some .CCF
    | "EXX"  => some .EXX
    | "RRD"  => some .RRD
    | "RLD"  => some .RLD

    | "LD" =>
      match operands with
      | [dst, src] =>
        let dst := trimStr dst
        let src := trimStr src
        match parseReg16? dst with
        | some rp =>
          match parseWord? src with
          | some nn => some (.LD16imm rp nn)
          | none => none
        | none =>
        match parseReg8? dst with
        | some rd =>
          match parseReg8? src with
          | some rs => some (.LD8 (.reg rd) (.reg rs))
          | none =>
            if src.toLower == "(hl)" then some (.LD8 (.reg rd) .indHL)
            else match parseByte? src with
              | some n => some (.LD8imm (.reg rd) n)
              | none => none
        | none =>
        if dst.toLower == "(hl)" then
          match parseReg8? src with
          | some rs => some (.LD8 .indHL (.reg rs))
          | none => match parseByte? src with
            | some n => some (.LD8imm .indHL n)
            | none => none
        else if dst.toLower == "a" then
          if src.toLower == "(bc)" then some (.LDA_ind .BC)
          else if src.toLower == "(de)" then some (.LDA_ind .DE)
          else match parenInner? src with
            | some inner => (parseWord? inner).map .LDA_nn
            | none => none
        else if src.toLower == "a" then
          if dst.toLower == "(bc)" then some (.LDind_A .BC)
          else if dst.toLower == "(de)" then some (.LDind_A .DE)
          else match parenInner? dst with
            | some inner => (parseWord? inner).map .LDnn_A
            | none => none
        else none
      | _ => none

    | "PUSH" =>
      match operands with
      | [rp] => (parseReg16s? (trimStr rp)).map .PUSH
      | _ => none

    | "POP" =>
      match operands with
      | [rp] => (parseReg16s? (trimStr rp)).map .POP
      | _ => none

    | "ADD" =>
      match operands with
      | [dst, src] =>
        let dst := trimStr dst
        let src := trimStr src
        if dst.toLower == "a" then
          match parseLoc8? src with
          | some loc => some (.ALU .ADD loc)
          | none => (parseByte? src).map (.ALUimm .ADD)
        else if dst.toLower == "hl" then
          (parseReg16? src).map .ADD_HL
        else none
      | _ => none

    | "ADC" =>
      match operands with
      | [dst, src] =>
        let dst := trimStr dst
        let src := trimStr src
        if dst.toLower == "a" then
          match parseLoc8? src with
          | some loc => some (.ALU .ADC loc)
          | none => (parseByte? src).map (.ALUimm .ADC)
        else if dst.toLower == "hl" then
          (parseReg16? src).map .ADC_HL
        else none
      | _ => none

    | "SUB" =>
      match operands with
      | [src] =>
        let src := trimStr src
        match parseLoc8? src with
        | some loc => some (.ALU .SUB loc)
        | none => (parseByte? src).map (.ALUimm .SUB)
      | _ => none

    | "SBC" =>
      match operands with
      | [dst, src] =>
        let dst := trimStr dst
        let src := trimStr src
        if dst.toLower == "a" then
          match parseLoc8? src with
          | some loc => some (.ALU .SBC loc)
          | none => (parseByte? src).map (.ALUimm .SBC)
        else if dst.toLower == "hl" then
          (parseReg16? src).map .SBC_HL
        else none
      | _ => none

    | "AND" =>
      match operands with
      | [src] =>
        match parseLoc8? (trimStr src) with
        | some loc => some (.ALU .AND loc)
        | none => (parseByte? (trimStr src)).map (.ALUimm .AND)
      | _ => none

    | "OR" =>
      match operands with
      | [src] =>
        match parseLoc8? (trimStr src) with
        | some loc => some (.ALU .OR loc)
        | none => (parseByte? (trimStr src)).map (.ALUimm .OR)
      | _ => none

    | "XOR" =>
      match operands with
      | [src] =>
        match parseLoc8? (trimStr src) with
        | some loc => some (.ALU .XOR loc)
        | none => (parseByte? (trimStr src)).map (.ALUimm .XOR)
      | _ => none

    | "CP" =>
      match operands with
      | [src] =>
        match parseLoc8? (trimStr src) with
        | some loc => some (.ALU .CP loc)
        | none => (parseByte? (trimStr src)).map (.ALUimm .CP)
      | _ => none

    | "INC" =>
      match operands with
      | [op] =>
        let op := trimStr op
        match parseReg16? op with
        | some rp => some (.INC16 rp)
        | none => (parseLoc8? op).map .INC8
      | _ => none

    | "DEC" =>
      match operands with
      | [op] =>
        let op := trimStr op
        match parseReg16? op with
        | some rp => some (.DEC16 rp)
        | none => (parseLoc8? op).map .DEC8
      | _ => none

    | "JP" =>
      match operands with
      | [target] =>
        let target := trimStr target
        if target.toLower == "(hl)" then some .JP_HL
        else match parseWord? target with
          | some nn => some (.JP nn)
          | none => (lookupLabel labels target).map (fun addr => .JP addr.toUInt16)
      | [cc, target] =>
        let target := trimStr target
        match parseCond? (trimStr cc) with
        | some cond =>
          match parseWord? target with
          | some nn => some (.JP_cc cond nn)
          | none => (lookupLabel labels target).map (fun addr => .JP_cc cond addr.toUInt16)
        | none => none
      | _ => none

    | "JR" =>
      let resolveRel (target : String) : Option Byte :=
        match parseByte? target with
        | some e => some e
        | none =>
          match lookupLabel labels target with
          | some addr =>
            let rel := (addr : Int) - ((currentOffset : Int) + 2)
            if -128 ≤ rel && rel < 128 then
              some ((rel % 256 + 256) % 256).toNat.toUInt8
            else none
          | none => none
      match operands with
      | [target] => (resolveRel (trimStr target)).map .JR
      | [cc, target] =>
        match parseCond? (trimStr cc) with
        | some cond => (resolveRel (trimStr target)).map (.JR_cc cond)
        | none => none
      | _ => none

    | "DJNZ" =>
      match operands with
      | [target] =>
        let target := trimStr target
        match parseByte? target with
        | some e => some (.DJNZ e)
        | none =>
          match lookupLabel labels target with
          | some addr =>
            let rel := (addr : Int) - ((currentOffset : Int) + 2)
            if -128 ≤ rel && rel < 128 then
              some (.DJNZ ((rel % 256 + 256) % 256).toNat.toUInt8)
            else none
          | none => none
      | _ => none

    | "CALL" =>
      match operands with
      | [target] =>
        let target := trimStr target
        match parseWord? target with
        | some nn => some (.CALL nn)
        | none => (lookupLabel labels target).map (fun addr => .CALL addr.toUInt16)
      | [cc, target] =>
        let target := trimStr target
        match parseCond? (trimStr cc) with
        | some cond =>
          match parseWord? target with
          | some nn => some (.CALL_cc cond nn)
          | none => (lookupLabel labels target).map (fun addr => .CALL_cc cond addr.toUInt16)
        | none => none
      | _ => none

    | "RST" =>
      match operands with
      | [v] => (parseByte? (trimStr v)).map .RST
      | _ => none

    | "OUT" =>
      match operands with
      | [port, src] =>
        let port := trimStr port
        let src := trimStr src
        if src.toLower == "a" then
          match parenInner? port with
          | some inner => (parseByte? inner).map .OUT_n_A
          | none => none
        else none
      | _ => none

    | "IN" =>
      match operands with
      | [dst, port] =>
        let dst := trimStr dst
        if dst.toLower == "a" then
          match parenInner? (trimStr port) with
          | some inner => (parseByte? inner).map .IN_A_n
          | none => none
        else none
      | _ => none

    | "EX" =>
      match operands with
      | [a, b] =>
        let a := trimStr a
        let b := trimStr b
        if a.toLower == "af" && b.toLower == "af'" then some .EX_AF
        else if a.toLower == "de" && b.toLower == "hl" then some .EX_DE_HL
        else if a.toLower == "(sp)" && b.toLower == "hl" then some .EX_SP_HL
        else none
      | _ => none

    | _ => none

/-! ## Two-pass assembler -/

structure AsmResult where
  bytecode : List Byte
  instructions : List Instr
  labels : List (String × Nat)
  deriving Repr

def parseAsmLines (source : String) : List (String ⊕ String) :=
  let lines := source.splitOn "\n"
  lines.filterMap fun line =>
    let line := trimStr line
    let line := match line.splitOn ";" with
      | part :: _ => trimStr part
      | [] => line
    if line.isEmpty then none
    else if line.endsWith ":" then
      some (.inl (strDropEnd line 1))
    else
      some (.inr line)

/-- Scan label positions without parsing instructions that need labels.
    For instructions, estimate size based on mnemonic. -/
private def scanLabels (parsed : List (String ⊕ String)) : List (String × Nat) :=
  let rec go : List (String ⊕ String) → Nat → List (String × Nat) → List (String × Nat)
    | [], _, acc => acc
    | .inl name :: rest, offset, acc => go rest offset ((name, offset) :: acc)
    | .inr line :: rest, offset, acc =>
      -- Estimate instruction size from mnemonic
      let line := trimStr line
      let parts := line.splitOn " "
      let mnem := (trimStr (parts.head!)).toUpper
      let size := match mnem with
        | "NOP" | "HALT" | "RET" | "RETI" | "RETN" | "RLCA" | "RRCA" |
          "RLA" | "RRA" | "DAA" | "CPL" | "SCF" | "CCF" | "EXX" |
          "RRD" | "RLD" | "DI" | "EI" => 1
        | "JR" | "DJNZ" | "OUT" | "IN" | "EX" => 2
        | "JP" | "CALL" | "LD" =>
          -- Need to check operands for size
          let operandStr := trimStr (String.intercalate " " (parts.drop 1))
          let operands := if operandStr.isEmpty then [] else splitComma operandStr
          match mnem with
          | "LD" =>
            match operands with
            | [dst, src] =>
              let dst := trimStr dst
              let src := trimStr src
              match parseReg16? dst with
              | some _ => 3  -- LD rp, nn
              | none =>
                match parseReg8? dst with
                | some _ =>
                  -- LD r, r = 1 byte; LD r, (HL) = 1 byte; LD r, n = 2 bytes
                  match parseReg8? src with
                  | some _ => 1
                  | none => if src.toLower == "(hl)" then 1 else 2
                | none =>
                  if dst.toLower == "(hl)" then
                    match parseReg8? src with
                    | some _ => 1  -- LD (HL), r
                    | none => 2   -- LD (HL), n
                  else if dst.toLower == "a" then
                    if src.toLower == "(bc)" || src.toLower == "(de)" then 1
                    else 3  -- LD A, (nn)
                  else if src.toLower == "a" then
                    if dst.toLower == "(bc)" || dst.toLower == "(de)" then 1
                    else 3  -- LD (nn), A
                  else 2
            | _ => 2
          | "JP" =>
            match operands with
            | [_] => 3
            | [_, _] => 3
            | _ => 3
          | "CALL" => 3
          | _ => 2
        | "SUB" | "AND" | "OR" | "XOR" | "CP" =>
          let operandStr := trimStr (String.intercalate " " (parts.drop 1))
          match parseReg8? operandStr with
          | some _ => 1
          | none =>
            if operandStr.toLower == "(hl)" then 1
            else 2  -- immediate
        | "ADD" | "ADC" | "SBC" =>
          let operandStr := trimStr (String.intercalate " " (parts.drop 1))
          let operands := if operandStr.isEmpty then [] else splitComma operandStr
          match operands with
          | [dst, src] =>
            let dst := trimStr dst
            let src := trimStr src
            if dst.toLower == "hl" then 1  -- ADD HL, rp
            else match parseReg8? src with
              | some _ => 1
              | none =>
                if src.toLower == "(hl)" then 1
                else 2
          | _ => 2
        | "INC" | "DEC" => 1
        | "PUSH" | "POP" => 1
        | "RST" => 1
        | "NEG" => 2
        | _ => 1
      go rest (offset + size) acc
  go parsed 0 []

def assemble (source : String) : Option AsmResult :=
  let parsed := parseAsmLines source
  -- Pass 1: scan label positions
  let labels := scanLabels parsed
  -- Pass 2: parse all instructions with resolved labels
  let rec pass2 (lines : List (String ⊕ String)) (offset : Nat)
      (instrs : List Instr) :
      Option (List Instr) :=
    match lines with
    | [] => some instrs.reverse
    | .inl _ :: rest => pass2 rest offset instrs
    | .inr line :: rest =>
      match parseInstr? line labels offset with
      | some instr =>
        let bytes := encode instr
        pass2 rest (offset + bytes.length) (instr :: instrs)
      | none => none
  match pass2 parsed 0 [] with
  | none => none
  | some instrs =>
    let bytecode := encodeProgram instrs
    some ⟨bytecode, instrs, labels⟩

/-! ## Bytecode validity -/

/-- A bytecode is "valid" if decoding it instruction-by-instruction
    consumes exactly all bytes with no gaps. -/
def bytecodeDecodesCleanly (bytes : List Byte) : Bool :=
  let mem := Memory.zeros.loadBytes 0 bytes
  let rec check (pc : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if pc ≥ bytes.length then pc == bytes.length
      else
        let dr := decodeMem mem pc.toUInt16
        if dr.len == 0 then false
        else check (pc + dr.len) fuel
  check 0 (bytes.length + 1)

end Z80
