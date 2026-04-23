import Z80Emu.Exec

/-!
# Z80 Model — Smoke Tests

Quick `#eval` tests demonstrating that the model decodes and executes
real Z80 programs correctly.
-/

open Z80

-- ═══ Helper: load a program into a fresh state ═══

def mkState (prog : List Byte) : State :=
  let mem := Memory.zeros.loadBytes 0 prog
  { mem := mem }

-- ═══ Test 1: LD A, 5 ; LD B, 3 ; ADD A, B ; HALT ═══

def prog1 : List Byte := [0x3E, 0x05, 0x06, 0x03, 0x80, 0x76]

#eval
  let s := run (mkState prog1) 10
  s.regA   -- expect 8

-- ═══ Test 2: Decoding verification ═══

#eval
  let s := mkState [0x00]
  let dr := decodeMem s.mem s.regPC
  (repr dr.instr, dr.len)

-- ═══ Test 3: Loop with DJNZ ═══

def prog3 : List Byte := [
  0x06, 0x05,    -- LD B, 5
  0x3E, 0x00,    -- LD A, 0
  0x3C,          -- INC A      (address 4)
  0x10, 0xFD,    -- DJNZ -3    (jump back to INC A)
  0x76           -- HALT
]

#eval
  let s := run (mkState prog3) 100
  (s.regA, s.regB, s.halted)  -- expect (5, 0, true)

-- ═══ Test 4: PUSH / POP ═══

def prog4 : List Byte := [
  0x01, 0x34, 0x12,  -- LD BC, 0x1234
  0xC5,              -- PUSH BC
  0xD1,              -- POP DE
  0x76               -- HALT
]

#eval
  let s := run (mkState prog4) 10
  s.de.toNat   -- expect 0x1234 = 4660

-- ═══ Test 5: Conditional jump ═══

def prog5 : List Byte := [
  0x3E, 0x00,    -- LD A, 0
  0xB7,          -- OR A       (sets Z if A=0)
  0x28, 0x02,    -- JR Z, +2  (skip next 2 bytes)
  0x3E, 0xFF,    -- LD A, 0xFF (skipped)
  0x76           -- HALT
]

#eval
  let s := run (mkState prog5) 10
  s.regA   -- expect 0

-- ═══ Test 6: SUB and flags ═══

def prog6 : List Byte := [
  0x3E, 0x05,    -- LD A, 5
  0xD6, 0x05,    -- SUB 5
  0x76           -- HALT
]

#eval
  let s := run (mkState prog6) 10
  (s.regA, s.regF.z, s.regF.n, s.regF.c)  -- expect (0, true, true, false)

-- ═══ Test 7: CB-prefix BIT instruction ═══

def prog7 : List Byte := [
  0x3E, 0x08,    -- LD A, 0x08
  0xCB, 0x5F,    -- BIT 3, A
  0x76           -- HALT
]

#eval
  let s := run (mkState prog7) 10
  s.regF.z  -- expect false (bit 3 is set)

-- ═══ Test 8: CALL and RET ═══

def prog8 : List Byte := [
  0x31, 0x00, 0x80,    -- LD SP, 0x8000
  0xCD, 0x09, 0x00,    -- CALL 0x0009
  0x76,                -- HALT          (address 7)
  0x00, 0x00,          -- padding
  0x3E, 0x42,          -- LD A, 0x42   (address 9)
  0xC9                 -- RET           (address 11)
]

#eval
  let s := run (mkState prog8) 20
  (s.regA, s.halted)  -- expect (66, true)

-- ═══ Test 9: EX AF,AF' ═══

def prog9 : List Byte := [
  0x3E, 0x12,    -- LD A, 0x12
  0x08,          -- EX AF,AF'
  0x3E, 0x34,    -- LD A, 0x34
  0x08,          -- EX AF,AF'
  0x76           -- HALT
]

#eval
  let s := run (mkState prog9) 10
  s.regA   -- expect 0x12 = 18
