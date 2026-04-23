import Z80Emu.Exec

/-!
# Z80 CPU Evaluation

`CPU.eval` loads a program (given as a byte array) into memory,
runs it for up to `maxSteps` instructions, and returns the output
bytes collected from `OUT` instructions.
-/

namespace Z80

/-- Create a fresh CPU state with `prog` loaded at address 0 and SP at 0x8000. -/
def mkInitState (prog : List Byte) : State :=
  let mem := Memory.zeros.loadBytes 0 prog
  { mem := mem, regSP := 0x8000 }

/-- Run a program and return the output bytes written via OUT instructions.
    The program is loaded at address 0 and executed for at most `maxSteps` steps. -/
def eval (prog : List Byte) (maxSteps : Nat := 10000) : List Byte :=
  let s := mkInitState prog
  let s := run s maxSteps
  s.output

/-- Run a program and return the full final CPU state. -/
def evalState (prog : List Byte) (maxSteps : Nat := 10000) : State :=
  let s := mkInitState prog
  run s maxSteps

end Z80
