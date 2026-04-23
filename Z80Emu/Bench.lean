import Z80Emu.Eval
import Z80Emu.Encode

open Z80

-- Triple-nested loop writing to fixed memory address.
-- b controls outer iterations, total steps ≈ b × 256 × 256 × 3.
def benchProg (b : UInt8) (seed : UInt8) : List Byte :=
  [ 0x21, 0x00, 0x80,
    0x3E, seed,
    0x06, b,
    0x16, 0x00,
    0x0E, 0x00,
    0x77,
    0x0D,
    0x20, 0xFC,
    0x15,
    0x20, 0xF7,
    0x10, 0xF3,
    0xD3, 0x00,
    0x76
  ]

-- Force evaluation by passing result through IO ref
@[noinline] def forceEval (s : State) : IO Nat := do
  return s.regA.toNat + (if s.halted then 0 else 1)

def main : IO Unit := do
  IO.println "=== Z80 Emulator Benchmark (ByteArray-backed Memory) ==="
  IO.println ""

  let seed ← IO.rand 0 255
  let seedByte := seed.toUInt8

  IO.println s!"seed={seed}"
  IO.println ""

  IO.println "--- Step scaling (single eval, varying B) ---"

  for b in [1, 2, 4, 8, 16, 32, 64, 128, 255] do
    let prog := benchProg b.toUInt8 seedByte
    let maxSteps := b * 256 * 256 * 4 + 10000
    let start ← IO.monoMsNow
    let s := evalState prog maxSteps
    let ck ← forceEval s
    let elapsed ← IO.monoMsNow
    let dt := elapsed - start
    let approxSteps := b * 65536 * 3
    IO.println s!"  B={b}: ~{approxSteps} steps, time={dt}ms, ck={ck}"

  IO.println ""
  IO.println "--- Multi-run (N × ~200K steps, fresh 64KB alloc each) ---"

  for n in [10, 20, 50, 100, 200] do
    let start ← IO.monoMsNow
    let mut ck : Nat := 0
    let mut i : Nat := 0
    while i < n do
      let s := evalState (benchProg 1 i.toUInt8) 300000
      let v ← forceEval s
      ck := ck + v
      i := i + 1
    let elapsed ← IO.monoMsNow
    let dt := elapsed - start
    IO.println s!"  N={n}: time={dt}ms ({dt/n}ms/iter)"

  IO.println ""
  IO.println "Linear: doubling work ≈ doubles time."
