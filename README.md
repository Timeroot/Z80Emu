This repository contains:
 * An emulator of the Z80 processor in Lean, suitable for actually running programs and evaluating, together with utilities for calling these functions from Lean.
 * An assembler (in Lean) to translate strings into bytecode that you can then execute.
 * An example assembly implementation of BigNum arithmetic and GCD (Euclidean algorithm), together with a Lean proof of correctness.

All is written by Harmonic's [Aristotle](http://aristotle.harmnonic.fun/) across 16 submissions. The code has not been edited by a human at all. Accordingly, the proofs are quite a mess. The emulator implementation seems fine though! I've made a deliberate choice to leave the code unedited, since this is mostly an interesting "huh, AI can do this!" artifact and not really intended for serious deployment anywhere. (Who would want to deploy it, anyway?)
