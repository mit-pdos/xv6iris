/-
Vtest: executable code for the machine model (see `Vtest.Compile`).

`MachCSL.riscvStep` is one fetch/decode/execute cycle of the Sail model plus
the optional clock tick; it is `noncomputable` only because the Sail backend
emits the decoder that way.  `compile_cone%` compiles a copy of each such
definition and ties it to the original by a `rfl`-proved `csimp` rule.
-/
import Vtest.Compile
import MachCSL.Lang

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

compile_cone% MachCSL.riscvStep MachCSL.bootProg
