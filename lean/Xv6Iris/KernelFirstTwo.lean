/-
Verifying the xv6 kernel's first two instructions on the *real* Sail RISC-V model,
by kernel reduction of the actual `try_step` (the analog of Rocq's
`wp_kernel_first_two`).

    _entry:  auipc sp, 0xa        # 0x80000000 : 0x0000a117
             ld   sp, 472(sp)     # 0x80000004 : 0x1d813103

Starting from a booting-Machine state with those two instructions in memory at the
entry point (and an 8-byte value at sp+472), two `riscv_step`s leave
`PC = entry+8` and `sp` holding the loaded doubleword. Everything (fetch, decode,
execute, retire) is the generated model's real `try_step`, evaluated concretely
through the free-monad interpreter `exec`.

NOTE: proved by `rfl` (kernel reduction). Needs a large interpreter stack — build
with `make kernel-first-two` (which passes `--tstack`), not a plain `lake build`.
-/
import Xv6Iris.Model
import Xv6Iris.RealRegs
import LeanRV64D

open Xv6Iris.Model LeanRV64D.Defs LeanRV64D.Functions PreSail

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000000

namespace Xv6Iris.Model.KernelFirstTwo

/-- An all-permissive PMA region covering the kernel RAM (boot config). -/
noncomputable def ramPMA : PMA := { (default : PMA) with
  executable := true, readable := true, writable := true }
noncomputable def ramRegion : PMA_Region :=
  { base := 0x80000000#64, size := 0x10000000#64, attributes := ramPMA, include_in_device_tree := false }

/-- Memory image: `auipc sp,0xa` (0x0000a117, LE) at the entry `0x80000000`,
`ld sp,472(sp)` (0x1d813103, LE) at `0x80000004`, and the 8-byte value
`0x0123456789ABCDEF` at `sp+472 = 0x8000A1D8`. -/
noncomputable def mem0 (a : Nat) : Option (BitVec 8) :=
  if a = 0x80000000 then some 0x17 else if a = 0x80000001 then some 0xa1
  else if a = 0x80000002 then some 0x00 else if a = 0x80000003 then some 0x00
  else if a = 0x80000004 then some 0x03 else if a = 0x80000005 then some 0x31
  else if a = 0x80000006 then some 0x81 else if a = 0x80000007 then some 0x1d
  else if a = 0x8000A1D8 then some 0xEF else if a = 0x8000A1D9 then some 0xCD
  else if a = 0x8000A1DA then some 0xAB else if a = 0x8000A1DB then some 0x89
  else if a = 0x8000A1DC then some 0x67 else if a = 0x8000A1DD then some 0x45
  else if a = 0x8000A1DE then some 0x23 else if a = 0x8000A1DF then some 0x01
  else some 0#8

/-- The booting-Machine-mode initial state at the kernel entry. -/
noncomputable def σ0 : MState where
  regs r := match r with
    | .cur_privilege => some Privilege.Machine
    | .PC => some (0x80000000#64)
    | .misa => some (BitVec.allOnes 64)
    | .pma_regions => some [ramRegion]
    | r => some (decReg r 0)
  mem := mem0

/-- **The xv6 kernel's first two instructions, verified on the real model.**
Two `riscv_step`s of the generated `try_step` advance `PC` to `entry+8` and load
the doubleword at `sp+472` into `sp` — `auipc sp,0xa; ld sp,472(sp)`. -/
theorem kernel_first_two :
    ((exec riscv_step σ0).bind (fun p => exec riscv_step p.2)).map
        (fun p => (p.2.regs Register.PC, p.2.regs Register.x2))
      = some (some 0x80000008#64, some 0x0123456789ABCDEF#64) := by
  -- kernel reduction of the real `try_step` (twice). `rfl`/`decide` use the
  -- elaborator's whnf, which won't crunch the structural-recursion (`brecOn`)
  -- interpreter; `with_unfolding_all` reduces at full transparency like `#reduce`.
  with_unfolding_all rfl

end Xv6Iris.Model.KernelFirstTwo
