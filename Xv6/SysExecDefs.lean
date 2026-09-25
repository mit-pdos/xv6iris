/-
sys_exec()'s VOCABULARY LEAF: the frame budget.

A PARTIAL port of Rocq `SysExecDefs.v` (`/shared/xv6rocq/iris/SysExecDefs.v`):
its PURE part (wave-7b brief §6.1, "pure part NOW").  Rocq's header, in
short:

> `uint64 sys_exec(void)` (this image: `KA.«sys_exec»`, 268 bytes, a 480-byte
> frame -- sixty slots, sixteen of them `path[MAXPATH]` and thirty-two
> `argv[MAXARG]`).  sys_exec exists to MARSHAL: it turns two user words in the
> trapframe into exactly the resources kexec's contract demands, and it is
> the only caller kexec has.  Its result is `kexec_ok` VERBATIM, against the
> block the copy-ins left behind: every path that never reaches kexec
> returns -1 with the block unchanged, which is that relation's own failure
> arm.  THE KALLOC'D PAGES DO NOT APPEAR: every page the loop allocates is
> freed by one of the two `kfree` loops.  THE OFF-BY-ONE: gcc compiles the
> `i >= NELEM(argv)` test as the loop's back edge, so the break is reached
> with `i < 32` -- which is why kexec takes `na < MAXARG` and this function
> discharges it.

## DEFERRED (the rest of the Rocq file)

`sys_exec_post γf pa pid V r` (`∃ U' na alen entry spv szv',
⌜kexec_ok V (us_V U') r …⌝ ∗ proc_priv γf pa pid U'`) states Rocq's WHOLE
process block `proc_priv`, which carries `ProcDefs.pv_fdg`'s descriptor
fragments and `FirstTok.first_tok` (Rocq's `GenId` binder).  The Lean block
of that shape is wave-7 item C0's P2 block (`procPriv` core ∗ `procOfiles`),
with D8's `first_tok` entering through it; stating it now would state it
over the pre-C0 `procPriv` and have to be re-cut (brief rule 5, D16).  It is
APPENDED after C0 merges.  Consumers (grep): SpecSysExec.v and
ProofSysExec.v only.

Imports only definitional files.
-/
import Xv6.KexecDefs

namespace Xv6

/-- sys_exec's own sixty-slot frame over kexec's 188, by a wide margin its
deepest callee (argstr 60, fetchstr 56; Rocq `K_sys_exec`). -/
def sysExecSlots : Nat := 60 + kexecSlots

theorem sysExecSlots_val : sysExecSlots = 248 := rfl

end Xv6
