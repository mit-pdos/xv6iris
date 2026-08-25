(* SpecSysGetpid.v -- the public interface of sys_getpid(), stated
   independently of its proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

     uint64 sys_getpid(void) { return myproc()->pid; }

   @ KernelSyms.sys_getpid = 0x800028ec, ten instructions:

     +0x00  1141        c.addi     sp,sp,-16     16-byte frame
     +0x02  e406        c.sdsp     ra,8(sp)
     +0x04  e022        c.sdsp     s0,0(sp)
     +0x06  0800        c.addi4spn s0,sp,16
     +0x08  810ff0ef    jal        ra,myproc     a0 := p
     +0x0c  5908        c.lw       a0,48(a0)     a0 := sext(p->pid)
     +0x0e  60a2        c.ldsp     ra,8(sp)
     +0x10  6402        c.ldsp     s0,0(sp)
     +0x12  0141        c.addi     sp,sp,16
     +0x14  8082        c.ret

   THE POINT OF THIS SPEC.  sys_getpid reads [p->pid] with NO lock held, on a
   proc every other core may be scanning under [p->lock] at the same moment
   (kill's loop reads exactly this field).  It is the smallest function that
   exercises the [struct proc] resource split of
   claude-notes/design/proc-struct.md, and it uses precisely one piece of it:

     - [cpu_own γ n eb p C] carries [cur_proc p] -- what myproc() returns;
     - [proc_priv γf p pid V] (ProcInv.v) is the private field block that
       rides ALONGSIDE it, and [proc_priv_pid] projects the read-only pid
       fraction out of it for the [c.lw a0,48(a0)].

   The return value is [sign_extend' 64 pid]: [c.lw] is a signed 32-bit load,
   and C's [int pid] widening to the [uint64] return type is exactly that
   sign-extension (gcc emits no cast -- compare sys_uptime's slli/srli pair,
   which zero-extends its [uint]).

   Note what is NOT a premise: no [procs_inv], no lock, no [γl].  The whole
   content of the design is that this read needs none of them, and the
   returned [pid] still agrees with what any lock-holding core would read
   ([ProcInv.proc_priv_pid_agree]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.


Definition wp_sys_getpid_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_getpid in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* myproc's push_off transient increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 2 for this frame, 10 for myproc's *)
  (12 <= av)%nat ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv γf p pid V -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 pid ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid V -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSGETPID.
  Parameter wp_sys_getpid_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string),
      wp_sys_getpid_sconf_body γf m av n eb p pid V b lks.
End SYSGETPID.
