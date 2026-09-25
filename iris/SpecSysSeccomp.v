(* SpecSysSeccomp.v -- the public interface of sys_seccomp() (upstream
   a083670), stated independently of its proof.  Requires only the
   definitional layer -- never a whole-function proof file -- so every
   function proof can be checked in parallel.

     uint64 sys_seccomp(void) {
       uint64 mask;
       argaddr(0, &mask);
       myproc()->seccomp &= mask;
       return 0;
     }

   @ KernelSyms.sys_seccomp, twenty-three instructions:

     +0x00  1101        c.addi     sp,sp,-32     32-byte frame
     +0x02  ec06        c.sdsp     ra,24(sp)
     +0x04  e822        c.sdsp     s0,16(sp)
     +0x06  1000        c.addi4spn s0,sp,32
     +0x08  fe840593    addi       a1,s0,-24     a1 := &mask
     +0x0c  4501        c.li       a0,0
     +0x0e  ...         jal        ra,argaddr    mask := trapframe a0
     +0x12  ...         jal        ra,myproc     a0 := p
     +0x16  16853783    ld         a5,360(a0)    a5 := p->seccomp
     +0x1a  fe843703    ld         a4,-24(s0)    a4 := mask
     +0x1e  8ff9        c.and      a5,a5,a4
     +0x20  16f53423    sd         a5,360(a0)    p->seccomp &= mask
     +0x24  4501        c.li       a0,0          return 0
     +0x26  60e2        c.ldsp     ra,24(sp)
     +0x28  6442        c.ldsp     s0,16(sp)
     +0x2a  6105        c.addi16sp sp,32
     +0x2c  8082        c.ret

   sys_getpid's shape (the running process's own block, no lock), plus
   argaddr's trapframe read: the mask cell [ProcGeom.p_secc] is the owner's
   ([ProcInv.proc_fields] carries it), so the AND needs no lock, and the
   block comes back at [ProcInv.us_secc] -- the one move of
   [ProcDefs.pv_secc] a syscall makes ([UsysMemOk.usys_secc_ok] is the row
   the dispatcher relays). *)
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
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecArgaddr.   (* [argaddr_stack] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import CtxIdDefs.
Import Defs.

(* 4 slots for this frame, and below it the deeper of the two callees:
   argaddr ([argaddr_stack]) and myproc (10). *)
Notation sys_seccomp_stack := ((4 + argaddr_stack)%nat) (only parsing).

Definition wp_sys_seccomp_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γf : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (pid : mword 32) (U : ustate) (v0 : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_seccomp in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the syscall argument, out of the trapframe page [proc_priv] carries *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  (* myproc's / argraw's push_off transient increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (sys_seccomp_stack <= av)%nat ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  proc_priv γf p pid U -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64) ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      (* THE MASK, ANDED with argument 0: [p->seccomp &= mask] *)
      proc_priv γf p pid (us_secc U v0) -∗
      mWP (Loop : expr riscv_lang)) -∗
  mWP (Loop : expr riscv_lang).

Module Type SYSSECCOMP.
  Parameter wp_sys_seccomp_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (U : ustate) (v0 : mword 64) (b : bool) (lks : gset string),
      wp_sys_seccomp_sconf_body γf m av n eb p pid U v0 b lks.
End SYSSECCOMP.
