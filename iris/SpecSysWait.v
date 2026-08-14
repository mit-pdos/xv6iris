(* SpecSysWait.v -- the public interface of sys_wait(), stated independently
   of its proof.

     uint64 sys_wait(void) {
       uint64 p;
       argaddr(0, &p);
       return wait(p);
     }

   @ KernelSyms.sys_wait = 0x80002924, thirteen instructions / 34 bytes: a
   32-byte ra/s0 frame whose slot 3 is the [uint64 p] local at s0-24 =
   sp+8 -- a WHOLE slot, unlike sys_kill's [int pid], which is the upper
   half of one.

     +0x00  1101        c.addi     sp,sp,-32
     +0x02  ec06        c.sdsp     ra,24(sp)
     +0x04  e822        c.sdsp     s0,16(sp)
     +0x06  1000        c.addi4spn s0,sp,32
     +0x08  fe840593    addi       a1,s0,-24      a1 := &p
     +0x0c  4501        c.li       a0,0
     +0x0e  efdff0ef    jal        ra,argaddr
     +0x12  fe843503    ld         a0,-24(s0)     a0 := p
     +0x16  83dff0ef    jal        ra,kwait
     +0x1a  60e2        c.ldsp     ra,24(sp)
     +0x1c  6442        c.ldsp     s0,16(sp)
     +0x1e  6105        c.addi16sp sp,32
     +0x20  8082        c.ret

   THE CONTRACT IS THE UNION OF ITS TWO CALLEES', and kwait's dominates it:
   everything kwait asks for (wait_lock, the scheduler chain, the
   running-thread bundle, the kalloc environment, [eb = true]) is here
   verbatim, because sys_wait adds no resource of its own.  The destination
   cell is carved out of sys_wait's own frame, so it does not appear.

   THE ARGUMENT COMES OUT OF [proc_priv], NOT OUT OF A SEPARATE TRAPFRAME
   FRACTION.  argaddr's own contract takes the trapframe as a bare fraction
   (SpecArgraw.v) and sys_kill's contract therefore passes one; but kwait
   needs the whole private block, so here the fraction is SPLIT OUT of it
   ([ProcInv.proc_priv_tf]) for the duration of the call and put back.  The
   argument is then named the way sys_sbrk names its two: as a fact about
   the block's own trapframe record, [pv_tf V !! tf_arg_idx 0 = Some v0].

   WHAT IT SAYS ABOUT THE RESULT is kwait's verbatim -- SOME sign-extended
   [int] -- and for kwait's reason: nothing in the tree ties a pid to a
   slot.  [v0] does not appear in the postcondition either: it is the
   address the exit status is copied to, and copyout's failure arm returns
   -1 just as a missing child does, so no resource distinguishes them.

   THE PRIVATE BLOCK GOES IN AND COMES BACK AT AN EXTENDED DESCRIPTOR
   ([uptd_ext_sz]), which is kwait's copyout, unchanged: argaddr touches no
   user page. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import WaitInv.
Require Import PanicStub.
Require Import SpecProcinit.   (* [wait_lock_addr] *)
Require Import SpecKwait.      (* [K_kwait] -- the budget this one is built on *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* 4 slots for sys_wait's own frame, and below it the deeper of its two
   callees: kwait's 60 (argaddr's is 18). *)
Definition sys_wait_stack : nat := (4 + K_kwait)%nat.

Definition wp_sys_wait_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa γf γw : gname)  (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset string)
    (pid : mword 32) (V : pprivate) (v0 : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_wait in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the syscall argument, out of the trapframe page [proc_priv] carries *)
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  (sys_wait_stack <= av)%nat ->
  (* the PARKING premise, inherited from kwait: everything that sleeps has it *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  cpu_own 0%nat eb pj C b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
  kalloc_env γa None -∗
  proc_priv γf pj pid V -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (P' : uptd) (rv : mword 32),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 rv ⌝ -∗
      ⌜ uptd_ext_sz (pv_sz V) (pv_upt V) P' ⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSWAIT.
  Parameter wp_sys_wait_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa γf γw : gname) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset string)
      (pid : mword 32) (V : pprivate) (v0 : mword 64),
      wp_sys_wait_sconf_body γa γf γw γs j γl m av eb C b lks pid V v0.
End SYSWAIT.
