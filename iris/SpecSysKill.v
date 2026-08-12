(* SpecSysKill.v -- the public interface of sys_kill(), stated independently
   of its proof.

     uint64 sys_kill(void) {
       int pid;
       argint(0, &pid);
       return kkill(pid);
     }

   @ KernelSyms.sys_kill = 0x80002a52, thirteen instructions: a 32-byte
   ra/s0 frame whose slots 3/4 are the local area, [int pid] at s0-20 =
   sp+12 -- the UPPER half of frame slot 3, the same shape sys_close's [fd]
   has -- then argint(0,&pid), [lw a0,-20(s0)] and a tail call to kkill.

   THE CONTRACT IS EXACTLY THE UNION OF ITS TWO CALLEES', with nothing of
   its own: argint's trapframe resources (a read fraction of [p->trapframe]
   plus the whole [tf_page], and the pure fact naming which word argument 0
   is), and kkill's [procs_inv] + [panic_wp] + the [length γs = NPROC] the
   scan's bound needs.  The destination cell is carved out of sys_kill's own
   frame, so it does not appear here.

   Note what the code does NOT do: this xv6's argint returns void, and
   sys_kill does not check anything -- whatever byte pattern the trapframe
   holds becomes the pid it looks for.  So the result is kkill's verbatim,
   0 or -1, and nothing here relates it to [v]: which slot (if any) carries
   that pid is not determined by any resource the caller holds.  See
   SpecKkill.v. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
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
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import ProcPtOwn.
Require Import SchedCtx.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_sys_kill_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
     (γs : list gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (tfp : mword 44) (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_kill in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  length γs = NPROC ->
  (* argint reads argument 0 *)
  ws !! tf_arg_idx 0 = Some v ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 18 for argint's, 16 for kkill's *)
  (22 <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* argint's trapframe resources *)
  p_trapframe p ↦₈{dqt} page_base tfp -∗
  tf_page tfp ws -∗
  (* kkill's *)
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (rv : mword 64),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = rv /\
        (rv = (zero_reg : mword 64) \/ rv = mword_of_int (-1)) ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b -∗
      pc_is ret_tgt -∗
      p_trapframe p ↦₈{dqt} page_base tfp -∗
      tf_page tfp ws -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSKILL.
  Parameter wp_sys_kill_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
       (γs : list gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (tfp : mword 44) (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool),
      wp_sys_kill_sconf_body γs m av n eb p C tfp ws v dqt b.
End SYSKILL.
