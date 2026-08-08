(* SpecSysPause.v -- the public interface of sys_pause(), stated
   independently of its proof.

     uint64 sys_pause(void) {
       int n; uint ticks0;
       argint(0, &n);
       if (n < 0) n = 0;
       acquire(&tickslock);
       ticks0 = ticks;
       while (ticks - ticks0 < n) {
         if (killed(myproc())) { release(&tickslock); return -1; }
         sleep(&ticks, &tickslock);
       }
       release(&tickslock);
       return 0;
     }

   @ KernelSyms.sys_pause = 0x800029b0, ~46 instructions.  The shape, from
   the image (the spec has to be honest about all of it):

     +0x00  64-byte frame; [n] is the 4-byte local at s0-52 = sp+12, i.e. the
            UPPER half of frame slot 7 -- argint writes into our own frame.
     +0x0e  argint(0, &n)
     +0x16  [blt a5,x0 -> +0x86]  the n < 0 fixup, which stores 0 and
            [c.j]s BACK to +0x1a -- so the acquire is reached by two paths.
     +0x22  acquire(&tickslock)
     +0x2a  [c.beqz a5 -> +0x70]  n == 0 skips the loop entirely
     +0x2c  s1/s2/s3 are saved HERE, i.e. only on the loop path, and
            restored at +0x6a / +0x9a -- the n == 0 path never touches them.
     +0x4a  the loop: myproc(); killed(); [c.bnez -> +0x8c] the killed exit;
            sleep(&ticks,&tickslock); [bltu -> +0x4a]
     +0x70  release; return 0        +0x8c  release; return -1

   THE CONTRACT.  Three groups of resources, and the interesting thing is
   that they are exactly the union of the callees' -- sys_pause adds no
   invariant of its own:

     - argint's: a read fraction of [p->trapframe] and the whole
       [tf_page]; the destination cell is carved out of our OWN frame, so it
       does not appear here.
     - tickslock's: [is_tickslock] + its free cpu word.  The tick counter
       itself is inside the lock's resource ([TicksInv.ticks_res]), which is
       why the loop's [c.lw a5,0(s1)] is legal.
     - the running-thread bundle sleep needs: [procs_inv], [own_ctx],
       the ▷-guarded parked scheduler, and [panic_wp].

   NOT here: [trap_csrs_pay].  sleep is not push/pop-balanced and does want
   the level-0 pay, but sys_pause's OWN acquire(&tickslock) is what produces
   it (acquire's post) and its release is what consumes it -- sys_pause as a
   whole IS balanced, so it must not also ask the caller for one.  Asking
   would be worse than redundant: [trap_csrs] is exclusive register
   ownership, so a second copy makes the eb = true precondition
   unsatisfiable and the spec vacuous exactly where interrupts are on.

   [killed(myproc())] needs nothing extra: it reads [p_killed] off the
   always-resident row of THIS process's own [proc_lock_res], reached
   through [procs_inv].

   The result is 0 or -1 and the caller cannot predict which (whether some
   other core sets [p->killed] is not determined by anything here), so it is
   existentially quantified with that two-way constraint -- the same honesty
   as sys_uptime's tick reading. *)
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
Require Import FdSlots FileInv ProcInv.
Require Import SwtchCtx SchedCtx.
Require Import ProcPtOwn.
Require Import TicksInv.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_sys_pause_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
    (γt : gname) (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
    (dqt : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_pause in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* argint reads argument 0 *)
  (i = 0)%nat ->
  ws !! tf_arg_idx i = Some v ->
  (* 8 slots for this frame, 18 for argint's, 22 for sleep's *)
  (30 <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol): the saved base enable
     is [true].  Everything below sleeps, and a parking thread must hand the
     trap CSRs across the crossing -- at level 0 with an enabled base the
     pushing acquire produces exactly that set.  See SpecSched.v. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* entered with no lock held *)
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* argint's trapframe resources *)
  p_trapframe pj ↦₈{dqt} page_base tfp -∗
  tf_page tfp ws -∗
  (* the tick lock.  Its cpu word is INSIDE lock_inv since main's lock
     rework, so nothing about it rides here. *)
  is_tickslock γt -∗
  (* the running-thread bundle killed() and sleep() need *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  panic_wp_any -∗
  park_hlf j true -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : mword 64),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = r /\
        (r = (zero_reg : mword 64) \/ r = mword_of_int (-1)) ⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      p_trapframe pj ↦₈{dqt} page_base tfp -∗
      tf_page tfp ws -∗
      park_hlf j true -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SYSPAUSE.
  Parameter wp_sys_pause_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (γt : gname) (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
      (dqt : dfrac) (b : bool),
      wp_sys_pause_sconf_body Φ γs j γl γt m av eb C i tfp ws v dqt b.
End SYSPAUSE.
