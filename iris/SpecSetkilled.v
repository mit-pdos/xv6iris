(* SpecSetkilled.v -- the public interface of setkilled(), stated
   independently of its proof.

     void setkilled(struct proc *p) {
       acquire(&p->lock);
       p->killed = 1;
       release(&p->lock);
     }

   @ KernelSyms.setkilled = 0x8000211e, sixteen instructions: a 32-byte
   ra/s0/s1 frame (slot 0 is padding), [c.mv s1,a0] to park [p] across the
   two calls, acquire, [c.li a5,1] + [c.sw a5,40(s1)] (p->killed = 1),
   [c.mv a0,s1], release.

   THE POINT, and the reason the postcondition is EMPTY.  [p_killed] lives
   in [SchedCtx.proc_pub], at the TOP LEVEL of [proc_lock_res] -- but
   [proc_pub] quantifies the flag EXISTENTIALLY, so the invariant says
   nothing about its value and there is nothing for a caller to learn.
   setkilled is therefore the mirror image of killed(): killed() reads a
   value the contract cannot constrain, setkilled writes one the contract
   need not report.  Both reach the cell by opening the lock and destructing
   one existential, and neither ever learns the process's state or touches
   either [proc_slots] guard -- which is exactly what the invariant's
   always-resident row is for.

   (The postcondition is not quite empty any more: the caller's quarter of
   [p->pid] is LENT to the call and handed back.  It says nothing about the
   write -- it is what shows the slot being written is LIVE; see the
   premise's note, lane SELF-KILL 4b'.)

   Making the write visible would mean giving [p->killed] a fraction that
   travels with the running thread (the [pid] discipline), and no consumer
   wants one: the only reader is killed(), which any hart may call on any
   proc.  See claude-notes/design/proc-struct.md, discipline 1.

   The panic credentials are threaded because acquire takes them (its
   "acquire" panic on a doubly-held lock). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.program_logic Require Import language lifting.
From transfinite.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import SchedCtx.
Require Import SlotGen.   (* [pid_reg] / [qeighth] -- the registration eighth
                             that names the target's incarnation; [ProcInv]
                             does not re-export it *)
Require Import ChildTok.  (* [kill_owed] / [kill_shot] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.


Definition wp_setkilled_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
     (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string)
    (pidv : mword 32) (gn : gname) (self : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.setkilled in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the argument is proc j *)
  m !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 10 for acquire's / release's *)
  (14 <= av)%nat ->
  (* THE TARGET IS A LIVE PROCESS (lane SELF-KILL, 4b').  See the resource
     premise below for why the write needs it.  BEFORE the order premise,
     which every caller leaves to its [lkbelow]. *)
  bv_unsigned pidv <> 0 ->
  (* THE ORDER PREMISE for the one lock this function takes: everything the
     caller already holds ranks strictly BELOW "proc".  It composes across a
     call chain in a way the bare non-membership does not
     ([LockRank.locks_below_mono]), and [locks_below_not_elem] recovers the
     ["proc" ∉ lks] the ghost step and the set algebra below need.
     No execution ever holds two "proc" locks at once (LockRank.v), so a
     caller inside some OTHER proc's critical section is not a problem here.
     setkilled is BALANCED -- both the entry and the exit [cpu_own] carry the
     same [lks] -- because the C releases p->lock on its only return path. *)
  locks_below lks "proc" ->
  (* THE PRICE OF THE KILL, AND IT IS TWO-SIDED (lane SELF-KILL, P6b).
     Writing [p->killed] nonzero costs the TARGET's exit payload at -1:
     [SchedCtx.kill_row] is "the flag is zero OR it has been paid", and
     this function is one of the two writers, so it cannot re-bundle the
     lock's payload without paying.  There are two ways to pay, and they
     are different parties':
       * the LEFT is the application's TAINT, which buys the target's
         payload through the row's published wand -- what a THIRD-PARTY
         killer uses ([SpecKkill], [SpecSysKill], which keep it);
       * the RIGHT is the payload ITSELF, deposited by the process that is
         about to be killed ([ChildTok.kill_owed]) -- setkilled's only
         caller is usertrap's fault arm on [myproc()], so a process that
         faults ON PURPOSE pays for its own death with no taint at all.
     Keyed at the target's generation, which is what the registration
     eighth below names. *)
  (* ...AND THE RIGHT SIDE BRINGS THE INCARNATION'S MARKER (design/pipe.md,
     "The exit path"): a self-kill closes every descriptor the process
     holds, which its own trap deposit pays, so the row it founds is the
     SPENT one -- marker in, payload kept (it comes back below, for the
     kexit two critical sections later).  The taint's side founds the paid
     arm as any third-party killer does. *)
  (* KEYED on which party pays ([self]), so the post can say which side it
     hands back: the owed side's payload is the only thing that can build
     kexit's payment for a self-kill, since its marker is now in the row. *)
  (if self then ChildTok.kill_owed gn ∗ ChildTok.taken_at gn
   else app_taint) -∗
  (* ...AND THE CALLER'S REGISTRATION EIGHTH, LENT (lane SELF-KILL, P6b):
     what says the [gn] the payment is keyed at IS the generation
     <p->lock>'s row is at ([SlotGen.pid_reg_agree]).  usertrap's fault arm
     holds it off the process's own block
     ([ProcInv.proc_priv_pid_reg]). *)
  pid_reg pidv (DfracOwn qeighth) gn -∗
  (* THE CALLER'S OWN QUARTER OF [p->pid], LENT (lane SELF-KILL, 4b').
     [SchedCtx.kill_paid] has a FREE arm at [p->pid = 0] which claims the
     flag is zero -- an invariant only because the C's writers cannot reach
     a free slot ([kkill] refuses pid 0, XV6_REV 64c58ba) -- so a writer
     that stores 1 must show the slot it re-closes is on the LIVE arm.
     [kkill] shows it from its own [beq] against a nonzero argument;
     setkilled writes unconditionally, and its ONE caller is usertrap's
     fault arm on [myproc()], which holds the process's block and reads
     the fact off it ([ProcInv.proc_priv_pid_nz], founded on the
     registration the block carries).  The quarter is what ties that pid to
     the one <p->lock>'s payload names ([ctx_word4_pointsto_agree]); it is
     LENT, and comes back in the postcondition. *)
  p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      (* the lent quarter, back *)
      p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
      (* ...and the lent registration eighth *)
      pid_reg pidv (DfracOwn qeighth) gn -∗
      (* ...AND THE ONE-SHOT, FIRED (lane SELF-KILL, P6b).  The write is
         what makes the flag monotone for this incarnation, and this is its
         ghost image: [ChildTok.kill_shot gn] is persistent and says the
         flag will never read zero again, which is what refutes the
         not-killed branch of the killed() check this arm walks into. *)
      ChildTok.kill_shot gn -∗
      (* ...AND THE SIDE THE WRITE DID NOT SPEND: the taint back (it is
         persistent), or the process's own death payload, which the fault
         arm hands its kexit directly ([SpecKexit]'s left side at -1) *)
      (if self then ChildTok.kill_owed gn else app_taint) -∗
      mWP (Loop : expr riscv_lang)) -∗
  mWP (Loop : expr riscv_lang).

Module Type SETKILLED.
  Parameter wp_setkilled_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
       (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string)
      (pidv : mword 32) (gn : gname) (self : bool),
      wp_setkilled_sconf_body γs j γl m av n eb p b lks pidv gn self.
End SETKILLED.
