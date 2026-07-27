(* ProcInv.v -- the [struct proc] resources beyond the five fields the
   scheduler needed: the PRIVATE field block a running process owns without
   holding any lock, the open-file-descriptor array (each non-null slot
   holding a real [FileInv.file_ref]), and the DORMANT shape that block
   collapses to when nobody is running the process.

   The analysis this realises is in claude-notes/design/proc-struct.md; the
   short version:

   * [state]/[chan]/[killed]/[xstate] are lock-protected and mutable, so all
     four cells live unconditionally in the proc lock's resource (SchedCtx.v).
   * [pid] is lock-protected but immutable-while-allocated, and is read BOTH
     by other cores under p->lock (kill's scan) and unlocked by the owning
     process (sys_getpid, acquiresleep).  That is FileInv's discipline 2, and
     it takes the same answer: a points-to FRACTION, half resident in the lock
     resource, half travelling with the runner.  Agreement between the halves
     is [word4_pointsto_agree] -- no ghost algebra.
   * [sz]/[pagetable]/[trapframe]/[ofile]/[cwd]/[name] are written by the
     running process with NO lock held (sys_sbrk's [myproc()->sz += n],
     sys_chdir, fdalloc, exec).  So the invariant can retain no fraction of
     them: it must give the whole block away while the process is live and
     take it back when it is not.  [proc_priv] is the block; [proc_dormant]
     is what the invariant holds instead.
   * [kstack] is written once by procinit and never again: persistent.

   [proc_priv] is the resource that rides alongside [cur_proc p]
   (ProcGeom.v).  myproc() returns the [p] of [cur_proc p]; [proc_priv] is
   what makes [myproc()->pid] / [->sz] / [->cwd] / [->ofile[fd]] readable
   with no lock in hand.

   NOTE (staging): the rewired [proc_lock_res] that consumes [proc_dormant]
   and [inv_dormant] lives in SchedCtx.v, since it also mentions [proc_ctx];
   that swap is a separate change (it re-proves yield/sched/sleep/wakeup).
   Everything in THIS file is independent of it. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import FileInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The private field block's contents.                                    *)
(* ===================================================================== *)
(* [pid] is NOT a member: it is the one field of the group with a SPLIT
   discipline (half here, half permanently in the lock resource), and call
   sites want to name it directly.  [kstack] is not a member either: it is
   persistent (see [is_kstack] below), so it needs no threading. *)
Record pprivate := MkPPriv {
  pv_sz        : mword 64;
  pv_pagetable : mword 64;
  pv_trapframe : mword 64;
  pv_ofile     : list (mword 64);   (* length NOFILE *)
  pv_cwd       : mword 64;
  pv_name      : list (bv 8);       (* length PNAMELEN *)
}.

(* functional update of one fd slot -- fdalloc / sys_close / kexit. *)
Definition upd_ofile (V : pprivate) (fd : nat) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_pagetable V) (pv_trapframe V)
          (<[fd := v]> (pv_ofile V)) (pv_cwd V) (pv_name V).

Definition upd_sz (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv v (pv_pagetable V) (pv_trapframe V) (pv_ofile V) (pv_cwd V) (pv_name V).

Definition upd_cwd (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_pagetable V) (pv_trapframe V) (pv_ofile V) v (pv_name V).

Lemma upd_ofile_length (V : pprivate) (fd : nat) (v : mword 64) :
  length (pv_ofile (upd_ofile V fd v)) = length (pv_ofile V).
Proof. simpl. apply length_insert. Qed.

Section ProcInv.
  Context `{!riscvGS Σ}.

  (* =================================================================== *)
  (* The scalar private cells.                                           *)
  (* =================================================================== *)
  Definition pname_cells (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] i ↦ b ∈ bs, p_name pa i ↦ₘ{dq} b)%I.

  Definition proc_fields (pa : mword 64) (dq : dfrac) (V : pprivate) : iProp Σ :=
    (p_sz pa        ↦₈{dq} pv_sz V ∗
     p_pagetable pa ↦₈{dq} pv_pagetable V ∗
     p_trapframe pa ↦₈{dq} pv_trapframe V ∗
     p_cwd pa       ↦₈{dq} pv_cwd V ∗
     ⌜length (pv_name V) = PNAMELEN⌝ ∗
     pname_cells pa dq (pv_name V))%I.

  (* =================================================================== *)
  (* p->ofile[fd]: the cell, plus the reference it names.                *)
  (* =================================================================== *)
  (* Bare cells, no validity clause: what the DORMANT bundle holds (every
     slot is null there, so there is no reference to describe). *)
  Definition ofile_cells (pa : mword 64) (fs : list (mword 64)) : iProp Σ :=
    ([∗ list] fd ↦ v ∈ fs, p_ofile pa fd ↦₈ v)%I.

  Context `{!lockG Σ, !fileG Σ}.

  (* A LIVE fd slot: the cell, and -- when non-null -- an actual reference on
     the [struct file] it points at.  [file_ref] is deliberately neither
     persistent nor duplicable: duplicating an fd IS filedup, which must bump
     the physical count under ftable.lock.  Naming the file by its ftable slot
     index [k] with [v = fnode k] is what bridges FileInv's index-keyed
     algebra to the pointer actually stored in memory. *)
  Definition ofile_slot (γf : gname) (pa : mword 64) (fd : nat) (v : mword 64) : iProp Σ :=
    (p_ofile pa fd ↦₈ v ∗
     (⌜v = (zero_reg : mword 64)⌝ ∨
      ∃ (k : nat) (q : Qp) (C : fcontent),
        ⌜v = fnode k /\ (k < NFILE)%nat⌝ ∗ file_ref γf k q C))%I.

  Definition proc_ofiles (γf : gname) (pa : mword 64) (fs : list (mword 64)) : iProp Σ :=
    (⌜length fs = NOFILE⌝ ∗ [∗ list] fd ↦ v ∈ fs, ofile_slot γf pa fd v)%I.

  (* =================================================================== *)
  (* THE resource that rides alongside [cur_proc p].                      *)
  (* =================================================================== *)
  (* [cwd]: there is no inode model in the tree yet, so the "cwd names a
     live inode" clause is [emp] for now -- deliberately a hole with the
     shape of [ofile_slot]'s, so it can be filled without restating any
     caller.  See the "holes" section of design/proc-struct.md. *)
  Definition cwd_ref (v : mword 64) : iProp Σ := emp%I.

  Definition proc_priv (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) : iProp Σ :=
    (p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) V ∗
     proc_ofiles γf pa (pv_ofile V) ∗
     cwd_ref (pv_cwd V))%I.

  (* ---- projections: what callers actually use ---- *)

  (* The read-only pid fraction.  This is what [myproc()->pid] reads, and it
     RETIRES the ad-hoc [p_pid pj ↦₄{dq} pidv] premise/postcondition pair
     threaded through SpecAcquiresleep / SpecHoldingsleep / SpecSleep: those
     become this projection, and [dq] stops being a spec parameter. *)
  Lemma proc_priv_pid (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    (p_pid pa ↦₄{DfracOwn (1/4)} pid -∗ proc_priv γf pa pid V).
  Proof.
    iIntros "(Hpid & Hf & Ho & Hc)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iIntros "Hq1". rewrite /proc_priv Hq word4_pointsto_frac_split. iFrame.
  Qed.

  (* Borrow one fd slot and hand back a (possibly different) one. *)
  Lemma proc_priv_ofile (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    proc_priv γf pa pid V -∗
    ofile_slot γf pa fd v ∗
    (∀ v', ofile_slot γf pa fd v' -∗ proc_priv γf pa pid (upd_ofile V fd v')).
  Proof.
    iIntros (Hfd) "(Hpid & Hf & [%Hlen Ho] & Hc)".
    iDestruct (big_sepL_insert_acc with "Ho") as "[$ Hback]"; first exact Hfd.
    iIntros (v') "Hslot". iDestruct ("Hback" $! v' with "Hslot") as "Ho".
    rewrite /proc_priv /proc_ofiles /=. iFrame.
    iPureIntro. rewrite length_insert. exact Hlen.
  Qed.

  (* The whole point of the fractional pid: another core reading p->pid under
     p->lock agrees with what the running thread believes. *)
  Lemma proc_priv_pid_agree (γf : gname) (pa : mword 64) (pid pid' : mword 32)
      (V : pprivate) (dq : dfrac) :
    proc_priv γf pa pid V -∗ p_pid pa ↦₄{dq} pid' -∗ ⌜pid = pid'⌝.
  Proof.
    iIntros "(Hpid & _) Hother".
    iApply (word4_pointsto_agree with "Hpid Hother").
  Qed.

  (* =================================================================== *)
  (* The DORMANT shape: what the lock invariant holds at UNUSED/ZOMBIE.   *)
  (* =================================================================== *)
  (* kexit() nulls every ofile[fd] and sets cwd = 0 BEFORE the process goes
     ZOMBIE, and freeproc() only zeroes more.  So the dormant bundle never
     owes a file reference or an inode reference -- it is raw cells plus one
     fact, and [γf] does not appear.  It is deliberately NOT indexed by [st]:
     freeproc's other zeroing (pid/sz/pagetable/trapframe = 0) has no
     consumer (freeproc branches on [if (p->trapframe)] at runtime and
     allocproc overwrites without reading), and stating it would cost an
     obligation on every release AND break [proc_dormant]'s symmetry between
     UNUSED and ZOMBIE. *)
  Definition proc_dormant (pa : mword 64) (pid : mword 32) : iProp Σ :=
    (∃ V : pprivate,
       ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
        pv_cwd V = (zero_reg : mword 64)⌝ ∗
       p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
       proc_fields pa (DfracOwn 1) V ∗
       ofile_cells pa (pv_ofile V) ∗
       own_ctx (p_context pa))%I.

  (* allocproc's move: the dormant block plus the invariant's own pid half is
     a full [proc_priv] (and a writable pid cell).  The null-ofile fact is
     exactly what discharges every [ofile_slot]'s left disjunct, with no
     [file_ref] to conjure from nowhere. *)
  Lemma proc_dormant_to_priv (γf : gname) (pa : mword 64) (pid : mword 32) :
    proc_dormant pa pid -∗
    own_ctx (p_context pa) ∗
    p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
    ∃ V, ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64)⌝ ∗
         proc_fields pa (DfracOwn 1) V ∗ proc_ofiles γf pa (pv_ofile V).
  Proof.
    iIntros "(%V & [%Hof %Hcwd] & Hpid & Hf & Ho & Hctx)".
    iFrame "Hctx Hpid". iExists V. iSplit; [done|]. iFrame "Hf".
    rewrite /proc_ofiles /ofile_cells Hof length_replicate. iSplit; [done|].
    iApply (big_sepL_impl with "Ho"). iIntros "!>" (fd v Hv) "Hcell".
    apply lookup_replicate in Hv as [-> _]. iFrame "Hcell". by iLeft.
  Qed.

  (* =================================================================== *)
  (* kstack: write-once at procinit, hence persistent.                    *)
  (* =================================================================== *)
  Definition is_kstack (pa : mword 64) (ks : mword 64) : iProp Σ :=
    p_kstack pa ↦₈□ ks.

  Global Instance is_kstack_persistent pa ks : Persistent (is_kstack pa ks).
  Proof. rewrite /is_kstack /word_pointsto /mem_pointsto. apply _. Qed.

End ProcInv.
