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

   The lock invariant that consumes [proc_dormant] / [inv_dormant] lives in
   SchedCtx.v, since it also mentions [proc_ctx]: [proc_pub] (the
   always-resident killed/xstate/pid-half row) + [proc_slots] (the two flat
   guards) + [proc_lock_res].  This file stays below it and mentions neither.

   Also here: [tf_args], the syscall-argument slice of the trapframe PAGE
   that [p_trapframe]'s pointer names -- what argraw() reads. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import FdSlots FileInv.
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

  Context `{!lockG Σ, !fileG Σ, !fdslotG Σ}.

  (* A LIVE fd slot: the cell, and -- when non-null -- an actual reference on
     the [struct file] it points at.  [file_ref] is deliberately neither
     persistent nor duplicable: duplicating an fd IS filedup, which must bump
     the physical count under ftable.lock.  Naming the file by its ftable slot
     index [k] with [v = fnode k] is what bridges FileInv's index-keyed
     algebra to the pointer actually stored in memory. *)
  (* Either way the slot owns ONE unit of fd-slot capability (FdSlots.v),
     and the disjunction is where it currently is: an EMPTY descriptor holds
     the unit itself; a descriptor naming a file has given it away, and the
     ftable holds it against that file's count.  That conservation is what
     bounds any file's [ref] by FDSLOTS, hence what makes filedup's unchecked
     [f->ref++] safe -- so this predicate is the proc-side end of the law
     whose file-side end is [FileInv.fslot]. *)
  Definition ofile_slot (γf : gname) (pa : mword 64) (fd : nat) (v : mword 64) : iProp Σ :=
    (p_ofile pa fd ↦₈ v ∗
     (⌜v = (zero_reg : mword 64)⌝ ∗ fd_slot ∨
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

  (* The read-only pid fraction: what [myproc()->pid] reads.

     This is also exactly what SpecAcquiresleep / SpecHoldingsleep already
     consume.  Those specs take [p_pid pj ↦₄{dq} pidv] at a UNIVERSALLY
     QUANTIFIED [dq], so they compose with [proc_priv] unchanged, at
     [dq := DfracOwn (1/4)] -- and they should STAY that way.  Threading the
     whole [proc_priv] through them instead would drag [fileG]/[γf] into the
     sleeplock layer purely to read a pid; the bare fraction is both the
     weaker premise and the honest one. *)
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

  (* The read-only trapframe-POINTER fraction: what [p->trapframe->aN] reads
     first.  Same discipline as [proc_priv_pid] and for the same reason --
     argraw should take the weakest premise (a bare fraction of one cell),
     not the whole [proc_priv] with its [fileG]/[γf] baggage. *)
  (* a 1/4 read-share of a full word cell, in proofmode form: a goal-level
     [rewrite] would hit every [DfracOwn 1] cell of [proc_fields] at once. *)
  Local Lemma word_frac14 (a w : mword 64) :
    a ↦₈ w ⊣⊢ a ↦₈{DfracOwn (1/4)} w ∗ a ↦₈{DfracOwn (3/4)} w.
  Proof.
    assert (Hq : DfracOwn 1 = DfracOwn (1/4 + 3/4)) by (f_equal; compute_done).
    rewrite {1}Hq. apply word_pointsto_frac_split.
  Qed.

  Local Lemma word_split14 (a w : mword 64) :
    a ↦₈ w -∗ a ↦₈{DfracOwn (1/4)} w ∗ a ↦₈{DfracOwn (3/4)} w.
  Proof. rewrite word_frac14. iIntros "$". Qed.

  Local Lemma word_join14 (a w : mword 64) :
    a ↦₈{DfracOwn (1/4)} w -∗ a ↦₈{DfracOwn (3/4)} w -∗ a ↦₈ w.
  Proof. rewrite word_frac14. iIntros "H1 H2". iFrame. Qed.

  Lemma proc_priv_trapframe (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_trapframe pa ↦₈{DfracOwn (1/4)} pv_trapframe V ∗
    (p_trapframe pa ↦₈{DfracOwn (1/4)} pv_trapframe V -∗ proc_priv γf pa pid V).
  Proof.
    iIntros "(Hpid & (Hsz & Hpt & Htf & Hcwd & Hnl & Hnm) & Ho & Hc)".
    iDestruct (word_split14 with "Htf") as "[Hq1 Hq2]".
    iSplitL "Hq1"; [iExact "Hq1"|].
    iIntros "Hq1". rewrite /proc_priv /proc_fields.
    iDestruct (word_join14 with "Hq1 Hq2") as "Htf". iFrame.
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
  (* The trapframe page's syscall-argument slice.                        *)
  (* =================================================================== *)
  (* [p_trapframe] owns only the POINTER; the 35-word page it points at is a
     separate resource, keyed by that pointer's value.  Only the six
     argument registers are modelled here -- a0..a5 at 112..152, exactly the
     ones argraw() reads.  The rest of the page (epc, kernel_sp,
     kernel_satp, the saved user callee-saved registers) is untouched by the
     syscall-argument path and stays unmodelled; see the "holes" section of
     claude-notes/design/proc-struct.md.

     Deliberately NOT folded into [proc_priv]: the page's ownership crosses
     to user mode through uservec/userret, and at ZOMBIE freeproc has
     already kfree'd it (so [proc_dormant] could not carry it).  Callers tie
     the two together with [pv_trapframe V = tf]. *)
  Definition NARG : nat := 6%nat.
  Definition arg_off (i : nat) : Z := 112 + 8 * Z.of_nat i.
  Definition a_tf_arg (tf : mword 64) (i : nat) : mword 64 :=
    add_vec tf (mword_of_int (arg_off i)).

  Definition tf_args (tf : mword 64) (dq : dfrac) (args : list (mword 64)) : iProp Σ :=
    (⌜length args = NARG⌝ ∗
     [∗ list] i ↦ v ∈ args, a_tf_arg tf i ↦₈{dq} v)%I.

  (* borrow one argument cell and put it back *)
  Lemma tf_args_lookup (tf : mword 64) (dq : dfrac) (args : list (mword 64))
      (i : nat) (v : mword 64) :
    args !! i = Some v ->
    tf_args tf dq args -∗
    a_tf_arg tf i ↦₈{dq} v ∗ (a_tf_arg tf i ↦₈{dq} v -∗ tf_args tf dq args).
  Proof.
    iIntros (Hi) "[%Hlen Hargs]".
    iDestruct (big_sepL_lookup_acc _ _ i v Hi with "Hargs") as "[$ Hback]".
    iIntros "Hcell". iSplit; [done|]. by iApply "Hback".
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
  (* [pid] is existential here rather than an index: the invariant's OWN half
     of the cell is always resident (SchedCtx's [proc_pub]), and two halves of
     the same points-to agree for free, so indexing would only duplicate a
     fact [word4_pointsto_agree] already gives.  Keeping [st] and [pid] both
     out makes [proc_slots] a function of the state alone, which is what makes
     [proc_slots_recast] hold in BOTH directions within a guard class. *)
  Definition proc_dormant (pa : mword 64) : iProp Σ :=
    (∃ (V : pprivate) (pid : mword 32),
       ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
        pv_cwd V = (zero_reg : mword 64)⌝ ∗
       p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
       proc_fields pa (DfracOwn 1) V ∗
       ofile_cells pa (pv_ofile V) ∗
       (* a dormant process still OWNS its NOFILE units -- every descriptor
          is null, so it holds all of them itself.  Parking them here rather
          than making allocproc conjure them is what keeps the supply
          conserved across the whole UNUSED -> live -> ZOMBIE cycle. *)
       ([∗ list] _ ∈ pv_ofile V, fd_slot) ∗
       own_ctx (p_context pa))%I.

  (* allocproc's move: the dormant block plus the invariant's own pid half is
     a full [proc_priv] (and a writable pid cell).  The null-ofile fact is
     exactly what discharges every [ofile_slot]'s left disjunct, with no
     [file_ref] to conjure from nowhere. *)
  Lemma proc_dormant_to_priv (γf : gname) (pa : mword 64) :
    proc_dormant pa -∗
    own_ctx (p_context pa) ∗
    ∃ (V : pprivate) (pid : mword 32),
      ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64)⌝ ∗
      p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
      proc_fields pa (DfracOwn 1) V ∗ proc_ofiles γf pa (pv_ofile V).
  Proof.
    iIntros "(%V & %pid & [%Hof %Hcwd] & Hpid & Hf & Ho & Hs & Hctx)".
    iFrame "Hctx". iExists V, pid. iSplit; [done|]. iFrame "Hpid Hf".
    rewrite /proc_ofiles /ofile_cells Hof length_replicate. iSplit; [done|].
    iAssert ([∗ list] fd ↦ v ∈ replicate NOFILE (zero_reg : mword 64),
               (p_ofile pa fd ↦₈ v ∗ fd_slot))%I with "[Ho Hs]" as "Ho".
    { rewrite big_sepL_sep. iFrame "Ho Hs". }
    iApply (big_sepL_impl with "Ho"). iIntros "!>" (fd v Hv) "[Hcell Hslot]".
    apply lookup_replicate in Hv as [-> _]. iFrame "Hcell". iLeft. by iFrame "Hslot".
  Qed.

  (* =================================================================== *)
  (* kstack: write-once at procinit, hence persistent.                    *)
  (* =================================================================== *)
  Definition is_kstack (pa : mword 64) (ks : mword 64) : iProp Σ :=
    p_kstack pa ↦₈□ ks.

  Global Instance is_kstack_persistent pa ks : Persistent (is_kstack pa ks).
  Proof. rewrite /is_kstack /word_pointsto /mem_pointsto. apply _. Qed.

End ProcInv.
