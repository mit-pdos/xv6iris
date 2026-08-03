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

   Also here: [tf_page], the whole trapframe PAGE that [p_trapframe]'s
   pointer names -- all 36 [struct trapframe] words with their values plus
   the 3808-byte tail.  It is here rather than in ProcPtOwn because the
   syscall path needs the VALUE of [tf->aN], which a contents-existential
   page cannot supply. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto.
Require Import ProcGeom.
Require Import UserPtTree ProcPtOwn.
Require Import SwtchCtx.
Require Import WpLock.
Require Import FdSlots FileInv.
Require Import KallocInv PageFields ByteBuf.
From Kernel Require KernelSyms.
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The private field block's contents.                                    *)
(* ===================================================================== *)
(* [pid] is NOT a member: it is the one field of the group with a SPLIT
   discipline (half here, half permanently in the lock resource), and call
   sites want to name it directly.  [kstack] is not a member either: it is
   persistent (see [is_kstack] below), so it needs no threading. *)
(* [pagetable] and [trapframe] are NOT value fields: [ProcPtOwn.proc_pt_at]
   owns both cells and pins them to [page_base (ud_root …)] / [page_base
   (ud_tfp …)], so a separate value here could only be dead weight or
   disagree.  The descriptor [pv_upt] determines both. *)
Record pprivate := MkPPriv {
  pv_sz    : mword 64;
  pv_upt   : uptd;                (* the user page table AND trapframe ppn *)
  pv_tf    : list (mword 64);     (* the trapframe's 36 words, length TFWORDS *)
  pv_ofile : list (mword 64);     (* length NOFILE *)
  pv_cwd   : mword 64;
  pv_name  : list (bv 8);         (* length PNAMELEN *)
}.

(* functional update of one fd slot -- fdalloc / sys_close / kexit. *)
Definition upd_ofile (V : pprivate) (fd : nat) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (<[fd := v]> (pv_ofile V)) (pv_cwd V) (pv_name V).

Definition upd_sz (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv v (pv_upt V) (pv_tf V) (pv_ofile V) (pv_cwd V) (pv_name V).

(* the descriptor moves, everything else stays -- what copyin / copyout /
   vmfault do to a process when they fault a page in ([uptd_ext], below). *)
Definition upd_upt (V : pprivate) (P : uptd) : pprivate :=
  MkPPriv (pv_sz V) P (pv_tf V) (pv_ofile V) (pv_cwd V) (pv_name V).

Definition upd_cwd (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (pv_ofile V) v (pv_name V).

(* a process GAINS its address space: the descriptor and the trapframe words
   move, the scalar fields stay.  allocproc's move, once kalloc has produced
   the trapframe page and proc_pagetable the table. *)
Definition upd_pt (V : pprivate) (P : uptd) (ws : list (mword 64)) : pprivate :=
  MkPPriv (pv_sz V) P ws (pv_ofile V) (pv_cwd V) (pv_name V).

(* writing back what was already there is a no-op -- what a caller that only
   READS a descriptor (argfd) needs to close [proc_priv_ofile]'s accessor
   without its [V] drifting. *)
Lemma upd_ofile_id (V : pprivate) (fd : nat) (v : mword 64) :
  pv_ofile V !! fd = Some v -> upd_ofile V fd v = V.
Proof.
  intro Hlk. unfold upd_ofile. rewrite (list_insert_id _ _ _ Hlk).
  by destruct V.
Qed.

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

  (* the SCALAR private cells.  pagetable and trapframe are absent: those two
     cells belong to [ProcPtOwn.proc_pt_at], which rides beside this in
     [proc_priv]. *)
  Definition proc_fields (pa : mword 64) (dq : dfrac) (V : pprivate) : iProp Σ :=
    (p_sz pa        ↦₈{dq} pv_sz V ∗
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

  (* ---- the two ends of "filling a descriptor", as accessors ----
     An EMPTY descriptor owns the fd-slot unit itself, so opening one YIELDS
     that unit; installing a file consumes a reference and gives the slot
     back.  Both directions are what fdalloc's install arm is made of, and in
     the null direction the file disjunct is REFUTED rather than assumed --
     a [struct file *] out of the global table is never NULL
     ([FileInv.fnode_ne_zero]). *)
  Lemma ofile_slot_null (γf : gname) (pa : mword 64) (fd : nat) :
    ofile_slot γf pa fd (zero_reg : mword 64) -∗
    p_ofile pa fd ↦₈ (zero_reg : mword 64) ∗ fd_slot.
  Proof.
    iIntros "[$ [[_ $] | (%k & %q & %C & [%Hfn %Hk] & _)]]".
    exfalso. apply (fnode_ne_zero k Hk). symmetry. exact Hfn.
  Qed.

  Lemma ofile_slot_file (γf : gname) (pa : mword 64) (fd k : nat) (q : Qp) (C : fcontent) :
    (k < NFILE)%nat ->
    p_ofile pa fd ↦₈ fnode k -∗ file_ref γf k q C -∗ ofile_slot γf pa fd (fnode k).
  Proof.
    iIntros (Hk) "Hc Href". iFrame "Hc". iRight.
    iExists k, q, C. iFrame "Href". iPureIntro. split; [reflexivity | exact Hk].
  Qed.

  Definition proc_ofiles (γf : gname) (pa : mword 64) (fs : list (mword 64)) : iProp Σ :=
    (⌜length fs = NOFILE⌝ ∗ [∗ list] fd ↦ v ∈ fs, ofile_slot γf pa fd v)%I.

  (* =================================================================== *)
  (* The trapframe PAGE.                                                  *)
  (* =================================================================== *)
  (* These 4096 bytes are owned HERE, not in [ProcPtOwn] as a
     contents-EXISTENTIAL [phys_page_own]: that shape cannot serve the
     syscall path, which needs the VALUE of [tf->aN].

     Covering the WHOLE page, not just the argument slots: the 36
     [struct trapframe] words carry values, and the 3808 bytes of tail
     padding are owned anonymously.  Anything less would leave part of a
     kalloc'd page unaccounted for, and [freeproc]'s [kfree] needs the
     whole page back.

     Stated at the PHYSICAL tier, indexed by the ppn: that is the tier
     kalloc hands out, and it is
     tier-neutral (no va inside), which matters because this page is
     reached from BOTH sides -- the kernel's identity map (argraw's
     [ld a0,112(a5)]) and the user table's TRAPFRAME va (uservec /
     userret).  Each access site converts with
     [RiscvPtsto.phys_to_mem_claim] / [mem_to_phys_claim], the same idiom
     the software page-table walks already use for PT slots. *)
  Definition a_tf_word (tfp : mword 44) (i : nat) : Arch.pa :=
    pa_add (page_base tfp) (8 * i).

  Definition tf_words (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    ([∗ list] i ↦ w ∈ ws, a_tf_word tfp i ↦₈ w)%I.

  (* the page beyond the struct: 288 .. 4095, contents irrelevant *)
  Definition tf_tail (tfp : mword 44) : iProp Σ :=
    ([∗ list] j ∈ seq (Z.to_nat TFBYTES) (4096 - Z.to_nat TFBYTES),
       ∃ b : bv 8, pa_add (page_base tfp) j ↦ₘ b)%I.

  Definition tf_page (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    (⌜length ws = TFWORDS⌝ ∗ tf_words tfp ws ∗ tf_tail tfp)%I.

  Typeclasses Opaque tf_words tf_tail tf_page.

  (* CONSTRUCTION: what [kalloc] hands allocproc IS a trapframe page.  The 36
     struct words come out with EXISTENTIAL contents (a fresh page's bytes are
     arbitrary), and the 3808-byte tail is exactly the window [tf_tail] owns
     anonymously.  This is the one crossing the header above anticipates. *)
  Lemma tf_page_of_page_own (tfp : mword 44) :
    page_valid (page_base tfp) ->
    page_own (page_base tfp) ⊢ ∃ ws : list (mword 64), tf_page tfp ws.
  Proof.
    intro Hpv. rewrite /page_own.
    replace 4096%nat with (8 * TFWORDS + 3808)%nat by (vm_compute; reflexivity).
    rewrite (bwin_split (page_base tfp) 0 (8 * TFWORDS) 3808).
    iIntros "[Hpre Htail]".
    iDestruct (page_words8 (page_base tfp) TFWORDS Hpv ltac:(vm_compute; lia)
                 with "Hpre") as (ws) "[%Hlen Hws]".
    iExists ws. rewrite /tf_page /tf_words /tf_tail /a_tf_word.
    iSplit; [done|]. iFrame "Hws".
    rewrite Nat.add_0_l.
    replace (Z.to_nat TFBYTES) with (8 * TFWORDS)%nat by (vm_compute; reflexivity).
    replace (4096 - Z.to_nat TFBYTES)%nat with 3808%nat by (vm_compute; reflexivity).
    rewrite /byte_any. iExact "Htail".
  Qed.

  (* borrow one trapframe word -- the nth syscall argument is [tf_arg_idx n] *)
  Lemma tf_page_word (tfp : mword 44) (ws : list (mword 64)) (i : nat) (w : mword 64) :
    ws !! i = Some w ->
    tf_page tfp ws -∗
    a_tf_word tfp i ↦₈ w ∗ (a_tf_word tfp i ↦₈ w -∗ tf_page tfp ws).
  Proof.
    rewrite /tf_page. iIntros (Hi) "(%Hlen & Hws & Htail)".
    iDestruct (big_sepL_lookup_acc _ _ i w Hi with "Hws") as "[$ Hback]".
    iIntros "Hc". iSplit; [done|]. iSplitL "Hc Hback"; [rewrite /tf_words; iApply ("Hback" with "Hc") | iExact "Htail"].
  Qed.

  (* STATED AT THE VA TIER.  Every kernel reader of this page -- argraw's
     [ld a0,112(a5)], syscall.c's [p->trapframe->a0 = ...], usertrap's
     [p->trapframe->epc] -- is an ordinary load/store through the identity
     map, so putting the page at the VA tier costs those sites nothing.  The
     ONE crossing that remains is at construction: allocproc gets physical
     bytes from kalloc and converts once (ProcPtOwn.phys_to_page_own is the
     page-level lemma for exactly that), and the trampoline side converts
     back with [RiscvPtsto.mem_to_phys_claim].  The alternative -- a physical
     [tf_page] with a per-read crossing -- needs [kmap_static_claims] at every
     reader, and that bundle is only reachable by opening [hw_config] inside
     a LEAF, so no whole-function caller can supply it. *)

  (* =================================================================== *)
  (* THE resource that rides alongside [cur_proc p].                      *)
  (* =================================================================== *)
  (* [cwd]: there is no inode model in the tree yet, so the "cwd names a
     live inode" clause is [emp] for now -- deliberately a hole with the
     shape of [ofile_slot]'s, so it can be filled without restating any
     caller.  See the "holes" section of design/proc-struct.md. *)
  Definition cwd_ref (v : mword 64) : iProp Σ := emp%I.

  (* [p->sz] NEVER EXCEEDS MAXVA.  This is a real invariant of a live
     process -- exec and growproc are the only writers and both bound the
     size -- and it belongs HERE rather than in each consumer's precondition:
     vmfault / copyin / copyout sit BELOW the [proc_priv] altitude (they take
     the bare [p_sz] cell, not the block) and must keep taking it as a
     premise, but every caller AT this altitude holds nothing but
     [proc_priv], so a premise there would be one no caller could discharge.
     [proc_priv_sz_bound] is how such a caller pays it. *)
  (* [p->sz] BOUNDS THE MAP, and both facts are conjuncts of the block.
     The size never exceeds TRAPFRAME ([uvm_maxsz]) -- growproc's own
     [sz + n > TRAPFRAME] check and exec's are the only things that raise it
     -- and NOTHING IS MAPPED AT OR ABOVE IT ([ProcPtOwn.um_below]).  The
     second is what growproc pays uvmalloc's freshness premise out of: the
     run [PGROUNDUP(sz) .. sz+n) is fresh in [ud_um] exactly because the
     invariant says so, and no caller of growproc could have supplied it.
     Neither can be a premise of a consumer for the reason in the header:
     everything at this altitude holds nothing but [proc_priv].  It is why
     copyin / copyout hand back [uptd_ext_sz], not [uptd_ext] -- see
     [proc_priv_copy]. *)
  Definition proc_priv (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) : iProp Σ :=
    (⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
     ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
     p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) V ∗
     proc_pt_at pa (pv_upt V) ∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
     proc_ofiles γf pa (pv_ofile V) ∗
     cwd_ref (pv_cwd V))%I.

  (* BUILDING one: allocproc is the only producer, and this is exactly its
     move -- the scalar cells and the descriptor array come out of the
     dormant block, the page table and the trapframe page it just built.
     The [p->sz] bound travels with the dormant block (which is where the
     invariant keeps it); everything else is a straight repackaging.
       The coherence conjunct is the caller's, and it costs allocproc
     nothing: the table it just built has an EMPTY user map, and
     [ProcPtOwn.um_below_empty] holds at any size. *)
  Lemma proc_priv_intro (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (P : uptd) (ws : list (mword 64)) :
    (uint (pv_sz V) <= uvm_maxsz)%Z ->
    um_below (pv_sz V) (ud_um P) ->
    p_pid pa ↦₄{DfracOwn (1/2)} pid -∗
    proc_fields pa (DfracOwn 1) V -∗
    proc_pt_at pa P -∗
    tf_page (ud_tfp P) ws -∗
    proc_ofiles γf pa (pv_ofile V) -∗
    proc_priv γf pa pid (upd_pt V P ws).
  Proof.
    iIntros (Hsz Hbel) "Hpid Hf Hpt Htf Ho".
    rewrite /proc_priv /cwd_ref.
    cbn [upd_pt pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR; [iPureIntro; exact Hsz|].
    iSplitR; [iPureIntro; exact Hbel|]. iFrame "Hpid Hf Hpt Htf Ho".
  Qed.

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
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho & Hc)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iIntros "Hq1". rewrite /proc_priv Hq word4_pointsto_frac_split.
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
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
    p_trapframe pa ↦₈{DfracOwn (1/4)} page_base (ud_tfp (pv_upt V)) ∗
    (p_trapframe pa ↦₈{DfracOwn (1/4)} page_base (ud_tfp (pv_upt V)) -∗
       proc_priv γf pa pid V).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho & Hc)".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iDestruct (word_split14 with "Htfc") as "[Hq1 Hq2]".
    iSplitL "Hq1"; [iExact "Hq1"|].
    iIntros "Hq1". rewrite /proc_priv /proc_pt_at.
    iDestruct (word_join14 with "Hq1 Hq2") as "Htfc".
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* The array's length, which a caller needs BEFORE it knows which
     descriptor it wants: an fd below NOFILE always has a slot to look up. *)
  Lemma proc_priv_ofile_len (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜length (pv_ofile V) = NOFILE⌝.
  Proof. iIntros "(_ & _ & _ & _ & _ & _ & [%Hlen _] & _)". done. Qed.

  (* The TRAPFRAME bound on [p->sz] -- what the uvm* layer asks of a size
     argument, and what growproc must re-establish when it writes one. *)
  Lemma proc_priv_sz_maxsz (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜uint (pv_sz V) <= uvm_maxsz⌝.
  Proof. iIntros "(%Hszb & _)". done. Qed.

  (* The MAXVA bound on [p->sz], for a caller that must hand it to vmfault /
     copyin / copyout.  Pure conclusion, so [iDestruct ... as %H] keeps the
     block.  A weakening of the above -- those three sit below this altitude
     and were written against MAXVA, and nothing is gained by tightening
     their premise. *)
  Lemma proc_priv_sz_bound (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜uint (pv_sz V) <= 2 ^ 38⌝.
  Proof.
    iIntros "(%Hszb & _)". iPureIntro.
    rewrite uvm_maxsz_val in Hszb. change (2 ^ 38)%Z with 274877906944%Z. lia.
  Qed.

  (* The map is below the size: what growproc hands uvmalloc as its
     freshness premise (through [ProcPtOwn.um_below_run_fresh]). *)
  Lemma proc_priv_um_below (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝.
  Proof. iIntros "(_ & %Hbel & _)". done. Qed.

  (* What a syscall-argument read needs, TOGETHER: the trapframe pointer
     fraction and the page it names.  [proc_priv_trapframe] alone cannot
     serve -- its wand swallows the [proc_priv] the page is still inside --
     so the pair is one accessor.  This is argfd's premise to argint. *)
  Lemma proc_priv_tf (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_trapframe pa ↦₈{DfracOwn (1/4)} page_base (ud_tfp (pv_upt V)) ∗
    tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
    (p_trapframe pa ↦₈{DfracOwn (1/4)} page_base (ud_tfp (pv_upt V)) -∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V) -∗ proc_priv γf pa pid V).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho & Hc)".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iDestruct (word_split14 with "Htfc") as "[Hq1 Hq2]".
    iFrame "Hq1 Htfp".
    iIntros "Hq1 Htfp". rewrite /proc_priv /proc_pt_at.
    iDestruct (word_join14 with "Hq1 Hq2") as "Htfc".
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* =================================================================== *)
  (* WHAT A CHANGE OF ADDRESS SPACE NEEDS -- one accessor.                *)
  (* =================================================================== *)
  (* copyin / copyout / uvmalloc / uvmdealloc are stated one tier DOWN, over
     the bare [p->sz] and [p->pagetable] cells plus [ProcPtOwn.proc_pt]
     (SpecCopyin.v, SpecUvmalloc.v), because they are also reachable from
     callers that hold no [struct proc] block.  This is the bridge from THIS
     altitude to that one, and it is stated at its GENERAL shape: BOTH the
     size and the descriptor may move, which is what growproc does and what
     [proc_priv_copy] below is the [szv := pv_sz V] instance of.
       What the caller owes on the way back is exactly the two conjuncts of
     the block that talk about the pair -- the size is inside the user region,
     and the map is below the size.  What it does NOT owe is anything about
     [ud_root] / [ud_tfp] beyond their being unchanged: that is what keeps the
     two cells and the trapframe page described by the NEW descriptor, so the
     block is rebuilt rather than reconstructed.  A wand that returned only
     [proc_pt] would have swallowed the [proc_priv] the cells are still inside
     (the [proc_priv_tf] lesson). *)
  Lemma proc_priv_addrspace (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_sz pa ↦₈ pv_sz V ∗
    p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗
    proc_pt (pv_upt V) ∗
    (∀ (P' : uptd) (szv : mword 64),
       ⌜ud_root P' = ud_root (pv_upt V)⌝ -∗
       ⌜ud_tfp P' = ud_tfp (pv_upt V)⌝ -∗
       ⌜uint szv <= uvm_maxsz⌝ -∗
       ⌜um_below szv (ud_um P')⌝ -∗
       p_sz pa ↦₈ szv -∗
       p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) -∗
       proc_pt P' -∗
       proc_priv γf pa pid (upd_sz (upd_upt V P') szv)).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho & Hc)".
    rewrite /proc_fields /proc_pt_at.
    iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iFrame "Hsz Hpg Hptt".
    iIntros (P' szv) "%Hroot %Htf %Hszb' %Hbel' Hsz Hpg Hptt".
    rewrite /proc_priv /proc_fields /proc_pt_at.
    cbn [upd_sz upd_upt pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    rewrite Hroot Htf.
    iSplitR; [iPureIntro; exact Hszb'|].
    iSplitR; [iPureIntro; exact Hbel'|].
    iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro. exact Hnl. }
    iFrame "Hpg Htfc Hptt Htfp Ho Hc".
  Qed.

  (* THE COPY INSTANCE: the size stays put and the descriptor only GREW --
     what copyin / copyout do to a process when they fault a page in.  The
     premise is [uptd_ext_sz], not [uptd_ext]: a bare extension would say
     nothing about WHERE the map grew, and the block cannot be rebuilt
     without that (see [proc_priv]).  It costs the two callees nothing --
     vmfault only backs a page it has already checked against [p->sz], so
     the fact was in their proofs all along. *)
  Lemma proc_priv_copy (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_sz pa ↦₈ pv_sz V ∗
    p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗
    proc_pt (pv_upt V) ∗
    (∀ P' : uptd, ⌜uptd_ext_sz (pv_sz V) (pv_upt V) P'⌝ -∗
       p_sz pa ↦₈ pv_sz V -∗
       p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) -∗
       proc_pt P' -∗
       proc_priv γf pa pid (upd_upt V P')).
  Proof.
    iIntros "Hpv".
    iDestruct (proc_priv_sz_maxsz with "Hpv") as "%Hszb".
    iDestruct (proc_priv_um_below with "Hpv") as "%Hbel".
    iDestruct (proc_priv_addrspace with "Hpv") as "($ & $ & $ & Hback)".
    iIntros (P') "%Hext Hsz Hpg Hptt".
    iApply ("Hback" $! P' (pv_sz V) with "[%] [%] [%] [%] Hsz Hpg Hptt").
    - exact (proj1 (uptd_ext_sz_ext _ _ _ Hext)).
    - exact (proj1 (proj2 (uptd_ext_sz_ext _ _ _ Hext))).
    - exact Hszb.
    - exact (um_below_ext_sz _ _ _ Hbel Hext).
  Qed.

  (* Borrow one fd slot and hand back a (possibly different) one. *)
  Lemma proc_priv_ofile (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    proc_priv γf pa pid V -∗
    ofile_slot γf pa fd v ∗
    (∀ v', ofile_slot γf pa fd v' -∗ proc_priv γf pa pid (upd_ofile V fd v')).
  Proof.
    iIntros (Hfd) "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & [%Hlen Ho] & Hc)".
    iDestruct (big_sepL_insert_acc with "Ho") as "[$ Hback]"; first exact Hfd.
    iIntros (v') "Hslot". iDestruct ("Hback" $! v' with "Hslot") as "Ho".
    rewrite /proc_priv /proc_ofiles.
    cbn [upd_ofile pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR; [iPureIntro; exact Hszb|].
    iSplitR; [iPureIntro; exact Hbel|].
    iFrame "Hpid Hf Hpt Htfp".
    iSplitL "Ho".
    { iFrame "Ho". iPureIntro. rewrite length_insert. exact Hlen. }
    iFrame "Hc".
  Qed.

  (* READ one fd slot's cell and put it straight back.  What a SCAN of the
     array wants (fdalloc's loop): it only needs to know whether the stored
     pointer is null, and touching the payload disjunction per iteration would
     put a case split inside a loop invariant for no reason. *)
  Lemma proc_priv_ofile_read (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    proc_priv γf pa pid V -∗
    p_ofile pa fd ↦₈ v ∗ (p_ofile pa fd ↦₈ v -∗ proc_priv γf pa pid V).
  Proof.
    iIntros (Hfd) "Hpv".
    iDestruct (proc_priv_ofile _ _ _ _ fd v Hfd with "Hpv") as "[[Hc Hval] Hback]".
    iFrame "Hc". iIntros "Hc".
    iDestruct ("Hback" $! v with "[Hc Hval]") as "Hpv"; [rewrite /ofile_slot; iFrame "Hc Hval"|].
    rewrite (upd_ofile_id _ _ _ Hfd). iExact "Hpv".
  Qed.

  (* The whole point of the fractional pid: another core reading p->pid under
     p->lock agrees with what the running thread believes. *)
  Lemma proc_priv_pid_agree (γf : gname) (pa : mword 64) (pid pid' : mword 32)
      (V : pprivate) (dq : dfrac) :
    proc_priv γf pa pid V -∗ p_pid pa ↦₄{dq} pid' -∗ ⌜pid = pid'⌝.
  Proof.
    iIntros "(_ & _ & Hpid & _) Hother".
    iApply (word4_pointsto_agree with "Hpid Hother").
  Qed.

  (* The two halves of [p->pid], joined and split ([RiscvPtsto]'s
     [word4_pointsto_half] is the 1/2 + 1/2 split itself).  allocproc is the one
     function that holds BOTH -- the invariant's permanent half out of
     [SchedCtx.proc_pub] and the dormant block's -- and so the one function
     that may WRITE the cell.  Joining first tells it the two halves agree,
     which is what [word4_pointsto_agree] is for; splitting after the store
     is what hands one half back to the invariant and one to [proc_priv]. *)
  Lemma p_pid_join (pa : mword 64) (p1 p2 : mword 32) :
    p_pid pa ↦₄{DfracOwn (1/2)} p1 -∗ p_pid pa ↦₄{DfracOwn (1/2)} p2 -∗
    ⌜p1 = p2⌝ ∗ p_pid pa ↦₄ p1.
  Proof.
    iIntros "H1 H2".
    iDestruct (word4_pointsto_agree with "H1 H2") as %<-.
    iSplit; [done|]. rewrite word4_pointsto_half. iFrame.
  Qed.

  Lemma p_pid_split (pa : mword 64) (v : mword 32) :
    p_pid pa ↦₄ v -∗ p_pid pa ↦₄{DfracOwn (1/2)} v ∗ p_pid pa ↦₄{DfracOwn (1/2)} v.
  Proof. rewrite word4_pointsto_half. iIntros "$". Qed.

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
  Definition proc_dormant (pa : mword 64) (st : mword 32) : iProp Σ :=
    (∃ (V : pprivate) (pid : mword 32),
       ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
        pv_cwd V = (zero_reg : mword 64) /\
        uint (pv_sz V) <= uvm_maxsz⌝ ∗
       p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
       proc_fields pa (DfracOwn 1) V ∗
       ofile_cells pa (pv_ofile V) ∗
       (* a dormant process still OWNS its NOFILE units -- every descriptor
          is null, so it holds all of them itself.  Parking them here rather
          than making allocproc conjure them is what keeps the supply
          conserved across the whole UNUSED -> live -> ZOMBIE cycle. *)
       ([∗ list] _ ∈ pv_ofile V, fd_slot) ∗
       (* ... and its ALLOWANCE, the FDSPARE units a syscall borrows for a
          reference in flight (FdSlots.v).  Parked here for the same reason
          and with the same effect: [FDSLOTS] is now exactly what the NPROC
          dormant blocks hold between them, so boot routes the WHOLE supply
          and nothing is left over. *)
       fd_slots FDSPARE ∗
       own_ctx (p_context pa) ∗
       (* The address-space cells, keyed on WHICH dormant state -- tied to
          [st], not a free disjunction.  A ZOMBIE still owns a live user
          table and trapframe page, which is precisely what wait()/freeproc
          reclaim; by UNUSED freeproc has kfree'd both and zeroed the two
          cells.  So the ZOMBIE -> UNUSED step genuinely MOVES resources,
          which is why [proc_slots_recast] deliberately does not cover the
          dormant class. *)
       (if bool_decide (st = ZOMBIE)
        then proc_pt_at pa (pv_upt V) ∗ tf_page (ud_tfp (pv_upt V)) (pv_tf V)
        else p_pagetable pa ↦₈ (zero_reg : mword 64) ∗
             p_trapframe pa ↦₈ (zero_reg : mword 64)))%I.

  (* The UNUSED block WITHOUT its fd-slot units: what procinit is handed for
     each process before the supply is distributed.  Nothing in procinit
     touches these cells (the BSS is already zero); the units are the one
     thing boot has to route, and [proc_dormant_seal] is that step.  Fixed at
     UNUSED -- procinit produces no ZOMBIEs -- so the two address-space cells
     are the zeroed pair. *)
  Definition proc_dormant_nofd (pa : mword 64) : iProp Σ :=
    (∃ (V : pprivate) (pid : mword 32),
       ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
        pv_cwd V = (zero_reg : mword 64) /\
        uint (pv_sz V) <= uvm_maxsz⌝ ∗
       p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
       proc_fields pa (DfracOwn 1) V ∗
       ofile_cells pa (pv_ofile V) ∗
       own_ctx (p_context pa) ∗
       p_pagetable pa ↦₈ (zero_reg : mword 64) ∗
       p_trapframe pa ↦₈ (zero_reg : mword 64))%I.

  Lemma proc_dormant_seal (pa : mword 64) :
    proc_dormant_nofd pa -∗ fd_slots (NOFILE + FDSPARE) -∗ proc_dormant pa UNUSED.
  Proof.
    iIntros "(%V & %pid & [%Hof [%Hcwd %Hsz]] & Hpid & Hf & Ho & Hctx & Hpg & Htf) Hs".
    iDestruct (fd_slots_split with "Hs") as "[Hs Hsp]".
    iExists V, pid. iFrame "Hpid Hf Ho Hsp Hctx". iSplit; [done|].
    rewrite bool_decide_eq_false_2; [| vm_compute; discriminate].
    iSplitL "Hs".
    { iApply fd_slots_to_any. by rewrite Hof length_replicate. }
    iFrame "Hpg Htf".
  Qed.

  (* allocproc's move: it finds an UNUSED slot, so the two address-space
     cells are zero and it must BUILD the table itself (kalloc a trapframe,
     proc_pagetable) -- which is exactly what allocproc's C does.  The
     null-ofile fact is what discharges every [ofile_slot]'s left disjunct
     with no [file_ref] to conjure from nowhere. *)
  (* The allowance comes out too, and separately: it is not part of the
     private field block, it is what the RUNNING THREAD carries beside
     [proc_priv] (FdSlots.v's [FDSPARE] note). *)
  Lemma proc_dormant_unused (γf : gname) (pa : mword 64) :
    proc_dormant pa UNUSED -∗
    own_ctx (p_context pa) ∗
    p_pagetable pa ↦₈ (zero_reg : mword 64) ∗
    p_trapframe pa ↦₈ (zero_reg : mword 64) ∗
    fd_slots FDSPARE ∗
    ∃ (V : pprivate) (pid : mword 32),
      ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
       pv_cwd V = (zero_reg : mword 64) /\
       uint (pv_sz V) <= uvm_maxsz⌝ ∗
      p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
      proc_fields pa (DfracOwn 1) V ∗ proc_ofiles γf pa (pv_ofile V).
  Proof.
    iIntros "(%V & %pid & [%Hof [%Hcwd %Hsz]] & Hpid & Hf & Ho & Hs & Hsp & Hctx & Haddr)".
    rewrite bool_decide_eq_false_2; [| vm_compute; discriminate].
    iDestruct "Haddr" as "[Hpg Htf]". iFrame "Hctx Hpg Htf Hsp".
    iExists V, pid. iSplit; [done|]. iFrame "Hpid Hf".
    rewrite /proc_ofiles /ofile_cells Hof length_replicate. iSplit; [done|].
    iAssert ([∗ list] fd ↦ v ∈ replicate NOFILE (zero_reg : mword 64),
               (p_ofile pa fd ↦₈ v ∗ fd_slot))%I with "[Ho Hs]" as "Ho".
    { rewrite big_sepL_sep. iFrame "Ho Hs". }
    iApply (big_sepL_impl with "Ho"). iIntros "!>" (fd v Hv) "[Hcell Hslot]".
    apply lookup_replicate in Hv as [-> _]. iFrame "Hcell". iLeft. by iFrame "Hslot".
  Qed.

  (* =================================================================== *)
  (* The saved-context save area AS BYTES.                                *)
  (* =================================================================== *)
  (* allocproc does [memset(&p->context, 0, sizeof(p->context))], and memset
     is stated over a BYTE buffer while [SwtchCtx.ctx_cells] is fourteen
     [↦₈] cells.  These three lemmas are that conversion.  It has to be an
     ACCESSOR rather than two independent directions: the eight bytes of a
     word no longer carry the word's 8-alignment, so the rebuild's side
     condition must be captured before the split (the
     [word_pointsto_split4] discipline, and [ByteBuf.bb_word_acc] is the
     one-cell instance this is built from). *)

  (* [ctx_cells] in the uniform [pa_add]-indexed form every byte lemma is
     stated at. *)
  Local Lemma ctx_cells_at_run (c : mword 64) (o : nat) (vs : list (mword 64)) :
    ctx_cells_at c (8 * Z.of_nat o) vs ⊣⊢
    [∗ list] i ↦ v ∈ vs, pa_add c (8 * (o + i))%nat ↦₈ v.
  Proof.
    revert o. induction vs as [|v vs IH]; intro o.
    - by rewrite big_sepL_nil.
    - rewrite big_sepL_cons /=.
      assert (Ha : pa_add c (8 * (o + 0))%nat = add_vec c (mword_of_int (8 * Z.of_nat o))).
      { unfold pa_add, add_vec_int. apply bv_eq.
        rewrite !add_vec64_unsigned !moi64_unsigned.
        rewrite !bv_wrap_add_idemp_r. f_equal. lia. }
      rewrite Ha.
      replace (8 * Z.of_nat o + 8)%Z with (8 * Z.of_nat (S o))%Z by lia.
      rewrite (IH (S o)).
      apply bi.sep_proper; [reflexivity|].
      apply big_sepL_proper. intros i x _.
      by replace (S o + i)%nat with (o + S i)%nat by lia.
  Qed.

  Lemma ctx_cells_run (c : mword 64) (vs : list (mword 64)) :
    ctx_cells c vs ⊣⊢ [∗ list] i ↦ v ∈ vs, pa_add c (8 * i)%nat ↦₈ v.
  Proof.
    rewrite /ctx_cells.
    replace 0%Z with (8 * Z.of_nat 0)%Z by lia.
    rewrite (ctx_cells_at_run c 0 vs).
    apply big_sepL_proper. intros i x _. by rewrite Nat.add_0_l.
  Qed.

  (* a run of word cells, borrowed as an anonymous byte window and rebuilt at
     whatever the bytes now hold. *)
  Lemma wcells_bytes_acc (a : mword 64) (ws : list (mword 64)) :
    ([∗ list] i ↦ w ∈ ws, pa_add a (8 * i)%nat ↦₈ w) ⊢
    ([∗ list] j ∈ seq 0 (8 * length ws), byte_any (pa_add a j)) ∗
    (∀ g : nat -> bv 8,
       ([∗ list] j ∈ seq 0 (8 * length ws), pa_add a j ↦ₘ g j) -∗
       ∃ ws' : list (mword 64), ⌜length ws' = length ws⌝ ∗
         [∗ list] i ↦ w ∈ ws', pa_add a (8 * i)%nat ↦₈ w).
  Proof.
    assert (Hshift : forall (b : mword 64) (l : list (mword 64)),
      ([∗ list] i ↦ x ∈ l, pa_add b (8 * S i)%nat ↦₈ x)
      ⊣⊢ ([∗ list] i ↦ x ∈ l, pa_add (pa_add b 8) (8 * i)%nat ↦₈ x)).
    { intros b l. apply big_sepL_proper. intros i x _.
      rewrite InstrBytes.pa_add_add. replace (8 * S i)%nat with (8 + 8 * i)%nat by lia.
      reflexivity. }
    revert a. induction ws as [|w ws IH]; intro a.
    - iIntros "_". cbn [length]. rewrite Nat.mul_0_r !big_sepL_nil.
      iSplit; [done|]. iIntros (g) "_". iExists []. by iSplit.
    - cbn [length]. replace (8 * S (length ws))%nat with (8 + 8 * length ws)%nat by lia.
      rewrite big_sepL_cons Nat.mul_0_r RiscvExtras.pa_add_0 (Hshift a ws).
      iIntros "[Hh Ht]".
      iDestruct (bb_word_acc a w with "Hh") as "[Hhb Hhback]".
      iDestruct (IH (pa_add a 8) with "Ht") as "[Htb Htback]".
      rewrite (bwin_split a 0 8 (8 * length ws)) Nat.add_0_l.
      iSplitL "Hhb Htb".
      { iSplitL "Hhb"; [iApply (bb_named_any with "Hhb")|].
        rewrite (bwin_rebase a 8 (8 * length ws)). iExact "Htb". }
      iIntros (g) "Hg".
      rewrite (bb_split a 8 (8 * length ws) g).
      iDestruct "Hg" as "[Hg0 Hg1]".
      iDestruct ("Hhback" $! g with "Hg0") as (w') "Hw'".
      iDestruct ("Htback" $! (fun j => g (8 + j)%nat) with "Hg1") as (ws') "[%Hlen Hws']".
      iExists (w' :: ws'). iSplit; [iPureIntro; cbn; lia|].
      rewrite big_sepL_cons Nat.mul_0_r RiscvExtras.pa_add_0.
      rewrite (Hshift a ws'). iFrame "Hw' Hws'".
  Qed.

  (* the instance allocproc uses: the whole 112-byte save area. *)
  Lemma own_ctx_bytes (c : mword 64) :
    own_ctx c ⊢
    ([∗ list] j ∈ seq 0 112, byte_any (pa_add c j)) ∗
    (∀ g : nat -> bv 8,
       ([∗ list] j ∈ seq 0 112, pa_add c j ↦ₘ g j) -∗
       ∃ ws : list (mword 64), ⌜length ws = 14%nat⌝ ∗
         [∗ list] i ↦ w ∈ ws, pa_add c (8 * i)%nat ↦₈ w).
  Proof.
    iIntros "(%vs & %Hlen & Hvs)".
    rewrite ctx_cells_run.
    iDestruct (wcells_bytes_acc c vs with "Hvs") as "[Hb Hback]".
    rewrite Hlen. iFrame "Hb".
    iIntros (g) "Hg". iApply ("Hback" $! g with "Hg").
  Qed.

  (* the two context slots allocproc writes after the memset, in the address
     form the two [sd rd,off(s1)] produce. *)
  Lemma p_ctx_slot0 (pa : mword 64) : pa_add (p_context pa) 0 = p_context pa.
  Proof. apply RiscvExtras.pa_add_0. Qed.

  Lemma p_ctx_slot1 (pa : mword 64) :
    pa_add (p_context pa) 8 = add_vec pa (mword_of_int 104).
  Proof.
    unfold pa_add, add_vec_int, p_context, context_off. apply bv_eq.
    rewrite !add_vec64_unsigned !moi64_unsigned.
    rewrite !bv_wrap_add_idemp_r !bv_wrap_add_idemp_l. f_equal. lia.
  Qed.

  (* =================================================================== *)
  (* kstack: write-once at procinit, hence persistent.                    *)
  (* =================================================================== *)
  Definition is_kstack (pa : mword 64) (ks : mword 64) : iProp Σ :=
    p_kstack pa ↦₈□ ks.

  Global Instance is_kstack_persistent pa ks : Persistent (is_kstack pa ks).
  Proof. rewrite /is_kstack /word_pointsto /mem_pointsto. apply _. Qed.

End ProcInv.
