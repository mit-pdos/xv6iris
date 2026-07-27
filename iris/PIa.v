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
   the 3808-byte tail.  It used to be ProcPtOwn's contents-existential
   [proc_tf_own]; the syscall path needs the VALUE of [tf->aN], which that
   could not supply. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import ProcGeom.
Require Import UserPtTree ProcPtOwn.
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

Definition upd_cwd (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (pv_ofile V) v (pv_name V).

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
  (* The trapframe PAGE.                                                  *)
  (* =================================================================== *)
  (* [ProcPtOwn] used to own these 4096 bytes as [proc_tf_own] = a
     contents-EXISTENTIAL [phys_page_own].  That cannot serve the syscall
     path, which needs the VALUE of [tf->aN], so the page moved here and
     gained structure -- exactly the evolution ProcPtOwn's own comment
     anticipated.

     Covering the WHOLE page, not just the argument slots: the 36
     [struct trapframe] words carry values, and the 3808 bytes of tail
     padding are owned anonymously.  Anything less would leave part of a
     kalloc'd page unaccounted for, and [freeproc]'s [kfree] needs the
     whole page back.

     Stated at the PHYSICAL tier, indexed by the ppn: that is the tier
     kalloc hands out and the tier [proc_tf_own] used, and it is
     tier-neutral (no va inside), which matters because this page is
     reached from BOTH sides -- the kernel's identity map (argraw's
     [ld a0,112(a5)]) and the user table's TRAPFRAME va (uservec /
     userret).  Each access site converts with
     [RiscvPtsto.phys_to_mem_claim] / [mem_to_phys_claim], the same idiom
     the software page-table walks already use for PT slots. *)
  Definition a_tf_word (tfp : mword 44) (i : nat) : Arch.pa :=
    pa_add (page_base tfp) (Z.to_nat (tf_word_off i)).

  Definition tf_words (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    ([∗ list] i ↦ w ∈ ws, a_tf_word tfp i ↦ₚ₈ w)%I.

  (* the page beyond the struct: 288 .. 4095, contents irrelevant *)
  Definition tf_tail (tfp : mword 44) : iProp Σ :=
    ([∗ list] j ∈ seq (Z.to_nat TFBYTES) (4096 - Z.to_nat TFBYTES),
       ∃ b : bv 8, pa_add (page_base tfp) j ↦ₚ b)%I.

  Definition tf_page (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    (⌜length ws = TFWORDS⌝ ∗ tf_words tfp ws ∗ tf_tail tfp)%I.

  (* borrow one trapframe word -- the nth syscall argument is [tf_arg_idx n] *)
  Lemma tf_page_word (tfp : mword 44) (ws : list (mword 64)) (i : nat) (w : mword 64) :
    ws !! i = Some w ->
    tf_page tfp ws -∗
    a_tf_word tfp i ↦ₚ₈ w ∗ (a_tf_word tfp i ↦ₚ₈ w -∗ tf_page tfp ws).
  Proof.
    iIntros (Hi) "(%Hlen & Hws & Htail)".
    iDestruct (big_sepL_lookup_acc _ _ i w Hi with "Hws") as "[$ Hback]".
    iIntros "Hc". iSplit; [done|]. iSplitL "Hc Hback"; [by iApply "Hback" | iExact "Htail"].
  Qed.

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
     proc_pt_at pa (pv_upt V) ∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
     proc_ofiles γf pa (pv_ofile V) ∗
     cwd_ref (pv_cwd V))%I.

End ProcInv.
