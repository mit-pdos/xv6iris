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
Require Import Pt4kWalk CommonWalk PtTree KptPt TrampPt KMap.
Require Import SwtchCtx.
Require Import FdSlots FileInvDefs.
Require Export ProcDefs.
(* [Typeclasses Opaque] is compilation-local: repeat the declaration here so
   broad [iFrame] calls do not unfold the 4 KiB [tf_page] big-op imported
   from [ProcDefs]. *)
Typeclasses Opaque tf_words tf_tail tf_page.
(* [IcacheRef.inode_held]: what [p->cwd] owns, and [IrefSlots.iref_slots]:
   the supply a dormant block parks.  Exported, because a consumer of
   [proc_priv] that has to name the reference should not have to know which
   of the two files it came from. *)
Require Export InodeRef.
Require Import KallocInv PageFields ByteBuf.
(* [FirstTok.first_tok], which is a CONJUNCT of the private block below.  It
   is a leaf import for this file's purposes: [FirstTok] sits entirely in the
   fs/kalloc layers and its cone does not reach any process file, so the edge
   runs one way only.  See the note at [proc_priv_core]. *)
(* ...and [RiscvLang], for the CLASS [GenId] alone: without the name in
   scope the backtick binder below generalizes a fresh [GenId : Type] and
   [first_tok]'s own [GEN] is then unresolvable (durable-notes.md's
   "missing/late imports auto-generalize silently"). *)
Require Import RiscvLang.
Require Import FirstTok.
(* [Typeclasses Opaque] is compilation-local (same note as [tf_page]'s above),
   and for [first_tok] it is CORRECTNESS, not speed: the token is a conjunct
   of [proc_priv], and an unsealed disjunction lets a broad [iFrame] frame a
   [kernel_text] into its boot arm.  See [FirstTok.v]'s note at the seal. *)
Typeclasses Opaque first_tok first_boot_persist.
From Kernel Require KernelSyms.
Require Import RiscvExtras.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* One generic bigop fact, needed by the fd-deficit accessor below.        *)
(* ===================================================================== *)
(* The REMAINDER after deleting index [i] cannot see a store at [i]: both
   sides are [take i l] ++ emp ++ [drop (S i) l].  This is what lets one
   accessor change the value at [i] AND the predicate everywhere else in a
   single step.  [big_sepL_insert_acc] does the value alone and
   [big_sepL_lookup_acc_impl] the predicate alone; a descriptor going on loan
   changes both at once (its cell is written, and it leaves the set of
   descriptors that own a payload), so neither suffices. *)
Lemma big_sepL_delete_insert {PROP : bi} {A : Type} (Φ : nat -> A -> PROP)
    (l : list A) (i : nat) (x y : A) :
  l !! i = Some x ->
  ([∗ list] k↦z ∈ l, if decide (k = i) then emp else Φ k z)
  ⊣⊢ ([∗ list] k↦z ∈ <[i := y]> l, if decide (k = i) then emp else Φ k z).
Proof.
  intro Hi.
  assert (Hlt : (i < length l)%nat) by (eapply lookup_lt_Some; exact Hi).
  rewrite -{1}(take_drop_middle l i x Hi) (insert_take_drop l i y Hlt).
  rewrite !big_sepL_app /= !Nat.add_0_r.
  rewrite length_take_le; [|lia].
  by rewrite !decide_True.
Qed.

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
(* functional update of one fd slot -- fdalloc / sys_close / kexit. *)
Definition upd_ofile (V : pprivate) (fd : nat) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (<[fd := v]> (pv_ofile V)) (pv_cwd V) (pv_name V).

Definition upd_sz (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv v (pv_upt V) (pv_tf V) (pv_ofile V) (pv_cwd V) (pv_name V).

(* functional update of the trapframe words -- what prepare_return does to
   the four KERNEL slots (kernel_satp / kernel_sp / kernel_trap /
   kernel_hartid) it re-arms for the next uservec, and what a syscall's
   return value write does to the a0 slot.  The page itself is unchanged;
   only [pv_tf]'s contents move. *)
Definition upd_tf (V : pprivate) (ws : list (mword 64)) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) ws (pv_ofile V) (pv_cwd V) (pv_name V).

(* the descriptor moves, everything else stays -- what copyin / copyout /
   vmfault do to a process when they fault a page in ([uptd_ext], below). *)
Definition upd_upt (V : pprivate) (P : uptd) : pprivate :=
  MkPPriv (pv_sz V) P (pv_tf V) (pv_ofile V) (pv_cwd V) (pv_name V).

(* [upd_cwd] and [upd_cwd_id] live in [ProcDefs], next to [pprivate]
   itself and to [proc_priv_bare_cwd], the borrow that needs them. *)

(* a process GAINS its address space: the descriptor and the trapframe words
   move, the scalar fields stay.  allocproc's move, once kalloc has produced
   the trapframe page and proc_pagetable the table. *)
Definition upd_pt (V : pprivate) (P : uptd) (ws : list (mword 64)) : pprivate :=
  MkPPriv (pv_sz V) P ws (pv_ofile V) (pv_cwd V) (pv_name V).

(* the 16 debug-name bytes -- kfork's [safestrcpy(np->name, p->name, 16)] and
   kexec's [safestrcpy(p->name, last, 16)]. *)
Definition upd_name (V : pprivate) (ns : list (bv 8)) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (pv_ofile V) (pv_cwd V) ns.

(* EXEC'S MOVE: a process REPLACES its address space.  The size, the
   descriptor, the trapframe words and the name all change at once; the
   descriptor array and the working directory survive (xv6's exec closes no
   file and does not chdir).  This is exactly the composite kexec's two
   accessors below produce, and [upd_exec_compose] is the equation that says
   so -- stating the postcondition with this one name is what keeps
   SpecKexec's success arm readable. *)
Definition upd_exec (V : pprivate) (szv : mword 64) (P : uptd)
    (ws : list (mword 64)) (ns : list (bv 8)) : pprivate :=
  MkPPriv szv P ws (pv_ofile V) (pv_cwd V) ns.

Lemma upd_exec_compose (V : pprivate) (szv : mword 64) (P : uptd)
    (ws : list (mword 64)) (ns : list (bv 8)) :
  upd_sz (upd_pt (upd_name V ns) P ws) szv = upd_exec V szv P ws ns.
Proof. by destruct V. Qed.

Lemma upd_name_id (V : pprivate) : upd_name V (pv_name V) = V.
Proof. by destruct V. Qed.

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
  Context `{XI : CurCtx}.

  (* =================================================================== *)
  (* The scalar private cells.                                           *)
  (* =================================================================== *)
  (* the SCALAR private cells.  pagetable and trapframe are absent: those two
     cells belong to [ProcPtOwn.proc_pt_at], which rides beside this in
     [proc_priv]. *)
  (* =================================================================== *)
  (* p->ofile[fd]: the cell, plus the reference it names.                *)
  (* =================================================================== *)
  (* Bare cells, no validity clause: what the DORMANT bundle holds (every
     slot is null there, so there is no reference to describe). *)
  (* [irefNameG] carries the itable's reference authority CANONICALLY --
     there is exactly one itable per system, and threading its gname would
     put a filesystem ghost NAME on [proc_priv], hence on the thirty-three
     spec files that mention it, purely so a process can name its cwd.
     [FdSlots] and [IrefSlots] already do this and [IrefSlots.v]'s header
     spells out the argument.  What propagates is the CLASS -- capacity, no
     resource, no change to any statement's shape. *)
  Context `{ !fileG Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ}.
  (* [FirstTok.first_tok] rides inside the private block (see
     [proc_priv_core]), and its boot arm names [RiscvPtsto.gen_cert]; that
     is the ONLY new index the block acquires.  The file-system's own two
     configuration classes are NOT new binders here: [fileG] already carries
     [IcacheRef.icfg] and [FsCfg.fscfg] as superclass fields
     ([FileInvDefs.file_icfg] / [file_fscfg]), so every mention of the token
     below -- and hence [proc_priv]'s own elaboration -- is at exactly the
     instance the whole process layer already shares.  Nothing downstream
     grows a binder for the file system. *)
  Context `{GEN : GenId}.

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
  (* THE DEFICIT: descriptors whose payload is on loan.                   *)
  (* =================================================================== *)
  (* A syscall that must hold one of its OWN descriptors' references in a
     register cannot leave the array satisfying [proc_ofiles]: the cell still
     names the file, so [ofile_slot]'s file disjunct demands a reference that
     is not there.  sys_dup is the case that forces it -- [fdalloc] stores the
     pointer before [filedup] bumps the count, and [filedup] wants the SOURCE
     descriptor's reference in hand to split, so two descriptors are payloadless
     at once.  Crucially [fdalloc] itself needs the array, so the reference
     cannot merely be borrowed with [proc_ofiles_ofile] across the call: that
     accessor's wand demands a whole [ofile_slot] back first.
       [proc_ofiles_owe γf pa fs D] is the array with the payloads of [D]
     missing -- each such descriptor contributes only its cell.

     WHY THE NON-NULL CLAUSE.  A lent descriptor's cell is never null (one only
     lends a descriptor that names a file), and saying so HERE is what lets
     fdalloc's install arm conclude [fd ∉ D] from "the cell I found is null":
     fdalloc is generic in [D] and never learns it, so without this it could
     not tell a free descriptor from a lent one, and could install a second
     reference over a loan.

     WHY NOT A THIRD [ofile_slot] DISJUNCT.  Because only the holder of the
     block sees [D].  A "maybe on loan" case inside [ofile_slot] would have to
     be REFUTED by every consumer of a non-null descriptor (argfd's callers,
     sys_close), and none of them can do that from [v <> 0] alone.  See
     claude-notes/design/file-table.md. *)
  Definition ofile_lent_or_slot (γf : gname) (pa : mword 64) (D : gset nat)
      (fd : nat) (v : mword 64) : iProp Σ :=
    (if bool_decide (fd ∈ D)
     then ⌜v <> (zero_reg : mword 64)⌝ ∗ p_ofile pa fd ↦₈ v
     else ofile_slot γf pa fd v)%I.

  Definition proc_ofiles_owe (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D : gset nat) : iProp Σ :=
    (⌜length fs = NOFILE⌝ ∗
     [∗ list] fd ↦ v ∈ fs, ofile_lent_or_slot γf pa D fd v)%I.

  Lemma ofile_lent_or_slot_in (γf : gname) (pa : mword 64) (D : gset nat)
      (fd : nat) (v : mword 64) :
    fd ∈ D ->
    ofile_lent_or_slot γf pa D fd v ⊣⊢ ⌜v <> (zero_reg : mword 64)⌝ ∗ p_ofile pa fd ↦₈ v.
  Proof. intro Hin. rewrite /ofile_lent_or_slot bool_decide_true //. Qed.

  Lemma ofile_lent_or_slot_out (γf : gname) (pa : mword 64) (D : gset nat)
      (fd : nat) (v : mword 64) :
    fd ∉ D -> ofile_lent_or_slot γf pa D fd v ⊣⊢ ofile_slot γf pa fd v.
  Proof. intro Hin. rewrite /ofile_lent_or_slot bool_decide_false //. Qed.

  (* NO deficit is the array itself -- so [proc_priv] never has to change
     shape for a function that lends nothing. *)
  Lemma proc_ofiles_owe_empty (γf : gname) (pa : mword 64) (fs : list (mword 64)) :
    proc_ofiles_owe γf pa fs ∅ ⊣⊢ proc_ofiles γf pa fs.
  Proof.
    rewrite /proc_ofiles_owe /proc_ofiles.
    apply bi.sep_proper; [reflexivity|].
    apply big_sepL_proper. intros fd v _.
    apply ofile_lent_or_slot_out. set_solver.
  Qed.

  Lemma proc_ofiles_owe_len (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D : gset nat) :
    proc_ofiles_owe γf pa fs D -∗ ⌜length fs = NOFILE⌝.
  Proof. iIntros "[$ _]". Qed.

  (* Away from [fd], two deficit sets that agree give the same remainder. *)
  Lemma ofiles_rest_agree (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D D' : gset nat) (fd : nat) :
    (forall j, j <> fd -> (j ∈ D <-> j ∈ D')) ->
    ([∗ list] k↦y ∈ fs, if decide (k = fd) then emp else ofile_lent_or_slot γf pa D k y)
    ⊣⊢ ([∗ list] k↦y ∈ fs, if decide (k = fd) then emp else ofile_lent_or_slot γf pa D' k y).
  Proof.
    intro Hag. apply big_sepL_proper. intros k y _.
    case_decide as Hk; [reflexivity|].
    rewrite /ofile_lent_or_slot.
    destruct (decide (k ∈ D)) as [Hin|Hin].
    - rewrite !bool_decide_true //. by apply Hag.
    - rewrite !bool_decide_false //. intro Hc. apply Hin. by apply (Hag k Hk).
  Qed.

  (* THE workhorse.  Open descriptor [fd] and close it back with a new VALUE
     and under a new deficit set, provided the two sets agree away from [fd].
     Lend, repay and install are all instances -- which is the point: the
     surgery happens once, here, and the three uses below are one line each. *)
  Lemma proc_ofiles_owe_acc (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D D' : gset nat) (fd : nat) (v : mword 64) :
    fs !! fd = Some v ->
    (forall j, j <> fd -> (j ∈ D <-> j ∈ D')) ->
    proc_ofiles_owe γf pa fs D -∗
    ofile_lent_or_slot γf pa D fd v ∗
    (∀ v', ofile_lent_or_slot γf pa D' fd v' -∗
           proc_ofiles_owe γf pa (<[fd := v']> fs) D').
  Proof.
    iIntros (Hfd Hag) "[%Hlen Ho]".
    rewrite (big_sepL_delete _ fs fd v Hfd).
    iDestruct "Ho" as "[$ Hrest]".
    rewrite (ofiles_rest_agree _ _ _ D D' fd Hag).
    iIntros (v') "Hnew". iSplitR.
    { iPureIntro. rewrite length_insert. exact Hlen. }
    rewrite (big_sepL_delete _ (<[fd := v']> fs) fd v').
    2:{ apply list_lookup_insert. eapply lookup_lt_Some; exact Hfd. }
    iFrame "Hnew".
    rewrite -(big_sepL_delete_insert _ fs fd v v' Hfd). iFrame "Hrest".
  Qed.

  (* LEND: a descriptor that names a file gives its reference up, and joins
     the deficit.  The caller only has to know the cell is non-null -- which
     is exactly what [SpecArgfd.arg_fd] reports. *)
  Lemma proc_ofiles_lend (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D : gset nat) (fd : nat) (v : mword 64) :
    fd ∉ D ->
    fs !! fd = Some v ->
    v <> (zero_reg : mword 64) ->
    proc_ofiles_owe γf pa fs D -∗
    ∃ (k : nat) (q : Qp) (C : fcontent),
      ⌜v = fnode k /\ (k < NFILE)%nat⌝ ∗ file_ref γf k q C ∗
      proc_ofiles_owe γf pa fs ({[fd]} ∪ D).
  Proof.
    iIntros (Hnin Hfd Hnz) "Ho".
    iDestruct (proc_ofiles_owe_acc _ _ _ D ({[fd]} ∪ D) fd v Hfd
                 ltac:(set_solver) with "Ho") as "[Hs Hback]".
    rewrite (ofile_lent_or_slot_out _ _ _ _ _ Hnin) /ofile_slot.
    iDestruct "Hs" as "[Hc [[%Hz _] | (%k & %q & %C & [%Hfn %Hk] & Href)]]";
      [contradiction|].
    iDestruct ("Hback" $! v with "[Hc]") as "Ho".
    { rewrite (ofile_lent_or_slot_in _ _ _ _ _ (elem_of_union_l _ _ _
                 (elem_of_singleton_2 _ _ (eq_refl fd)))).
      iFrame "Hc". iPureIntro. exact Hnz. }
    rewrite list_insert_id; [|exact Hfd].
    iExists k, q, C. iFrame "Href Ho". iPureIntro. split; [exact Hfn|exact Hk].
  Qed.

  (* REPAY: hand a reference back, and the descriptor leaves the deficit. *)
  Lemma proc_ofiles_repay (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D : gset nat) (fd k : nat) (q : Qp) (C : fcontent) :
    fd ∉ D ->
    fs !! fd = Some (fnode k) ->
    (k < NFILE)%nat ->
    proc_ofiles_owe γf pa fs ({[fd]} ∪ D) -∗ file_ref γf k q C -∗
    proc_ofiles_owe γf pa fs D.
  Proof.
    iIntros (Hnin Hfd Hk) "Ho Href".
    iDestruct (proc_ofiles_owe_acc _ _ _ ({[fd]} ∪ D) D fd (fnode k) Hfd
                 ltac:(set_solver) with "Ho") as "[Hs Hback]".
    rewrite (ofile_lent_or_slot_in _ _ _ _ _ (elem_of_union_l _ _ _
               (elem_of_singleton_2 _ _ (eq_refl fd)))).
    iDestruct "Hs" as "[_ Hc]".
    iDestruct ("Hback" $! (fnode k) with "[Hc Href]") as "Ho".
    { rewrite (ofile_lent_or_slot_out _ _ _ _ _ Hnin).
      iApply (ofile_slot_file _ _ _ _ q C Hk with "Hc Href"). }
    rewrite list_insert_id; [|exact Hfd]. iExact "Ho".
  Qed.

  (* INSTALL: fdalloc's whole move.  A free descriptor's unit comes out with
     its cell; writing a non-null pointer puts the descriptor in the deficit,
     for the caller to settle.  fdalloc needs no [file_ref] at all -- its code
     only stores a pointer, and [fd ∉ D] is DERIVED from the cell being null
     (the non-null clause on the lent case). *)
  Lemma proc_ofiles_install (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D : gset nat) (fd : nat) :
    fs !! fd = Some (zero_reg : mword 64) ->
    proc_ofiles_owe γf pa fs D -∗
    p_ofile pa fd ↦₈ (zero_reg : mword 64) ∗ fd_slot ∗
    (∀ v', ⌜v' <> (zero_reg : mword 64)⌝ -∗ p_ofile pa fd ↦₈ v' -∗
           proc_ofiles_owe γf pa (<[fd := v']> fs) ({[fd]} ∪ D)).
  Proof.
    iIntros (Hfd) "Ho".
    (* the cell is null, so this descriptor is NOT on loan *)
    iAssert (⌜fd ∉ D⌝)%I as "%Hnin".
    { iDestruct "Ho" as "[_ Ho]".
      iDestruct (big_sepL_lookup_acc _ _ _ _ Hfd with "Ho") as "[Hs _]".
      destruct (decide (fd ∈ D)) as [Hin|Hin]; [|iPureIntro; exact Hin].
      rewrite (ofile_lent_or_slot_in _ _ _ _ _ Hin).
      iDestruct "Hs" as "[%Hnz _]". done. }
    iDestruct (proc_ofiles_owe_acc _ _ _ D ({[fd]} ∪ D) fd _ Hfd
                 ltac:(set_solver) with "Ho") as "[Hs Hback]".
    rewrite (ofile_lent_or_slot_out _ _ _ _ _ Hnin).
    iDestruct (ofile_slot_null with "Hs") as "[$ $]".
    iIntros (v' Hnz) "Hc".
    iApply ("Hback" $! v' with "[Hc]").
    rewrite (ofile_lent_or_slot_in _ _ _ _ _ (elem_of_union_l _ _ _
               (elem_of_singleton_2 _ _ (eq_refl fd)))).
    iFrame "Hc". iPureIntro. exact Hnz.
  Qed.

  (* READ one cell, loan or no loan: fdalloc's scan.  Touching the payload
     disjunction per iteration would put a case split in a loop invariant for
     no reason. *)
  Lemma proc_ofiles_owe_read (γf : gname) (pa : mword 64) (fs : list (mword 64))
      (D : gset nat) (fd : nat) (v : mword 64) :
    fs !! fd = Some v ->
    proc_ofiles_owe γf pa fs D -∗
    p_ofile pa fd ↦₈ v ∗ (p_ofile pa fd ↦₈ v -∗ proc_ofiles_owe γf pa fs D).
  Proof.
    iIntros (Hfd) "Ho".
    iDestruct (proc_ofiles_owe_acc _ _ _ D D fd v Hfd
                 (fun j _ => iff_refl (j ∈ D)) with "Ho") as "[Hs Hback]".
    destruct (decide (fd ∈ D)) as [Hin|Hin].
    - rewrite (ofile_lent_or_slot_in _ _ _ _ _ Hin).
      iDestruct "Hs" as "[%Hnz Hc]". iFrame "Hc". iIntros "Hc".
      iDestruct ("Hback" $! v with "[Hc]") as "Ho".
      { rewrite (ofile_lent_or_slot_in _ _ _ _ _ Hin). iFrame "Hc".
        iPureIntro. exact Hnz. }
      rewrite list_insert_id; [|exact Hfd]. iExact "Ho".
    - rewrite (ofile_lent_or_slot_out _ _ _ _ _ Hin) /ofile_slot.
      iDestruct "Hs" as "[Hc Hpay]". iFrame "Hc". iIntros "Hc".
      iDestruct ("Hback" $! v with "[Hc Hpay]") as "Ho".
      { rewrite (ofile_lent_or_slot_out _ _ _ _ _ Hin) /ofile_slot.
        iFrame "Hc Hpay". }
      rewrite list_insert_id; [|exact Hfd]. iExact "Ho".
  Qed.

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
  Lemma tf_page_length (tfp : mword 44) (ws : list (mword 64)) :
    tf_page tfp ws -∗ ⌜length ws = TFWORDS⌝.
  Proof. rewrite /tf_page. iIntros "(%Hlen & _ & _)". done. Qed.

  (* [tf_pa]'s address IS [pa_add (page_base tfp) off] -- same value, built
     via [bits_of_virtaddr]'s concat instead of [pa_add]'s addition -- so
     [tf_words]/[tf_tail] (below, addressed the two different ways their
     two construction paths need) still land on the same bytes.  Mirrors
     [Pt4kWalk.pte_addr_at_unsigned]'s derivation. *)
  Lemma tf_pa_unsigned (tfp : mword 44) (off : Z) :
    0 <= off < 4096 ->
    bv_unsigned (tf_pa tfp off) = bv_unsigned tfp * 4096 + off.
  Proof.
    intro Hoff. unfold tf_pa.
    rewrite zext64_concat44_12_unsigned.
    cbn [bits_of_virtaddr].
    rewrite subrange64_unsigned_11_0. change (2 ^ 12) with 4096.
    assert (Hmv : bv_unsigned (mword_of_int (TRAPFRAME + off) : mword 64) = TRAPFRAME + off).
    { unfold mword_of_int, Values.to_word, get_word. cbn.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      unfold bv_modulus. cbn. unfold TRAPFRAME. lia. }
    rewrite Hmv.
    assert (Htmod : (TRAPFRAME + off) mod 4096 = off).
    { unfold TRAPFRAME. rewrite <- Z.add_mod_idemp_l; [| lia].
      replace (0x3FFFFFE000 mod 4096) with 0 by (vm_compute; reflexivity).
      rewrite Z.add_0_l. apply Z.mod_small. lia. }
    rewrite Htmod. reflexivity.
  Qed.

  Lemma tf_pa_eq_pa_add (tfp : mword 44) (off : nat) :
    (off < 4096)%nat ->
    tf_pa tfp (Z.of_nat off) = pa_add (page_base tfp) off.
  Proof.
    intro Hoff. apply bv_eq.
    rewrite (tf_pa_unsigned tfp (Z.of_nat off) ltac:(lia)).
    symmetry. exact (pa_add_page_unsigned tfp off ltac:(lia)).
  Qed.

  (* the [8 * Z.of_nat i] (Z-mult, [tf_words]'s own index shape) vs
     [Z.of_nat (8 * i)] (nat-mult then cast, [tf_pa_eq_pa_add]'s own) forms
     are propositionally but not syntactically equal, which defeats a bare
     [rewrite] at either call site below -- fold that mismatch into ONE
     lemma instead of chasing it at each one. *)
  Lemma tf_pa_eq_pa_add8 (tfp : mword 44) (i : nat) :
    (i < 512)%nat ->
    tf_pa tfp (8 * Z.of_nat i) = pa_add (page_base tfp) (8 * i)%nat.
  Proof.
    intro Hi. rewrite <- (tf_pa_eq_pa_add tfp (8 * i) ltac:(lia)).
    f_equal. lia.
  Qed.

  (* [a_tf_word]: the pre-physical-native WORD-INDEXED address helper, kept
     as a plain arithmetic alias (not a resource predicate any more -- that
     role is [tf_pa]'s, via [tf_words]) purely so callers stating a REGISTER
     VALUE equals "the trapframe's i-th word's address" (kfork's copy loop,
     kexec's argv walk) don't have to carry a [Z.of_nat]/[8 *] conversion at
     every call site. Its VALUE is the same formula it always was, so a
     caller that already unfolds it (as several do, for the arithmetic
     underneath) is unaffected -- see [tf_pa_eq_pa_add8] for the bridge to
     [tf_pa] when one is needed. *)
  Definition a_tf_word (tfp : mword 44) (i : nat) : Arch.pa :=
    pa_add (page_base tfp) (8 * i).

  (* THE BRIDGE a caller needs when it has an [a_tf_word]-shaped fact (its
     own premise, stated that way) but is calling into a [tf_pa]-shaped
     lemma (every physical-native one now is) -- one [rewrite] instead of
     re-deriving [tf_pa_eq_pa_add8] at the call site. *)
  Lemma a_tf_word_eq_tf_pa (tfp : mword 44) (i : nat) :
    (i < 512)%nat ->
    a_tf_word tfp i = tf_pa tfp (8 * Z.of_nat i).
  Proof. intro Hi. rewrite /a_tf_word (tf_pa_eq_pa_add8 tfp i Hi). reflexivity. Qed.

  (* CONSTRUCTION: what [kalloc] hands allocproc IS a trapframe page.  The 36
     struct words come out with EXISTENTIAL contents (a fresh page's bytes are
     arbitrary), and the 3808-byte tail is exactly the window [tf_tail] owns
     anonymously.  Both cross to the physical tier ONCE, via the whole-page
     [ProcPtOwn.page_own_to_phys] -- the same [kmap_static_claims] every
     other kalloc'd page uses, no new per-page claim needed. *)
  Lemma tf_page_of_page_own (tfp : mword 44) :
    page_valid (page_base tfp) ->
    kmap_static_claims -∗ page_own (page_base tfp) -∗ ∃ ws : list (mword 64), tf_page tfp ws.
  Proof.
    iIntros (Hpv) "#Hb Hp".
    iDestruct (page_own_to_phys tfp Hpv with "Hb Hp") as "Hp".
    rewrite /phys_page_own.
    replace 4096%nat with (8 * TFWORDS + 3808)%nat by (vm_compute; reflexivity).
    rewrite (phys_bwin_split (page_base tfp) 0 (8 * TFWORDS) 3808).
    iDestruct "Hp" as "[Hpre Htail]".
    iDestruct (phys_page_words8 (page_base tfp) TFWORDS Hpv ltac:(vm_compute; lia)
                 with "Hpre") as (ws) "[%Hlen Hws]".
    iExists ws. rewrite /tf_page /tf_words /tf_tail.
    iSplit; [done|]. iSplitL "Hws".
    - iApply (big_sepL_impl with "Hws"). iIntros "!>" (i w Hi) "Hw".
      assert (Hilt : (i < TFWORDS)%nat) by (rewrite -Hlen; apply lookup_lt_is_Some_1; eauto).
      rewrite (tf_pa_eq_pa_add8 tfp i ltac:(unfold TFWORDS in Hilt; lia)). iExact "Hw".
    - rewrite Nat.add_0_l.
      replace (Z.to_nat TFBYTES) with (8 * TFWORDS)%nat by (vm_compute; reflexivity).
      replace (4096 - Z.to_nat TFBYTES)%nat with 3808%nat by (vm_compute; reflexivity).
      rewrite /phys_byte_any. iExact "Htail".
  Qed.

  (* DESTRUCTION, the converse: freeproc hands the page back to kfree, which
     wants the 4096 anonymous bytes and nothing else.  The struct words and
     the tail forget their contents and rejoin, then cross back mem-tier
     once via [ProcPtOwn.phys_to_page_own]. *)
  Lemma tf_page_to_page_own (tfp : mword 44) (ws : list (mword 64)) :
    page_valid (page_base tfp) ->
    kmap_static_claims -∗ tf_page tfp ws -∗ page_own (page_base tfp).
  Proof.
    intro Hpv. rewrite /tf_page /tf_words /tf_tail.
    iIntros "#Hb (%Hlen & Hws & Htail)".
    iApply (phys_to_page_own tfp Hpv with "Hb").
    rewrite /phys_page_own.
    replace 4096%nat with (8 * TFWORDS + 3808)%nat by (vm_compute; reflexivity).
    rewrite (phys_bwin_split (page_base tfp) 0 (8 * TFWORDS) 3808).
    iSplitL "Hws".
    - rewrite -Hlen. iApply (phys_page_words8_back (page_base tfp) ws).
      iApply (big_sepL_impl with "Hws"). iIntros "!>" (i w Hi) "Hw".
      assert (Hilt : (i < TFWORDS)%nat) by (rewrite -Hlen; apply lookup_lt_is_Some_1; eauto).
      rewrite <- (tf_pa_eq_pa_add8 tfp i ltac:(unfold TFWORDS in Hilt; lia)). iExact "Hw".
    - rewrite Nat.add_0_l.
      replace (8 * TFWORDS)%nat with (Z.to_nat TFBYTES) by (vm_compute; reflexivity).
      replace 3808%nat with (4096 - Z.to_nat TFBYTES)%nat by (vm_compute; reflexivity).
      rewrite /phys_byte_any. iExact "Htail".
  Qed.

  (* borrow one trapframe word, at the PHYSICAL tier -- the nth syscall
     argument is [tf_arg_idx n].  No tier crossing: [tf_words] is already
     physical, so this is a plain [big_sepL] borrow. *)
  Lemma tf_page_word (tfp : mword 44) (ws : list (mword 64)) (i : nat) (w : mword 64) :
    ws !! i = Some w ->
    tf_page tfp ws -∗
    tf_pa tfp (8 * Z.of_nat i) ↦ₚ₈ w ∗
    (tf_pa tfp (8 * Z.of_nat i) ↦ₚ₈ w -∗ tf_page tfp ws).
  Proof.
    rewrite /tf_page. iIntros (Hi) "(%Hlen & Hws & Htail)".
    iDestruct (big_sepL_lookup_acc _ _ i w Hi with "Hws") as "[$ Hback]".
    iIntros "Hc". iSplit; [done|]. iSplitL "Hc Hback"; [rewrite /tf_words; iApply ("Hback" with "Hc") | iExact "Htail"].
  Qed.

  (* THE WRITE TWIN: borrow the cell and put back a DIFFERENT word, the page
     re-indexed at [<[i := w']> ws].  [tf_page_word] above cannot serve -- its
     wand demands the old value back -- and every trapframe WRITER needs this
     one: prepare_return's four kernel slots, syscall's a0, uservec's saves.
     The length side condition survives by [insert_length], so the page's own
     [⌜length ws = TFWORDS⌝ ] is re-established with no arithmetic. *)
  Lemma tf_page_word_upd (tfp : mword 44) (ws : list (mword 64)) (i : nat) (w : mword 64) :
    ws !! i = Some w ->
    tf_page tfp ws -∗
    tf_pa tfp (8 * Z.of_nat i) ↦ₚ₈ w ∗
    (∀ w' : mword 64, tf_pa tfp (8 * Z.of_nat i) ↦ₚ₈ w' -∗ tf_page tfp (<[i := w']> ws)).
  Proof.
    rewrite /tf_page. iIntros (Hi) "(%Hlen & Hws & Htail)".
    iDestruct (big_sepL_insert_acc _ _ i w Hi with "Hws") as "[$ Hback]".
    iIntros (w') "Hc". iSplit.
    { iPureIntro. rewrite length_insert. exact Hlen. }
    iSplitL "Hc Hback"; [rewrite /tf_words; iApply ("Hback" with "Hc") | iExact "Htail"].
  Qed.

  (* THE PHYSICAL<->MEM WORD BRIDGE for one trapframe slot -- the mirror of
     [KptTree.pt_slot_phys_to_mem]/[pt_slot_mem_to_phys] for PT slots,
     re-addressed at [tf_pa] instead of [u_pte_addr].  [pt_node_claim]
     itself is fully generic over any identity-mapped kdata page (its own
     [pt_page_vpn] is just [svpn_of (page_base _)]) -- the trapframe page IS
     one (a kalloc'd page, per [tf_page_of_page_own]/[tf_page_to_page_own]
     above), so [PtTree.pt_node_claim_from_static tfp] supplies it from the
     same [kmap_static_claims] every other kalloc'd page uses, no new
     per-page claim needed.  Used ONLY by the handful of KERNEL-SIDE
     (identity-map) readers/writers that still want the mem tier --
     prepare_return's four kernel-word writes and one epc read, the
     syscall argument fetchers, kfork's copy loop -- composed with
     [tf_page_word]/[tf_page_word_upd] below into
     [tf_page_word_mem]/[tf_page_word_upd_mem].  Uservec/userret themselves
     never need this: their own [tf_pa] cells already match [tf_words]
     natively, so uservec's tail simply opens [usertrap_res]'s [tf_page]
     (SpecUsertrap.usertrap_res_tf_open) straight into them and reseals
     before handing off to usertrap -- see SpecUservec.v's header and
     claude-notes/completed/usertrap.md. *)
  Lemma tf_pa_aligned8 (tfp : mword 44) (i : nat) :
    (i < 512)%nat ->
    is_aligned_paddr (Physaddr (tf_pa tfp (8 * Z.of_nat i))) 8 = true.
  Proof.
    intro Hi. unfold is_aligned_paddr. apply Z.eqb_eq.
    rewrite uint_unsigned (tf_pa_unsigned tfp (8 * Z.of_nat i) ltac:(lia)).
    replace (bv_unsigned tfp * 4096 + 8 * Z.of_nat i)
      with ((bv_unsigned tfp * 512 + Z.of_nat i) * 8) by lia.
    apply Z.rem_mul. lia.
  Qed.

  (* the facts [phys_to_mem_claim]/[mem_to_phys_claim] need of a trapframe
     slot -- the mirror of [KptTree.u_pte_slot_facts] *)
  Lemma tf_pa_slot_facts (tfp : mword 44) (i j : nat) :
    node_kdata tfp -> (i < 512)%nat -> (j < 8)%nat ->
    pa_of tfp (pa_add (tf_pa tfp (8 * Z.of_nat i)) j) = pa_add (tf_pa tfp (8 * Z.of_nat i)) j /\
    addr_is_ram (pa_add (tf_pa tfp (8 * Z.of_nat i)) j) /\
    (uint (pa_add (tf_pa tfp (8 * Z.of_nat i)) j) < 274877906944)%Z /\
    svpn_of (pa_add (tf_pa tfp (8 * Z.of_nat i)) j) = pt_page_vpn tfp.
  Proof.
    intros [Hklo Hkhi] Hi Hj.
    pose proof (bv_unsigned_in_range _ tfp) as [Htlo Hthi].
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416)
      by (vm_compute; reflexivity).
    rewrite Hm in Hthi.
    assert (Hpaij : bv_unsigned (pa_add (tf_pa tfp (8 * Z.of_nat i)) j)
                   = bv_unsigned tfp * 4096 + 8 * Z.of_nat i + Z.of_nat j).
    { unfold pa_add. rewrite pt_add_vec_int_small.
      - rewrite (tf_pa_unsigned tfp (8 * Z.of_nat i) ltac:(lia)). reflexivity.
      - lia.
      - rewrite (tf_pa_unsigned tfp (8 * Z.of_nat i) ltac:(lia)). lia. }
    unfold node_kdata, ram_base, ram_size in Hklo, Hkhi.
    assert (Hram : addr_is_ram (pa_add (tf_pa tfp (8 * Z.of_nat i)) j)).
    { unfold addr_is_ram, ram_base, ram_size. rewrite uint_unsigned Hpaij. lia. }
    assert (Hcanpa : (uint (pa_add (tf_pa tfp (8 * Z.of_nat i)) j) < 274877906944)%Z).
    { rewrite uint_unsigned Hpaij. lia. }
    assert (Ha0 : bv_unsigned (u_pte_addr tfp (mword_of_int 0)) = bv_unsigned tfp * 4096).
    { rewrite (pte_addr_at_unsigned tfp (mword_of_int 0)).
      replace (bv_unsigned (mword_of_int 0 : mword 9)) with 0 by (vm_compute; reflexivity). lia. }
    assert (Hcana0 : (uint (u_pte_addr tfp (mword_of_int 0)) < 274877906944)%Z).
    { rewrite uint_unsigned Ha0. lia. }
    split; [| split; [exact Hram | split; [exact Hcanpa |]]].
    - (* pa_of tfp (pa_add a j) = pa_add a j *)
      apply bv_eq. unfold pa_of. rewrite zext64_concat44_12_unsigned.
      rewrite subrange64_unsigned_11_0. change (2 ^ 12) with 4096.
      rewrite Hpaij.
      replace (bv_unsigned tfp * 4096 + 8 * Z.of_nat i + Z.of_nat j)
        with ((8 * Z.of_nat i + Z.of_nat j) + bv_unsigned tfp * 4096) by lia.
      rewrite Z_mod_plus_full.
      rewrite (Z.mod_small (8 * Z.of_nat i + Z.of_nat j) 4096 ltac:(lia)). lia.
    - (* svpn_of (pa_add a j) = pt_page_vpn tfp *)
      apply bv_eq.
      assert (Hlo1 : bv_unsigned (svpn_of (pa_add (tf_pa tfp (8 * Z.of_nat i)) j))
                    = Z.shiftr (bv_unsigned tfp * 4096 + 8 * Z.of_nat i + Z.of_nat j) 12).
      { rewrite (svpn_of_unsigned_lo (pa_add (tf_pa tfp (8 * Z.of_nat i)) j) Hcanpa).
        rewrite uint_unsigned. rewrite Hpaij. reflexivity. }
      assert (Hlo2 : bv_unsigned (pt_page_vpn tfp) = Z.shiftr (bv_unsigned tfp * 4096) 12).
      { unfold pt_page_vpn.
        rewrite (svpn_of_unsigned_lo (u_pte_addr tfp (mword_of_int 0)) Hcana0).
        rewrite uint_unsigned. rewrite Ha0. reflexivity. }
      rewrite Hlo1 Hlo2.
      rewrite !Z.shiftr_div_pow2; [| lia | lia]. change (2 ^ 12) with 4096.
      assert (Hsmall : (bv_unsigned tfp * 4096 + 8 * Z.of_nat i + Z.of_nat j) / 4096 = bv_unsigned tfp).
      { rewrite <- Z.add_assoc. rewrite Z.div_add_l; [| lia].
        rewrite (Z.div_small (8 * Z.of_nat i + Z.of_nat j) 4096 ltac:(lia)). lia. }
      rewrite Hsmall.
      symmetry. apply Z.div_mul. lia.
  Qed.

  Lemma tf_word_phys_to_mem (tfp : mword 44) (i : nat) (dq : dfrac) (w : mword 64) :
    (i < 512)%nat ->
    pt_node_claim tfp -∗
    tf_pa tfp (8 * Z.of_nat i) ↦ₚ₈{dq} w -∗
    tf_pa tfp (8 * Z.of_nat i) ↦₈{dq} w.
  Proof.
    iIntros (Hi) "(%Hkd & %Hpv & #Hk) Hw".
    iApply ctx_word_pointsto_intro; [exact (tf_pa_aligned8 tfp i Hi) |].
    iDestruct (phys_word_pointsto_bytes with "Hw") as "Hbs".
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k j Hkj) "Hp".
    apply lookup_seq in Hkj. destruct Hkj as [-> Hjlt].
    destruct (tf_pa_slot_facts tfp i (0 + k)%nat Hkd Hi ltac:(lia)) as (Hid & Hram & Hcan & Hsvpn).
    iAssert (kmap_at (svpn_of (pa_add (tf_pa tfp (8 * Z.of_nat i)) (0 + k))) tfp KP_rw) as "#Hk'".
    { rewrite Hsvpn. iExact "Hk". }
    iApply TsoCtxShim.ctx_pointsto_of_mem.
    iApply (phys_to_mem_claim (pa_add (tf_pa tfp (8 * Z.of_nat i)) (0 + k)) tfp dq (nth_byte w (0 + k))
              Hid Hram Hcan with "Hk' Hp").
  Qed.

  Lemma tf_word_mem_to_phys (tfp : mword 44) (i : nat) (dq : dfrac) (w : mword 64) :
    (i < 512)%nat ->
    pt_node_claim tfp -∗
    tf_pa tfp (8 * Z.of_nat i) ↦₈{dq} w -∗
    tf_pa tfp (8 * Z.of_nat i) ↦ₚ₈{dq} w.
  Proof.
    iIntros (Hi) "(%Hkd & %Hpv & #Hk) Hw".
    iApply phys_word_pointsto_intro; [exact (tf_pa_aligned8 tfp i Hi) |].
    iDestruct (ctx_word_pointsto_bytes with "Hw") as "Hbs".
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k j Hkj) "Hp".
    apply lookup_seq in Hkj. destruct Hkj as [-> Hjlt].
    destruct (tf_pa_slot_facts tfp i (0 + k)%nat Hkd Hi ltac:(lia)) as (Hid & _ & _ & Hsvpn).
    iAssert (kmap_at (svpn_of (pa_add (tf_pa tfp (8 * Z.of_nat i)) (0 + k))) tfp KP_rw) as "#Hk'".
    { rewrite Hsvpn. iExact "Hk". }
    iDestruct (TsoCtxShim.ctx_pointsto_to_mem with "Hp") as "Hp".
    iApply (mem_to_phys_claim (pa_add (tf_pa tfp (8 * Z.of_nat i)) (0 + k)) tfp dq (nth_byte w (0 + k))
              Hid with "Hk' Hp").
  Qed.

  (* THE MEM-TIER CONVENIENCE PAIR: what prepare_return/the syscall argument
     fetchers/kfork's copy loop actually call -- [tf_page_word]/
     [tf_page_word_upd] (native physical) composed with the bridge above,
     so their OWN call sites are unchanged from before this file went
     physical-native (still borrow/return a [↦₈] cell). *)
  Lemma tf_page_word_mem (tfp : mword 44) (ws : list (mword 64)) (i : nat) (w : mword 64) :
    (i < 512)%nat -> ws !! i = Some w ->
    pt_node_claim tfp -∗
    tf_page tfp ws -∗
    tf_pa tfp (8 * Z.of_nat i) ↦₈ w ∗ (tf_pa tfp (8 * Z.of_nat i) ↦₈ w -∗ tf_page tfp ws).
  Proof.
    iIntros (Hi Hlk) "#Hk Ht".
    iDestruct (tf_page_word tfp ws i w Hlk with "Ht") as "[Hw Hback]".
    iDestruct (tf_word_phys_to_mem tfp i (DfracOwn 1) w Hi with "Hk Hw") as "Hw".
    iFrame "Hw". iIntros "Hw".
    iDestruct (tf_word_mem_to_phys tfp i (DfracOwn 1) w Hi with "Hk Hw") as "Hw".
    iApply ("Hback" with "Hw").
  Qed.

  Lemma tf_page_word_upd_mem (tfp : mword 44) (ws : list (mword 64)) (i : nat) (w : mword 64) :
    (i < 512)%nat -> ws !! i = Some w ->
    pt_node_claim tfp -∗
    tf_page tfp ws -∗
    tf_pa tfp (8 * Z.of_nat i) ↦₈ w ∗
    (∀ w' : mword 64, tf_pa tfp (8 * Z.of_nat i) ↦₈ w' -∗ tf_page tfp (<[i := w']> ws)).
  Proof.
    iIntros (Hi Hlk) "#Hk Ht".
    iDestruct (tf_page_word_upd tfp ws i w Hlk with "Ht") as "[Hw Hback]".
    iDestruct (tf_word_phys_to_mem tfp i (DfracOwn 1) w Hi with "Hk Hw") as "Hw".
    iFrame "Hw". iIntros (w') "Hw".
    iDestruct (tf_word_mem_to_phys tfp i (DfracOwn 1) w' Hi with "Hk Hw") as "Hw".
    iApply ("Hback" with "Hw").
  Qed.

  (* STATED AT THE PHYSICAL TIER, so uservec/userret's OWN low-level
     instruction lemmas (already physical, per [SpecUserret.tf_pa]) need no
     crossing to touch it.  The ONE crossing at construction/destruction
     (allocproc/freeproc, above) goes through the SAME whole-page
     [kmap_static_claims] every other kalloc'd page already needs, not a
     per-word one -- and the handful of kernel-side identity-map readers
     that still want the mem tier pay it per-word, via
     [tf_page_word_mem]/[tf_page_word_upd_mem] just above, using
     [pt_node_claim_from_static]'s own persistent claim (no LEAF-only
     [hw_config] opening needed at the read site: [pt_node_claim] is
     obtained ONCE, from the same boot-time bundle, and threaded in). *)

  (* =================================================================== *)
  (* THE resource that rides alongside [cur_proc p].                      *)
  (* =================================================================== *)
  (* [cwd]: p->cwd holds ONE WHOLE inode reference -- [IcacheRef.inode_held],
     the same predicate the last [fileclose] of an FD_INODE file recovers
     from its payload and hands to iput.  (C6b: this was [emp] while there
     was no inode model; design/proc-struct.md's "holes to be honest about"
     records the hole and design/fs-icache.md §3 the route out of it.)

     THERE IS NO [v = zero_reg] ARM, AND THAT IS THE POINT.  A null
     [p->cwd] is not a state this predicate describes -- it is a state in
     which the block does not hold this conjunct at all, which is what
     [proc_priv_nocwd] is for.  The two mechanisms are alternatives, not
     partners: with a null arm, [proc_priv] no longer implies
     [pv_cwd V <> 0], and every contract that reaches [iput(p->cwd)] --
     kexit, kfork, and their syscall wrappers -- has to carry that fact as
     a PREMISE its own callers must then supply.  Without one it is a
     PROJECTION of the block ([proc_priv_cwd_nonzero]), free at every
     altitude, and the construction window (allocproc's return, kfork's
     150 bytes before the [sd a0,336(s4)], kexit's tail after [iput]) is
     covered by the deficit block instead.

     That matters beyond tidiness because of WHERE the fact would have to
     travel: [SchedCtx.proc_slots_recast] moves SLEEPING -> RUNNABLE ->
     RUNNING for free, and stays free only because [proc_slots] mentions
     neither [proc_ctx]'s nor [proc_dormant]'s contents.  A [cwd <> 0]
     conjunct anywhere near it would break exactly that; as a projection it
     rides inside the Löb'd obligation and no recast ever looks at it. *)
  Definition cwd_ref (v : mword 64) : iProp Σ := inode_held v.

  (* The two directions, kept as NAMES so consumers do not unfold: they are
     definitional now, but they were not, and the call sites read better
     for saying which way they are going. *)
  Lemma cwd_ref_held (v : mword 64) : cwd_ref v -∗ inode_held v.
  Proof. iIntros "$". Qed.

  Lemma cwd_ref_of_held (v : mword 64) : inode_held v -∗ cwd_ref v.
  Proof. iIntros "$". Qed.

  (* ... and the projection the missing arm buys. *)
  Lemma cwd_ref_nonzero (v : mword 64) :
    cwd_ref v -∗ ⌜v <> (zero_reg : mword 64)⌝.
  Proof. iIntros "H". by iApply (inode_held_ne_zero with "H"). Qed.

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
  (* THE BLOCK MINUS THE FD TABLE.  Split out because the fd table is the one
     component a syscall may have to hold in a NON-[proc_ofiles] state (a
     payload on loan, see [proc_ofiles_owe] above) while still handing the rest
     of the block to a callee.  A deficit block is not [proc_priv ∗ anything] --
     the cell of a lent descriptor names a file and [ofile_slot] then demands
     the missing reference, so there is no frame lemma to be had -- and making
     every [proc_priv]-taking spec generic in the deficit set would be the
     wrong shape.  Splitting HERE costs nothing instead: the callees that must
     be callable across a loan (piperead / pipewrite / fileread / filewrite /
     filestat) never touch the descriptor array at all, so they take
     [proc_priv_core] and the caller keeps its own fd-table term.  [fdalloc] is
     the single exception, and it takes the deficit set explicitly.

     No [γf]: the core is exactly the part with no file-layer content.

     ---- THE LAST CONJUNCT IS [FirstTok.first_tok] ---------------------
     proc.c's [static int first], as a resource the PROCESS carries: either
     the exclusive boot arm (the pinned [first_addr ↦₄ 1] cell, main's
     sixteen persistent rows, the sealed page count and fsinit's whole
     premise pile) or the persistent steady arm ([first_addr ↦₄□ 0] beside
     [FsReady.fs_ready]).  It lives HERE, in the block, because forkret --
     the branch's only reader -- runs on a context a park saved, and the
     block is the only thing a parked process still owns.  "At most one
     process ever runs the boot arm" is then a theorem about ownership: the
     two arms are incompatible at one address, so no second block can hold
     the exclusive one.

     WHY IT IS NOT IN [proc_priv_nocwd].  allocproc does not return a
     process in a RUNNABLE or SLEEPING state -- kfork holds its result for
     150 bytes before the [sd a0,336(s4)] that installs the cwd -- so a
     contract at the deficit block must not have to PRODUCE a token.  The
     deficit block is exactly the pre-park shape, and the token joins at the
     same seam the working directory does ([proc_priv_split_cwd] is
     three-way for that reason). *)
  Definition proc_priv_core (pa : mword 64) (pid : mword 32) (V : pprivate) : iProp Σ :=
    (⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
     ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
     p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) V ∗
     proc_pt_at pa (pv_upt V) ∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
     cwd_ref (pv_cwd V) ∗
     first_tok)%I.

  (* ...AND ITS FILE-LAYER-FREE PART, WHICH IS WHAT THE BLOCK LAYER TAKES.
     [ProcDefs.proc_priv_bare] is this minus [cwd_ref]; the note at its
     definition says why the sleeplock/buffer-cache chain must not be handed
     anything that mentions an inode reference.  An [⊣⊢], so a caller splits
     and rejoins with a rewrite -- no borrow and no closer to carry. *)
  Lemma proc_priv_core_bare (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V ⊣⊢
    proc_priv_bare pa pid V ∗ cwd_ref (pv_cwd V) ∗ first_tok.
  Proof.
    rewrite /proc_priv_core /proc_priv_bare. iSplit.
    - iIntros "(%A & %B & Hpid & Hf & Hpt & Htfp & Hc & Hft)".
      iFrame "Hc Hft Hpid Hf Hpt Htfp". iSplitR; [done|]. done.
    - iIntros "[(%A & %B & Hpid & Hf & Hpt & Htfp) [Hc Hft]]".
      iFrame "Hpid Hf Hpt Htfp Hc Hft". iSplitR; [done|]. done.
  Qed.

  (* THE BORROW FORM.  Every fs callee below the file layer -- bread, bmap,
     ilock, begin_op, ... -- asks for [proc_priv_bare], never for a fraction
     of [p->pid]; a caller holding the full block lends the bare part for the
     length of the call and takes it back.  Only [cwd_ref] stays behind, and
     nothing under the file layer wants it. *)
  Lemma proc_priv_core_bare_acc (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗
    proc_priv_bare pa pid V ∗ (proc_priv_bare pa pid V -∗ proc_priv_core pa pid V).
  Proof.
    rewrite proc_priv_core_bare. iIntros "[Hb [Hc Hft]]".
    iSplitL "Hb"; [iExact "Hb"|]. iIntros "Hb". iFrame.
  Qed.

  Definition proc_priv (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) : iProp Σ :=
    (proc_priv_core pa pid V ∗ proc_ofiles γf pa (pv_ofile V))%I.

  (* ---- THE CONSTRUCTION WINDOW -------------------------------------
     [cwd_ref] has no null arm, so a process whose [p->cwd] is still 0 does
     not satisfy [proc_priv] -- and allocproc returns exactly such a
     process, which kfork then holds for 150 bytes before its
     [sd a0,336(s4)].  So the reference SPLITS OFF, the same move S4c made
     for the fd table: a block with a deficit is not [proc_priv ∗ anything],
     so split at the component the callee does not touch.

     Note this splits only the REFERENCE, not the [p_cwd] CELL: the cell
     stays inside [proc_fields], so [proc_dormant], [SpecFreeproc] and every
     other consumer of [proc_fields] is untouched.  A holder of the deficit
     block still owns the cell and writes it with
     [proc_priv_nocwd_cwd]. *)
  Definition proc_priv_nocwd (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) : iProp Σ :=
    (⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
     ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
     p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) V ∗
     proc_pt_at pa (pv_upt V) ∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
     proc_ofiles γf pa (pv_ofile V))%I.

  (* THREE-WAY since the token joined the block.  The deficit block is the
     PRE-PARK shape -- what allocproc returns -- and neither the working
     directory nor [FirstTok.first_tok] is installed yet, so both split off
     at the same seam and rejoin at the same store. *)
  Lemma proc_priv_split_cwd (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V ⊣⊢
    proc_priv_nocwd γf pa pid V ∗ cwd_ref (pv_cwd V) ∗ first_tok.
  Proof.
    rewrite /proc_priv /proc_priv_core /proc_priv_nocwd.
    iSplit.
    - iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
      iFrame "Hc Hft". iSplitR; [done|]. iSplitR; [done|]. iFrame.
    - iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho) [Hc Hft]]".
      iSplitR "Ho"; [|iExact "Ho"].
      iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* ...and the same borrow one layer up, for a caller holding the WHOLE
     block.  [proc_ofiles] and [cwd_ref] stay behind; nothing under the file
     layer wants either. *)
  Lemma proc_priv_bare_acc (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗
    proc_priv_bare pa pid V ∗ (proc_priv_bare pa pid V -∗ proc_priv γf pa pid V).
  Proof.
    rewrite /proc_priv proc_priv_core_bare. iIntros "[[Hb [Hc Hft]] Ho]".
    iSplitL "Hb"; [iExact "Hb"|]. iIntros "Hb". iFrame.
  Qed.

  (* THE cwd-DEFICIT BLOCK IS THE BARE BLOCK PLUS THE FD TABLE.  Both sides
     spell the same six conjuncts in the same order, so this is a regrouping
     and not a transfer. *)
  Lemma proc_priv_nocwd_bare (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nocwd γf pa pid V ⊣⊢
    proc_priv_bare pa pid V ∗ proc_ofiles γf pa (pv_ofile V).
  Proof.
    rewrite /proc_priv_nocwd /proc_priv_bare. iSplit.
    - iIntros "(%A & %B & Hpid & Hf & Hpt & Htfp & Ho)".
      iFrame "Ho Hpid Hf Hpt Htfp". iSplitR; [done|]. done.
    - iIntros "[(%A & %B & Hpid & Hf & Hpt & Htfp) Ho]".
      iFrame "Hpid Hf Hpt Htfp Ho". iSplitR; [done|]. done.
  Qed.


  (* ---- THE ADDRESS-SPACE SPLIT --------------------------------------
     THE BLOCK MINUS THE PAGE TABLE.  Split out for the reason the fd
     table and the cwd reference above were, one tier further out: the
     one window in which a live process's block is NOT complete is user
     execution, where the address space is INSTALLED (satp points at it,
     [UserPtTree.user_pt_inv] owns it) rather than parked.  A kernel-side
     residue that must survive that window therefore cannot contain
     [proc_pt] -- holding both is [ptree_own 2 (DfracOwn 1)] and the user
     pages claimed TWICE, i.e. an unsatisfiable precondition and a vacuous
     lemma, which is exactly the trap the uservec boundary fell into (see
     claude-notes/projects/uservec.md).

     The two [struct proc] CELLS stay: [p->pagetable] / [p->trapframe] are
     ordinary kernel words that merely NAME the table, and the kernel owns
     them straight through user execution.  So does the trapframe page --
     [tf_page] is at the tier-neutral physical tier and user mode cannot
     reach it (its leaf has U = 0), so it is residue, not address space.
     What leaves is [proc_pt] and nothing else. *)
  Definition proc_priv_nopt (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) : iProp Σ :=
    (⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
     ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
     p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) V ∗
     proc_pt_cells pa (pv_upt V) ∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
     cwd_ref (pv_cwd V) ∗
     proc_ofiles γf pa (pv_ofile V) ∗
     first_tok)%I.

  Lemma proc_priv_split_pt (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V ⊣⊢ proc_priv_nopt γf pa pid V ∗ proc_pt (pv_upt V).
  Proof.
    rewrite /proc_priv /proc_priv_core /proc_priv_nopt proc_pt_at_split
            /proc_pt_cells.
    iSplit.
    - iIntros "[(%Hszb & %Hbel & Hpid & Hf & ((Hc1 & Hc2) & Hpt) & Htfp & Hc & Hft) Ho]".
      iFrame "Hpt". iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hpid Hf Hc1 Hc2 Htfp Hc Ho Hft".
    - iIntros "[(%Hszb & %Hbel & Hpid & Hf & (Hc1 & Hc2) & Htfp & Hc & Ho & Hft) Hpt]".
      iFrame "Ho". iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hpid Hf Hc1 Hc2 Hpt Htfp Hc Hft".
  Qed.

  (* THE TRAPFRAME BORROW at the reduced block -- same statement as
     [UsertrapRes.proc_priv_tf_open], which is where the complete block's
     version lives; this one is what a residue that has already given up
     its page table opens. *)
  Lemma proc_priv_nopt_tf_open (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nopt γf pa pid V -∗
    ∃ ws : list (mword 64), ⌜ws = pv_tf V⌝ ∗ tf_page (ud_tfp (pv_upt V)) ws ∗
      (∀ ws' : list (mword 64), tf_page (ud_tfp (pv_upt V)) ws' -∗
         proc_priv_nopt γf pa pid (upd_tf V ws')).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hc & Htfp & Hcwd & Ho & Hft)".
    iExists (pv_tf V). iSplitR; [done|]. iFrame "Htfp".
    iIntros (ws') "Htfp".
    (* every field [upd_tf] does not touch is equal by a single iota step;
       name them so the goal reduces by [rewrite] rather than by a blind
       [iFrame] match against an opaque [upd_tf V ws'] -- the same hazard
       [proc_priv_tf_open] documents. *)
    assert (Heq1 : pv_sz (upd_tf V ws') = pv_sz V) by reflexivity.
    assert (Heq2 : pv_upt (upd_tf V ws') = pv_upt V) by reflexivity.
    assert (Heq3 : pv_ofile (upd_tf V ws') = pv_ofile V) by reflexivity.
    assert (Heq4 : pv_cwd (upd_tf V ws') = pv_cwd V) by reflexivity.
    assert (Heq6 : pv_tf (upd_tf V ws') = ws') by reflexivity.
    assert (Heq7 : proc_fields pa (DfracOwn 1) (upd_tf V ws')
                   = proc_fields pa (DfracOwn 1) V) by reflexivity.
    rewrite /proc_priv_nopt Heq1 Heq2 Heq3 Heq4 Heq6 Heq7.
    iSplitR; [done|]. iSplitR; [done|].
    iFrame "Hpid Hf Hc Htfp Hcwd Ho Hft".
  Qed.

  (* THE FOOTPRINT FIELD IS INVISIBLE HERE.  The reduced block reads
     [pv_upt V] only through [ud_root] / [ud_tfp] / [ud_um]; [ud_data] is
     the derived footprint ([ProcPtOwn.ud_pas]) that only the user tier
     names.  So a residue keyed on a descriptor may be RENORMALISED
     ([ProcPtOwn.ud_norm]) for free -- which is what lets the trap loop
     hand the user tier a descriptor whose coverage side condition holds
     by construction while the kernel side keeps the one it had. *)
  Lemma proc_priv_nopt_upt_irrel (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (Q : uptd) :
    ud_root (pv_upt V) = ud_root Q ->
    ud_tfp (pv_upt V) = ud_tfp Q ->
    ud_um (pv_upt V) = ud_um Q ->
    proc_priv_nopt γf pa pid V ⊣⊢ proc_priv_nopt γf pa pid (upd_upt V Q).
  Proof.
    intros Hr Ht Hu.
    assert (Heq1 : pv_sz (upd_upt V Q) = pv_sz V) by reflexivity.
    assert (Heq2 : pv_upt (upd_upt V Q) = Q) by reflexivity.
    assert (Heq3 : pv_ofile (upd_upt V Q) = pv_ofile V) by reflexivity.
    assert (Heq4 : pv_cwd (upd_upt V Q) = pv_cwd V) by reflexivity.
    assert (Heq6 : pv_tf (upd_upt V Q) = pv_tf V) by reflexivity.
    assert (Heq7 : proc_fields pa (DfracOwn 1) (upd_upt V Q)
                   = proc_fields pa (DfracOwn 1) V) by reflexivity.
    rewrite /proc_priv_nopt Heq1 Heq2 Heq3 Heq4 Heq6 Heq7 /proc_pt_cells.
    rewrite -Hr -Ht -Hu. reflexivity.
  Qed.

  (* the deficit block's [p->cwd] CELL, borrowed and replaced -- what the
     [sd] that installs a working directory needs.  [proc_priv_cwd] cannot
     serve: it hands out the reference too, and during the window there is
     none. *)
  Lemma proc_priv_nocwd_cwd (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nocwd γf pa pid V -∗
    p_cwd pa ↦₈ pv_cwd V ∗
    (∀ v' : mword 64,
       p_cwd pa ↦₈ v' -∗ proc_priv_nocwd γf pa pid (upd_cwd V v')).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho)".
    rewrite /proc_fields. iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iFrame "Hcwd". iIntros (v') "Hcwd".
    rewrite /proc_priv_nocwd /proc_fields.
    cbn [upd_cwd pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR; [done|]. iSplitR; [done|]. iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro; exact Hnl. }
    iFrame.
  Qed.

  (* the cwd cell AND the pid quarter out of the deficit block, because
     kexit needs both at once and for [proc_priv_cwd_pid]'s reason: begin_op
     / iput / end_op each take [p_pid pa ↦₄{dq} _], while the cwd cell has
     to stay out across all three -- from the [ld a0,336(s3)] that reads the
     pointer iput destroys to the [sd x0,336(s3)] that clears it.  kexit
     splits the REFERENCE off first ([proc_priv_split_cwd]) and spends it,
     so what it holds across the call is the deficit block; this is the
     accessor at that altitude. *)
  Lemma proc_priv_nocwd_cwd_pid (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nocwd γf pa pid V -∗
    p_cwd pa ↦₈ pv_cwd V ∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    (∀ v' : mword 64,
       p_cwd pa ↦₈ v' -∗ p_pid pa ↦₄{DfracOwn (1/4)} pid -∗
       proc_priv_nocwd γf pa pid (upd_cwd V v')).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho)".
    rewrite /proc_fields. iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]".
    iFrame "Hcwd Hq1". iIntros (v') "Hcwd Hq1".
    rewrite /proc_priv_nocwd /proc_fields.
    cbn [upd_cwd pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR; [done|]. iSplitR; [done|].
    rewrite Hq word4_pointsto_frac_split. iFrame "Hq1 Hq2".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro; exact Hnl. }
    iFrame.
  Qed.

  (* and the deficit block's own projections, for a holder that has not yet
     installed a cwd.  (The [pv_cwd V <> 0] projection is NOT among them --
     during the window it is false.) *)
  Lemma proc_priv_nocwd_ofile_len (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nocwd γf pa pid V -∗ ⌜length (pv_ofile V) = NOFILE⌝.
  Proof. iIntros "(_ & _ & _ & _ & _ & _ & [%Hlen _])". done. Qed.

  Lemma proc_priv_nocwd_sz_maxsz (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nocwd γf pa pid V -∗ ⌜uint (pv_sz V) <= uvm_maxsz⌝.
  Proof. iIntros "(%Hszb & _)". done. Qed.

  Lemma proc_priv_nocwd_um_below (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nocwd γf pa pid V -∗ ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝.
  Proof. iIntros "(_ & %Hbel & _)". done. Qed.

  Lemma proc_priv_nocwd_pid (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv_nocwd γf pa pid V -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    (p_pid pa ↦₄{DfracOwn (1/4)} pid -∗ proc_priv_nocwd γf pa pid V).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iIntros "Hq1". rewrite /proc_priv_nocwd Hq word4_pointsto_frac_split.
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  Lemma proc_priv_nocwd_ofile (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    proc_priv_nocwd γf pa pid V -∗
    ofile_slot γf pa fd v ∗
    (∀ v', ofile_slot γf pa fd v' -∗
       proc_priv_nocwd γf pa pid (upd_ofile V fd v')).
  Proof.
    iIntros (Hfd) "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & [%Hlen Ho])".
    iDestruct (big_sepL_insert_acc with "Ho") as "[$ Hback]"; first exact Hfd.
    iIntros (v') "Hslot". iDestruct ("Hback" $! v' with "Hslot") as "Ho".
    rewrite /proc_priv_nocwd /proc_ofiles.
    cbn [upd_ofile pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR; [iPureIntro; exact Hszb|].
    iSplitR; [iPureIntro; exact Hbel|].
    iFrame "Hpid Hf Hpt Htfp Ho". iPureIntro.
    rewrite length_insert. exact Hlen.
  Qed.

  (* the split, as an equivalence -- everything below and every landed spec
     keeps using [proc_priv] and never sees the core *)
  Lemma proc_priv_split (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V ⊣⊢ proc_priv_core pa pid V ∗ proc_ofiles γf pa (pv_ofile V).
  Proof. reflexivity. Qed.

  (* The core does not constrain the descriptor array, so it survives any
     store into it unchanged.  This is what lets fdalloc hand back a core at
     the ORIGINAL [V] while the array it returns is the updated one. *)
  Lemma proc_priv_core_upd_ofile (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    proc_priv_core pa pid (upd_ofile V fd v) ⊣⊢ proc_priv_core pa pid V.
  Proof.
    rewrite /proc_priv_core.
    by cbn [upd_ofile pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
  Qed.

  (* BUILDING one: allocproc is the only producer, and this is exactly its
     move -- the scalar cells and the descriptor array come out of the
     dormant block, the page table and the trapframe page it just built.
     The [p->sz] bound travels with the dormant block (which is where the
     invariant keeps it); everything else is a straight repackaging.
       The coherence conjunct is the caller's, and it costs allocproc
     nothing: the table it just built has an EMPTY user map, and
     [ProcPtOwn.um_below_empty] holds at any size.
       It produces the DEFICIT block: allocproc's [p->cwd] is still 0 at this
     point, and [cwd_ref] has no null arm, so there is no [proc_priv] to be
     had here and there should not be.  The caller that installs a working
     directory closes the window with [proc_priv_split_cwd]. *)
  Lemma proc_priv_nocwd_intro (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (P : uptd) (ws : list (mword 64)) :
    (uint (pv_sz V) <= uvm_maxsz)%Z ->
    um_below (pv_sz V) (ud_um P) ->
    p_pid pa ↦₄{DfracOwn (1/2)} pid -∗
    proc_fields pa (DfracOwn 1) V -∗
    proc_pt_at pa P -∗
    tf_page (ud_tfp P) ws -∗
    proc_ofiles γf pa (pv_ofile V) -∗
    proc_priv_nocwd γf pa pid (upd_pt V P ws).
  Proof.
    iIntros (Hsz Hbel) "Hpid Hf Hpt Htf Ho".
    rewrite /proc_priv_nocwd.
    cbn [upd_pt pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR; [iPureIntro; exact Hsz|].
    iSplitR; [iPureIntro; exact Hbel|]. iFrame "Hpid Hf Hpt Htf Ho".
  Qed.

  Lemma proc_priv_intro (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (P : uptd) (ws : list (mword 64)) :
    (uint (pv_sz V) <= uvm_maxsz)%Z ->
    um_below (pv_sz V) (ud_um P) ->
    p_pid pa ↦₄{DfracOwn (1/2)} pid -∗
    proc_fields pa (DfracOwn 1) V -∗
    proc_pt_at pa P -∗
    tf_page (ud_tfp P) ws -∗
    proc_ofiles γf pa (pv_ofile V) -∗
    cwd_ref (pv_cwd V) -∗
    (* ...AND THE TOKEN.  [proc_priv_nocwd_intro] above has NO such premise
       and must not: allocproc produces the deficit block, and allocproc
       does not park a RUNNABLE or SLEEPING process. *)
    first_tok -∗
    proc_priv γf pa pid (upd_pt V P ws).
  Proof.
    iIntros (Hsz Hbel) "Hpid Hf Hpt Htf Ho Hc Hft".
    iDestruct (proc_priv_nocwd_intro γf pa pid V P ws Hsz Hbel
                 with "Hpid Hf Hpt Htf Ho") as "H".
    iApply proc_priv_split_cwd. iFrame "H Hft".
    by cbn [upd_pt pv_cwd].
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
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iIntros "Hq1". rewrite /proc_priv /proc_priv_core Hq word4_pointsto_frac_split.
    iSplitR "Ho"; [|iFrame "Ho"].
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
    rewrite {1}Hq. apply (ctx_word_pointsto_frac_split cur_ctx).
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
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iDestruct (word_split14 with "Htfc") as "[Hq1 Hq2]".
    iSplitL "Hq1"; [iExact "Hq1"|].
    iIntros "Hq1". rewrite /proc_priv /proc_priv_core /proc_pt_at.
    iDestruct (word_join14 with "Hq1 Hq2") as "Htfc".
    iSplitR "Ho"; [|iFrame "Ho"].
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* THE WORKING DIRECTORY, borrowed and replaced.  kexit and sys_chdir are
     the two writers, and both do the same thing: hand the reference the cell
     names to iput, then store a new pointer.  So the accessor gives out the
     cell AND the reference clause together and takes back a matching pair --
     which is what kept both callers standing when [cwd_ref] stopped being a
     placeholder (C6b, design/fs-icache.md §3). *)
  Lemma proc_priv_cwd (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_cwd pa ↦₈ pv_cwd V ∗ cwd_ref (pv_cwd V) ∗
    (∀ v' : mword 64,
       p_cwd pa ↦₈ v' -∗ cwd_ref v' -∗ proc_priv γf pa pid (upd_cwd V v')).
  Proof.
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_fields. iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iSplitL "Hcwd"; [iExact "Hcwd"|].
    (* [iExact], not [iFrame]: the hypothesis and the goal are the same
       FOLDED [cwd_ref _] and conversion closes it.  (This is what kept the
       lemma standing across C6b, when the predicate gained content.) *)
    iSplitL "Hc"; [iExact "Hc"|].
    iIntros (v') "Hcwd Hc".
    rewrite /proc_priv /proc_priv_core /proc_fields.
    cbn [upd_cwd pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho"; [| iExact "Ho"].
    iSplitR; [done|]. iSplitR; [done|].
    iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro; exact Hnl. }
    iSplitL "Hpt"; [iExact "Hpt"|].
    iSplitL "Htfp"; [iExact "Htfp"|].
    iSplitL "Hc"; [iExact "Hc"|]. iExact "Hft".
  Qed.

  (* THE WORKING DIRECTORY AND THE PID QUARTER TOGETHER, because kexit needs
     both AT ONCE and neither single accessor will do: [begin_op], [iput] and
     [end_op] each take [p_pid pa ↦₄{dq} _] (bread's acquiresleep records it),
     while the cwd cell has to stay out across all three -- from the
     [ld a0,336(s3)] that reads the pointer iput destroys to the
     [sd x0,336(s3)] that clears it, which is the first moment [cwd_ref] can
     be re-supplied).  Each of [proc_priv_cwd] and
     [proc_priv_pid] consumes the whole block, so they do not nest; this is
     their conjunction, proved once.  sys_chdir wants the same pair. *)
  (* THE BLOCK AND THE cwd REFERENCE, TOGETHER.  This is what a syscall that
     walks a path holds across the walk: namei/nameiparent/namex want
     [proc_priv_bare] (they read [p->cwd] out of it) and [inode_held] on the
     directory it names, which is what [cwd_ref] converts to.  [proc_ofiles]
     is what stays behind.

     Compare [proc_priv_cwd_pid] just below, which is the same move for a
     caller that wanted the cwd CELL and a quarter of [p->pid] as loose rows.
     Nothing wants either any more: the cell is in the block and the walk
     borrows it for its one load. *)
  Lemma proc_priv_bare_cref (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗
    proc_priv_bare pa pid V ∗ cwd_ref (pv_cwd V) ∗
    (proc_priv_bare pa pid V -∗ cwd_ref (pv_cwd V) -∗ proc_priv γf pa pid V).
  Proof.
    (* one [rewrite] does both occurrences -- the hypothesis AND the one
       under the wand -- so the give-back needs no second one. *)
    rewrite /proc_priv proc_priv_core_bare. iIntros "[[Hb [Hc Hft]] Ho]".
    iSplitL "Hb"; [iExact "Hb"|]. iSplitL "Hc"; [iExact "Hc"|].
    iIntros "Hb Hc". iFrame.
  Qed.

  Lemma proc_priv_cwd_pid (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_cwd pa ↦₈ pv_cwd V ∗ cwd_ref (pv_cwd V) ∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    (∀ v' : mword 64,
       p_cwd pa ↦₈ v' -∗ cwd_ref v' -∗ p_pid pa ↦₄{DfracOwn (1/4)} pid -∗
       proc_priv γf pa pid (upd_cwd V v')).
  Proof.
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_fields. iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]".
    iSplitL "Hcwd"; [iExact "Hcwd"|].
    (* [iExact], not [iFrame] -- see [proc_priv_cwd]. *)
    iSplitL "Hc"; [iExact "Hc"|].
    iSplitL "Hq1"; [iExact "Hq1"|].
    iIntros (v') "Hcwd Hc Hq1".
    rewrite /proc_priv /proc_priv_core /proc_fields.
    cbn [upd_cwd pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho"; [| iExact "Ho"].
    iSplitR; [done|]. iSplitR; [done|].
    rewrite Hq word4_pointsto_frac_split. iFrame "Hq1 Hq2".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro; exact Hnl. }
    iSplitL "Hpt"; [iExact "Hpt"|].
    iSplitL "Htfp"; [iExact "Htfp"|].
    iSplitL "Hc"; [iExact "Hc"|]. iExact "Hft".
  Qed.

  (* The array's length, which a caller needs BEFORE it knows which
     descriptor it wants: an fd below NOFILE always has a slot to look up. *)
  (* A LIVE PROCESS HAS A NON-NULL WORKING DIRECTORY, as a projection of the
     block rather than a conjunct anybody maintains.  This is what the
     no-null-arm shape buys, and it is what kexit / kfork / sys_fork /
     sys_exit used to take as a premise their callers could not discharge
     from anything but another copy of the same premise. *)
  Lemma proc_priv_cwd_nonzero (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜pv_cwd V <> (zero_reg : mword 64)⌝.
  Proof.
    iIntros "[(_ & _ & _ & _ & _ & _ & Hc & _) _]".
    by iApply (cwd_ref_nonzero with "Hc").
  Qed.

  Lemma proc_priv_ofile_len (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜length (pv_ofile V) = NOFILE⌝.
  Proof. iIntros "[_ [%Hlen _]]". done. Qed.

  (* The TRAPFRAME bound on [p->sz] -- what the uvm* layer asks of a size
     argument, and what growproc must re-establish when it writes one. *)
  Lemma proc_priv_sz_maxsz (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜uint (pv_sz V) <= uvm_maxsz⌝.
  Proof. iIntros "[(%Hszb & _) _]". done. Qed.

  (* The MAXVA bound on [p->sz], for a caller that must hand it to vmfault /
     copyin / copyout.  Pure conclusion, so [iDestruct ... as %H] keeps the
     block.  A weakening of the above -- those three sit below this altitude
     and were written against MAXVA, and nothing is gained by tightening
     their premise. *)
  Lemma proc_priv_sz_bound (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜uint (pv_sz V) <= 2 ^ 38⌝.
  Proof.
    iIntros "[(%Hszb & _) _]". iPureIntro.
    rewrite uvm_maxsz_val in Hszb. change (2 ^ 38)%Z with 274877906944%Z. lia.
  Qed.

  (* The map is below the size: what growproc hands uvmalloc as its
     freshness premise (through [ProcPtOwn.um_below_run_fresh]). *)
  Lemma proc_priv_um_below (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗ ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝.
  Proof. iIntros "[(_ & %Hbel & _) _]". done. Qed.

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
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iDestruct (word_split14 with "Htfc") as "[Hq1 Hq2]".
    iFrame "Hq1 Htfp".
    iIntros "Hq1 Htfp". rewrite /proc_priv /proc_priv_core /proc_pt_at.
    iDestruct (word_join14 with "Hq1 Hq2") as "Htfc".
    iSplitR "Ho"; [|iFrame "Ho"].
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* THE WRITE TWIN, standing to [proc_priv_tf] as [tf_page_word_upd] stands
     to [tf_page_word]: the wand takes back a DIFFERENT [ws'], and the block
     is rebuilt at [upd_tf V ws'].  Every trapframe WRITER needs it --
     prepare_return's four kernel slots, kfork's copy loop, syscall's a0.

     It hands the [p_trapframe] cell out WHOLE rather than at the quarter
     [proc_priv_tf] splits off: a store's base-register load wants a fraction
     and does not care which, and the whole cell is what the callers already
     thread.  No length side condition is owed on the way back -- [tf_page]
     carries [length ws = TFWORDS] itself. *)
  Lemma proc_priv_tf_upd (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    proc_priv γf pa pid V -∗
    p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) ∗
    tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
    (∀ ws' : list (mword 64),
       p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) -∗
       tf_page (ud_tfp (pv_upt V)) ws' -∗
       proc_priv γf pa pid (upd_tf V ws')).
  Proof.
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iFrame "Htfc Htfp".
    iIntros (ws') "Htfc Htfp".
    rewrite /proc_priv /proc_priv_core /proc_pt_at.
    cbn [upd_tf pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho"; [| iFrame "Ho"].
    iSplitR; [iPureIntro; exact Hszb|].
    iSplitR; [iPureIntro; exact Hbel|].
    iFrame "Hpid Hf Hpg Htfc Hptt Htfp Hc Hft".
  Qed.

  (* [upd_tf] at the contents it lent out is the identity -- the record eta a
     round trip through the accessor above needs when it changed nothing. *)
  Lemma upd_tf_id (V : pprivate) : upd_tf V (pv_tf V) = V.
  Proof. by destruct V. Qed.

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
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_fields /proc_pt_at.
    iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iFrame "Hsz Hpg Hptt".
    iIntros (P' szv) "%Hroot %Htf %Hszb' %Hbel' Hsz Hpg Hptt".
    rewrite /proc_priv /proc_priv_core /proc_fields /proc_pt_at.
    cbn [upd_sz upd_upt pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    rewrite Hroot Htf.
    iSplitR "Ho"; [|iFrame "Ho"].
    iSplitR; [iPureIntro; exact Hszb'|].
    iSplitR; [iPureIntro; exact Hbel'|].
    iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro. exact Hnl. }
    iFrame "Hpg Htfc Hptt Htfp Hc Hft".
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

  (* =================================================================== *)
  (* THE SAME PROJECTIONS AT THE CORE'S ALTITUDE                          *)
  (* =================================================================== *)
  (* WHY THERE ARE TWO FAMILIES, AND WHY IT IS NOT A CROSS-PRODUCT.  A
     [file.c] function that copies to or from user memory needs the process
     block AND a descriptor's [file_ref] -- and those cannot be held at once,
     because the only source for the reference is [proc_ofiles], which
     [proc_priv_ofile] / [proc_priv_lend] BORROW out of the block
     (design/file-table.md, "A FUNCTION THAT TAKES A DESCRIPTOR'S REFERENCE
     MUST NOT TAKE [proc_priv]").  So fileread / filewrite / filestat and
     their whole cone are stated over [proc_priv_core], and the syscall above
     them splits once ([proc_priv_lend]), keeps the fd table, and hands the
     core down.

     None of those callees ever touches the descriptor array -- measured, and
     that is what makes the move free -- so each of these is exactly its
     [proc_priv] twin with the [proc_ofiles] conjunct absent.  The twin at the
     block's altitude stays: every consumer that does NOT hold a reference
     (growproc, kexit, kfork, the trapframe writers) is stated there and
     should not be made to split.

     They are stated rather than derived from the block versions for the
     obvious reason: [proc_priv_core] cannot conjure a [proc_ofiles]. *)

  Lemma proc_priv_core_pid (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    (p_pid pa ↦₄{DfracOwn (1/4)} pid -∗ proc_priv_core pa pid V).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iIntros "Hq1". rewrite /proc_priv_core Hq word4_pointsto_frac_split.
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  Lemma proc_priv_core_sz_maxsz (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗ ⌜uint (pv_sz V) <= uvm_maxsz⌝.
  Proof. iIntros "(%Hszb & _)". done. Qed.

  Lemma proc_priv_core_sz_bound (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗ ⌜uint (pv_sz V) <= 2 ^ 38⌝.
  Proof.
    iIntros "(%Hszb & _)". iPureIntro.
    rewrite uvm_maxsz_val in Hszb. change (2 ^ 38)%Z with 274877906944%Z. lia.
  Qed.

  Lemma proc_priv_core_um_below (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗ ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝.
  Proof. iIntros "(_ & %Hbel & _)". done. Qed.

  Lemma proc_priv_core_tf (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗
    p_trapframe pa ↦₈{DfracOwn (1/4)} page_base (ud_tfp (pv_upt V)) ∗
    tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
    (p_trapframe pa ↦₈{DfracOwn (1/4)} page_base (ud_tfp (pv_upt V)) -∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V) -∗ proc_priv_core pa pid V).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft)".
    rewrite /proc_pt_at. iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iDestruct (word_split14 with "Htfc") as "[Hq1 Hq2]".
    iFrame "Hq1 Htfp".
    iIntros "Hq1 Htfp". rewrite /proc_priv_core /proc_pt_at.
    iDestruct (word_join14 with "Hq1 Hq2") as "Htfc".
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  Lemma proc_priv_core_addrspace (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗
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
       proc_priv_core pa pid (upd_sz (upd_upt V P') szv)).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft)".
    rewrite /proc_fields /proc_pt_at.
    iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iFrame "Hsz Hpg Hptt".
    iIntros (P' szv) "%Hroot %Htf %Hszb' %Hbel' Hsz Hpg Hptt".
    rewrite /proc_priv_core /proc_fields /proc_pt_at.
    cbn [upd_sz upd_upt pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    rewrite Hroot Htf.
    iSplitR; [iPureIntro; exact Hszb'|].
    iSplitR; [iPureIntro; exact Hbel'|].
    iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro. exact Hnl. }
    iFrame "Hpg Htfc Hptt Htfp Hc Hft".
  Qed.

  Lemma proc_priv_core_copy (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗
    p_sz pa ↦₈ pv_sz V ∗
    p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗
    proc_pt (pv_upt V) ∗
    (∀ P' : uptd, ⌜uptd_ext_sz (pv_sz V) (pv_upt V) P'⌝ -∗
       p_sz pa ↦₈ pv_sz V -∗
       p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) -∗
       proc_pt P' -∗
       proc_priv_core pa pid (upd_upt V P')).
  Proof.
    iIntros "Hpv".
    iDestruct (proc_priv_core_sz_maxsz with "Hpv") as "%Hszb".
    iDestruct (proc_priv_core_um_below with "Hpv") as "%Hbel".
    iDestruct (proc_priv_core_addrspace with "Hpv") as "($ & $ & $ & Hback)".
    iIntros (P') "%Hext Hsz Hpg Hptt".
    iApply ("Hback" $! P' (pv_sz V) with "[%] [%] [%] [%] Hsz Hpg Hptt").
    - exact (proj1 (uptd_ext_sz_ext _ _ _ Hext)).
    - exact (proj1 (proj2 (uptd_ext_sz_ext _ _ _ Hext))).
    - exact Hszb.
    - exact (um_below_ext_sz _ _ _ Hbel Hext).
  Qed.

  (* =================================================================== *)
  (* THE ADDRESS-SPACE SWAP -- exec, and only exec.                       *)
  (* =================================================================== *)
  (* [proc_priv_addrspace] above is the GROW/SHRINK bridge: the table OBJECT
     stays put and only its map moves, which is why it pins [ud_root] and
     demands the same [p->pagetable] value back.  kexec REPLACES the object:
     it builds a second table with proc_pagetable, loads the image into that,
     and only at the commit block stores its root into [p->pagetable].  So no
     premise about [ud_root] can be paid, and the cell comes back holding a
     DIFFERENT page.
       [ud_tfp] is still pinned, and that is not an artifact of the proof.
     The trapframe PAGE genuinely does not move across an exec: proc_pagetable
     maps whatever [p->trapframe] already holds, and [tf_page] -- the page's
     BYTES -- is outside [proc_pt] entirely, so it survives the old table's
     proc_freepagetable and is simply re-attached to the new descriptor.  The
     trapframe WORDS do move (epc / sp / a1), which is what [ws'] is for.
       Three things this lends that [proc_priv_addrspace] does not, each
     because kexec needs it while the block is open: the [p->trapframe] CELL
     (proc_pagetable reads it), [tf_page] (the commit block writes three of
     its words), and the two pure conjuncts (proc_freepagetable's premises are
     exactly those, AT THE OLD SIZE AND DESCRIPTOR, and the old size is gone
     from the cell by the time the free happens -- the C saves it in [oldsz]
     for the same reason). *)
  Lemma proc_priv_newspace (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    ⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
    ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
    p_sz pa ↦₈ pv_sz V ∗
    p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗
    p_trapframe pa ↦₈ page_base (ud_tfp (pv_upt V)) ∗
    proc_pt (pv_upt V) ∗
    tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
    (∀ (P' : uptd) (szv : mword 64) (ws' : list (mword 64)),
       ⌜ud_tfp P' = ud_tfp (pv_upt V)⌝ -∗
       ⌜uint szv <= uvm_maxsz⌝ -∗
       ⌜um_below szv (ud_um P')⌝ -∗
       p_sz pa ↦₈ szv -∗
       p_pagetable pa ↦₈ page_base (ud_root P') -∗
       p_trapframe pa ↦₈ page_base (ud_tfp P') -∗
       proc_pt P' -∗
       tf_page (ud_tfp P') ws' -∗
       proc_priv γf pa pid (upd_sz (upd_pt V P' ws') szv)).
  Proof.
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_fields /proc_pt_at.
    iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iDestruct "Hpt" as "(Hpg & Htfc & Hptt)".
    iSplitR; [iPureIntro; exact Hszb|].
    iSplitR; [iPureIntro; exact Hbel|].
    iFrame "Hsz Hpg Htfc Hptt Htfp".
    iIntros (P' szv ws') "%Htf %Hszb' %Hbel' Hsz Hpg Htfc Hptt Htfp".
    rewrite /proc_priv /proc_priv_core /proc_fields /proc_pt_at.
    cbn [upd_sz upd_pt pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho"; [|iFrame "Ho"].
    iSplitR; [iPureIntro; exact Hszb'|].
    iSplitR; [iPureIntro; exact Hbel'|].
    iFrame "Hpid Hpg Htfc Hptt Htfp Hc Hft".
    iFrame "Hsz Hcwd Hnm". iPureIntro. exact Hnl.
  Qed.

  (* p->name: the sixteen debug bytes, out and back.  PROMOTED HERE from
     ProofKforkB4's [kfk_name_open], whose own comment asked for it once there
     was a second consumer; kexec's [safestrcpy(p->name, last, 16)] is it. *)
  Lemma proc_priv_name (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    ⌜length (pv_name V) = PNAMELEN⌝ ∗
    pname_cells pa (DfracOwn 1) (pv_name V) ∗
    (∀ ns : list (bv 8), ⌜length ns = PNAMELEN⌝ -∗
       pname_cells pa (DfracOwn 1) ns -∗
       proc_priv γf pa pid (upd_name V ns)).
  Proof.
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) Ho]".
    rewrite /proc_fields.
    iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iSplitR; [iPureIntro; exact Hnl|].
    iFrame "Hnm".
    iIntros (ns) "%Hnl' Hnm".
    rewrite /proc_priv /proc_priv_core /proc_fields.
    cbn [upd_name pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho"; [|iFrame "Ho"].
    iSplitR; [iPureIntro; exact Hszb|].
    iSplitR; [iPureIntro; exact Hbel|].
    iFrame "Hpid Hpt Htfp Hc Hft Hsz Hcwd Hnm".
    iPureIntro. exact Hnl'.
  Qed.

  (* Borrow one fd slot and hand back a (possibly different) one. *)
  Lemma proc_priv_ofile (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    proc_priv γf pa pid V -∗
    ofile_slot γf pa fd v ∗
    (∀ v', ofile_slot γf pa fd v' -∗ proc_priv γf pa pid (upd_ofile V fd v')).
  Proof.
    iIntros (Hfd) "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) [%Hlen Ho]]".
    iDestruct (big_sepL_insert_acc with "Ho") as "[$ Hback]"; first exact Hfd.
    iIntros (v') "Hslot". iDestruct ("Hback" $! v' with "Hslot") as "Ho".
    rewrite /proc_priv /proc_priv_core /proc_ofiles.
    cbn [upd_ofile pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho".
    { iSplitR; [iPureIntro; exact Hszb|].
      iSplitR; [iPureIntro; exact Hbel|].
      iFrame "Hpid Hf Hpt Htfp Hc Hft". }
    iFrame "Ho". iPureIntro. rewrite length_insert. exact Hlen.
  Qed.

  (* Borrow one fd slot AND the pid quarter at once.  A closer of a
     descriptor needs both simultaneously -- the reference to give fileclose,
     and the pid cell fileclose's file-system arm threads down to bread's
     acquiresleep -- and neither of the one-at-a-time accessors can be open
     while the other is, since each swallows the whole block.  kexit's fd loop
     is the consumer. *)
  Lemma proc_priv_pid_ofile (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    proc_priv γf pa pid V -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗ ofile_slot γf pa fd v ∗
    (∀ v', p_pid pa ↦₄{DfracOwn (1/4)} pid -∗ ofile_slot γf pa fd v' -∗
           proc_priv γf pa pid (upd_ofile V fd v')).
  Proof.
    iIntros (Hfd) "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc & Hft) [%Hlen Ho]]".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iDestruct (big_sepL_insert_acc with "Ho") as "[$ Hback]"; first exact Hfd.
    iIntros (v') "Hq1 Hslot". iDestruct ("Hback" $! v' with "Hslot") as "Ho".
    rewrite /proc_priv /proc_priv_core /proc_ofiles.
    cbn [upd_ofile pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho".
    { iSplitR; [iPureIntro; exact Hszb|].
      iSplitR; [iPureIntro; exact Hbel|].
      rewrite Hq word4_pointsto_frac_split.
      iFrame "Hq1 Hq2 Hf Hpt Htfp Hc Hft". }
    iFrame "Ho". iPureIntro. rewrite length_insert. exact Hlen.
  Qed.

  (* THE SAME PAIRING, AT THE BLOCK.  A closer of one of its own descriptors
     -- sys_close, kexit, sys_pipe on its rollback arm -- hands fileclose the
     descriptor AND the process block, because fileclose reaches bread and
     acquiresleep, which take [proc_priv_bare] now rather than a quarter of
     [p->pid].  [cwd_ref] is what stays behind, and no closer needs it. *)
  Lemma proc_priv_bare_ofile (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    proc_priv γf pa pid V -∗
    proc_priv_bare pa pid V ∗ ofile_slot γf pa fd v ∗
    (∀ v', proc_priv_bare pa pid V -∗ ofile_slot γf pa fd v' -∗
           proc_priv γf pa pid (upd_ofile V fd v')).
  Proof.
    iIntros (Hfd) "[Hcore [%Hlen Ho]]".
    rewrite proc_priv_core_bare. iDestruct "Hcore" as "[Hb Hc]".
    iFrame "Hb".
    iDestruct (big_sepL_insert_acc with "Ho") as "[$ Hback]"; first exact Hfd.
    iIntros (v') "Hb Hslot". iDestruct ("Hback" $! v' with "Hslot") as "Ho".
    rewrite /proc_priv /proc_ofiles.
    cbn [upd_ofile pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho".
    { rewrite proc_priv_core_bare /proc_priv_bare.
      cbn [upd_ofile pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
      iFrame "Hb Hc". }
    iFrame "Ho". iPureIntro. rewrite length_insert. exact Hlen.
  Qed.

  (* ---- the two ends of a LOAN, at the block's altitude ----
     What a syscall that must carry one of its own descriptors' references in
     a register actually does: take the block apart, lend the payload, and keep
     the core to hand on to a callee.  sys_dup is the worked example. *)
  Lemma proc_priv_lend (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd : nat) (v : mword 64) :
    pv_ofile V !! fd = Some v ->
    v <> (zero_reg : mword 64) ->
    proc_priv γf pa pid V -∗
    ∃ (k : nat) (q : Qp) (C : fcontent),
      ⌜v = fnode k /\ (k < NFILE)%nat⌝ ∗ file_ref γf k q C ∗
      proc_priv_core pa pid V ∗
      proc_ofiles_owe γf pa (pv_ofile V) {[fd]}.
  Proof.
    iIntros (Hfd Hnz) "[Hcore Ho]".
    rewrite -(proc_ofiles_owe_empty γf pa (pv_ofile V)).
    iDestruct (proc_ofiles_lend _ _ _ ∅ fd v ltac:(set_solver) Hfd Hnz with "Ho")
      as (k q C) "[%Hk [Href Ho]]".
    iExists k, q, C. iFrame "Href Hcore".
    rewrite (union_empty_r_L {[fd]}). iFrame "Ho". iPureIntro. exact Hk.
  Qed.

  (* ... and putting the block back together once every loan is settled. *)
  Lemma proc_priv_join (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V -∗ proc_ofiles_owe γf pa (pv_ofile V) ∅ -∗
    proc_priv γf pa pid V.
  Proof.
    iIntros "Hcore Ho". rewrite proc_ofiles_owe_empty. iFrame "Hcore Ho".
  Qed.

  (* THE CALLER-OF-FDALLOC one-liner.  A caller that already holds the
     reference (sys_open after filealloc, sys_pipe after pipealloc) settles the
     deficit fdalloc opened the moment it returns, and is back to holding a
     plain [proc_priv] -- so nothing downstream of the call sees the split.
     sys_dup is the caller that CANNOT do this: its reference is still inside
     the source descriptor at that point, and only [filedup] can make a second
     one. *)
  Lemma proc_priv_settle (γf : gname) (pa : mword 64) (pid : mword 32)
      (V : pprivate) (fd k : nat) (q : Qp) (C : fcontent) :
    (fd < NOFILE)%nat ->
    length (pv_ofile V) = NOFILE ->
    (k < NFILE)%nat ->
    proc_priv_core pa pid V -∗
    proc_ofiles_owe γf pa (pv_ofile (upd_ofile V fd (fnode k))) ({[fd]} ∪ ∅) -∗
    file_ref γf k q C -∗
    proc_priv γf pa pid (upd_ofile V fd (fnode k)).
  Proof.
    iIntros (Hfd Hlen Hk) "Hcore Ho Href".
    assert (Hlk : pv_ofile (upd_ofile V fd (fnode k)) !! fd = Some (fnode k)).
    { cbn [upd_ofile pv_ofile]. apply list_lookup_insert. rewrite Hlen. exact Hfd. }
    iDestruct (proc_ofiles_repay _ _ _ ∅ fd k q C ltac:(set_solver) Hlk Hk
                 with "Ho Href") as "Ho".
    iApply (proc_priv_join with "[Hcore] Ho").
    rewrite proc_priv_core_upd_ofile. iExact "Hcore".
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
    iIntros "[(_ & _ & Hpid & _) _] Hother".
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
  (* ------------------------------------------------------------------- *)
  (* THE SAME BLOCK WITHOUT ITS CONTEXT CELLS.                            *)
  (*                                                                      *)
  (* A thread parking FOREVER -- kexit, at ZOMBIE -- owes the dormant      *)
  (* block to its lock's [inv_dormant] slot, but it cannot hand over the   *)
  (* fourteen context cells with it: it is about to swtch, and swtch SAVES *)
  (* into exactly those cells.  So the crossing carries the block minus    *)
  (* the context ([SchedCtx.park_pay]) and the scheduler -- which is       *)
  (* handed the parked record itself, by its own swtch -- puts the two     *)
  (* back together ([SchedCtx.proc_slots_park_gen], where the record is    *)
  (* FORGOTTEN down to its cells: nothing ever resumes a zombie).          *)
  (*                                                                      *)
  (* Splitting here, rather than making the payload carry a rebuild wand,  *)
  (* is what keeps [proc_dormant] the ONE shape procinit / allocproc /     *)
  (* freeproc see.                                                        *)
  (* ------------------------------------------------------------------- *)
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

  (* THE STACK ENTERS HERE.  [kstack_free] is the one thing in the block
     that is neither a [struct proc] cell nor a ghost unit, and boot is the
     only party that ever mints one ([KstackOwn.kstack_bank], out of
     kvminit's 64 pages and kvminithart's 64 claims): every later producer
     of a dormant slot (freeproc, kexit) passes on the one it was given. *)
  (* ...AND SO DOES THE BIO ALLOWANCE, for the same reason and by the same
     route: three units per slot, minted once at boot out of [BSLOTS] and
     passed on by every later producer of a dormant slot.  See
     [ProcDefs.proc_dormant]'s note for why the slot rather than the process
     owns them while it is dormant. *)
  Lemma proc_dormant_seal (pa : mword 64) :
    proc_dormant_nofd pa -∗ fd_slots (NOFILE + FDSPARE) -∗
    iref_slots (1 + IREFSPARE) -∗ bslots 3 -∗ kstack_free pa -∗
    proc_dormant pa UNUSED.
  Proof.
    iIntros "(%V & %pid & [%Hof [%Hcwd %Hsz]] & Hpid & Hf & Ho & Hctx & Hpg & Htf) Hs Hir Hbs Hkst".
    iDestruct (fd_slots_split with "Hs") as "[Hs Hsp]".
    iExists V, pid. iFrame "Hpid Hf Ho Hsp Hir Hbs Hkst Hctx". iSplit; [done|].
    rewrite bool_decide_eq_false_2; [| vm_compute; discriminate].
    iSplitL "Hs".
    { iApply fd_slots_to_any. by rewrite Hof length_replicate. }
    iFrame "Hpg Htf".
  Qed.

  (* THE BLOCK WITH ITS UNITS ROUTED BUT ITS STACK NOT YET DEPOSITED.
     procinit carries this rather than a sealed [proc_dormant], and it has
     to: the deposit needs [is_kstack], the PERSISTENT [p->kstack]
     agreement, and procinit is the function that WRITES that cell -- the
     full cell and a discarded one cannot coexist, so a block sealed before
     the store would be unsatisfiable, not merely premature.  The seal
     happens at the one point where the cell has been written and persisted
     ([SpecProcinit.procs_inv_alloc]'s pass 3). *)
  Definition proc_dormant_prestk (pa : mword 64) : iProp Σ :=
    (proc_dormant_nofd pa ∗ fd_slots (NOFILE + FDSPARE) ∗
     iref_slots (1 + IREFSPARE) ∗ bslots 3)%I.

  Lemma proc_dormant_prestk_intro (pa : mword 64) :
    proc_dormant_nofd pa -∗ fd_slots (NOFILE + FDSPARE) -∗
    iref_slots (1 + IREFSPARE) -∗ bslots 3 -∗ proc_dormant_prestk pa.
  Proof. iIntros "H Hs Hir Hbs". iFrame "H Hs Hir Hbs". Qed.

  Lemma proc_dormant_prestk_seal (pa : mword 64) :
    proc_dormant_prestk pa -∗ kstack_free pa -∗ proc_dormant pa UNUSED.
  Proof.
    iIntros "(Hd & Hs & Hir & Hbs) Hkst".
    iApply (proc_dormant_seal with "Hd Hs Hir Hbs Hkst").
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
    (* the CWD'S UNIT and the iref allowance come out together and stay
       OUTSIDE the private block, for [FDSPARE]'s reason: every [proc_priv]
       accessor is borrow-and-return and its wand swallows the block, so a
       syscall holding its allowance inside could not then pass the block to
       a callee.  The [1] is what kfork spends on [idup]. *)
    iref_slots (1 + IREFSPARE) ∗
    (* ...AND THE BIO ALLOWANCE, out with them and for the same reason.  This
       is the hand-over: the slot owned three units while it was dormant,
       and from here they are the RUNNING THREAD's, beside [proc_priv] --
       which is where [UsertrapRes.ut_own_nopt] already carries them.  kexit
       is what puts them back ([SchedCtx.park_pay ZOMBIE]). *)
    bslots 3 ∗
    (* THE SLOT'S KERNEL STACK, out with the block: it is what the caller
       eventually parks in the fresh process's context record
       ([SpecForkretParkPaid.forkret_park_pkg]), and the reason a slot owns
       one at all. *)
    kstack_free pa ∗
    ∃ (V : pprivate) (pid : mword 32),
      ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
       pv_cwd V = (zero_reg : mword 64) /\
       uint (pv_sz V) <= uvm_maxsz⌝ ∗
      p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
      proc_fields pa (DfracOwn 1) V ∗ proc_ofiles γf pa (pv_ofile V).
  Proof.
    iIntros "(%V & %pid & [%Hof [%Hcwd %Hsz]] & Hpid & Hf & Ho & Hs & Hsp & Hir & Hbs & Hkst & Hctx & Haddr)".
    rewrite bool_decide_eq_false_2; [| vm_compute; discriminate].
    iDestruct "Haddr" as "[Hpg Htf]". iFrame "Hctx Hpg Htf Hsp Hir Hbs Hkst".
    iExists V, pid. iSplit; [done|]. iFrame "Hpid Hf".
    rewrite /proc_ofiles /ofile_cells Hof length_replicate. iSplit; [done|].
    iAssert ([∗ list] fd ↦ v ∈ replicate NOFILE (zero_reg : mword 64),
               (p_ofile pa fd ↦₈ v ∗ fd_slot))%I with "[Ho Hs]" as "Ho".
    { rewrite big_sepL_sep. iFrame "Ho Hs". }
    iApply (big_sepL_impl with "Ho"). iIntros "!>" (fd v Hv) "[Hcell Hslot]".
    apply lookup_replicate in Hv as [-> _]. iFrame "Hcell". iLeft. by iFrame "Hslot".
  Qed.

  (* ... and back, at ALL-NULL descriptors: the shape [proc_dormant] parks.
     freeproc's precondition is the dormant block SPLIT (its two
     address-space cells have to be independently optional), so a caller
     that took the block apart with [proc_dormant_unused] and now wants to
     hand freeproc the rest needs this direction.  allocproc's two failure
     tails are the first consumers. *)
  Lemma proc_ofiles_null_split (γf : gname) (pa : mword 64) (fs : list (mword 64)) :
    fs = replicate NOFILE (zero_reg : mword 64) ->
    proc_ofiles γf pa fs -∗
    ofile_cells pa fs ∗ ([∗ list] _ ∈ fs, fd_slot).
  Proof.
    intros Hfs. rewrite /proc_ofiles /ofile_cells.
    iIntros "[_ Ho]".
    iAssert ([∗ list] fd ↦ v ∈ fs, (p_ofile pa fd ↦₈ v ∗ fd_slot))%I
      with "[Ho]" as "Ho".
    { iApply (big_sepL_impl with "Ho"). iIntros "!>" (fd v Hv) "Hs".
      rewrite Hfs in Hv. apply lookup_replicate in Hv as [-> _].
      iApply (ofile_slot_null γf pa fd with "Hs"). }
    rewrite big_sepL_sep. iDestruct "Ho" as "[$ Hs]".
    iApply (big_sepL_mono with "Hs"). iIntros (fd v _) "$".
  Qed.

  (* KEXIT'S MOVE, and the one producer of a ZOMBIE block: a process that has
     closed every descriptor and dropped its cwd has reduced its private
     block to the dormant shape.  Everything the ZOMBIE slot owns is already
     inside [proc_priv] -- the scalar cells, the emptied descriptor array with
     the units it took back from fileclose, the user page table and the
     trapframe page wait()/freeproc will reclaim -- except the allowance,
     which travels BESIDE [proc_priv] (FdSlots.v's [FDSPARE] note), and the
     context, which is the swtch's.  So this is a repackaging, not a
     construction, and nothing about the process has to be re-established.

     IT TAKES THE DEFICIT BLOCK, and that is forced rather than convenient:
     a ZOMBIE's [p->cwd] is 0, so it holds no [cwd_ref] and a [proc_priv] at
     this [V] does not exist.  kexit arrives in exactly that state -- it has
     already spent its reference on [iput] -- so the premise is the one it
     can actually pay. *)
  Lemma proc_priv_to_dormant_zombie (γf : gname) (pa : mword 64)
      (pid : mword 32) (V : pprivate) :
    pv_ofile V = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd V = (zero_reg : mword 64) ->
    proc_priv_nocwd γf pa pid V -∗ fd_slots FDSPARE -∗
    iref_slots (1 + IREFSPARE) -∗
    (* AND THE BIO ALLOWANCE BACK.  THIS IS THE RECLAIM, and without it the
       supply would drain: a dormant slot owns three units, allocproc hands
       them to the process, and nothing but this reassembly ever returns
       them.  Three per slot against [BSLOTS = 1024] leaves no slack for
       leaking one set per exit -- after BSLOTS/3 exits no recycled slot
       could be allocated again.  kexit still holds its three here (every
       borrow below it is stated to give one back: [SpecBread] in,
       [SpecBrelse] out), so the donation costs it nothing. *)
    bslots 3 -∗
    (* AND THE STACK BACK.  A zombie owns its kernel stack exactly as an
       unused slot does -- that is what makes freeproc's ZOMBIE -> UNUSED
       step a pass-through, and it is the whole reason the exit path has to
       reassemble the page (SpecKexit.v's park). *)
    kstack_free pa -∗ proc_dormant_noctx pa ZOMBIE.
  Proof.
    iIntros (Hof Hcwd) "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Ho) Hsp Hir Hbs Hkst".
    iDestruct (proc_ofiles_null_split γf pa (pv_ofile V) Hof with "Ho") as "[Ho Hs]".
    iExists V, pid. iSplit; [by iPureIntro|]. iFrame "Hpid Hf Ho Hs Hsp Hir Hbs Hkst".
    rewrite bool_decide_eq_true_2; [| reflexivity].
    iSplitR; [iPureIntro; exact Hbel|]. iFrame "Hpt Htfp".
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
End ProcInv.

(* ====================================================================== *)
(* THE PRIVATE BLOCK'S TRANSPORT OBLIGATION (tso-port M3 / absorb).        *)
(*                                                                         *)
(* This is [ProofForkretPark.forkret_park_paid]'s SIXTH deposit row, and    *)
(* the last one to close.  §0.15′ measured the chain down to its first      *)
(* failure -- [proc_priv] -> [proc_priv_core] -> [FirstTok.first_tok] ->    *)
(* [FsReady.fs_ready] -> [BioInv.bio_ctx] -> [buf_escrow], an [inv] over a  *)
(* ξ-indexed body, which no transport can cross.  With the escrow a PARKED  *)
(* RECORD that row is closed, and the rest of the walk is structural:       *)
(* [ofile_slot]'s disjunction (whence [TsoCtx.ctx_morph_or], the instance   *)
(* this tranche adds) and one [big_sepL] over the fd array, both applied AS *)
(* TERMS.                                                                   *)
(*                                                                         *)
(* OUTSIDE the section, because each instance quantifies the context the    *)
(* section fixes.                                                           *)
(* ====================================================================== *)
Section ProcInvMorph.
  Context `{!riscvGS Σ}.
  Context `{ !fileG Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.

  (* by SEARCH: a sep of [fref_tok] / [file_fields] (its own instance) /
     [file_pay] / [flive_tok].  Named so the slot below can apply it. *)
  Global Instance file_ref_morph (γ : gname) (k : nat) (q : Qp) (C : fcontent) :
    CtxMorph (λ ξ : CtxId, file_ref (XI := ξ) γ k q C).
  Proof. apply _. Qed.

  (* NO [cwd_ref_morph]: [cwd_ref] is [InodeInv.inode_held], which is a
     CLOSED TERM (measured -- [Check] prints no [CurCtx]), so the row is
     [ctx_morph_const] and simply frames. *)

  Global Instance ofile_slot_morph (γf : gname) (pa : mword 64)
      (fd : nat) (v : mword 64) :
    CtxMorph (λ ξ : CtxId, ofile_slot (XI := ξ) γf pa fd v).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /ofile_slot.
    iDestruct "H" as "[Hc Harm]".
    iDestruct (ctx_morph_word _ _ _ _ ξ ξ' with "Hd Hc") as "[Hd Hc]".
    iDestruct "Harm" as "[[%Hv Hfd] | (%k & %q & %C & %Hk & Href)]".
    - iFrame "Hd Hc". iLeft. iFrame "Hfd". done.
    - iDestruct (file_ref_morph γf k q C ξ ξ' with "Hd Href") as "[Hd Href]".
      iFrame "Hd Hc". iRight. iExists k, q, C. iFrame "Href". done.
  Qed.

  Global Instance proc_ofiles_morph (γf : gname) (pa : mword 64)
      (fs : list (mword 64)) :
    CtxMorph (λ ξ : CtxId, proc_ofiles (XI := ξ) γf pa fs).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /proc_ofiles.
    iDestruct "H" as "[%Hlen Hs]".
    iDestruct (ctx_morph_big_sepL fs
                 (λ fd v ξ0, ofile_slot (XI := ξ0) γf pa fd v)
                 (λ i x, ofile_slot_morph γf pa i x) ξ ξ' with "Hd Hs")
      as "[Hd Hs]".
    iFrame "Hd Hs". done.
  Qed.

  Global Instance proc_priv_core_morph (pa : mword 64) (pid : mword 32)
      (V : pprivate) :
    CtxMorph (λ ξ : CtxId, proc_priv_core (XI := ξ) pa pid V).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /proc_priv_core.
    iDestruct "H" as "(%HA & %HB & Hpid & Hf & Hpt & Htfp & Hcwd & Hft)".
    iDestruct (proc_fields_morph pa (DfracOwn 1) V ξ ξ' with "Hd Hf")
      as "[Hd Hf]".
    iDestruct (proc_pt_at_morph pa (pv_upt V) ξ ξ' with "Hd Hpt") as "[Hd Hpt]".
    iDestruct (first_tok_morph ξ ξ' with "Hd Hft") as "[Hd Hft]".
    iFrame "Hd Hpid Hf Hpt Htfp Hcwd Hft". done.
  Qed.

  Global Instance proc_priv_morph (γf : gname) (pa : mword 64)
      (pid : mword 32) (V : pprivate) :
    CtxMorph (λ ξ : CtxId, proc_priv (XI := ξ) γf pa pid V).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /proc_priv.
    iDestruct "H" as "[Hc Ho]".
    iDestruct (proc_priv_core_morph pa pid V ξ ξ' with "Hd Hc") as "[Hd Hc]".
    iDestruct (proc_ofiles_morph γf pa (pv_ofile V) ξ ξ' with "Hd Ho")
      as "[Hd Ho]".
    iFrame.
  Qed.

End ProcInvMorph.
