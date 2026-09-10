(* WaitInv.v -- [struct proc]'s [parent] field, and the resource that owns it.

   [parent] is the one field of [struct proc] that is protected by a DIFFERENT
   lock: [wait_lock], not [p->lock] (proc.h, and the comment above reparent()
   says so explicitly -- "Caller must hold wait_lock").  It is also the one
   field that is read and written ACROSS processes: kexit() walks the whole
   table handing its children to initproc, and kwait() reads a child's parent
   pointer.  So it cannot live in [SchedCtx.proc_lock_res] -- putting it there
   would make the documented lock ORDER [wait_lock] -> [p->lock] unstateable,
   because a holder of wait_lock would then have to hold every proc lock too.

   Hence this file: ONE flat resource holding all NPROC parent cells, keyed by
   nothing but the slot index.  [parents_own ps] is the CONTENTS-OUT form -- what
   a function that already holds wait_lock is handed -- and [parents_res] is the
   existential closure of it.  Nothing here mentions the lock itself,
   deliberately: reparent()'s contract is about the cells, and its caller's
   obligation to hold the lock is discharged one level up.

   THE SECOND HALF: THE CHILDREN SETS.  [children_own_at γc cs] is one
   [gset gname] per slot -- the GENERATIONS ([SchedCtx.gen_slot]) of that
   slot's live children -- and [wait_res_at γc] is the lock's payload,
   closing both.  It is ghost and not memory because [struct proc] has no
   such field: the C code answers "does p have children?" by scanning
   [q->parent] under this very lock, and the ghost is that scan's
   contents-out form.  [children_wf] states the tie between the two lists;
   the payload does not carry it, because reading a slot's generation needs
   the p->lock cells that hold it.

   THE PURE MODEL.  reparent(p) rewrites every cell equal to [p] to [initproc]
   and leaves the rest alone; that is [rp_map p ip].  [rp_upto p ip k] is the
   same map applied to the first [k] slots only -- the loop invariant -- and
   [rp_upto_step] is the one lemma the loop body needs.  Both are stated over an
   ARBITRARY list rather than over [NPROC] so the induction never has to know
   how long the table is. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import TsoCtx CtxMorphTac.
(* A6.61 THE RE-TIERING (A6.58's owner tranche, owner 3 -- and the owner is
   THIS file, not ProcInv: ProcInv already imports TsoCtx and its slot cells
   are ctx today).  [parents_own] held [p_parent] in the RAW word tower, so
   the five [p_parent] accesses in kexit/reparent/kwait/kforkB5 each crossed
   in through the shim, the direction the flip makes FALSE.  The owner moves
   instead; the five crossings delete and their return legs (already
   [ctx_word_pointsto_forget]) become identities.  No cycle: TsoCtx does not
   reach ProcGeom. *)
Require Import ProcGeom.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The pure model of what reparent() does to the parent table.           *)
(* ===================================================================== *)

(* one slot: a child of [p] is handed to [ip], anything else is untouched.
   The test is the [bne a5,s2] the code actually executes, on the whole
   64-bit pointer. *)
Definition rp_slot (p ip v : mword 64) : mword 64 :=
  if eq_vec v p then ip else v.

Definition rp_map (p ip : mword 64) (ps : list (mword 64)) : list (mword 64) :=
  rp_slot p ip <$> ps.

(* the loop invariant's partial map: slots [0 .. k) done, [k ..] untouched. *)
Definition rp_upto (p ip : mword 64) (k : nat) (ps : list (mword 64)) : list (mword 64) :=
  (rp_map p ip (take k ps) ++ drop k ps)%list.

Lemma rp_map_length (p ip : mword 64) (ps : list (mword 64)) :
  length (rp_map p ip ps) = length ps.
Proof. apply length_fmap. Qed.

Lemma rp_upto_length (p ip : mword 64) (k : nat) (ps : list (mword 64)) :
  length (rp_upto p ip k ps) = length ps.
Proof.
  unfold rp_upto. rewrite length_app rp_map_length length_take length_drop. lia.
Qed.

Lemma rp_upto_0 (p ip : mword 64) (ps : list (mword 64)) :
  rp_upto p ip 0 ps = ps.
Proof. unfold rp_upto, rp_map. rewrite take_0 drop_0. reflexivity. Qed.

Lemma rp_upto_all (p ip : mword 64) (k : nat) (ps : list (mword 64)) :
  (length ps <= k)%nat -> rp_upto p ip k ps = rp_map p ip ps.
Proof.
  intro Hk. unfold rp_upto.
  rewrite (take_ge ps k Hk) (drop_ge ps k Hk) app_nil_r. reflexivity.
Qed.

(* the cell the loop is about at index [k] still holds its ORIGINAL value:
   nothing before [k] can have moved it, because [rp_upto] rewrites a prefix. *)
Lemma rp_upto_lookup_k (p ip : mword 64) (k : nat) (ps : list (mword 64)) (v : mword 64) :
  ps !! k = Some v -> rp_upto p ip k ps !! k = Some v.
Proof.
  intro Hk. unfold rp_upto.
  assert (Hlen : length (rp_map p ip (take k ps)) = k).
  { rewrite rp_map_length length_take.
    apply lookup_lt_Some in Hk. lia. }
  rewrite lookup_app_r; [| lia].
  rewrite Hlen Nat.sub_diag.
  rewrite (lookup_drop ps k 0) Nat.add_0_r. exact Hk.
Qed.

(* ONE iteration: writing [rp_slot p ip v] into slot [k] advances the
   partial map by one.  This is the only lemma the loop body needs. *)
Lemma rp_upto_step (p ip : mword 64) (k : nat) (ps : list (mword 64)) (v : mword 64) :
  ps !! k = Some v ->
  <[k := rp_slot p ip v]> (rp_upto p ip k ps) = rp_upto p ip (S k) ps.
Proof.
  intro Hk. unfold rp_upto.
  assert (Hlen : length (rp_map p ip (take k ps)) = k).
  { rewrite rp_map_length length_take.
    apply lookup_lt_Some in Hk. lia. }
  rewrite insert_app_r_alt; [| lia].
  rewrite Hlen Nat.sub_diag.
  rewrite (drop_S ps v k Hk).
  rewrite (take_S_r ps k v Hk).
  unfold rp_map. rewrite fmap_app. cbn [fmap list_fmap]. cbn [insert list_insert].
  rewrite -app_assoc. reflexivity.
Qed.

(* ===================================================================== *)
(* The resource.                                                         *)
(* ===================================================================== *)
Section WaitInv.
  Context `{!riscvGS Σ}.
  (* [Xv6Cameras.wchG]'s capacity: the children cells' ghost.  This file
     does not take the whole-system bundle -- it is one field of one
     struct -- so it names the class it needs, as [UserChildren.v] does. *)
  Context `{!ghost_varG Σ (list (gset gname))}.
  Context `{XI : CurCtx}.

  (* every proc's [parent] cell, at its slot's value.  The length conjunct is
     part of the resource rather than a caller premise: it is a fact about the
     TABLE, and a caller handed the block has no other way to learn it. *)
  (* A6.129 (the M3 λ-conversion, A6.121's recipe): the block over an
     EXPLICIT context, so the wait lock's payload is a function of the
     holder's context with a real transport proof; [parents_own] stays as
     the ambient spelling every consumer reads and writes. *)
  Definition parents_own_at (ξ : CtxId) (ps : list (mword 64)) : iProp Σ :=
    (⌜length ps = NPROC⌝ ∗
     [∗ list] j ↦ v ∈ ps,
       ctx_word_pointsto ξ (p_parent (proc_addr j)) (DfracOwn 1) v)%I.
  Definition parents_own (ps : list (mword 64)) : iProp Σ := parents_own_at cur_ctx ps.

  Global Instance parents_own_at_morph ps : CtxMorph (λ ξ, parents_own_at ξ ps).
  Proof. rewrite /parents_own_at. ctx_morph_solve. Qed.

  (* the parent cells' own existential closure -- what the BOOT CARVE
     produces, before there is a children ghost to pair it with. *)
  Definition parents_res_at (ξ : CtxId) : iProp Σ := (∃ ps, parents_own_at ξ ps)%I.
  Definition parents_res : iProp Σ := parents_res_at cur_ctx.

  (* ------------------------------------------------------------------ *)
  (* THE CHILDREN CELLS, wait_lock's other half.                          *)
  (*                                                                      *)
  (* One [gset gname] per slot: the GENERATIONS of that slot's live        *)
  (* children ([SchedCtx.gen_slot] names an incarnation, and this is the   *)
  (* set of the incarnations a process has fathered and not yet reaped).   *)
  (* GHOST AND NOT MEMORY, because [struct proc] has no such field: the C  *)
  (* code answers "does p have children?" by scanning [q->parent] under    *)
  (* the same lock, and this is that scan's contents-out form.  It belongs *)
  (* to wait_lock for the reason [parent] does -- fork, exit and wait all  *)
  (* move it ACROSS processes, and [p->lock] cannot express that.          *)
  (*                                                                       *)
  (* WHOLE (fraction 1), like the cells beside it: a holder of the lock     *)
  (* may write it, and nobody outside holds a fragment.                     *)
  (* ------------------------------------------------------------------ *)
  Definition children_own_at (γc : gname) (cs : list (gset gname)) : iProp Σ :=
    (⌜length cs = NPROC⌝ ∗ ghost_var γc 1 cs)%I.

  Lemma children_own_at_length γc cs :
    children_own_at γc cs -∗ ⌜length cs = NPROC⌝.
  Proof. iIntros "[% _]". done. Qed.

  (* borrow the whole list and put back a possibly different one: the shape
     every writer of the table wants, since fork touches the PARENT's entry
     and exit touches init's as well as its own. *)
  Lemma children_own_at_upd γc cs cs' :
    length cs' = NPROC ->
    children_own_at γc cs -∗ |==> children_own_at γc cs'.
  Proof.
    intros Hl. iIntros "[_ Hg]".
    iMod (ghost_var_update cs' with "Hg") as "Hg".
    iModIntro. iSplit; [done|]. iExact "Hg".
  Qed.

  (* THE INVARIANT'S SHAPE, as a pure predicate on the two lists: a
     generation in slot [j]'s children set is the generation of a slot whose
     parent cell points at [j].  It is STATED and not carried: reading "the
     slot with generation γ" needs the per-slot generation cells, which live
     under p->lock, and a payload cannot mention resources of a lock it does
     not hold.  WX-FORK carries it, at the p->lock-protected mirror of these
     cells that fork's writers keep in step. *)
  Definition children_wf (ps : list (mword 64)) (cs : list (gset gname))
      (gs : list gname) : Prop :=
    forall (j : nat) (γ : gname) (S : gset gname),
      cs !! j = Some S -> γ ∈ S ->
      exists k : nat, gs !! k = Some γ /\ ps !! k = Some (proc_addr j).

  (* the children cells' own existential closure, the shape every party
     that does not read them carries: one opaque conjunct. *)
  Definition children_res (γc : gname) : iProp Σ :=
    (∃ cs : list (gset gname), children_own_at γc cs)%I.

  (* what [wait_lock] protects: the parent cells and the children sets. *)
  Definition wait_res_at (γc : gname) (ξ : CtxId) : iProp Σ :=
    (parents_res_at ξ ∗ children_res γc)%I.
  Definition wait_res (γc : gname) : iProp Σ := wait_res_at γc cur_ctx.

  Global Instance parents_res_at_morph : CtxMorph parents_res_at.
  Proof. rewrite /parents_res_at. ctx_morph_solve. Qed.
  Global Instance wait_res_at_morph γc : CtxMorph (wait_res_at γc).
  Proof. rewrite /wait_res_at. ctx_morph_solve. Qed.

  (* THE BOOT CARVE'S SHAPE, GATHERED.  [BootCarveMain.boot_procs_raw] hands
     the parent cells out one existential per slot; [parents_own] wants ONE
     list.  The conversion is an induction with an OFFSET, because
     [seq k (S n)] is [k :: seq (S k) n] -- the tail's table indices shift by
     one while the [j] in [parents_own]'s big-op is an index into the LIST.
     Stated here rather than at the carve so that [parents_res]'s shape stays
     this file's business. *)
  Lemma parents_cells_gather (n k : nat) :
    ([∗ list] i ∈ seq k n, ∃ pv : mword 64, p_parent (proc_addr i) ↦₈ pv)
    -∗ ∃ ps : list (mword 64), ⌜length ps = n⌝ ∗
         ([∗ list] j ↦ v ∈ ps, p_parent (proc_addr (k + j)) ↦₈ v).
  Proof.
    revert k. induction n as [|n IH]; intros k.
    - iIntros "_". iExists []. iSplit; [done | done].
    - cbn [seq]. rewrite big_sepL_cons.
      iIntros "[Hhd Htl]". iDestruct "Hhd" as (v0) "Hhd".
      iDestruct (IH (S k) with "Htl") as (ps) "[%Hlen Htl]".
      iExists (v0 :: ps).
      iSplit; [iPureIntro; cbn [length]; lia |].
      rewrite big_sepL_cons.
      iSplitL "Hhd"; [rewrite Nat.add_0_r; iExact "Hhd" |].
      iApply (big_sepL_mono with "Htl").
      iIntros (j v _) "Hv".
      replace (k + S j)%nat with (S k + j)%nat by lia.
      iExact "Hv".
  Qed.

  (* ...and what the boot chain actually hands main: the parent half, out of
     the NPROC parent cells the image owns and nothing else claims.  The
     children half has no cells to come out of, so it is MINTED instead --
     [wait_res_alloc] below, in main's own update. *)
  Lemma parents_res_of_cells :
    ([∗ list] i ∈ seq 0 NPROC, ∃ pv : mword 64, p_parent (proc_addr i) ↦₈ pv)
    -∗ parents_res.
  Proof.
    iIntros "H".
    iDestruct (parents_cells_gather NPROC 0 with "H") as (ps) "[%Hlen H]".
    iExists ps. rewrite /parents_own /parents_own_at.
    iSplit; [iPureIntro; exact Hlen |].
    iApply (big_sepL_mono with "H"). iIntros (j v _) "Hv". iExact "Hv".
  Qed.

  (* THE BOOT MINT: every slot starts with no children.  One name for the
     whole table, carved once and threaded exactly as the lock's own gname
     is ([ProofMain]'s wait_lock assembly builds both in the same step). *)
  Lemma wait_res_alloc : parents_res ==∗ ∃ γc : gname, wait_res γc.
  Proof.
    iIntros "Hp".
    iMod (ghost_var_alloc (replicate NPROC (∅ : gset gname))) as (γc) "Hg".
    iModIntro. iExists γc. iFrame "Hp".
    iExists (replicate NPROC (∅ : gset gname)).
    iSplit; [iPureIntro; apply length_replicate |]. iExact "Hg".
  Qed.

  Lemma parents_own_length ps : parents_own ps -∗ ⌜length ps = NPROC⌝.
  Proof. iIntros "[% _]". done. Qed.

  (* borrow one slot and give it back at a possibly DIFFERENT value -- the
     shape [ProcInv.proc_priv_ofile] has, and for the same reason: the scan
     touches one cell at a time and nothing has to know that two indices name
     different cells. *)
  Lemma parents_own_acc (ps : list (mword 64)) (j : nat) (v : mword 64) :
    ps !! j = Some v ->
    parents_own ps -∗
    p_parent (proc_addr j) ↦₈ v ∗
    (∀ v' : mword 64, p_parent (proc_addr j) ↦₈ v' -∗ parents_own (<[j := v']> ps)).
  Proof.
    intro Hj. iIntros "[%Hlen Hcells]".
    iDestruct (big_sepL_insert_acc _ _ j v Hj with "Hcells") as "[Hc Hback]".
    iFrame "Hc". iIntros (v') "Hc".
    iSplitR; [iPureIntro; rewrite length_insert; exact Hlen|].
    iApply ("Hback" with "Hc").
  Qed.

  (* the read-only instance: the cell comes back unchanged, so the descriptor
     does too.  What the loop's [ld a5,56(s1)] wants. *)
  Lemma parents_own_read (ps : list (mword 64)) (j : nat) (v : mword 64) :
    ps !! j = Some v ->
    parents_own ps -∗
    p_parent (proc_addr j) ↦₈ v ∗ (p_parent (proc_addr j) ↦₈ v -∗ parents_own ps).
  Proof.
    intro Hj. iIntros "H".
    iDestruct (parents_own_acc ps j v Hj with "H") as "[Hc Hback]".
    iFrame "Hc". iIntros "Hc".
    iSpecialize ("Hback" $! v with "Hc").
    rewrite list_insert_id; [| exact Hj]. iExact "Hback".
  Qed.

End WaitInv.

(* the [ld/sd rd,56(rs)] displacement form, which is what the instruction
   leaves produce, folded back onto [p_parent]'s [mword_of_int] spelling.
   Same bridge [p_pid]'s consumers need in the other direction. *)
Lemma p_parent_sext (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 56 : mword 12)) = p_parent pa.
Proof.
  unfold p_parent. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.
