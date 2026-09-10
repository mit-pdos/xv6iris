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

   THE SECOND HALF: THE CHILDREN SETS.  One [gset gname] per LIVE process
   -- the GENERATIONS ([ChildTok.gen_slot]) of its live children -- as a
   GHOST MAP: [children_own_at γc m] is the AUTHORITY, the lock's payload,
   and [ch_frag γc γ S] is one process's ROW, which rides that process's
   trap residue beside [FdSlots.fd_frags] and is what [UexecSlot.uvis_ch]
   reads.  It is ghost and not memory because [struct proc] has no such
   field: the C code answers "does p have children?" by scanning
   [q->parent] under this very lock, and the ghost is that scan's
   contents-out form.

   KEYED BY THE PROCESS'S OWN CHILDREN-GHOST NAME ([ProcDefs.pv_chg]) and
   not by the slot index, because the party that has to find its entry --
   the process itself, at fork and at wait -- names the block and nothing
   else: with a map, holding the row PROVES which entry of the payload is
   yours ([children_own_lookup]), where two halves of a per-slot
   [ghost_var] would leave a lock holder unable to say so.  A row is
   INSTALLED under this lock ([children_own_install], at a name fresh for
   the map's domain: kfork for a forked child, main for the first process,
   which is why allocproc does not mint it) and DELETED here when the
   incarnation is reaped ([children_own_del]).  [children_wf] states the
   tie between the rows and the parent cells; the payload does not carry
   it, because reading a slot's generation needs the p->lock cells that
   hold it.

   THE PURE MODEL.  reparent(p) rewrites every cell equal to [p] to [initproc]
   and leaves the rest alone; that is [rp_map p ip].  [rp_upto p ip k] is the
   same map applied to the first [k] slots only -- the loop invariant -- and
   [rp_upto_step] is the one lemma the loop body needs.  Both are stated over an
   ARBITRARY list rather than over [NPROC] so the induction never has to know
   how long the table is. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_var ghost_map.
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
  (* [Xv6Cameras.wchG]'s capacity: the children map's ghost.  This file
     does not take the whole-system bundle -- it is one field of one
     struct -- so it names the class it needs, as [UserChildren.v] does. *)
  Context `{!ghost_mapG Σ gname (gset gname)}.
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
  (* THE CHILDREN MAP, wait_lock's other half.                            *)
  (*                                                                      *)
  (* One [gset gname] per live process: the GENERATIONS of the children   *)
  (* it has fathered and not yet reaped ([ChildTok.gen_slot] names an     *)
  (* incarnation).  GHOST AND NOT MEMORY, because [struct proc] has no    *)
  (* such field: the C code answers "does p have children?" by scanning   *)
  (* [q->parent] under the same lock, and this is that scan's             *)
  (* contents-out form.  It belongs to wait_lock for the reason [parent]  *)
  (* does -- fork, exit and wait all move it ACROSS processes, and        *)
  (* [p->lock] cannot express that.                                       *)
  (*                                                                      *)
  (* AUTHORITY HERE, ROW WITH THE PROCESS.  A holder of the lock may not  *)
  (* move a set on its own: the row is the process's ([ch_frag], in its   *)
  (* trap residue), and an update needs both -- which is exactly the      *)
  (* discipline fork and wait execute, each holding this lock AND its own *)
  (* row.  Nobody else may touch a set, and no set can move behind the    *)
  (* back of the process whose key names it.                              *)
  (* ------------------------------------------------------------------ *)
  Definition children_own_at (γc : gname) (m : gmap gname (gset gname)) : iProp Σ :=
    ghost_map_auth γc 1 m.

  (* ONE PROCESS'S ROW, at the name its private block records
     ([ProcDefs.pv_chg]).  This is the resource behind
     [UexecSlot.uvis_ch].

     NOTHING CARRIES IT YET.  The trap residue is not indexed by the
     children set ([UsertrapRes.ut_own] carries [FdSlots.fd_frags] and no
     row), so at fork the key's [uvis_ch] moving to [cs ∪ {γ}] is a fact
     about the KEY THE PARKER PAYS -- the resumer instantiates
     [ParkCap.park_cap]'s [∀ cs] at the grown set -- and not a move of the
     map below: [SpecKfork] carries the child token and touches no row.
     Lane WX-RES puts this row in the residue beside the descriptor
     fragments, and then fork and wait move the map under the lock with
     the caller's own row, which is what the lemmas below are for. *)
  Definition ch_frag (γc : gname) (γ : gname) (S : gset gname) : iProp Σ :=
    (γ ↪[γc] S)%I.

  Global Instance ch_frag_timeless γc γ S : Timeless (ch_frag γc γ S).
  Proof. apply _. Qed.

  (* A ROW READS THE AUTHORITY -- the lemma the map shape exists for: a
     lock holder that also holds a row learns WHICH entry is its own, and
     that is what a per-slot pair of [ghost_var] halves could not say. *)
  Lemma children_own_lookup γc m γ S :
    children_own_at γc m -∗ ch_frag γc γ S -∗ ⌜m !! γ = Some S⌝.
  Proof.
    iIntros "Ha Hf". rewrite /children_own_at /ch_frag.
    by iDestruct (ghost_map_lookup with "Ha Hf") as %Hm.
  Qed.

  (* ...AND BOTH TOGETHER MOVE IT: fork's [cs -> cs ∪ {γ}] and wait's
     [cs -> cs ∖ {γ}], each under this lock. *)
  Lemma children_own_upd γc m γ S S' :
    children_own_at γc m -∗ ch_frag γc γ S ==∗
    children_own_at γc (<[γ := S']> m) ∗ ch_frag γc γ S'.
  Proof.
    iIntros "Ha Hf". rewrite /children_own_at /ch_frag.
    by iMod (ghost_map_update S' with "Ha Hf") as "[$ $]".
  Qed.

  (* THE INSTALL.  A new process needs a row, and the row can only be
     created by the authority -- i.e. under this lock, which allocproc does
     not hold.  So whoever CREATES the process installs it: kfork at its
     [acquire(&wait_lock); np->parent = p], and main for the first process,
     before the lock goes up.  The name is fresh for the map's domain and
     nothing more is needed -- a [gname] is a [positive] and the domain is
     finite, so no allocation is involved. *)
  Lemma children_own_install γc m (S : gset gname) :
    children_own_at γc m ==∗
    ∃ γ : gname, ⌜m !! γ = None⌝ ∗
      children_own_at γc (<[γ := S]> m) ∗ ch_frag γc γ S.
  Proof.
    iIntros "Ha". rewrite /children_own_at /ch_frag.
    set (γ := fresh (dom m)).
    assert (Hfr : m !! γ = None).
    { apply not_elem_of_dom. apply is_fresh. }
    iMod (ghost_map_insert γ S Hfr with "Ha") as "[Ha Hf]".
    iModIntro. iExists γ. iSplitR; [done|]. iFrame "Ha Hf".
  Qed.

  (* ...and the reap: the row dies with the incarnation, under this lock,
     spending the row itself. *)
  Lemma children_own_del γc m γ S :
    children_own_at γc m -∗ ch_frag γc γ S ==∗ children_own_at γc (delete γ m).
  Proof.
    iIntros "Ha Hf". rewrite /children_own_at /ch_frag.
    by iMod (ghost_map_delete with "Ha Hf") as "$".
  Qed.

  (* THE INVARIANT'S SHAPE, as a pure predicate: a generation in the
     children set of the process at slot [j] is the generation of a slot
     whose parent cell points at [j].  [chs] is the per-slot list of the
     processes' row names ([ProcDefs.pv_chg]) and [gs] of their generations
     ([ProcDefs.pv_gen]); both live under p->lock, which is why this is
     STATED and not carried -- a payload cannot mention resources of a lock
     it does not hold.  It is carried at the p->lock-protected mirror that
     fork's and wait's writers keep in step. *)
  Definition children_wf (ps : list (mword 64)) (m : gmap gname (gset gname))
      (chs : list gname) (gs : list gname) : Prop :=
    forall (j : nat) (γ0 γ : gname) (S : gset gname),
      chs !! j = Some γ0 -> m !! γ0 = Some S -> γ ∈ S ->
      exists k : nat, gs !! k = Some γ /\ ps !! k = Some (proc_addr j).

  (* the children map's own existential closure, the shape every party
     that does not read it carries: one opaque conjunct. *)
  Definition children_res (γc : gname) : iProp Σ :=
    (∃ m : gmap gname (gset gname), children_own_at γc m)%I.

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

  (* THE BOOT MINT, and it hands out ONE ROW WITH THE MAP.  The map's name
     is carved once and threaded exactly as the lock's own gname is
     ([ProofMain]'s wait_lock assembly builds both in the same step) -- and
     the same step installs the row of the FIRST process, because userinit
     takes no wait_lock and so cannot install its own.  The row travels to
     userinit as a premise and lands in its block at [pv_chg]. *)
  Lemma wait_res_alloc :
    parents_res ==∗ ∃ (γc γ0 : gname), wait_res γc ∗ ch_frag γc γ0 ∅.
  Proof.
    iIntros "Hp".
    iMod (ghost_map_alloc (∅ : gmap gname (gset gname))) as (γc) "[Ha _]".
    iMod (children_own_install γc ∅ ∅ with "Ha") as (γ0) "(_ & Ha & Hf)".
    iModIntro. iExists γc, γ0. iFrame "Hf Hp". iExists _. iExact "Ha".
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
