(* ===================================================================== *)
(* UserHeap.v -- A SEPARATION-LOGIC HEAP OVER USER MEMORY.                *)
(*                                                                        *)
(* The U tier's memory has been an image VALUE ([uvis_M W : gmap Z (bv 8)]) *)
(* threaded through every contract as an equation.  That has no frame      *)
(* rule: a function that touches ANY of it must say what happened to ALL   *)
(* of it, so a four-byte copyout propagates as [M' = umem_wr M a d bs]     *)
(* through every layer, and any layer that drops the window's bounds       *)
(* (the syscall dispatcher does) makes "outside the window" empty and      *)
(* nothing frames at all.  That is what blocked a verified [init]: it      *)
(* calls [wait] with a NULL status pointer, its text lives at address 0, and no layer above *)
(* kwait says the null pointer wrote nothing.                              *)
(*                                                                        *)
(* This file replaces the value with a HEAP: one [ghost_map Z (bv 8)] per  *)
(* process, allocated with a fresh [gname] over the process's initial      *)
(* image, and a RUNNING PREDICATE [urun γ W] tying its authority to the    *)
(* slot's key.  U-mode code then owns its bytes and frames everything it   *)
(* does not hand over.                                                     *)
(*                                                                        *)
(* THE ONE IDEA WORTH READING THIS FILE FOR: HOW AN EXCLUSIVE POINTS-TO    *)
(* PROVES ITS OWN WRITABILITY, WITH NO PERMISSION BIT IN SIGHT.            *)
(*                                                                        *)
(* The rule we want is "if I own [a] exclusively, I may write it".  The    *)
(* machine's reason is that [a] is on a PTE_W page -- but a permission map *)
(* in every U-mode statement is exactly the ugliness this file exists to   *)
(* remove, and the authority alone cannot tell which fragments are         *)
(* outstanding or at which [dfrac].  The trick is to make the SPLIT at     *)
(* allocation and let dfrac incompatibility do the reasoning:              *)
(*                                                                        *)
(*   - every address of the image on a NON-writable page is PERSISTED      *)
(*     ([a ↪[γ]□ b]) when the heap is allocated, and the running predicate *)
(*     KEEPS those persisted fragments;                                    *)
(*   - everything on a writable page is left EXCLUSIVE and handed to the   *)
(*     process.                                                           *)
(*                                                                        *)
(* Now "I hold [a ↪[γ] b] exclusively" PROVES [a] is writable: if it were  *)
(* not, the invariant would hold a persisted fragment for the very same    *)
(* key, and [ghost_map_elem_ne] -- an exclusive element is distinct from   *)
(* any element at any dfrac -- gives [a <> a].  [urun_writable] is that    *)
(* proof, and it is three lines.                                          *)
(*                                                                        *)
(* Two things fall out of the same fact, rather than needing notions of    *)
(* their own:                                                             *)
(*                                                                        *)
(*   - THE TEXT REGION IS IMMUTABLE.  A program's text is on an X, not-W   *)
(*     page, so it is persisted, so no one can ever write it AND the       *)
(*     fragments are freely duplicable -- which is what an instruction     *)
(*     fetch wants, since [uk_instr] needs the same bytes at every step.   *)
(*   - THE PERMISSION MAP IS CONSUMED ONCE, HERE.  [uvis_perm] appears in  *)
(*     this file and nowhere above it: it decides what gets persisted at   *)
(*     allocation and is never consulted again.                           *)
(*                                                                        *)
(* WHAT THIS FILE DOES NOT YET DO.  It is the substrate, not the payoff.   *)
(* [urun γ W] still names [uvis_M W], so the image is not yet HIDDEN; the  *)
(* next step restates the U-mode continuation so the image is existential  *)
(* behind [urun] and the leaves take points-to instead of image facts.     *)
(* And the payoff for [init] needs the syscall arms to take the FOOTPRINT  *)
(* they write rather than state an equation -- separation logic localizes  *)
(* that obligation to each syscall, it does not remove it: [wait] at a null pointer takes *)
(* NO fragments, so init keeps its text by separation and no window        *)
(* equation is needed anywhere.                                            *)
(*                                                                        *)
(* NO NEW GHOST CLASS.  [ghost_mapG Σ Z (bv 8)] already exists and         *)
(* RiscvPtsto.v declares [riscvF_diskGS] its UNIQUE source in a [riscvGS]  *)
(* context; a per-process heap is a fresh [ghost_map_alloc] at that same   *)
(* class, so neither Σ nor adequacy moves.                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvPtsto.
Require Import UserPtTree.
Require Import UserPerm.
Require Import UexecSlot.   (* [uvis] / [uvis_M] / [uvis_perm] *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 WRITABILITY, as an ADDRESS-level fact -- the only place the          *)
(* permission map is read.                                                *)
(* ===================================================================== *)

Definition uw_addr (π : gmap (mword 27) uperm) (a : Z) : Prop :=
  exists q : uperm, uperm_at π (mword_of_int a : mword 64) = Some q /\ up_W q = true.

Global Instance uw_addr_dec (π : gmap (mword 27) uperm) (a : Z) :
  Decision (uw_addr π a).
Proof.
  unfold uw_addr, uperm_at.
  destruct (π !! svpn_of (mword_of_int a : mword 64)) as [q |] eqn:E.
  - destruct (up_W q) eqn:Ew.
    + left. exists q. split; [ reflexivity | exact Ew ].
    + right. intros (q' & Hq' & Hw'). injection Hq' as <-.
      rewrite Ew in Hw'. discriminate.
  - right. intros (q' & Hq' & _). discriminate Hq'.
Defined.

(* the image's two halves: what a process may write, and what it may not.
   The split is made ONCE, at allocation. *)
Definition uro_part (W : uvis) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => ~ uw_addr (uvis_perm W) kv.1) (uvis_M W).

Definition uw_part (W : uvis) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => uw_addr (uvis_perm W) kv.1) (uvis_M W).

Lemma uro_part_sub (W : uvis) : uro_part W ⊆ uvis_M W.
Proof. apply map_filter_subseteq. Qed.

Lemma uw_part_sub (W : uvis) : uw_part W ⊆ uvis_M W.
Proof. apply map_filter_subseteq. Qed.

Lemma uro_uw_disjoint (W : uvis) : uro_part W ##ₘ uw_part W.
Proof.
  apply map_disjoint_spec. intros a b1 b2 H1 H2.
  apply map_lookup_filter_Some in H1 as [_ Hn].
  apply map_lookup_filter_Some in H2 as [_ Hy].
  exact (Hn Hy).
Qed.

Lemma uro_uw_union (W : uvis) : uro_part W ∪ uw_part W = uvis_M W.
Proof.
  apply map_eq. intros a.
  destruct (uvis_M W !! a) as [b |] eqn:Hb.
  - destruct (decide (uw_addr (uvis_perm W) a)) as [Hw | Hn].
    + rewrite lookup_union_r.
      * apply map_lookup_filter_Some. split; [ exact Hb | exact Hw ].
      * apply map_lookup_filter_None. right. intros x Hx. rewrite Hb in Hx.
        injection Hx as <-. intro Hc. exact (Hc Hw).
    + rewrite lookup_union_l'.
      * apply map_lookup_filter_Some. split; [ exact Hb | exact Hn ].
      * (* [lookup_union_l'] asks for [is_Some], not for the right map's None *)
        exists b. apply map_lookup_filter_Some. split; [ exact Hb | exact Hn ].
  - rewrite lookup_union_None. split; apply map_lookup_filter_None; left; exact Hb.
Qed.

(* the covering fact the running predicate carries: every non-writable byte
   of the image is in the read-only half *)
Lemma uro_part_covers (W : uvis) (a : Z) :
  is_Some (uvis_M W !! a) -> ~ uw_addr (uvis_perm W) a -> is_Some (uro_part W !! a).
Proof.
  intros [b Hb] Hn. exists b. apply map_lookup_filter_Some.
  split; [ exact Hb | exact Hn ].
Qed.

Section UserHeap.
  Context `{!riscvGS Σ}.

  (* ===================================================================== *)
  (* §2 THE POINTS-TO FAMILY.                                              *)
  (* ===================================================================== *)

  (* ONE BYTE, exclusively owned: the right to write it (§3's              *)
  (* [urun_writable] is what turns this into the machine's permission).    *)
  Definition ubyte (γ : gname) (a : Z) (b : bv 8) : iProp Σ := (a ↪[γ] b)%I.

  (* ...and READ-ONLY, hence persistent, duplicable and IMMUTABLE: the     *)
  (* value can never change again, which is exactly what a text byte is.   *)
  Definition ubyte_ro (γ : gname) (a : Z) (b : bv 8) : iProp Σ := (a ↪[γ]□ b)%I.

  Global Instance ubyte_ro_persistent γ a b : Persistent (ubyte_ro γ a b).
  Proof. apply _. Qed.

  Global Instance ubyte_timeless γ a b : Timeless (ubyte γ a b).
  Proof. apply _. Qed.

  (* ===================================================================== *)
  (* §3 THE RUNNING PREDICATE.                                             *)
  (*                                                                       *)
  (* It owns the authority at the key's image, and KEEPS the persisted     *)
  (* fragments for every non-writable byte -- which is the whole mechanism *)
  (* (see the header).                                                     *)
  (* ===================================================================== *)
  Definition urun (γ : gname) (W : uvis) : iProp Σ :=
    (∃ Mro : gmap Z (bv 8),
       ⌜ Mro ⊆ uvis_M W ⌝ ∗
       ⌜ forall a : Z, is_Some (uvis_M W !! a) -> ~ uw_addr (uvis_perm W) a ->
                       is_Some (Mro !! a) ⌝ ∗
       ghost_map_auth γ 1 (uvis_M W) ∗
       ([∗ map] a ↦ b ∈ Mro, ubyte_ro γ a b))%I.

  (* THE BRIDGE to the image, at ANY fraction: a fragment names the byte
     the key's image holds.  This is how a leaf that still speaks the image
     gets its byte fact out of a points-to. *)
  Lemma urun_lookup (γ : gname) (W : uvis) (a : Z) (dq : dfrac) (b : bv 8) :
    urun γ W -∗ a ↪[γ]{dq} b -∗ ⌜ uvis_M W !! a = Some b ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mro) "(%Hsub & %Hcov & Hauth & Hro)".
    iApply (ghost_map_lookup with "Hauth Hb").
  Qed.

  (* THE PAYOFF: AN EXCLUSIVE POINTS-TO PROVES ITS OWN WRITABILITY.
     If [a] were not writable the invariant would hold a PERSISTED fragment
     at the same key, and an exclusive element is distinct from an element
     at any dfrac ([ghost_map_elem_ne]) -- so [a <> a]. *)
  Lemma urun_writable (γ : gname) (W : uvis) (a : Z) (b : bv 8) :
    urun γ W -∗ ubyte γ a b -∗ ⌜ uw_addr (uvis_perm W) a ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mro) "(%Hsub & %Hcov & Hauth & Hro)".
    iDestruct (ghost_map_lookup with "Hauth Hb") as %HM.
    destruct (decide (uw_addr (uvis_perm W) a)) as [Hw | Hnw]; [ done | ].
    destruct (Hcov a (mk_is_Some _ _ HM) Hnw) as [b0 Hb0].
    iDestruct (big_sepM_lookup _ _ a b0 Hb0 with "Hro") as "Hp".
    rewrite /ubyte /ubyte_ro.
    iDestruct (ghost_map_elem_ne with "Hb Hp") as %Hne.
    exfalso. exact (Hne eq_refl).
  Qed.

  (* ...and therefore the store: an exclusively-owned byte may be replaced,
     and the key's image moves with it.  Note what does NOT have to be
     re-established: the read-only half is untouched (the written address is
     writable, so it is not in it) and the permission map does not move. *)
  Definition uvis_wM (W : uvis) (M' : gmap Z (bv 8)) : uvis :=
    MkUvis (uvis_tf W) M' (uvis_perm W).

  Lemma urun_store (γ : gname) (W : uvis) (a : Z) (b b' : bv 8) :
    urun γ W -∗ ubyte γ a b ==∗
      urun γ (uvis_wM W (<[a := b']> (uvis_M W))) ∗ ubyte γ a b'.
  Proof.
    iIntros "Hrun Hb".
    iDestruct (urun_writable with "Hrun Hb") as %Hw.
    iDestruct "Hrun" as (Mro) "(%Hsub & %Hcov & Hauth & Hro)".
    (* THE WRITTEN KEY IS NOT IN THE READ-ONLY HALF.  [Mro] is abstract here
       -- the invariant only says it COVERS the non-writable bytes, not that
       it consists of them -- so this is not a pure fact about a filter; it
       is the same dfrac conflict as [urun_writable], run once more: a
       persisted fragment at the key we hold exclusively is impossible. *)
    destruct (Mro !! a) as [b0 |] eqn:Hnro.
    { iDestruct (big_sepM_lookup _ _ a b0 Hnro with "Hro") as "Hp".
      rewrite /ubyte /ubyte_ro.
      iDestruct (ghost_map_elem_ne with "Hb Hp") as %Hne.
      exfalso. exact (Hne eq_refl). }
    iMod (ghost_map_update b' with "Hauth Hb") as "[Hauth Hb]".
    iModIntro. iFrame "Hb". iExists Mro.
    cbn [uvis_M uvis_perm uvis_wM].
    iFrame "Hauth Hro". iPureIntro. split.
    - apply insert_subseteq_r; [ exact Hnro | exact Hsub ].
    - intros k Hk Hnw.
      destruct (decide (k = a)) as [-> | Hne]; [ exfalso; exact (Hnw Hw) | ].
      apply Hcov; [ | exact Hnw ].
      rewrite lookup_insert_ne in Hk; [ exact Hk | exact (not_eq_sym Hne) ].
  Qed.

  (* ===================================================================== *)
  (* §4 ALLOCATION -- the process's FIRST WP.                              *)
  (*                                                                       *)
  (* One [ghost_map_alloc] over the whole initial image, then PERSIST the  *)
  (* read-only half.  The process walks away with an exclusive fragment    *)
  (* for every writable byte and a persistent one for every other.         *)
  (* ===================================================================== *)
  Lemma urun_alloc (W : uvis) :
    ⊢ |==> ∃ γ : gname,
        urun γ W ∗
        ([∗ map] a ↦ b ∈ uw_part W, ubyte γ a b) ∗
        ([∗ map] a ↦ b ∈ uro_part W, ubyte_ro γ a b).
  Proof.
    iMod (ghost_map_alloc (uvis_M W)) as (γ) "[Hauth Hfrag]".
    iEval (rewrite -(uro_uw_union W)) in "Hfrag".
    rewrite big_sepM_union; [ | apply uro_uw_disjoint ].
    iDestruct "Hfrag" as "[Hro Hw]".
    (* PERSIST the read-only half.  This is the whole mechanism: after this
       step no one can ever hold those keys exclusively, which is what makes
       [urun_writable] and [urun_store] go through. *)
    iAssert (|==> [∗ map] a ↦ b ∈ uro_part W, ubyte_ro γ a b)%I
      with "[Hro]" as ">#Hrop".
    { iApply big_sepM_bupd. iApply (big_sepM_impl with "Hro").
      iIntros "!>" (a b _) "H". rewrite /ubyte_ro.
      iApply (ghost_map_elem_persist with "H"). }
    iModIntro. iExists γ. rewrite /urun.
    iSplitL "Hauth"; [ | iFrame "Hw"; iFrame "Hrop" ].
    iExists (uro_part W). iFrame "Hauth". iFrame "Hrop". iPureIntro.
    split; [ apply uro_part_sub | exact (uro_part_covers W) ].
  Qed.

End UserHeap.
