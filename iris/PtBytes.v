(* ====================================================================== *)
(* PtBytes.v -- THE BYTE-MAP VIEW of a physical doubleword, and the        *)
(* algebra of [HartMemRun.bytes_own] the per-node port needs.              *)
(*                                                                        *)
(* Under whole-cycle stepping a memory composer consumed                   *)
(* [gen_heap_interp sigma.(mem)] only to LEARN what memory held, and       *)
(* the page-table slots were reached as [->p8] words.  Under per-node      *)
(* stepping the hart HOLDS its bytes: every certified access is checked    *)
(* against a [gmap pa (bv 8)] the caller owns ([HartMemRun.goodmb]'s       *)
(* [bytes_owned] and [hmrun]'s [read_bytes]).  So the port needs the two   *)
(* views to MEET, and this file is that meeting point:                     *)
(*                                                                        *)
(*   section 1  [word_bytes a w] -- the 8 bytes of a doubleword as a map,  *)
(*              and [phys_word_bytes_own], the ONE view lemma: an          *)
(*              [a ->p8 w] IS [bytes_own (word_bytes a w)] plus the        *)
(*              alignment fact.  Every page-table slot, at every level,    *)
(*              enters the byte world through here.                        *)
(*   section 2  the pure side conditions [goodmb] asks for, read off a     *)
(*              byte map's DOMAIN: [bytes_owned] and the read.             *)
(*   section 3  what OWNERSHIP proves about a byte map and nothing else    *)
(*              can: that its addresses are RAM (hence not device --       *)
(*              [goodmb] refuses MMIO by construction), and that two       *)
(*              separately-owned maps are DISJOINT.  Both are today        *)
(*              re-derived at each use from [RiscvPtsto.phys_ram] and from *)
(*              the separating conjunction; the port must extract them     *)
(*              ONCE, because a pure [goodmb] certificate cannot look at   *)
(*              resources.  The disjointness one is what makes a user      *)
(*              store unable to corrupt a PTE (risk R7 of the port plan).  *)
(*                                                                        *)
(* PRIVILEGE- AND TIER-NEUTRAL on purpose: the kernel page table           *)
(* ([KptTree]) wants exactly the same view, and so does any future         *)
(* stretch that owns bytes.                                                *)
(* ====================================================================== *)
(* IMPORT SET, and it is load-bearing: [SailStdpp.Base] / [SailStdpp.Values]
   put a SECOND [Countable Arch.pa] instance ([Countable_mword]) in scope,
   and a [gmap Arch.pa (bv 8)] elaborated against it is NOT the type
   [read_bytes] / [bytes_own] are stated at (which use stdpp's
   [bv_countable]).  The two are convertible and print identically; the
   error is a bare "has type ... while it is expected to have type ...".
   So this file mirrors [HartMemRun]'s import list exactly. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes VirtioQueue.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import HartMemRun.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* 1. A PHYSICAL DOUBLEWORD, AS A BYTE MAP.                               *)
(* ===================================================================== *)

(* THE BYTE-MAP TYPE, FROZEN at the instances [read_bytes] / [bytes_own] are
   stated over -- see the import-set note in the header.  A file that has to
   MENTION the type (in a list, a record field, a fixpoint's result) should
   spell it [pamap] rather than re-elaborate [gmap Arch.pa (bv 8)] under its
   own import set, where a second [Countable Arch.pa] instance may win. *)
Definition pamap : Type := gmap Arch.pa (bv 8).

Definition word_bytes (a : Arch.pa) (w : bv 64) : gmap Arch.pa (bv 8) :=
  list_to_map ((fun j : nat => (pa_add a j, nth_byte w j)) <$> seq 0 8).

Lemma word_bytes_keys_nodup (a : Arch.pa) (w : bv 64) :
  base.NoDup (((fun j : nat => (pa_add a j, nth_byte w j)) <$> seq 0 8).*1).
Proof.
  rewrite <- list_fmap_compose.
  apply NoDup_fmap_2_strong; [| apply NoDup_seq].
  intros i j Hi Hj Heq. apply elem_of_seq in Hi, Hj.
  apply (pa_add_inj a i j); [ lia | lia | exact Heq ].
Qed.

Lemma word_bytes_lookup (a : Arch.pa) (w : bv 64) (j : nat) :
  (j < 8)%nat -> word_bytes a w !! pa_add a j = Some (nth_byte w j).
Proof.
  intros Hj. rewrite /word_bytes. apply elem_of_list_to_map_1.
  - apply word_bytes_keys_nodup.
  - apply elem_of_list_fmap. exists j. split; [reflexivity |].
    apply elem_of_seq. lia.
Qed.

(* the domain, pointwise.  Deliberately NOT stated as [dom (word_bytes a w)
   = pa_range a 8]: [pa_range]'s [gset Arch.pa] and the one instance
   resolution finds for [dom] at this import set are built over different
   (convertible, not syntactically equal) [Countable Arch.pa] instances, so
   that equation leaves an unresolvable [Dom] evar.  The pointwise pair is
   what every consumer wants anyway. *)
Lemma word_bytes_dom_intro (a : Arch.pa) (w : bv 64) (j : nat) :
  (j < 8)%nat -> pa_add a j ∈ (dom (word_bytes a w) : gset Arch.pa).
Proof.
  intros Hj. apply elem_of_dom. exists (nth_byte w j).
  by apply word_bytes_lookup.
Qed.

Lemma word_bytes_dom_elim (a : Arch.pa) (w : bv 64) (x : Arch.pa) :
  x ∈ (dom (word_bytes a w) : gset Arch.pa) ->
  exists j : nat, (j < 8)%nat /\ x = pa_add a j.
Proof.
  intros Hx. apply elem_of_dom in Hx as [b Hb].
  rewrite /word_bytes in Hb. apply elem_of_list_to_map_2 in Hb.
  apply elem_of_list_fmap in Hb as (j & [= -> ->] & Hj).
  exists j. split; [| reflexivity]. apply elem_of_seq in Hj. lia.
Qed.

(* the domain does not depend on the VALUE -- which is what makes an A/D
   write-back a [u_mem_step] and not a re-shaping of the owned map *)
Lemma word_bytes_dom_eq (a : Arch.pa) (w w' : bv 64) :
  (dom (word_bytes a w) : gset Arch.pa) = dom (word_bytes a w').
Proof.
  apply set_eq. intros x. split; intros Hx;
    apply word_bytes_dom_elim in Hx as (j & Hj & ->);
    by apply word_bytes_dom_intro.
Qed.

Lemma word_bytes_read (a : Arch.pa) (w : bv 64) :
  read_bytes (word_bytes a w) a 8 = Some w.
Proof.
  apply read_bytes_of_list. intros j Hj. apply word_bytes_lookup. lia.
Qed.

Section PtBytesIris.
  Context `{!riscvGS Σ}.
  Context `{XI : TsoCtx.CurCtx}.

  (* THE VIEW LEMMA.  [->p8] is [<align>] plus the eight byte cells, and
     [bytes_own] over [word_bytes] is those same eight cells -- the whole
     content of the equivalence is that the eight keys are distinct. *)
  Lemma phys_word_bytes_own (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    a ↦ₚ₈{dq} w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ map] a' ↦ b ∈ word_bytes a w, a' ↦ₚ{dq} b).
  Proof.
    rewrite /phys_word_pointsto /word_bytes.
    rewrite big_sepM_list_to_map; [| apply word_bytes_keys_nodup ].
    by rewrite big_sepL_fmap.
  Qed.

  (* the [DfracOwn 1] instance, which is the one the frame carries -- AT THE
     LEDGER TIER since [bytes_own] moved there (tso-machine-flip.md §6
     amendment A6.16).  [TsoCtx.ctx_phys_word_pointsto] is character for
     character [↦ₚ₈] over the ledger byte, so this is the same equivalence
     it always was: the eight keys are distinct. *)
  Lemma phys_word_bytes_own_full (a : Arch.pa) (w : bv 64) :
    TsoCtx.ctx_phys_word_pointsto XI a (DfracOwn 1) w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗ bytes_own (word_bytes a w).
  Proof.
    rewrite /TsoCtx.ctx_phys_word_pointsto /bytes_own /word_bytes.
    rewrite big_sepM_list_to_map; [| apply word_bytes_keys_nodup ].
    by rewrite big_sepL_fmap.
  Qed.

End PtBytesIris.

(* ===================================================================== *)
(* 2. THE PURE SIDE CONDITIONS, off a byte map's DOMAIN.                   *)
(*                                                                       *)
(* [goodmb] asks two things of every RAM access: that the footprint is    *)
(* inside the owned map ([bytes_owned]) and that the address is not a     *)
(* device ([negb (dev_addr pa)]).  Both must be PURE, because a           *)
(* certificate is a [bool] over a state and a map and cannot consult a    *)
(* resource -- which is exactly why section 3 exists.                      *)
(* ===================================================================== *)

Lemma bytes_owned_of_dom (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) :
  (forall j : nat, (j < N.to_nat n)%nat -> pa_add pa j ∈ (dom mm : gset Arch.pa)) ->
  bytes_owned mm pa n = true.
Proof.
  intros Hd. rewrite /bytes_owned.
  apply Is_true_eq_true, forallb_True, Forall_forall.
  intros j Hj. apply elem_of_seq in Hj.
  apply bool_decide_pack, elem_of_dom, Hd. lia.
Qed.

(* the word view's own instance: an 8-byte slot inside the map is owned *)
Lemma bytes_owned_word (mm : gmap Arch.pa (bv 8)) (a : Arch.pa) (w : bv 64) :
  word_bytes a w ⊆ mm -> bytes_owned mm a 8 = true.
Proof.
  intros Hsub. apply bytes_owned_of_dom. intros j Hj.
  apply elem_of_dom. exists (nth_byte w j).
  eapply lookup_weaken; [| exact Hsub ]. apply word_bytes_lookup. lia.
Qed.

Lemma read_bytes_word (mm : gmap Arch.pa (bv 8)) (a : Arch.pa) (w : bv 64) :
  word_bytes a w ⊆ mm -> read_bytes mm a 8 = Some w.
Proof.
  intros Hsub. apply read_bytes_of_list. intros j Hj.
  eapply lookup_weaken; [| exact Hsub ]. apply word_bytes_lookup. lia.
Qed.

(* ===================================================================== *)
(* 3. WHAT OWNERSHIP PROVES, AND A CERTIFICATE CANNOT.                    *)
(* ===================================================================== *)

Section BytesOwnFacts.
  Context `{!riscvGS Σ}.
  Context `{XI : TsoCtx.CurCtx}.

  (* an owned byte cell is EXCLUSIVE, so two of them are at distinct
     addresses -- the one fact the disjointness below is made of *)
  Lemma phys_pointsto_ne (a1 a2 : Arch.pa) (dq : dfrac) (b1 b2 : bv 8) :
    a1 ↦ₚ b1 -∗ a2 ↦ₚ{dq} b2 -∗ ⌜a1 <> a2⌝.
  Proof.
    rewrite /phys_pointsto. iIntros "[H1 _] [H2 _]".
    by iDestruct (pointsto_ne with "H1 H2") as %?.
  Qed.

  (* every owned byte sits in RAM -- [RiscvPtsto.phys_ram] at every key at
     once.  With [RiscvPtsto.addr_is_ram_not_dev] this is what discharges
     [goodmb]'s [negb (dev_addr pa)] for every access inside the map, and it
     is why the tier needs NO MMIO arm: a user page is RAM by ownership. *)
  Lemma bytes_own_ram (mm : gmap Arch.pa (bv 8)) :
    bytes_own mm ⊢ ⌜forall a : Arch.pa, a ∈ (dom mm : gset Arch.pa) -> addr_is_ram a⌝.
  Proof.
    rewrite /bytes_own. iIntros "Hm".
    rewrite bi.pure_forall. iIntros (a). rewrite bi.pure_impl. iIntros (Ha).
    apply elem_of_dom in Ha as [b Hb].
    iDestruct (big_sepM_lookup _ _ _ _ Hb with "Hm") as "Hb".
    iDestruct (TsoCtx.ctx_phys_pointsto_forget with "Hb") as "Hb".
    by iDestruct (phys_ram with "Hb") as %?.
  Qed.

  Lemma bytes_own_not_dev (mm : gmap Arch.pa (bv 8)) :
    bytes_own mm ⊢ ⌜forall a : Arch.pa, a ∈ (dom mm : gset Arch.pa) -> dev_addr a = false⌝.
  Proof.
    iIntros "Hm". iDestruct (bytes_own_ram with "Hm") as %Hram.
    iPureIntro. intros a Ha. by apply addr_is_ram_not_dev, Hram.
  Qed.

  (* TWO SEPARATELY OWNED BYTE MAPS ARE DISJOINT.  This is the fact that
     makes a user store unable to corrupt a PTE, and today it is implicit
     in the separating conjunction between [ptree_own] and [udata_own];
     the port must have it as a PURE conjunct, because [goodmb] and
     [u_mem_step] are propositions about maps. *)
  Lemma bytes_own_disj (m1 m2 : gmap Arch.pa (bv 8)) :
    bytes_own m1 -∗ bytes_own m2 -∗ ⌜m1 ##ₘ m2⌝.
  Proof.
    rewrite /bytes_own. iIntros "H1 H2".
    rewrite map_disjoint_alt. rewrite bi.pure_forall. iIntros (a).
    destruct (m1 !! a) as [b1|] eqn:H1; [| iPureIntro; by left ].
    destruct (m2 !! a) as [b2|] eqn:H2; [| iPureIntro; by right ].
    iDestruct (big_sepM_lookup _ _ _ _ H1 with "H1") as "Hb1".
    iDestruct (big_sepM_lookup _ _ _ _ H2 with "H2") as "Hb2".
    iDestruct (TsoCtx.ctx_phys_pointsto_forget with "Hb1") as "Hb1".
    iDestruct (TsoCtx.ctx_phys_pointsto_forget with "Hb2") as "Hb2".
    by iDestruct (phys_pointsto_ne with "Hb1 Hb2") as %?.
  Qed.

  Lemma bytes_own_union (m1 m2 : gmap Arch.pa (bv 8)) :
    m1 ##ₘ m2 -> bytes_own (m1 ∪ m2) ⊣⊢ bytes_own m1 ∗ bytes_own m2.
  Proof. intros Hd. rewrite /bytes_own. by apply big_sepM_union. Qed.

  Lemma bytes_own_split (m1 m2 : gmap Arch.pa (bv 8)) :
    bytes_own m1 -∗ bytes_own m2 -∗ ⌜m1 ##ₘ m2⌝ ∗ bytes_own (m1 ∪ m2).
  Proof.
    iIntros "H1 H2". iDestruct (bytes_own_disj with "H1 H2") as %Hd.
    iSplitR; [done |]. rewrite (bytes_own_union _ _ Hd). iFrame.
  Qed.

End BytesOwnFacts.

(* ===================================================================== *)
(* 4. A LIST OF BYTE MAPS AND ITS UNION.                                  *)
(*                                                                       *)
(* A page table's bytes are the bytes of its slots, node by node, and     *)
(* the hart holds them as ONE map -- [hmrun] reads and writes a single    *)
(* [gmap], and [goodmb] certifies against a single domain.  So the        *)
(* separating conjunction over the pieces has to become a union, and      *)
(* THAT NEEDS DISJOINTNESS -- which section 3 derives from the ownership  *)
(* itself, so no caller has to assume it.                                 *)
(* ===================================================================== *)

Fixpoint maps_disj (l : list (gmap Arch.pa (bv 8))) : Prop :=
  match l with
  | [] => True
  | m :: l' => (forall m', m' ∈ l' -> m ##ₘ m') /\ maps_disj l'
  end.

(* disjointness is a fact about DOMAINS only, so a list whose maps have the
   same domains pointwise inherits it -- which is what makes an A/D
   write-back preserve it *)
Lemma maps_disj_dom (l l' : list (gmap Arch.pa (bv 8))) :
  Forall2 (fun m m' => (dom m : gset Arch.pa) = dom m') l l' ->
  maps_disj l -> maps_disj l'.
Proof.
  revert l'. induction l as [| m l IH]; intros l' Hf2 Hd.
  - by inversion Hf2.
  - inversion Hf2 as [| ? m2 ? l2 Hdm Hrest]; subst.
    destruct Hd as [Hhd Htl]. split; [| by apply IH].
    intros m'' Hm''.
    (* locate [m''] in [l2] and its partner in [l] *)
    apply elem_of_list_lookup in Hm'' as [k Hk].
    destruct (Forall2_lookup_r _ _ _ _ _ Hrest Hk) as (mk & Hmk & Hdomk).
    apply map_disjoint_dom. rewrite <- Hdm, <- Hdomk.
    apply map_disjoint_dom, Hhd, elem_of_list_lookup. by exists k.
Qed.

(* the head of a disjoint list is disjoint from the union of the tail *)
Lemma maps_disj_head (m : pamap) (l : list pamap) :
  (forall m' : pamap, m' ∈ l -> m ##ₘ m') -> m ##ₘ ⋃ l.
Proof.
  intros H. apply map_disjoint_union_list_r, Forall_forall.
  intros m' Hm'. by apply symmetry, H.
Qed.

(* ...so a member of a disjoint list is a SUBMAP of the union: what turns
   "the walk owns this slot" into "the slot is readable out of the hart's
   one byte map" *)
Lemma maps_disj_subseteq (l : list pamap) (m : pamap) :
  maps_disj l -> m ∈ l -> m ⊆ ⋃ l.
Proof.
  induction l as [| m0 l IH]; intros Hd Hm; [by apply elem_of_nil in Hm |].
  destruct Hd as [Hhd Htl]. rewrite union_list_cons.
  apply elem_of_cons in Hm as [-> | Hm].
  - apply map_union_subseteq_l.
  - etrans; [ apply (IH Htl Hm) |].
    apply map_union_subseteq_r, (maps_disj_head m0 l Hhd).
Qed.

Section MapsUnion.
  Context `{!riscvGS Σ}.
  Context `{XI : TsoCtx.CurCtx}.

  Lemma bytes_own_list_disj (l : list (gmap Arch.pa (bv 8))) :
    ([∗ list] m ∈ l, bytes_own m) ⊢ ⌜maps_disj l⌝.
  Proof.
    induction l as [| m l IH]; [by iIntros "_" |].
    rewrite big_sepL_cons. iIntros "[Hm Hl]".
    iDestruct (IH with "Hl") as %Hd.
    iAssert (⌜forall m', m' ∈ l -> m ##ₘ m'⌝)%I with "[Hm Hl]" as %Hhd.
    { rewrite bi.pure_forall. iIntros (m'). rewrite bi.pure_impl. iIntros (Hm').
      apply elem_of_list_lookup in Hm' as [k Hk].
      iDestruct (big_sepL_lookup _ _ _ _ Hk with "Hl") as "Hm'".
      by iDestruct (bytes_own_disj with "Hm Hm'") as %?. }
    iPureIntro. by split.
  Qed.

  Lemma bytes_own_list_union (l : list (gmap Arch.pa (bv 8))) :
    maps_disj l -> ([∗ list] m ∈ l, bytes_own m) ⊣⊢ bytes_own (⋃ l).
  Proof.
    induction l as [| m l IH]; intros Hd.
    - rewrite /bytes_own /=. by rewrite big_sepM_empty.
    - destruct Hd as [Hhd Htl].
      pose proof (maps_disj_head m l Hhd) as Hdisj.
      rewrite big_sepL_cons (IH Htl) /=.
      by rewrite (bytes_own_union _ _ Hdisj).
  Qed.

End MapsUnion.
