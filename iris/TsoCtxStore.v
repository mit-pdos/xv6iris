(* TsoCtxStore.v -- THE STORE GATES OF THE CONTEXT SURFACE.

   The second of TsoCtx.v's three files (read its header): the same
   [Section ctx], continued.  Everything here is a store gate -- the
   per-byte inductions [ctx_store_bytes] / [ledger_store_*_bytes] and the
   window forms over them -- and every proof is multi-second, which is why
   they are not in TsoCtx.v: that file is imported by ~1000 files and its
   wall is the build's critical path, while these are needed only by the
   store leaves (HartMStore, SmodeCorePt, WpSconfMem) and a few dozen
   whole-function proofs.  Import TsoCtx for the vocabulary; import this
   file only when a lemma named here is used. *)

From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_var ghost_map mono_nat gen_heap.
(* SailStdpp.Base is deliberately ABSENT (the SC file imported it): it
   exports [Countable_mword]/[Decidable_eq_mword], which would make every
   [gmap]/[ghost_map] over [Arch.pa] in THIS file elaborate at the Sail
   key instances while [TsoGhost]'s classes carry stdpp's -- the
   riscvF_kmapGS trap, live.  [Values] alone does not export them. *)
Require Import SailStdpp.Values.
Require Import SailStdpp.Operators_mwords.  (* [uint]; exports no mword key instances *)
Require Import Riscv.rv64d_types Riscv.rv64d.   (* [is_aligned_paddr]/[Physaddr]: the word tower's alignment vocabulary *)
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.


Section ctx.
  Context `{!riscvGS Σ}.

  Lemma ctx_phys_map_free (ξ : CtxId) (P : gmap Arch.pa (bv 8)) :
    ([∗ map] a ↦ v ∈ P, ctx_phys_pointsto ξ a (DfracOwn 1) v) ⊢
    ([∗ map] a ↦ _ ∈ P, phys_free a (DfracOwn 1)).
  Proof. apply big_sepM_mono. intros ? ? _. apply ctx_phys_pointsto_free. Qed.

  (* ---------------------------------------------------------------- *)
  (* The per-byte half of the store gate.  THE THREE AUTHORITIES that   *)
  (* hold a ledger byte -- gen_heap (the flat cell), [ts_name] (the     *)
  (* timestamp) and ξ's own dirty set -- move together over the write's *)
  (* whole footprint, in ONE modality, against ONE appended message.     *)
  (* A byte at a time would be a message at a time, i.e. a different    *)
  (* machine, so this loop is primitive and not a fold of a byte gate.   *)
  (* ---------------------------------------------------------------- *)
  (* §0.26′ / A6.85: THE PREMISE IS THE VISIBILITY-FREE BYTE, NOT THE
     REGISTERED ONE, and that is not a weakening for convenience -- it is
     what this proof always did.  The old text destructed the ctx byte and
     [iClear]ed its justification bit before touching anything: a store
     does not read, so the writer owes no license on the cell it is about
     to overwrite.  Stating it at [phys_free] makes that visible, hands
     the free-page path ([KallocInv.byte_any]) its store with no new
     ghost machinery, and leaves [ctx_store_ok] below stated exactly as
     before (one [ctx_phys_pointsto_free] on the way in). *)
  Local Lemma ctx_store_bytes (ξ : CtxId) (h : agent) (B i : nat)
      (msg : pwmsg) (Pold Pnew mem : gmap Arch.pa (bv 8))
      (TM : gmap Arch.pa ts_elem) (D : gset (nat * Arch.pa)) :
    dom Pold = dom Pnew ->
    (forall k, k ∈ D -> (k.1 <= i)%nat) ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    ghost_map_auth ts_name 1 TM -∗
    dset_auth (ctx_dirty_name ξ) 1 D -∗
    ([∗ map] a ↦ _ ∈ Pold, phys_free a (DfracOwn 1)) ==∗
    ∃ D' : gset (nat * Arch.pa),
      ⌜dom Pnew ⊆ dom mem⌝ ∗
      ⌜forall k, k ∈ D' <-> (k ∈ D \/ (k.1 = S i /\ k.2 ∈ dom Pnew))⌝ ∗
      gen_heap_interp (hG := riscv_memGS) (Pnew ∪ mem) ∗
      ghost_map_auth ts_name 1 (((fun _ => (S i, ts_pay_none)) <$> Pnew) ∪ TM) ∗
      dset_auth (ctx_dirty_name ξ) 1 D' ∗
      ([∗ map] a ↦ v ∈ Pnew,
         phys_pointsto a (DfracOwn 1) v ∗ a ↪[ts_name] (S i, ts_pay_none) ∗
         dset_in (ctx_dirty_name ξ) (S i, a)).
  Proof.
    revert Pold. induction Pnew as [|a vn P2 Hfresh IH] using map_ind;
      intros Pold Hdom HD.
    - (* empty footprint: nothing moves *)
      rewrite dom_empty_L in Hdom.
      apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hgh Hts Hd _". iModIntro. iExists D.
      rewrite fmap_empty !left_id_L !big_sepM_empty.
      iFrame "Hgh Hts Hd". iPureIntro. split; first set_solver.
      intros k. rewrite dom_empty_L. set_solver.
    - iIntros "Hgh Hts Hd Hold".
      (* pull the byte's OLD entry out of [Pold] *)
      assert (Ha : a ∈ dom Pold).
      { rewrite Hdom dom_insert_L. by apply elem_of_union_l, elem_of_singleton. }
      apply elem_of_dom in Ha as [vo Hvo].
      iDestruct (big_sepM_delete _ _ a vo Hvo with "Hold") as "[Hb Hrest]".
      assert (Hdom2 : dom (delete a Pold) = dom P2).
      { rewrite dom_delete_L Hdom dom_insert_L.
        assert (a ∉ dom P2) by (by apply not_elem_of_dom). set_solver + H. }
      iMod (IH (delete a Pold) Hdom2 HD with "Hgh Hts Hd Hrest")
        as "(%D2 & %Hsub2 & %HD2 & Hgh & Hts & Hd & Hbig)".
      (* now the one byte *)
      rewrite /phys_free.
      iDestruct "Hb" as "(%vo0 & %e & Hpt & Hte)".
      iDestruct (phys_valid with "Hgh Hpt") as %Hmem.
      iMod (phys_update _ a vo0 vn with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update (S i, ts_pay_none) with "Hts Hte") as "[Hts Hte]".
      (* the dirty key is REGISTERED (A6.128: registration is monotone and
         needs no freshness -- the set authority re-mints membership) *)
      iMod (dset_insert _ D2 (S i, a) with "Hd") as "[Hd #Hdt]".
      iModIntro.
      iExists (D2 ∪ {[(S i, a)]}).
      rewrite fmap_insert -!insert_union_l !big_sepM_insert //.
      iFrame "Hgh Hts Hd Hbig Hpt Hte Hdt".
      iPureIntro. split.
      { rewrite dom_insert_L. apply union_least; [|exact Hsub2].
        assert (Hin : a ∈ dom mem).
        { apply elem_of_dom_2 in Hmem. rewrite dom_union_L elem_of_union in Hmem.
          destruct Hmem as [Hx|Hx]; last done.
          apply not_elem_of_dom in Hfresh. set_solver + Hx Hfresh. }
        set_solver + Hin. }
      intros k. rewrite elem_of_union elem_of_singleton dom_insert_L.
      split.
      + intros [Hk| ->]; last (right; simpl; set_solver + P2).
        apply HD2 in Hk as [Hk|[Hk1 Hk2]]; [by left|]. right. set_solver + Hk1 Hk2.
      + intros [Hk|[Hk1 Hk2]]; first (left; apply HD2; by left).
        apply elem_of_union in Hk2 as [Hk2|Hk2].
        * apply elem_of_singleton in Hk2. right. destruct k; cbn in *. by subst.
        * left. apply HD2. right. by split.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE STORE GATE ([TsoCtxTwin2.twin_store_ok] at the surface types;  *)
  (* tso-machine-flip.md §6's [Wobl_ram]).  A running context's OWNED   *)
  (* footprint is written, publishing ONE message authored by the       *)
  (* ambient hart, and the append's four ghost steps are paid here:     *)
  (*   (1) every byte's [ts_name] element moves to the new top;         *)
  (*   (2) the message is PERSISTED in the log map (append-only, so     *)
  (*       stable -- it is what carries the dirty entries' author tie); *)
  (*   (3) the log-length [mono_nat] is bumped;                          *)
  (*   (4) each written byte's entry is INSERTED into ξ's dirty set at  *)
  (*       the new timestamp, and the running token's watermark rises.  *)
  (* The bytes come back DIRTY -- visible to this hart by the           *)
  (* forwarding arm, to any other only after a park raises the bound.   *)
  (*                                                                   *)
  (* NO RECEIPT AND NO VIEW MOVE: a plain store is buffered (§2), which *)
  (* is why the post-state's [gtv] is the pre-state's.  The AMO half    *)
  (* takes the view past its own append and mints its receipt in the    *)
  (* leaf (A6.6(b)), not here.                                          *)
  (*                                                                   *)
  (* THE POST-STATE IS GIVEN BY FIELD EQUATIONS rather than built: the  *)
  (* leaf already has the machine's successor state in hand and only    *)
  (* the four fields [tso_interp_at] reads are constrained, so this     *)
  (* form applies without a [gs_of] round trip on the way out.  The     *)
  (* memory equation is spelled [Pnew ∪ mem], which is exactly          *)
  (* [TsoMemPa.write_bytes_union]'s reading of the arm's [write_bytes]. *)
  (* ---------------------------------------------------------------- *)
  (* §0.26′ / A6.85: THE GATE IS STATED AT THE VISIBILITY-FREE TIER and
     [ctx_store_ok] (the registered form every existing client names) is
     its five-line corollary.  THE MINT IS HERE: bytes go in owning only
     their future (fraction + element, no justification) and come back
     REGISTERED to ξ and DIRTY -- determinacy re-minted by the write
     itself, with no receipt, no drain and no evidence, because a store
     does not read and one's own write is visible by forwarding.  That is
     §0.26′'s whole content, and it costs one weaker premise. *)
  Lemma ctx_store_free_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (Pold Pnew : gmap Arch.pa (bv 8)) :
    dom Pold = dom Pnew ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew (hart_agent cpu_id)])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (* THE VIEW MOVES MONOTONELY OR NOT AT ALL.  A plain store buffers, so
       the author's entry does not move and this is an equality; the AMO /
       conditional half takes the view PAST its own append, which is still
       a legal post-state -- [own_context]'s receipt is a LOWER bound and
       views only grow, so nothing in the running token is falsified. *)
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ map] a ↦ _ ∈ Pold, phys_free a (DfracOwn 1)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ map] a ↦ v ∈ Pnew, ctx_phys_pointsto ξ a (DfracOwn 1) v).
  Proof.
    iIntros (Hdom Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hold".
    rewrite own_context_unseal /own_context_def.
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdomtm & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htvok & Hcov) & Hera).
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    (* (2) the message is persisted, at slot [length glog] *)
    set (msg := PWMsg Pnew (hart_agent cpu_id)).
    iDestruct (llb_valid with "Hlen HW") as %HWlen.
    assert (HLMfresh : LM !! length g.(glog) = None).
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length g.(glog)) msg HLMfresh with "Hm")
      as "[Hm #Hlogm]".
    (* (3) the length bump *)
    iMod (mono_nat_own_update (length g'.(glog)) with "Hlen") as "[Hlen #Hlb]".
    { rewrite Hlog length_app /=. lia. }
    (* (1) + (4): the footprint *)
    assert (HDi : forall k, k ∈ D -> (k.1 <= length g.(glog))%nat).
    { intros k Hk. have := HDW _ Hk. lia. }
    iMod (ctx_store_bytes ξ (hart_agent cpu_id) B (length g.(glog)) msg
            Pold Pnew g.(gmem) TM D Hdom HDi with "Hgh Hts Hd Hold")
      as "(%D' & %Hsub & %HD' & Hgh & Hts & Hd & Hbig)".
    assert (Hlen' : length g'.(glog) = S (length g.(glog))).
    { rewrite Hlog length_app /=. lia. }
    (* THE ONE VIEW MOVE A PLAIN STORE MAKES, and it is not the author's:
       every BUS-MASTER agent is pinned to the top (RULING 2), so the
       append carries the disk's view with it.  The harts, this one
       included, keep theirs -- store buffering. *)
    assert (Havf : forall x, (avf g x <= avf g' x)%nat).
    { intros x. rewrite /avf Hlog length_app /=.
      destruct (lt_dec x NCPU) as [Hx|Hx]; [apply Htv | lia]. }
    iMod (view_auth_update _ (avf g) (avf g') Havf with "Hv") as "Hv".
    iModIntro.
    iSplitL "Hgh"; first by rewrite Hmem.
    iSplitL "Hts Hm Hlen Hv".
    { iExists (((fun _ : bv 8 => ((S (length g.(glog)), ts_pay_none) : ts_elem)) <$> Pnew) ∪ TM),
              (<[length g.(glog) := msg]> LM).
      iFrame "Hts Hm Hlen Hv".
      iSplitR.
      { iPureIntro.
        rewrite dom_union_L dom_fmap_L Hmem dom_union_L Hdomtm.
        by rewrite (subseteq_union_1_L _ _ Hsub). }
      iSplitR.
      { (* THE ELEMENT TIE, both halves.  The written bytes' elements are
           UNPINNED by definition of the payer ([ctx_phys_pointsto] pins
           the option to [None]), so their new elements are unpinned too
           and owe only the latest tie; and an address OUTSIDE the
           footprint has [msg_byte msg a = None], which is
           [TsoMemPa.pin_ok_app]'s free arm -- so an unpinned store gate
           needs no new premise (tso-pin-memo.md §5.3). *)
        iPureIntro. intros a e Hlk.
        destruct (Pnew !! a) as [vn|] eqn:Hpa.
        - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), ts_pay_none) : ts_elem)) <$> Pnew) !! a
                       = Some ((S (length g.(glog)), ts_pay_none) : ts_elem))
            by (rewrite lookup_fmap Hpa //).
          rewrite (lookup_union_Some_l _ _ _ _ Hl) in Hlk.
          injection Hlk as <-.
          apply (ts_ok_unpinned _ _ _ _ _ vn).
          { rewrite Hmem. by apply lookup_union_Some_l. }
          rewrite Hlog Himg. apply latest_app_new. by rewrite /msg_byte /=.
        - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), ts_pay_none) : ts_elem)) <$> Pnew) !! a = None)
            by (rewrite lookup_fmap Hpa //).
          rewrite (lookup_union_r _ _ _ Hl) in Hlk.
          pose proof (Htie _ _ Hlk) as Hok.
          assert (Hmb : msg_byte msg a = None) by (rewrite /msg_byte /=; exact Hpa).
          split_and!.
          + destruct (ts_ok_latest _ _ _ _ _ Hok) as (v0 & Hgm & Hlat).
            exists v0. split.
            { rewrite Hmem. by rewrite lookup_union_r. }
            rewrite Hlog Himg. by apply latest_app_frame.
          + intros Sv Bp He2. rewrite Hlog Himg.
            apply (pin_ok_app_frame _ _ _ _ _ _
                     (ts_ok_pin _ _ _ _ _ _ _ Hok He2) Hmb).
          (* the WINDOW arm frames on the SAME per-address side condition as
             the pin's -- which is the whole content of TsoMemPa §12c's
             correction (the byte-0 shape would need a per-WINDOW one here,
             and there is nothing in scope to prove it from). *)
          + intros W0 HW0. rewrite Hlog Himg.
            apply (win_ok1_app_frame _ _ _ _ _
                     (ts_ok_win _ _ _ _ _ _ Hok HW0) Hmb).
          + intros R0 HR0. rewrite Hlog Himg.
            apply (rel_ok1_app_frame _ _ _ _ _
                     (ts_ok_rel _ _ _ _ _ _ Hok HR0) Hmb).
          + intros Wp HWp. rewrite Hlog Himg.
            apply (pinw_ok1_app_frame _ _ _ _ _
                     (ts_ok_pinw _ _ _ _ _ _ Hok HWp) Hmb). }
      iSplitR.
      { iPureIntro. intros j. rewrite Hlog.
        destruct (decide (j = length g.(glog))) as [->|Hne].
        - rewrite lookup_insert. symmetry. by apply list_lookup_middle.
        - rewrite lookup_insert_ne; last congruence. rewrite HLM.
          destruct (decide (j < length g.(glog))%nat) as [Hlt|Hge].
          + by rewrite lookup_app_l.
          + rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia. }
      iPureIntro. split; [split_and! | rewrite Himg; exact Hera].
      - rewrite Hmem Hlog Himg flat_snoc /=. by rewrite -Hflat.
      - intros c. have := Htvok' c. lia.
      - rewrite Himg. exact Hcov. }
    iSplitL "Hb Hd".
    { iExists B, K, (length g'.(glog)), D'. iFrame "Hb Hd HK".
      iSplitR; first done.
      iSplitR; first (iLeft; iExact "Hlb").
      iSplitR.
      { iPureIntro. intros k Hk. apply HD' in Hk as [Hk|[Hk1 _]].
        - have := HDW _ Hk. lia.
        - rewrite Hk1 Hlen'. lia. }
      iApply big_sepS_intro. iIntros "!>" (k Hk).
      apply HD' in Hk as [Hin|[Hk1 _]].
      - by iApply (big_sepS_elem_of _ _ _ Hin with "Hoks").
      - iRight. iExists (length g.(glog)), msg. iFrame "Hlogm".
        by iPureIntro. }
    iApply (big_sepM_mono with "Hbig").
    iIntros (a v _) "(Hpt & Hte & Hdt)".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iExists (S (length g.(glog))). iFrame "Hpt Hte". by iRight.
  Qed.

  (* THE REGISTERED FORM, unchanged for every client: a byte already
     registered to ξ owns strictly more than the gate asks. *)
  Lemma ctx_store_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (Pold Pnew : gmap Arch.pa (bv 8)) :
    dom Pold = dom Pnew ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew (hart_agent cpu_id)])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ map] a ↦ v ∈ Pold, ctx_phys_pointsto ξ a (DfracOwn 1) v) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ map] a ↦ v ∈ Pnew, ctx_phys_pointsto ξ a (DfracOwn 1) v).
  Proof.
    iIntros (Hdom Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hold".
    iDestruct (ctx_phys_map_free with "Hold") as "Hold".
    by iApply (ctx_store_free_ok g g' ξ Pold Pnew Hdom Himg Hlog Hmem Htv Htvok'
                 with "Hgh Hint Hrun Hold").
  Qed.


  (* the OWNED footprint of a pinned store, per-address sets *)
  Definition pin_map_own (Pv : gmap Arch.pa (bv 8)) (dq : dfrac)
      (Bg : Arch.pa -> nat)
      (Sf : Arch.pa -> gset (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ v ∈ Pv, ∃ t : nat, phys_ledger_pin a dq v t (Bg a) (Sf a))%I.

  (* the per-byte half, TWO authorities instead of three: no dirty set, so
     no freshness obligation and no context anywhere *)
  Local Lemma ledger_store_bytes (i : nat)
      (Pold Pnew mem : gmap Arch.pa (bv 8)) (TM : gmap Arch.pa ts_elem) :
    dom Pold = dom Pnew ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    ghost_map_auth ts_name 1 TM -∗
    ([∗ map] a ↦ v ∈ Pold, phys_ledger a (DfracOwn 1) v) ==∗
    ⌜dom Pnew ⊆ dom mem⌝ ∗
    gen_heap_interp (hG := riscv_memGS) (Pnew ∪ mem) ∗
    ghost_map_auth ts_name 1 (((fun _ => (S i, ts_pay_none)) <$> Pnew) ∪ TM) ∗
    ([∗ map] a ↦ v ∈ Pnew, phys_ledger_at a (DfracOwn 1) v (S i)).
  Proof.
    revert Pold. induction Pnew as [|a vn P2 Hfresh IH] using map_ind;
      intros Pold Hdom.
    - rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hgh Hts _". iModIntro.
      rewrite fmap_empty !left_id_L !big_sepM_empty.
      iFrame "Hgh Hts". iPureIntro. set_solver.
    - iIntros "Hgh Hts Hold".
      assert (Ha : a ∈ dom Pold) by (rewrite Hdom dom_insert_L; set_solver).
      apply elem_of_dom in Ha as [vo Hvo].
      iDestruct (big_sepM_delete _ _ a vo Hvo with "Hold") as "[Hb Hrest]".
      assert (Hdom2 : dom (delete a Pold) = dom P2).
      { rewrite dom_delete_L Hdom dom_insert_L.
        assert (a ∉ dom P2) by (by apply not_elem_of_dom). set_solver + H. }
      iMod (IH (delete a Pold) Hdom2 with "Hgh Hts Hrest")
        as "(%Hsub2 & Hgh & Hts & Hbig)".
      rewrite phys_ledger_unseal /phys_ledger_def.
      iDestruct "Hb" as "(%t & Hpt & Hte)".
      iDestruct (phys_valid with "Hgh Hpt") as %Hmem.
      iMod (phys_update _ a vo vn with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update (S i, ts_pay_none) with "Hts Hte") as "[Hts Hte]".
      iModIntro.
      rewrite fmap_insert -!insert_union_l !big_sepM_insert //.
      iFrame "Hgh Hts Hbig".
      iSplitR.
      { iPureIntro. rewrite dom_insert_L. apply union_least; [|exact Hsub2].
        assert (Hin : a ∈ dom mem).
        { apply elem_of_dom_2 in Hmem. rewrite dom_union_L elem_of_union in Hmem.
          destruct Hmem as [Hx|Hx]; last done.
          apply not_elem_of_dom in Hfresh. set_solver + Hx Hfresh. }
        set_solver + Hin. }
      rewrite /phys_ledger_at. iFrame "Hpt Hte".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* (3) THE PINNED STORE GATE (tso-pin-memo.md §5.3).  The A/D           *)
  (* write-back's own gate: same message, same three ghost steps, and     *)
  (* ONE extra premise -- every written byte lands in its address's       *)
  (* allowed set.  The pin's bound [B] and sets [Sf] are UNCHANGED (they  *)
  (* are fixed at the mint), so the tie is re-established by              *)
  (* [TsoMemPa.pin_ok_app] on the footprint and [pin_ok_app_frame] off    *)
  (* it -- and a byte's pin survives its own write-back, which is the     *)
  (* property that makes the shared kernel table canon-INVARIANT rather   *)
  (* than merely canon-monotone.                                          *)
  (* ---------------------------------------------------------------- *)
  Definition pin_tm (i : nat) (Bg : Arch.pa -> nat) (Sf : Arch.pa -> gset (bv 8))
      (Pv : gmap Arch.pa (bv 8)) : gmap Arch.pa ts_elem :=
    map_imap (fun a _ => Some ((S i, ts_pay_pin (Sf a) (Bg a)) : ts_elem)) Pv.

  Local Lemma pin_tm_lookup i Bg Sf Pv a :
    pin_tm i Bg Sf Pv !! a
    = (fun _ : bv 8 => ((S i, ts_pay_pin (Sf a) (Bg a)) : ts_elem)) <$> (Pv !! a).
  Proof.
    rewrite /pin_tm map_lookup_imap. by destruct (Pv !! a).
  Qed.

  Local Lemma pin_tm_empty i Bg Sf : pin_tm i Bg Sf ∅ = ∅.
  Proof. apply map_eq. intros k. by rewrite pin_tm_lookup lookup_empty. Qed.

  Local Lemma pin_tm_insert i Bg Sf (P : gmap Arch.pa (bv 8)) a v :
    pin_tm i Bg Sf (<[a := v]> P)
    = <[a := ((S i, ts_pay_pin (Sf a) (Bg a)) : ts_elem)]> (pin_tm i Bg Sf P).
  Proof.
    apply map_eq. intros k. rewrite pin_tm_lookup.
    destruct (decide (k = a)) as [->|Hne].
    - by rewrite !lookup_insert.
    - rewrite !lookup_insert_ne // pin_tm_lookup //.
  Qed.

  Local Lemma ledger_store_pin_bytes (i : nat) (Bg : Arch.pa -> nat) (Sf : Arch.pa -> gset (bv 8))
      (Pold Pnew mem : gmap Arch.pa (bv 8)) (TM : gmap Arch.pa ts_elem) :
    dom Pold = dom Pnew ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    ghost_map_auth ts_name 1 TM -∗
    pin_map_own Pold (DfracOwn 1) Bg Sf ==∗
    ⌜dom Pnew ⊆ dom mem⌝ ∗
    (* the OLD elements, so the caller can re-establish the pin tie on the
       footprint out of [TsoMemPa.pin_ok_app] rather than out of nothing *)
    ⌜forall a, a ∈ dom Pnew ->
       exists t, TM !! a = Some ((t, ts_pay_pin (Sf a) (Bg a)) : ts_elem)⌝ ∗
    gen_heap_interp (hG := riscv_memGS) (Pnew ∪ mem) ∗
    ghost_map_auth ts_name 1 (pin_tm i Bg Sf Pnew ∪ TM) ∗
    ([∗ map] a ↦ v ∈ Pnew, phys_ledger_pin a (DfracOwn 1) v (S i) (Bg a) (Sf a)).
  Proof.
    revert Pold. rewrite /pin_map_own.
    induction Pnew as [|a vn P2 Hfresh IH] using map_ind; intros Pold Hdom.
    - rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hgh Hts _". iModIntro.
      rewrite pin_tm_empty !left_id_L !big_sepM_empty.
      iFrame "Hgh Hts". iPureIntro. split; first set_solver.
      intros a Ha. rewrite dom_empty_L in Ha. set_solver.
    - iIntros "Hgh Hts Hold".
      assert (Ha : a ∈ dom Pold) by (rewrite Hdom dom_insert_L; set_solver).
      apply elem_of_dom in Ha as [vo Hvo].
      iDestruct (big_sepM_delete _ _ a vo Hvo with "Hold") as "[Hb Hrest]".
      assert (Hdom2 : dom (delete a Pold) = dom P2).
      { rewrite dom_delete_L Hdom dom_insert_L.
        assert (a ∉ dom P2) by (by apply not_elem_of_dom). set_solver + H. }
      iMod (IH (delete a Pold) Hdom2 with "Hgh Hts Hrest")
        as "(%Hsub2 & %Hold2 & Hgh & Hts & Hbig)".
      iDestruct "Hb" as "(%t & Hpt & Hte)".
      iDestruct (phys_valid with "Hgh Hpt") as %Hmem.
      iDestruct (ghost_map_lookup with "Hts Hte") as %Hlk.
      assert (HTMa : TM !! a = Some ((t, ts_pay_pin (Sf a) (Bg a)) : ts_elem)).
      { rewrite lookup_union_r in Hlk; first exact Hlk.
        rewrite pin_tm_lookup. by rewrite Hfresh. }
      iMod (phys_update _ a vo vn with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update ((S i, ts_pay_pin (Sf a) (Bg a)) : ts_elem) with "Hts Hte")
        as "[Hts Hte]".
      iModIntro.
      rewrite pin_tm_insert -!insert_union_l !big_sepM_insert //.
      iFrame "Hgh Hts Hbig".
      iSplitR.
      { iPureIntro. rewrite dom_insert_L. apply union_least; [|exact Hsub2].
        assert (Hin : a ∈ dom mem).
        { apply elem_of_dom_2 in Hmem. rewrite dom_union_L elem_of_union in Hmem.
          destruct Hmem as [Hx|Hx]; last done.
          apply not_elem_of_dom in Hfresh. set_solver + Hx Hfresh. }
        set_solver + Hin. }
      iSplitR.
      { iPureIntro. intros a' Ha'. rewrite dom_insert_L elem_of_union in Ha'.
        destruct Ha' as [Ha'|Ha'].
        - apply elem_of_singleton in Ha' as ->. by exists t.
        - exact (Hold2 a' Ha'). }
      rewrite /phys_ledger_pin. iFrame "Hpt Hte".
  Qed.

  Lemma ledger_store_pin_ok (g g' : gstate) (auth : agent)
      (Pold Pnew : gmap Arch.pa (bv 8)) (Bg : Arch.pa -> nat)
      (Sf : Arch.pa -> gset (bv 8)) :
    dom Pold = dom Pnew ->
    (* THE ONE NEW PREMISE *)
    (forall a v, Pnew !! a = Some v -> v ∈ Sf a) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew auth])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    pin_map_own Pold (DfracOwn 1) Bg Sf ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog)) (PWMsg Pnew auth) ∗
    ([∗ map] a ↦ v ∈ Pnew,
       phys_ledger_pin a (DfracOwn 1) v (S (length g.(glog))) (Bg a) (Sf a)).
  Proof.
    iIntros (Hdom Hin Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdomtm & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htvok & Hcov) & Hera).
    set (msg := PWMsg Pnew auth).
    assert (HLMfresh : LM !! length g.(glog) = None).
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length g.(glog)) msg HLMfresh with "Hm")
      as "[Hm #Hmsg]".
    iMod (mono_nat_own_update (length g'.(glog)) with "Hlen") as "[Hlen _]".
    { rewrite Hlog length_app /=. lia. }
    iMod (ledger_store_pin_bytes (length g.(glog)) Bg Sf Pold Pnew g.(gmem) TM
            Hdom with "Hgh Hts Hold")
      as "(%Hsub & %Hold2 & Hgh & Hts & Hbig)".
    assert (Hlen' : length g'.(glog) = S (length g.(glog))).
    { rewrite Hlog length_app /=. lia. }
    assert (Havf : forall x, (avf g x <= avf g' x)%nat).
    { intros x. rewrite /avf Hlog length_app /=.
      destruct (lt_dec x NCPU) as [Hx|Hx]; [apply Htv | lia]. }
    iMod (view_auth_update _ (avf g) (avf g') Havf with "Hv") as "Hv".
    iModIntro.
    iSplitL "Hgh"; first by rewrite Hmem.
    iFrame "Hbig". iFrame "Hmsg".
    iExists (pin_tm (length g.(glog)) Bg Sf Pnew ∪ TM),
            (<[length g.(glog) := msg]> LM).
    iFrame "Hts Hm Hlen Hv".
    iSplitR.
    { iPureIntro.
      assert (Hdpin : dom (pin_tm (length g.(glog)) Bg Sf Pnew) = dom Pnew).
      { apply set_eq. intros k.
        by rewrite !elem_of_dom pin_tm_lookup fmap_is_Some. }
      rewrite dom_union_L Hdpin Hmem dom_union_L Hdomtm.
      by rewrite (subseteq_union_1_L _ _ Hsub). }
    iSplitR.
    { iPureIntro. intros a e Hlk.
      destruct (Pnew !! a) as [vn|] eqn:Hpa.
      - assert (Hl : pin_tm (length g.(glog)) Bg Sf Pnew !! a
                     = Some ((S (length g.(glog)), ts_pay_pin (Sf a) (Bg a)) : ts_elem))
          by (rewrite pin_tm_lookup Hpa //).
        rewrite (lookup_union_Some_l _ _ _ _ Hl) in Hlk. injection Hlk as <-.
        assert (Hmb : msg_byte msg a = Some vn)
          by (rewrite /msg_byte /=; exact Hpa).
        split_and!; [ | | by move => W0 HW0 | by move => R0 HR0 | by move => Wp HWp ].
        + exists vn. split.
          { rewrite Hmem. by apply lookup_union_Some_l. }
          rewrite Hlog Himg. apply latest_app_new. exact Hmb.
        + intros Sv' B' Heq. cbn in Heq. injection Heq as <- <-.
          destruct (Hold2 a ltac:(by apply elem_of_dom)) as (told & HTMa).
          rewrite Hlog Himg.
          apply pin_ok_app.
          * exact (ts_ok_pin _ _ _ _ _ _ _ (Htie _ _ HTMa) eq_refl).
          * right. exists vn. split; [exact Hmb | exact (Hin a vn Hpa)].
      - assert (Hl : pin_tm (length g.(glog)) Bg Sf Pnew !! a = None)
          by (rewrite pin_tm_lookup Hpa //).
        rewrite (lookup_union_r _ _ _ Hl) in Hlk.
        pose proof (Htie _ _ Hlk) as Hok.
        assert (Hmb : msg_byte msg a = None) by (rewrite /msg_byte /=; exact Hpa).
        split_and!.
        + destruct (ts_ok_latest _ _ _ _ _ Hok) as (v0 & Hgm & Hlat).
          exists v0. split.
          { rewrite Hmem. by rewrite lookup_union_r. }
          rewrite Hlog Himg. by apply latest_app_frame.
        + intros Sv' B' He2. rewrite Hlog Himg.
          apply (pin_ok_app_frame _ _ _ _ _ _
                   (ts_ok_pin _ _ _ _ _ _ _ Hok He2) Hmb).
        (* the WINDOW arm frames on the SAME per-address side condition
           as the pin's (TsoMemPa §12c) *)
        + intros W0 HW0. rewrite Hlog Himg.
          apply (win_ok1_app_frame _ _ _ _ _
                   (ts_ok_win _ _ _ _ _ _ Hok HW0) Hmb).
        + intros R0 HR0. rewrite Hlog Himg.
          apply (rel_ok1_app_frame _ _ _ _ _
                   (ts_ok_rel _ _ _ _ _ _ Hok HR0) Hmb).
        + intros Wp HWp. rewrite Hlog Himg.
          apply (pinw_ok1_app_frame _ _ _ _ _
                   (ts_ok_pinw _ _ _ _ _ _ Hok HWp) Hmb). }
    iSplitR.
    { iPureIntro. intros j. rewrite Hlog.
      destruct (decide (j = length g.(glog))) as [->|Hne].
      - rewrite lookup_insert. symmetry. by apply list_lookup_middle.
      - rewrite lookup_insert_ne; last congruence. rewrite HLM.
        destruct (decide (j < length g.(glog))%nat) as [Hlt|Hge].
        + by rewrite lookup_app_l.
        + rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia. }
    iPureIntro. split; [split_and! | rewrite Himg; exact Hera].
    - rewrite Hmem Hlog Himg flat_snoc /=. by rewrite -Hflat.
    - intros c. have := Htvok' c. lia.
    - rewrite Himg. exact Hcov.
  Qed.

  (* THE CONTEXT-FREE STORE GATE.  Same three of the four ghost steps as
     [ctx_store_ok] -- γts to the new top, γlogm persist, the mono_nat bump
     -- and NO dirty-set insert, because there is no context to insert into.
     The view premises are the same and for the same reason. *)
  (* A6.28: THE AUTHOR IS A PARAMETER, NOT THE AMBIENT HART.  The
     context-free ledger has no author tie to keep -- there is no dirty set
     and no load licence -- and the proof never uses the hart-ness of the
     message's [pm_tid] ([msg_byte] ignores it, and both [latest_app_*] laws
     are author-blind).  So one gate serves an M-mode store's append
     ([hart_agent cpu_id]) AND the DMA lease's reclaim ([disk_agent], A6.9).
     [CID] stays because the [gtv] premises quantify over harts. *)
  (* NO [CpuId] BINDER: the author is a PARAMETER, and the disk agent is not
     a hart (A6.48 ruling 4 -- [WpUart]'s disk loop applies this at
     [disk_agent] and has no ambient hart to offer). *)
  Lemma ledger_store_ok (g g' : gstate) (auth : agent)
      (Pold Pnew : gmap Arch.pa (bv 8)) :
    dom Pold = dom Pnew ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew auth])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ map] a ↦ v ∈ Pold, phys_ledger a (DfracOwn 1) v) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    (* A6.47 ruling 1: the append's own message, PERSISTED, so the writer
       can hand its slot the AUTHOR tie -- that is what lets hart 0's own
       later walks discharge by store forwarding without any receipt.  The
       timestamp is exposed for the same reason: an existential [t] cannot
       be compared against the message index. *)
    ledger_msg_at (length g.(glog)) (PWMsg Pnew auth) ∗
    ([∗ map] a ↦ v ∈ Pnew,
       phys_ledger_at a (DfracOwn 1) v (S (length g.(glog)))).
  Proof.
    iIntros (Hdom Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdomtm & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htvok & Hcov) & Hera).
    set (msg := PWMsg Pnew auth).
    assert (HLMfresh : LM !! length g.(glog) = None).
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length g.(glog)) msg HLMfresh with "Hm")
      as "[Hm #Hmsg]".
    iMod (mono_nat_own_update (length g'.(glog)) with "Hlen") as "[Hlen _]".
    { rewrite Hlog length_app /=. lia. }
    iMod (ledger_store_bytes (length g.(glog)) Pold Pnew g.(gmem) TM Hdom
            with "Hgh Hts Hold") as "(%Hsub & Hgh & Hts & Hbig)".
    assert (Hlen' : length g'.(glog) = S (length g.(glog))).
    { rewrite Hlog length_app /=. lia. }
    assert (Havf : forall x, (avf g x <= avf g' x)%nat).
    { intros x. rewrite /avf Hlog length_app /=.
      destruct (lt_dec x NCPU) as [Hx|Hx]; [apply Htv | lia]. }
    iMod (view_auth_update _ (avf g) (avf g') Havf with "Hv") as "Hv".
    iModIntro.
    iSplitL "Hgh"; first by rewrite Hmem.
    iFrame "Hbig". iFrame "Hmsg".
    iExists (((fun _ : bv 8 => ((S (length g.(glog)), ts_pay_none) : ts_elem)) <$> Pnew) ∪ TM),
            (<[length g.(glog) := msg]> LM).
    iFrame "Hts Hm Hlen Hv".
    iSplitR.
    { iPureIntro. rewrite dom_union_L dom_fmap_L Hmem dom_union_L Hdomtm.
      by rewrite (subseteq_union_1_L _ _ Hsub). }
    iSplitR.
    { (* both halves; see [ctx_store_ok]'s note *)
      iPureIntro. intros a e Hlk.
      destruct (Pnew !! a) as [vn|] eqn:Hpa.
      - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), ts_pay_none) : ts_elem)) <$> Pnew) !! a
                     = Some ((S (length g.(glog)), ts_pay_none) : ts_elem))
          by (rewrite lookup_fmap Hpa //).
        rewrite (lookup_union_Some_l _ _ _ _ Hl) in Hlk. injection Hlk as <-.
        apply (ts_ok_unpinned _ _ _ _ _ vn).
        { rewrite Hmem. by apply lookup_union_Some_l. }
        rewrite Hlog Himg. apply latest_app_new. by rewrite /msg_byte /=.
      - assert (Hl : ((fun _ : bv 8 => ((S (length g.(glog)), ts_pay_none) : ts_elem)) <$> Pnew) !! a = None)
          by (rewrite lookup_fmap Hpa //).
        rewrite (lookup_union_r _ _ _ Hl) in Hlk.
        pose proof (Htie _ _ Hlk) as Hok.
        assert (Hmb : msg_byte msg a = None) by (rewrite /msg_byte /=; exact Hpa).
        split_and!.
        + destruct (ts_ok_latest _ _ _ _ _ Hok) as (v0 & Hgm & Hlat).
          exists v0. split.
          { rewrite Hmem. by rewrite lookup_union_r. }
          rewrite Hlog Himg. by apply latest_app_frame.
        + intros Sv Bp He2. rewrite Hlog Himg.
          apply (pin_ok_app_frame _ _ _ _ _ _
                   (ts_ok_pin _ _ _ _ _ _ _ Hok He2) Hmb).
        (* the WINDOW arm frames on the SAME per-address side condition
           as the pin's (TsoMemPa §12c) *)
        + intros W0 HW0. rewrite Hlog Himg.
          apply (win_ok1_app_frame _ _ _ _ _
                   (ts_ok_win _ _ _ _ _ _ Hok HW0) Hmb).
        + intros R0 HR0. rewrite Hlog Himg.
          apply (rel_ok1_app_frame _ _ _ _ _
                   (ts_ok_rel _ _ _ _ _ _ Hok HR0) Hmb).
        + intros Wp HWp. rewrite Hlog Himg.
          apply (pinw_ok1_app_frame _ _ _ _ _
                   (ts_ok_pinw _ _ _ _ _ _ Hok HWp) Hmb). }
    iSplitR.
    { iPureIntro. intros j. rewrite Hlog.
      destruct (decide (j = length g.(glog))) as [->|Hne].
      - rewrite lookup_insert. symmetry. by apply list_lookup_middle.
      - rewrite lookup_insert_ne; last congruence. rewrite HLM.
        destruct (decide (j < length g.(glog))%nat) as [Hlt|Hge].
        + by rewrite lookup_app_l.
        + rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia. }
    iPureIntro. split; [split_and! | rewrite Himg; exact Hera].
    - rewrite Hmem Hlog Himg flat_snoc /=. by rewrite -Hflat.
    - intros c. have := Htvok' c. lia.
    - rewrite Himg. exact Hcov.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE SUBMAP FORM: the writer owns MORE than it writes.              *)
  (*                                                                   *)
  (* [HartMemRun]'s user-tier walker carries its whole owned byte map    *)
  (* and writes a window inside it, so it needs the gate at             *)
  (* "footprint ⊆ owned" rather than at "footprint = owned".  The split  *)
  (* is done here, once, rather than at every walker arm: the owned map  *)
  (* is [Pold ∪ rest] at [Pold := mm ∩ Pnew] (stdpp's intersection keeps *)
  (* the LEFT values, i.e. the OLD bytes at the written keys), the gate  *)
  (* moves [Pold] to [Pnew], and the rejoined map is [Pnew ∪ mm] --      *)
  (* which is exactly [TsoMemPa.write_bytes_union]'s reading of          *)
  (* [write_bytes mm pa n v].                                           *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_store_sub_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (mm Pnew : gmap Arch.pa (bv 8)) :
    dom Pnew ⊆ dom mm ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew (hart_agent cpu_id)])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ map] a ↦ v ∈ mm, ctx_phys_pointsto ξ a (DfracOwn 1) v) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ map] a ↦ v ∈ Pnew ∪ mm, ctx_phys_pointsto ξ a (DfracOwn 1) v).
  Proof.
    iIntros (Hsub Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hown".
    set (Pold := mm ∩ Pnew).
    assert (HPsub : Pold ⊆ mm).
    { rewrite map_subseteq_spec. intros a b Hab.
      by apply lookup_intersection_Some in Hab as [? _]. }
    assert (Hdom : dom Pold = dom Pnew).
    { rewrite /Pold dom_intersection_L. set_solver. }
    assert (Hdisj : Pold ##ₘ mm ∖ Pold)
      by apply (map_disjoint_difference_r mm Pold Pold), reflexivity.
    assert (Hsplit : mm = Pold ∪ (mm ∖ Pold))
      by (symmetry; by apply map_difference_union).
    assert (Hdisj2 : Pnew ##ₘ mm ∖ Pold).
    { apply map_disjoint_dom. rewrite dom_difference_L -Hdom. set_solver + Pold. }
    assert (Hjoin : Pnew ∪ mm = Pnew ∪ (mm ∖ Pold)).
    { apply map_eq. intros a. destruct (Pnew !! a) as [b|] eqn:Hp.
      - by rewrite !(lookup_union_Some_l _ _ _ _ Hp).
      - rewrite !lookup_union_r //.
        destruct (mm !! a) as [c|] eqn:Hm; last first.
        { symmetry. apply lookup_difference_None. by left. }
        symmetry. rewrite lookup_difference_Some. split; first done.
        by rewrite /Pold lookup_intersection Hm Hp. }
    rewrite Hsplit big_sepM_union //.
    iDestruct "Hown" as "[Hfp Hrest]".
    rewrite -Hsplit.
    iMod (ctx_store_ok g g' ξ Pold Pnew Hdom Himg Hlog Hmem Htv Htvok'
            with "Hgh Hint Hrun Hfp") as "($ & $ & $ & Hfp)".
    iModIntro. rewrite Hjoin big_sepM_union //. iFrame "Hfp Hrest".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE WINDOW BRIDGE: a leaf's byte LIST and the log message's byte   *)
  (* MAP are the same resource.  [write_bytes]/[snap_of] is a foldr of  *)
  (* inserts over [seq 0 n] and the addresses are distinct              *)
  (* ([tso_pa_add_inj]), so the two big-ops agree conjunct for          *)
  (* conjunct.  This is what makes [ctx_store_ok]'s map form -- the one *)
  (* [TsoMemPa.write_bytes_union] states the arm's update in -- usable  *)
  (* at a leaf that owns [↦ₚ₈]-shaped bytes.                            *)
  (* ---------------------------------------------------------------- *)

  Lemma big_sepM_foldr_ins {A} (Φ : Arch.pa -> A -> iProp Σ)
      (f : nat -> A) (pa : Arch.pa) (l : list nat) :
    base.NoDup (pa_add pa <$> l) ->
    ([∗ list] j ∈ l, Φ (pa_add pa j) (f j)) ⊣⊢
    ([∗ map] a ↦ b ∈ foldr (fun j acc => <[pa_add pa j := f j]> acc) ∅ l,
       Φ a b).
  Proof.
    induction l as [|x xs IH]; intros Hnd.
    - by rewrite big_sepM_empty.
    - cbn [fmap list_fmap] in Hnd.
      pose proof (list_relations.NoDup_cons_1_1 _ _ Hnd) as Hx.
      pose proof (list_relations.NoDup_cons_1_2 _ _ Hnd) as Hnd2.
      cbn [foldr]. rewrite big_sepM_insert; last first.
      { apply not_elem_of_dom. rewrite tso_foldr_ins_dom dom_empty_L.
        rewrite right_id_L elem_of_list_to_set. exact Hx. }
      cbn [big_opL]. by rewrite (IH Hnd2).
  Qed.

  Lemma phys_ledger_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger (pa_add pa j) dq (nth_byte v j)) ⊣⊢
    ([∗ map] a ↦ b ∈ snap_of pa n v, phys_ledger a dq b).
  Proof.
    intros Hn. rewrite /snap_of /write_bytes.
    apply (big_sepM_foldr_ins (fun a b => phys_ledger a dq b)
             (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))).
    by apply tso_nodup_win.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE PINNED WINDOW (A6.53).  Same [big_sepM_foldr_ins] regrouping as *)
  (* [phys_ledger_win_map], with the allowed sets re-keyed from BYTE     *)
  (* OFFSET (which is how a word states them) to ADDRESS (which is how   *)
  (* the store gate's footprint map states them).  The re-keying is a    *)
  (* premise rather than a definition so the caller keeps its own        *)
  (* spelling -- [PtTree]'s is [pte_slot_set w] at the slot's base.      *)
  (* ---------------------------------------------------------------- *)
  Lemma phys_ledger_pin_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) (Bf : nat -> nat)
      (Sf : nat -> TsoMemPa.byteset) (Sg : Arch.pa -> TsoMemPa.byteset)
      (Bg : Arch.pa -> nat) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Sg (pa_add pa j) = Sf j) ->
    (forall j : nat, (j < N.to_nat n)%nat -> Bg (pa_add pa j) = Bf j) ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) dq (nth_byte v j) t (Bf j) (Sf j))
    ⊣⊢ pin_map_own (snap_of pa n v) dq Bg Sg.
  Proof.
    intros Hn HS HB. rewrite /pin_map_own /snap_of /write_bytes.
    rewrite <- (big_sepM_foldr_ins
                 (fun a b => ∃ t : nat, phys_ledger_pin a dq b t (Bg a) (Sg a))%I
                 (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))
                 ltac:(by apply tso_nodup_win)).
    apply big_opL_proper. intros k j Hk.
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    by rewrite (HS (0 + k)%nat ltac:(lia)) (HB (0 + k)%nat ltac:(lia)).
  Qed.

  (* THE PINNED WINDOW STORE, and it is the A/D write-back's own gate:   *)
  (* one message over the slot's eight bytes, the pin's bound and sets   *)
  (* UNCHANGED, and the only new premise is that each written byte lands *)
  (* in its offset's allowed set.                                        *)
  Lemma ledger_store_win_pin_okf `{CID : CpuId} (g g' : gstate)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) (Bf : nat -> nat)
      (Sf : nat -> TsoMemPa.byteset) (Sg : Arch.pa -> TsoMemPa.byteset)
      (Bg : Arch.pa -> nat) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Sg (pa_add pa j) = Sf j) ->
    (forall j : nat, (j < N.to_nat n)%nat -> Bg (pa_add pa j) = Bf j) ->
    (forall j : nat, (j < N.to_nat n)%nat -> nth_byte vnew j ∈ Sf j) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) (DfracOwn 1) (nth_byte vold j) t (Bf j) (Sf j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) (DfracOwn 1) (nth_byte vnew j) t (Bf j) (Sf j)).
  Proof.
    iIntros (Hn HS HB Hin Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    rewrite (phys_ledger_pin_win_map pa n vold _ Bf Sf Sg Bg Hn HS HB).
    iMod (ledger_store_pin_ok g g' (hart_agent cpu_id)
            (snap_of pa n vold) (snap_of pa n vnew) Bg Sg
            ltac:(by rewrite !dom_snap_of)
            ltac:(intros a b Hab;
                  destruct (snap_of_lookup_Some _ _ _ _ _ Hab) as (j & Hj & -> & ->);
                  rewrite (HS j ltac:(lia)); exact (Hin j ltac:(lia)))
            Himg Hlog ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & _ & Hnew)".
    iModIntro. rewrite (phys_ledger_pin_win_map pa n vnew _ Bf Sf Sg Bg Hn HS HB).
    rewrite /pin_map_own.
    iApply (big_sepM_mono with "Hnew"). iIntros (a v _) "H".
    by iExists (S (length g.(glog))).
  Qed.

  (* the [_at] window map, for the strengthened store gate below *)
  Lemma phys_ledger_at_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) (t : nat) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_at (pa_add pa j) dq (nth_byte v j) t) ⊣⊢
    ([∗ map] a ↦ b ∈ snap_of pa n v, phys_ledger_at a dq b t).
  Proof.
    intros Hn. rewrite /snap_of /write_bytes.
    apply (big_sepM_foldr_ins (fun a b => phys_ledger_at a dq b t)
             (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))).
    by apply tso_nodup_win.
  Qed.

  (* THE STRENGTHENED STORE GATE (A6.47 ruling 1).  Same premises as
     [ledger_store_win_ok]; what it hands back additionally is the append's
     OWN message fragment and the window at the NEW timestamp, which is
     what a page-table writer needs to re-establish its slot's licence --
     [ledger_vis_own] turns the pair into "visible to me at any view", and
     [ledger_vis_below] turns it into "visible to everyone past the bound"
     once the bound is published.  The weak form above is kept so the
     existing [Wobl_ram] payers do not move. *)
  Lemma ledger_store_win_at_ok `{CID : CpuId} (g g' : gstate)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger (pa_add pa j) (DfracOwn 1) (nth_byte vold j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog))
      (PWMsg (snap_of pa n vnew) (hart_agent cpu_id)) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_at (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)
         (S (length g.(glog)))).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    rewrite (phys_ledger_win_map pa n vold _ Hn).
    iMod (ledger_store_ok g g' (hart_agent cpu_id)
            (snap_of pa n vold) (snap_of pa n vnew)
            ltac:(by rewrite !dom_snap_of) Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & $ & Hnew)".
    iModIntro. by rewrite (phys_ledger_at_win_map pa n vnew _ _ Hn).
  Qed.

  Lemma ctx_phys_win_map (ξ : CtxId) (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add pa j) dq (nth_byte v j)) ⊣⊢
    ([∗ map] a ↦ b ∈ snap_of pa n v, ctx_phys_pointsto ξ a dq b).
  Proof.
    intros Hn. rewrite /snap_of /write_bytes.
    apply (big_sepM_foldr_ins (fun a b => ctx_phys_pointsto ξ a dq b)
             (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))).
    by apply tso_nodup_win.
  Qed.

  (* ... and the store gate in the shape a leaf's [Wobl_ram] is stated in:
     the arm's [write_bytes] update, the arm's own [snap_of] message, and
     the byte window on both sides. *)
  Lemma ctx_store_win_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add pa j) (DfracOwn 1) (nth_byte vold j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hold".
    rewrite (ctx_phys_win_map ξ pa n vold _ Hn).
    iMod (ctx_store_ok g g' ξ (snap_of pa n vold) (snap_of pa n vnew)
            ltac:(by rewrite !dom_snap_of) Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hrun Hold") as "($ & $ & $ & Hnew)".
    iModIntro. by rewrite (ctx_phys_win_map ξ pa n vnew _ Hn).
  Qed.

  (* ================================================================== *)
  (* THE CONTEXT-FREE LOAD GATE: A LEDGER BYTE PLUS A MACHINE RECEIPT   *)
  (* (tso-machine-flip.md A6.37, the secondary-hart half of the         *)
  (* corrected RULING 1 discharge plan)                                 *)
  (*                                                                   *)
  (* WHY IT IS NEEDED.  A6.20 built [phys_ledger] as the WRITE-ONLY     *)
  (* ledger byte on the argument that its consumer -- the kernel page   *)
  (* table, owned by a bare [inv] that cannot name a context -- would   *)
  (* only ever be READ through a strongly-ordered arm.  The owner's     *)
  (* overruling of RULING 1 deleted that arm, so those slots now need a *)
  (* read story, and it cannot be [ctx_phys_load_ok]'s: there is no     *)
  (* [own_context] to be had inside a shared invariant.                 *)
  (*                                                                   *)
  (* WHAT REPLACES THE CONTEXT'S BOUND IS THE MACHINE'S OWN RECEIPT.    *)
  (* [own_context] certifies -- my view has passed my context's bound B *)
  (* -- and nothing else about it is used here;                         *)
  (* here the caller instead exhibits [view_lb h F] -- minted at an     *)
  (* AMO/acquire leaf, §6 amendment A6.6(b) -- together with            *)
  (* [⌜t ≤ F⌝] for the byte's own timestamp.  Boot's message-passing    *)
  (* shape is exactly that: hart 0 writes the page table (every slot at *)
  (* some [t ≤ B]) and then the [started] flag at [F > B]; a secondary  *)
  (* that has READ the flag holds [view_lb h F], and every later walk   *)
  (* of the shared table discharges from the inv-opened slot fact.      *)
  (*                                                                   *)
  (* AND WITHIN ONE OPENING THE READ IS EXACT.  [phys_ledger_at] holds  *)
  (* the timestamp ELEMENT, and [era_interp]'s tie says that element IS *)
  (* the latest write at that address -- so there is no later message   *)
  (* at all, and any view at or above [t] returns exactly [v].  No      *)
  (* history predicate over the log, and no -- every later message is  *)
  (* an A/D variant -- invariant: the A/D write-back is itself a        *)
  (* [ledger_store_ok] under the same invariant and cannot interleave   *)
  (* inside an opening.  The modulo-A-D weakening the walk certificates *)
  (* need lives one tier up and is already there ([ptree_canon]).       *)
  (* ================================================================== *)

  (* THE GATE, one byte.  Same proof shape as [ctx_phys_load_ok]'s clean
     arm, with the context's [llb] bound replaced by the receipt: the
     receipt gives [F ≤ gtv], the premise gives [t ≤ F], so the byte's own
     latest write is BELOW every reachable view and [visibleb_below]
     closes it. *)
  (* ---------------------------------------------------------------- *)
  (* THE GENERAL GATE (A6.47 ruling 1): ONE lemma for both routes.  The *)
  (* caller exhibits a receipt at [B] and a per-timestamp LICENCE; the  *)
  (* licence's two arms are exactly [visibleb]'s two, so a secondary    *)
  (* hart uses [ledger_vis_below] with the boot receipt and hart 0 uses *)
  (* [ledger_vis_own] with the author fragment its own store handed     *)
  (* back, and NOTHING downstream has to know which.  ([view_lb_0]      *)
  (* makes the receipt free at [B = 0], which is the pure-forwarding    *)
  (* case.)                                                             *)
  (* ---------------------------------------------------------------- *)
  Lemma ledger_read_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t B : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ledger_vis (hart_agent cpu_id) B t -∗
    phys_ledger_at a dq v t -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    iIntros "Hgh Hint #HB #Hvis [Hpt Htse]".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HB") as %HBtvs.
    rewrite avf_hart in HBtvs.
    iAssert (⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
               visibleb (hart_agent cpu_id) tv' g.(glog) t = true⌝)%I as %Hvis.
    { iDestruct "Hvis" as "[%Hb | (%i & %mg & %Hti & Hi & %Htid)]".
      - iPureIntro. intros tv' Htv'. apply visibleb_below. lia.
      - iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
        iPureIntro. intros tv' _. rewrite Hti.
        apply (visibleb_own _ _ _ _ mg); [by rewrite -HLM | done]. }
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|by apply Hvis].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* ...AND ITS PREMISE IS A FACT OF THE MACHINE, NOT A DEBT ON THE     *)
  (* CLIENT (A6.78).  [RiscvLang.mm_ok]'s third conjunct says the era   *)
  (* image covers ALL of RAM, so the "no evidence" read is discharged   *)
  (* from [addr_is_ram] alone -- which is what A6.74 §(3) priced it at  *)
  (* and what A6.75 §(3) had to leave as a named residual because no    *)
  (* interp conjunct supplied it.                                       *)
  (*                                                                   *)
  (* A DEGENERATE WINDOW PAYLOAD ON THE LOCK WORD IS THEREFORE NOT      *)
  (* NEEDED, AND MUST NOT BE BUILT: [win_ok1]'s conjunct (1) says every *)
  (* message touching the cell writes the CLEAR word or the author's    *)
  (* own, and the lock word's writer is an AMO whose stored value is    *)
  (* the caller's register.  A6.75 §(3)'s two options were not          *)
  (* equivalent; this is the one that exists.                           *)
  (* ---------------------------------------------------------------- *)
  Lemma ledger_img_cover (g : gstate) (a : Arch.pa) :
    addr_is_ram a ->
    tso_interp_at riscv_eraGS g -∗ ⌜is_Some (g.(gimg) !! a)⌝.
  Proof.
    iIntros (Hram) "Hint".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as ((_ & _ & Hcov) & _).
    iPureIntro. apply Hcov.
    move: Hram. rewrite /addr_is_ram /ram_base /ram_size /ram_lo /ram_hi. lia.
  Qed.

  Lemma ledger_rpay_ok (g : gstate) (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t : nat) (R : ts_rel) :
    tso_interp_at riscv_eraGS g -∗ phys_ledger_rpay a dq v t R -∗
    ⌜rel_ok1 g.(gimg) g.(glog) a R⌝.
  Proof.
    iIntros "Hint [_ Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    iPureIntro. exact (ts_ok_rel _ _ _ _ _ _ (Htie _ _ HTM) eq_refl).
  Qed.

  Lemma ledger_rpay_mint1 (g : gstate) (a : Arch.pa) (v : bv 8) (t : nat)
      (R : ts_rel) :
    rel_ok1 g.(gimg) g.(glog) a R ->
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_at a (DfracOwn 1) v t ==∗
    tso_interp_at riscv_eraGS g ∗
    phys_ledger_rpay a (DfracOwn 1) v t R.
  Proof.
    iIntros (Hr) "Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    cbn in Hlat.
    iMod (ghost_map_update ((t, ts_pay_rel R) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro.
    iSplitR "Hpt Hts"; last (rewrite /phys_ledger_rpay; iFrame "Hpt Hts").
    iExists (<[a := ((t, ts_pay_rel R) : ts_elem)]> TM), LM.
    iFrame "Hauth Hm Hlen Hvw".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Ha' : a ∈ dom g.(gmem)) by (by eapply elem_of_dom_2).
      set_solver. }
    iSplitR; last (iPureIntro; split; [exact HLM | exact (conj Hmm Hera)]).
    iPureIntro. intros a' e Hlk.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Hlk. injection Hlk as <-.
      split_and!.
      + exists v0. split; [exact Hgm0 | exact Hlat].
      + move => Sv' B' Heq. discriminate Heq.
      + by move => W0 HW0.
      + move => R0 HR0. cbn in HR0. injection HR0 as <-. exact Hr.
      + by move => Wp HWp.
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.

  Lemma ledger_rpay_drop (g : gstate) (a : Arch.pa) (v : bv 8) (t : nat)
      (R : ts_rel) :
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_rpay a (DfracOwn 1) v t R ==∗
    tso_interp_at riscv_eraGS g ∗ phys_ledger_at a (DfracOwn 1) v t.
  Proof.
    iIntros "Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    cbn in Hlat.
    iMod (ghost_map_update ((t, ts_pay_none) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro. iFrame "Hpt Hts".
    iExists (<[a := ((t, ts_pay_none) : ts_elem)]> TM), LM.
    iFrame "Hauth Hm Hlen Hvw".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Ha' : a ∈ dom g.(gmem)) by (by eapply elem_of_dom_2).
      set_solver. }
    iSplitR; last (iPureIntro; split; [exact HLM | exact (conj Hmm Hera)]).
    iPureIntro. intros a' e Hlk.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Hlk. injection Hlk as <-.
      split_and!.
      + exists v0. split; [exact Hgm0 | exact Hlat].
      + by move => Sv' B' Heq.
      + by move => W0 HW0.
      + by move => R0 HR0.
      + by move => Wp HWp.
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.

  (* the runs over a list of offsets *)
  Local Lemma ledger_rpay_mint_run (g : gstate) (base : Arch.pa) (n : nat)
      (f : nat -> bv 8) (tf : nat -> nat) (Rf : nat -> ts_rel) (l : list nat) :
    (forall j, j ∈ l -> rel_ok1 g.(gimg) g.(glog) (pa_add base j) (Rf j)) ->
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ l, phys_ledger_at (pa_add base j) (DfracOwn 1) (f j) (tf j)) ==∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ l, phys_ledger_rpay (pa_add base j) (DfracOwn 1) (f j) (tf j) (Rf j)).
  Proof.
    induction l as [|j l IH]; intros Hok.
    - iIntros "Hint _". iModIntro. iFrame "Hint". done.
    - iIntros "Hint Hb".
      rewrite !big_sepL_cons. iDestruct "Hb" as "[Hbj Hbl]".
      assert (Hj : j ∈ j :: l) by set_solver.
      iMod (ledger_rpay_mint1 g (pa_add base j) (f j) (tf j) (Rf j) (Hok j Hj)
              with "Hint Hbj") as "(Hint & Hbj)".
      assert (Hok' : forall k, k ∈ l -> rel_ok1 g.(gimg) g.(glog) (pa_add base k) (Rf k))
        by (intros k Hk; apply Hok; set_solver).
      iMod (IH Hok' with "Hint Hbl") as "(Hint & Hbl)".
      iModIntro. iFrame "Hint Hbj Hbl".
  Qed.

  Local Lemma ledger_rpay_drop_run (g : gstate) (base : Arch.pa)
      (f : nat -> bv 8) (Rf : nat -> ts_rel) (l : list nat) :
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ l, ∃ t : nat, phys_ledger_rpay (pa_add base j) (DfracOwn 1) (f j) t (Rf j)) ==∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ l, phys_ledger (pa_add base j) (DfracOwn 1) (f j)).
  Proof.
    induction l as [|j l IH].
    - iIntros "Hint _". iModIntro. iFrame "Hint". done.
    - iIntros "Hint Hb".
      rewrite !big_sepL_cons. iDestruct "Hb" as "[(%t & Hbj) Hbl]".
      iMod (ledger_rpay_drop g (pa_add base j) (f j) t (Rf j) with "Hint Hbj")
        as "(Hint & Hbj)".
      iMod (IH with "Hint Hbl") as "(Hint & Hbl)".
      iModIntro. iFrame "Hint Hbl". by iApply phys_ledger_at_ledger.
  Qed.

  (* THE MINT: n cells, each at ITS OWN latest stamp, all at or under a bound
     [lo] that one of them attains, become a release window with per-byte
     floors = those stamps, floor bytes = their values, and an empty
     history.  (A6.126 §6: the init hart zeroes the used page byte by byte,
     so the two bytes of the used index have two stamps.) *)
  Lemma ledger_rpay_mint (g : gstate) (base : Arch.pa) (n : nat)
      (auth : agent) (lo : nat) (tf : nat -> nat) (f : nat -> bv 8) :
    (0 < n)%nat ->
    (forall k, (k < n)%nat -> (tf k <= lo)%nat) ->
    (exists k, (k < n)%nat /\ lo = tf k) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 n,
       phys_ledger_at (pa_add base j) (DfracOwn 1) (f j) (tf j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ seq 0 n,
       phys_ledger_rpay (pa_add base j) (DfracOwn 1) (f j) (tf j)
         (TsRel base n j auth lo tf f [])).
  Proof.
    iIntros (Hn Htf Hlo) "Hgh Hint Hb".
    iAssert (⌜forall k, (k < n)%nat -> is_Some (g.(gimg) !! pa_add base k)⌝)%I
      as %Hcov.
    { rewrite bi.pure_forall. iIntros (k). rewrite bi.pure_impl. iIntros (Hk).
      iDestruct (big_sepL_lookup _ (seq 0 n) k k with "Hb") as "Hbk".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iDestruct (phys_ledger_at_ledger with "Hbk") as "Hbk".
      iDestruct (phys_ledger_ram with "Hbk") as %Hram.
      iApply (ledger_img_cover g (pa_add base k) Hram with "Hint"). }
    iAssert (⌜forall k, (k < n)%nat ->
               latest g.(gimg) g.(glog) (pa_add base k) (tf k) (f k)⌝)%I as %Hlat.
    { rewrite bi.pure_forall. iIntros (k). rewrite bi.pure_impl. iIntros (Hk).
      iDestruct (big_sepL_lookup _ (seq 0 n) k k with "Hb") as "Hbk".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_latest_ok g (pa_add base k) (DfracOwn 1) (f k) (tf k)
                with "Hgh Hint Hbk"). }
    assert (Hlolen : (lo <= length g.(glog))%nat).
    { destruct Hlo as (k & Hk & ->).
      destruct (Hlat k Hk) as [Hb _]. exact (log_byte_some_le _ _ _ _ _ Hb). }
    iFrame "Hgh".
    iApply (ledger_rpay_mint_run g base n f tf
              (fun j => TsRel base n j auth lo tf f []) (seq 0 n) with "Hint Hb").
    intros j Hj. apply elem_of_seq in Hj.
    exact (rel_ok1_of_latest g.(gimg) g.(glog) base n j auth lo tf f
             ltac:(lia) Hlolen Htf Hlat Hcov).
  Qed.

  (* THE AUTHOR'S STORE, map-shaped (A6.126 §6): the machine appends ONE
     message [w] that covers the window and more (the device's completion
     writes the used element, the status byte, an IN buffer and the index
     word together).  The rest of [w] comes in as sealed cells and goes out
     stamped at the append; the window's cells drop their arm, ride the
     append with everything else, and are re-minted with the history
     extended by this store's position and bytes. *)
  Lemma ledger_store_rel_map_ok (g g' : gstate) (auth : agent)
      (old w : gmap Arch.pa (bv 8))
      (base : Arch.pa) (n : N) {m : N} (vold vnew : bv m)
      (lo : nat) (tf : nat -> nat) (fv : nat -> bv 8)
      (hist : list (nat * (nat -> bv 8))) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    snap_of base n vnew ⊆ w ->
    dom old = dom w ∖ dom (snap_of base n vold) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg w auth])%list ->
    g'.(gmem) = w ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ map] a ↦ b ∈ old, phys_ledger a (DfracOwn 1) b) -∗
    rel_cells base (N.to_nat n) (DfracOwn 1) auth lo tf fv (nth_byte vold) hist ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog)) (PWMsg w auth) ∗
    ([∗ map] a ↦ b ∈ w ∖ snap_of base n vnew,
       phys_ledger_at a (DfracOwn 1) b (S (length g.(glog)))) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_rpay (pa_add base j) (DfracOwn 1) (nth_byte vnew j)
         (S (length g.(glog)))
         (TsRel base (N.to_nat n) j auth lo tf fv
            (hist ++ [(S (length g.(glog)), nth_byte vnew)]))).
  Proof.
    iIntros (Hn Hsub Hdom Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold Hrel".
    rewrite /rel_cells.
    iAssert (⌜forall j, (j < N.to_nat n)%nat ->
               rel_ok1 g.(gimg) g.(glog) (pa_add base j)
                 (TsRel base (N.to_nat n) j auth lo tf fv hist)⌝)%I as %Hcov.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hrel") as (tj) "Hej".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_rpay_ok with "Hint Hej"). }
    assert (Hsnap : forall j : nat, (j < N.to_nat n)%nat ->
              msg_byte (PWMsg w auth) (pa_add base j) = Some (nth_byte vnew j)).
    { intros j Hj. rewrite /msg_byte /=.
      apply (lookup_weaken (snap_of base n vnew)); [| exact Hsub].
      assert (Hin : pa_add base j ∈ dom (snap_of base n vnew)).
      { rewrite dom_snap_of. apply elem_of_footprint. exists j.
        split; [lia | reflexivity]. }
      apply elem_of_dom in Hin as [b Hb].
      destruct (snap_of_lookup_Some _ _ _ _ _ Hb) as (j' & Hj' & Heq & ->).
      assert (Hjj : j = j')
        by (apply (tso_pa_add_inj base j j'); [lia | lia | exact Heq]).
      subst j'. exact Hb. }
    (* drop the arm: the window's cells become sealed *)
    iMod (ledger_rpay_drop_run g base (nth_byte vold)
            (fun j => TsRel base (N.to_nat n) j auth lo tf fv hist)
            (seq 0 (N.to_nat n)) with "Hint Hrel") as "(Hint & Hwin)".
    rewrite (phys_ledger_win_map base n vold _ Hn).
    (* the whole old map: the rest and the window, disjoint *)
    assert (Hdisj : old ##ₘ snap_of base n vold).
    { apply map_disjoint_dom. rewrite Hdom. apply disjoint_difference_l1. reflexivity. }
    iAssert ([∗ map] a ↦ b ∈ old ∪ snap_of base n vold, phys_ledger a (DfracOwn 1) b)%I
      with "[Hold Hwin]" as "Hold".
    { rewrite (big_sepM_union _ _ _ Hdisj). iFrame "Hold Hwin". }
    assert (Hdomw : dom (old ∪ snap_of base n vold) = dom w).
    { rewrite dom_union_L Hdom !dom_snap_of.
      rewrite difference_union_L union_comm_L. apply subseteq_union_1_L.
      rewrite -(dom_snap_of base n vnew). apply subseteq_dom. exact Hsub. }
    iMod (ledger_store_ok g g' auth (old ∪ snap_of base n vold) w Hdomw Himg Hlog
            Hmem Htv Htvok' with "Hgh Hint Hold") as "($ & Hint & $ & Hnew)".
    (* split the new cells: the rest and the window *)
    rewrite -{1}(map_difference_union (snap_of base n vnew) w Hsub).
    assert (Hdisj2 : snap_of base n vnew ##ₘ w ∖ snap_of base n vnew)
      by (apply map_disjoint_difference_r; reflexivity).
    rewrite (big_sepM_union _ _ _ Hdisj2).
    iDestruct "Hnew" as "[Hwin $]".
    rewrite -(phys_ledger_at_win_map base n vnew _ _ Hn).
    iApply (ledger_rpay_mint_run g' base (N.to_nat n) (nth_byte vnew)
              (fun _ => S (length g.(glog)))
              (fun j => TsRel base (N.to_nat n) j auth lo tf fv
                          (hist ++ [(S (length g.(glog)), nth_byte vnew)]))
              (seq 0 (N.to_nat n)) with "Hint Hwin").
    intros j Hj. apply elem_of_seq in Hj.
    rewrite Hlog Himg.
    exact (rel_ok1_app_store g.(gimg) g.(glog) (PWMsg w auth)
             base (N.to_nat n) j auth lo tf fv hist (nth_byte vnew)
             (Hcov j ltac:(lia)) eq_refl Hsnap).
  Qed.

  Lemma ledger_pinw_mint1 (g : gstate) (a : Arch.pa) (v : bv 8) (t : nat)
      (W : ts_pinw) :
    pinw_ok1 g.(gimg) g.(glog) a W ->
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_at a (DfracOwn 1) v t ==∗
    tso_interp_at riscv_eraGS g ∗
    phys_ledger_pinw a (DfracOwn 1) v t W.
  Proof.
    iIntros (Hr) "Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    cbn in Hlat.
    iMod (ghost_map_update ((t, ts_pay_pinw W) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro.
    iSplitR "Hpt Hts"; last (rewrite /phys_ledger_pinw; iFrame "Hpt Hts").
    iExists (<[a := ((t, ts_pay_pinw W) : ts_elem)]> TM), LM.
    iFrame "Hauth Hm Hlen Hvw".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Ha' : a ∈ dom g.(gmem)) by (by eapply elem_of_dom_2).
      set_solver. }
    iSplitR; last (iPureIntro; split; [exact HLM | exact (conj Hmm Hera)]).
    iPureIntro. intros a' e Hlk.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Hlk. injection Hlk as <-.
      split_and!.
      + exists v0. split; [exact Hgm0 | exact Hlat].
      + by move => Sv' B' Heq.
      + by move => W0 HW0.
      + by move => R0 HR0.
      + move => Wp HWp. cbn in HWp. injection HWp as <-. exact Hr.
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.

  Lemma ledger_pinw_drop (g : gstate) (a : Arch.pa) (v : bv 8) (t : nat)
      (W : ts_pinw) :
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_pinw a (DfracOwn 1) v t W ==∗
    tso_interp_at riscv_eraGS g ∗ phys_ledger_at a (DfracOwn 1) v t.
  Proof.
    iIntros "Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    cbn in Hlat.
    iMod (ghost_map_update ((t, ts_pay_none) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro. iFrame "Hpt Hts".
    iExists (<[a := ((t, ts_pay_none) : ts_elem)]> TM), LM.
    iFrame "Hauth Hm Hlen Hvw".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Ha' : a ∈ dom g.(gmem)) by (by eapply elem_of_dom_2).
      set_solver. }
    iSplitR; last (iPureIntro; split; [exact HLM | exact (conj Hmm Hera)]).
    iPureIntro. intros a' e Hlk.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Hlk. injection Hlk as <-.
      split_and!.
      + exists v0. split; [exact Hgm0 | exact Hlat].
      + by move => Sv' B' Heq.
      + by move => W0 HW0.
      + by move => R0 HR0.
      + by move => Wp HWp.
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.

  Lemma ledger_read_bytes_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : N) {m : N} (w : bv m) (dq : dfrac) (B : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, ledger_vis (hart_agent cpu_id) B t ∗
         phys_ledger_at (pa_add a j) dq (nth_byte w j) t) -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a n w⌝.
  Proof.
    iIntros "Hgh Hint #HB Hb".
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_add a j)
                 = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as (t) "[#Hvis Hbj]".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_vis_ok g (pa_add a j) dq (nth_byte w j) t B
                with "Hgh Hint HB Hvis Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. exact (HH j Hj tv' Htv').
  Qed.

End ctx.
