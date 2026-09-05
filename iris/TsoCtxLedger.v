(* TsoCtxLedger.v -- THE LEDGER'S MINTS, DROPS AND RELAXED READS.

   The third of TsoCtx.v's three files (read its header): the same
   [Section ctx], continued after TsoCtxStore.v.  The pin / wpay / rpay /
   pinw mint-and-drop pairs, the relaxed-cell and racy reads, the x-stamp
   lemmas and the sub-map store -- the device drivers' (VirtioProto,
   DiskInv) and the boot carve's gates.  Nothing above the drivers and the
   boot chain needs this file; import TsoCtx alone for the vocabulary. *)

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
Require Import TsoCtx TsoCtxStore.


Section ctx.
  Context `{!riscvGS Σ}.

  Lemma ctx_string_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'} ξ a dq s :
    ctx_string_pointsto (KTR := kt) ξ a dq s ⊢
    ctx_string_pointsto (KTR := kt') ξ a dq s.
  Proof.
    rewrite /ctx_string_pointsto. iIntros "H".
    iApply (big_sepL_mono with "H").
    iIntros (k b _) "H". iApply (ctx_ktier_mono kt kt' with "H").
  Qed.

  (* THE VIEW-RECEIPT MINT ([TsoCtxTwin2.twin_passed_get]): at the
     AMO-acquire leaf the hart's view sits at the log top, so the parked
     record's own [llb T] receipt yields the STABLE pair
     [hart_view_lb K ∗ ⌜T ≤ K⌝] that [ctx_resume]/[ctx_exchange]
     consume -- persistent-monotone, so it survives every step between
     the acquire and the swtch. *)
  Lemma hart_view_lb_get `{CID : CpuId} (g : gstate) (T : nat) :
    (length g.(glog) ≤ g.(gtv) cpu_id)%nat →
    tso_interp_at riscv_eraGS g -∗ llb loglen_name T -∗
    tso_interp_at riscv_eraGS g ∗
    hart_view_lb (g.(gtv) cpu_id) ∗ ⌜(T ≤ g.(gtv) cpu_id)%nat⌝.
  Proof.
    rewrite hart_view_lb_unseal /hart_view_lb_def.
    iIntros (Htop) "Hint #HT".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htv & Hcov) & Hera).
    iDestruct (llb_valid with "Hlen HT") as %HTlen.
    iDestruct (view_lb_get _ _ (avf g) (length g.(glog)) (hart_agent cpu_id)
                with "Hv Hlen") as "(Hv & Hlen & #Hrcpt)".
    { rewrite avf_hart. apply Htv. }
    rewrite avf_hart.
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iFrame "Hrcpt". iPureIntro. lia.
  Qed.

  (* ACQUIRE-SIDE MINT ([TsoCtxTwin2.ctx_dom_of_parked]): domination
     FROM a parked source INTO the running acquirer, whose hart sits at
     the log top (what the AMO delivers).  The one mint that needs the
     interp -- it must compare the source's stamp with the log length
     and raise the acquirer's bound to its hart's view. *)
  Lemma ctx_dom_of_parked `{CID : CpuId} (g : gstate) (ξ ξ' : CtxId) (T : nat) :
    (length g.(glog) ≤ g.(gtv) cpu_id)%nat →
    tso_interp_at riscv_eraGS g -∗ own_context ξ' -∗ ctx_parked ξ T ==∗
    tso_interp_at riscv_eraGS g ∗ own_context ξ' ∗
    ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_parked ξ T).
  Proof.
    rewrite own_context_unseal /own_context_def
            ctx_parked_unseal /ctx_parked_def ctx_dom_unseal /ctx_dom_def.
    iIntros (Htop) "Hint Hrun Hpk".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htv & Hcov) & Hera).
    iDestruct "Hrun"
      as "(%B' & %K & %W & %D' & [Hb' Hd'] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hpk" as "(%D & Hat & #HT & %HDT)".
    (* the source stamp is a legal log position, hence under the view *)
    iDestruct (llb_valid with "Hlen HT") as %HTlen.
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    (* raise the acquirer's bound to its (top) view *)
    iMod (mono_nat_own_update (g.(gtv) cpu_id) with "Hb'") as "[Hb' #Hlb']".
    { lia. }
    iDestruct (view_lb_get _ _ (avf g) (length g.(glog)) (hart_agent cpu_id)
                with "Hv Hlen") as "(Hv & Hlen & #Hrcpt)".
    { rewrite avf_hart. apply Htv. }
    rewrite avf_hart.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iModIntro.
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iSplitL "Hb' Hd'".
    { iExists (g.(gtv) cpu_id), (g.(gtv) cpu_id), W, D'. iFrame "Hb' Hd'".
      iSplitR; first iExact "Hrcpt".
      iSplitR; first done.
      iFrame "HW". iSplitR; first done.
      iApply (big_sepS_impl with "Hoks").
      iIntros "!>" (k Hk) "Hok".
      iApply (dirty_ok_mono with "Hok"). lia. }
    iSplitL "Hat1".
    { iExists T, T, (g.(gtv) cpu_id), D. iFrame "Hat1 Hlb'".
      iPureIntro. split_and!; [exact HDT | lia | lia]. }
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* A6.66 THE ACQUIRE-SIDE GATE, and at THIS machine it is honest.      *)
  (* [ctx_deposit] above is the release side and is INTERP-FREE (a       *)
  (* parked target's stamp may be raised at will).  Its dual is not:     *)
  (* claiming a parked record's facts INTO the running context needs the *)
  (* at-the-top evidence, because the claimer must show its own view     *)
  (* already covers the whole log -- that is [ctx_dom_of_parked]'s       *)
  (* [length glog ≤ gtv cpu_id] premise, and it is what the AMO leaf     *)
  (* actually establishes when it reads at the top.                      *)
  (*                                                                     *)
  (* THIS IS WHY THE FLIP MAKES THE LOCK KIT *BETTER*, NOT WORSE         *)
  (* (tso-port.md §0.18′): at SC the same lemma is provable with         *)
  (* [ctx_dom_unseal; done] and a CONJURED [hart_view_lb], because SC's  *)
  (* [ctx_dom] is vacuous.  Here the receipt is real and the conjured    *)
  (* lower bound has no role left at the acquire -- the interp supplies  *)
  (* it.  The premise is therefore a STRENGTHENING of the statement and  *)
  (* a WEAKENING of what the caller must invent.                         *)


  (* ---------------------------------------------------------------- *)
  (* THE STAMPED BYTE (claude-notes/projects/icache.md): a context's    *)
  (* fact PLUS a pure stamp -- its latest write is at or below [IK], an *)
  (* INSTRUCTION-view position.  Paired with the hart's [hart_iview_lb  *)
  (* IK] receipt this is what an instruction fetch pays with            *)
  (* ([ctx_xfetch_ok]): the icache agent sees no store forwarding, so a *)
  (* fetch at any view from the instruction view up reads the byte's    *)
  (* latest write only if that write is under the view.  Minted from a  *)
  (* RUNNING context's fact at a [fence.i] ([ctx_xstamp]), whose drain  *)
  (* covers everything the context owns at that instant; forgotten back *)
  (* to the plain fact for data use.  The stamp is pure and indexed by  *)
  (* [IK] rather than by a context ghost, so nothing in [CtxId] or the   *)
  (* token surface moves; a user store to the byte (which re-times it    *)
  (* above [IK]) is exactly what cannot be stamped -- executable pages   *)
  (* are the non-writable ones.                                          *)
  (* ---------------------------------------------------------------- *)
  Definition ctx_xpointsto_def `{KTR : !CurKtier} (ξ : CtxId) (IK : nat)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ (ppn : mword 44) (t : nat),
       kmap_at (svpn_of va) ppn KP_rw ∗
       ⌜(uint va < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn va)⌝ ∗
       ⌜ktier_pin cur_ktier ppn va⌝ ∗
       pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn va) dq v ∗
       (pa_of ppn va) ↪[ts_name]{dq} (t, ts_pay_none) ∗
       (llb (ctx_bound_name ξ) t
        ∨ dset_in (ctx_dirty_name ξ) (t, pa_of ppn va)) ∗
       ⌜(t <= IK)%nat⌝)%I.
  Lemma ctx_xpointsto_aux : { f | f = @ctx_xpointsto_def }.
  Proof. by eexists. Qed.
  Definition ctx_xpointsto `{KTR : !CurKtier} (ξ : CtxId) (IK : nat)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    proj1_sig ctx_xpointsto_aux KTR ξ IK va dq v.
  Lemma ctx_xpointsto_unseal `{KTR : !CurKtier} (ξ : CtxId) (IK : nat)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_xpointsto ξ IK va dq v = ctx_xpointsto_def ξ IK va dq v.
  Proof. unfold ctx_xpointsto. by rewrite (proj2_sig ctx_xpointsto_aux). Qed.

  Global Instance ctx_xpointsto_timeless `{KTR : !CurKtier} ξ IK va dq v :
    Timeless (ctx_xpointsto ξ IK va dq v).
  Proof. rewrite ctx_xpointsto_unseal /ctx_xpointsto_def. apply _. Qed.

  (* forgetting the stamp gives the plain fact back *)
  Lemma ctx_xpointsto_forget `{KTR : !CurKtier} ξ IK va dq v :
    ctx_xpointsto ξ IK va dq v ⊢ ctx_pointsto ξ va dq v.
  Proof.
    rewrite ctx_xpointsto_unseal /ctx_xpointsto_def
            ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & Hk & % & % & % & Hp & Hts & Hbit & _)".
    iExists ppn, t. by iFrame.
  Qed.

  (* the stamp only ever moves UP, with the instruction view *)
  Lemma ctx_xpointsto_mono `{KTR : !CurKtier} ξ IK IK' va dq v :
    (IK <= IK')%nat -> ctx_xpointsto ξ IK va dq v ⊢ ctx_xpointsto ξ IK' va dq v.
  Proof.
    intros Hle. rewrite !ctx_xpointsto_unseal /ctx_xpointsto_def.
    iIntros "(%ppn & %t & Hk & % & % & % & Hp & Hts & Hbit & %Ht)".
    iExists ppn, t. iFrame. iPureIntro. split_and!; [done|done|done|lia].
  Qed.

  (* THE STAMP, at a [fence.i]: a running context's fact is clean -- under
     the bound, which the hart's view dominates -- or dirty and either under
     the bound or this hart's own message, which [own_pub] covers; the
     drained instruction view passes both the hart's view and its own last
     message ([RiscvLang.mnode_step]'s Barrier arm), so it passes every
     timestamp the context owns at that instant. *)
  Lemma ctx_xstamp `{CID : CpuId} {KTR : CurKtier} (g : gstate)
      (ξ : CtxId) (IK : nat) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    (g.(gtv) cpu_id <= IK)%nat ->
    (own_pub (hart_agent cpu_id) g.(glog) <= IK)%nat ->
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_pointsto (KTR := KTR) ξ a dq v -∗
    tso_interp_at riscv_eraGS g ∗ own_context ξ ∗
    ctx_xpointsto (KTR := KTR) ξ IK a dq v.
  Proof.
    intros Htv Hpub.
    rewrite own_context_unseal /own_context_def
            ctx_pointsto_unseal /ctx_pointsto_def
            ctx_xpointsto_unseal /ctx_xpointsto_def.
    iIntros "Hint Hrun Hfact".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htv0 & Hcov) & Hera).
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hfact"
      as "(%ppn & %t & #Hk & %Hc & %Hr & %Hpin & Hpt & Htse & Hbit)".
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    iAssert (⌜(t <= IK)%nat⌝)%I as %HtIK.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid with "Hb Hcl") as %HtB. iPureIntro. lia.
      - iDestruct (dset_lookup with "Hd Hdt") as %HDt.
        iDestruct (big_sepS_elem_of _ _ _ HDt with "Hoks") as "[%HtB | Hown]".
        + iPureIntro. simpl in HtB. lia.
        + iDestruct "Hown" as (i m) "(%Hti & Hi & %Htid)".
          iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
          iPureIntro. simpl in Hti. rewrite Hti.
          rewrite HLM in HLi.
          pose proof (own_pub_lookup _ _ _ _ HLi Htid). lia. }
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iSplitL "Hb Hd".
    { iExists B, K, W, D. iFrame "Hb Hd HK HW Hoks". by iPureIntro. }
    iExists ppn, t. iFrame "Hk Hpt Htse Hbit". by iPureIntro.
  Qed.

  (* THE FETCH GATE: with the receipt that this hart's instruction view is
     at or above the stamp, the byte reads its value through the icache
     agent at every view from the instruction view up -- exactly
     [HartMFetch.fobl_ifetch]'s shape, byte by byte. *)
  Lemma ctx_xfetch_ok `{CID : CpuId} {KTR : CurKtier} (g : gstate)
      (ξ : CtxId) (IK itv : nat) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    (IK <= itv)%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ctx_xpointsto (KTR := KTR) ξ IK a dq v -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    ctx_xpointsto (KTR := KTR) ξ IK a dq v ∗
    ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗
      ⌜∀ tv', (itv ≤ tv')%nat →
         tso_read g.(gimg) g.(glog) (ifetch_agent (hart_agent cpu_id)) tv'
           (pa_of ppn a) = Some v⌝.
  Proof.
    intros HIK.
    rewrite ctx_xpointsto_unseal /ctx_xpointsto_def.
    iIntros "Hgh Hint Hfact".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htv0 & Hcov) & Hera).
    iDestruct "Hfact"
      as "(%ppn & %t & #Hk & %Hc & %Hr & %Hpin & Hpt & Htse & Hbit & %HtIK)".
    iDestruct (gen_heap_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iSplitL "Hgh"; first iExact "Hgh".
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iSplitL.
    { iExists ppn, t. iFrame "Hk Hpt Htse Hbit". by iPureIntro. }
    iExists ppn. iFrame "Hk". iPureIntro.
    intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|].
    apply visibleb_below. lia.
  Qed.


  (* the window analogue of [pin_map_own]: the footprint a window store
     hands in.  Same shape, and the [Wf] is a FUNCTION of the address
     because each byte's element names its own offset. *)
  Definition wpay_map_own (Pv : gmap Arch.pa (bv 8)) (dq : dfrac)
      (Wf : Arch.pa -> ts_win) : iProp Σ :=
    ([∗ map] a ↦ v ∈ Pv, ∃ t : nat, phys_ledger_wpay a dq v t (Wf a))%I.

  Lemma ledger_vis_own (h : agent) (B i : nat) (m : pwmsg) :
    pm_tid m = h -> ledger_msg_at i m -∗ ledger_vis h B (S i).
  Proof.
    iIntros (Htid) "#Hm". iRight. iExists i, m. iFrame "Hm".
    iSplit; by iPureIntro.
  Qed.


  (* the 8-byte tower, so a PT slot can be spelled at either tier *)
  Definition phys_ledger_word (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, phys_ledger (pa_add a j) dq (nth_byte w j))%I.


  Global Instance phys_ledger_word_timeless a dq w :
    Timeless (phys_ledger_word a dq w).
  Proof. rewrite /phys_ledger_word. apply _. Qed.

  Definition wpay_tm (i : nat) (Wf : Arch.pa -> ts_win)
      (Pv : gmap Arch.pa (bv 8)) : gmap Arch.pa ts_elem :=
    map_imap (fun a _ => Some ((S i, ts_pay_win (Wf a)) : ts_elem)) Pv.

  Local Lemma wpay_tm_lookup i Wf Pv a :
    wpay_tm i Wf Pv !! a
    = (fun _ : bv 8 => ((S i, ts_pay_win (Wf a)) : ts_elem)) <$> (Pv !! a).
  Proof.
    rewrite /wpay_tm map_lookup_imap. by destruct (Pv !! a).
  Qed.

  Local Lemma wpay_tm_empty i Wf : wpay_tm i Wf ∅ = ∅.
  Proof. apply map_eq. intros k. by rewrite wpay_tm_lookup lookup_empty. Qed.

  Local Lemma wpay_tm_insert i Wf (P : gmap Arch.pa (bv 8)) a v :
    wpay_tm i Wf (<[a := v]> P)
    = <[a := ((S i, ts_pay_win (Wf a)) : ts_elem)]> (wpay_tm i Wf P).
  Proof.
    apply map_eq. intros k. rewrite wpay_tm_lookup.
    destruct (decide (k = a)) as [->|Hne].
    - by rewrite !lookup_insert.
    - rewrite !lookup_insert_ne // wpay_tm_lookup //.
  Qed.

  Local Lemma ledger_store_wpay_bytes (i : nat) (Wold Wf : Arch.pa -> ts_win)
      (Pold Pnew mem : gmap Arch.pa (bv 8)) (TM : gmap Arch.pa ts_elem) :
    dom Pold = dom Pnew ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    ghost_map_auth ts_name 1 TM -∗
    wpay_map_own Pold (DfracOwn 1) Wold ==∗
    ⌜dom Pnew ⊆ dom mem⌝ ∗
    (* the OLD elements, so the caller can re-establish the pin tie on the
       footprint out of [TsoMemPa.win_ok1_app_store] rather than out of
       nothing *)
    ⌜forall a, a ∈ dom Pnew ->
       exists t, TM !! a = Some ((t, ts_pay_win (Wold a)) : ts_elem)⌝ ∗
    gen_heap_interp (hG := riscv_memGS) (Pnew ∪ mem) ∗
    ghost_map_auth ts_name 1 (wpay_tm i Wf Pnew ∪ TM) ∗
    ([∗ map] a ↦ v ∈ Pnew, phys_ledger_wpay a (DfracOwn 1) v (S i) (Wf a)).
  Proof.
    revert Pold. rewrite /wpay_map_own.
    induction Pnew as [|a vn P2 Hfresh IH] using map_ind; intros Pold Hdom.
    - rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hgh Hts _". iModIntro.
      rewrite wpay_tm_empty !left_id_L !big_sepM_empty.
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
      assert (HTMa : TM !! a = Some ((t, ts_pay_win (Wold a)) : ts_elem)).
      { rewrite lookup_union_r in Hlk; first exact Hlk.
        rewrite wpay_tm_lookup. by rewrite Hfresh. }
      iMod (phys_update _ a vo vn with "Hgh Hpt") as "[Hgh Hpt]".
      iMod (ghost_map_update ((S i, ts_pay_win (Wf a)) : ts_elem) with "Hts Hte")
        as "[Hts Hte]".
      iModIntro.
      rewrite wpay_tm_insert -!insert_union_l !big_sepM_insert //.
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
      rewrite /phys_ledger_wpay. iFrame "Hpt Hte".
  Qed.

  (* THE WINDOW STORE GATE: [ledger_store_pin_ok]'s twin for a cell that
     carries the racy payload rather than the pin.  It exists because the
     ordinary [ledger_store_ok] REPLACES the elements it writes with
     [ts_pay_none] -- correct, but it would drop the window claim the lock's
     readers assemble from.

     THE TWO ARMS OF [Hstore] ARE THE LOCK'S TWO STORES, and stating them
     as a disjunction is what keeps the gate honest: a release writes the
     CLEAR word and the author's own-last entry moves to the top (so the
     author may read "not mine" again); an acquire writes the author's OWN
     word and the entry is REVOKED (the author is excluded until it
     releases).  Every other agent's entry is untouched, and its four
     conjuncts frame on the author premise alone -- which is the same
     [auth] argument [ledger_store_ok] already takes. *)
  Lemma ledger_store_wpay_ok (g g' : gstate) (auth : agent)
      (Pold Pnew : gmap Arch.pa (bv 8))
      (base : Arch.pa) (n : nat) (lo : nat) (z : nat -> bv 8)
      (cp : agent -> nat -> bv 8) (own own' : agent -> option nat)
      (Wold Wf : Arch.pa -> ts_win) :
    dom Pold = dom Pnew ->
    (* the footprint IS the window, byte for byte -- and THE FLOOR IS
       FRAMED: both arms keep [lo], exactly as they keep [z] and [cp].
       Only [own] moves. *)
    (forall j, (j < n)%nat -> Wold (pa_add base j) = TsWin base n j z cp own lo) ->
    (forall j, (j < n)%nat -> Wf (pa_add base j) = TsWin base n j z cp own' lo) ->
    (forall a, a ∈ dom Pnew -> exists j, (j < n)%nat /\ a = pa_add base j) ->
    (* WHAT WAS WRITTEN -- the two arms above *)
    ((forall j, (j < n)%nat -> Pnew !! pa_add base j = Some (z j))
       /\ own' auth = Some (S (length g.(glog)))
     \/ (forall j, (j < n)%nat -> Pnew !! pa_add base j = Some (cp auth j))
       /\ own' auth = None) ->
    (forall h, h <> auth -> own' h = own h) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg Pnew auth])%list ->
    g'.(gmem) = Pnew ∪ g.(gmem) ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    wpay_map_own Pold (DfracOwn 1) Wold ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog)) (PWMsg Pnew auth) ∗
    ([∗ map] a ↦ v ∈ Pnew,
       phys_ledger_wpay a (DfracOwn 1) v (S (length g.(glog))) (Wf a)).
  Proof.
    iIntros (Hdom HWold HWf Hfoot Hstore Hoth Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
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
    iMod (ledger_store_wpay_bytes (length g.(glog)) Wold Wf Pold Pnew g.(gmem) TM
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
    iExists (wpay_tm (length g.(glog)) Wf Pnew ∪ TM),
            (<[length g.(glog) := msg]> LM).
    iFrame "Hts Hm Hlen Hv".
    iSplitR.
    { iPureIntro.
      assert (Hdpin : dom (wpay_tm (length g.(glog)) Wf Pnew) = dom Pnew).
      { apply set_eq. intros k.
        by rewrite !elem_of_dom wpay_tm_lookup fmap_is_Some. }
      rewrite dom_union_L Hdpin Hmem dom_union_L Hdomtm.
      by rewrite (subseteq_union_1_L _ _ Hsub). }
    iSplitR.
    { iPureIntro. intros a e Hlk.
      destruct (Pnew !! a) as [vn|] eqn:Hpa.
      - assert (Hl : wpay_tm (length g.(glog)) Wf Pnew !! a
                     = Some ((S (length g.(glog)), ts_pay_win (Wf a)) : ts_elem))
          by (rewrite wpay_tm_lookup Hpa //).
        rewrite (lookup_union_Some_l _ _ _ _ Hl) in Hlk. injection Hlk as <-.
        assert (Hmb : msg_byte msg a = Some vn)
          by (rewrite /msg_byte /=; exact Hpa).
        destruct (Hfoot a ltac:(by apply elem_of_dom)) as (j & Hj & ->).
        destruct (Hold2 (pa_add base j) ltac:(by apply elem_of_dom))
          as (told & HTMa).
        split_and!.
        + exists vn. split.
          { rewrite Hmem. by apply lookup_union_Some_l. }
          rewrite Hlog Himg. apply latest_app_new. exact Hmb.
        + intros Sv' B' Heq. rewrite (HWf j Hj) in Heq. discriminate Heq.
        + intros W0 HW0. rewrite (HWf j Hj) in HW0.
          cbn in HW0. injection HW0 as <-.
          rewrite Hlog Himg.
          apply (win_ok1_app_store _ _ _ base n j lo z cp own own').
          * rewrite -(HWold j Hj).
            exact (ts_ok_win _ _ _ _ _ _ (Htie _ _ HTMa) eq_refl).
          * cbn [pm_tid]. case: Hstore => [[Hcl Ho] | [Hme Ho]].
            -- left. split; [| exact Ho].
               move => k Hk. rewrite /msg_byte /=. exact (Hcl k Hk).
            -- right. split; [| exact Ho].
               move => k Hk. rewrite /msg_byte /=. exact (Hme k Hk).
          * cbn [pm_tid]. exact Hoth.
        + intros R0 HR0. rewrite (HWf j Hj) in HR0. discriminate HR0.
        + intros Wp HWp. rewrite (HWf j Hj) in HWp. discriminate HWp.
      - assert (Hl : wpay_tm (length g.(glog)) Wf Pnew !! a = None)
          by (rewrite wpay_tm_lookup Hpa //).
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

  (* the context-free gate in the shape a leaf's [Wobl_ram] is stated in --
     the A/D write-back's, and any other store by a tier whose owner is an
     invariant (A6.20) *)
  Lemma ledger_store_win_ok `{CID : CpuId} (g g' : gstate)
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
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    rewrite (phys_ledger_win_map pa n vold _ Hn).
    iMod (ledger_store_ok g g' (hart_agent cpu_id)
            (snap_of pa n vold) (snap_of pa n vnew)
            ltac:(by rewrite !dom_snap_of) Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & _ & Hnew)".
    iModIntro. rewrite (phys_ledger_win_map pa n vnew _ Hn).
    iApply (big_sepM_mono with "Hnew"). iIntros (a v _) "H".
    by iApply phys_ledger_at_ledger.
  Qed.

  Lemma ledger_store_win_pin_ok `{CID : CpuId} (g g' : gstate)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m) (B : nat)
      (Sf : nat -> TsoMemPa.byteset) (Sg : Arch.pa -> TsoMemPa.byteset) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Sg (pa_add pa j) = Sf j) ->
    (forall j : nat, (j < N.to_nat n)%nat -> nth_byte vnew j ∈ Sf j) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) pa n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) (DfracOwn 1) (nth_byte vold j) t B (Sf j)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_pin (pa_add pa j) (DfracOwn 1) (nth_byte vnew j) t B (Sf j)).
  Proof.
    intros Hn HS Hin.
    exact (ledger_store_win_pin_okf g g' pa n vold vnew (fun _ => B) Sf Sg
             (fun _ => B) Hn HS (fun j _ => eq_refl) Hin).
  Qed.

  (* §0.26′: the window bridge and the window gate at the VISIBILITY-FREE
     tier.  Same two lines as the registered pair above; the OLD side is
     free, the NEW side comes back registered and dirty. *)
  (* THE OLD SIDE IS FUNCTION-VALUED, NOT WORD-VALUED, and that is the
     whole point: a free window's bytes are NOT the bytes of any word the
     caller can name.  [snap_of] is this foldr at [f := nth_byte v], so
     the two footprints have the same domain by [tso_foldr_ins_dom]. *)
  Definition free_win_map (pa : Arch.pa) (nn : nat) (f : nat -> bv 8)
      : gmap Arch.pa (bv 8) :=
    foldr (fun j acc => <[pa_add pa j := f j]> acc) ∅ (seq 0 nn).

  Lemma dom_free_win_map (pa : Arch.pa) (nn : nat) (f : nat -> bv 8) :
    dom (free_win_map pa nn f) = list_to_set (pa_add pa <$> seq 0 nn).
  Proof.
    rewrite /free_win_map tso_foldr_ins_dom dom_empty_L. set_solver.
  Qed.

  Lemma dom_free_win_snap (pa : Arch.pa) (n : N) {m : N}
      (f : nat -> bv 8) (v : bv m) :
    dom (free_win_map pa (N.to_nat n) f) = dom (snap_of pa n v).
  Proof.
    rewrite dom_free_win_map /snap_of /write_bytes tso_foldr_ins_dom dom_empty_L.
    set_solver.
  Qed.

  Lemma phys_free_win_map (pa : Arch.pa) (nn : nat)
      (f : nat -> bv 8) (dq : dfrac) :
    (Z.of_nat nn <= 18446744073709551616)%Z ->
    ([∗ list] j ∈ seq 0 nn, phys_free (pa_add pa j) dq) ⊣⊢
    ([∗ map] a ↦ _ ∈ free_win_map pa nn f, phys_free a dq).
  Proof.
    intros Hn. rewrite /free_win_map.
    apply (big_sepM_foldr_ins (fun a (_ : bv 8) => phys_free a dq) f pa (seq 0 nn)).
    by apply tso_nodup_win.
  Qed.

  Lemma ctx_store_win_free_ok `{CID : CpuId} (g g' : gstate) (ξ : CtxId)
      (pa : Arch.pa) (n : N) {m : N} (vnew : bv m) :
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
       phys_free (pa_add pa j) (DfracOwn 1)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    own_context ξ ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hrun Hold".
    rewrite (phys_free_win_map pa (N.to_nat n) (fun _ => bv_0 8) _ Hn).
    iMod (ctx_store_free_ok g g' ξ (free_win_map pa (N.to_nat n) (fun _ => bv_0 8))
            (snap_of pa n vnew)
            (dom_free_win_snap pa n (fun _ => bv_0 8) vnew) Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hrun Hold") as "($ & $ & $ & Hnew)".
    iModIntro. by rewrite (ctx_phys_win_map ξ pa n vnew _ Hn).
  Qed.

  (* ... and the window form, [HartMFetch.fobl_ifetch]'s shape *)
  Lemma ctx_phys_xfetch_bytes_ok `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (IK itv : nat) (a : Arch.pa) (n : N) {m : N} (w : bv m) (dq : dfrac) :
    (IK <= itv)%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_xpointsto ξ IK (pa_add a j) dq (nth_byte w j)) -∗
    ⌜forall tv' : nat, (itv <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (ifetch_agent (hart_agent cpu_id))
         tv' a n w⌝.
  Proof.
    intros HIK. iIntros "Hgh Hint Hb".
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall tv' : nat, (itv <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (ifetch_agent (hart_agent cpu_id))
                   tv' (pa_add a j) = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ctx_phys_xfetch_ok g ξ IK itv (pa_add a j) dq (nth_byte w j) HIK
                with "Hgh Hint Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. exact (HH j Hj tv' Htv').
  Qed.

  (* >>> A6.119: THE PIN'S RETRACTION, and it is the mint read backwards.
     The owner of a pinned cell AT FULL FRACTION may give the pin up: the
     element's LATEST tie is untouched (the value does not move), and both the
     PIN and WINDOW ties are VACUOUS at [None], so nothing that was being
     relied on survives to be broken -- which is exactly why the option arm
     was made vacuous-at-None in the first place.

     ITS CLIENT is the lock word's release ([WpSconfLock]'s `sw x0`): the held
     arm's value set is [{1}] and release stores [0], so the pin CANNOT be
     preserved across it ([ledger_store_win_pin_ok] wants the stored value in
     the set).  The lock goes free and the word goes back to the plain ledger
     cell, which is precisely what the free arm of [WpLock.lock_word_at]
     holds.  Retract first, then store: the store is then the ordinary
     [ledger_store_win_at_ok] the free word already uses. <<< *)
  Lemma ledger_pin_drop (g : gstate) (a : Arch.pa) (v : bv 8)
      (t B : nat) (Sv : gset (bv 8)) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_pin a (DfracOwn 1) v t B Sv ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    phys_ledger_at a (DfracOwn 1) v t.
  Proof.
    iIntros "Hgh Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iMod (ghost_map_update ((t, ts_pay_none) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro. iFrame "Hgh Hpt Hts".
    iExists (<[a := ((t, ts_pay_none) : ts_elem)]> TM), LM.
    iFrame "Hauth Hm Hlen Hvw".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Ha : a ∈ dom g.(gmem)) by (by eapply elem_of_dom_2).
      set_solver. }
    iSplitR; last (iPureIntro; split; [exact HLM | exact (conj Hmm Hera)]).
    iPureIntro. intros a' e Hlk.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Hlk. injection Hlk as <-.
      split_and!.
      + exists v. split; [exact Hgm | exact Hlat].
      + by move => Sv' B' Heq.
      + by move => W0 HW0.
      + by move => R0 HR0.
      + by move => Wp HWp.
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.


  (* THE GHOST STEP, at an ALREADY-PROVED window claim.  Splitting the
     pure content off is what lets the window form below establish
     [win_ok1] ONCE, from the [n] cells' shared timestamp, before any
     element moves. *)
  Lemma ledger_wpay_mint1 (g : gstate) (a : Arch.pa) (v : bv 8) (t : nat)
      (W : ts_win) :
    win_ok1 g.(gimg) g.(glog) a W ->
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_at a (DfracOwn 1) v t ==∗
    tso_interp_at riscv_eraGS g ∗
    phys_ledger_wpay a (DfracOwn 1) v t W.
  Proof.
    iIntros (Hw) "Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    cbn in Hlat.
    iMod (ghost_map_update ((t, ts_pay_win W) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro.
    iSplitR "Hpt Hts"; last (rewrite /phys_ledger_wpay; iFrame "Hpt Hts").
    iExists (<[a := ((t, ts_pay_win W) : ts_elem)]> TM), LM.
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
      + move => W0 HW0. cbn in HW0. injection HW0 as <-. exact Hw.
      + by move => R0 HR0.
      + by move => Wp HWp.
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.

  (* THE WINDOW FORM the creator applies: [n] adjacent cells AT ONE
     TIMESTAMP become the [n] agreeing copies the reader assembles from,
     with that timestamp as the floor. *)
  Local Lemma ledger_wpay_mint_run (g : gstate) (base : Arch.pa) (n t : nat)
      (f : nat -> bv 8) (cp : agent -> nat -> bv 8) (l : list nat) :
    (forall j, (j < n)%nat ->
       win_ok1 g.(gimg) g.(glog) (pa_add base j)
         (TsWin base n j f cp (fun _ => Some t) t)) ->
    (forall j, j ∈ l -> (j < n)%nat) ->
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ l, phys_ledger_at (pa_add base j) (DfracOwn 1) (f j) t) ==∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ l,
       phys_ledger_wpay (pa_add base j) (DfracOwn 1) (f j) t
         (TsWin base n j f cp (fun _ => Some t) t)).
  Proof.
    intros Hwin.
    revert l. induction l as [|j l IH]; intros Hlt.
    - iIntros "Hint _". iModIntro. iFrame "Hint". done.
    - iIntros "Hint Hb".
      rewrite !big_sepL_cons. iDestruct "Hb" as "[Hbj Hbl]".
      assert (Hjn : (j < n)%nat) by (apply Hlt; set_solver).
      iMod (ledger_wpay_mint1 g (pa_add base j) (f j) t _ (Hwin j Hjn)
              with "Hint Hbj") as "(Hint & Hbj)".
      assert (Hlt' : forall k, k ∈ l -> (k < n)%nat)
        by (intros k Hk; apply Hlt; set_solver).
      iMod (IH Hlt' with "Hint Hbl") as "(Hint & Hbl)".
      iModIntro. iFrame "Hint Hbj Hbl".
  Qed.

  Lemma ledger_wpay_mint (g : gstate) (base : Arch.pa) (n t : nat)
      (f : nat -> bv 8) (cp : agent -> nat -> bv 8) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 n,
       phys_ledger_at (pa_add base j) (DfracOwn 1) (f j) t) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ seq 0 n,
       phys_ledger_wpay (pa_add base j) (DfracOwn 1) (f j) t
         (TsWin base n j f cp (fun _ => Some t) t)).
  Proof.
    iIntros "Hgh Hint Hb".
    (* the window's image coverage, off the cells' own RAM-ness plus
       [mm_ok]'s third conjunct -- extracted before anything moves *)
    iAssert (⌜forall k, (k < n)%nat -> is_Some (g.(gimg) !! pa_add base k)⌝)%I
      as %Hcov.
    { rewrite bi.pure_forall. iIntros (k). rewrite bi.pure_impl. iIntros (Hk).
      iDestruct (big_sepL_lookup _ (seq 0 n) k k with "Hb") as "Hbk".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iDestruct (phys_ledger_at_ledger with "Hbk") as "Hbk".
      iDestruct (phys_ledger_ram with "Hbk") as %Hram.
      iApply (ledger_img_cover g (pa_add base k) Hram with "Hint"). }
    (* ...and the SHARED TIMESTAMP's tie, one per byte.  THIS is the
       mint's whole content: [n] cells latest at one [t]. *)
    iAssert (⌜forall k, (k < n)%nat ->
               latest g.(gimg) g.(glog) (pa_add base k) t (f k)⌝)%I as %Hlat.
    { rewrite bi.pure_forall. iIntros (k). rewrite bi.pure_impl. iIntros (Hk).
      iDestruct (big_sepL_lookup _ (seq 0 n) k k with "Hb") as "Hbk".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_latest_ok g (pa_add base k) (DfracOwn 1) (f k) t
                with "Hgh Hint Hbk"). }
    iFrame "Hgh".
    iApply (ledger_wpay_mint_run g base n t f cp (seq 0 n)
              (fun j Hj => win_ok1_of_latest g.(gimg) g.(glog) base n j t f cp
                             Hj Hlat Hcov)
              with "Hint Hb").
    intros j Hj. apply elem_of_seq in Hj. lia.
  Qed.


  (* ---- THE HOLDER'S READ, at a cell whose payload is set ----
     [ledger_read_vis_ok]'s twin for a WPAY cell.  Same proof: the
     element's payload arm plays no part in the LATEST tie, which is all
     the read consumes.  It exists because the lock's owner cell carries
     the racy payload and its HOLDER still wants the exact value it
     itself wrote. *)
  Lemma ledger_read_wpay_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t B : nat) (W : ts_win) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ledger_vis (hart_agent cpu_id) B t -∗
    phys_ledger_wpay a dq v t W -∗
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

  (* and its window form, in the shape a load leaf's obligation wants *)
  Lemma ledger_read_wpay_bytes_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : nat) {m : N} (w : bv m) (dq : dfrac) (B : nat)
      (Wf : nat -> ts_win) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ([∗ list] j ∈ seq 0 n, ∃ t : nat, ledger_vis (hart_agent cpu_id) B t ∗
       phys_ledger_wpay (pa_add a j) dq (nth_byte w j) t (Wf j)) -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a
         (N.of_nat n) w⌝.
  Proof.
    iIntros "Hgh Hint #HB Hb".
    iAssert (⌜forall j : nat, (j < n)%nat ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_add a j)
                 = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb") as (t) "[#Hvis Hbj]".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_wpay_vis_ok g (pa_add a j) dq (nth_byte w j) t B (Wf j)
                with "Hgh Hint HB Hvis Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. apply HH; [lia|exact Htv'].
  Qed.


  (* ---- THE WINDOW STORE, in the shape the two cpu-field stores want ----
     [ledger_store_win_pin_ok]'s twin: the payload's [z], [cp] and FLOOR
     are unchanged and only [own] moves, which is exactly
     [win_ok1_app_store]'s two arms lifted to a whole word.  It hands the
     append's own message fragment back, because the AUTHOR of an acquire
     store is the hart whose later read of the cell must be exact. *)
  Lemma phys_ledger_wpay_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) (Wf : Arch.pa -> ts_win) (Wg : nat -> ts_win) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Wf (pa_add pa j) = Wg j) ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ∃ t : nat, phys_ledger_wpay (pa_add pa j) dq (nth_byte v j) t (Wg j))
    ⊣⊢ wpay_map_own (snap_of pa n v) dq Wf.
  Proof.
    intros Hn HW. rewrite /wpay_map_own /snap_of /write_bytes.
    rewrite <- (big_sepM_foldr_ins
                 (fun a b => ∃ t : nat, phys_ledger_wpay a dq b t (Wf a))%I
                 (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))
                 ltac:(by apply tso_nodup_win)).
    apply big_opL_proper. intros k j Hk.
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    by rewrite (HW (0 + k)%nat ltac:(lia)).
  Qed.

  (* ...and the same bridge at a FIXED timestamp, which is what the store
     gate hands back: every byte of the window was written by ONE message,
     so they share its position. *)
  Lemma phys_ledger_wpay_at_win_map (pa : Arch.pa) (n : N) {m : N}
      (v : bv m) (dq : dfrac) (t : nat)
      (Wf : Arch.pa -> ts_win) (Wg : nat -> ts_win) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    (forall j : nat, (j < N.to_nat n)%nat -> Wf (pa_add pa j) = Wg j) ->
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_wpay (pa_add pa j) dq (nth_byte v j) t (Wg j))
    ⊣⊢ ([∗ map] a ↦ b ∈ snap_of pa n v, phys_ledger_wpay a dq b t (Wf a)).
  Proof.
    intros Hn HW. rewrite /snap_of /write_bytes.
    rewrite <- (big_sepM_foldr_ins
                 (fun a b => phys_ledger_wpay a dq b t (Wf a))
                 (fun j => nth_byte v j) pa (seq 0 (N.to_nat n))
                 ltac:(by apply tso_nodup_win)).
    apply big_opL_proper. intros k j Hk.
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    by rewrite (HW (0 + k)%nat ltac:(lia)).
  Qed.

  Lemma ledger_store_win_wpay_ok `{CID : CpuId} (g g' : gstate)
      (base : Arch.pa) (n : N) {m : N} (vold vnew : bv m) (lo : nat)
      (z : nat -> bv 8) (cp : agent -> nat -> bv 8)
      (own own' : agent -> option nat) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    ((forall j, (j < N.to_nat n)%nat -> nth_byte vnew j = z j)
       /\ own' (hart_agent cpu_id) = Some (S (length g.(glog)))
     \/ (forall j, (j < N.to_nat n)%nat -> nth_byte vnew j = cp (hart_agent cpu_id) j)
       /\ own' (hart_agent cpu_id) = None) ->
    (forall h, h <> hart_agent cpu_id -> own' h = own h) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++ [PWMsg (snap_of base n vnew) (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) base n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), ∃ t : nat,
       phys_ledger_wpay (pa_add base j) (DfracOwn 1) (nth_byte vold j) t
         (TsWin base (N.to_nat n) j z cp own lo)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog))
      (PWMsg (snap_of base n vnew) (hart_agent cpu_id)) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_wpay (pa_add base j) (DfracOwn 1) (nth_byte vnew j)
         (S (length g.(glog))) (TsWin base (N.to_nat n) j z cp own' lo)).
  Proof.
    iIntros (Hn Hstore Hoth Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    assert (Hfoot : forall a, a ∈ dom (snap_of base n vnew) ->
              exists j, (j < N.to_nat n)%nat /\ a = pa_add base j).
    { intros a Ha. apply elem_of_dom in Ha. destruct Ha as (b & Hb).
      destruct (snap_of_lookup_Some _ _ _ _ _ Hb) as (j & Hj & -> & _).
      exists j. split; [lia | reflexivity]. }
    assert (Hsnap : forall j : nat, (j < N.to_nat n)%nat ->
              snap_of base n vnew !! pa_add base j = Some (nth_byte vnew j)).
    { intros j Hj.
      assert (Hin : pa_add base j ∈ dom (snap_of base n vnew)).
      { rewrite dom_snap_of. apply elem_of_footprint. exists j.
        split; [lia | reflexivity]. }
      apply elem_of_dom in Hin. destruct Hin as (b & Hb).
      rewrite Hb.
      destruct (snap_of_lookup_Some _ _ _ _ _ Hb) as (j' & Hj' & Heq & ->).
      assert (j = j') by (apply (tso_pa_add_inj base j j'); [lia|lia|exact Heq]).
      by subst j'. }
    assert (Hwritten :
      ((forall j, (j < N.to_nat n)%nat ->
          snap_of base n vnew !! pa_add base j = Some (z j))
         /\ own' (hart_agent cpu_id) = Some (S (length g.(glog))))
      \/ ((forall j, (j < N.to_nat n)%nat ->
             snap_of base n vnew !! pa_add base j = Some (cp (hart_agent cpu_id) j))
          /\ own' (hart_agent cpu_id) = None)).
    { case: Hstore => [[Hcl Ho] | [Hme Ho]].
      - left. split; [| exact Ho]. intros j Hj.
        rewrite (Hsnap j Hj) (Hcl j Hj) //.
      - right. split; [| exact Ho]. intros j Hj.
        rewrite (Hsnap j Hj) (Hme j Hj) //. }
    set (Wold := fun a : Arch.pa =>
           TsWin base (N.to_nat n) (tso_pa_off base a) z cp own lo).
    set (Wf := fun a : Arch.pa =>
           TsWin base (N.to_nat n) (tso_pa_off base a) z cp own' lo).
    assert (HWold : forall j : nat, (j < N.to_nat n)%nat ->
              Wold (pa_add base j) = TsWin base (N.to_nat n) j z cp own lo).
    { intros j Hj. rewrite /Wold (tso_pa_off_add base j ltac:(lia)) //. }
    assert (HWf : forall j : nat, (j < N.to_nat n)%nat ->
              Wf (pa_add base j) = TsWin base (N.to_nat n) j z cp own' lo).
    { intros j Hj. rewrite /Wf (tso_pa_off_add base j ltac:(lia)) //. }
    rewrite (phys_ledger_wpay_win_map base n vold (DfracOwn 1) Wold
               (fun j => TsWin base (N.to_nat n) j z cp own lo) Hn HWold).
    iMod (ledger_store_wpay_ok g g' (hart_agent cpu_id)
            (snap_of base n vold) (snap_of base n vnew)
            base (N.to_nat n) lo z cp own own' Wold Wf
            ltac:(by rewrite !dom_snap_of) HWold HWf
            Hfoot Hwritten
            Hoth Himg Hlog
            ltac:(by rewrite Hmem write_bytes_union) Htv Htvok'
            with "Hgh Hint Hold") as "($ & $ & $ & Hnew)".
    iModIntro.
    rewrite (phys_ledger_wpay_at_win_map base n vnew (DfracOwn 1)
               (S (length g.(glog))) Wf
               (fun j => TsWin base (N.to_nat n) j z cp own' lo) Hn HWf).
    iExact "Hnew".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE STORE-THEN-MINT GATE (A6.82 §(4)'s INVERTED ORDER).            *)
  (*                                                                   *)
  (* ONE store leaf's obligation does both halves: the clear word goes  *)
  (* down over the whole window, and the racy payload is minted at THAT *)
  (* STORE'S OWN POSITION.  A6.79's order was mint-then-store and it is *)
  (* what A6.81 refuted at [initlock]'s dynamic caller -- the mint       *)
  (* wanted an UNWRITTEN cell, and a lock inside a [kalloc]'d page has   *)
  (* [kfree]'s memset in its past.  With a floor the order inverts: the  *)
  (* floor IS the store's position, so the store must have HAPPENED      *)
  (* before the payload can name it, and the cell's pre-mint history     *)
  (* never appears in any conjunct.                                     *)
  (*                                                                   *)
  (* WHY THE MINT'S PREMISE IS DISCHARGED HERE AND NOWHERE ELSE: the     *)
  (* [n] cells come out of the store gate at ONE timestamp, which is     *)
  (* exactly [ledger_wpay_mint]'s input ([win_ok1_of_latest]).  No       *)
  (* other producer in the tree hands out a whole window at a shared     *)
  (* timestamp.                                                         *)
  (* ---------------------------------------------------------------- *)
  Lemma ledger_store_win_wpay_mint_frag_ok `{CID : CpuId} (g g' : gstate)
      (pa : Arch.pa) (n : N) {m : N} (vold vnew : bv m)
      (cp : agent -> nat -> bv 8) :
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
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_ledger_wpay (pa_add pa j) (DfracOwn 1) (nth_byte vnew j)
         (S (length g.(glog)))
         (TsWin pa (N.to_nat n) j (nth_byte vnew) cp
            (fun _ => Some (S (length g.(glog)))) (S (length g.(glog))))) ∗
    (* A6.120: THE STORE'S OWN-MESSAGE FRAGMENT, kept.  It was produced by
       [ledger_store_win_at_ok] underneath and dropped with an [_] -- the
       same throw-away A6.114 §4 found one gate over.  It is the creator's
       arm of [WpLock.lk_floor]: [ctx_wrote_register] below turns it into
       the ctx tower's own dirty witness. *)
    ledger_msg_at (length g.(glog))
      (PWMsg (snap_of pa n vnew) (hart_agent cpu_id)).
  Proof.
    iIntros (Hn Himg Hlog Hmem Htv Htvok') "Hgh Hint Hold".
    iMod (ledger_store_win_at_ok g g' pa n vold vnew Hn Himg Hlog Hmem Htv Htvok'
            with "Hgh Hint Hold") as "(Hgh & Hint & #Hmsg & Hnew)".
    iMod (ledger_wpay_mint g' pa (N.to_nat n) (S (length g.(glog)))
            (nth_byte vnew) cp with "Hgh Hint Hnew") as "(Hgh & Hint & Hnew)".
    iModIntro. iFrame "Hgh Hint Hnew Hmsg".
  Qed.

  (* the window form: eight pinned bytes, one per-offset set *)
  Lemma ledger_read_pin_bytes_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8) (B : nat)
      (Sf : nat -> gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ([∗ list] j ∈ seq 0 n, ∃ t : nat,
       phys_ledger_pin (pa_add a j) dq (f j) t B (Sf j)) -∗
    ⌜forall (h : agent) (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
       forall j : nat, (j < n)%nat ->
         exists b, tso_read g.(gimg) g.(glog) h tv' (pa_add a j) = Some b
                   /\ b ∈ Sf j⌝.
  Proof.
    iIntros "Hint #HB Hb".
    iAssert (⌜forall j : nat, (j < n)%nat ->
               forall (h : agent) (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
                 exists b, tso_read g.(gimg) g.(glog) h tv' (pa_add a j) = Some b
                           /\ b ∈ Sf j⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb") as (t) "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_pin_ok g (pa_add a j) dq (f j) t B (Sf j)
                with "Hint HB Hbj"). }
    iPureIntro. intros h tv' Htv' j Hj. exact (HH j Hj h tv' Htv').
  Qed.

  (* (5) THE "NO EVIDENCE" GATE (tso-machine-flip.md A6.74 §(3)'s third kit
     item, owner-approved).  The memo's site table marks the free-path lock
     word read "receipt in hand? no" and prices it at nothing.  At the real
     machine "no receipt" still owes a READ RESULT: the leaf must exhibit a
     value at every reachable view even when it concludes nothing about it.
     It is payable from image coverage alone -- [read_down] bottoms out at
     timestamp 0, which is visible at every view -- and it needs neither a
     receipt nor ownership of the byte's VALUE. *)
  (* PURE: it consumes no resource at all, which is the honest statement of
     "no evidence" -- the leaf's obligation is discharged by the machine's
     own totality over the image, not by anything the client owns. *)
  Lemma ledger_read_any_ok `{CID : CpuId} (g : gstate) (a : Arch.pa) (b : bv 8) :
    g.(gimg) !! a = Some b ->
    forall tv : nat, exists c,
      tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv a = Some c.
  Proof. intros Hi tv. exact (tso_read_total _ _ _ _ _ b Hi). Qed.

  Lemma ledger_read_any_ram_ok `{CID : CpuId} (g : gstate) (a : Arch.pa) :
    addr_is_ram a ->
    tso_interp_at riscv_eraGS g -∗
    ⌜forall tv : nat, exists c,
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv a = Some c⌝.
  Proof.
    iIntros (Hram) "Hint".
    iDestruct (ledger_img_cover g a Hram with "Hint") as %[b Hb].
    iPureIntro. exact (ledger_read_any_ok g a b Hb).
  Qed.

  (* ...and the WORD form the free-path leaf actually consumes: [n] RAM
     bytes each return SOMETHING, and [assemble_bytes] is what turns the
     [n] values into the one word the read node must exhibit.  The word is
     per-view, which is why this cannot be [Mobl_ram_ex]'s shape: a racy
     word has no single value good at every reachable view. *)
  Lemma ledger_read_any_word_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (n : nat) (m : N) :
    (8 * Z.of_nat n <= Z.of_N m)%Z ->
    (forall j, (j < n)%nat -> addr_is_ram (pa_add a j)) ->
    tso_interp_at riscv_eraGS g -∗
    ⌜forall tv : nat, exists w : bv m,
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv a
         (N.of_nat n) w⌝.
  Proof.
    iIntros (Hm Hram) "Hint".
    iAssert (⌜forall j : nat, (j < n)%nat ->
               forall tv : nat, exists c,
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add a j)
                 = Some c⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iApply (ledger_read_any_ram_ok g (pa_add a j) (Hram j Hj) with "Hint"). }
    iPureIntro. intros tv.
    (* NO CHOICE AXIOM: [tso_read] is a FUNCTION, so the per-offset byte is
       its own [default] and the existential above only has to say that the
       option is not [None]. *)
    pose (f := fun j : nat =>
            default (bv_0 8)
              (tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add a j))).
    exists (Z_to_bv m (assemble_bytes (f <$> seq 0 n))).
    intros j Hj.
    assert (Hjn : (j < n)%nat) by lia.
    assert (Hlen : length (f <$> seq 0 n) = n)
      by (rewrite length_fmap length_seq //).
    (* durable-notes' [ltac:] trap: both side conditions are about
       [length (f <$> seq 0 n)], which is an ATOM until [Hlen] is used --
       so they are named, not passed as [ltac:(lia)]. *)
    assert (Hw : (8 * Z.of_nat (length (f <$> seq 0 n)) <= Z.of_N m)%Z)
      by (rewrite Hlen; lia).
    assert (Hjl : (j < length (f <$> seq 0 n))%nat) by (rewrite Hlen; lia).
    rewrite (nth_byte_assemble_len m (f <$> seq 0 n) j Hw Hjl).
    assert (Hlk : (f <$> seq 0 n) !!! j = f j).
    { rewrite list_lookup_total_alt list_lookup_fmap lookup_seq_lt //. }
    rewrite Hlk /f.
    destruct (HH j Hjn tv) as (c & Hc). by rewrite Hc.
  Qed.

  (* THE HOLDER'S EXACT READ.  [B := 0] because the author arm is what pays
     here -- the reader IS the writer, so no view receipt beyond the trivial
     one is wanted ([TsoGhost.view_lb_0]). *)
  Lemma ledger_read_word4_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (w : bv 32) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_word4_vis (hart_agent cpu_id) 0 a dq w -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a 4 w⌝.
  Proof.
    iIntros "Hgh Hint [%Hal Hb]".
    iApply (ledger_read_bytes_vis_ok g a 4 w dq 0 with "Hgh Hint [] [Hb]").
    { iApply view_lb_0. }
    { change (N.to_nat 4) with 4%nat. iExact "Hb". }
  Qed.

  Lemma ledger_read_at_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t F : nat) :
    (t ≤ F)%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) F -∗
    phys_ledger_at a dq v t -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    iIntros (HtF) "Hgh Hint #HF [Hpt Htse]".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HF") as %HFtvs.
    rewrite avf_hart in HFtvs.
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|].
    apply visibleb_below. lia.
  Qed.

End ctx.
