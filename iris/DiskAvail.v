(* DiskAvail.v -- THE AVAIL-INDEX WORD'S PAYLOAD HALF (A6.124).

   [struct virtq_avail.idx] is written only by [vdisk_lock] holders and read
   only by them (the device READS it through the lease).  §0.35′(iv) case 3
   says its floor rides in the lock payload; A6.121 made [disk_res]
   context-indexed so that it can.  The split:

     - the DMA lease ([VirtioProto.virtio_proto]) keeps HALF of each of the
       word's two ledger cells, sealed ([avail_lease_half]) -- the device's
       view of the word and the publisher's full cell (halves joined inside
       the store) are both still there;
     - the payload keeps the other half with the STAMP EXPOSED and the FLOOR
       beside it ([avail_half]): a holder reads the word with its own half
       and cashes the floor against its running token ([WpLock.lk_floor_vis]
       + [TsoCtx.ledger_read_at_vis_ok]) -- no invariant opened; a publisher
       stores through the joined cell, registers its position
       ([TsoCtx.ctx_wrote_register]) and installs the right arm; the floor
       transports across release/acquire on both arms ([lk_floor_morph]).

   The boot creator's arm comes from FORGETTING the zeroed ctx bytes into
   the ledger ([TsoCtx.ctx_phys_pointsto_forget_floor]): clean is the boot
   context's bound, dirty is its own memset write, persisted. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
(* NB: no [SailStdpp.Values] import -- a [gmap Arch.pa _] written under it
   picks a different Countable instance from VirtioProto's (durable-notes'
   instance-leak trap); [mword] is spelled qualified below. *)
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import TsoMemPa TsoGhost TsoCtx CtxMorphTac.
Require Import KptPt KMap.
Require Import VirtioModel VirtioQueue WpVirtio VirtioProto.
Require Import WpLock.
Local Open Scope Z_scope.

Section DiskAvail.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  (* the payload's half of the word: per byte, the exposed stamp and the
     floor the holder cashes against its token *)
  Definition avail_half (pav : SailStdpp.Values.mword 64) (np : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 2, ∃ t : nat,
       phys_ledger_at (pa_add (pa_add pav 2%nat) j) (DfracOwn (1/2))
         (nth_byte (wrap16 np) j) t ∗
       lk_floor cur_ctx t)%I.

  Lemma avail_half_ram (pav : SailStdpp.Values.mword 64) (np : nat) :
    avail_half pav np -∗ ⌜addr_is_ram (pa_add pav 2%nat)⌝.
  Proof.
    rewrite /avail_half. iEval (cbn [seq]). iIntros "((%t & Hc & _) & _)".
    rewrite /phys_ledger_at /phys_pointsto pa_add_0.
    iDestruct "Hc" as "[[_ %Hr] _]". by iPureIntro.
  Qed.

  (* THE HOLDER'S READ, as the datum obligation of
     [WpSconfMem.wp_load_s_sconf_au_dat]: exact, on either arm of each
     byte's floor. *)
  Lemma avail_half_read_ok `{CID : CpuId} (g : gstate) (pav : SailStdpp.Values.mword 64) (np : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context cur_ctx -∗
    avail_half pav np -∗
    ⌜forall tvr : nat, (g.(gtv) cpu_id <= tvr)%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tvr
         (pa_add pav 2%nat) 2 (wrap16 np)⌝.
  Proof.
    iIntros "Hgh Hint Hrun H".
    iAssert (⌜forall j, (j < 2)%nat -> forall tvr, (g.(gtv) cpu_id <= tvr)%nat ->
               tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tvr
                 (pa_add (pa_add pav 2%nat) j) = Some (nth_byte (wrap16 np) j)⌝)%I
      with "[Hgh Hint Hrun H]" as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ _ j j with "H") as (t) "[Hc #Hfl]";
        [apply lookup_seq; split; lia|].
      iDestruct (lk_floor_vis with "Hrun Hfl") as "[Hrun (%K & #HK & #Hvis)]".
      iApply (ledger_read_at_vis_ok with "Hgh Hint HK Hvis Hc"). }
    iPureIntro. intros tvr Htvr j Hj. apply HH; [lia | exact Htvr].
  Qed.

  (* THE BOOT SPLIT: the two zeroed ctx bytes leave the tower as halves --
     the lease's sealed half and the payload's half with its floor. *)
  Lemma avail_split_init (pd pav pu : SailStdpp.Values.mword 64) :
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add (pa_add pav 2%nat) j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 2,
       (pa_add (pa_add pav 2%nat) j) ↦ₘ nth_byte (wrap16 0%nat) j) ==∗
    avail_lease_half (virtio_init_cfg pd pav pu) 0 ∗ avail_half pav 0.
  Proof.
    iIntros (Hs) "#Hkm H".
    assert (Havi : avail_idx_pa (virtio_init_cfg pd pav pu) = pa_add pav 2%nat)
      by reflexivity.
    rewrite /avail_lease_half /avail_half Havi.
    iAssert (|==> [∗ list] j ∈ seq 0 2,
       phys_ledger (pa_add (pa_add pav 2%nat) j) (DfracOwn (1/2))
         (nth_byte (wrap16 0%nat) j) ∗
       ∃ t : nat,
         phys_ledger_at (pa_add (pa_add pav 2%nat) j) (DfracOwn (1/2))
           (nth_byte (wrap16 0%nat) j) t ∗ lk_floor cur_ctx t)%I
      with "[H]" as ">H".
    { iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!>" (k j Hk) "Hb".
      apply lookup_seq in Hk. destruct Hk as [-> Hlt].
      iDestruct (ctx_pointsto_canonical with "Hb") as %Hc.
      assert (Hk2 : (0 + k < 2)%nat) by lia.
      iDestruct (kmap_static_claims_at (svpn_of (pa_add (pa_add pav 2%nat) (0 + k)%nat))
                   KP_rw (Hs _ Hk2) with "Hkm") as "#Hk0".
      iDestruct (ctx_pointsto_to_phys cur_ctx _ _ _ _
                   (pa_of_id (pa_add (pa_add pav 2%nat) (0 + k)%nat) Hc)
                   with "Hk0 Hb") as "Hb".
      iMod (ctx_phys_pointsto_forget_floor with "Hb") as (t) "[Hat Hfl]".
      iEval (rewrite phys_ledger_at_halves) in "Hat". iDestruct "Hat" as "[H1 H2]".
      iModIntro. iSplitL "H1"; [ by iApply phys_ledger_at_ledger | ].
      iExists t. iFrame "H2".
      iDestruct "Hfl" as "[Hfl | Hfl]";
        [ by iApply lk_floor_of_ctx | by iApply lk_floor_of_wrote ]. }
    iModIntro. rewrite big_sepL_sep. iDestruct "H" as "[$ $]".
  Qed.

  (* ================================================================= *)
  (* A6.125 step 4: THE KEPT HALVES OF A PIN.  A publisher's ctx cells   *)
  (* split into the lease's PIN OFFER (VirtioProto) and [keep_map]: per   *)
  (* address, half the stamp with its arm.  With the memory half the      *)
  (* lease hands back ([pin_back]) that is [hcell_map] -- the half ctx    *)
  (* cells -- which rides the vdisk_lock payload (CtxMorph) and joins the *)
  (* lease's sealed halves back into full ctx cells at withdraw.          *)
  (* ================================================================= *)
  Definition keep_map (ξ : CtxId) (m : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ _ ∈ m, ctx_cell_keep ξ a)%I.
  Definition hcell_map (ξ : CtxId) (m : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ m, ctx_phys_pointsto_h ξ a b)%I.
  Definition ccell_map (ξ : CtxId) (m : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ m, ctx_phys_pointsto ξ a (DfracOwn 1) b)%I.

  Lemma keep_map_union (ξ : CtxId) (m1 m2 : gmap Arch.pa (bv 8)) :
    m1 ##ₘ m2 -> keep_map ξ (m1 ∪ m2) ⊣⊢ keep_map ξ m1 ∗ keep_map ξ m2.
  Proof. intro H. rewrite /keep_map. by apply big_sepM_union. Qed.

  Lemma keep_map_empty (ξ : CtxId) : keep_map ξ ∅ ⊣⊢ emp.
  Proof. rewrite /keep_map. apply big_sepM_empty. Qed.

  Lemma keep_map_back (ξ : CtxId) (m : gmap Arch.pa (bv 8)) :
    keep_map ξ m -∗ pin_back m -∗ hcell_map ξ m.
  Proof.
    rewrite /keep_map /pin_back /hcell_map. iIntros "Hk Hb".
    iDestruct (big_sepM_sep_2 with "Hk Hb") as "H".
    iApply (big_sepM_mono with "H"). intros a b _. iIntros "[Hk Hb]".
    iApply (ctx_cell_keep_back with "Hk Hb").
  Qed.

  Lemma hcell_map_join (ξ : CtxId) (m : gmap Arch.pa (bv 8)) :
    hcell_map ξ m -∗ half_map m -∗ ccell_map ξ m.
  Proof.
    rewrite /hcell_map /half_map /ccell_map. iIntros "Hh Hl".
    iDestruct (big_sepM_sep_2 with "Hh Hl") as "H".
    iApply (big_sepM_mono with "H"). intros a b _. iIntros "[Hh Hl]".
    iDestruct (ctx_phys_pointsto_join with "Hh Hl") as "[_ $]".
  Qed.

  (* a ctx-tier byte under the static map is a full ctx cell at its own
     physical address ([ctx_ident_ledger] without the final forget) *)
  Lemma ctx_ident_phys (a : Arch.pa) (dq : dfrac) (b : bv 8) :
    kmap_static (svpn_of a) KP_rw ->
    kmap_static_claims -∗ a ↦ₘ{dq} b -∗ ctx_phys_pointsto cur_ctx a dq b.
  Proof.
    iIntros (Hs) "#Hcl H".
    iDestruct (ctx_pointsto_canonical with "H") as %Hc.
    iDestruct (kmap_static_claims_at (svpn_of a) KP_rw Hs with "Hcl") as "#Hk0".
    iApply (ctx_pointsto_to_phys cur_ctx (kpt_leaf_ppn (svpn_of a)) a dq b
              (pa_of_id a Hc) with "Hk0 H").
  Qed.

  (* a window of ctx bytes splits into its offer and its kept halves *)
  Lemma ctx_win_offer (a : Arch.pa) (n : nat) (f : nat -> bv 8) :
    Z.of_nat n < 18446744073709551616 ->
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 n, (pa_add a j) ↦ₘ f j) -∗
    pin_offer (range_map a n f) ∗ keep_map cur_ctx (range_map a n f).
  Proof.
    iIntros (Hn Hs) "#Hkm H".
    rewrite /pin_offer /keep_map
            (range_map_big_sepM (fun x b => (phys_pointsto x (DfracOwn (1/2)) b ∗
                                             phys_ledger x (DfracOwn (1/2)) b)%I) a n f Hn)
            (range_map_big_sepM (fun x _ => ctx_cell_keep cur_ctx x) a n f Hn)
            -big_sepL_sep.
    iApply (big_sepL_impl with "H"). iIntros "!>" (k j Hk) "Hb".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    assert (Hk' : (0 + k < n)%nat) by lia.
    iDestruct (ctx_ident_phys _ _ _ (Hs _ Hk') with "Hkm Hb") as "Hb".
    iApply ctx_phys_pointsto_offer_split. iExact "Hb".
  Qed.

  (* and a window of full ctx cells becomes ctx bytes again *)
  Lemma ctx_win_of_ccell (a : Arch.pa) (n : nat) (f : nat -> bv 8) :
    Z.of_nat n < 18446744073709551616 ->
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < n)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗
    ccell_map cur_ctx (range_map a n f) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add a j) ↦ₘ f j).
  Proof.
    iIntros (Hn Hs Hc) "#Hkm H".
    rewrite /ccell_map
            (range_map_big_sepM (fun x b => ctx_phys_pointsto cur_ctx x (DfracOwn 1) b) a n f Hn).
    iApply (big_sepL_impl with "H"). iIntros "!>" (k j Hk) "Hb".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    assert (Hk' : (0 + k < n)%nat) by lia.
    iDestruct (kmap_static_claims_at (svpn_of (pa_add a (0 + k)%nat)) KP_rw (Hs _ Hk')
                 with "Hkm") as "#Hk0".
    iApply (ctx_pointsto_of_phys cur_ctx (kpt_leaf_ppn (svpn_of (pa_add a (0 + k)%nat)))
              _ _ _ (pa_of_id _ (Hc _ Hk')) (Hc _ Hk')
              (ktier_pin_of_id _ _ _ (pa_of_id _ (Hc _ Hk'))) with "Hk0 Hb").
  Qed.
End DiskAvail.

Section DiskAvailMorph.
  Context `{!riscvGS Σ}.
  Global Instance avail_half_morph (pav : SailStdpp.Values.mword 64) (np : nat) :
    CtxMorph (λ ξ, avail_half (XI := ξ) pav np).
  Proof. rewrite /avail_half. ctx_morph_solve. all: apply lk_floor_morph. Qed.

  (* NB not [ctx_morph_solve]: [apply] would unfold the leaves' own ∃ *)
  Global Instance keep_map_morph (m : gmap Arch.pa (bv 8)) :
    CtxMorph (λ ξ, keep_map ξ m).
  Proof.
    rewrite /keep_map. apply ctx_morph_big_sepM. intros a b. apply ctx_morph_cell_keep.
  Qed.

  Global Instance hcell_map_morph (m : gmap Arch.pa (bv 8)) :
    CtxMorph (λ ξ, hcell_map ξ m).
  Proof.
    rewrite /hcell_map. apply ctx_morph_big_sepM. intros a b.
    apply ctx_morph_phys_pointsto_h.
  Qed.
End DiskAvailMorph.
