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
Require Import TsoMemPa TsoCtx CtxMorphTac.
Require Import KptPt KMap.
Require Import VirtioModel VirtioQueue WpVirtio VirtioProto.
Require Import DiskAddrs.   (* [d_ring] *)
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
  (* A6.126 §6: THE BOOT CARVE-OUT OF THE USED INDEX WORD.  The whole used *)
  (* page is the init hart's zeroed ctx bytes; the index word's two bytes  *)
  (* leave the tower STAMPED with the hart's floor at each stamp (the byte *)
  (* was its own write: [ctx_phys_pointsto_forget_floor]), the rest leaves *)
  (* sealed as the lease's map.                                           *)
  (* ================================================================= *)
  Lemma mem_win_to_phys_raw (p : Arch.pa) (n : nat) (dq : dfrac)
      (f : nat -> bv 8) :
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add p j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 n, mem_pointsto (pa_add p j) dq (f j)) -∗
    ([∗ list] j ∈ seq 0 n, phys_pointsto (pa_add p j) dq (f j)).
  Proof.
    iIntros (Hstat) "#Hb Hbytes".
    iApply (big_sepL_impl with "Hbytes").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    iApply (mem_ident_phys (pa_add p (0 + k)%nat) dq (f (0 + k)%nat)
              (Hstat (0 + k)%nat ltac:(lia)) with "Hb H").
  Qed.

  (* THE WINDOW KEEPS ITS LEDGER NOW (A6.48 ruling 4), and that reverses the
     sentence this bridge used to carry.  [↦ₘ] IS [ctx_pointsto], which
     CONTAINS the byte's latest-write timestamp element; the old bridge threw
     it away with [ctx_pointsto_forget] because the DMA tier was raw
     [phys_pointsto].  Now the tier is [TsoCtx.phys_ledger], so the element
     travels with the byte -- and that is exactly what lets the device's
     completion pay its own log append.  A6.9's "a raw byte has left the
     ledger for good" is unchanged as a statement; what changed is that the
     lease never leaves the ledger in the first place. *)
  Lemma ctx_ident_ledger (a : Arch.pa) (dq : dfrac) (b : bv 8) :
    kmap_static (svpn_of a) KP_rw ->
    kmap_static_claims -∗ a ↦ₘ{dq} b -∗ phys_ledger a dq b.
  Proof.
    iIntros (Hs) "#Hcl H".
    iDestruct (ctx_pointsto_canonical with "H") as %Hc.
    iDestruct (kmap_static_claims_at (svpn_of a) KP_rw Hs with "Hcl") as "#Hk0".
    iDestruct (ctx_pointsto_to_phys cur_ctx (kpt_leaf_ppn (svpn_of a)) a dq b
                 (pa_of_id a Hc) with "Hk0 H") as "H".
    by iApply ctx_phys_pointsto_ledger.
  Qed.

  Lemma mem_win_to_phys (p : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8) :
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add p j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 n, (pa_add p j) ↦ₘ{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, phys_ledger (pa_add p j) dq (f j)).
  Proof.
    iIntros (Hstat) "#Hb Hbytes".
    iApply (big_sepL_impl with "Hbytes").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    iApply (ctx_ident_ledger (pa_add p (0 + k)%nat) dq (f (0 + k)%nat)
              (Hstat (0 + k)%nat ltac:(lia)) with "Hb H").
  Qed.

  Lemma used_split_init (pd pav pu : SailStdpp.Values.mword 64) :
    (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add pu j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 4096, (pa_add pu j) ↦ₘ byte_zero) ==∗
    ∃ t0 t1 : nat,
      phys_map (used_page_rest (virtio_init_cfg pd pav pu)) ∗
      ([∗ list] j ∈ seq 0 2,
         phys_ledger_at (pa_add (used_idx_pa (virtio_init_cfg pd pav pu)) j)
           (DfracOwn 1) byte_zero (tf2 t0 t1 j)) ∗
      lk_floor cur_ctx t0 ∗ lk_floor cur_ctx t1.
  Proof.
    iIntros (Hs) "#Hkm H".
    assert (Hvu : vc_used (virtio_init_cfg pd pav pu) = pu) by reflexivity.
    assert (Hidx : forall j, pa_add (used_idx_pa (virtio_init_cfg pd pav pu)) j = pa_add pu (2 + j)).
    { intro j. unfold used_idx_pa, vq_idx_off. rewrite Hvu pa_off_add. reflexivity. }
    (* the page in three windows: 0..1, 2..3 (the word), 4..4095 *)
    change (seq 0 4096) with (seq 0 (2 + 4094)). rewrite (seq_app 2 4094 0).
    change (seq (0 + 2) 4094) with (seq 2 (2 + 4092)). rewrite (seq_app 2 4092 2).
    change (seq (2 + 2) 4092) with (seq 4 4092).
    rewrite !big_sepL_app.
    iDestruct "H" as "(H0 & H2 & H4)".
    (* the sealed windows *)
    iDestruct (mem_win_to_phys pu 2 (DfracOwn 1) (fun _ : nat => byte_zero)
                 ltac:(intros j Hj; apply Hs; lia) with "Hkm H0") as "H0".
    iAssert ([∗ list] j ∈ seq 0 4092, (pa_add pu (4 + j)) ↦ₘ byte_zero)%I
      with "[H4]" as "H4".
    { iEval (change (seq 4 4092) with (seq (4 + 0) 4092)) in "H4".
      iEval (rewrite -(fmap_add_seq 4 0 4092) big_sepL_fmap) in "H4". iExact "H4". }
    iAssert ([∗ list] j ∈ seq 0 4092, (pa_add (pa_add pu 4) j) ↦ₘ byte_zero)%I
      with "[H4]" as "H4".
    { iApply (big_sepL_impl with "H4"). iIntros "!>" (k j _) "H".
      rewrite pa_add_add. iExact "H". }
    iDestruct (mem_win_to_phys (pa_add pu 4) 4092 (DfracOwn 1) (fun _ : nat => byte_zero)
                 ltac:(intros j Hj; rewrite pa_add_add; apply Hs; lia) with "Hkm H4") as "H4".
    (* the word's two bytes, stamped, with the floors *)
    iAssert (|==> [∗ list] j ∈ seq 0 2,
       ∃ t : nat,
         phys_ledger_at (pa_add pu (2 + j)) (DfracOwn 1) byte_zero t ∗ lk_floor cur_ctx t)%I
      with "[H2]" as ">H2".
    { iEval (change (seq 2 2) with (seq (2 + 0) 2)) in "H2".
      iEval (rewrite -(fmap_add_seq 2 0 2) big_sepL_fmap) in "H2".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "H2").
      iIntros "!>" (k j Hk) "Hb".
      apply lookup_seq in Hk. destruct Hk as [-> Hlt].
      iDestruct (ctx_pointsto_canonical with "Hb") as %Hc.
      iDestruct (kmap_static_claims_at (svpn_of (pa_add pu (2 + k)%nat)) KP_rw
                   (Hs (2 + k)%nat ltac:(lia)) with "Hkm") as "#Hk0".
      iDestruct (ctx_pointsto_to_phys cur_ctx _ _ _ _
                   (pa_of_id (pa_add pu (2 + k)%nat) Hc) with "Hk0 Hb") as "Hb".
      iMod (ctx_phys_pointsto_forget_floor with "Hb") as (t) "[Hat Hfl]".
      iModIntro. iExists t. iFrame "Hat".
      iDestruct "Hfl" as "[Hfl | Hfl]";
        [ by iApply lk_floor_of_ctx | by iApply lk_floor_of_wrote ]. }
    iEval (cbn [seq]) in "H2".
    iEval (rewrite big_sepL_cons big_sepL_cons big_sepL_nil) in "H2".
    iDestruct "H2" as "((%t0 & Hc0 & #Hf0) & (%t1 & Hc1 & #Hf1) & _)".
    iModIntro. iExists t0, t1. iFrame "Hf0 Hf1".
    iSplitL "H0 H4".
    { rewrite used_page_rest_split Hvu.
      iDestruct (phys_map_range pu 2 (fun _ : nat => byte_zero) ltac:(lia)) as "Heq0".
      rewrite /phys_map.
      rewrite (big_sepM_union _ (range_map pu 2 (fun _ : nat => byte_zero))
                 (range_map (pa_add pu 4) 4092 (fun _ : nat => byte_zero))
                 ltac:(apply map_disjoint_dom_2; rewrite !range_map_dom;
                 apply elem_of_disjoint; intros x Hx Hy;
                 apply pa_range_elim in Hx as (i & Hi & ->); apply pa_range_elim in Hy as (j & Hj & Heq);
                 rewrite pa_add_add in Heq;
                 assert (i = 4 + j)%nat by (apply (pa_add_inj pu); [lia | lia | exact Heq]); lia)).
      iSplitL "H0".
      - rewrite (range_map_big_sepM _ pu 2 (fun _ : nat => byte_zero) ltac:(lia)).
        iExact "H0".
      - rewrite (range_map_big_sepM _ (pa_add pu 4) 4092 (fun _ : nat => byte_zero) ltac:(lia)).
        iExact "H4". }
    iEval (cbn [seq]). rewrite !big_sepL_cons big_sepL_nil.
    iSplitL "Hc0"; [| iSplitL "Hc1"; [| done]].
    - rewrite (Hidx 0%nat). iExact "Hc0".
    - rewrite (Hidx 1%nat). iExact "Hc1".
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

  Lemma hcell_map_union (ξ : CtxId) (m1 m2 : gmap Arch.pa (bv 8)) :
    m1 ##ₘ m2 -> hcell_map ξ (m1 ∪ m2) ⊣⊢ hcell_map ξ m1 ∗ hcell_map ξ m2.
  Proof. intro H. rewrite /hcell_map. by apply big_sepM_union. Qed.

  (* carve a 2-byte window out of a half-cell map by its own read (the ring
     entry out of the pin, A6.126 §6.7); one clone per tier *)
  Lemma hcell_map_carve (ξ : CtxId) (A : Arch.pa) (w : bv 16)
      (pin : gmap Arch.pa (bv 8)) :
    read_bytes pin A 2 = Some w ->
    hcell_map ξ pin -∗
    hcell_map ξ (range_map A 2 (nth_byte w)) ∗
    hcell_map ξ (pin ∖ range_map A 2 (nth_byte w)).
  Proof.
    intro Hr.
    set (rm := range_map A 2 (nth_byte w)).
    assert (Hsub : rm ⊆ pin).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec pin A 2 w Hr j). lia. }
    assert (Hd : rm ∪ (pin ∖ rm) = pin) by (apply map_difference_union; exact Hsub).
    assert (Hdj : rm ##ₘ pin ∖ rm)
      by (apply (map_disjoint_difference_r pin rm rm); reflexivity).
    assert (Heq : hcell_map ξ pin ⊣⊢ hcell_map ξ rm ∗ hcell_map ξ (pin ∖ rm)).
    { rewrite -(hcell_map_union ξ rm (pin ∖ rm) Hdj) Hd. reflexivity. }
    iIntros "Hpin". iEval (rewrite Heq) in "Hpin". iExact "Hpin".
  Qed.

  Lemma half_map_carve (A : Arch.pa) (w : bv 16) (pin : gmap Arch.pa (bv 8)) :
    read_bytes pin A 2 = Some w ->
    half_map pin -∗
    half_map (range_map A 2 (nth_byte w)) ∗
    half_map (pin ∖ range_map A 2 (nth_byte w)).
  Proof.
    intro Hr.
    set (rm := range_map A 2 (nth_byte w)).
    assert (Hsub : rm ⊆ pin).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec pin A 2 w Hr j). lia. }
    assert (Hd : rm ∪ (pin ∖ rm) = pin) by (apply map_difference_union; exact Hsub).
    assert (Hdj : rm ##ₘ pin ∖ rm)
      by (apply (map_disjoint_difference_r pin rm rm); reflexivity).
    assert (Heq : half_map pin ⊣⊢ half_map rm ∗ half_map (pin ∖ rm)).
    { rewrite -(half_map_union rm (pin ∖ rm) Hdj) Hd. reflexivity. }
    iIntros "Hpin". iEval (rewrite Heq) in "Hpin". iExact "Hpin".
  Qed.

  (* a half-cell window's RAM fact, off its first byte *)
  Lemma hcell_map_ram (ξ : CtxId) (A : Arch.pa) (w : bv 16) :
    hcell_map ξ (range_map A 2 (nth_byte w)) -∗ ⌜addr_is_ram A⌝.
  Proof.
    rewrite /hcell_map (range_map_big_sepM _ _ 2 _ ltac:(lia)).
    iEval (cbn [seq big_opL]). iIntros "(Hc & _)".
    rewrite /TsoCtx.ctx_phys_pointsto_h /phys_pointsto pa_add_0.
    iDestruct "Hc" as (t) "([_ %Hr] & _)". by iPureIntro.
  Qed.

  (* the holder's half cells and the lease's sealed halves agree on the
     cell's contents: both carry half the memory *)
  Lemma hcell_half_agree (ξ : CtxId) (A : Arch.pa) (w0 w1 : bv 16) :
    hcell_map ξ (range_map A 2 (nth_byte w0)) -∗
    half_map (range_map A 2 (nth_byte w1)) -∗ ⌜w0 = w1⌝.
  Proof.
    rewrite /hcell_map /half_map !(range_map_big_sepM _ _ 2 _ ltac:(lia)).
    iEval (cbn [seq big_opL]). iIntros "(H0 & H1 & _) (G0 & G1 & _)".
    iAssert (⌜nth_byte w0 0 = nth_byte w1 0⌝)%I as %E0.
    { rewrite /TsoCtx.ctx_phys_pointsto_h. iDestruct "H0" as (t) "(Hp & _)".
      iDestruct (TsoCtx.phys_ledger_forget with "G0") as "Hq".
      rewrite /phys_pointsto. iDestruct "Hp" as "[Hp _]". iDestruct "Hq" as "[Hq _]".
      iApply (pointsto_agree with "Hp Hq"). }
    iAssert (⌜nth_byte w0 1 = nth_byte w1 1⌝)%I as %E1.
    { rewrite /TsoCtx.ctx_phys_pointsto_h. iDestruct "H1" as (t) "(Hp & _)".
      iDestruct (TsoCtx.phys_ledger_forget with "G1") as "Hq".
      rewrite /phys_pointsto. iDestruct "Hp" as "[Hp _]". iDestruct "Hq" as "[Hq _]".
      iApply (pointsto_agree with "Hp Hq"). }
    iPureIntro.
    assert (Hmeq : range_map A 2 (nth_byte w0) = range_map A 2 (nth_byte w1)).
    { apply range_map_ext; [lia|]. intros j Hj.
      destruct j as [|[|j]]; [exact E0 | exact E1 | lia]. }
    pose proof (read_write_bytes ∅ A 2 w0 ltac:(lia)) as R0.
    pose proof (read_write_bytes ∅ A 2 w1 ltac:(lia)) as R1.
    rewrite (write_bytes_range_map A 2 w0) in R0.
    rewrite (write_bytes_range_map A 2 w1) in R1.
    change (N.to_nat 2) with 2%nat in R0. change (N.to_nat 2) with 2%nat in R1.
    rewrite Hmeq in R0. congruence.
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

  (* ================================================================= *)
  (* A6.126 §6: THE HANDLER'S RE-REGISTRATION.  A byte the DEVICE wrote,   *)
  (* stamped at its completion's position, becomes the handler's own ctx  *)
  (* byte once the handler's floor is past the stamp -- the ONE sound way *)
  (* a device-written byte re-enters a context (tso-port.md §1 ruling 2). *)
  (* ================================================================= *)
  Lemma ctx_word2_of_ccell (a : Arch.pa) (w : bv 16) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 2)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗
    ccell_map cur_ctx (range_map a 2 (nth_byte w)) -∗
    TsoCtx.ctx_word2_pointsto cur_ctx a (DfracOwn 1) w.
  Proof.
    iIntros (Hal Hs Hc) "#Hkm H".
    iDestruct (ctx_win_of_ccell a 2 (nth_byte w) ltac:(lia) Hs Hc with "Hkm H") as "Hm".
    rewrite /TsoCtx.ctx_word2_pointsto. iFrame "Hm". iPureIntro. exact Hal.
  Qed.

  Lemma ctx_byte_of_at (a : Arch.pa) (v : bv 8) (q : nat) :
    kmap_static (svpn_of a) KP_rw ->
    (uint (a : SailStdpp.Values.mword 64) < 274877906944)%Z ->
    kmap_static_claims -∗ TsoCtx.ctx_floor cur_ctx q -∗
    phys_ledger_at a (DfracOwn 1) v q -∗ a ↦ₘ v.
  Proof.
    iIntros (Hs Hc) "#Hkm #Hfl Hat".
    iDestruct (ctx_phys_pointsto_of_at_floor cur_ctx a v q with "Hat Hfl") as "Hb".
    iDestruct (kmap_static_claims_at (svpn_of a) KP_rw Hs with "Hkm") as "#Hk0".
    iApply (ctx_pointsto_of_phys cur_ctx (kpt_leaf_ppn (svpn_of a)) _ _ _
              (pa_of_id _ Hc) Hc (ktier_pin_of_id _ _ _ (pa_of_id _ Hc)) with "Hk0 Hb").
  Qed.

  Lemma ctx_bytes_of_at_seq (a : Arch.pa) (n : nat) (f : nat -> bv 8) (q : nat) :
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < n)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ TsoCtx.ctx_floor cur_ctx q -∗
    ([∗ list] j ∈ seq 0 n, phys_ledger_at (pa_add a j) (DfracOwn 1) (f j) q) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add a j) ↦ₘ f j).
  Proof.
    iIntros (Hs Hc) "#Hkm #Hfl H".
    iApply (big_sepL_impl with "H"). iIntros "!>" (k j Hk) "Hb".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    iApply (ctx_byte_of_at _ _ _ (Hs (0 + k)%nat ltac:(lia)) (Hc (0 + k)%nat ltac:(lia))
              with "Hkm Hfl Hb").
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

  (* ================================================================= *)
  (* A6.126 §6 ON THE POP MODEL (virtio-tso-port.md decision 4): THE   *)
  (* RING'S HOLDER HALVES.  The eight avail-ring cells stay in the      *)
  (* lease's control set at HALF/HALF for the queue's whole life; this  *)
  (* is the other half -- one half-cell window per cell, at whatever    *)
  (* contents it holds -- and it rides the vdisk_lock payload.  A       *)
  (* publisher takes its cell out of the list, joins it with the        *)
  (* lease's sealed half ([hcell_map_join]) into a full ctx cell,       *)
  (* stores through it and splits the new cell back the same way.  The  *)
  (* T-leg's per-publish pin/unpin of ring cells is NOT this design.    *)
  (* ================================================================= *)
  Definition ring_hcells (ξ : CtxId) (pav : SailStdpp.Values.mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, ∃ w : bv 16,
       hcell_map ξ (range_map (d_ring pav j) 2 (nth_byte w)))%I.

  Global Instance ring_hcells_morph (pav : SailStdpp.Values.mword 64) :
    CtxMorph (λ ξ, ring_hcells ξ pav).
  Proof. rewrite /ring_hcells. ctx_morph_solve. all: apply hcell_map_morph. Qed.

  (* a byte run regrouped into pairs *)
  Lemma big_sepL_seq_pairs (Φ : nat -> iProp Σ) (n : nat) :
    ([∗ list] j ∈ seq 0 (2 * n)%nat, Φ j)
    ⊣⊢ ([∗ list] k ∈ seq 0 n, Φ (2 * k)%nat ∗ Φ (2 * k + 1)%nat).
  Proof.
    induction n as [|n IH].
    - done.
    - replace (2 * S n)%nat with (S (S (2 * n)))%nat by lia.
      rewrite !seq_S !big_sepL_snoc IH. cbn [Nat.add].
      replace (S (2 * n))%nat with (2 * n + 1)%nat by lia.
      iSplit.
      + iIntros "[[Hl Ha] Hb]". iFrame "Hl Ha Hb".
      + iIntros "[Hl [Ha Hb]]". iFrame "Hl Ha Hb".
  Qed.

  (* THE BOOT SPLIT of the sixteen zeroed ring bytes: the pin-offer split
     ([ctx_win_offer]) -- the offer's ledger half is the lease's (the shape
     [VirtioProto.virtio_proto_intro] wants, via [ring_bytes_zero_range]),
     its stamp half rejoins the kept arms ([keep_map_back]) into the eight
     holder half-cells. *)
  Lemma ring_hcells_init `{XI : CurCtx} (pav : SailStdpp.Values.mword 64) :
    (forall j, (j < 16)%nat -> kmap_static (svpn_of (pa_add (pa_add pav 4%nat) j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 16, (pa_add (pa_add pav 4%nat) j) ↦ₘ byte_zero) -∗
    half_map (range_map (pa_add pav 4%nat) 16 (fun _ : nat => byte_zero)) ∗
    ring_hcells cur_ctx pav.
  Proof.
    iIntros (Hs) "#Hkm H".
    iDestruct (ctx_win_offer (pa_add pav 4%nat) 16 (fun _ : nat => byte_zero)
                 ltac:(lia) Hs with "Hkm H") as "[Hoff Hkeep]".
    iDestruct (pin_offer_split with "Hoff") as "[Hhalf Hback]".
    iFrame "Hhalf".
    iDestruct (keep_map_back with "Hkeep Hback") as "Hh".
    assert (Hcell : forall k : nat,
      hcell_map cur_ctx (range_map (d_ring pav k) 2 (nth_byte zero16))
      ⊣⊢ ctx_phys_pointsto_h cur_ctx (pa_add (pa_add pav 4%nat) (2 * k)%nat) byte_zero
         ∗ ctx_phys_pointsto_h cur_ctx (pa_add (pa_add pav 4%nat) (2 * k + 1)%nat) byte_zero).
    { intro k. rewrite /hcell_map (range_map_big_sepM _ _ 2 _ ltac:(lia)).
      cbn [seq big_opL]. rewrite right_id.
      rewrite zero16_wrap16 (nth_byte_wrap16_0 0 ltac:(lia)) (nth_byte_wrap16_0 1 ltac:(lia)).
      rewrite /d_ring !pa_add_add.
      replace (4 + 2 * k + 0)%nat with (4 + 2 * k)%nat by lia.
      replace (4 + 2 * k + 1)%nat with (4 + (2 * k + 1))%nat by lia.
      done. }
    rewrite /hcell_map (range_map_big_sepM _ _ 16 _ ltac:(lia)).
    change 16%nat with (2 * 8)%nat.
    rewrite (big_sepL_seq_pairs
               (fun j => ctx_phys_pointsto_h cur_ctx (pa_add (pa_add pav 4%nat) j) byte_zero) 8).
    rewrite /ring_hcells.
    iApply (big_sepL_impl with "Hh"). iIntros "!>" (k j Hk) "[H0 H1]".
    apply lookup_seq in Hk as [-> Hlt].
    iExists zero16. rewrite (Hcell (0 + k)%nat). iFrame "H0 H1".
  Qed.
End DiskAvailMorph.
