(* WpPlic.v: the S-mode, width-4 PLIC MMIO STORE weakest-precondition over
   the SIE-agnostic [sconf] bundle.

   A width-1 -> width-4 adaptation of [wp_sb_uart_s_sconf] (ProofUart.v),
   with the UART device leaf swapped for the width-4 PLIC device-store tower
   ([exec_execute_STORE_4_gpr_S_walk_dev], WpPlicExec.v).  Two forms of the
   store: [wp_sw_plic_pinv_s_sconf], which borrows the shared [plic_frag] half
   by opening the bare [plic_inv], and [wp_sw_plic_dev_s_sconf], that leaf's
   restatement over the [dev_inv] bundle.  (A RAW-[plic_frag] form was retired
   once [plicinit] was proved under the invariant: the PLIC gateway latches
   from step 0, so no CPU precondition may hold a device fragment raw, and
   nothing was left to call it.)  The translate side still runs
   REGIME-BLIND through [sr_transform]/[sr_absorb] (claim from the static bundle) at the derived regime
   instance [strans_regime] (the folded translation slot [Htr] threads
   straight through, no skolem-root open or repack), absorbing the
   device walk for ANY device vpn ([kpt_dev_vpn]).                          *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import DevModel RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad WpGpr InstrBytes WpMmodeLeafBase HartTp WpNext.
Require Import RegFile.
Require Import KptPt KMap.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt SRegime.
Require Import HartLift HartSpan HartSpanChar HartSwp HartSFrame HartSMem.
Require Import WpSmodePtEngine WpSmodePtFetch.
Require Import KptShare KptGoodb.
Require Import WpIntrInv.
Require Import HartMemRun.
Require Import PlicPlan DiskPtsto WpUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpPlicExec.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

(* the width-4 store tower's store word [wv] is a double [autocast]/subrange of
   the register value: [wv = autocast (subrange_vec_dec vrs2 31 0)] with
   [vrs2 : mword 32].  Collapsing the redundant outer layer bridges it to the
   caller-facing single-layer [storeword]. *)
Lemma subrange32_31_0_id (x : mword 32) : subrange_vec_dec x 31 0 = x.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (31 - 0 + 1)) with 32%N.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N in Hx.
  exact Hx.
Qed.

Lemma wv32_collapse (x : mword 32) :
  autocast (T := mword) (subrange_vec_dec x 31 0) = x.
Proof. rewrite subrange32_31_0_id. apply autocast_id. Qed.

Section WpPlic.
Context `{!riscvGS Σ, !xv6G Σ}.
Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
(* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
   bundle like the register map.  Implicit, so no call site changes. *)
Context {p : mword 64}.
Existing Instance riscv_memGS.

(* The SAME width-4 PLIC store, but for code that runs CONCURRENTLY on every
   hart and therefore cannot own [plic_frag] across its step: the shared half
   lives in the PLIC invariant and this leaf borrows it by opening [plic_inv]
   around the (atomic) write.  Nothing about the PLIC survives into the
   continuation -- what the caller gets instead is that the invariant, i.e.
   the kernel's PLIC plan [plic_ok] (PlicPlan.v), still holds.  The caller's
   obligation is correspondingly universal: the write must be DEFINED and must
   preserve the plan at EVERY state the plan admits, since the caller cannot
   know what the other harts have written.

   It takes the BARE [plic_inv], not the [dev_inv] bundle: the PLIC store
   touches no UART and no disk resource, so a function whose contract mentions
   only the PLIC ([plicinit]) can use it directly.  The bundle-taking form is
   the restatement [wp_sw_plic_dev_s_sconf] below, kept verbatim for the
   existing consumers. *)

(* ==================================================================== *)
(* THE READ-SIDE SIDE CONDITION [SrcOk] ON EVERY LEAF IN THIS SECTION.   *)
(* Read once; each leaf below carries a three-line pointer back here.    *)
(*                                                                      *)
(* WHAT IT IS.  These leaves take their operands out of CALLER-CHOSEN    *)
(* registers, spelled [rget m rs] -- a lookup in [tp_pin m] (HartTp.v),  *)
(* which is [m] with tp's slot overwritten by THIS HART's id.  So the    *)
(* value depends on the ambient hart at exactly one register, rs = tp,   *)
(* and agrees at every other ([HartTp.rget_hart_indep]).  Those operands *)
(* are computed from the ENTRY map, at the hart we came from, and appear *)
(* again inside the [wp_next] lambda, where every resource is about the  *)
(* hart we resume on.  Today the funnel's sigma-callback is instantiated  *)
(* at the entry hart so the two coincide; once that callback moves       *)
(* inside [WpNext.wp_next] -- so an instruction can execute on the hart  *)
(* a trap returned to -- the obligation arrives at the REBOUND hart      *)
(* while the caller's premise was stated at the ENTRY hart, and they     *)
(* agree only away from tp.  [IntrDefs.SrcOk rs] is that side condition. *)
(*                                                                      *)
(* WHY A CLASS AND NOT A PREMISE.  These leaves have no premise slot     *)
(* whose MEANING could be widened for free: a store writes no register   *)
(* at all, and a load's [rd_ok] slot is about the DESTINATION, not the   *)
(* source.  An ordinary premise would change ARITY at every reference,   *)
(* each of which would need a positional [ltac:(...)] in the right       *)
(* place.  An implicit instance argument shifts no positional argument,  *)
(* so the family converts with ZERO call-site churn -- and it cannot be  *)
(* [ops_ok] either, whose source conjuncts are guarded on [b = true]     *)
(* while an address has to be hart-independent at [b = true] as well.    *)
(* Multi-source leaves take ONE CLASS ARGUMENT PER SOURCE; they resolve  *)
(* independently, so there is no combinatorial blow-up.                  *)
(*                                                                      *)
(* THE PREMISES STAY SPELLED [rget m rs].  Respelling them hart-free as  *)
(* [m !!! Regidx rs] was MEASURED (on [WpSconfMem.wp_csdsp_s_sconf]) and *)
(* rejected: it breaks 99 consumer files, because callers normalise with *)
(* [rget]-shaped rewrites that then have nothing to match.  So the class *)
(* carries the side condition, the spelling does not move, and the       *)
(* reconciliation happens INSIDE each proof in one line, via             *)
(* [IntrDefs.src_ok_rget_indep].                                         *)
(*                                                                      *)
(* THAT LINE IS ALSO THE LEAF'S WIRING CHECK, so do not delete it as an  *)
(* unused hypothesis: it names the register the premise reads, so a      *)
(* class attached to the wrong parameter fails to typecheck HERE instead  *)
(* of shelving silently at a consumer's [Qed] -- an unresolved instance  *)
(* inside an [iApply] is SHELVED, not reported.                          *)
(* ==================================================================== *)

Lemma wp_sw_plic_pinv_s_sconf (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) :
  let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 4 8) 1) 0) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  (forall p, plic_ok p ->
     exists p', plic_write p (uint a8 - plic_base)%Z storeword = Some p' /\ plic_ok p') ->
  sie_cap_gpr kt m n false p -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  plic_inv -∗
  wp_next false p (fun (CID : CpuId) =>
    sie_cap_gpr kt m n false p -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn Hwrite.
  (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
     and this leaf's wiring check.  See the family note at the head of this
     section. *)
  assert (Hea_all : forall hh : CpuId,
            add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
    by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
  assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
    by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
  (* [a8] IS [ea]: the model's [subrange 63 0] / [sign_extend' 64] round trip.
     Every premise of this leaf is stated at [a8] and every engine argument
     below wants [ea], so the equation is proved once and used throughout. *)
  assert (Ha8ea : a8 = ea)
    by (unfold a8; rewrite subrange_id sign_extend'_id; reflexivity).
  rewrite Ha8ea in Hrange, Halign, Hcanon, Hdevvpn, Hwrite.
  (* the device window's own claim and canonicality, off [hw_config]'s static
     bundle -- a device page is mapped by the kernel table at every tier, so
     nothing here has to open an invariant to learn its [ppn]. *)
  assert (Hdevstatic : kmap_static (svpn_of ea) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  pose proof (static_canon_lo ea KP_rw Hdevstatic Hcanon) as Healt.
  pose proof (pa_of_id ea Healt) as Hpaid.
  assert (Hdcls : dev_cls 4 (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)).
  { rewrite Hpaid. split; [ exact (dev_addr_plic ea Hrange) | ].
    split; [ exact (plic_pa_not_in_clint ea Hrange) | ].
    exact (pma_access_io ea 4 plic_base (plic_base + plic_size)
             (proj1 Hrange) (proj2 Hrange) eq_refl eq_refl
             (pma_width_ok 4 eq_refl eq_refl)). }
  assert (Hpalign : is_aligned_paddr (Physaddr (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)) 4 = true)
    by (rewrite Hpaid; exact Halign).
  iIntros "Hcg Hpc Hinstr #Hpinv Hcont".
  iApply (wp_instr_s_sconf m n false false pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            (fun (_CIDx : CpuId) npc _ms' m' n' =>
               (⌜npc = add_vec_int pc (if is_rvc then 2 else 4)⌝ ∗
                ⌜m' = m⌝ ∗ ⌜n' = n⌝)%I)
            with "Hcg Hpc Hinstr [Hcont]").
  iNext.
  (* FREE THE NAME [CID] FOR THE REBOUND HART -- see the templates in
     WpSconfMem.v.  At [b = false] the two harts coincide, but the obligation
     is stated hart-generically, so the body is annotated all the same. *)
  rename CID into CID0.
  iIntros (CID Hs). rewrite /sconf_step_obl. iSplitR "Hcont".
  - (* ---------------- THE INSTRUCTION ---------------- *)
    iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
    assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
      by exact (src_ok_rget_indep m rs1 CID CID0).
    assert (Lpin_rs2 : tp_pin (CID := CID) m !!! Regidx rs2 = rget m rs2)
      by exact (src_ok_rget_indep m rs2 CID CID0).
    iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
      "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
        Hmdl & Hmenv)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                        HMPP & HTVM).
    (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
       [WpIntrInv.sda_slot_acc] below, the one place the two translation
       arms are told apart. *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
        %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
        %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    iDestruct "Hkmapb" as "[#Hkms _]".
    iDestruct (kmap_static_claims_at (svpn_of ea) KP_rw Hdevstatic
                 with "Hkms") as "#Hclaim".
    (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
           [sda_Drw] under the kernel table, the EMPTY set under Bare. ---- *)
    iDestruct (sda_slot_acc (CID := CID) kt (DfracOwn 1) mst0 MENVCFG_S
                 pmar0 eq_refl HSXL HMPRV (pma_all_ram Hpma_all)
                 with "Htr Hms Hpriv Hmenv Hpma Hhtif Hmisa")
      as (SD satp0 tlbv pcfg paddr)
      "(%Hdisj & %Hsub & %Hsok & %Hpok & Htrobl & Hrw & Hro & HRes & Hclose)".
    destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
    iAssert (sr_swp_res (strans_regime (CID := CID))
               (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
      with "[HRes]" as "HRes".
    { rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)).
      rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
    iDestruct "Hresv" as (rr) "Hfrag".
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                    (sign_extend' 64 imm) = ea)
      by (rewrite Lpin_rs1; reflexivity).
    (* the tower's lookups, POSED: an [ltac:] in argument position runs before
       the application's implicits are solved (durable-notes). *)
    pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
    pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
    pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
    assert (Lsv : autocast (T := mword)
              (subrange_vec_dec (tp_pin (CID := CID) m !!! Regidx rs2)
                 (Z.sub (Z.mul 4 8) 1) 0) = storeword)
      by (rewrite Lpin_rs2; reflexivity).
    assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
            = true) by (rewrite Lmst; exact HMXR).
    assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
            = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
    assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
            by (rewrite Lmst; exact HSXL).
    assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
              (register_lookup satp
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
            = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
            by (rewrite Lsatp;
                exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
    assert (Lep : effectivePrivilege (Store Data) (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
            = returnM Supervisor)
            by (rewrite Lmst;
                exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
    assert (Lva : is_aligned_vaddr (Virtaddr (add_vec
              (tp_pin (CID := CID) m !!! Regidx rs1) (sign_extend' 64 imm))) 4
            = true) by (rewrite Hea; exact Halign).
    iApply (swp_mono (CID := CID)
              with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
    2:{ iApply (swp_execute_STORE_dev_S4 (CID := CID)
                  SD sda_Dro (sda_Df (DfracOwn 1))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                  imm rs2 rs1 (tp_pin (CID := CID) m)
                  (pa_of (kpt_leaf_ppn (svpn_of ea)) ea) storeword
                  pmar0 pcfg paddr
                  True%I (sr_swp_res (strans_regime (CID := CID))) rr
                  (sr_swp_mode (strans_regime (CID := CID)) satp0)
                  Lsv
                  Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                  (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                  (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                  (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                  (sda_rs_htif _ _ _ _ _ _ _)
                  Lmxr Lpmm Lsxl
                  (hval_transform_effective_address_S_mode
                     (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                        (sign_extend' 64 imm))
                     (Store Data)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                     (sda_rs_priv _ _ _ _ _ _ _)
                     Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                  (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                  Lep
                  HA Hord HW Hcov (pma_all_io Hpma_all) Hdcls
                  Lva Hpalign
                  with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] []").
        - (* the data translation, at the DEVICE page's static claim *)
          iIntros "Hfrag HRes Hrw Hro".
          rewrite Hea.
          iApply ("Htrobl" $! KT0 (Store Data) KP_rw
                    ea (kpt_leaf_ppn (svpn_of ea)) rr
                    with "[%] [%] [%] [%] [%] Hwit Hclaim Hcert
                    Hfrag HRes Hrw Hro").
          + apply _.
          + exact (or_intror (or_intror (or_introl eq_refl))).
          + exact eq_refl.
          + exact Healt.
          + exact Hpaid.
        - (* THE MMIO WRITE NODE: the PLIC invariant is opened HERE *)
          iIntros (sigma) "Hsi".
          iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
          iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
          iInv "Hpinv" as ">Hdbody" "Hdclose".
          iDestruct "Hdbody" as (pl) "(Hplf & %Hpok)".
          iDestruct (plic_agree with "Hpldev Hplf") as %Hpeq.
          destruct (Hwrite pl Hpok) as (pl' & Hpw & Hpok').
          iMod (dev_interp_update_plic sigma.(mdev) pl pl'
                  with "[$Hua $Hpldev $Hvdev] Hplf") as "[Hdev' Hp']".
          iMod ("Hdclose" with "[Hp']") as "_".
          { iNext. iExists pl'. iFrame "Hp'". iPureIntro. exact Hpok'. }
          iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
          iModIntro. iExists (set_dplic sigma.(mdev) pl').
          iSplitR.
          { iPureIntro. rewrite Hpaid.
            apply (dev_write_plic sigma.(mdev) ea storeword pl' Hrange).
            rewrite <- Hpeq. exact Hpw. }
          iNext. iMod "Hb2" as "_". iModIntro.
          iFrame "Hreg Hmem Hdev'". }
    (* ---- the post ---- *)
    iIntros (e) "(-> & Hfile & Hland)".
    iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & _ & Hfrag)".
    iSplitR; [done|].
    iAssert (∃ tv2 : type_of_register tlb,
               hreg_frame (CID := CID)
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) SD ∗
               hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
               strans_res_at (CID := CID) satp0 tv2)%I
      with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
    { destruct Hshape as [-> | (tvx & ->)].
      - iExists tlbv. iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
               sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
      - iExists tvx.
        iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hrw") as "Hrw".
        iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hro") as "Hro".
        iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (register_set tlb tvx
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
               register_lookup_set) in "HRes".
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite sda_rs_satp. iExact "HRes". }
    (* the slot re-seals itself, at the landing tlb value *)
    iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes") as
      "(Htr & Hms & Hpriv & Hmenv)".
    iExists (add_vec_int pc (if is_rvc then 2 else 4)), mst0, m, n.
    iFrame "HPC HnPC".
    iSplitL "Hfrag"; [ iApply (resv_any_intro _ None with "Hfrag") | ].
    iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
    { rewrite /sconf_at_priv. iExists mdv0.
      iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      iPureIntro. split; assumption. }
    iSplitL "Htr Hstk Harm".
    { rewrite /sie_cap. iFrame "Hstk Htr Harm Hwit". }
    iFrame "Hfile". iPureIntro. split_and!; reflexivity.
  - (* ---------------- THE CONTINUATION ---------------- *)
    iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & ->)".
    iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
    iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
Qed.

(* The bundle-taking RESTATEMENT of the leaf above, for the consumers written
   before the device invariant was split per device ([plicinithart],
   [plic_complete]): statement verbatim, proof one projection. *)
Lemma wp_sw_plic_dev_s_sconf (γd : uart_names) (γv : disk_names) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) :
  let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 4 8) 1) 0) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  (forall p, plic_ok p ->
     exists p', plic_write p (uint a8 - plic_base)%Z storeword = Some p' /\ plic_ok p') ->
  sie_cap_gpr kt m n false p -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  dev_inv γd γv -∗
  wp_next false p (fun (CID : CpuId) =>
    sie_cap_gpr kt m n false p -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn Hwrite.
  (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
     and this leaf's wiring check.  See the family note at the head of this
     section. *)
  assert (Hea_all : forall hh : CpuId,
            add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
    by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
  assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
    by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iDestruct (dev_inv_plic with "Hdinv") as "#Hpinv".
  iApply (wp_sw_plic_pinv_s_sconf pc is_rvc rs2 rs1 imm m n
            Hrange Halign Hcanon Hdevvpn Hwrite
            with "Hcg Hpc Hinstr Hpinv Hcont").
Qed.

(* The width-4 PLIC MMIO LOAD, dual to [wp_sw_plic_dev_s_sconf].  A PLIC read
   can MUTATE the device (a claim takes a source: it clears that source's
   pending bit and marks it claimed), so it too runs with [dev_inv] open across
   the step.  The caller's obligation is again universal over every state the
   kernel's plan admits, and in exchange it may name a property [P] of the value
   read that holds at all of them -- that is how [plic_claim] learns its result
   is one of the machine's own interrupt ids. *)
Lemma wp_lw_plic_dev_s_sconf (γd : uart_names) (γv : disk_names) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1}
    (imm : mword 12) (m : regfile) (n : nat) (P : bv 32 -> Prop) :
  let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  (* the vmem level hands back the value itself now, not the split accumulator *)
  let ldval := fun (v : mword (8*4)) => (extend_value is_unsigned v : mword 64) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  uint rd <> 0 ->
  rd_ok rd ->
  (forall p, plic_ok p ->
     exists v p', plic_read p (uint a8 - plic_base)%Z = Some (v, p') /\ plic_ok p' /\ P v) ->
  sie_cap_gpr kt m n false p -∗
  pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) -∗
  dev_inv γd γv -∗
  ( ∀ v : bv 32,
    ⌜ P v ⌝ -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ldval v)]> m) n false p -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      WP (Loop : expr riscv_lang))) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros ea a8 ldval Hrange Halign Hcanon Hdevvpn Hrd Hrdok Hread.
  (* the class, consumed at [rs1] -- the one line the funnel change needs,
     and this leaf's wiring check.  See the family note at the head of this
     section. *)
  assert (Hea_all : forall hh : CpuId,
            add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
    by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
  pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
  pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
  (* [a8] IS [ea] -- see the store leaf above. *)
  assert (Ha8ea : a8 = ea)
    by (unfold a8; rewrite subrange_id sign_extend'_id; reflexivity).
  rewrite Ha8ea in Hrange, Halign, Hcanon, Hdevvpn, Hread.
  assert (Hdevstatic : kmap_static (svpn_of ea) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  pose proof (static_canon_lo ea KP_rw Hdevstatic Hcanon) as Healt.
  pose proof (pa_of_id ea Healt) as Hpaid.
  assert (Hdcls : dev_cls 4 (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)).
  { rewrite Hpaid. split; [ exact (dev_addr_plic ea Hrange) | ].
    split; [ exact (plic_pa_not_in_clint ea Hrange) | ].
    exact (pma_access_io ea 4 plic_base (plic_base + plic_size)
             (proj1 Hrange) (proj2 Hrange) eq_refl eq_refl
             (pma_width_ok 4 eq_refl eq_refl)). }
  assert (Hpalign : is_aligned_paddr
            (Physaddr (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)) 4 = true)
    by (rewrite Hpaid; exact Halign).
  assert (Hsp : m !!! Regidx csp_rs1
                = <[Regidx rd := regval_into_reg (zero_reg : mword 64)]> m
                    !!! Regidx csp_rs1)
    by (symmetry; apply upd_ne; congruence).
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iDestruct (dev_inv_plic with "Hdinv") as "#Hpinv".
  iApply (wp_instr_s_sconf m n false false pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
            (fun (_CIDx : CpuId) npc _ms' m' n' =>
               (∃ v : bv 32,
                  ⌜npc = add_vec_int pc (if is_rvc then 2 else 4)⌝ ∗
                  ⌜m' = <[Regidx rd := regval_into_reg (ldval v)]> m⌝ ∗
                  ⌜n' = n⌝ ∗ ⌜P v⌝)%I)
            with "Hcg Hpc Hinstr [Hcont]").
  iNext.
  rename CID into CID0.
  iIntros (CID Hs). rewrite /sconf_step_obl. iSplitR "Hcont".
  - (* ---------------- THE INSTRUCTION ---------------- *)
    iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
    assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
      by exact (src_ok_rget_indep m rs1 CID CID0).
    iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
      "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
        Hmdl & Hmenv)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                        HMPP & HTVM).
    (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
       [WpIntrInv.sda_slot_acc] below, the one place the two translation
       arms are told apart. *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
        %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
        %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    iDestruct "Hkmapb" as "[#Hkms _]".
    iDestruct (kmap_static_claims_at (svpn_of ea) KP_rw Hdevstatic
                 with "Hkms") as "#Hclaim".
    (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
           [sda_Drw] under the kernel table, the EMPTY set under Bare. ---- *)
    iDestruct (sda_slot_acc (CID := CID) kt (DfracOwn 1) mst0 MENVCFG_S
                 pmar0 eq_refl HSXL HMPRV (pma_all_ram Hpma_all)
                 with "Htr Hms Hpriv Hmenv Hpma Hhtif Hmisa")
      as (SD satp0 tlbv pcfg paddr)
      "(%Hdisj & %Hsub & %Hsok & %Hpok & Htrobl & Hrw & Hro & HRes & Hclose)".
    destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
    iAssert (sr_swp_res (strans_regime (CID := CID))
               (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
      with "[HRes]" as "HRes".
    { rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)).
      rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
    iDestruct "Hresv" as (rr) "Hfrag".
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 4).
    assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                    (sign_extend' 64 imm) = ea)
      by (rewrite Lpin_rs1; reflexivity).
    pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
    pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
    pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
    assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
            = true) by (rewrite Lmst; exact HMXR).
    assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
            = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
    assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
            by (rewrite Lmst; exact HSXL).
    assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
              (register_lookup satp
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
            = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
            by (rewrite Lsatp;
                exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
    assert (Lep : effectivePrivilege (Load Data) (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
            = returnM Supervisor)
            by (rewrite Lmst;
                exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
    assert (Lva : is_aligned_vaddr (Virtaddr (add_vec
              (tp_pin (CID := CID) m !!! Regidx rs1) (sign_extend' 64 imm))) 4
            = true) by (rewrite Hea; exact Halign).
    iApply (swp_mono (CID := CID)
              with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
    2:{ iApply (swp_execute_LOAD_dev_S4_ex (CID := CID)
                  SD sda_Dro (sda_Df (DfracOwn 1))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                  imm rs1 rd is_unsigned (tp_pin (CID := CID) m)
                  (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)
                  pmar0 pcfg paddr
                  (fun v => ⌜P v⌝)%I
                  (Mobl_dev4_ex (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)
                     (fun v => ⌜P v⌝)%I)
                  (sr_swp_res (strans_regime (CID := CID))) rr
                  (sr_swp_mode (strans_regime (CID := CID)) satp0)
                  Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                  (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                  (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                  (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                  (sda_rs_paddr _ _ _ _ _ _ _)
                  Lmxr Lpmm Lsxl
                  (hval_transform_effective_address_S_mode
                     (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                        (sign_extend' 64 imm))
                     (Load Data)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                     (sda_rs_priv _ _ _ _ _ _ _)
                     Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                  (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                  Lep
                  HA Hord HR Hcov (pma_all_io Hpma_all) Hdcls
                  Lva Hpalign Hrd
                  (swp_dev_read_node4_ex (CID := CID)
                     (pa_of (kpt_leaf_ppn (svpn_of ea)) ea) (fun v => ⌜P v⌝)%I
                     (proj1 Hdcls))
                  with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [Hpinv]").
        - (* the data translation, at the DEVICE page's static claim *)
          iIntros "Hfrag HRes Hrw Hro".
          rewrite Hea.
          iApply ("Htrobl" $! KT0 (Load Data) KP_rw
                    ea (kpt_leaf_ppn (svpn_of ea)) rr
                    with "[%] [%] [%] [%] [%] Hwit Hclaim Hcert
                    Hfrag HRes Hrw Hro").
          + apply _.
          + exact (or_intror (or_introl eq_refl)).
          + exact I.
          + exact Healt.
          + exact Hpaid.
        - (* THE MMIO READ NODE: the PLIC invariant is opened HERE, and the
             value read is the DEVICE's -- which is why the engine had to go
             existential (HartSMem's [_ex] chain). *)
          rewrite /Mobl_dev4_ex. iIntros (sigma) "Hsi".
          iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
          iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
          iInv "Hpinv" as ">Hdbody" "Hdclose".
          iDestruct "Hdbody" as (pl) "(Hplf & %Hpok)".
          iDestruct (plic_agree with "Hpldev Hplf") as %Hpeq.
          destruct (Hread pl Hpok) as (v & pl' & Hpr & Hpok' & HPv).
          iMod (dev_interp_update_plic sigma.(mdev) pl pl'
                  with "[$Hua $Hpldev $Hvdev] Hplf") as "[Hdev' Hp']".
          iMod ("Hdclose" with "[Hp']") as "_".
          { iNext. iExists pl'. iFrame "Hp'". iPureIntro. exact Hpok'. }
          iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
          iModIntro. iExists v, (set_dplic sigma.(mdev) pl').
          iSplitR.
          { iPureIntro. rewrite Hpaid.
            apply (dev_read_plic sigma.(mdev) ea v pl' Hrange).
            rewrite <- Hpeq. exact Hpr. }
          iNext. iMod "Hb2" as "_". iModIntro.
          iFrame "Hreg Hmem Hdev'". iPureIntro. exact HPv. }
    (* ---- the post ---- *)
    iIntros (e) "(-> & Hpost)".
    iDestruct "Hpost" as (v) "(Hfile & Hland)".
    iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & %HPv)".
    iSplitR; [done|].
    iAssert (∃ tv2 : type_of_register tlb,
               hreg_frame (CID := CID)
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) SD ∗
               hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
               strans_res_at (CID := CID) satp0 tv2)%I
      with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
    { destruct Hshape as [-> | (tvx & ->)].
      - iExists tlbv. iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
               sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
      - iExists tvx.
        iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hrw") as "Hrw".
        iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hro") as "Hro".
        iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (register_set tlb tvx
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
               register_lookup_set) in "HRes".
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite sda_rs_satp. iExact "HRes". }
    (* the slot re-seals itself, at the landing tlb value *)
    iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes") as
      "(Htr & Hms & Hpriv & Hmenv)".
    iExists (add_vec_int pc (if is_rvc then 2 else 4)), mst0,
            (<[Regidx rd := regval_into_reg (ldval v)]> m), n.
    iFrame "HPC HnPC Hany".
    iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
    { rewrite /sconf_at_priv. iExists mdv0.
      iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      iPureIntro. split; assumption. }
    assert (Hspv : m !!! Regidx csp_rs1
                   = <[Regidx rd := regval_into_reg (ldval v)]> m
                       !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iSplitL "Htr Hstk Harm".
    { rewrite /sie_cap -Hspv. iFrame "Hstk Htr Harm Hwit". }
    iSplitL "Hfile".
    { iEval (rewrite (tp_pin_upd m rd (regval_into_reg (ldval v)) Hrdtp))
        in "Hfile". iExact "Hfile". }
    iExists v. iPureIntro. split_and!; try reflexivity. exact HPv.
  - (* ---------------- THE CONTINUATION ---------------- *)
    iIntros (npc ms' m' n') "Hcg' Hpc' Hpay".
    iDestruct "Hpay" as (v) "(-> & -> & -> & %HPv)".
    iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
    iDestruct ("Hcont" $! v with "[%]") as "Hcont2"; [ exact HPv | ].
    iApply ("Hcont2" $! CID with "[%] Hcg' Hpc'"). exact Hs.
Qed.

(* ------------------------------------------------------------------- *)
(* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block.  x15/x14 (a5/a4) *)
(* are the registers plicinit / plic_claim hold the PLIC base in.         *)
(* ------------------------------------------------------------------- *)
Definition plic_srcok_pos_a5 : SrcOk (mword_of_int 15 : mword 5) := _.
Definition plic_srcok_pos_a4 : SrcOk (mword_of_int 14 : mword 5) := _.
Fail Definition plic_srcok_neg : SrcOk Rtp := _.

End WpPlic.
