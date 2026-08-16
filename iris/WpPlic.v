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
Require Import PlicPlan DiskPtsto WpUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpPlicExec.
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
Context `{!riscvGS Σ, !sieG Σ}.
Context `{!uartGhostG Σ, !diskGhostG Σ}.
Context `{GEN : GenId} `{CID : CpuId}.
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
  sie_cap_gpr m n false p -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  plic_inv -∗
  wp_next false p (fun (CID : CpuId) =>
    sie_cap_gpr m n false p -∗
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
  iIntros "Hcg Hpc Hinstr #Hpinv Hcont".
  iApply (wp_instr_s_sconf m n false pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            with "Hcg Hpc Hinstr").
  (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic
     obligation is discharged by [wp_next]'s OWN introduction rule at the
     ambient hart -- the same [wp_next_off_intro] every b = false leaf
     already uses for its own conclusion.  Nothing is renamed and nothing
     is substituted: the body below is the pre-move proof VERBATIM. *)
  iApply wp_next_off_intro.
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & Hspp & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (pma_all_io Hpma_all a8 4
             (pma_access_io _ _ plic_base (plic_base + plic_size) (proj1 Hrange) (proj2 Hrange)
                eq_refl eq_refl (pma_width_ok 4 eq_refl eq_refl))) as (region_st & Hmatch_st & _ & Hwrite_st).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
  (* only the PLIC half of the fabric is touched *)
  iInv "Hpinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (pl) "(Hplf & %Hpok)".
  iDestruct (plic_agree with "Hpldev Hplf") as %Hpeq.
  destruct (Hwrite pl Hpok) as (pl' & Hpw & Hpok').
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hr2c") as %Lv2.
  iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform strans_regime (Store Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
  unshelve iMod (sr_absorb strans_regime (Store Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc _
          (or_intror (or_intror (or_introl eq_refl))) eq_refl Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' (pa_of_id a8 Ha8lt) _ with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hwr_plic : dev_write s_tr.(mdev) a8 4 storeword = Some (set_dplic σ.(mdev) pl')).
  { rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
    apply (dev_write_plic σ.(mdev) a8 storeword pl' Hrange).
    rewrite <- Hpeq. exact Hpw. }
  pose (d' := set_dplic σ.(mdev) pl').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_4_gpr_S_walk_dev rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(rewrite !Lva; exact Halign)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply plic_pmp_match4; [exact Hrange | exact Hcov1])
               HW1
               ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_st)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
               Hwrite_st
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_plic; [exact Hrange | lia])
               ltac:(apply within_sig_plic)
               ltac:(apply within_htif_writable_false; exact Lhtif_tr)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_plic; exact Hrange)
               ltac:(rewrite !Lva !Lv2; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id;
                     change (8 * (0 + 1) * 4 - 1)%Z with 31%Z; change (8 * 0 * 4)%Z with 0%Z;
                     rewrite wv32_collapse; exact Hwr_plic)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_plic σ.(mdev) pl pl' with "[$Hua $Hpldev $Hvdev] Hplf") as "[Hdev' Hp']".
  iMod ("Hdclose" with "[Hp']") as "_".
  { iNext. iExists pl'. iFrame "Hp'". iPureIntro. exact Hpok'. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hstore. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; cbn [sregs].
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  iAssert (sconf) with "[Hpriv Hmiex Hms Hhalf Hspp Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf Hspp".
    { iExists mstatus0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap m n false p) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr Hwit". }
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
     obligation is discharged by instantiating it here. *)
  iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
  iPureIntro. done.
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
  sie_cap_gpr m n false p -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  dev_inv γd γv -∗
  wp_next false p (fun (CID : CpuId) =>
    sie_cap_gpr m n false p -∗
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
  sie_cap_gpr m n false p -∗
  pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) -∗
  dev_inv γd γv -∗
  ( ∀ v : bv 32,
    ⌜ P v ⌝ -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (ldval v)]> m) n false p -∗
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
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iApply (wp_instr_s_sconf m n false pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
            with "Hcg Hpc Hinstr").
  (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic
     obligation is discharged by [wp_next]'s OWN introduction rule at the
     ambient hart -- the same [wp_next_off_intro] every b = false leaf
     already uses for its own conclusion.  Nothing is renamed and nothing
     is substituted: the body below is the pre-move proof VERBATIM. *)
  iApply wp_next_off_intro.
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & Hspp & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (pma_all_io Hpma_all a8 4
             (pma_access_io _ _ plic_base (plic_base + plic_size) (proj1 Hrange) (proj2 Hrange)
                eq_refl eq_refl (pma_width_ok 4 eq_refl eq_refl))) as (region_ld & Hmatch_ld & Hread_ld & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
  (* only the PLIC half of the fabric is touched, and [↑plicN ⊆ ↑devN] *)
  iDestruct (dev_inv_plic with "Hdinv") as "#Hpinv".
  iInv "Hpinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (pl) "(Hplf & %Hpok)".
  iDestruct (plic_agree with "Hpldev Hplf") as %Hpeq.
  destruct (Hread pl Hpok) as (v & pl' & Hrd_p & Hpok' & HPv).
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform strans_regime (Load Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
  unshelve iMod (sr_absorb strans_regime (Load Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc _
          (or_intror (or_introl eq_refl)) I Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_load s_pc)
          Lpma_pc' (pa_of_id a8 Ha8lt) _ with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hdrd_plic : dev_read s_tr.(mdev) a8 4 = Some (v, set_dplic σ.(mdev) pl')).
  { rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
    apply (dev_read_plic σ.(mdev) a8 v pl' Hrange).
    rewrite <- Hpeq. exact Hrd_p. }
  pose (d' := set_dplic σ.(mdev) pl').
  pose (s_x := set_reg (MState s_tr.(sregs) s_tr.(mem) d')
                 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (ldval v))).
  assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s_pc
                  = Some (RETIRE_SUCCESS, s_x)).
  { subst s_x. unfold ldval.
    apply (exec_execute_LOAD_4_gpr_S_walk_dev rs1 rd imm is_unsigned v d' region_ld s_pc s_tr
             Hrd Htea
             ltac:(rewrite !Lva; exact Halign)
             md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
             Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
             HA1 Hord1
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply plic_pmp_match4; [exact Hrange | exact Hcov1])
             HR1
             ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_ld)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
             Hread_ld
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_plic; [exact Hrange | lia])
             ltac:(apply within_sig_plic)
             ltac:(apply within_htif_false; exact Lhtif_tr)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_plic; exact Hrange)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hdrd_plic)). }
  iMod (dev_interp_update_plic σ.(mdev) pl pl' with "[$Hua $Hpldev $Hvdev] Hplf") as "[Hdev' Hp']".
  iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (ldval v)) with "Hfmap") as "[Hrdc Hfins]".
  rewrite (gpr_pt_nz rd _ Hrd).
  iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (ldval v)) with "Hreg Hrdc") as "[Hreg Hrdc]".
  iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
  { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
  iMod ("Hdclose" with "[Hp']") as "_".
  { iNext. iExists pl'. iFrame "Hp'". iPureIntro. exact Hpok'. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hload. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; rewrite ?sregs_set_reg. tmig.
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  assert (Hsp : m !!! Regidx csp_rs1
                = <[Regidx rd := regval_into_reg (ldval v)]> m !!! Regidx csp_rs1)
    by (symmetry; apply upd_ne; congruence).
  iAssert (sconf) with "[Hpriv Hmiex Hms Hhalf Hspp Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf Hspp".
    { iExists mstatus0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap m n false p) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr Hwit". }
  (* the leaf's own write commutes with the tp pin *)
  tp_refold Hrdtp "Hfmap".
  iDestruct (sie_cap_retarget m
               (<[Regidx rd := regval_into_reg (ldval v)]> m) n false Hsp with "Hcap") as "Hcap".
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iSpecialize ("Hcont" $! v with "[%]"); [ exact HPv |].
  (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
     obligation is discharged by instantiating it here. *)
  iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc]").
  iPureIntro. done.
Qed.

(* ------------------------------------------------------------------- *)
(* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block.  x15/x14 (a5/a4) *)
(* are the registers plicinit / plic_claim hold the PLIC base in.         *)
(* ------------------------------------------------------------------- *)
Definition plic_srcok_pos_a5 : SrcOk (mword_of_int 15 : mword 5) := _.
Definition plic_srcok_pos_a4 : SrcOk (mword_of_int 14 : mword 5) := _.
Fail Definition plic_srcok_neg : SrcOk Rtp := _.

End WpPlic.
