(* M-mode Store leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
Require Import RegFile.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr InstrBytes RiscvModelBytes RiscvTryStep RiscvExtras SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartMPmp
        HartMFrame HartMStore.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Import Defs.
Import Defs.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* THE STORE LEAF'S OWN REGISTER FRAME.                                    *)
(*                                                                        *)
(* [WpInstr.wp_instr_w]'s obligation hands a leaf [gpr_file], PC, nextPC   *)
(* and the reservation and nothing else, so the SIX config cells the       *)
(* width-8 store engine reads have to be assembled here, out of the HALF   *)
(* of [mmode_config] the leaf keeps back plus [hw_config]'s persistent     *)
(* pins.  [execute_STORE] writes no register, so the writable frame is     *)
(* EMPTY -- the whole footprint is read-only.                              *)
(* ====================================================================== *)
Definition st_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register); (mseccfg : register);
     (pmpcfg_n : register); (pma_regions : register);
     (htif_tohost_base : register) ]}.

(* the TOR variants read pmpaddr_n as well; the witness state carries the
   cell either way and only the read SET differs. *)
Definition st_Dro_tor : gset register := {[ (pmpaddr_n : register) ]} ∪ st_Dro.

(* the witness state carries a pmpaddr_n slot even when the read set does not
   contain it, so a non-TOR leaf needs SOME value there; nothing reads it. *)
Definition st_paddr0 : type_of_register pmpaddr_n :=
  register_lookup pmpaddr_n init_regstate.

Definition st_rs (ms0 sec0 : mword 64) (pcfg : type_of_register pmpcfg_n)
    (paddrs : type_of_register pmpaddr_n)
    (pmar0 : list PMA_Region) : regstate :=
  register_set mstatus ms0
    (register_set mseccfg sec0
       (register_set pmpcfg_n pcfg
          (register_set pmpaddr_n paddrs
             (register_set pma_regions pmar0
                (register_set htif_tohost_base None
                   (register_set cur_privilege Machine init_regstate)))))).

Local Ltac st_lk :=
  rewrite /st_rs;
  repeat (etransitivity;
          [ apply irrelevant_register_set; vm_compute; reflexivity | ]);
  apply register_lookup_set.

Lemma st_rs_mst ms0 sec0 pcfg paddrs pmar0 :
  register_lookup mstatus (st_rs ms0 sec0 pcfg paddrs pmar0) = ms0.
Proof. st_lk. Qed.
Lemma st_rs_sec ms0 sec0 pcfg paddrs pmar0 :
  register_lookup mseccfg (st_rs ms0 sec0 pcfg paddrs pmar0) = sec0.
Proof. st_lk. Qed.
Lemma st_rs_pcfg ms0 sec0 pcfg paddrs pmar0 :
  register_lookup pmpcfg_n (st_rs ms0 sec0 pcfg paddrs pmar0) = pcfg.
Proof. st_lk. Qed.
Lemma st_rs_paddr ms0 sec0 pcfg paddrs pmar0 :
  register_lookup pmpaddr_n (st_rs ms0 sec0 pcfg paddrs pmar0) = paddrs.
Proof. st_lk. Qed.
Lemma st_rs_pma ms0 sec0 pcfg paddrs pmar0 :
  register_lookup pma_regions (st_rs ms0 sec0 pcfg paddrs pmar0) = pmar0.
Proof. st_lk. Qed.
Lemma st_rs_htif ms0 sec0 pcfg paddrs pmar0 :
  register_lookup htif_tohost_base (st_rs ms0 sec0 pcfg paddrs pmar0) = None.
Proof. st_lk. Qed.
Lemma st_rs_priv ms0 sec0 pcfg paddrs pmar0 :
  register_lookup cur_privilege (st_rs ms0 sec0 pcfg paddrs pmar0) = Machine.
Proof. st_lk. Qed.

Definition st_Df (dq : dfrac) : register -> dfrac := fun r =>
  if decide (r = (mseccfg : register)) then DfracDiscarded
  else if decide (r = (pma_regions : register)) then DfracDiscarded
  else if decide (r = (htif_tohost_base : register)) then DfracDiscarded
  else dq.

Local Ltac stdf :=
  rewrite /st_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.

Lemma st_Df_priv dq : st_Df dq cur_privilege = dq.
Proof. stdf. Qed.
Lemma st_Df_mst dq : st_Df dq mstatus = dq.
Proof. stdf. Qed.
Lemma st_Df_pcfg dq : st_Df dq pmpcfg_n = dq.
Proof. stdf. Qed.
Lemma st_Df_paddr dq : st_Df dq pmpaddr_n = dq.
Proof. stdf. Qed.
Lemma st_Df_sec dq : st_Df dq mseccfg = DfracDiscarded.
Proof. stdf. Qed.
Lemma st_Df_pma dq : st_Df dq pma_regions = DfracDiscarded.
Proof. stdf. Qed.
Lemma st_Df_htif dq : st_Df dq htif_tohost_base = DfracDiscarded.
Proof. stdf. Qed.

Lemma st_disj : (∅ : gset register) ## st_Dro.
Proof. set_solver. Qed.
Lemma st_in_priv : (cur_privilege : register) ∈ (∅ : gset register) ∪ st_Dro.
Proof. rewrite /st_Dro. set_solver. Qed.
Lemma st_in_mst : (mstatus : register) ∈ (∅ : gset register) ∪ st_Dro.
Proof. rewrite /st_Dro. set_solver. Qed.
Lemma st_in_sec : (mseccfg : register) ∈ (∅ : gset register) ∪ st_Dro.
Proof. rewrite /st_Dro. set_solver. Qed.
Lemma st_in_pcfg : (pmpcfg_n : register) ∈ (∅ : gset register) ∪ st_Dro.
Proof. rewrite /st_Dro. set_solver. Qed.
Lemma st_in_pma : (pma_regions : register) ∈ (∅ : gset register) ∪ st_Dro.
Proof. rewrite /st_Dro. set_solver. Qed.
Lemma st_in_htif : (htif_tohost_base : register) ∈ (∅ : gset register) ∪ st_Dro.
Proof. rewrite /st_Dro. set_solver. Qed.

Lemma stt_disj : (∅ : gset register) ## st_Dro_tor.
Proof. set_solver. Qed.
Lemma stt_in_priv : (cur_privilege : register) ∈ (∅ : gset register) ∪ st_Dro_tor.
Proof. rewrite /st_Dro_tor /st_Dro. set_solver. Qed.
Lemma stt_in_mst : (mstatus : register) ∈ (∅ : gset register) ∪ st_Dro_tor.
Proof. rewrite /st_Dro_tor /st_Dro. set_solver. Qed.
Lemma stt_in_sec : (mseccfg : register) ∈ (∅ : gset register) ∪ st_Dro_tor.
Proof. rewrite /st_Dro_tor /st_Dro. set_solver. Qed.
Lemma stt_in_pcfg : (pmpcfg_n : register) ∈ (∅ : gset register) ∪ st_Dro_tor.
Proof. rewrite /st_Dro_tor /st_Dro. set_solver. Qed.
Lemma stt_in_paddr : (pmpaddr_n : register) ∈ (∅ : gset register) ∪ st_Dro_tor.
Proof. rewrite /st_Dro_tor. set_solver. Qed.
Lemma stt_in_pma : (pma_regions : register) ∈ (∅ : gset register) ∪ st_Dro_tor.
Proof. rewrite /st_Dro_tor /st_Dro. set_solver. Qed.
Lemma stt_in_htif : (htif_tohost_base : register) ∈ (∅ : gset register) ∪ st_Dro_tor.
Proof. rewrite /st_Dro_tor /st_Dro. set_solver. Qed.

(* ---------------------------------------------------------------------- *)
(* THE PMP CHECK, AS THE PURE FACT THE WIDTH-8 CHAIN TAKES.                 *)
(*                                                                        *)
(* [HartMStore]'s width-8 chain abstracts its PMP obligation to one [hval] *)
(* over [pmpCheck], so the all-OFF and the TOR-configured leaves differ    *)
(* only in WHICH of these two they hand it.                                *)
(* ---------------------------------------------------------------------- *)
Lemma st_hval_pmp_off (D Drw : gset register) (rs : regstate)
    (pcfg : type_of_register pmpcfg_n) (ea : mword 64) :
  (pmpcfg_n : register) ∈ D ->
  register_lookup pmpcfg_n rs = pcfg ->
  pmp_all_off pcfg ->
  hval D Drw rs (pmpCheck (Physaddr ea) 8 (Store Data) Machine) None rs.
Proof.
  intros HD Hc Hoff.
  exact (mpmp_hval_off D Drw pcfg ea rs 8 (Store Data)
           ltac:(intros ent; eexists; reflexivity) HD Hoff Hc).
Qed.

(* the two Z facts, in an EMPTY context: [lia] cannot relate the goal's and
   [pmp_tor0_grants]'s spellings of [vec_access_dec] (they differ in the
   [Inhabited] instance, convertible but not syntactically equal, and lia
   atomises syntactically), so the arithmetic is proved once here and
   [exact]ed -- which does look through the conversion. *)
Local Lemma tor0_pos (x y : Z) : 0 <= x -> x + 8 <= y * 4 -> 0 < y.
Proof. lia. Qed.
Local Lemma tor0_lo (x : Z) : 0 <= x -> 0 * 4 <= x.
Proof. lia. Qed.
Local Lemma tor0_w : 0 < 8.
Proof. lia. Qed.

Lemma st_hval_pmp_tor0 (D Drw : gset register) (rs : regstate)
    (pcfg : type_of_register pmpcfg_n) (paddrs : type_of_register pmpaddr_n)
    (ea : mword 64) :
  (pmpcfg_n : register) ∈ D ->
  (pmpaddr_n : register) ∈ D ->
  register_lookup pmpcfg_n rs = pcfg ->
  register_lookup pmpaddr_n rs = paddrs ->
  pmp_tor0_grants pcfg paddrs ea 8 ->
  hval D Drw rs (pmpCheck (Physaddr ea) 8 (Store Data) Machine) None rs.
Proof.
  intros HDc HDa Hc Ha (HA & HL & Hw & Hin).
  pose proof (bv_unsigned_in_range _ ea) as [Hea0 _].
  rewrite <- uint_unsigned in Hea0.
  assert (Hz0 : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  assert (Hw8 : uint (to_bits 64 8 : mword 64) = 8) by (vm_compute; reflexivity).
  apply (mpmp_hval_tor0 D Drw pcfg paddrs ea rs 8 (Store Data)
           ltac:(intros ent; eexists; reflexivity) HDc HDa Hc Ha HA HL).
  - unfold zopz0zKzJ_u. rewrite Hz0. rewrite Z.geb_leb. apply Z.leb_gt.
    exact (tor0_pos (uint ea) _ Hea0 Hin).
  - rewrite Hz0 Hw8.
    exact (pmpRangeMatch_full (0 * 4) _ (uint ea) 8
             (tor0_lo _ Hea0) tor0_w Hin).
Qed.

Section StoreFrame.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma st_frame_empty (rs : regstate) : ⊢ (hreg_frame rs ∅ : iProp Σ).
  Proof. rewrite /hreg_frame big_sepS_empty. auto. Qed.

  Lemma st_frames (dq : dfrac) (ms0 sec0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddrs : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) :
    (hreg_frame_ro (st_Df dq) (st_rs ms0 sec0 pcfg paddrs pmar0) st_Dro
       : iProp Σ)
    ⊣⊢ (reg_pointsto cur_privilege dq Machine ∗
        reg_pointsto mstatus dq ms0 ∗
        reg_pointsto mseccfg DfracDiscarded sec0 ∗
        reg_pointsto pmpcfg_n dq pcfg ∗
        reg_pointsto pma_regions DfracDiscarded pmar0 ∗
        reg_pointsto htif_tohost_base DfracDiscarded None).
  Proof.
    rewrite /hreg_frame_ro /st_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite st_rs_priv st_rs_mst st_rs_sec st_rs_pcfg st_rs_pma st_rs_htif.
    rewrite st_Df_priv st_Df_mst st_Df_sec st_Df_pcfg st_Df_pma st_Df_htif.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma st_frames_tor (dq : dfrac) (ms0 sec0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddrs : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) :
    (hreg_frame_ro (st_Df dq) (st_rs ms0 sec0 pcfg paddrs pmar0) st_Dro_tor
       : iProp Σ)
    ⊣⊢ (reg_pointsto pmpaddr_n dq paddrs ∗
        reg_pointsto cur_privilege dq Machine ∗
        reg_pointsto mstatus dq ms0 ∗
        reg_pointsto mseccfg DfracDiscarded sec0 ∗
        reg_pointsto pmpcfg_n dq pcfg ∗
        reg_pointsto pma_regions DfracDiscarded pmar0 ∗
        reg_pointsto htif_tohost_base DfracDiscarded None).
  Proof.
    rewrite /hreg_frame_ro /st_Dro_tor.
    rewrite big_sepS_union; last (rewrite /st_Dro; set_solver).
    rewrite big_sepS_singleton st_rs_paddr st_Df_paddr.
    rewrite -/(hreg_frame_ro (st_Df dq) (st_rs ms0 sec0 pcfg paddrs pmar0) st_Dro).
    rewrite (st_frames dq ms0 sec0 pcfg paddrs pmar0).
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma st_frames_in (dq : dfrac) (ms0 sec0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddrs : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) :
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mstatus dq ms0 -∗
    reg_pointsto mseccfg DfracDiscarded sec0 -∗
    reg_pointsto pmpcfg_n dq pcfg -∗
    reg_pointsto pma_regions DfracDiscarded pmar0 -∗
    reg_pointsto htif_tohost_base DfracDiscarded None -∗
    (hreg_frame (st_rs ms0 sec0 pcfg paddrs pmar0) ∅ ∗
     hreg_frame_ro (st_Df dq) (st_rs ms0 sec0 pcfg paddrs pmar0) st_Dro
       : iProp Σ).
  Proof.
    iIntros "H1 H2 H3 H4 H5 H6". iSplitR; [iApply st_frame_empty|].
    rewrite (st_frames dq ms0 sec0 pcfg paddrs pmar0). iFrame.
  Qed.

  Lemma st_frames_out (dq : dfrac) (ms0 sec0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddrs : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) :
    (hreg_frame_ro (st_Df dq) (st_rs ms0 sec0 pcfg paddrs pmar0) st_Dro
       : iProp Σ) -∗
    (reg_pointsto cur_privilege dq Machine ∗
     reg_pointsto mstatus dq ms0 ∗
     reg_pointsto mseccfg DfracDiscarded sec0 ∗
     reg_pointsto pmpcfg_n dq pcfg ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto htif_tohost_base DfracDiscarded None).
  Proof.
    rewrite (st_frames dq ms0 sec0 pcfg paddrs pmar0). iIntros "H". iExact "H".
  Qed.

  Lemma st_frames_tor_in (dq : dfrac) (ms0 sec0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddrs : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) :
    reg_pointsto pmpaddr_n dq paddrs -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mstatus dq ms0 -∗
    reg_pointsto mseccfg DfracDiscarded sec0 -∗
    reg_pointsto pmpcfg_n dq pcfg -∗
    reg_pointsto pma_regions DfracDiscarded pmar0 -∗
    reg_pointsto htif_tohost_base DfracDiscarded None -∗
    (hreg_frame (st_rs ms0 sec0 pcfg paddrs pmar0) ∅ ∗
     hreg_frame_ro (st_Df dq) (st_rs ms0 sec0 pcfg paddrs pmar0) st_Dro_tor
       : iProp Σ).
  Proof.
    iIntros "H0 H1 H2 H3 H4 H5 H6". iSplitR; [iApply st_frame_empty|].
    rewrite (st_frames_tor dq ms0 sec0 pcfg paddrs pmar0). iFrame.
  Qed.

  Lemma st_frames_tor_out (dq : dfrac) (ms0 sec0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddrs : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) :
    (hreg_frame_ro (st_Df dq) (st_rs ms0 sec0 pcfg paddrs pmar0) st_Dro_tor
       : iProp Σ) -∗
    (reg_pointsto pmpaddr_n dq paddrs ∗
     reg_pointsto cur_privilege dq Machine ∗
     reg_pointsto mstatus dq ms0 ∗
     reg_pointsto mseccfg DfracDiscarded sec0 ∗
     reg_pointsto pmpcfg_n dq pcfg ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto htif_tohost_base DfracDiscarded None).
  Proof.
    rewrite (st_frames_tor dq ms0 sec0 pcfg paddrs pmar0).
    iIntros "H". iExact "H".
  Qed.
End StoreFrame.


Local Ltac w_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not __id].

Local Ltac w_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Local Ltac w_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Lemma hfrun_tea_store (D Drw : gset register) (rs : regstate)
    (a : SailStdpp.Values.mword 64) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (mseccfg : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs)) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg rs)) = PMM_Disabled ->
  hfrun 12 D Drw rs
    (Defs.bind (transform_effective_address (Virtaddr a) (Store Data))
       (fun v => returnM (Ext_DataAddr_OK v : Ext_DataAddr_Check unit)))
  = Some ((Ext_DataAddr_OK (Virtaddr a) : Ext_DataAddr_Check unit), rs).
Proof.
  intros HDm HDp HDs Hpriv Hmprv Hpmm.
  unfold transform_effective_address. w_cbn.
  w_read. w_read. rewrite Hpriv.
  unfold effectivePrivilege.
  change (Instances.generic_neq (Store Data) (InstructionFetch tt)) with true.
  w_glue. rewrite Hmprv. w_glue.
  rewrite mbind_ret.
  unfold get_pmlen, is_pmm_applicable. w_cbn.
  change (Instances.generic_neq (Store Data) (InstructionFetch tt)) with true.
  change (Instances.generic_neq (Store Data) (Load PageTableEntry)) with true.
  change (Instances.generic_neq (Store Data) (Store PageTableEntry)) with true.
  change (Instances.generic_eq Machine Machine) with true.
  w_glue. w_cbn.
  change (xlen =? 64) with true. w_cbn.
  unfold get_pmm. w_cbn. w_read. rewrite Hpmm. w_cbn.
  unfold translationMode.
  change (Instances.generic_eq Machine Machine) with true. w_cbn.
  change (Instances.generic_eq Bare Bare) with true. w_cbn.
  cbn [pm_transform_PA].
  rewrite subrange_id zero_extend'_id.
  apply hfrun_ret.
Qed.

(* the byte string the model's request actually carries: the [autocast] of the
   full-width subrange and [sail_mem_write]'s own [cast_N] are both identities
   at width 8. *)
Lemma st_write_value (pa : SailStdpp.Values.mword 64)
    (d : SailStdpp.Values.mword 64) :
  Interface.WriteReq.value
    (mwrite_req8 pa
       (TypeCasts.autocast (@subrange_vec_dec 64 d (8 * 8 - 1) 0)))
  = d.
Proof.
  unfold mwrite_req8. cbn [Interface.WriteReq.value].
  rewrite autocast_subrange_id. apply TypeCasts.cast_N_refl.
Qed.

(* from WpGprStore.v *)
Section WpStoreGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic 8-byte STORE WP -- the
     write-dual of [wp_ld_gpr].  STORE reads TWO sources: rs1 (base address) and
     rs2 (data), each borrowed off [gpr_file] independently (so rs1 = rs2 is
     fine), and WRITES the 8 target bytes from their old contents [vold] to rs2's
     bytes.  The caller supplies the OLD (full-owned) target bytes and the store's
     alignment; the config the translation / PMP checks read is recovered from the
     KEPT half of [mmode_config] + [hw_config].  No register is written ([gpr_file]
     is handed back UNCHANGED). *)
  Lemma wp_store_gpr (pc : mword 64) (is_rvc : bool) (rs1 rs2 : mword 5)
      (imm : mword 12) (m : regfile) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    (* the 8-byte DATA access needs the stronger all-OFF form: an 8-byte
       window can partially overlap a TOR/NA4 boundary (partial match faults
       even in M-mode), so unlocked-ness alone does not suffice.  The fetch
       side uses [pmp_all_off_allows_all]. *)
    pmp_all_off pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦ₚ₈ vold -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      ea ↦ₚ₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros offset ea Hpmp Hstat.
    iIntros "Hmm Hpmpc Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_ea.
    iDestruct "Hbw" as "(%Halign & Hbytes)".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & #Hmseccfg & #Hpma & #Hhtif & _ & _ & _ & _ & _ & _ & %Hpma_all &
        %Hpmm & _ & _ & _ & _ & _ & _ & _)".
    iApply (wp_instr_w pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (STORE (imm, Regidx rs2, Regidx rs1, 8)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               ea ↦ₚ₈ (m !!! Regidx rs2))%I
              (pmp_all_off_allows_all _ Hpmp) Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfile Hinstr
                    [Hhs_k Hpriv_k Hms_k Hpmpc_k Hbytes] [Hcont]").
    2:{ iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hbw')".
        iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
        iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
        iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hbw'"). }
    iIntros "Hf HPC HnPC Hfrag".
    iDestruct (st_frames_in (DfracOwn (q/2)) ms0 mseccfg0 pmpcfg0 st_paddr0
                 pmar0 with "Hpriv_k Hms_k Hmseccfg Hpmpc_k Hpma Hhtif")
      as "[Hrw Hro]".
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
    unfold execute_STORE.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. w_glue.
    assert (Hva : is_aligned_vaddr (Virtaddr ea) 8 = true).
    { unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign. }
    iApply (swp_bind_use (rX_bits (Regidx rs2)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (w) "(-> & Hf)". w_glue.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗ gpr_file m ∗
                         hreg_frame
                           (st_rs ms0 mseccfg0 pmpcfg0 st_paddr0 pmar0) ∅ ∗
                         hreg_frame_ro (st_Df (DfracOwn (q/2)))
                           (st_rs ms0 mseccfg0 pmpcfg0 st_paddr0 pmar0)
                           st_Dro ∗
                         ([∗ list] j ∈ seq 0 8,
                            (pa_add ea j) ↦ₚ nth_byte (m !!! Regidx rs2) j) ∗
                         resv_frag cpu_id None)%I) _
              with "[Hf Hrw Hro Hbytes Hfrag] [-]").
    { iApply (swp_vmem_write_gen8 ∅ st_Dro (st_Df (DfracOwn (q/2)))
                (st_rs ms0 mseccfg0 pmpcfg0 st_paddr0 pmar0) (Regidx rs1)
                (sign_extend' 64 imm) ea _ pmar0
                ([∗ list] j ∈ seq 0 8,
                   (pa_add ea j) ↦ₚ nth_byte (m !!! Regidx rs2) j)%I
                (gpr_file m) None
                st_disj st_in_mst st_in_priv st_in_pma st_in_htif
                (st_rs_priv _ _ _ _ _) (st_rs_pma _ _ _ _ _)
                (st_rs_htif _ _ _ _ _)
                ltac:(rewrite st_rs_mst; exact HMPRV)
                (st_hval_pmp_off (∅ ∪ st_Dro) ∅ _ pmpcfg0 ea st_in_pcfg
                   (st_rs_pcfg _ _ _ _ _) Hpmp)
                (pma_all_ram Hpma_all) Hram_ea Hva Halign
                with "Hcert Hfrag Hrw Hro Hf [] [Hbytes]").
      - (* the address stretch: rs1 out of [gpr_file], then a computed walk *)
        iIntros "HQ Hrw Hro".
        unfold get_transformed_data_addr.
        iApply (swp_bind_use
                  (ext_data_get_addr (Regidx rs1) (sign_extend' 64 imm)
                     (Store Data) 8) _
                  (fun r => (⌜r = (Ext_DataAddr_OK (Virtaddr ea)
                                   : Ext_DataAddr_Check unit)⌝ ∗
                             gpr_file m)%I) _
                  with "[HQ] [-]").
        { unfold ext_data_get_addr.
          iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[HQ] [-]").
          { iApply (swp_rX_file rs1 m with "Hcert HQ"). }
          iIntros (w1) "(-> & Hf1)". iApply swp_ret. by iFrame. }
        iIntros (r) "(-> & Hf1)". cbn match.
        iApply (swp_mono with "[Hf1] [-]");
          [| iApply (swp_hfrun 12 ∅ st_Dro (st_Df (DfracOwn (q/2)))
                       (st_rs ms0 mseccfg0 pmpcfg0 st_paddr0 pmar0) _ _ _
                       st_disj
                       (hfrun_tea_store (∅ ∪ st_Dro) ∅
                          (st_rs ms0 mseccfg0 pmpcfg0 st_paddr0 pmar0) ea
                          st_in_mst st_in_priv st_in_sec
                          (st_rs_priv _ _ _ _ _)
                          ltac:(rewrite st_rs_mst; exact HMPRV)
                          ltac:(rewrite st_rs_sec; exact Hpmm))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)". by iFrame.
      - (* the memory obligation: the eight target bytes change hands *)
        iIntros (sg) "Hsg". rewrite /mstate_interp.
        iDestruct "Hsg" as "(Hri & Hmem & Hdev)".
        iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
        iNext. iMod "Hmask" as "_".
        iMod (upd_window_8 sg.(mem) ea (m !!! Regidx rs2) vold
                with "Hmem Hbytes") as "[Hmem Hbytes]".
        iModIntro. rewrite st_write_value. by iFrame. }
    iIntros (v0) "(-> & Hf & Hrw & Hro & Hbytes & Hfrag)". w_glue.
    iApply swp_ret.
    iDestruct (st_frames_out (DfracOwn (q/2)) ms0 mseccfg0 pmpcfg0 st_paddr0
                 pmar0 with "Hro") as "(Hpriv_k & Hms_k & _ & Hpmpc_k & _ & _)".
    iSplitR; [done|]. iFrame "Hf HPC HnPC".
    iSplitL "Hfrag"; [iApply (resv_any_intro with "Hfrag")|].
    iSplitL "Hhs_k Hpriv_k Hms_k".
    { iFrame "Hhw Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro.
      exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iFrame "Hpmpc_k".
    rewrite /phys_word_pointsto. iFrame "Hbytes". iPureIntro. exact Halign.
  Qed.
End WpStoreGpr.

(* from WpGprRvcTor.v (RvcTorEngines, store leaves) *)
Section MmodeStoreTor.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_store_gpr_tor (pc : mword 64) (is_rvc : bool) (rs1 rs2 : mword 5)
      (imm : mword 12) (m : regfile) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦ₚ₈ vold -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      ea ↦ₚ₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros offset ea Hpmp Hstat Htor.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_ea.
    iDestruct "Hbw" as "(%Halign & Hbytes)".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hpaddr" as "[Hpaddr_f Hpaddr_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & #Hmseccfg & #Hpma & #Hhtif & _ & _ & _ & _ & _ & _ & %Hpma_all &
        %Hpmm & _ & _ & _ & _ & _ & _ & _)".
    iApply (wp_instr_w pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (STORE (imm, Regidx rs2, Regidx rs1, 8)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               pmpaddr_n ↦ᵣ{DfracOwn (q/2)} pmpaddrs ∗
               ea ↦ₚ₈ (m !!! Regidx rs2))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfile Hinstr
                    [Hhs_k Hpriv_k Hms_k Hpmpc_k Hpaddr_f Hbytes]
                    [Hcont Hpaddr_k]").
    2:{ iNext. iIntros "Hmm' Hpmpc' Hpc' Hf'
                        (Hmm_k' & Hpmpc_k' & Hpaddr_f' & Hbw')".
        iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
        iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
        iCombine "Hpaddr_f' Hpaddr_k" as "Hpaddr''".
        iApply ("Hcont" with "Hmm'' Hpmpc'' Hpaddr'' Hpc' Hf' Hbw'"). }
    iIntros "Hf HPC HnPC Hfrag".
    iDestruct (st_frames_tor_in (DfracOwn (q/2)) ms0 mseccfg0 pmpcfg0 pmpaddrs
                 pmar0
                 with "Hpaddr_f Hpriv_k Hms_k Hmseccfg Hpmpc_k Hpma Hhtif")
      as "[Hrw Hro]".
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
    unfold execute_STORE.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. w_glue.
    assert (Hva : is_aligned_vaddr (Virtaddr ea) 8 = true).
    { unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign. }
    iApply (swp_bind_use (rX_bits (Regidx rs2)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (w) "(-> & Hf)". w_glue.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗ gpr_file m ∗
                         hreg_frame
                           (st_rs ms0 mseccfg0 pmpcfg0 pmpaddrs pmar0) ∅ ∗
                         hreg_frame_ro (st_Df (DfracOwn (q/2)))
                           (st_rs ms0 mseccfg0 pmpcfg0 pmpaddrs pmar0)
                           st_Dro_tor ∗
                         ([∗ list] j ∈ seq 0 8,
                            (pa_add ea j) ↦ₚ nth_byte (m !!! Regidx rs2) j) ∗
                         resv_frag cpu_id None)%I) _
              with "[Hf Hrw Hro Hbytes Hfrag] [-]").
    { iApply (swp_vmem_write_gen8 ∅ st_Dro_tor (st_Df (DfracOwn (q/2)))
                (st_rs ms0 mseccfg0 pmpcfg0 pmpaddrs pmar0) (Regidx rs1)
                (sign_extend' 64 imm) ea _ pmar0
                ([∗ list] j ∈ seq 0 8,
                   (pa_add ea j) ↦ₚ nth_byte (m !!! Regidx rs2) j)%I
                (gpr_file m) None
                stt_disj stt_in_mst stt_in_priv stt_in_pma stt_in_htif
                (st_rs_priv _ _ _ _ _) (st_rs_pma _ _ _ _ _)
                (st_rs_htif _ _ _ _ _)
                ltac:(rewrite st_rs_mst; exact HMPRV)
                (st_hval_pmp_tor0 (∅ ∪ st_Dro_tor) ∅ _ pmpcfg0 pmpaddrs ea
                   stt_in_pcfg stt_in_paddr (st_rs_pcfg _ _ _ _ _)
                   (st_rs_paddr _ _ _ _ _) Htor)
                (pma_all_ram Hpma_all) Hram_ea Hva Halign
                with "Hcert Hfrag Hrw Hro Hf [] [Hbytes]").
      - iIntros "HQ Hrw Hro".
        unfold get_transformed_data_addr.
        iApply (swp_bind_use
                  (ext_data_get_addr (Regidx rs1) (sign_extend' 64 imm)
                     (Store Data) 8) _
                  (fun r => (⌜r = (Ext_DataAddr_OK (Virtaddr ea)
                                   : Ext_DataAddr_Check unit)⌝ ∗
                             gpr_file m)%I) _
                  with "[HQ] [-]").
        { unfold ext_data_get_addr.
          iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[HQ] [-]").
          { iApply (swp_rX_file rs1 m with "Hcert HQ"). }
          iIntros (w1) "(-> & Hf1)". iApply swp_ret. by iFrame. }
        iIntros (r) "(-> & Hf1)". cbn match.
        iApply (swp_mono with "[Hf1] [-]");
          [| iApply (swp_hfrun 12 ∅ st_Dro_tor (st_Df (DfracOwn (q/2)))
                       (st_rs ms0 mseccfg0 pmpcfg0 pmpaddrs pmar0) _ _ _
                       stt_disj
                       (hfrun_tea_store (∅ ∪ st_Dro_tor) ∅
                          (st_rs ms0 mseccfg0 pmpcfg0 pmpaddrs pmar0) ea
                          stt_in_mst stt_in_priv stt_in_sec
                          (st_rs_priv _ _ _ _ _)
                          ltac:(rewrite st_rs_mst; exact HMPRV)
                          ltac:(rewrite st_rs_sec; exact Hpmm))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)". by iFrame.
      - iIntros (sg) "Hsg". rewrite /mstate_interp.
        iDestruct "Hsg" as "(Hri & Hmem & Hdev)".
        iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
        iNext. iMod "Hmask" as "_".
        iMod (upd_window_8 sg.(mem) ea (m !!! Regidx rs2) vold
                with "Hmem Hbytes") as "[Hmem Hbytes]".
        iModIntro. rewrite st_write_value. by iFrame. }
    iIntros (v0) "(-> & Hf & Hrw & Hro & Hbytes & Hfrag)". w_glue.
    iApply swp_ret.
    iDestruct (st_frames_tor_out (DfracOwn (q/2)) ms0 mseccfg0 pmpcfg0 pmpaddrs
                 pmar0 with "Hro")
      as "(Hpaddr_f & Hpriv_k & Hms_k & _ & Hpmpc_k & _ & _)".
    iSplitR; [done|]. iFrame "Hf HPC HnPC".
    iSplitL "Hfrag"; [iApply (resv_any_intro with "Hfrag")|].
    iSplitL "Hhs_k Hpriv_k Hms_k".
    { iFrame "Hhw Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro.
      exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iFrame "Hpmpc_k Hpaddr_f".
    rewrite /phys_word_pointsto. iFrame "Hbytes". iPureIntro. exact Halign.
  Qed.

  (* ---- c.ldsp rd, uimm(sp), TOR-aware ---- *)

  Lemma wp_csdsp_gpr_tor (pc : mword 64) (uimm : mword 6)
      (rs2 : mword 5) (m : regfile) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx csp_rs1, 8)) -∗
    ea ↦ₚ₈ vold -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      ea ↦ₚ₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm ea Hpmp Hstat Htor.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont".
    iApply (wp_store_gpr_tor pc true csp_rs1 rs2 imm m vold
              pmpcfg0 pmpaddrs q Hpmp Hstat Htor
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont").
  Qed.

End MmodeStoreTor.
