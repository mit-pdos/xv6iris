(* HartSMem.v -- the S-MODE DATA-ACCESS [swp] ENGINES.

   The twins of [HartMLoad.swp_execute_LOAD8] / [HartMStore.swp_execute_STORE]
   one privilege over, and the suppliers for the S-mode data leaves
   (WpSconfMem.v's loads and stores, WpSconfLock.v's amoswap.w.aq, and the
   4-/1-byte MMIO accesses of WpPlic.v / WpVirtioDev.v / ProofUart.v).

   FOUR THINGS ARE DIFFERENT FROM THE M-MODE CHAIN, and they are the whole
   content of this file:

   1. THE TRANSLATION IS AN OBLIGATION, NOT A WALK.  At Machine the chain
      computes [translateAddr] with [hfrun] (Bare is the identity).  At
      Supervisor it is a page walk that READS MEMORY and may WRITE the [tlb]
      register, so it cannot be a computed run: it enters as a wand premise
      whose conclusion is exactly [SRegime.sr_swp_translate]'s -- the
      landing file [rsf] existential with [rsf = rs \/ exists tv,
      rsf = register_set tlb tv rs], the regime residue [Rt rsf], and
      [resv_any cpu_id].  A leaf plugs in [sr_swp_translate] or
      [HartSKpt.swp_translate_kpt] and the engine stays regime-agnostic.
      EVERYTHING AFTER THE TRANSLATION RUNS AT [rsf]; [sland_lookup] below is
      the one lemma that transports a register fact across the landing.

   2. THE PMP CHECK IS [PtTreeAdue.swp_pmpCheck_S] -- the kernel's TOR entry
      0, generic in the access class and the width, its premises spelled the
      way [WpSFrames.s_cycle] spells them.  The M-mode chain instead takes
      the check as an obligation because an 8-byte window can straddle a
      grain boundary at an arbitrary PMP configuration; the kernel's does
      not, so here it is discharged inside.

   3. THE WIDTH IS A PARAMETER.  The leaves need 1/2/4/8, signed and
      unsigned.  Everything above the memory NODE is proved once over a
      symbolic [width] (the section variables below); the node itself is
      per-width, because [ReadReq.t n] / [bv (8*n)] are TYPE indices that do
      not reduce at a call site (the trap [HartMFetch]'s 2-byte twins
      record).  So the node enters the generic chain as the [Hread_node] /
      [Hwrite_node] hypotheses and the four instances are at the bottom.

   4. THE MMIO ARM.  At a device address [within_mmio_readable] answers
      TRUE, the model takes [mmio_read]/[mmio_write] instead of
      [read_ram]/[write_ram], and the event is [HartEvents.swp_hart_dev_read]
      / [_dev_write].  Those engines are separate rules rather than a flag on
      the RAM ones -- the two arms share no node.

   The [R]-threading of design note 9 is preserved throughout: every memory
   obligation hands back a caller-chosen [R] so a leaf can tell its
   continuation what the cell now holds. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes TsoMemPa.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMPmp HartMFetch HartMFrame
        HartMLoad HartMStore.
Require Import RiscvExtras RiscvFetchExec.
Require Import RegFile WpGpr.
Require Import WpMmodeLeafBase SmodePte PtTreeAdue.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Local Arguments Z.sub _ _ : simpl nomatch.
Local Arguments Z.add _ _ : simpl nomatch.
Local Arguments Z.mul _ _ : simpl nomatch.
Local Arguments Z.eqb _ _ : simpl nomatch.
Local Arguments Z.compare _ _ : simpl nomatch.
Local Arguments Z.pos_sub _ _ : simpl nomatch.
Local Arguments Pos.compare _ _ : simpl nomatch.
Local Arguments Pos.compare_cont _ _ _ : simpl nomatch.

Local Ltac sm_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Riscv.rv64d_types.returnR
     Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access __id
     get_config_rvfi plat_have_clint plat_have_sig].

(* the GLUE reducer for the swp walk: pure combinators only.  It must NOT
   unfold [Defs.bind]/[liftR]/[catch_early_return] -- those are the shape
   [swp_use_cer] matches on. *)
Local Ltac sm_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR Riscv.rv64d_types.returnR
     andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Local Ltac sm_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

(* [returnR] is [Interface.Ret] behind an explicit type argument, and it does
   NOT unfold under a whitelisted [cbn] (the model sets it [simpl never]), so
   the two reduction equations the early-return regions need are named. *)
Lemma mbindR_ret {R A B : Type} (v : A) (f : A -> MR R B) :
  Defs.bind (Riscv.rv64d_types.returnR R v) f = f v.
Proof. reflexivity. Qed.

Lemma mbind0R_ret {R B : Type} (x : MR R B) :
  Defs.bind0 (Riscv.rv64d_types.returnR R tt) x = x.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(* 0. THE LANDING FILE.                                                    *)
(*                                                                        *)
(* The translation may fill the TLB and nothing else, so every register    *)
(* fact except [tlb]'s survives it.  [SmodeCorePt.pt_regs_preserved] is    *)
(* the same statement at the exec layer; it is restated here because that  *)
(* file sits ABOVE this one.                                              *)
(* ====================================================================== *)
Lemma sland_lookup (rs rsf : regstate) :
  (rsf = rs \/ exists tv, rsf = register_set tlb tv rs)%type ->
  forall r : register, register_beq r tlb = false ->
    register_lookup r rsf = register_lookup r rs.
Proof.
  intros [-> | (tv & ->)] r Hr; [reflexivity |].
  apply (irrelevant_register_set r tlb rs tv Hr).
Qed.

(* fuel-slack composition: [hfrun_bind] with the two fuels not required to
   ADD UP to the caller's, so a chain's fuel is one round number. *)
Lemma hfrun_bindm {X Y : Type} (n n1 n2 : nat) (D Drw : gset register)
    (rs rs' rs'' : regstate) (m : M X) (f : X -> M Y) (x : X) (y : Y) :
  (n1 + n2 <= n)%nat ->
  hfrun n1 D Drw rs m = Some (x, rs') ->
  hfrun n2 D Drw rs' (f x) = Some (y, rs'') ->
  hfrun n D Drw rs (Defs.bind m f) = Some (y, rs'').
Proof.
  intros Hle H1 H2.
  apply (hfrun_mono (n1 + n2) n D Drw rs _ _ Hle).
  exact (hfrun_bind n1 n2 D Drw rs rs' rs'' m f x y H1 H2).
Qed.

(* ====================================================================== *)
(* 1. THE PMA CHECK at Supervisor, WIDTH-GENERIC.                          *)
(*                                                                        *)
(* [HartMLoad.hfrun_check_pma_load8] / [HartMStore.hfrun_check_pma_store4] *)
(* with the width a parameter and the privilege one over.  The RAM-access  *)
(* side condition is derived from [addr_is_ram] the same way, but it needs *)
(* [(width | 4096)] rather than a per-width [lia]: the bank's end is       *)
(* 4096-aligned, so a [width]-aligned base whose byte is in the bank has   *)
(* room for the whole window exactly when [width] divides 4096.            *)
(* ====================================================================== *)
Lemma pma_ram_access_w (a : SailStdpp.Values.mword 64) (width : Z) :
  0 < width -> width <= 4096 -> (width | 4096) ->
  addr_is_ram a -> is_aligned_paddr (Physaddr a) width = true ->
  pma_ram_access a width.
Proof.
  intros Hpos Hle Hdvd [Hlo Hhi] Hal.
  unfold is_aligned_paddr in Hal. apply Z.eqb_eq in Hal.
  apply Zrem_divides in Hal. destruct Hal as [k Hk].
  destruct Hdvd as [q Hq].
  unfold ram_base, ram_size in Hhi, Hlo.
  unfold pma_ram_access, ram_base, ram_size.
  split; [ lia | ]. split; [ lia | ].
  (* uint a = width * k, and 2281701376 = 4096 * 557056 = width * (q * 557056) *)
  assert (Hend : (2147483648 + 134217728)%Z = width * (q * 557056)) by nia.
  assert (Hlt : width * k < width * (q * 557056))
    by (rewrite <- Hend; rewrite <- Hk; exact Hhi).
  assert (Hk2 : k < q * 557056) by nia.
  rewrite Hk. rewrite Hend. nia.
Qed.

Lemma hfrun_check_pma_load_S (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region)
    (width : Z) :
  0 < width -> width <= 4096 -> (width | 4096) ->
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  addr_is_ram pa ->
  is_aligned_paddr (Physaddr pa) width = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Load Data) PBMT_PMA Supervisor
       (Physaddr pa) width false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros Hpos Hle Hdvd HD Hpma Hpallow Hram Hpa.
  unfold check_pma_with_pmp_priority. sm_cbn.
  sm_read. rewrite Hpma. sm_cbn.
  destruct (Hpallow pa width (pma_ram_access_w pa width Hpos Hle Hdvd Hram Hpa))
    as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. sm_cbn.
  rewrite Hx. sm_cbn.
  rewrite Hpa. sm_cbn.
  apply hfrun_ret.
Qed.

Lemma hfrun_check_pma_store_S (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region)
    (width : Z) :
  0 < width -> width <= 4096 -> (width | 4096) ->
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  addr_is_ram pa ->
  is_aligned_paddr (Physaddr pa) width = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Store Data) PBMT_PMA Supervisor
       (Physaddr pa) width false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros Hpos Hle Hdvd HD Hpma Hpallow Hram Hpa.
  unfold check_pma_with_pmp_priority. sm_cbn.
  sm_read. rewrite Hpma. sm_cbn.
  destruct (Hpallow pa width (pma_ram_access_w pa width Hpos Hle Hdvd Hram Hpa))
    as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & _ & Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. sm_cbn.
  rewrite Hx. sm_cbn.
  rewrite Hpa. sm_cbn.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 2. THE PAGE-SPLIT TEST, as a TERM equation, at any of the four widths.   *)
(*                                                                        *)
(* [RiscvExtras.exec_split_on_page_boundary_aligned] is the same fact at    *)
(* the exec layer; the [swp] chain needs it as a rewrite on the model term  *)
(* instead, and the whole difference is the last line.  With this the data  *)
(* chains have NO page-split premise -- natural alignment decides it.       *)
(* ====================================================================== *)
Lemma split_on_page_boundary_aligned_w (a : SailStdpp.Values.mword 64) (w : Z) :
  vmem_width w ->
  is_aligned_vaddr (Virtaddr a) w = true ->
  split_on_page_boundary a w = returnM (w, 0).
Proof.
  intros Hw Halign.
  assert (Hpos : 0 < w) by (apply vmem_width_pos; exact Hw).
  assert (Hle : w <= 8) by (apply vmem_width_le; exact Hw).
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  destruct Hr as [Hr0 Hr1].
  assert (Hal : bv_unsigned a mod w = 0).
  { unfold is_aligned_vaddr in Halign. apply Z.eqb_eq in Halign.
    rewrite uint_unsigned in Halign.
    assert (Hrm : Z.rem (bv_unsigned a) w = (bv_unsigned a) mod w)
      by (apply Z.rem_mod_nonneg; [ exact Hr0 | lia ]).
    rewrite Hrm in Halign. exact Halign. }
  assert (Hnw : bv_unsigned a + (w - 1) < 2 ^ 64)
    by (apply z_alignw_room; assumption).
  assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a w) 1)
                 = bv_unsigned a + (w - 1)).
  { unfold sub_vec_int, add_vec_int.
    rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
    rewrite !moi64_unsigned.
    assert (Hww : bv_wrap 64 w = w)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    assert (Hw1 : bv_wrap 64 1 = 1)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hww. rewrite Hw1.
    rewrite bv_wrap_sub_idemp_l.
    assert (Hsimp : bv_unsigned a + w - 1 = bv_unsigned a + (w - 1))
      by (clear; lia).
    rewrite Hsimp.
    apply bv_wrap_small. rewrite bv_modulus64.
    assert (H64 : (2:Z) ^ 64 = 18446744073709551616)
      by (vm_compute; reflexivity).
    rewrite <- H64. split; [ clear - Hr0 Hpos; lia | exact Hnw ]. }
  unfold split_on_page_boundary.
  assert (Hintra :
    eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                         (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
           (and_vec (sub_vec_int (add_vec_int a w) 1)
                    (update_subrange_vec_dec ((ones 64) : bits 64)
                       (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = true).
  { apply eq_vec_true_iff. apply bv_eq.
    rewrite !and_vec64_unsigned. rewrite page_mask64_val.
    rewrite Hsub.
    assert (Hnn : 0 <= bv_unsigned a + (w - 1)) by (clear - Hr0 Hpos; lia).
    rewrite (z_land_pagemask (bv_unsigned a) Hr0 Hr1).
    rewrite (z_land_pagemask (bv_unsigned a + (w - 1)) Hnn Hnw).
    rewrite <- (z_shiftr12_stable_w (bv_unsigned a) w Hr0 Hw Hal). reflexivity. }
  rewrite Hintra. reflexivity.
Qed.

(* ====================================================================== *)
(* 3. [translationMode] AT SUPERVISOR, Sv39, as a computed run.            *)
(*                                                                        *)
(* [SRegime.hfrun_translateAddr_S_bare] runs the same two nodes inline at   *)
(* satp.MODE = Bare; this is the Sv39 answer, needed on its own because     *)
(* [vmem_read_addr] / [vmem_write_addr] and                                *)
(* [transform_effective_address] all consult it OUTSIDE [translateAddr].   *)
(* ====================================================================== *)
(* THE MODE-GENERIC WALK.  The mode's VALUE is never used downstream (see
   the branch note in [swp_vmem_read_addr_S_gen]); what a caller needs is
   that the walk LANDS, and it does as soon as the satp mode bits decode --
   which is the one thing a regime says about its satp value.  The Sv39
   instance below keeps its statement, and a Bare caller (or any regime,
   through [s_regime]'s own mode field) uses the generic one. *)
Lemma hfrun_translationMode_S_mode (D Drw : gset register) (rs : regstate)
    (md : SATPMode) :
  (mstatus : register) ∈ D ->
  (satp : register) ∈ D ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)))
    = Some md ->
  hfrun 6 D Drw rs (translationMode Supervisor) = Some (md, rs).
Proof.
  intros HDmst HDsatp HSXL Hmd.
  unfold translationMode.
  replace (Instances.generic_eq Supervisor Machine) with false
    by (vm_compute; reflexivity).
  sm_cbn.
  unfold architecture. cbn match. sm_cbn.
  sm_read. sm_cbn.
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity).
  cbn match. sm_cbn.
  change (xlen >=? 64) with true.
  unfold Defs.assert_exp'. cbn match. sm_cbn.
  sm_read. sm_cbn.
  rewrite Hmd.
  cbn match. sm_cbn.
  apply hfrun_ret.
Qed.

Lemma hfrun_translationMode_S_sv39 (D Drw : gset register) (rs : regstate) :
  (mstatus : register) ∈ D ->
  (satp : register) ∈ D ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)) = ('b"1000" : mword 4) ->
  hfrun 6 D Drw rs (translationMode Supervisor) = Some (Sv39, rs).
Proof.
  intros HDmst HDsatp HSXL Hmode.
  unfold translationMode.
  replace (Instances.generic_eq Supervisor Machine) with false
    by (vm_compute; reflexivity).
  sm_cbn.
  unfold architecture. cbn match. sm_cbn.
  sm_read. sm_cbn.
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity).
  cbn match. sm_cbn.
  change (xlen >=? 64) with true.
  unfold Defs.assert_exp'. cbn match. sm_cbn.
  sm_read. sm_cbn.
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. sm_cbn.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 4. [transform_effective_address] AT SUPERVISOR.                         *)
(*                                                                        *)
(* [HartMLoad.hfrun_transform_effective_address_load] one privilege over.   *)
(* Two differences, both from the privilege: the pointer-masking mode comes *)
(* from [menvcfg] (M-mode reads [mseccfg]) and reaching it needs MXR = 0,   *)
(* and the mode is Sv39, so the transform is [pm_transform_VA] rather than  *)
(* [pm_transform_PA] -- at pmlen 0 both are the identity.                  *)
(* ====================================================================== *)
Lemma hfrun_transform_effective_address_S_mode (D Drw : gset register)
    (rs : regstate) (a : SailStdpp.Values.mword 64)
    (acc : MemoryAccessType mem_payload) (md : SATPMode) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (menvcfg : register) ∈ D ->
  (satp : register) ∈ D ->
  register_lookup cur_privilege rs = Supervisor ->
  effectivePrivilege acc (register_lookup mstatus rs) Supervisor
    = returnM Supervisor ->
  Instances.generic_neq acc (InstructionFetch tt) = true ->
  Instances.generic_neq acc (Load PageTableEntry) = true ->
  Instances.generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
    = PMM_Disabled ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)))
    = Some md ->
  hfrun 20 D Drw rs (transform_effective_address (Virtaddr a) acc)
  = Some (Virtaddr a, rs).
Proof.
  intros HDmst HDpriv HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr Hpmm HSXL Hmode.
  unfold transform_effective_address.
  sm_cbn.
  sm_read. sm_cbn.
  sm_read. rewrite Hpriv. sm_cbn.
  rewrite Hep. sm_cbn.
  unfold get_pmlen, is_pmm_applicable.
  sm_cbn.
  rewrite Hnf Hnlp Hnsp. sm_cbn.
  replace (Instances.generic_eq Supervisor Machine) with false
    by (vm_compute; reflexivity).
  sm_cbn.
  sm_read. rewrite Hmxr. sm_cbn.
  unfold get_pmm. cbn match. sm_cbn.
  sm_read. rewrite Hpmm. sm_cbn.
  apply (hfrun_bindm _ 6 10 D Drw rs rs rs _ _ md (Virtaddr a));
    [ lia
    | exact (hfrun_translationMode_S_mode D Drw rs md HDmst HDsatp HSXL Hmode)
    | ].
  sm_cbn.
  (* THE MODE'S ONE EFFECT ON THE ADDRESS, and it is none: at pmlen 0 the
     physical transform and the virtual one are both the identity (this is
     what the section header claims; here it is, discharged). *)
  destruct (Instances.generic_eq md Bare);
    cbn match;
    [ unfold pm_transform_PA; change (xlen - 0 - 1) with 63;
      rewrite subrange_full_64 zero_extend'_id
    | unfold pm_transform_VA; change (xlen - 0 - 1) with 63;
      rewrite subrange_full_64 sign_extend'_id ];
    apply hfrun_ret.
Qed.

(* the Sv39 instance, statement unchanged *)
Lemma hfrun_transform_effective_address_S (D Drw : gset register)
    (rs : regstate) (a : SailStdpp.Values.mword 64)
    (acc : MemoryAccessType mem_payload) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (menvcfg : register) ∈ D ->
  (satp : register) ∈ D ->
  register_lookup cur_privilege rs = Supervisor ->
  effectivePrivilege acc (register_lookup mstatus rs) Supervisor
    = returnM Supervisor ->
  Instances.generic_neq acc (InstructionFetch tt) = true ->
  Instances.generic_neq acc (Load PageTableEntry) = true ->
  Instances.generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
    = PMM_Disabled ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)) = ('b"1000" : mword 4) ->
  hfrun 20 D Drw rs (transform_effective_address (Virtaddr a) acc)
  = Some (Virtaddr a, rs).
Proof.
  intros HDmst HDpriv HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr Hpmm HSXL Hmode.
  apply (hfrun_transform_effective_address_S_mode D Drw rs a acc Sv39
           HDmst HDpriv HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr Hpmm HSXL).
  rewrite Hmode. vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE TWO Sv39 ADAPTERS.  The engines below take the address transform and *)
(* the translation mode as [hval] FACTS rather than as the satp-mode        *)
(* equation, because the leaves they serve are REGIME-GENERIC: a leaf       *)
(* holding only [SRegime.sr_inv R] cannot say whether its regime installs   *)
(* Sv39 or Bare, and the mode decides a branch inside [vmem_read_addr] /    *)
(* [vmem_write_addr] and inside [transform_effective_address].  A leaf that *)
(* DOES know it is on the kernel table feeds these two, which are the       *)
(* [hfrun] walks above at the [hval] layer.                                 *)
(* ---------------------------------------------------------------------- *)
Lemma hval_translationMode_S_sv39 (D Drw : gset register) (rs : regstate) :
  (mstatus : register) ∈ D ->
  (satp : register) ∈ D ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)) = ('b"1000" : mword 4) ->
  hval D Drw rs (translationMode Supervisor) Sv39 rs.
Proof.
  intros HDmst HDsatp HSXL Hmode.
  exact (hfrun_hval 6 D Drw rs _ _ _
           (hfrun_translationMode_S_sv39 D Drw rs HDmst HDsatp HSXL Hmode)).
Qed.

Lemma hval_transform_effective_address_S (D Drw : gset register)
    (rs : regstate) (a : SailStdpp.Values.mword 64)
    (acc : MemoryAccessType mem_payload) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (menvcfg : register) ∈ D ->
  (satp : register) ∈ D ->
  register_lookup cur_privilege rs = Supervisor ->
  effectivePrivilege acc (register_lookup mstatus rs) Supervisor
    = returnM Supervisor ->
  Instances.generic_neq acc (InstructionFetch tt) = true ->
  Instances.generic_neq acc (Load PageTableEntry) = true ->
  Instances.generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
    = PMM_Disabled ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)) = ('b"1000" : mword 4) ->
  hval D Drw rs (transform_effective_address (Virtaddr a) acc) (Virtaddr a) rs.
Proof.
  intros HDmst HDpriv HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr Hpmm HSXL Hmode.
  exact (hfrun_hval 20 D Drw rs _ _ _
           (hfrun_transform_effective_address_S D Drw rs a acc HDmst HDpriv
              HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr Hpmm HSXL Hmode)).
Qed.

(* ...and the MODE-GENERIC twins, which is what a regime-generic leaf uses:
   it names no mode, only that its regime's satp value decodes. *)
Lemma hval_translationMode_S_mode (D Drw : gset register) (rs : regstate)
    (md : SATPMode) :
  (mstatus : register) ∈ D ->
  (satp : register) ∈ D ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)))
    = Some md ->
  hval D Drw rs (translationMode Supervisor) md rs.
Proof.
  intros HDmst HDsatp HSXL Hmd.
  exact (hfrun_hval 6 D Drw rs _ _ _
           (hfrun_translationMode_S_mode D Drw rs md HDmst HDsatp HSXL Hmd)).
Qed.

Lemma hval_transform_effective_address_S_mode (D Drw : gset register)
    (rs : regstate) (a : SailStdpp.Values.mword 64)
    (acc : MemoryAccessType mem_payload) (md : SATPMode) :
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (menvcfg : register) ∈ D ->
  (satp : register) ∈ D ->
  register_lookup cur_privilege rs = Supervisor ->
  effectivePrivilege acc (register_lookup mstatus rs) Supervisor
    = returnM Supervisor ->
  Instances.generic_neq acc (InstructionFetch tt) = true ->
  Instances.generic_neq acc (Load PageTableEntry) = true ->
  Instances.generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
    = PMM_Disabled ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs)))
    = Some md ->
  hval D Drw rs (transform_effective_address (Virtaddr a) acc) (Virtaddr a) rs.
Proof.
  intros HDmst HDpriv HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr Hpmm HSXL Hmd.
  exact (hfrun_hval 20 D Drw rs _ _ _
           (hfrun_transform_effective_address_S_mode D Drw rs a acc md HDmst
              HDpriv HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr Hpmm HSXL Hmd)).
Qed.

(* ====================================================================== *)
(* 5. THE ENGINES.                                                         *)
(*                                                                        *)
(* [width] and the RAM node are section parameters (see the header): the    *)
(* node's request record is a TYPE index, so it is instantiated per width   *)
(* at the bottom of the file, and everything between the node and           *)
(* [execute_LOAD] / [execute_STORE] is proved once.                        *)
(* ====================================================================== *)

(* THE BYTE-WISE MEMORY PREMISE.  [read_bytes] ties the value's width to the
   access's ([option (bv (8*n))]), and at a SYMBOLIC width the two indices --
   [8 * Z.to_N width] and [Z_idx (8 * width)] -- are equal only by [lia].  The
   byte-wise spelling has no such tie, and it is already the shape the S-mode
   leaves own their data in ([WpSconfMem.wordw_pointsto]). *)
Definition mem_bytes_at (s : mstate) (pa : Arch.pa) (width : Z)
    (w : SailStdpp.Values.mword (8 * width)) : Prop :=
  forall j : nat, (N.of_nat j < Z.to_N width)%N ->
    s.(mem) !! (pa_add pa j) = Some (nth_byte w j).

Section smem.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ---- the section's width and its two per-width nodes ---- *)
  Variable width : Z.
  Hypothesis Hvw : vmem_width width.
  Hypothesis Hdvd : (width | 4096).
  Hypothesis Huintw : uint (to_bits 64 width) = width.

  Local Lemma w_pos : 0 < width.
  Proof. exact (vmem_width_pos width Hvw). Qed.
  Local Lemma w_le8 : width <= 8.
  Proof. exact (vmem_width_le width Hvw). Qed.

  (* THE ADDRESS CLASS.  RAM and MMIO run the SAME chain and differ in
     exactly four facts, so those are the section's parameters rather than a
     second copy of the tower: what the PMA table must grant ([Pma]), which
     addresses this engine serves ([Acls]), and -- derived from those -- the
     PMA walk, the [within_mmio_*] answer, the PMP range match and the node.
     The RAM and device instances are at the bottom of the file. *)
  Variable Acls : SailStdpp.Values.mword 64 -> Prop.
  Variable Pma : list PMA_Region -> Prop.

  Hypothesis Hpma_load :
    forall (D Drw : gset register) (rs : regstate)
           (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region),
      (pma_regions : register) ∈ D ->
      register_lookup pma_regions rs = pmar0 ->
      Pma pmar0 -> Acls pa ->
      is_aligned_paddr (Physaddr pa) width = true ->
      hfrun 6 D Drw rs
        (check_pma_with_pmp_priority (Load Data) PBMT_PMA Supervisor
           (Physaddr pa) width false)
      = Some (Values.Ok
                {| Phys_Mem_Access_Info_splittable := CannotSplit;
                   Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).

  Hypothesis Hmmio_r :
    forall (D Drw : gset register) (rs : regstate)
           (pa : SailStdpp.Values.mword 64),
      (htif_tohost_base : register) ∈ D ->
      register_lookup htif_tohost_base rs = None ->
      Acls pa ->
      hfrun 12 D Drw rs (within_mmio_readable (Physaddr pa) width)
      = Some (false, rs).

  Hypothesis Hpmprange :
    forall (pa paddr0 : SailStdpp.Values.mword 64),
      Acls pa -> is_aligned_paddr (Physaddr pa) width = true ->
      (ram_base + ram_size <= uint paddr0 * 4)%Z ->
      pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint paddr0) 4) (uint pa) (uint (to_bits 64 width))
      = PMP_Match.

  (* THE MEMORY OBLIGATION IS ABSTRACT TOO.  A RAM read hands the state back
     unchanged and pins the bytes; a DEVICE read hands back a NEW device state
     and pins the word the device answered.  The chain above never looks
     inside, so it is one parameter and the two instances differ only in it. *)
  Variable Mobl : SailStdpp.Values.mword 64 ->
                  SailStdpp.Values.mword (8 * width) -> iProp Σ -> iProp Σ.

  Hypothesis Hread_node :
    forall (pa : SailStdpp.Values.mword 64)
           (bytes : SailStdpp.Values.mword (8 * width)) (R : iProp Σ),
      Acls pa ->
      gen_cert -∗
      Mobl pa bytes R -∗
      swp (read_ram Read_plain (Physaddr pa) width false)
        (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).

  (* ------------------------------------------------------------------ *)
  (* [checked_mem_read] at [Load Data], Supervisor.                       *)
  (* [PtTreeAdue.swp_checked_mem_read_pte8]'s twin at the DATA access and  *)
  (* a symbolic width: the PMA conjunct is the readable one instead of     *)
  (* the pte-readable one, and the loop's accumulator identity is the      *)
  (* generic [usvd_zeros_full_gen] instead of a numeral instance.          *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_checked_mem_read_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * width)) (R : iProp Σ) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Mobl pa bytes R -∗
    swp (checked_mem_read (Load Data) PBMT_PMA Supervisor
           (Physaddr pa) width false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HR Hcov Hpallow Hram Hpa.
    pose proof w_pos as Hw0. pose proof w_le8 as Hw8.
    pose proof (Hpmprange pa (vec_access_dec paddr 0) Hram Hpa Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Load Data) PBMT_PMA
                 Supervisor (Physaddr pa) width false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (Hpma_load (Drw ∪ Dro) Drw rs pa pmar0
                   HDpma Hpma Hpallow Hram Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    replace (0 * width)%Z with 0%Z by lia. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) width (Load Data) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (Load Data) Drw Dro Df rs pcfg paddr
                pa width Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HR; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) width)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (Hmmio_r (Drw ∪ Dro) Drw rs pa HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_plain (Physaddr pa) width false)
              (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I)
              _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_mono (read_ram Read_plain (Physaddr pa) width false)
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗ R)%I)
                with "[Hrw Hro] [Hmem]").
      - iIntros (r) "(-> & HR)". by iFrame.
      - iApply (Hread_node pa bytes R Hram with "Hcert Hmem"). }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    replace (update_subrange_vec_dec (zeros' (8 * 1 * width))
               (8 * (0 + 1) * width - 1) (8 * 0 * width)
               (autocast (T := mword) bytes))
      with (update_subrange_vec_dec (zeros' (8 * width)) (8 * width - 1) 0
              (autocast (T := mword) bytes))
      by (f_equal; lia).
    rewrite (usvd_zeros_full_gen (8 * width) bytes ltac:(lia)).
    kill_autocast.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [mem_read] at [Load Data], Supervisor.  [HartMLoad.swp_mem_read_load8] *)
  (* with [effectivePrivilege] handed in as a TERM equation instead of      *)
  (* computed from MPRV: at Supervisor the answer depends on MPRV *and* MPP, *)
  (* which is the caller's [sconf] fact set, not this chain's business.      *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_mem_read_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr)
      (w : SailStdpp.Values.mword (8 * width)) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (Load Data) PBMT_PMA Supervisor pa width
              false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (mem_read (Load Data) PBMT_PMA pa width false false false)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv Hep.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep. rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [translate_and_read_value] -- WHERE THE TRANSLATION ENTERS.          *)
  (*                                                                     *)
  (* The obligation's conclusion is [SRegime.sr_swp_translate]'s verbatim, *)
  (* so a leaf plugs that field (or [HartSKpt.swp_translate_kpt]) straight *)
  (* in.  Everything after it runs at the landing file [rsf]; the register *)
  (* premises are stated at [rs] and transported by [sland_lookup].        *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_translate_and_read_value_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * width))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mobl pa bytes R -∗
    swp (translate_and_read_value (Virtaddr ea) width (Load Data)
           false false false)
      (fun r => ⌜r = Values.Ok (Physaddr pa, bytes)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv Hhtif Hpma
      Hpcfg Hpaddr Hep HA Hord HR Hcov Hpallow Hram Hpa.
    iIntros "#Hcert Hfrag Hres Hrw Hro Htr Hmem".
    unfold translate_and_read_value.
    iApply (swp_bind_use (translateAddr (Virtaddr ea) (Load Data)) _ _ _
              with "[Hfrag Hres Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hfrag Hres Hrw Hro"). }
    iIntros (v) "(-> & Hland)". cbn beta iota.
    iDestruct "Hland" as (rsf) "(%Hland & Hrw & Hro & Hres & Hany)".
    assert (Hpriv' : register_lookup cur_privilege rsf = Supervisor)
      by (rewrite (sland_lookup rs rsf Hland cur_privilege eq_refl); exact Hpriv).
    assert (Hmst' : register_lookup mstatus rsf = register_lookup mstatus rs)
      by (apply (sland_lookup rs rsf Hland mstatus eq_refl)).
    assert (Hhtif' : register_lookup htif_tohost_base rsf = None)
      by (rewrite (sland_lookup rs rsf Hland htif_tohost_base eq_refl); exact Hhtif).
    assert (Hpma' : register_lookup pma_regions rsf = pmar0)
      by (rewrite (sland_lookup rs rsf Hland pma_regions eq_refl); exact Hpma).
    assert (Hpcfg' : register_lookup pmpcfg_n rsf = pcfg)
      by (rewrite (sland_lookup rs rsf Hland pmpcfg_n eq_refl); exact Hpcfg).
    assert (Hpaddr' : register_lookup pmpaddr_n rsf = paddr)
      by (rewrite (sland_lookup rs rsf Hland pmpaddr_n eq_refl); exact Hpaddr).
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok bytes⌝ ∗
                         hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗ R)%I) _
              with "[Hrw Hro Hmem] [Hres Hany]").
    { iApply (swp_mem_read_S Drw Dro Df rsf (Physaddr pa) bytes R Hdisj
                HDmst HDpriv Hpriv' ltac:(rewrite Hmst'; exact Hep)
                with "Hcert Hrw Hro [Hmem]").
      iIntros "Hrw Hro".
      iApply (swp_checked_mem_read_S Drw Dro Df rsf pa pmar0 pcfg paddr bytes R
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif' Hpma' Hpcfg' Hpaddr'
                HA Hord HR Hcov Hpallow Hram Hpa with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota.
    iApply swp_ret. iSplitR; [done|].
    iExists rsf. iFrame. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [vmem_read_addr] at Supervisor.  Two nodes more than the M-mode twin: *)
  (* [translationMode] really RUNS here (mstatus.SXL then satp), where at   *)
  (* Machine it short-circuits to [Bare].  Its answer decides                *)
  (* [do_split_access], and the page-split test has already answered          *)
  (* [(width, 0)], so the split arm is dead and the chain is one access.     *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_vmem_read_addr_S_gen (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * width))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mobl pa bytes R -∗
    swp (vmem_read_addr (Virtaddr ea) width (Load Data) false false false)
      (fun r => ⌜r = Values.Ok bytes⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hhtif
      Hpma Hpcfg Hpaddr HSXL Hmode Hep HA Hord HR Hcov Hpallow Hram Hva Hpa.
    pose proof w_pos as Hw0. pose proof w_le8 as Hw8.
    iIntros "#Hcert Hfrag Hres Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read_addr.
    rewrite Hva. sm_glue.
    rewrite mbind0_ret.
    rewrite (split_on_page_boundary_aligned_w ea width Hvw Hva).
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep.
    rewrite mliftR_ret mbind_ret. sm_glue.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (translationMode Supervisor) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hmode
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    (* THE ONE BRANCH THE MODE DECIDES, and both arms reach the same value:
       at [md <> Bare] the second conjunct is evaluated and is [false]; at
       [Bare] the [and_boolM] short-circuits to [false] outright. *)
    (* THE ONE BRANCH THE TRANSLATION MODE DECIDES, COLLAPSED BEFORE IT
       SPLITS THE PROOF.  The page-split conjunct is [next_page_bytes > 0]
       and the address is aligned, so the second conjunct is [0 >? 0] --
       [false] -- and [and_boolM] returns [false] whatever the mode is.
       Collapsing it here (rather than [destruct]ing the mode) is what keeps
       this walk ONE goal and the engines regime-generic: a leaf holding only
       [sr_inv R] cannot say which mode its regime installs. *)
    rewrite mbindR_ret.
    match goal with
    | |- context [ if Instances.generic_neq md Bare then ?x else ?y ] =>
        replace (if Instances.generic_neq md Bare then x else y) with x
          by (destruct (Instances.generic_neq md Bare); reflexivity)
    end.
    sm_glue.
    change (Z.gtb 0 0) with false. sm_glue.
    change (sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer
              (translate_and_read_value (Virtaddr ea) width (Load Data)
                 false false false) _ _ C HC
              with "[Hfrag Hres Hrw Hro Htr Hmem] [-]").
    { iApply (swp_translate_and_read_value_S Drw Dro Df rs ea pa pmar0 pcfg
                paddr bytes R Rt rr Hdisj HDmst HDpriv HDpma HDcfg HDaddr
                HDhtif Hpriv Hhtif Hpma Hpcfg Hpaddr Hep HA Hord HR Hcov
                Hpallow Hram Hpa with "Hcert Hfrag Hres Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hland)". cbn beta iota. sm_glue.
    rewrite mbind0R_ret. sm_glue.
    rewrite mbindR_ret. sm_glue.
    change (not sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite (usvd_zeros_full_gen (8 * width) bytes ltac:(lia)).
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok bytes)). iFrame. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the EFFECTIVE-ADDRESS stretch.  [rX_bits] at a SYMBOLIC index is the  *)
  (* one node no walker takes, so it is peeled at [gpr_file]; the rest is   *)
  (* the pinned-register walk [hfrun_transform_effective_address_S].        *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_get_transformed_data_addr_S_gen (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (i : SailStdpp.Values.mword 5) (m : regfile)
      (offset : SailStdpp.Values.mword 64)
      (acc : MemoryAccessType mem_payload) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    effectivePrivilege acc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    Instances.generic_neq acc (InstructionFetch tt) = true ->
    Instances.generic_neq acc (Load PageTableEntry) = true ->
    Instances.generic_neq acc (Store PageTableEntry) = true ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address
         (Virtaddr (add_vec (m !!! Regidx i) offset)) acc)
      (Virtaddr (add_vec (m !!! Regidx i) offset)) rs ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (get_transformed_data_addr (Regidx i) offset acc width)
      (fun r => ⌜r = Ext_DataAddr_OK
                       (Virtaddr (add_vec (m !!! Regidx i) offset))⌝ ∗
                gpr_file m ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep Hnf Hnlp Hnsp Hmxr
      Hpmm HSXL Hmode.
    iIntros "#Hcert Hf Hrw Hro".
    unfold get_transformed_data_addr, ext_data_get_addr.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Ext_DataAddr_OK
                               (Virtaddr (add_vec (m !!! Regidx i) offset))⌝ ∗
                         gpr_file m)%I) _ with "[Hf] [-]").
    { iApply (swp_bind_use (rX_bits (Regidx i)) _ _ _ with "[Hf] [-]").
      { iApply (swp_rX_file i m with "Hcert Hf"). }
      iIntros (w) "(-> & Hf)". iApply swp_ret. by iFrame. }
    iIntros (v0) "(-> & Hf)". cbn beta iota.
    iApply (swp_bind_use
              (transform_effective_address
                 (Virtaddr (add_vec (m !!! Regidx i) offset)) acc)
              _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hmode
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [vmem_read] and [execute_LOAD] at Supervisor.                        *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_vmem_read_S_gen (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (i : SailStdpp.Values.mword 5) (m : regfile)
      (offset pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * width))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx i) offset in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Load Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mobl pa bytes R -∗
    swp (vmem_read (Regidx i) offset width (Load Data) false false false)
      (fun r => ⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hhtif Hpma Hpcfg Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR
      Hcov Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx i) offset (Load Data) width)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_S_gen Drw Dro Df rs i m offset
                (Load Data) Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hmxr Hpmm HSXL Htf with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer0
              (vmem_read_addr (Virtaddr ea) width (Load Data) false false false)
              _ C HC with "[Hfrag Hres Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_read_addr_S_gen Drw Dro Df rs ea pa pmar0 pcfg paddr
                bytes R Rt rr md Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr
                HDhtif Hpriv Hhtif Hpma Hpcfg Hpaddr HSXL Hmode Hep HA Hord HR
                Hcov Hpallow Hram Hva Hpa
                with "Hcert Hfrag Hres Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hland)".
    iApply ("Hcont" $! (Values.Ok bytes)). iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_execute_LOAD_S_gen (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (imm : SailStdpp.Values.mword 12)
      (rs1 rd : SailStdpp.Values.mword 5) (is_unsigned : bool)
      (m : regfile) (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * width))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Load Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    uint rd <> 0 ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mobl pa bytes R -∗
    swp (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned width)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd
                            := regval_into_reg (extend_value is_unsigned bytes)]> m) ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hhtif Hpma Hpcfg Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR
      Hcov Hpallow Hram Hva Hpa Hrd.
    pose proof w_le8 as Hw8.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hmem".
    unfold execute_LOAD.
    replace (Z.leb width xlen_bytes) with true
      by (change xlen_bytes with 8; symmetry; apply Z.leb_le; exact Hw8).
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. sm_glue.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                         ∃ rsf : regstate,
                           ⌜ rsf = rs \/
                             exists tv, rsf = register_set tlb tv rs ⌝ ∗
                           hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                           Rt rsf ∗ resv_any cpu_id ∗ R)%I) _
              with "[Hfrag Hres Hf Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_read_S_gen Drw Dro Df rs rs1 m (sign_extend' 64 imm) pa
                pmar0 pcfg paddr bytes R Rt rr md Hdisj HDmst HDpriv HDmenv
                HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hhtif Hpma Hpcfg
                Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR Hcov Hpallow
                Hram Hva Hpa with "Hcert Hfrag Hres Hf Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hf & Hland)". cbn beta iota.
    iApply (swp_bind0_use (wX_bits (Regidx rd) (extend_value is_unsigned bytes))
              _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m (extend_value is_unsigned bytes) Hrd
                with "Hcert Hf"). }
    iIntros (u) "Hf". iApply swp_ret. by iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE SAME CHAIN WITH THE LOADED WORD EXISTENTIAL.                       *)
  (*                                                                       *)
  (* An atomic-update leaf -- a lock word, a device register -- learns the   *)
  (* value it loads by opening an invariant INSIDE the read node's own       *)
  (* callback, so it cannot name [bytes] before the step.  The read node is  *)
  (* therefore a parameter here too, but in its existential form: [Mex] is   *)
  (* whatever the leaf hands the node, [Rr] the value-indexed rider it gets  *)
  (* back, and [Hnode_ex] the leaf's own node fact.  The value-known chain   *)
  (* above is the instance [Rr b := ⌜b = bytes⌝ ∗ R].                        *)
  (* ==================================================================== *)
  Lemma swp_checked_mem_read_S_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) (Mex : iProp Σ) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    (⊢ gen_cert -∗ Mex -∗
       swp (read_ram Read_plain (Physaddr pa) width false)
         (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                     ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Mex -∗
    swp (checked_mem_read (Load Data) PBMT_PMA Supervisor
           (Physaddr pa) width false false false false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ Rr bytes).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HR Hcov Hpallow Hram Hpa Hnode_ex.
    pose proof w_pos as Hw0. pose proof w_le8 as Hw8.
    pose proof (Hpmprange pa (vec_access_dec paddr 0) Hram Hpa Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Load Data) PBMT_PMA
                 Supervisor (Physaddr pa) width false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (Hpma_load (Drw ∪ Dro) Drw rs pa pmar0
                   HDpma Hpma Hpallow Hram Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    replace (0 * width)%Z with 0%Z by lia. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) width (Load Data) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (Load Data) Drw Dro Df rs pcfg paddr
                pa width Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HR; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) width)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (Hmmio_r (Drw ∪ Dro) Drw rs pa HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_plain (Physaddr pa) width false)
              (fun r => (∃ bytes : SailStdpp.Values.mword (8 * width),
                         ⌜r = (bytes, default_meta)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗
                         Rr bytes)%I)
              _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_mono (read_ram Read_plain (Physaddr pa) width false)
                (fun r => (∃ bytes : SailStdpp.Values.mword (8 * width),
                           ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes)%I)
                with "[Hrw Hro] [Hmem]").
      - iIntros (r) "(%bs & -> & HR)". iExists bs. by iFrame.
      - iApply (Hnode_ex with "Hcert Hmem"). }
    iIntros (v) "(%bytes & -> & Hrw & Hro & HR)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    replace (update_subrange_vec_dec (zeros' (8 * 1 * width))
               (8 * (0 + 1) * width - 1) (8 * 0 * width)
               (autocast (T := mword) bytes))
      with (update_subrange_vec_dec (zeros' (8 * width)) (8 * width - 1) 0
              (autocast (T := mword) bytes))
      by (f_equal; lia).
    rewrite (usvd_zeros_full_gen (8 * width) bytes ltac:(lia)).
    kill_autocast.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). iExists bytes. by iFrame.
  Qed.

  Lemma swp_mem_read_S_ex (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (Load Data) PBMT_PMA Supervisor pa width
              false false false false)
         (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                   ⌜r = Values.Ok (bytes, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ Rr bytes)) -∗
    swp (mem_read (Load Data) PBMT_PMA pa width false false false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                ⌜r = Values.Ok bytes⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ Rr bytes).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv Hep.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep. rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (∃ bytes : SailStdpp.Values.mword (8 * width),
                         ⌜r = Values.Ok (bytes, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗
                         Rr bytes)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (∃ bytes : SailStdpp.Values.mword (8 * width),
                           ⌜r = Values.Ok (bytes, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗
                           Rr bytes)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(%bs & -> & Hrw & Hro & HR)". iApply swp_ret.
        iExists bs. by iFrame. }
    iIntros (v) "(%bs & -> & Hrw & Hro & HR)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. iExists bs. by iFrame.
  Qed.

  Lemma swp_translate_and_read_value_S_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) (Mex : iProp Σ)
      (Rt : regstate -> iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    (⊢ gen_cert -∗ Mex -∗
       swp (read_ram Read_plain (Physaddr pa) width false)
         (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                     ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes)) ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mex -∗
    swp (translate_and_read_value (Virtaddr ea) width (Load Data)
           false false false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                ⌜r = Values.Ok (Physaddr pa, bytes)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ Rr bytes).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv Hhtif Hpma
      Hpcfg Hpaddr Hep HA Hord HR Hcov Hpallow Hram Hpa Hnode_ex.
    iIntros "#Hcert Hfrag Hres Hrw Hro Htr Hmem".
    unfold translate_and_read_value.
    iApply (swp_bind_use (translateAddr (Virtaddr ea) (Load Data)) _ _ _
              with "[Hfrag Hres Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hfrag Hres Hrw Hro"). }
    iIntros (v) "(-> & Hland)". cbn beta iota.
    iDestruct "Hland" as (rsf) "(%Hland & Hrw & Hro & Hres & Hany)".
    assert (Hpriv' : register_lookup cur_privilege rsf = Supervisor)
      by (rewrite (sland_lookup rs rsf Hland cur_privilege eq_refl); exact Hpriv).
    assert (Hmst' : register_lookup mstatus rsf = register_lookup mstatus rs)
      by (apply (sland_lookup rs rsf Hland mstatus eq_refl)).
    assert (Hhtif' : register_lookup htif_tohost_base rsf = None)
      by (rewrite (sland_lookup rs rsf Hland htif_tohost_base eq_refl); exact Hhtif).
    assert (Hpma' : register_lookup pma_regions rsf = pmar0)
      by (rewrite (sland_lookup rs rsf Hland pma_regions eq_refl); exact Hpma).
    assert (Hpcfg' : register_lookup pmpcfg_n rsf = pcfg)
      by (rewrite (sland_lookup rs rsf Hland pmpcfg_n eq_refl); exact Hpcfg).
    assert (Hpaddr' : register_lookup pmpaddr_n rsf = paddr)
      by (rewrite (sland_lookup rs rsf Hland pmpaddr_n eq_refl); exact Hpaddr).
    iApply (swp_bind_use _ _
              (fun r => (∃ bytes : SailStdpp.Values.mword (8 * width),
                         ⌜r = Values.Ok bytes⌝ ∗
                         hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                         Rr bytes)%I) _
              with "[Hrw Hro Hmem] [Hres Hany]").
    { iApply (swp_mem_read_S_ex Drw Dro Df rsf (Physaddr pa) Rr Hdisj
                HDmst HDpriv Hpriv' ltac:(rewrite Hmst'; exact Hep)
                with "Hcert Hrw Hro [Hmem]").
      iIntros "Hrw Hro".
      iApply (swp_checked_mem_read_S_ex Drw Dro Df rsf pa pmar0 pcfg paddr
                Rr Mex Hdisj HDpma HDcfg HDaddr HDhtif Hhtif' Hpma' Hpcfg'
                Hpaddr' HA Hord HR Hcov Hpallow Hram Hpa Hnode_ex
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(%bytes & -> & Hrw & Hro & HR)". cbn beta iota.
    iApply swp_ret. iExists bytes. iSplitR; [done|].
    iExists rsf. iFrame. done.
  Qed.

  Lemma swp_vmem_read_addr_S_gen_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) (Mex : iProp Σ)
      (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    (⊢ gen_cert -∗ Mex -∗
       swp (read_ram Read_plain (Physaddr pa) width false)
         (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                     ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes)) ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mex -∗
    swp (vmem_read_addr (Virtaddr ea) width (Load Data) false false false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                ⌜r = Values.Ok bytes⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ Rr bytes).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hhtif
      Hpma Hpcfg Hpaddr HSXL Hmode Hep HA Hord HR Hcov Hpallow Hram Hva Hpa
      Hnode_ex.
    pose proof w_pos as Hw0. pose proof w_le8 as Hw8.
    iIntros "#Hcert Hfrag Hres Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read_addr.
    rewrite Hva. sm_glue.
    rewrite mbind0_ret.
    rewrite (split_on_page_boundary_aligned_w ea width Hvw Hva).
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep.
    rewrite mliftR_ret mbind_ret. sm_glue.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (translationMode Supervisor) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hmode
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbindR_ret.
    match goal with
    | |- context [ if Instances.generic_neq md Bare then ?x else ?y ] =>
        replace (if Instances.generic_neq md Bare then x else y) with x
          by (destruct (Instances.generic_neq md Bare); reflexivity)
    end.
    sm_glue.
    change (Z.gtb 0 0) with false. sm_glue.
    change (sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer
              (translate_and_read_value (Virtaddr ea) width (Load Data)
                 false false false) _ _ C HC
              with "[Hfrag Hres Hrw Hro Htr Hmem] [-]").
    { iApply (swp_translate_and_read_value_S_ex Drw Dro Df rs ea pa pmar0 pcfg
                paddr Rr Mex Rt rr Hdisj HDmst HDpriv HDpma HDcfg HDaddr
                HDhtif Hpriv Hhtif Hpma Hpcfg Hpaddr Hep HA Hord HR Hcov
                Hpallow Hram Hpa Hnode_ex
                with "Hcert Hfrag Hres Hrw Hro Htr Hmem"). }
    iIntros (v0) "(%bytes & -> & Hland)". cbn beta iota. sm_glue.
    rewrite mbind0R_ret. sm_glue.
    rewrite mbindR_ret. sm_glue.
    change (not sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite (usvd_zeros_full_gen (8 * width) bytes ltac:(lia)).
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok bytes)). iExists bytes. iFrame. done.
  Qed.

  Lemma swp_vmem_read_S_gen_ex (Drw Dro : gset register)
      (Df : register -> dfrac)
      (rs : regstate) (i : SailStdpp.Values.mword 5) (m : regfile)
      (offset pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) (Mex : iProp Σ)
      (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx i) offset in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Load Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    (⊢ gen_cert -∗ Mex -∗
       swp (read_ram Read_plain (Physaddr pa) width false)
         (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                     ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes)) ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mex -∗
    swp (vmem_read (Regidx i) offset width (Load Data) false false false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                ⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ Rr bytes).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hhtif Hpma Hpcfg Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR
      Hcov Hpallow Hram Hva Hpa Hnode_ex.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx i) offset (Load Data) width)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_S_gen Drw Dro Df rs i m offset
                (Load Data) Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hmxr Hpmm HSXL Htf with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer0
              (vmem_read_addr (Virtaddr ea) width (Load Data) false false false)
              _ C HC with "[Hfrag Hres Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_read_addr_S_gen_ex Drw Dro Df rs ea pa pmar0 pcfg paddr
                Rr Mex Rt rr md Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr
                HDhtif Hpriv Hhtif Hpma Hpcfg Hpaddr HSXL Hmode Hep HA Hord HR
                Hcov Hpallow Hram Hva Hpa Hnode_ex
                with "Hcert Hfrag Hres Hrw Hro Htr Hmem"). }
    iIntros (v0) "(%bytes & -> & Hland)".
    iApply ("Hcont" $! (Values.Ok bytes)). iExists bytes.
    iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_execute_LOAD_S_gen_ex (Drw Dro : gset register)
      (Df : register -> dfrac)
      (rs : regstate) (imm : SailStdpp.Values.mword 12)
      (rs1 rd : SailStdpp.Values.mword 5) (is_unsigned : bool)
      (m : regfile) (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) (Mex : iProp Σ)
      (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Load Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    uint rd <> 0 ->
    (⊢ gen_cert -∗ Mex -∗
       swp (read_ram Read_plain (Physaddr pa) width false)
         (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                     ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes)) ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Mex -∗
    swp (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned width)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                ∃ bytes : SailStdpp.Values.mword (8 * width),
                gpr_file (<[Regidx rd
                            := regval_into_reg (extend_value is_unsigned bytes)]> m) ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ Rr bytes).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hhtif Hpma Hpcfg Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR
      Hcov Hpallow Hram Hva Hpa Hrd Hnode_ex.
    pose proof w_le8 as Hw8.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hmem".
    unfold execute_LOAD.
    replace (Z.leb width xlen_bytes) with true
      by (change xlen_bytes with 8; symmetry; apply Z.leb_le; exact Hw8).
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. sm_glue.
    iApply (swp_bind_use _ _
              (fun r => (∃ bytes : SailStdpp.Values.mword (8 * width),
                         ⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                         ∃ rsf : regstate,
                           ⌜ rsf = rs \/
                             exists tv, rsf = register_set tlb tv rs ⌝ ∗
                           hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                           Rt rsf ∗ resv_any cpu_id ∗ Rr bytes)%I) _
              with "[Hfrag Hres Hf Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_read_S_gen_ex Drw Dro Df rs rs1 m (sign_extend' 64 imm)
                pa pmar0 pcfg paddr Rr Mex Rt rr md Hdisj HDmst HDpriv HDmenv
                HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hhtif Hpma Hpcfg
                Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR Hcov Hpallow
                Hram Hva Hpa Hnode_ex
                with "Hcert Hfrag Hres Hf Hrw Hro Htr Hmem"). }
    iIntros (v0) "(%bytes & -> & Hf & Hland)". cbn beta iota.
    iApply (swp_bind0_use (wX_bits (Regidx rd) (extend_value is_unsigned bytes))
              _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m (extend_value is_unsigned bytes) Hrd
                with "Hcert Hf"). }
    iIntros (u) "Hf". iApply swp_ret. iSplitR; [done|].
    iExists bytes. by iFrame.
  Qed.

End smem.

(* ====================================================================== *)
(* 6. THE RAM READ NODE, per width.                                        *)
(*                                                                        *)
(* [ReadReq.t n] and [bv (8*n)] are TYPE indices, so the request record and *)
(* its two projections do not reduce at a symbolic width -- the trap        *)
(* [HartMFetch]'s 2-byte twins record.  Four instances; widths 2, 4 and 8   *)
(* reuse [HartMFetch]'s records, and only width 1 is new.                   *)
(* ====================================================================== *)
Definition mread_req1 (pa : SailStdpp.Values.mword 64)
    : Interface.ReadReq.t 1 :=
  {| Interface.ReadReq.pa := pa;
     Interface.ReadReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.ReadReq.va := None;
     Interface.ReadReq.translation := tt;
     Interface.ReadReq.tag := false |}.

Local Ltac req_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size].

Lemma hread_req_at_read_ram1 (pa : SailStdpp.Values.mword 64) :
  hread_req_at 1 (read_ram Read_plain (Physaddr pa) 1 false)
  = Some (mread_req1 pa).
Proof.
  unfold read_ram, Defs.sail_mem_read. req_cbn.
  cbn [hread_req_at].
  destruct (decide (1%N = 1%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hread_resume_read_ram1 (pa : SailStdpp.Values.mword 64) (w : bv 8) :
  hread_resume (bv_unsigned w) (read_ram Read_plain (Physaddr pa) 1 false)
  = Interface.Ret (w, default_meta).
Proof.
  unfold read_ram, Defs.sail_mem_read. req_cbn.
  cbn [hread_resume].
  rewrite Z_to_bv_bv_unsigned TypeCasts.cast_N_refl.
  reflexivity.
Qed.

Section snodes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* THE S-MODE DATA READ IS THE Ztso ARM (tso-machine-flip.md §6
     amendments A6.6(a) + A6.18): [read_ram Read_plain] is [ak_strong =
     false], so what a node owes is [Mobl_ram_plain] -- a [tso_read_bytes]
     fact at EVERY view the machine's drain may choose -- and NOT a
     [read_bytes] against the flat cache.  The bundle rides in and back out
     unchanged; the rule pays the view advance itself. *)
  Local Ltac node_read req Hproj Hres :=
    iIntros "#Hcert Hmem";
    iApply (swp_hart_ram_read_plain _ req _ _ Hproj ltac:(assumption)
              ltac:(reflexivity) with "Hcert [Hmem]");
    iIntros (s ? ? ? ?) "%Htv Hs Htso";
    iMod ("Hmem" $! _ _ _ _ _ with "[//] Hs Htso") as "[Hb Hcl]";
    iModIntro; iExists _;
    iSplitR "Hcl"; [ iExact "Hb" | ];
    iNext; iMod "Hcl" as "(Hs & Htso & HR)"; iModIntro; iFrame "Hs Htso";
    iIntros (tvn ? ?) "_";
    rewrite Hres; iApply swp_ret; by iFrame.

  Lemma swp_read_ram_node1 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 1)) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           tso_read_bytes img log (hart_agent cpu_id) tv' pa 1 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 1 false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read (mread_req1 pa) (hread_req_at_read_ram1 pa)
      (hread_resume_read_ram1 pa bytes).
  Qed.

  Lemma swp_read_ram_node2 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 2)) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           tso_read_bytes img log (hart_agent cpu_id) tv' pa 2 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 2 false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read (mread_req2 pa) (hread_req_at_read_ram2 pa)
      (hread_resume_read_ram2 pa bytes).
  Qed.

  Lemma swp_read_ram_node4 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           tso_read_bytes img log (hart_agent cpu_id) tv' pa 4 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 4 false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read (mread_req pa) (hread_req_at_read_ram pa)
      (hread_resume_read_ram pa bytes).
  Qed.

  Lemma swp_read_ram_node8 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 8)) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           tso_read_bytes img log (hart_agent cpu_id) tv' pa 8 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 8 false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read (mread_req8 pa) (hread_req_at_read_ram8 pa)
      (hread_resume_read_ram8 pa bytes).
  Qed.

  (* THE SAME FOUR NODES WITH THE READ VALUE EXISTENTIAL.  A leaf whose
     target cell lives in an INVARIANT (a lock word, a device register)
     cannot name the bytes before the step -- it learns them by opening the
     invariant inside this very callback.  The node already chooses the word
     inside [swp_hart_ram_read]'s own existential, so each [_ex] form costs
     only its statement. *)
  Local Ltac node_read_ex req Hproj Hres :=
    let bs := fresh "bs" in
    iIntros "#Hcert Hmem";
    iApply (swp_hart_ram_read_plain _ req _ _ Hproj ltac:(assumption)
              ltac:(reflexivity) with "Hcert [Hmem]");
    iIntros (s ? ? ? ?) "%Htv Hs Htso";
    iMod ("Hmem" $! _ _ _ _ _ with "[//] Hs Htso") as (bs) "[Hb Hcl]";
    iModIntro; iExists bs;
    iSplitR "Hcl"; [ iExact "Hb" | ];
    iNext; iMod "Hcl" as "(Hs & Htso & HR)"; iModIntro; iFrame "Hs Htso";
    iIntros (tvn ? ?) "_";
    rewrite (Hres bs); iApply swp_ret; iExists bs; by iFrame.

  (* THE SAME FOUR NODES WITH THE VALUE *CONFINED* RATHER THAN NAMED
     (tso-m4-memo.md §6, as amended by tso-machine-flip.md A6.73's
     measurement B).

     THE DIFFERENCE FROM [_ex], AND IT IS THE WHOLE POINT: [_ex] puts its
     [∃ bytes] OUTSIDE the [∀ tv'], i.e. it names ONE word good at every
     reachable view.  That is [tso-pin-memo.md] §0's refuted shape and it
     is FALSE of any cell another hart may be writing -- which is exactly
     the racy lock-owner cell.  Here the existential moves INSIDE the [∀]
     and what the caller pins is a PREDICATE [P]; the VALUE comes back from
     the step, together with [⌜P w⌝].

     The resource [R] is deliberately NOT value-indexed: a racy leaf's
     continuation wants [⌜P c⌝ ∗ T], and a value-indexed [Rr] would have to
     be chosen before the step it is about.

     COST: only the statement.  [HartEvents.swp_hart_ram_read_plain_ex]
     (A6.51 ruling 1) is already this shape one tier down, and
     [PtTreeAdue.v:985-1006] is a worked call site of it. *)
  Local Ltac node_read_exv req Hproj Hres pr :=
    let bs := fresh "bs" in
    let tn := fresh "tn" in
    iIntros "#Hcert Hmem";
    iApply (swp_hart_ram_read_plain_ex _ req _ _ pr Hproj ltac:(assumption)
              ltac:(reflexivity) with "Hcert [Hmem]");
    iIntros (s ? ? ? ?) "%Htv Hs Htso";
    iMod ("Hmem" $! _ _ _ _ _ with "[//] Hs Htso") as "[% Hcl]";
    iModIntro; iSplitR; [ iPureIntro; assumption | ];
    iNext; iMod "Hcl" as "(Hs & Htso & HR)"; iModIntro; iFrame "Hs Htso";
    iIntros (tn bs) "_ _ _ % _";
    rewrite (Hres bs); iApply swp_ret; iExists bs;
    iSplitR; [ done | iSplitR; [ iPureIntro; assumption | iExact "HR" ] ].

  Lemma swp_read_ram_node1_exv (pa : SailStdpp.Values.mword 64)
      (P : SailStdpp.Values.mword (8 * 1) -> Prop) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           exists bytes : SailStdpp.Values.mword (8 * 1),
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 1 bytes
             /\ P bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 1 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 1),
                  ⌜r = (bytes, default_meta)⌝ ∗ ⌜P bytes⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read_exv (mread_req1 pa) (hread_req_at_read_ram1 pa)
      (hread_resume_read_ram1 pa) P.
  Qed.

  Lemma swp_read_ram_node2_exv (pa : SailStdpp.Values.mword 64)
      (P : SailStdpp.Values.mword (8 * 2) -> Prop) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           exists bytes : SailStdpp.Values.mword (8 * 2),
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 2 bytes
             /\ P bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 2 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 2),
                  ⌜r = (bytes, default_meta)⌝ ∗ ⌜P bytes⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read_exv (mread_req2 pa) (hread_req_at_read_ram2 pa)
      (hread_resume_read_ram2 pa) P.
  Qed.

  Lemma swp_read_ram_node4_exv (pa : SailStdpp.Values.mword 64)
      (P : SailStdpp.Values.mword (8 * 4) -> Prop) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           exists bytes : SailStdpp.Values.mword (8 * 4),
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 4 bytes
             /\ P bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 4 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 4),
                  ⌜r = (bytes, default_meta)⌝ ∗ ⌜P bytes⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read_exv (mread_req pa) (hread_req_at_read_ram pa)
      (hread_resume_read_ram pa) P.
  Qed.

  Lemma swp_read_ram_node8_exv (pa : SailStdpp.Values.mword 64)
      (P : SailStdpp.Values.mword (8 * 8) -> Prop) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           exists bytes : SailStdpp.Values.mword (8 * 8),
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 8 bytes
             /\ P bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 8 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 8),
                  ⌜r = (bytes, default_meta)⌝ ∗ ⌜P bytes⌝ ∗ R).
  Proof.
    intro Hdev.
    node_read_exv (mread_req8 pa) (hread_req_at_read_ram8 pa)
      (hread_resume_read_ram8 pa) P.
  Qed.

  Lemma swp_read_ram_node1_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 1) -> iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 1),
          ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 1 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗
               tso_interp_of riscv_eraGS img σ.(mem) log V ∗ Rr bytes)) -∗
    swp (read_ram Read_plain (Physaddr pa) 1 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 1),
                  ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes).
  Proof.
    intro Hdev.
    node_read_ex (mread_req1 pa) (hread_req_at_read_ram1 pa)
      (hread_resume_read_ram1 pa).
  Qed.

  Lemma swp_read_ram_node2_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 2) -> iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 2),
          ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 2 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗
               tso_interp_of riscv_eraGS img σ.(mem) log V ∗ Rr bytes)) -∗
    swp (read_ram Read_plain (Physaddr pa) 2 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 2),
                  ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes).
  Proof.
    intro Hdev.
    node_read_ex (mread_req2 pa) (hread_req_at_read_ram2 pa)
      (hread_resume_read_ram2 pa).
  Qed.

  Lemma swp_read_ram_node4_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 4) -> iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 4),
          ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 4 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗
               tso_interp_of riscv_eraGS img σ.(mem) log V ∗ Rr bytes)) -∗
    swp (read_ram Read_plain (Physaddr pa) 4 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 4),
                  ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes).
  Proof.
    intro Hdev.
    node_read_ex (mread_req pa) (hread_req_at_read_ram pa)
      (hread_resume_read_ram pa).
  Qed.

  Lemma swp_read_ram_node8_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 8) -> iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 8),
          ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
             tso_read_bytes img log (hart_agent cpu_id) tv' pa 8 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗
               tso_interp_of riscv_eraGS img σ.(mem) log V ∗ Rr bytes)) -∗
    swp (read_ram Read_plain (Physaddr pa) 8 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 8),
                  ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes).
  Proof.
    intro Hdev.
    node_read_ex (mread_req8 pa) (hread_req_at_read_ram8 pa)
      (hread_resume_read_ram8 pa).
  Qed.

End snodes.

(* ====================================================================== *)
(* 7. THE STORE CHAIN.                                                     *)
(*                                                                        *)
(* [HartMStore]'s chain one privilege over, with the same two structural    *)
(* changes as the load side: the translation is an obligation (so the       *)
(* [mem_write_ea] / [mem_write_value] pair runs at the landing file), and   *)
(* the PMP check is the kernel's TOR entry 0 at Supervisor.  The write      *)
(* NODE is per-width for the reason the read node is.                      *)
(* ====================================================================== *)
Section smem_w.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Variable width : Z.
  Hypothesis Hvw : vmem_width width.
  Hypothesis Hdvd : (width | 4096).
  Hypothesis Huintw : uint (to_bits 64 width) = width.

  Local Lemma ww_pos : 0 < width.
  Proof. exact (vmem_width_pos width Hvw). Qed.
  Local Lemma ww_le8 : width <= 8.
  Proof. exact (vmem_width_le width Hvw). Qed.

  (* the store side's copy of the load section's address-class parameters *)
  Variable Acls : SailStdpp.Values.mword 64 -> Prop.
  Variable Pma : list PMA_Region -> Prop.

  Hypothesis Hpma_store :
    forall (D Drw : gset register) (rs : regstate)
           (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region),
      (pma_regions : register) ∈ D ->
      register_lookup pma_regions rs = pmar0 ->
      Pma pmar0 -> Acls pa ->
      is_aligned_paddr (Physaddr pa) width = true ->
      hfrun 6 D Drw rs
        (check_pma_with_pmp_priority (Store Data) PBMT_PMA Supervisor
           (Physaddr pa) width false)
      = Some (Values.Ok
                {| Phys_Mem_Access_Info_splittable := CannotSplit;
                   Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).

  Hypothesis Hmmio_w :
    forall (D Drw : gset register) (rs : regstate)
           (pa : SailStdpp.Values.mword 64),
      (htif_tohost_base : register) ∈ D ->
      register_lookup htif_tohost_base rs = None ->
      Acls pa ->
      hfrun 12 D Drw rs (within_mmio_writable (Physaddr pa) width)
      = Some (false, rs).

  Hypothesis Hpmprange :
    forall (pa paddr0 : SailStdpp.Values.mword 64),
      Acls pa -> is_aligned_paddr (Physaddr pa) width = true ->
      (ram_base + ram_size <= uint paddr0 * 4)%Z ->
      pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint paddr0) 4) (uint pa) (uint (to_bits 64 width))
      = PMP_Match.

  (* the store side's abstract memory obligation (see the load section) *)
  Variable Wobl : SailStdpp.Values.mword 64 ->
                  SailStdpp.Values.mword (8 * width) -> iProp Σ -> iProp Σ.

  Hypothesis Hwrite_node :
    forall (pa : SailStdpp.Values.mword 64)
           (v : SailStdpp.Values.mword (8 * width)) (R : iProp Σ)
           (rr : option resv),
      Acls pa ->
      gen_cert -∗
      resv_frag cpu_id rr -∗
      Wobl pa v R -∗
      swp (write_ram Write_plain (Physaddr pa) width v tt)
        (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).

  (* the PMP/PMA premise bundle every store node repeats *)
  Local Ltac wpmp HW := unfold pmpCheckRWX; cbn match; rewrite HW; reflexivity.

  Lemma swp_mem_write_ea_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA
           false false false)
      (fun r => ⌜r = Values.Ok tt⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDaddr Hpriv Hpma Hpcfg Hpaddr
      Hep HA Hord HW Hcov Hpallow Hram Hpa.
    pose proof ww_pos as Hw0. pose proof ww_le8 as Hw8.
    pose proof (Hpmprange pa (vec_access_dec paddr 0) Hram Hpa Hcov) as Hrange.
    iIntros "#Hcert Hrw Hro".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold mem_write_ea.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep.
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Store Data) PBMT_PMA Supervisor
                 (Physaddr pa) width false) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (Hpma_store (Drw ∪ Dro) Drw rs pa pmar0
                   HDpma Hpma Hpallow Hram Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbindR_ret. sm_glue.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing write_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    sm_glue.
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    rewrite mliftR_ret mbind_ret. sm_glue.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. sm_glue.
    replace (0 * width)%Z with 0%Z by lia. rewrite avi0.
    iApply (swp_use_cer3 (pmpCheck (Physaddr pa) width (Store Data) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (Store Data) Drw Dro Df rs pcfg paddr
                pa width Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(wpmp HW) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbind0R_ret. sm_glue.
    change (0 =? 1 - 1) with true. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok tt)). by iFrame.
  Qed.

  Lemma swp_checked_mem_write_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * width))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Wobl pa v R -∗
    swp (checked_mem_write (Physaddr pa) width v (Store Data) PBMT_PMA
           Supervisor tt false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                resv_frag cpu_id None).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hpma Hpcfg Hpaddr Hhtif
      HA Hord HW Hcov Hpallow Hram Hpa.
    pose proof ww_pos as Hw0. pose proof ww_le8 as Hw8.
    pose proof (Hpmprange pa (vec_access_dec paddr 0) Hram Hpa Hcov) as Hrange.
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_write.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Store Data) PBMT_PMA Supervisor
                 (Physaddr pa) width false) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (Hpma_store (Drw ∪ Dro) Drw rs pa pmar0
                   HDpma Hpma Hpallow Hram Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbindR_ret. sm_glue.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing write_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    sm_glue.
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    rewrite mliftR_ret mbind_ret. sm_glue.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. sm_glue.
    replace (0 * width)%Z with 0%Z by lia. rewrite avi0.
    iApply (swp_use_cer3 (pmpCheck (Physaddr pa) width (Store Data) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (Store Data) Drw Dro Df rs pcfg paddr
                pa width Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(wpmp HW) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbind0R_ret.
    iApply (swp_use_cer3 (within_mmio_writable (Physaddr pa) width)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (Hmmio_w (Drw ∪ Dro) Drw rs pa HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    change (autocast (T := mword)
              (subrange_vec_dec v (8 * (0 + 1) * width - 1) (8 * 0 * width))
            : mword (8 * width))
      with (autocast (T := mword) (subrange_vec_dec v (8 * width - 1) 0)
            : mword (8 * width)).
    rewrite (subrange_full_gen_cast (8 * width) v ltac:(lia)).
    iApply (swp_use_cer4 (write_ram Write_plain (Physaddr pa) width v tt)
              (fun r => (⌜r = true⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                         resv_frag cpu_id None)%I)
              _ _ _ _ C HC with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_mono (write_ram Write_plain (Physaddr pa) width v tt)
                (fun r => (⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None)%I)
                with "[Hrw Hro] [Hmem Hfrag]").
      - iIntros (r) "(-> & HR & Hfrag)". by iFrame.
      - iApply (Hwrite_node pa v R rr Hram with "Hcert Hfrag Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". sm_glue.
    change (0 =? 1 - 1) with true. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). by iFrame.
  Qed.

  Lemma swp_mem_write_value_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * width))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Wobl pa v R -∗
    swp (mem_write_value (Physaddr pa) width v (Store Data) PBMT_PMA
           false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                resv_frag cpu_id None).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv Hpma Hpcfg
      Hpaddr Hhtif Hep HA Hord HW Hcov Hpallow Hram Hpa.
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    unfold mem_write_value, mem_write_value_meta.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep. rewrite mbind_ret.
    unfold mem_write_value_priv_meta.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                         resv_frag cpu_id None)%I) _
              with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_checked_mem_write_S Drw Dro Df rs pa v pmar0 pcfg paddr R rr
                Hdisj HDpma HDcfg HDaddr HDhtif Hpma Hpcfg Hpaddr Hhtif
                HA Hord HW Hcov Hpallow Hram Hpa
                with "Hcert Hfrag Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". sm_glue.
    iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [vmem_write_addr] at Supervisor -- WHERE THE TRANSLATION ENTERS on    *)
  (* the store side.  Unlike the load, the model calls [translateAddr]      *)
  (* here DIRECTLY (there is no [translate_and_write_value] on the          *)
  (* non-straddling path), so this is the one obligation site and both      *)
  (* [mem_write_ea] and [mem_write_value] run at the landing file.          *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_vmem_write_addr_S_gen (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * width))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Store Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Wobl pa v R -∗
    swp (vmem_write_addr (Virtaddr ea) width v (Store Data) false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hpma
      Hpcfg Hpaddr Hhtif HSXL Hmode Hep HA Hord HW Hcov Hpallow Hram Hva Hpa.
    pose proof ww_pos as Hw0. pose proof ww_le8 as Hw8.
    iIntros "#Hcert Hfrag Hres Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_write_addr.
    rewrite Hva. sm_glue.
    rewrite mbind0_ret.
    rewrite (split_on_page_boundary_aligned_w ea width Hvw Hva).
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep.
    rewrite mliftR_ret mbind_ret. sm_glue.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (translationMode Supervisor) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hmode
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    (* THE ONE BRANCH THE MODE DECIDES, and both arms reach the same value:
       at [md <> Bare] the second conjunct is evaluated and is [false]; at
       [Bare] the [and_boolM] short-circuits to [false] outright. *)
    (* THE ONE BRANCH THE TRANSLATION MODE DECIDES, COLLAPSED BEFORE IT
       SPLITS THE PROOF.  The page-split conjunct is [next_page_bytes > 0]
       and the address is aligned, so the second conjunct is [0 >? 0] --
       [false] -- and [and_boolM] returns [false] whatever the mode is.
       Collapsing it here (rather than [destruct]ing the mode) is what keeps
       this walk ONE goal and the engines regime-generic: a leaf holding only
       [sr_inv R] cannot say which mode its regime installs. *)
    rewrite mbindR_ret.
    match goal with
    | |- context [ if Instances.generic_neq md Bare then ?x else ?y ] =>
        replace (if Instances.generic_neq md Bare then x else y) with x
          by (destruct (Instances.generic_neq md Bare); reflexivity)
    end.
    sm_glue.
    change (Z.gtb 0 0) with false. sm_glue.
    change (sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer (translateAddr (Virtaddr ea) (Store Data)) _ _ C HC
              with "[Hfrag Hres Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hfrag Hres Hrw Hro"). }
    iIntros (v0) "(-> & Hland)". sm_glue.
    iDestruct "Hland" as (rsf) "(%Hland & Hrw & Hro & Hres & Hany)".
    iDestruct "Hany" as (rr') "Hfrag".
    assert (Hpriv' : register_lookup cur_privilege rsf = Supervisor)
      by (rewrite (sland_lookup rs rsf Hland cur_privilege eq_refl); exact Hpriv).
    assert (Hmst' : register_lookup mstatus rsf = register_lookup mstatus rs)
      by (apply (sland_lookup rs rsf Hland mstatus eq_refl)).
    assert (Hhtif' : register_lookup htif_tohost_base rsf = None)
      by (rewrite (sland_lookup rs rsf Hland htif_tohost_base eq_refl); exact Hhtif).
    assert (Hpma' : register_lookup pma_regions rsf = pmar0)
      by (rewrite (sland_lookup rs rsf Hland pma_regions eq_refl); exact Hpma).
    assert (Hpcfg' : register_lookup pmpcfg_n rsf = pcfg)
      by (rewrite (sland_lookup rs rsf Hland pmpcfg_n eq_refl); exact Hpcfg).
    assert (Hpaddr' : register_lookup pmpaddr_n rsf = paddr)
      by (rewrite (sland_lookup rs rsf Hland pmpaddr_n eq_refl); exact Hpaddr).
    change (Bool.eqb false (is_store_conditional (Store Data))) with true.
    cbn beta iota zeta delta [Defs.assert_exp].
    rewrite /returnM mliftR_ret mbind0_ret. sm_glue.
    iApply (swp_use_cer2
              (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA
                 false false false) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_mem_write_ea_S Drw Dro Df rsf pa pmar0 pcfg paddr Hdisj
                HDmst HDpriv HDpma HDcfg HDaddr Hpriv' Hpma' Hpcfg' Hpaddr'
                ltac:(rewrite Hmst'; exact Hep) HA Hord HW Hcov Hpallow Hram
                Hpa with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite (subrange_full_gen_cast (8 * width) v ltac:(lia)).
    iApply (swp_use_cer2
              (mem_write_value (Physaddr pa) width v (Store Data) PBMT_PMA
                 false false false) _ _ _ C HC with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_mem_write_value_S Drw Dro Df rsf pa v pmar0 pcfg paddr R rr'
                Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv' Hpma'
                Hpcfg' Hpaddr' Hhtif' ltac:(rewrite Hmst'; exact Hep)
                HA Hord HW Hcov Hpallow Hram Hpa
                with "Hcert Hfrag Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". sm_glue.
    rewrite mbindR_ret. sm_glue.
    change (not sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). iSplitR; [done|].
    iExists rsf. iFrame. done.
  Qed.

  Lemma swp_vmem_write_S_gen (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (i : SailStdpp.Values.mword 5) (m : regfile)
      (offset pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * width))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx i) offset in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Store Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Store Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Wobl pa v R -∗
    swp (vmem_write (Regidx i) offset width v (Store Data) false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗ gpr_file m ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HW
      Hcov Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_write.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx i) offset (Store Data) width)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_S_gen width Drw Dro Df rs i m
                offset (Store Data) Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hmxr Hpmm HSXL Htf with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer0
              (vmem_write_addr (Virtaddr ea) width v (Store Data)
                 false false false) _ C HC
              with "[Hfrag Hres Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_write_addr_S_gen Drw Dro Df rs ea pa v pmar0 pcfg paddr
                R Rt rr md Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr HDhtif
                Hpriv Hpma Hpcfg Hpaddr Hhtif HSXL Hmode Hep HA Hord HW Hcov
                Hpallow Hram Hva Hpa with "Hcert Hfrag Hres Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hland)".
    iApply ("Hcont" $! (Values.Ok true)). iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_execute_STORE_S_gen (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (imm : SailStdpp.Values.mword 12)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * width))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    (* the stored word: the model truncates the source GPR to the width *)
    autocast (T := mword)
      (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul width 8) 1) 0) = v ->
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Store Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    Pma pmar0 ->
    Acls pa ->
    is_aligned_vaddr (Virtaddr ea) width = true ->
    is_aligned_paddr (Physaddr pa) width = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Store Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    Wobl pa v R -∗
    swp (execute_STORE imm (Regidx rs2) (Regidx rs1) width)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros ea Hdata Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr
      HDhtif Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL Htf Hmode Hep HA Hord
      HW Hcov Hpallow Hram Hva Hpa.
    pose proof ww_le8 as Hw8.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hmem".
    unfold execute_STORE.
    replace (Z.leb width xlen_bytes) with true
      by (change xlen_bytes with 8; symmetry; apply Z.leb_le; exact Hw8).
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. sm_glue.
    iApply (swp_bind_use (rX_bits (Regidx rs2)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (v0) "(-> & Hf)". sm_glue.
    rewrite Hdata.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗ gpr_file m ∗
                         ∃ rsf : regstate,
                           ⌜ rsf = rs \/
                             exists tv, rsf = register_set tlb tv rs ⌝ ∗
                           hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                           Rt rsf ∗ R ∗ resv_frag cpu_id None)%I) _
              with "[Hfrag Hres Hf Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_write_S_gen Drw Dro Df rs rs1 m (sign_extend' 64 imm) pa
                v pmar0 pcfg paddr R Rt rr md Hdisj HDmst HDpriv HDmenv HDsatp
                HDpma HDcfg HDaddr HDhtif Hpriv Hpma Hpcfg Hpaddr Hhtif
                Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HW Hcov Hpallow Hram Hva
                Hpa with "Hcert Hfrag Hres Hf Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hf & Hland)". cbn beta iota.
    iApply swp_ret. by iFrame.
  Qed.

End smem_w.

(* ====================================================================== *)
(* 8. THE RAM WRITE NODE, per width.                                       *)
(* ====================================================================== *)
Definition mwrite_req1 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 8) : Interface.WriteReq.t 1 :=
  {| Interface.WriteReq.pa := pa;
     Interface.WriteReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.WriteReq.value :=
       TypeCasts.cast_N v (Defs.sail_mem_write_subproof 1);
     Interface.WriteReq.va := None;
     Interface.WriteReq.translation := tt;
     Interface.WriteReq.tag := None |}.

Definition mwrite_req2 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 16) : Interface.WriteReq.t 2 :=
  {| Interface.WriteReq.pa := pa;
     Interface.WriteReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.WriteReq.value :=
       TypeCasts.cast_N v (Defs.sail_mem_write_subproof 2);
     Interface.WriteReq.va := None;
     Interface.WriteReq.translation := tt;
     Interface.WriteReq.tag := None |}.

Local Ltac wreq_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Z.to_N bits_of_physaddr
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value].

Lemma hwrite_req_at_write_ram1 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 8) :
  hwrite_req_at 1 (write_ram Write_plain (Physaddr pa) 1 v tt)
  = Some (mwrite_req1 pa v).
Proof.
  unfold write_ram, Defs.sail_mem_write. wreq_cbn.
  cbn [hwrite_req_at].
  destruct (decide (1%N = 1%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hwrite_resume_write_ram1 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 8) :
  hwrite_resume (write_ram Write_plain (Physaddr pa) 1 v tt)
  = Interface.Ret true.
Proof.
  unfold write_ram, Defs.sail_mem_write. wreq_cbn.
  cbn [hwrite_resume]. reflexivity.
Qed.

Lemma hwrite_req_at_write_ram2 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 16) :
  hwrite_req_at 2 (write_ram Write_plain (Physaddr pa) 2 v tt)
  = Some (mwrite_req2 pa v).
Proof.
  unfold write_ram, Defs.sail_mem_write. wreq_cbn.
  cbn [hwrite_req_at].
  destruct (decide (2%N = 2%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hwrite_resume_write_ram2 (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 16) :
  hwrite_resume (write_ram Write_plain (Physaddr pa) 2 v tt)
  = Interface.Ret true.
Proof.
  unfold write_ram, Defs.sail_mem_write. wreq_cbn.
  cbn [hwrite_resume]. reflexivity.
Qed.

(* the request's VALUE is the word behind an [m = m] cast *)
Lemma mwrite_req1_value (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 8) :
  Interface.WriteReq.value (mwrite_req1 pa v) = v.
Proof. cbn [mwrite_req1 Interface.WriteReq.value]. apply TypeCasts.cast_N_refl. Qed.

Lemma mwrite_req2_value (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 16) :
  Interface.WriteReq.value (mwrite_req2 pa v) = v.
Proof. cbn [mwrite_req2 Interface.WriteReq.value]. apply TypeCasts.cast_N_refl. Qed.

Lemma mwrite_req4_value (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) :
  Interface.WriteReq.value (mwrite_req pa v) = v.
Proof. cbn [mwrite_req Interface.WriteReq.value]. apply TypeCasts.cast_N_refl. Qed.

Lemma mwrite_req8_value (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 64) :
  Interface.WriteReq.value (mwrite_req8 pa v) = v.
Proof. cbn [mwrite_req8 Interface.WriteReq.value]. apply TypeCasts.cast_N_refl. Qed.

Section swnodes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* THE S-MODE DATA STORE OWES THE APPEND (§6's [Wobl_ram], A6.16): the
     flat update AND one authored message, at the SAME view -- a plain store
     is buffered, so [wstore_tv] is the identity here and the receipt the
     rule hands back is dropped (it says nothing its holder did not already
     have).  [HartMStore.wobl_ram_ctx] is the M-mode twin of what pays it. *)
  Local Ltac node_write req Hproj Hval Hres :=
    let Hcl := fresh in
    iIntros "#Hcert Hfrag Hmem";
    iApply (swp_hart_ram_write _ req _ _ _ Hproj ltac:(assumption)
              with "Hcert Hfrag [Hmem]");
    iIntros (s ? ? ? ?) "%Htv Hs Htso";
    iMod ("Hmem" $! _ _ _ _ _ with "[//] Hs Htso") as "Hcl";
    iModIntro; iNext; iMod "Hcl" as "(Hs & Htso & HR)"; iModIntro;
    rewrite Hval; iFrame "Hs Htso"; iIntros "Hfrag _";
    rewrite Hres; iApply swp_ret; by iFrame.

  Lemma swp_write_ram_node1 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 1)) (R : iProp Σ) (rr : option resv) :
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa (Z.to_N 1) v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img
               (write_bytes σ.(mem) pa (Z.to_N 1) v)
               (log ++ [PWMsg (snap_of pa (Z.to_N 1) v)
                          (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) tv
                  (log ++ [PWMsg (snap_of pa (Z.to_N 1) v)
                             (hart_agent cpu_id)])%list V) ∗ R)) -∗
    swp (write_ram Write_plain (Physaddr pa) 1 v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intro Hdev.
    node_write (mwrite_req1 pa v) (hwrite_req_at_write_ram1 pa v)
      (mwrite_req1_value pa v) (hwrite_resume_write_ram1 pa v).
  Qed.

  Lemma swp_write_ram_node2 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 2)) (R : iProp Σ) (rr : option resv) :
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa (Z.to_N 2) v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img
               (write_bytes σ.(mem) pa (Z.to_N 2) v)
               (log ++ [PWMsg (snap_of pa (Z.to_N 2) v)
                          (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) tv
                  (log ++ [PWMsg (snap_of pa (Z.to_N 2) v)
                             (hart_agent cpu_id)])%list V) ∗ R)) -∗
    swp (write_ram Write_plain (Physaddr pa) 2 v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intro Hdev.
    node_write (mwrite_req2 pa v) (hwrite_req_at_write_ram2 pa v)
      (mwrite_req2_value pa v) (hwrite_resume_write_ram2 pa v).
  Qed.

  Lemma swp_write_ram_node4 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) (rr : option resv) :
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa (Z.to_N 4) v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img
               (write_bytes σ.(mem) pa (Z.to_N 4) v)
               (log ++ [PWMsg (snap_of pa (Z.to_N 4) v)
                          (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) tv
                  (log ++ [PWMsg (snap_of pa (Z.to_N 4) v)
                             (hart_agent cpu_id)])%list V) ∗ R)) -∗
    swp (write_ram Write_plain (Physaddr pa) 4 v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intro Hdev.
    node_write (mwrite_req pa v) (hwrite_req_at_write_ram pa v)
      (mwrite_req4_value pa v) (hwrite_resume_write_ram pa v).
  Qed.

  Lemma swp_write_ram_node8 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 8)) (R : iProp Σ) (rr : option resv) :
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa (Z.to_N 8) v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img
               (write_bytes σ.(mem) pa (Z.to_N 8) v)
               (log ++ [PWMsg (snap_of pa (Z.to_N 8) v)
                          (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) tv
                  (log ++ [PWMsg (snap_of pa (Z.to_N 8) v)
                             (hart_agent cpu_id)])%list V) ∗ R)) -∗
    swp (write_ram Write_plain (Physaddr pa) 8 v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intro Hdev.
    node_write (mwrite_req8 pa v) (hwrite_req_at_write_ram8 pa v)
      (mwrite_req8_value pa v) (hwrite_resume_write_ram8 pa v).
  Qed.

End swnodes.

(* ====================================================================== *)
(* 9. THE TWO ADDRESS CLASSES.                                             *)
(*                                                                        *)
(* Each is five facts: the PMA walk at a load, the PMA walk at a store,     *)
(* the [within_mmio_readable]/[_writable] answer, and the PMP range match.  *)
(* Instantiating the sections above with one of them and the matching node  *)
(* gives the engine for that class; nothing else differs.                   *)
(* ====================================================================== *)

(* ---- the RAM class ---- *)
Section ram_class.
  Variable width : Z.
  Hypothesis Hvw : vmem_width width.
  Hypothesis Hdvd : (width | 4096).
  Hypothesis Huintw : uint (to_bits 64 width) = width.

  Lemma ram_pma_load (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
    (pma_regions : register) ∈ D ->
    register_lookup pma_regions rs = pmar0 ->
    pma_allows_ram pmar0 -> addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    hfrun 6 D Drw rs
      (check_pma_with_pmp_priority (Load Data) PBMT_PMA Supervisor
         (Physaddr pa) width false)
    = Some (Values.Ok
              {| Phys_Mem_Access_Info_splittable := CannotSplit;
                 Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
  Proof.
    pose proof (vmem_width_pos width Hvw) as Hw0.
    pose proof (vmem_width_le width Hvw) as Hw8.
    exact (hfrun_check_pma_load_S D Drw rs pa pmar0 width Hw0
             ltac:(lia) Hdvd).
  Qed.

  Lemma ram_pma_store (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
    (pma_regions : register) ∈ D ->
    register_lookup pma_regions rs = pmar0 ->
    pma_allows_ram pmar0 -> addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    hfrun 6 D Drw rs
      (check_pma_with_pmp_priority (Store Data) PBMT_PMA Supervisor
         (Physaddr pa) width false)
    = Some (Values.Ok
              {| Phys_Mem_Access_Info_splittable := CannotSplit;
                 Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
  Proof.
    pose proof (vmem_width_pos width Hvw) as Hw0.
    pose proof (vmem_width_le width Hvw) as Hw8.
    exact (hfrun_check_pma_store_S D Drw rs pa pmar0 width Hw0
             ltac:(lia) Hdvd).
  Qed.

  Lemma ram_mmio_r (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) :
    (htif_tohost_base : register) ∈ D ->
    register_lookup htif_tohost_base rs = None ->
    addr_is_ram pa ->
    hfrun 12 D Drw rs (within_mmio_readable (Physaddr pa) width)
    = Some (false, rs).
  Proof.
    pose proof (vmem_width_pos width Hvw) as Hw0.
    exact (hfrun_within_mmio_ram D Drw rs pa width ltac:(lia)).
  Qed.

  Lemma ram_mmio_w (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) :
    (htif_tohost_base : register) ∈ D ->
    register_lookup htif_tohost_base rs = None ->
    addr_is_ram pa ->
    hfrun 12 D Drw rs (within_mmio_writable (Physaddr pa) width)
    = Some (false, rs).
  Proof.
    pose proof (vmem_width_pos width Hvw) as Hw0.
    exact (hfrun_within_mmio_w_ram D Drw rs pa width ltac:(lia)).
  Qed.

  Lemma ram_pmprange (pa paddr0 : SailStdpp.Values.mword 64) :
    addr_is_ram pa -> is_aligned_paddr (Physaddr pa) width = true ->
    (ram_base + ram_size <= uint paddr0 * 4)%Z ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint paddr0) 4) (uint pa) (uint (to_bits 64 width))
    = PMP_Match.
  Proof.
    intros Hram Hpa Hcov.
    pose proof (vmem_width_pos width Hvw) as Hw0.
    pose proof (vmem_width_le width Hvw) as Hw8.
    pose proof (pma_ram_access_w pa width Hw0 ltac:(lia) Hdvd Hram Hpa) as Hacc.
    apply (ram_pmp_match_w pa paddr0 width Hw0 Huintw);
      [ exact (proj1 Hram) | exact (proj2 (proj2 Hacc)) | exact Hcov ].
  Qed.
End ram_class.

(* ---- the DEVICE class: the UART / PLIC / virtio-mmio band. ---- *)
(* [dev_addr] is "below DRAM", which includes the CLINT, and a CLINT access
   is served by [mmio_read]/[mmio_write] rather than by the device thread --
   so the class explicitly excludes it.  [pma_io_access] pins the band, and
   with it the PMP range (the whole band is below [ram_base]). *)
Definition dev_cls (width : Z) (pa : SailStdpp.Values.mword 64) : Prop :=
  dev_addr pa = true /\ not_in_clint pa /\ pma_io_access pa width.

Lemma hfrun_check_pma_load_io (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) (width : Z) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_io pmar0 ->
  pma_io_access pa width ->
  is_aligned_paddr (Physaddr pa) width = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Load Data) PBMT_PMA Supervisor
       (Physaddr pa) width false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hacc Hpa.
  unfold check_pma_with_pmp_priority. sm_cbn.
  sm_read. rewrite Hpma. sm_cbn.
  destruct (Hpallow pa width Hacc) as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (Hx & _).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. sm_cbn.
  rewrite Hx. sm_cbn.
  rewrite Hpa. sm_cbn.
  apply hfrun_ret.
Qed.

Lemma hfrun_check_pma_store_io (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) (width : Z) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_io pmar0 ->
  pma_io_access pa width ->
  is_aligned_paddr (Physaddr pa) width = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Store Data) PBMT_PMA Supervisor
       (Physaddr pa) width false)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hacc Hpa.
  unfold check_pma_with_pmp_priority. sm_cbn.
  sm_read. rewrite Hpma. sm_cbn.
  destruct (Hpallow pa width Hacc) as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & Hx).
  cbn [PMA_Region_attributes] in Hx.
  rewrite Hmatch. sm_cbn.
  rewrite Hx. sm_cbn.
  rewrite Hpa. sm_cbn.
  apply hfrun_ret.
Qed.

Local Lemma clint_false_dev (a : SailStdpp.Values.mword 64) (n : Z) :
  0 < n -> not_in_clint a ->
  andb (Z.leb (uint plat_clint_base) (uint a))
       (Z.leb (Z.add (uint a) (__id n))
              (Z.add (uint plat_clint_base) (uint plat_clint_size)))
  = false.
Proof.
  intros Hn Hnc. unfold __id.
  destruct Hnc as [H|H];
    [ apply andb_false_intro1 | apply andb_false_intro2 ];
    apply Z.leb_gt; lia.
Qed.

Local Ltac dmr_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Riscv.rv64d_types.returnR
     Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not
     within_clint within_sig within_htif_readable within_htif_writable
     __id get_config_rvfi plat_have_clint plat_have_sig].

Lemma hfrun_within_mmio_dev_r (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (n : Z) :
  0 < n ->
  (htif_tohost_base : register) ∈ D ->
  register_lookup htif_tohost_base rs = None ->
  not_in_clint pa ->
  hfrun 12 D Drw rs (within_mmio_readable (Physaddr pa) n) = Some (false, rs).
Proof.
  intros Hn HD Hhtif Hnc.
  unfold within_mmio_readable. dmr_cbn.
  rewrite (clint_false_dev pa n Hn Hnc). dmr_cbn.
  sm_read. rewrite Hhtif. dmr_cbn.
  apply hfrun_ret.
Qed.

Lemma hfrun_within_mmio_dev_w (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (n : Z) :
  0 < n ->
  (htif_tohost_base : register) ∈ D ->
  register_lookup htif_tohost_base rs = None ->
  not_in_clint pa ->
  hfrun 12 D Drw rs (within_mmio_writable (Physaddr pa) n) = Some (false, rs).
Proof.
  intros Hn HD Hhtif Hnc.
  unfold within_mmio_writable. dmr_cbn.
  rewrite (clint_false_dev pa n Hn Hnc). dmr_cbn.
  sm_read. rewrite Hhtif. dmr_cbn.
  apply hfrun_ret.
Qed.

Section dev_class.
  Variable width : Z.
  Hypothesis Hvw : vmem_width width.
  Hypothesis Huintw : uint (to_bits 64 width) = width.

  Lemma dev_pma_load (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
    (pma_regions : register) ∈ D ->
    register_lookup pma_regions rs = pmar0 ->
    pma_allows_io pmar0 -> dev_cls width pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    hfrun 6 D Drw rs
      (check_pma_with_pmp_priority (Load Data) PBMT_PMA Supervisor
         (Physaddr pa) width false)
    = Some (Values.Ok
              {| Phys_Mem_Access_Info_splittable := CannotSplit;
                 Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
  Proof.
    intros HD Hpma Hpallow (Hdev & Hnc & Hacc) Hpa.
    exact (hfrun_check_pma_load_io D Drw rs pa pmar0 width HD Hpma Hpallow
             Hacc Hpa).
  Qed.

  Lemma dev_pma_store (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
    (pma_regions : register) ∈ D ->
    register_lookup pma_regions rs = pmar0 ->
    pma_allows_io pmar0 -> dev_cls width pa ->
    is_aligned_paddr (Physaddr pa) width = true ->
    hfrun 6 D Drw rs
      (check_pma_with_pmp_priority (Store Data) PBMT_PMA Supervisor
         (Physaddr pa) width false)
    = Some (Values.Ok
              {| Phys_Mem_Access_Info_splittable := CannotSplit;
                 Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
  Proof.
    intros HD Hpma Hpallow (Hdev & Hnc & Hacc) Hpa.
    exact (hfrun_check_pma_store_io D Drw rs pa pmar0 width HD Hpma Hpallow
             Hacc Hpa).
  Qed.

  Lemma dev_mmio_r (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) :
    (htif_tohost_base : register) ∈ D ->
    register_lookup htif_tohost_base rs = None ->
    dev_cls width pa ->
    hfrun 12 D Drw rs (within_mmio_readable (Physaddr pa) width)
    = Some (false, rs).
  Proof.
    intros HD Hhtif (Hdev & Hnc & Hacc).
    exact (hfrun_within_mmio_dev_r D Drw rs pa width
             (vmem_width_pos width Hvw) HD Hhtif Hnc).
  Qed.

  Lemma dev_mmio_w (D Drw : gset register) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) :
    (htif_tohost_base : register) ∈ D ->
    register_lookup htif_tohost_base rs = None ->
    dev_cls width pa ->
    hfrun 12 D Drw rs (within_mmio_writable (Physaddr pa) width)
    = Some (false, rs).
  Proof.
    intros HD Hhtif (Hdev & Hnc & Hacc).
    exact (hfrun_within_mmio_dev_w D Drw rs pa width
             (vmem_width_pos width Hvw) HD Hhtif Hnc).
  Qed.

  Lemma dev_pmprange (pa paddr0 : SailStdpp.Values.mword 64) :
    dev_cls width pa -> is_aligned_paddr (Physaddr pa) width = true ->
    (ram_base + ram_size <= uint paddr0 * 4)%Z ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint paddr0) 4) (uint pa) (uint (to_bits 64 width))
    = PMP_Match.
  Proof.
    intros (Hdev & Hnc & Hacc) Hpa Hcov.
    pose proof (vmem_width_pos width Hvw) as Hw0.
    destruct Hacc as (Hwr & Hlo & Hhi).
    assert (Hz : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
    rewrite Hz Huintw. rewrite Z.mul_0_l.
    apply pmpRangeMatch_full;
      unfold ram_base, ram_size, mmio_base, mmio_size in *; lia.
  Qed.
End dev_class.

(* ====================================================================== *)
(* 10. THE DEVICE NODES (widths 1 and 4 -- what the MMIO leaves use).       *)
(*                                                                        *)
(* At a device address the model still calls [read_ram]/[write_ram] --      *)
(* [within_mmio_readable] is FALSE outside the CLINT -- and the MemRead /   *)
(* MemWrite outcome is serviced by the device arm of the step relation.     *)
(* So these are the same two nodes with [HartEvents.swp_hart_dev_read] /    *)
(* [_dev_write] instead of the RAM rules, and the obligation names          *)
(* [dev_read]/[dev_write] instead of [read_bytes]/[write_bytes].            *)
(* ====================================================================== *)
Section sdevnodes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma swp_dev_read_node1 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 1)) (R : iProp Σ) :
    dev_addr pa = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_read σ.(mdev) pa 1 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 1 false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).
  Proof.
    intro Hdev. iIntros "#Hcert Hmem".
    iApply (swp_hart_dev_read 1 (mread_req1 pa) _ _
              (hread_req_at_read_ram1 pa) Hdev with "Hcert [Hmem]").
    iIntros (s) "Hs". iMod ("Hmem" $! s with "Hs") as (d0) "[%Hdr Hcl]".
    iModIntro. iExists bytes, d0. iSplitR; [ done | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs".
    rewrite hread_resume_read_ram1. iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_dev_read_node4 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) :
    dev_addr pa = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_read σ.(mdev) pa 4 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R)) -∗
    swp (read_ram Read_plain (Physaddr pa) 4 false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).
  Proof.
    intro Hdev. iIntros "#Hcert Hmem".
    iApply (swp_hart_dev_read 4 (mread_req pa) _ _
              (hread_req_at_read_ram pa) Hdev with "Hcert [Hmem]").
    iIntros (s) "Hs". iMod ("Hmem" $! s with "Hs") as (d0) "[%Hdr Hcl]".
    iModIntro. iExists bytes, d0. iSplitR; [ done | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs".
    rewrite hread_resume_read_ram. iApply swp_ret. by iFrame.
  Qed.

  (* the two DEVICE read nodes with the value existential: an MMIO read's
     value comes from the device, not from a points-to, so no leaf can name
     it before the step. *)
  Lemma swp_dev_read_node1_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 1) -> iProp Σ) :
    dev_addr pa = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ (bytes : SailStdpp.Values.mword (8 * 1)) (d' : dev_state),
        ⌜dev_read σ.(mdev) pa 1 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ Rr bytes)) -∗
    swp (read_ram Read_plain (Physaddr pa) 1 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 1),
                  ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes).
  Proof.
    intro Hdev. iIntros "#Hcert Hmem".
    iApply (swp_hart_dev_read 1 (mread_req1 pa) _ _
              (hread_req_at_read_ram1 pa) Hdev with "Hcert [Hmem]").
    iIntros (s) "Hs". iMod ("Hmem" $! s with "Hs") as (bs d0) "[%Hdr Hcl]".
    iModIntro. iExists bs, d0. iSplitR; [ done | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs".
    rewrite hread_resume_read_ram1. iApply swp_ret. iExists bs. by iFrame.
  Qed.

  Lemma swp_dev_read_node4_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 4) -> iProp Σ) :
    dev_addr pa = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ (bytes : SailStdpp.Values.mword (8 * 4)) (d' : dev_state),
        ⌜dev_read σ.(mdev) pa 4 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ Rr bytes)) -∗
    swp (read_ram Read_plain (Physaddr pa) 4 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 4),
                  ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes).
  Proof.
    intro Hdev. iIntros "#Hcert Hmem".
    iApply (swp_hart_dev_read 4 (mread_req pa) _ _
              (hread_req_at_read_ram pa) Hdev with "Hcert [Hmem]").
    iIntros (s) "Hs". iMod ("Hmem" $! s with "Hs") as (bs d0) "[%Hdr Hcl]".
    iModIntro. iExists bs, d0. iSplitR; [ done | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs".
    rewrite hread_resume_read_ram. iApply swp_ret. iExists bs. by iFrame.
  Qed.

  Lemma swp_dev_write_node1 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 1)) (R : iProp Σ) (rr : option resv) :
    dev_addr pa = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_write σ.(mdev) pa 1 v = Some d'⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R)) -∗
    swp (write_ram Write_plain (Physaddr pa) 1 v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intro Hdev. iIntros "#Hcert Hfrag Hmem".
    iApply (swp_hart_dev_write 1 (mwrite_req1 pa v) _ _ rr
              (hwrite_req_at_write_ram1 pa v) Hdev
              with "Hcert Hfrag [Hmem]").
    iIntros (s) "Hs". iMod ("Hmem" $! s with "Hs") as (d0) "[%Hdw Hcl]".
    iModIntro. iExists d0. rewrite mwrite_req1_value. iSplitR; [ done | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs".
    iIntros "Hfrag". rewrite hwrite_resume_write_ram1.
    iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_dev_write_node4 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) (rr : option resv) :
    dev_addr pa = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_write σ.(mdev) pa 4 v = Some d'⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R)) -∗
    swp (write_ram Write_plain (Physaddr pa) 4 v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intro Hdev. iIntros "#Hcert Hfrag Hmem".
    iApply (swp_hart_dev_write 4 (mwrite_req pa v) _ _ rr
              (hwrite_req_at_write_ram pa v) Hdev
              with "Hcert Hfrag [Hmem]").
    iIntros (s) "Hs". iMod ("Hmem" $! s with "Hs") as (d0) "[%Hdw Hcl]".
    iModIntro. iExists d0. rewrite mwrite_req4_value. iSplitR; [ done | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs".
    iIntros "Hfrag". rewrite hwrite_resume_write_ram.
    iApply swp_ret. by iFrame.
  Qed.

End sdevnodes.

(* ====================================================================== *)
(* 11. THE ENGINES, INSTANTIATED.                                          *)
(*                                                                        *)
(* These are what a leaf applies.  Each is the generic engine at one width  *)
(* and one address class; the statement is the generic one with [Acls],     *)
(* [Pma], [Mobl]/[Wobl] and the width filled in, so it is read off          *)
(* [swp_execute_LOAD_S] / [swp_execute_STORE_S] above.                      *)
(* ====================================================================== *)
Lemma vmw1 : vmem_width 1. Proof. by left. Qed.
Lemma vmw2 : vmem_width 2. Proof. right; by left. Qed.
Lemma vmw4 : vmem_width 4. Proof. right; right; by left. Qed.
Lemma vmw8 : vmem_width 8. Proof. right; right; by right. Qed.

Lemma dvd1 : (1 | 4096)%Z. Proof. exists 4096. lia. Qed.
Lemma dvd2 : (2 | 4096)%Z. Proof. exists 2048. lia. Qed.
Lemma dvd4 : (4 | 4096)%Z. Proof. exists 1024. lia. Qed.
Lemma dvd8 : (8 | 4096)%Z. Proof. exists 512. lia. Qed.

Lemma uintw1 : uint (to_bits 64 1) = 1. Proof. vm_compute; reflexivity. Qed.
Lemma uintw2 : uint (to_bits 64 2) = 2. Proof. vm_compute; reflexivity. Qed.
Lemma uintw4 : uint (to_bits 64 4) = 4. Proof. vm_compute; reflexivity. Qed.
Lemma uintw8 : uint (to_bits 64 8) = 8. Proof. vm_compute; reflexivity. Qed.

Section instances.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the RAM obligations: the state is handed back UNCHANGED at a read and
     with exactly the written bytes at a write *)
  (* §6's [Mobl_ram_plain] at a FIXED value, at this file's Z width
     (tso-machine-flip.md A6.18).  The NAME is kept -- every engine below
     is abstract over it and every consumer names it, so the amendment is
     invisible above this line. *)
  Definition Mobl_ram (width : Z) (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * width)) (R : iProp Σ) : iProp Σ :=
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           tso_read_bytes img log (hart_agent cpu_id) tv' pa
             (Z.to_N width) bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R))%I.

  Definition Wobl_ram (width : Z) (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * width)) (R : iProp Σ) : iProp Σ :=
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa (Z.to_N width) v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img
               (write_bytes σ.(mem) pa (Z.to_N width) v)
               (log ++ [PWMsg (snap_of pa (Z.to_N width) v)
                          (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) tv
                  (log ++ [PWMsg (snap_of pa (Z.to_N width) v)
                             (hart_agent cpu_id)])%list V) ∗ R))%I.

  (* the DEVICE obligations: the DEVICE state advances, and the value read is
     the one the device answered *)
  Definition Mobl_dev1 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 1)) (R : iProp Σ) : iProp Σ :=
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_read σ.(mdev) pa 1 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R))%I.

  Definition Mobl_dev4 (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) : iProp Σ :=
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_read σ.(mdev) pa 4 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R))%I.

  Definition Wobl_dev1 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 1)) (R : iProp Σ) : iProp Σ :=
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_write σ.(mdev) pa 1 v = Some d'⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R))%I.

  Definition Wobl_dev4 (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) : iProp Σ :=
    (∀ σ, mstate_interp σ ={⊤,∅}=∗ ∃ d' : dev_state,
        ⌜dev_write σ.(mdev) pa 4 v = Some d'⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗ R))%I.

  Local Lemma dev_cls_dev (width : Z) (pa : SailStdpp.Values.mword 64) :
    dev_cls width pa -> dev_addr pa = true.
  Proof. by intros (H & _ & _). Qed.

  (* ---- the four RAM LOAD engines ---- *)
  Definition swp_execute_LOAD_ram_S1 :=
    swp_execute_LOAD_S_gen 1 vmw1 addr_is_ram pma_allows_ram
      (ram_pma_load 1 vmw1 dvd1) (ram_mmio_r 1 vmw1)
      (ram_pmprange 1 vmw1 dvd1 uintw1) (Mobl_ram 1)
      (fun pa bytes R H => swp_read_ram_node1 pa bytes R
                             (addr_is_ram_not_dev pa H)).
  Definition swp_execute_LOAD_ram_S2 :=
    swp_execute_LOAD_S_gen 2 vmw2 addr_is_ram pma_allows_ram
      (ram_pma_load 2 vmw2 dvd2) (ram_mmio_r 2 vmw2)
      (ram_pmprange 2 vmw2 dvd2 uintw2) (Mobl_ram 2)
      (fun pa bytes R H => swp_read_ram_node2 pa bytes R
                             (addr_is_ram_not_dev pa H)).
  Definition swp_execute_LOAD_ram_S4 :=
    swp_execute_LOAD_S_gen 4 vmw4 addr_is_ram pma_allows_ram
      (ram_pma_load 4 vmw4 dvd4) (ram_mmio_r 4 vmw4)
      (ram_pmprange 4 vmw4 dvd4 uintw4) (Mobl_ram 4)
      (fun pa bytes R H => swp_read_ram_node4 pa bytes R
                             (addr_is_ram_not_dev pa H)).
  Definition swp_execute_LOAD_ram_S8 :=
    swp_execute_LOAD_S_gen 8 vmw8 addr_is_ram pma_allows_ram
      (ram_pma_load 8 vmw8 dvd8) (ram_mmio_r 8 vmw8)
      (ram_pmprange 8 vmw8 dvd8 uintw8) (Mobl_ram 8)
      (fun pa bytes R H => swp_read_ram_node8 pa bytes R
                             (addr_is_ram_not_dev pa H)).

  (* ---- the four RAM STORE engines ---- *)
  Definition swp_execute_STORE_ram_S1 :=
    swp_execute_STORE_S_gen 1 vmw1 addr_is_ram pma_allows_ram
      (ram_pma_store 1 vmw1 dvd1) (ram_mmio_w 1 vmw1)
      (ram_pmprange 1 vmw1 dvd1 uintw1) (Wobl_ram 1)
      (fun pa v R rr H => swp_write_ram_node1 pa v R rr
                            (addr_is_ram_not_dev pa H)).
  Definition swp_execute_STORE_ram_S2 :=
    swp_execute_STORE_S_gen 2 vmw2 addr_is_ram pma_allows_ram
      (ram_pma_store 2 vmw2 dvd2) (ram_mmio_w 2 vmw2)
      (ram_pmprange 2 vmw2 dvd2 uintw2) (Wobl_ram 2)
      (fun pa v R rr H => swp_write_ram_node2 pa v R rr
                            (addr_is_ram_not_dev pa H)).
  Definition swp_execute_STORE_ram_S4 :=
    swp_execute_STORE_S_gen 4 vmw4 addr_is_ram pma_allows_ram
      (ram_pma_store 4 vmw4 dvd4) (ram_mmio_w 4 vmw4)
      (ram_pmprange 4 vmw4 dvd4 uintw4) (Wobl_ram 4)
      (fun pa v R rr H => swp_write_ram_node4 pa v R rr
                            (addr_is_ram_not_dev pa H)).
  Definition swp_execute_STORE_ram_S8 :=
    swp_execute_STORE_S_gen 8 vmw8 addr_is_ram pma_allows_ram
      (ram_pma_store 8 vmw8 dvd8) (ram_mmio_w 8 vmw8)
      (ram_pmprange 8 vmw8 dvd8 uintw8) (Wobl_ram 8)
      (fun pa v R rr H => swp_write_ram_node8 pa v R rr
                            (addr_is_ram_not_dev pa H)).

  (* ---- THE WIDTH-GENERIC RAM NODE AND ENGINES.  The node is the ONE
     thing that cannot be width-generic (its request record is a TYPE
     index), but [vmem_width] is a four-way disjunction of LITERALS, so a
     leaf stated at a symbolic width recovers it by destructing that
     premise -- which is exactly what the width-generic memory leaves
     ([WpSconfMem]'s two atomic-update forms) need. ---- *)
  Lemma swp_read_ram_node_w (width : Z) (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * width)) (R : iProp Σ) :
    vmem_width width ->
    dev_addr pa = false ->
    gen_cert -∗
    Mobl_ram width pa bytes R -∗
    swp (read_ram Read_plain (Physaddr pa) width false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R).
  Proof.
    intros [-> | [-> | [-> | ->]]] Hdev;
      [ exact (swp_read_ram_node1 pa bytes R Hdev)
      | exact (swp_read_ram_node2 pa bytes R Hdev)
      | exact (swp_read_ram_node4 pa bytes R Hdev)
      | exact (swp_read_ram_node8 pa bytes R Hdev) ].
  Qed.

  Lemma swp_write_ram_node_w (width : Z) (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * width)) (R : iProp Σ)
      (rr : option resv) :
    vmem_width width ->
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Wobl_ram width pa v R -∗
    swp (write_ram Write_plain (Physaddr pa) width v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros [-> | [-> | [-> | ->]]] Hdev;
      [ exact (swp_write_ram_node1 pa v R rr Hdev)
      | exact (swp_write_ram_node2 pa v R rr Hdev)
      | exact (swp_write_ram_node4 pa v R rr Hdev)
      | exact (swp_write_ram_node8 pa v R rr Hdev) ].
  Qed.

  Definition swp_execute_LOAD_ram_Sw (width : Z) (Hvw : vmem_width width)
      (Hdvd : (width | 4096)) (Huintw : uint (to_bits 64 width) = width) :=
    swp_execute_LOAD_S_gen width Hvw addr_is_ram pma_allows_ram
      (ram_pma_load width Hvw Hdvd) (ram_mmio_r width Hvw)
      (ram_pmprange width Hvw Hdvd Huintw) (Mobl_ram width)
      (fun pa bytes R H => swp_read_ram_node_w width pa bytes R Hvw
                             (addr_is_ram_not_dev pa H)).

  Definition swp_execute_STORE_ram_Sw (width : Z) (Hvw : vmem_width width)
      (Hdvd : (width | 4096)) (Huintw : uint (to_bits 64 width) = width) :=
    swp_execute_STORE_S_gen width Hvw addr_is_ram pma_allows_ram
      (ram_pma_store width Hvw Hdvd) (ram_mmio_w width Hvw)
      (ram_pmprange width Hvw Hdvd Huintw) (Wobl_ram width)
      (fun pa v R rr H => swp_write_ram_node_w width pa v R rr Hvw
                            (addr_is_ram_not_dev pa H)).

  (* ---- THE EXISTENTIAL-VALUE OBLIGATIONS AND ENGINES ---- *)
  Definition Mobl_ram_ex (width : Z) (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) : iProp Σ :=
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * width),
          ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
             tso_read_bytes img log (hart_agent cpu_id) tv' pa
               (Z.to_N width) bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗
               tso_interp_of riscv_eraGS img σ.(mem) log V ∗ Rr bytes))%I.

  Definition Mobl_dev1_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 1) -> iProp Σ) : iProp Σ :=
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ (bytes : SailStdpp.Values.mword (8 * 1)) (d' : dev_state),
        ⌜dev_read σ.(mdev) pa 1 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
                     Rr bytes))%I.

  Definition Mobl_dev4_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 4) -> iProp Σ) : iProp Σ :=
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ (bytes : SailStdpp.Values.mword (8 * 4)) (d' : dev_state),
        ⌜dev_read σ.(mdev) pa 4 = Some (bytes, d')⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
                     Rr bytes))%I.

  (* ---- THE VALUE-CONFINED OBLIGATION (tso-m4-memo.md §6; A6.73's
     measurement B).  [Mobl_ram_ex]'s body with the [∃ bytes] moved INSIDE
     the [∀ tv'] and the resource made value-independent.  The reader of a
     RACY cell cannot name the word at all -- what it can name is a
     predicate the word satisfies at every view the machine's drain may
     choose -- and [Mobl_ram_ex] must NOT be used for such a cell: its
     shape asserts one word good at every reachable view, which is false
     the moment another hart writes.

     [Mobl_ram] (the fixed-value form) is the special case [P := eq v]
     with the [∃] discharged by [v]; it is left as its own definition
     because every engine below is abstract over the NAME. *)
  Definition Mobl_ram_exv (width : Z) (pa : SailStdpp.Values.mword 64)
      (P : SailStdpp.Values.mword (8 * width) -> Prop) (R : iProp Σ) : iProp Σ :=
    (∀ σ img log tv V,
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
           exists bytes : SailStdpp.Values.mword (8 * width),
             tso_read_bytes img log (hart_agent cpu_id) tv' pa
               (Z.to_N width) bytes /\ P bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗ R))%I.

  Lemma swp_read_ram_node_w_exv (width : Z) (pa : SailStdpp.Values.mword 64)
      (P : SailStdpp.Values.mword (8 * width) -> Prop) (R : iProp Σ) :
    vmem_width width ->
    dev_addr pa = false ->
    ⊢ gen_cert -∗
      Mobl_ram_exv width pa P R -∗
      swp (read_ram Read_plain (Physaddr pa) width false)
        (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                    ⌜r = (bytes, default_meta)⌝ ∗ ⌜P bytes⌝ ∗ R).
  Proof.
    intros [-> | [-> | [-> | ->]]] Hdev;
      [ exact (swp_read_ram_node1_exv pa P R Hdev)
      | exact (swp_read_ram_node2_exv pa P R Hdev)
      | exact (swp_read_ram_node4_exv pa P R Hdev)
      | exact (swp_read_ram_node8_exv pa P R Hdev) ].
  Qed.

  Lemma swp_read_ram_node_w_ex (width : Z) (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * width) -> iProp Σ) :
    vmem_width width ->
    dev_addr pa = false ->
    ⊢ gen_cert -∗
      Mobl_ram_ex width pa Rr -∗
      swp (read_ram Read_plain (Physaddr pa) width false)
        (fun r => ∃ bytes : SailStdpp.Values.mword (8 * width),
                    ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes).
  Proof.
    intros [-> | [-> | [-> | ->]]] Hdev;
      [ exact (swp_read_ram_node1_ex pa Rr Hdev)
      | exact (swp_read_ram_node2_ex pa Rr Hdev)
      | exact (swp_read_ram_node4_ex pa Rr Hdev)
      | exact (swp_read_ram_node8_ex pa Rr Hdev) ].
  Qed.

  Definition swp_execute_LOAD_ram_Sw_ex (width : Z) (Hvw : vmem_width width)
      (Hdvd : (width | 4096)) (Huintw : uint (to_bits 64 width) = width) :=
    swp_execute_LOAD_S_gen_ex width Hvw addr_is_ram pma_allows_ram
      (ram_pma_load width Hvw Hdvd) (ram_mmio_r width Hvw)
      (ram_pmprange width Hvw Hdvd Huintw).

  (* ---- the MMIO engines (widths 1 and 4) ---- *)
  Definition swp_execute_LOAD_dev_S1 :=
    swp_execute_LOAD_S_gen 1 vmw1 (dev_cls 1) pma_allows_io
      (dev_pma_load 1) (dev_mmio_r 1 vmw1) (dev_pmprange 1 vmw1 uintw1)
      Mobl_dev1
      (fun pa bytes R H => swp_dev_read_node1 pa bytes R (dev_cls_dev 1 pa H)).
  Definition swp_execute_LOAD_dev_S4 :=
    swp_execute_LOAD_S_gen 4 vmw4 (dev_cls 4) pma_allows_io
      (dev_pma_load 4) (dev_mmio_r 4 vmw4) (dev_pmprange 4 vmw4 uintw4)
      Mobl_dev4
      (fun pa bytes R H => swp_dev_read_node4 pa bytes R (dev_cls_dev 4 pa H)).
  Definition swp_execute_STORE_dev_S1 :=
    swp_execute_STORE_S_gen 1 vmw1 (dev_cls 1) pma_allows_io
      (dev_pma_store 1) (dev_mmio_w 1 vmw1) (dev_pmprange 1 vmw1 uintw1)
      Wobl_dev1
      (fun pa v R rr H => swp_dev_write_node1 pa v R rr (dev_cls_dev 1 pa H)).
  Definition swp_execute_STORE_dev_S4 :=
    swp_execute_STORE_S_gen 4 vmw4 (dev_cls 4) pma_allows_io
      (dev_pma_store 4) (dev_mmio_w 4 vmw4) (dev_pmprange 4 vmw4 uintw4)
      Wobl_dev4
      (fun pa v R rr H => swp_dev_write_node4 pa v R rr (dev_cls_dev 4 pa H)).


  (* ---- the two MMIO LOAD engines with the value existential ---- *)
  Definition swp_execute_LOAD_dev_S1_ex :=
    swp_execute_LOAD_S_gen_ex 1 vmw1 (dev_cls 1) pma_allows_io
      (dev_pma_load 1) (dev_mmio_r 1 vmw1) (dev_pmprange 1 vmw1 uintw1).
  Definition swp_execute_LOAD_dev_S4_ex :=
    swp_execute_LOAD_S_gen_ex 4 vmw4 (dev_cls 4) pma_allows_io
      (dev_pma_load 4) (dev_mmio_r 4 vmw4) (dev_pmprange 4 vmw4 uintw4).

End instances.

(* ====================================================================== *)
(* 12. THE AMO PATH (amoswap.w.aq -- what WpSconfLock's acquire uses).      *)
(*                                                                        *)
(* The three nodes of one AMO, in the reservation design of                *)
(* claude-notes/design/main-cycle-port.md §3a: the effective-address        *)
(* announcement ([mem_write_ea], no event), the EXCLUSIVE read (which       *)
(* records [(pa, n, bytes)] in the hart's reservation) and the CONDITIONAL  *)
(* write (which consumes exactly that reservation and learns from           *)
(* [resv_ok] that the bytes it is overwriting are the ones it read).  The   *)
(* window between them -- the [rX_bits rs2] read and the AMOCAS test -- is  *)
(* an ORDINARY silent stretch taking the ordinary rules; there is no fused  *)
(* AMO step and no walker for the window.                                  *)
(* ====================================================================== *)

(* the EXCLUSIVE read request: [read_kind_of_flags true false true] is
   [Read_RISCV_reserved_acquire], which the model maps to AV_exclusive at
   AS_rel_or_acq -- that acquire strength is the only difference from
   [HartMFetch.mread_req8_res]. *)
Definition mread_req4_racq (pa : SailStdpp.Values.mword 64)
    : Interface.ReadReq.t 4 :=
  {| Interface.ReadReq.pa := pa;
     Interface.ReadReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_exclusive;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_rel_or_acq |};
     Interface.ReadReq.va := None;
     Interface.ReadReq.translation := tt;
     Interface.ReadReq.tag := false |}.

Lemma hread_req_at_read_ram4_racq (pa : SailStdpp.Values.mword 64) :
  hread_req_at 4 (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
  = Some (mread_req4_racq pa).
Proof.
  unfold read_ram, Defs.sail_mem_read. req_cbn.
  cbn [hread_req_at].
  destruct (decide (4%N = 4%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hread_resume_read_ram4_racq (pa : SailStdpp.Values.mword 64) (w : bv 32) :
  hread_resume (bv_unsigned w)
    (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
  = Interface.Ret (w, default_meta).
Proof.
  unfold read_ram, Defs.sail_mem_read. req_cbn.
  cbn [hread_resume].
  rewrite Z_to_bv_bv_unsigned TypeCasts.cast_N_refl.
  reflexivity.
Qed.

(* the CONDITIONAL write request: [write_kind_of_flags false false true] is
   [Write_RISCV_conditional] -> AV_exclusive at AS_normal. *)
Definition mwrite_req4_con (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) : Interface.WriteReq.t 4 :=
  {| Interface.WriteReq.pa := pa;
     Interface.WriteReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_exclusive;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.WriteReq.value :=
       TypeCasts.cast_N v (Defs.sail_mem_write_subproof 4);
     Interface.WriteReq.va := None;
     Interface.WriteReq.translation := tt;
     Interface.WriteReq.tag := None |}.

Lemma hwrite_req_at_write_ram4_con (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) :
  hwrite_req_at 4 (write_ram Write_RISCV_conditional (Physaddr pa) 4 v tt)
  = Some (mwrite_req4_con pa v).
Proof.
  unfold write_ram, Defs.sail_mem_write. wreq_cbn.
  cbn [hwrite_req_at].
  destruct (decide (4%N = 4%N)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hwrite_resume_write_ram4_con (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) :
  hwrite_resume (write_ram Write_RISCV_conditional (Physaddr pa) 4 v tt)
  = Interface.Ret true.
Proof.
  unfold write_ram, Defs.sail_mem_write. wreq_cbn.
  cbn [hwrite_resume]. reflexivity.
Qed.

Lemma mwrite_req4_con_value (pa : SailStdpp.Values.mword 64)
    (v : SailStdpp.Values.mword 32) :
  Interface.WriteReq.value (mwrite_req4_con pa v) = v.
Proof.
  cbn [mwrite_req4_con Interface.WriteReq.value]. apply TypeCasts.cast_N_refl.
Qed.

(* the PMA check at an ATOMIC access.  [res_or_con] is TRUE here (that is
   what tells [pmaCheck] to take the atomic arm), and the grant is the
   conjunction of readable, writable and the region's atomic support at this
   op and width -- the [∀ op n, n <= 16] conjunct of [pma_class_grants]. *)
Lemma hfrun_check_pma_amo_S (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) (width : Z)
    (aq rl : bool) :
  Z.leb width 16 = true ->
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  pma_ram_access pa width ->
  is_aligned_paddr (Physaddr pa) width = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Atomic (AMOSWAP, aq, rl, Data, Data))
       PBMT_PMA Supervisor (Physaddr pa) width true)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros Hw16 HD Hpma Hpallow Hacc Hpa.
  unfold check_pma_with_pmp_priority. sm_cbn.
  sm_read. rewrite Hpma. sm_cbn.
  destruct (Hpallow pa width Hacc) as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & Hr & Hw & Hat & _).
  cbn [PMA_Region_attributes] in Hr, Hw, Hat.
  rewrite Hmatch. sm_cbn.
  rewrite Hr Hw (Hat AMOSWAP width Hw16). sm_cbn.
  rewrite Hpa. sm_cbn.
  apply hfrun_ret.
Qed.

Section samo_nodes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the EXCLUSIVE read node: the plain read plus the reservation update.  It
     is the ONLY thing the atomic window needs from the language -- what makes
     the region atomic is that a competing write to the reserved bytes
     self-loops until the conditional write clears the reservation. *)
  Lemma swp_read_ram_node4_racq (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ)
      (rr : option resv) :
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜mem_bytes_at σ pa 4 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ R)) -∗
    swp (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
      (fun r => ⌜r = (bytes, default_meta)⌝ ∗ R ∗
                resv_frag cpu_id (Some (snap_of pa 4 bytes))).
  Proof.
    intro Hdev. iIntros "#Hcert Hfrag Hmem".
    iApply (swp_hart_ram_read_excl 4 (mread_req4_racq pa) _ _ rr
              (hread_req_at_read_ram4_racq pa) Hdev ltac:(reflexivity)
              with "Hcert Hfrag [Hmem]").
    (* THE OBLIGATION IS UNCHANGED, and that is RULING 4 talking: an
       exclusive read reads at the LOG TOP, i.e. off the flat cache, so the
       caller still owes a [mem_bytes_at] fact and nothing else.  The rule
       has already drained this hart's view and minted the receipt; the node
       FRAMES the bundle and drops the receipt (a consumer that wants it
       takes it from the leaf, A6.6(b)). *)
    iIntros (s ? ? ? ?) "%Htv Hs Htso _".
    iMod ("Hmem" $! s with "Hs") as "[%Hb Hcl]".
    iModIntro. iExists bytes.
    iSplitR; [ iPureIntro; by apply read_bytes_of_bytes | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs Htso".
    iIntros "Hfrag". rewrite hread_resume_read_ram4_racq.
    iApply swp_ret. by iFrame.
  Qed.

  (* THE SAME NODE WITH THE LOADED WORD EXISTENTIAL.  A leaf whose target
     cell lives in an INVARIANT cannot name the bytes before the step: it
     learns them by opening the invariant inside this very callback.  The
     node already chooses the word inside [swp_hart_ram_read_excl]'s own
     existential, so the [_ex] form costs nothing but the statement -- and
     it is what every lock / device leaf uses. *)
  Lemma swp_read_ram_node4_racq_ex (pa : SailStdpp.Values.mword 64)
      (Rr : SailStdpp.Values.mword (8 * 4) -> iProp Σ) (rr : option resv) :
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 4),
          ⌜mem_bytes_at σ pa 4 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗ Rr bytes)) -∗
    swp (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 4),
                  ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes ∗
                  resv_frag cpu_id (Some (snap_of pa 4 bytes))).
  Proof.
    intro Hdev. iIntros "#Hcert Hfrag Hmem".
    iApply (swp_hart_ram_read_excl 4 (mread_req4_racq pa) _ _ rr
              (hread_req_at_read_ram4_racq pa) Hdev ltac:(reflexivity)
              with "Hcert Hfrag [Hmem]").
    iIntros (s ? ? ? ?) "%Htv Hs Htso _".
    iMod ("Hmem" $! s with "Hs") as (bytes) "[%Hb Hcl]".
    iModIntro. iExists bytes.
    iSplitR; [ iPureIntro; by apply read_bytes_of_bytes | ].
    iNext. iMod "Hcl" as "[Hs HR]". iModIntro. iFrame "Hs Htso".
    iIntros "Hfrag". rewrite hread_resume_read_ram4_racq.
    iApply swp_ret. iExists bytes. by iFrame.
  Qed.

  (* the CONDITIONAL write node.  Its callback LEARNS the old bytes -- that
     is [resv_ok] talking, and it is the one thing the logic needs to make an
     acquire sound (the invariant it opens at the write must know the word is
     the one the exclusive read saw). *)
  Lemma swp_write_ram_node4_con (pa : SailStdpp.Values.mword 64)
      (v old : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) :
    dev_addr pa = false ->
    gen_cert -∗
    resv_frag cpu_id (Some (snap_of pa 4 old)) -∗
    (* THE CONDITIONAL WRITE APPENDS LIKE ANY OTHER STORE, and its view goes
       PAST its own append ([ak_excl] is true here -- "the drain includes my
       write"), which is what makes the AMO an acquire. *)
    (∀ σ img log tv V, ⌜read_bytes σ.(mem) pa 4 = Some old⌝ -∗
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        mstate_interp σ -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs) (write_bytes σ.(mem) pa 4 v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img (write_bytes σ.(mem) pa 4 v)
               (log ++ [PWMsg (snap_of pa 4 v) (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) (S (length log))
                  (log ++ [PWMsg (snap_of pa 4 v) (hart_agent cpu_id)])%list V)
             ∗ R)) -∗
    swp (write_ram Write_RISCV_conditional (Physaddr pa) 4 v tt)
      (fun r => ⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intro Hdev. iIntros "#Hcert Hfrag Hmem".
    iApply (swp_hart_ram_write_cond 4 (mwrite_req4_con pa v) _ _ old
              (hwrite_req_at_write_ram4_con pa v) Hdev ltac:(lia)
              with "Hcert Hfrag [Hmem]").
    iIntros (s ? ? ? ?) "%Hrb %Htv Hs Htso".
    iMod ("Hmem" $! s _ _ _ _ with "[//] [//] Hs Htso") as "Hcl".
    iModIntro. iNext. iMod "Hcl" as "(Hs & Htso & HR)". iModIntro.
    rewrite mwrite_req4_con_value. iFrame "Hs Htso".
    iIntros "Hfrag _". rewrite hwrite_resume_write_ram4_con.
    iApply swp_ret. by iFrame.
  Qed.

End samo_nodes.

(* ---------------------------------------------------------------------- *)
(* The amoswap.w.aq chain.  Pinned to [AMOSWAP], width 4 and the aq/rl pair *)
(* the kernel's [acquire] issues: the model's [write_kind_of_flags] /       *)
(* [read_kind_of_flags] MATCH on those booleans, so a symbolic pair leaves   *)
(* the request record unreduced and buys no generality here (xv6 has        *)
(* exactly one AMO).                                                        *)
(* ---------------------------------------------------------------------- *)
Local Notation amoacc := (Atomic (AMOSWAP, true, false, Data, Data)).

Section samo.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the PMP/PMA premise bundle repeated by all three AMO nodes *)
  Local Ltac apmp HR HW :=
    unfold pmpCheckRWX; cbn match; rewrite HR HW; reflexivity.

  Lemma swp_mem_write_ea_amo_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    effectivePrivilege amoacc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (mem_write_ea (Physaddr pa) 4 amoacc PBMT_PMA false false true)
      (fun r => ⌜r = Values.Ok tt⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDaddr Hpriv Hpma Hpcfg Hpaddr
      Hep HA Hord HR HW Hcov Hpallow Hram Hpa.
    assert (Hacc : pma_ram_access pa 4)
      by (apply (pma_ram_access_w pa 4 ltac:(lia) ltac:(lia) dvd4 Hram Hpa)).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                       (Z.mul (uint (vec_access_dec paddr 0)) 4)
                       (uint pa) (uint (to_bits 64 4)) = PMP_Match)
      by (apply (ram_pmp_match_w pa (vec_access_dec paddr 0) 4 ltac:(lia) uintw4);
          [ exact (proj1 Hram) | exact (proj2 (proj2 Hacc)) | exact Hcov ]).
    iIntros "#Hcert Hrw Hro".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold mem_write_ea.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep.
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority amoacc PBMT_PMA Supervisor
                 (Physaddr pa) 4 true) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_amo_S (Drw ∪ Dro) Drw rs pa pmar0 4 true false
                   ltac:(reflexivity) HDpma Hpma Hpallow Hacc Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbindR_ret. sm_glue.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing write_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    sm_glue.
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    rewrite mliftR_ret mbind_ret. sm_glue.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. sm_glue.
    change (0 * 4)%Z with 0%Z. rewrite avi0.
    iApply (swp_use_cer3 (pmpCheck (Physaddr pa) 4 amoacc Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S amoacc Drw Dro Df rs pcfg paddr
                pa 4 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(apmp HR HW) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbind0R_ret. sm_glue.
    change (0 =? 1 - 1) with true. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok tt)). by iFrame.
  Qed.

  Lemma swp_checked_mem_read_amo_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ)
      (rr : option resv) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜mem_bytes_at σ pa 4 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ R)) -∗
    swp (checked_mem_read amoacc PBMT_PMA Supervisor (Physaddr pa) 4
           true false true false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                resv_frag cpu_id (Some (snap_of pa 4 bytes))).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HR HW Hcov Hpallow Hram Hpa.
    assert (Hacc : pma_ram_access pa 4)
      by (apply (pma_ram_access_w pa 4 ltac:(lia) ltac:(lia) dvd4 Hram Hpa)).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                       (Z.mul (uint (vec_access_dec paddr 0)) 4)
                       (uint pa) (uint (to_bits 64 4)) = PMP_Match)
      by (apply (ram_pmp_match_w pa (vec_access_dec paddr 0) 4 ltac:(lia) uintw4);
          [ exact (proj1 Hram) | exact (proj2 (proj2 Hacc)) | exact Hcov ]).
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority amoacc PBMT_PMA Supervisor
                 (Physaddr pa) 4 true) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_amo_S (Drw ∪ Dro) Drw rs pa pmar0 4 true false
                   ltac:(reflexivity) HDpma Hpma Hpallow Hacc Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbindR_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 4)%Z with 0%Z. rewrite avi0.
    iApply (swp_use_cer3 (pmpCheck (Physaddr pa) 4 amoacc Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S amoacc Drw Dro Df rs pcfg paddr
                pa 4 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(apmp HR HW) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0R_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 4)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 4
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4
              (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
              (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                         resv_frag cpu_id (Some (snap_of pa 4 bytes)))%I)
              _ _ _ _ C HC with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_mono
                (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗ R ∗
                           resv_frag cpu_id (Some (snap_of pa 4 bytes)))%I)
                with "[Hrw Hro] [Hmem Hfrag]").
      - iIntros (r) "(-> & HR & Hfrag)". by iFrame.
      - iApply (swp_read_ram_node4_racq pa bytes R rr
                  (addr_is_ram_not_dev pa Hram) with "Hcert Hfrag Hmem"). }
    iIntros (v) "(-> & Hrw & Hro & HR & Hfrag)". cbn beta iota zeta.
    rewrite mbindR_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_32 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  (* ...and the same with the loaded word EXISTENTIAL.  See
     [swp_read_ram_node4_racq_ex]: a leaf whose cell lives in an invariant
     learns the bytes only inside the callback, so the value cannot be a
     parameter.  [Rr] is therefore indexed by it. *)
  Lemma swp_checked_mem_read_amo_S_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr : SailStdpp.Values.mword (8 * 4) -> iProp Σ)
      (rr : option resv) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 4),
          ⌜mem_bytes_at σ pa 4 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗ Rr bytes)) -∗
    swp (checked_mem_read amoacc PBMT_PMA Supervisor (Physaddr pa) 4
           true false true false)
      (fun r => ∃ bytes : SailStdpp.Values.mword (8 * 4),
                  ⌜r = Values.Ok (bytes, tt)⌝ ∗
                  hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ Rr bytes ∗
                  resv_frag cpu_id (Some (snap_of pa 4 bytes))).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord HR HW Hcov Hpallow Hram Hpa.
    assert (Hacc : pma_ram_access pa 4)
      by (apply (pma_ram_access_w pa 4 ltac:(lia) ltac:(lia) dvd4 Hram Hpa)).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                       (Z.mul (uint (vec_access_dec paddr 0)) 4)
                       (uint pa) (uint (to_bits 64 4)) = PMP_Match)
      by (apply (ram_pmp_match_w pa (vec_access_dec paddr 0) 4 ltac:(lia) uintw4);
          [ exact (proj1 Hram) | exact (proj2 (proj2 Hacc)) | exact Hcov ]).
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority amoacc PBMT_PMA Supervisor
                 (Physaddr pa) 4 true) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_amo_S (Drw ∪ Dro) Drw rs pa pmar0 4 true false
                   ltac:(reflexivity) HDpma Hpma Hpallow Hacc Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbindR_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 4)%Z with 0%Z. rewrite avi0.
    iApply (swp_use_cer3 (pmpCheck (Physaddr pa) 4 amoacc Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S amoacc Drw Dro Df rs pcfg paddr
                pa 4 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(apmp HR HW) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0R_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 4)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 4
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4
              (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
              (fun r => (∃ bytes : SailStdpp.Values.mword (8 * 4),
                         ⌜r = (bytes, default_meta)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗
                         Rr bytes ∗
                         resv_frag cpu_id (Some (snap_of pa 4 bytes)))%I)
              _ _ _ _ C HC with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_mono
                (read_ram Read_RISCV_reserved_acquire (Physaddr pa) 4 false)
                (fun r => (∃ bytes : SailStdpp.Values.mword (8 * 4),
                           ⌜r = (bytes, default_meta)⌝ ∗ Rr bytes ∗
                           resv_frag cpu_id (Some (snap_of pa 4 bytes)))%I)
                with "[Hrw Hro] [Hmem Hfrag]").
      - iIntros (r) "(%bytes & -> & HR & Hfrag)". iExists bytes. by iFrame.
      - iApply (swp_read_ram_node4_racq_ex pa Rr rr
                  (addr_is_ram_not_dev pa Hram) with "Hcert Hfrag Hmem"). }
    iIntros (v) "(%bytes & -> & Hrw & Hro & HR & Hfrag)". cbn beta iota zeta.
    rewrite mbindR_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_32 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). iExists bytes. by iFrame.
  Qed.

  Lemma swp_mem_read_amo_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr)
      (w : SailStdpp.Values.mword (8 * 4)) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    effectivePrivilege amoacc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read amoacc PBMT_PMA Supervisor pa 4
              true false true false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (mem_read amoacc PBMT_PMA pa 4 true false true)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv Hep.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep. rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro & HR)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

  (* the [mem_read] wrapper, loaded word existential *)
  Lemma swp_mem_read_amo_S_ex (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : physaddr)
      (R : SailStdpp.Values.mword (8 * 4) -> iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    effectivePrivilege amoacc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read amoacc PBMT_PMA Supervisor pa 4
              true false true false)
         (fun r => ∃ w : SailStdpp.Values.mword (8 * 4),
                     ⌜r = Values.Ok (w, tt)⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R w)) -∗
    swp (mem_read amoacc PBMT_PMA pa 4 true false true)
      (fun r => ∃ w : SailStdpp.Values.mword (8 * 4),
                  ⌜r = Values.Ok w⌝ ∗
                  hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R w).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv Hep.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold mem_read.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep. rewrite mbind_ret.
    unfold mem_read_priv, mem_read_priv_meta.
    cbn beta iota.
    iApply (swp_bind_use _ _
              (fun r => (∃ w : SailStdpp.Values.mword (8 * 4),
                         ⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R w)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (∃ w : SailStdpp.Values.mword (8 * 4),
                           ⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R w)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(%w & -> & Hrw & Hro & HR)". iApply swp_ret.
        iExists w. by iFrame. }
    iIntros (v) "(%w & -> & Hrw & Hro & HR)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. iExists w. by iFrame.
  Qed.

  Lemma swp_checked_mem_write_amo_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (v old : SailStdpp.Values.mword (8 * 4))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (R : iProp Σ) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    resv_frag cpu_id (Some (snap_of pa 4 old)) -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* THE CONDITIONAL WRITE APPENDS LIKE ANY OTHER STORE, and its view goes
       PAST its own append ([ak_excl] is true here -- "the drain includes my
       write"), which is what makes the AMO an acquire. *)
    (∀ σ img log tv V, ⌜read_bytes σ.(mem) pa 4 = Some old⌝ -∗
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        mstate_interp σ -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs) (write_bytes σ.(mem) pa 4 v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img (write_bytes σ.(mem) pa 4 v)
               (log ++ [PWMsg (snap_of pa 4 v) (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) (S (length log))
                  (log ++ [PWMsg (snap_of pa 4 v) (hart_agent cpu_id)])%list V)
             ∗ R)) -∗
    swp (checked_mem_write (Physaddr pa) 4 v amoacc PBMT_PMA Supervisor tt
           false false true)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                resv_frag cpu_id None).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hpma Hpcfg Hpaddr Hhtif
      HA Hord HR HW Hcov Hpallow Hram Hpa.
    assert (Hacc : pma_ram_access pa 4)
      by (apply (pma_ram_access_w pa 4 ltac:(lia) ltac:(lia) dvd4 Hram Hpa)).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                       (Z.mul (uint (vec_access_dec paddr 0)) 4)
                       (uint pa) (uint (to_bits 64 4)) = PMP_Match)
      by (apply (ram_pmp_match_w pa (vec_access_dec paddr 0) 4 ltac:(lia) uintw4);
          [ exact (proj1 Hram) | exact (proj2 (proj2 Hacc)) | exact Hcov ]).
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_write.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority amoacc PBMT_PMA Supervisor
                 (Physaddr pa) 4 true) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_amo_S (Drw ∪ Dro) Drw rs pa pmar0 4 true false
                   ltac:(reflexivity) HDpma Hpma Hpallow Hacc Hpa)
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbindR_ret. sm_glue.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing write_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    sm_glue.
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    rewrite mliftR_ret mbind_ret. sm_glue.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. sm_glue.
    change (0 * 4)%Z with 0%Z. rewrite avi0.
    iApply (swp_use_cer3 (pmpCheck (Physaddr pa) 4 amoacc Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S amoacc Drw Dro Df rs pcfg paddr
                pa 4 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(apmp HR HW) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbind0R_ret.
    iApply (swp_use_cer3 (within_mmio_writable (Physaddr pa) 4)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_w_ram (Drw ∪ Dro) Drw rs pa 4
                   ltac:(lia) HDhtif Hhtif Hram) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    change (8 * (0 + 1) * 4 - 1)%Z with 31%Z. change (8 * 0 * 4)%Z with 0%Z.
    rewrite subrange_full_32 autocast_id.
    iApply (swp_use_cer4
              (write_ram Write_RISCV_conditional (Physaddr pa) 4 v tt)
              (fun r => (⌜r = true⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                         resv_frag cpu_id None)%I)
              _ _ _ _ C HC with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_mono
                (write_ram Write_RISCV_conditional (Physaddr pa) 4 v tt)
                (fun r => (⌜r = true⌝ ∗ R ∗ resv_frag cpu_id None)%I)
                with "[Hrw Hro] [Hmem Hfrag]").
      - iIntros (r) "(-> & HR & Hfrag)". by iFrame.
      - iApply (swp_write_ram_node4_con pa v old R
                  (addr_is_ram_not_dev pa Hram) with "Hcert Hfrag Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". sm_glue.
    change (0 =? 1 - 1) with true. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). by iFrame.
  Qed.

  Lemma swp_mem_write_value_amo_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (v old : SailStdpp.Values.mword (8 * 4))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (R : iProp Σ) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    effectivePrivilege amoacc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    gen_cert -∗
    resv_frag cpu_id (Some (snap_of pa 4 old)) -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* THE CONDITIONAL WRITE APPENDS LIKE ANY OTHER STORE, and its view goes
       PAST its own append ([ak_excl] is true here -- "the drain includes my
       write"), which is what makes the AMO an acquire. *)
    (∀ σ img log tv V, ⌜read_bytes σ.(mem) pa 4 = Some old⌝ -∗
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        mstate_interp σ -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs) (write_bytes σ.(mem) pa 4 v) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img (write_bytes σ.(mem) pa 4 v)
               (log ++ [PWMsg (snap_of pa 4 v) (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) (S (length log))
                  (log ++ [PWMsg (snap_of pa 4 v) (hart_agent cpu_id)])%list V)
             ∗ R)) -∗
    swp (mem_write_value (Physaddr pa) 4 v amoacc PBMT_PMA false false true)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                resv_frag cpu_id None).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv Hpma Hpcfg
      Hpaddr Hhtif Hep HA Hord HR HW Hcov Hpallow Hram Hpa.
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    unfold mem_write_value, mem_write_value_meta.
    iApply (swp_bind_use (Defs.read_reg mstatus) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep. rewrite mbind_ret.
    unfold mem_write_value_priv_meta.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                         resv_frag cpu_id None)%I) _
              with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_checked_mem_write_amo_S Drw Dro Df rs pa v old pmar0 pcfg
                paddr R Hdisj HDpma HDcfg HDaddr HDhtif Hpma Hpcfg Hpaddr
                Hhtif HA Hord HR HW Hcov Hpallow Hram Hpa
                with "Hcert Hfrag Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". sm_glue.
    iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [execute_AMO AMOSWAP true false rs2 rs1 4 rd] -- amoswap.w.aq.       *)
  (*                                                                     *)
  (* The three memory nodes with the ordinary silent stretch between them: *)
  (* [rX_bits rs2] and the AMOCAS test are plain register traffic and take  *)
  (* the plain rules.  The read obligation hands the caller [Rr] (what its  *)
  (* invariant told it at the read), and the write obligation CONSUMES [Rr] *)
  (* -- which is how a lock acquire opens its invariant read-only at the    *)
  (* read and does its one logical atomic access at the conditional write.  *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_execute_AMOSWAP_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (rs2 rs1 rd : SailStdpp.Values.mword 5) (m : regfile)
      (pa : SailStdpp.Values.mword 64)
      (bytes : SailStdpp.Values.mword (8 * 4))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv) :
    let ea := add_vec (m !!! Regidx rs1) (zeros' 64) in
    let sv := sign_extend' (Z.mul 8 (__id 4))
                (trunc (Z.mul (__id 4) 8) (m !!! Regidx rs2)) in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs))
      = ('b"1000" : mword 4) ->
    effectivePrivilege amoacc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    uint rd <> 0 ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) amoacc)
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜mem_bytes_at σ pa 4 bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ Rr)) -∗
    (Rr -∗ ∀ σ img log tv V, ⌜read_bytes σ.(mem) pa 4 = Some bytes⌝ -∗
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        mstate_interp σ -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs) (write_bytes σ.(mem) pa 4 sv) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img (write_bytes σ.(mem) pa 4 sv)
               (log ++ [PWMsg (snap_of pa 4 sv) (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) (S (length log))
                  (log ++ [PWMsg (snap_of pa 4 sv) (hart_agent cpu_id)])%list V)
             ∗ R)) -∗
    swp (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd
                            := regval_into_reg
                                 (sign_extend' 64
                                    (autocast (T := mword) bytes
                                     : mword (4 * 8)))]> m) ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros ea sv Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL Hmode Hep HA Hord HR HW
      Hcov Hpallow Hram Hva Hpa Hrd.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hrd0 Hwr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold execute_AMO. cbn zeta.
    change (Z.leb 4 (Z.mul xlen_bytes 2)) with true.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx rs1) (zeros' 64) amoacc 4)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_S_gen 4 Drw Dro Df rs rs1 m
                (zeros' 64) amoacc Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hmxr Hpmm HSXL
                (hval_transform_effective_address_S (Drw ∪ Dro) Drw rs _ amoacc
                   HDmst HDpriv HDmenv HDsatp Hpriv Hep
                   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                   Hmxr Hpmm HSXL Hmode)
                with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota.
    rewrite mbindR_ret. sm_glue.
    rewrite Hva. sm_glue.
    rewrite mbind0R_ret. sm_glue.
    iApply (swp_use_cer (translateAddr (Virtaddr ea) amoacc) _ _ C HC
              with "[Hfrag Hres Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hfrag Hres Hrw Hro"). }
    iIntros (v0) "(-> & Hland)". cbn beta iota.
    iDestruct "Hland" as (rsf) "(%Hland & Hrw & Hro & Hres & Hany)".
    iDestruct "Hany" as (rr') "Hfrag".
    assert (Hpriv' : register_lookup cur_privilege rsf = Supervisor)
      by (rewrite (sland_lookup rs rsf Hland cur_privilege eq_refl); exact Hpriv).
    assert (Hmst' : register_lookup mstatus rsf = register_lookup mstatus rs)
      by (apply (sland_lookup rs rsf Hland mstatus eq_refl)).
    assert (Hhtif' : register_lookup htif_tohost_base rsf = None)
      by (rewrite (sland_lookup rs rsf Hland htif_tohost_base eq_refl); exact Hhtif).
    assert (Hpma' : register_lookup pma_regions rsf = pmar0)
      by (rewrite (sland_lookup rs rsf Hland pma_regions eq_refl); exact Hpma).
    assert (Hpcfg' : register_lookup pmpcfg_n rsf = pcfg)
      by (rewrite (sland_lookup rs rsf Hland pmpcfg_n eq_refl); exact Hpcfg).
    assert (Hpaddr' : register_lookup pmpaddr_n rsf = paddr)
      by (rewrite (sland_lookup rs rsf Hland pmpaddr_n eq_refl); exact Hpaddr).
    rewrite mbindR_ret. cbn beta iota.
    iApply (swp_use_cer
              (mem_write_ea (Physaddr pa) 4 amoacc PBMT_PMA false false true)
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_mem_write_ea_amo_S Drw Dro Df rsf pa pmar0 pcfg paddr Hdisj
                HDmst HDpriv HDpma HDcfg HDaddr Hpriv' Hpma' Hpcfg' Hpaddr'
                ltac:(rewrite Hmst'; exact Hep) HA Hord HR HW Hcov Hpallow
                Hram Hpa with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer2 (mem_read amoacc PBMT_PMA (Physaddr pa) 4
                            true false true)
              _ _ _ C HC with "[Hrw Hro Hrd0 Hfrag] [-]").
    { iApply (swp_mem_read_amo_S Drw Dro Df rsf (Physaddr pa) bytes
                (Rr ∗ resv_frag cpu_id (Some (snap_of pa 4 bytes)))%I
                Hdisj HDmst HDpriv Hpriv'
                ltac:(rewrite Hmst'; exact Hep)
                with "Hcert Hrw Hro [Hrd0 Hfrag]").
      iIntros "Hrw Hro".
      iApply (swp_mono _
                (fun r => (⌜r = Values.Ok (bytes, tt)⌝ ∗
                           hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗ Rr ∗
                           resv_frag cpu_id (Some (snap_of pa 4 bytes)))%I)
                with "[] [Hrw Hro Hrd0 Hfrag]").
      - iIntros (r) "(-> & Hrw & Hro & HRr & Hfrag)". by iFrame.
      - iApply (swp_checked_mem_read_amo_S Drw Dro Df rsf pa pmar0 pcfg paddr
                  bytes Rr rr' Hdisj HDpma HDcfg HDaddr HDhtif Hhtif' Hpma'
                  Hpcfg' Hpaddr' HA Hord HR HW Hcov Hpallow Hram Hpa
                  with "Hcert Hfrag Hrw Hro Hrd0"). }
    iIntros (v0) "(-> & Hrw & Hro & HRr & Hfrag)". cbn beta iota.
    rewrite mbindR_ret. cbn beta iota zeta.
    change (Z.leb 4 xlen_bytes) with true. cbn beta iota.
    iApply (swp_use_cer2 (rX_bits (Regidx rs2)) _ _ _ C HC
              with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (v0) "(-> & Hf)". cbn beta iota.
    rewrite mbindR_ret. cbn beta iota zeta.
    change (Instances.generic_eq AMOSWAP AMOCAS) with false.
    unfold Defs.and_boolM.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer
              (mem_write_value (Physaddr pa) 4 sv amoacc PBMT_PMA
                 false false true) _ _ C HC
              with "[Hrw Hro Hwr HRr Hfrag] [-]").
    { iApply (swp_mem_write_value_amo_S Drw Dro Df rsf pa sv bytes pmar0 pcfg
                paddr R Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv'
                Hpma' Hpcfg' Hpaddr' Hhtif' ltac:(rewrite Hmst'; exact Hep)
                HA Hord HR HW Hcov Hpallow Hram Hpa
                with "Hcert Hfrag Hrw Hro [Hwr HRr]").
      iApply ("Hwr" with "HRr"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". cbn beta iota.
    iApply (swp_use_cer
              (wX_bits (Regidx rd)
                 (sign_extend' 64
                    (autocast (T := mword) bytes : mword (4 * 8))))
              _ _ C HC with "[Hf] [-]").
    { iApply (swp_wX_file rd m _ Hrd with "Hcert Hf"). }
    iIntros (u) "Hf". cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! RETIRE_SUCCESS). iSplitR; [done|].
    iSplitL "Hf"; [ iExact "Hf" | ].
    iExists rsf. iFrame. done.
  Qed.


  (* ==================================================================== *)
  (* THE SAME ENGINE WITH THE LOADED WORD EXISTENTIAL.                     *)
  (*                                                                      *)
  (* A leaf whose target word lives in an INVARIANT (every lock leaf, and  *)
  (* every device read) cannot name the loaded bytes BEFORE the step: it   *)
  (* learns them by opening the invariant inside the read node's own       *)
  (* callback, and the exclusive read is a step of its own -- the mask is  *)
  (* back at [⊤] between it and the conditional write, so the invariant    *)
  (* CANNOT be held open across the window.  What makes the window atomic  *)
  (* is the RESERVATION (design §3a): the conditional write's callback     *)
  (* learns [read_bytes = Some bytes] from [resv_ok], which is exactly the *)
  (* fact an acquire needs to know the word it is overwriting is still the *)
  (* one it read.  So both the read's rider [Rr] and the write's [R] are   *)
  (* INDEXED BY the loaded word, and the conclusion existentially          *)
  (* quantifies it.  [swp_execute_AMOSWAP_S] is the instance in which the  *)
  (* caller already knows the word.                                        *)
  (* ==================================================================== *)
  Lemma swp_execute_AMOSWAP_S_ex_mode (Drw Dro : gset register)
      (Df : register -> dfrac)
      (rs : regstate) (rs2 rs1 rd : SailStdpp.Values.mword 5) (m : regfile)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr R : SailStdpp.Values.mword (8 * 4) -> iProp Σ)
      (Rt : regstate -> iProp Σ) (rr : option resv) (md : SATPMode) :
    let ea := add_vec (m !!! Regidx rs1) (zeros' 64) in
    let sv := sign_extend' (Z.mul 8 (__id 4))
                (trunc (Z.mul (__id 4) 8) (m !!! Regidx rs2)) in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    satpMode_of_bits RV64
      (_get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs))) = Some md ->
    effectivePrivilege amoacc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    uint rd <> 0 ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) amoacc)
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 4),
          ⌜mem_bytes_at σ pa 4 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗ Rr bytes)) -∗
    (∀ bytes : SailStdpp.Values.mword (8 * 4),
       Rr bytes -∗ ∀ σ img log tv V, ⌜read_bytes σ.(mem) pa 4 = Some bytes⌝ -∗
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        mstate_interp σ -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs) (write_bytes σ.(mem) pa 4 sv) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img (write_bytes σ.(mem) pa 4 sv)
               (log ++ [PWMsg (snap_of pa 4 sv) (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) (S (length log))
                  (log ++ [PWMsg (snap_of pa 4 sv) (hart_agent cpu_id)])%list V)
             ∗ R bytes)) -∗
    swp (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                ∃ bytes : SailStdpp.Values.mword (8 * 4),
                gpr_file (<[Regidx rd
                            := regval_into_reg
                                 (sign_extend' 64
                                    (autocast (T := mword) bytes
                                     : mword (4 * 8)))]> m) ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R bytes ∗ resv_frag cpu_id None).
  Proof.
    intros ea sv Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL Hmode Hep HA Hord HR HW
      Hcov Hpallow Hram Hva Hpa Hrd.
    iIntros "#Hcert Hfrag Hres Hf Hrw Hro Htr Hrd0 Hwr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold execute_AMO. cbn zeta.
    change (Z.leb 4 (Z.mul xlen_bytes 2)) with true.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx rs1) (zeros' 64) amoacc 4)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_S_gen 4 Drw Dro Df rs rs1 m
                (zeros' 64) amoacc Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hmxr Hpmm HSXL
                (hval_transform_effective_address_S_mode (Drw ∪ Dro) Drw rs
                   _ amoacc md
                   HDmst HDpriv HDmenv HDsatp Hpriv Hep
                   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                   Hmxr Hpmm HSXL Hmode)
                with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota.
    rewrite mbindR_ret. sm_glue.
    rewrite Hva. sm_glue.
    rewrite mbind0R_ret. sm_glue.
    iApply (swp_use_cer (translateAddr (Virtaddr ea) amoacc) _ _ C HC
              with "[Hfrag Hres Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hfrag Hres Hrw Hro"). }
    iIntros (v0) "(-> & Hland)". cbn beta iota.
    iDestruct "Hland" as (rsf) "(%Hland & Hrw & Hro & Hres & Hany)".
    iDestruct "Hany" as (rr') "Hfrag".
    assert (Hpriv' : register_lookup cur_privilege rsf = Supervisor)
      by (rewrite (sland_lookup rs rsf Hland cur_privilege eq_refl); exact Hpriv).
    assert (Hmst' : register_lookup mstatus rsf = register_lookup mstatus rs)
      by (apply (sland_lookup rs rsf Hland mstatus eq_refl)).
    assert (Hhtif' : register_lookup htif_tohost_base rsf = None)
      by (rewrite (sland_lookup rs rsf Hland htif_tohost_base eq_refl); exact Hhtif).
    assert (Hpma' : register_lookup pma_regions rsf = pmar0)
      by (rewrite (sland_lookup rs rsf Hland pma_regions eq_refl); exact Hpma).
    assert (Hpcfg' : register_lookup pmpcfg_n rsf = pcfg)
      by (rewrite (sland_lookup rs rsf Hland pmpcfg_n eq_refl); exact Hpcfg).
    assert (Hpaddr' : register_lookup pmpaddr_n rsf = paddr)
      by (rewrite (sland_lookup rs rsf Hland pmpaddr_n eq_refl); exact Hpaddr).
    rewrite mbindR_ret. cbn beta iota.
    iApply (swp_use_cer
              (mem_write_ea (Physaddr pa) 4 amoacc PBMT_PMA false false true)
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_mem_write_ea_amo_S Drw Dro Df rsf pa pmar0 pcfg paddr Hdisj
                HDmst HDpriv HDpma HDcfg HDaddr Hpriv' Hpma' Hpcfg' Hpaddr'
                ltac:(rewrite Hmst'; exact Hep) HA Hord HR HW Hcov Hpallow
                Hram Hpa with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer2 (mem_read amoacc PBMT_PMA (Physaddr pa) 4
                            true false true)
              _ _ _ C HC with "[Hrw Hro Hrd0 Hfrag] [-]").
    { iApply (swp_mem_read_amo_S_ex Drw Dro Df rsf (Physaddr pa)
                (fun b => Rr b ∗ resv_frag cpu_id (Some (snap_of pa 4 b)))%I
                Hdisj HDmst HDpriv Hpriv'
                ltac:(rewrite Hmst'; exact Hep)
                with "Hcert Hrw Hro [Hrd0 Hfrag]").
      iIntros "Hrw Hro".
      iApply (swp_mono _
                (fun r => (∃ b : SailStdpp.Values.mword (8 * 4),
                           ⌜r = Values.Ok (b, tt)⌝ ∗
                           hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                           Rr b ∗
                           resv_frag cpu_id (Some (snap_of pa 4 b)))%I)
                with "[] [Hrw Hro Hrd0 Hfrag]").
      - iIntros (r) "(%b & -> & Hrw & Hro & HRr & Hfrag)".
        iExists b. by iFrame.
      - iApply (swp_checked_mem_read_amo_S_ex Drw Dro Df rsf pa pmar0 pcfg paddr
                  Rr rr' Hdisj HDpma HDcfg HDaddr HDhtif Hhtif' Hpma'
                  Hpcfg' Hpaddr' HA Hord HR HW Hcov Hpallow Hram Hpa
                  with "Hcert Hfrag Hrw Hro Hrd0"). }
    iIntros (v0) "(%bytes & -> & Hrw & Hro & HRr & Hfrag)". cbn beta iota.
    rewrite mbindR_ret. cbn beta iota zeta.
    change (Z.leb 4 xlen_bytes) with true. cbn beta iota.
    iApply (swp_use_cer2 (rX_bits (Regidx rs2)) _ _ _ C HC
              with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (v0) "(-> & Hf)". cbn beta iota.
    rewrite mbindR_ret. cbn beta iota zeta.
    change (Instances.generic_eq AMOSWAP AMOCAS) with false.
    unfold Defs.and_boolM.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer
              (mem_write_value (Physaddr pa) 4 sv amoacc PBMT_PMA
                 false false true) _ _ C HC
              with "[Hrw Hro Hwr HRr Hfrag] [-]").
    { iApply (swp_mem_write_value_amo_S Drw Dro Df rsf pa sv bytes pmar0 pcfg
                paddr (R bytes) Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv'
                Hpma' Hpcfg' Hpaddr' Hhtif' ltac:(rewrite Hmst'; exact Hep)
                HA Hord HR HW Hcov Hpallow Hram Hpa
                with "Hcert Hfrag Hrw Hro [Hwr HRr]").
      iApply ("Hwr" $! bytes with "HRr"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". cbn beta iota.
    iApply (swp_use_cer
              (wX_bits (Regidx rd)
                 (sign_extend' 64
                    (autocast (T := mword) bytes : mword (4 * 8))))
              _ _ C HC with "[Hf] [-]").
    { iApply (swp_wX_file rd m _ Hrd with "Hcert Hf"). }
    iIntros (u) "Hf". cbn beta iota.
    rewrite mcer_ret.
    iApply ("Hcont" $! RETIRE_SUCCESS). iSplitR; [done|].
    iExists bytes. iSplitL "Hf"; [ iExact "Hf" | ].
    iExists rsf. iFrame. done.
  Qed.

  (* the Sv39 instance -- the statement before the mode generalization, kept
     for a caller whose regime is the kernel table outright. *)
  Lemma swp_execute_AMOSWAP_S_ex (Drw Dro : gset register)
      (Df : register -> dfrac)
      (rs : regstate) (rs2 rs1 rd : SailStdpp.Values.mword 5) (m : regfile)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (Rr R : SailStdpp.Values.mword (8 * 4) -> iProp Σ)
      (Rt : regstate -> iProp Σ) (rr : option resv) :
    let ea := add_vec (m !!! Regidx rs1) (zeros' 64) in
    let sv := sign_extend' (Z.mul 8 (__id 4))
                (trunc (Z.mul (__id 4) 8) (m !!! Regidx rs2)) in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs))
      = ('b"1000" : mword 4) ->
    effectivePrivilege amoacc (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    uint rd <> 0 ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) amoacc)
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ resv_any cpu_id)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ∃ bytes : SailStdpp.Values.mword (8 * 4),
          ⌜mem_bytes_at σ pa 4 bytes⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ ∗ Rr bytes)) -∗
    (∀ bytes : SailStdpp.Values.mword (8 * 4),
       Rr bytes -∗ ∀ σ img log tv V, ⌜read_bytes σ.(mem) pa 4 = Some bytes⌝ -∗
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        mstate_interp σ -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs) (write_bytes σ.(mem) pa 4 sv) σ.(mdev)) ∗
             tso_interp_of riscv_eraGS img (write_bytes σ.(mem) pa 4 sv)
               (log ++ [PWMsg (snap_of pa 4 sv) (hart_agent cpu_id)])%list
               (vstep (hart_agent cpu_id) (S (length log))
                  (log ++ [PWMsg (snap_of pa 4 sv) (hart_agent cpu_id)])%list V)
             ∗ R bytes)) -∗
    swp (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                ∃ bytes : SailStdpp.Values.mword (8 * 4),
                gpr_file (<[Regidx rd
                            := regval_into_reg
                                 (sign_extend' 64
                                    (autocast (T := mword) bytes
                                     : mword (4 * 8)))]> m) ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R bytes ∗ resv_frag cpu_id None).
  Proof.
    intros ea sv Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL Hmode Hep HA Hord HR HW
      Hcov Hpallow Hram Hva Hpa Hrd.
    exact (swp_execute_AMOSWAP_S_ex_mode Drw Dro Df rs rs2 rs1 rd m pa pmar0
             pcfg paddr Rr R Rt rr Sv39 Hdisj HDmst HDpriv HDmenv HDsatp HDpma
             HDcfg HDaddr HDhtif Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL
             ltac:(rewrite Hmode; vm_compute; reflexivity)
             Hep HA Hord HR HW Hcov Hpallow Hram Hva Hpa Hrd).
  Qed.
End samo.
