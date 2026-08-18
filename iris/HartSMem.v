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
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMPmp HartMFetch HartMFrame
        HartMLoad HartMStore.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec.
Require Import RegFile WpGpr.
Require Import WpMmodeLeafBase SmodePte PtTreeAdue.
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
     Defs.returnR Defs.read_reg Defs.early_return Defs.throw
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
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Local Ltac sm_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

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
  apply (hfrun_bindm _ 6 10 D Drw rs rs rs _ _ Sv39 (Virtaddr a));
    [ lia
    | exact (hfrun_translationMode_S_sv39 D Drw rs HDmst HDsatp HSXL Hmode)
    | ].
  sm_cbn.
  change (Instances.generic_eq Sv39 Bare) with false.
  cbn match.
  unfold pm_transform_VA.
  change (xlen - 0 - 1) with 63.
  rewrite subrange_full_64 sign_extend'_id.
  apply hfrun_ret.
Qed.
