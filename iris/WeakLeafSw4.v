(** * WeakLeafSw4.v — M4 batch 2: the [sw]-class 4-byte STORE leaf

    The width-4 replay of [WeakLeafSd8.v] (READ THAT FILE FIRST — it is the
    template and this file deliberately mirrors its section structure), over
    [WeakLeafLw4]'s 4+4 window: from the M-mode config bundle, the PC cell,
    [WeakFunnel.winstr] and the OWNED four-byte window at the effective
    address to [WP (Loop) {{ Φ }}].

    WHAT THE WIDTH CHANGES, AND WHAT IT DOES NOT:

      - THE CERTIFICATE IS FREE.  Width 4 is [WeakCert]'s native width:
        [WeakFetchEff.wcert_store_base4] IS this leaf's certificate, at the
        concrete fetch element and with [Q := wQ_store (Some cid) ea vw].
        (The width-generic family [WeakLeafSd8.wcert_store_w] subsumes it at
        [n := 4] — [wcert_store_w_4], the recorded regression check.)  So
        this file has NO §1 at all.
      - THE STORED VALUE IS A TRUNCATION.  At width 8 the store's
        [subrange_vec_dec vrs2 63 0] is the whole register; at width 4 it is
        the genuine low word [subrange_vec_dec rs2v 31 0], and the leaf's
        postcondition carries it: the window comes back as
        [ea ↦w₄{1} vw] with [vw] tied to the register by the premise
        [subrange_vec_dec rs2v 31 0 = vw] (a [vm_compute]/[reflexivity] at a
        real call site, the same move as the [add_vec … = ea] premise).
      - THE Q HALF IS THE [sd] 4-MOVE BLOCK AT WIDTH 4:
        [WeakStore.wpt4_at_elems] → [wlat4_store_prim] (retarget at
        [wQ_store]'s message) → [WeakGhost.wlog_update] (the log authority
        grows) → [wlat4_wpt4] with [wQ_store]'s [wV] conjunct as the floor.
        FULL fraction forced (the element retarget is a [ghost_map_update]).
      - THE RELEASE-DEPOSIT SURFACE is identical: [vwp_hold R ws] in,
        [monPred_at R (view_scl T)] out at [T = S (length (wm_log σ))].

    Reused rather than cloned: the SHARED kit [WeakLeafWin] — the 4+4 window
    [wwin pc ea 4] with its membership/nonzero/pinned/conf-text lemmas and
    the write-domain confinement [wwin_wdom], plus [set_lookup_ne] /
    [leaf_peel] / [reg_at_flat] / [store_regs_facts] / [wpt4_align] — and
    [WeakFetchEff.exec_eff_within_htif_w_false] (§1 there).

    EVERY PURE / GEOMETRY SIDE CONDITION IS A PREMISE; a real call site
    discharges each by [vm_compute], exactly as for the SC leaf. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
(* DELIBERATELY NOT [Require Import SailStdpp.Base] — the [Countable Arch.pa]
   instance trap; see [WeakLeafLd8.v]'s header comment. *)
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakFetchEff WeakLeafBase4.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
(* The shared window kit + register helpers ([wwin], [set_lookup_ne],
   [leaf_peel], [store_regs_facts], [reg_at_flat], [wpt4_align]). *)
Require Import WeakLeafWin.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE CERTIFICATE — nothing to prove

    [WeakFetchEff.wcert_store_base4] is this leaf's certificate on the nose;
    §3 consumes it directly. *)

(* ====================================================================== *)
(** ** 2. THE WINDOW AND THE [wP_eff] HALF

    *** 2a/2b. The window and every window obligation are the SHARED kit's
    ([WeakLeafWin]): [wwin pc ea 4] with [wwin_nonzero] / [wwin_pinned] /
    [wwin_conf_text], and the WRITE-DOMAIN CONFINEMENT [wwin_wdom]. *)

(** [SailStdpp.Values] is imported for the ['b"…"] literal notation; every
    [gset Arch.pa] lives in [WeakLeafWin] (the instance trap — durable
    notes). *)
Import SailStdpp.Values.

(** *** 2c. THE SECOND INSTANTIATION — the whole per-instruction cost.

    [WeakLeafBase4.exec_eff_execute_STORE_4_gpr] at an ARBITRARY [s0] with
    the funnel's two pre-writes on top, so the confined and the flat
    instantiation are literally this lemma applied twice.  The stored value
    is handed over ALREADY TRUNCATED, through the premise
    [subrange_vec_dec vs 31 0 = vw], so every consumer downstream (the trace,
    the certificate's message, the [↦w₄] rebuild) speaks only [vw]. *)

Lemma exec_eff_sw4_at (s0 : mstate) (b : bool)
    (pc : SailStdpp.Values.mword 64) (rs1 rs2 : mword 5) (imm : mword 12)
    (ea : Arch.pa) (vs : SailStdpp.Values.mword 64) (vw : bv 32) :
  register_lookup cur_privilege s0.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s0.(sregs))) ('b"1")
    = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s0.(sregs)))
    = PMM_Disabled ->
  pmp_all_off (register_lookup pmpcfg_n s0.(sregs)) ->
  pma_allows_all (register_lookup pma_regions s0.(sregs)) ->
  register_lookup htif_tohost_base s0.(sregs) = None ->
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s0.(sregs))
          (sign_extend' 64 imm) = ea ->
  (if Z.eqb (uint rs2) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s0.(sregs))
    = vs ->
  subrange_vec_dec vs 31 0 = vw ->
  is_aligned_paddr (Physaddr ea) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) ->
  exec_eff (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
    (set_reg (set_reg s0 (R_bool minstret_increment) b)
             nextPC (add_vec_int pc 4))
  = Some (RETIRE_SUCCESS,
          MState (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b)
                          nextPC (add_vec_int pc 4)))
                 (write_bytes s0.(mem) ea 4 vw) s0.(mdev),
          [WEwrite wak_plain ea 4 vw]).
Proof.
  intros Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hvs Hvw Hal Hram4.
  assert (Hram : addr_is_ram ea)
    by (rewrite -(pa_add_0 ea); apply (Hram4 0%nat); lia).
  assert (Hram3 : addr_is_ram (pa_add ea 3)) by (apply Hram4; lia).
  destruct (pma_all_ram Lpma ea 4
              (pma_access_ram _ _ _ Hram Hram3
                 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & _ & _ & Hwrite & _).
  set (s := set_reg (set_reg s0 (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 4)).
  (* every config register, moved past the funnel's two pre-writes *)
  assert (Lpriv_s : register_lookup cur_privilege s.(sregs) = Machine)
    by (unfold s; leaf_peel cur_privilege; exact Lpriv).
  assert (Lms_s : register_lookup mstatus s.(sregs)
                  = register_lookup mstatus s0.(sregs))
    by (unfold s; leaf_peel mstatus; reflexivity).
  assert (Lsec_s : register_lookup mseccfg s.(sregs)
                   = register_lookup mseccfg s0.(sregs))
    by (unfold s; leaf_peel mseccfg; reflexivity).
  assert (Lpmpc_s : register_lookup pmpcfg_n s.(sregs)
                    = register_lookup pmpcfg_n s0.(sregs))
    by (unfold s; leaf_peel pmpcfg_n; reflexivity).
  assert (Lpma_s : register_lookup pma_regions s.(sregs)
                   = register_lookup pma_regions s0.(sregs))
    by (unfold s; leaf_peel pma_regions; reflexivity).
  assert (Lhtif_s : register_lookup htif_tohost_base s.(sregs) = None)
    by (unfold s; leaf_peel htif_tohost_base; exact Lhtif).
  (* the base register, uniform over [rs1] (x0 -> zero_reg) *)
  assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                          s.(sregs))
                  = (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            s0.(sregs))).
  { destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs1))); reflexivity. }
  (* the data register, ditto over [rs2] *)
  assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                          s.(sregs)) = vs).
  { destruct (Z.eqb (uint rs2) 0) eqn:Ez; [exact Hvs|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs2))). exact Hvs. }
  (* the two identity bridges the model's [Let]s need *)
  assert (Ha4 : zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (sign_extend' 64 imm)) (xlen - 0 - 1) 0) = ea).
  { rewrite Hbase Hea zero_extend'_id subrange_id. reflexivity. }
  assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (sign_extend' 64 imm)) (xlen - 0 - 1) 0)) (0 * 4)) = ea).
  { rewrite Hbase Hea !zero_extend'_id subrange_id.
    change (0 * 4) with 0. rewrite avi0. reflexivity. }
  rewrite -Hvw -Hdata -Hpa.
  apply (exec_eff_execute_STORE_4_gpr rs2 rs1 imm region s Lpriv_s).
  - rewrite Lms_s. exact Lmprv.
  - rewrite Lsec_s. exact Lpmm.
  - rewrite Ha4. unfold is_aligned_vaddr. unfold is_aligned_paddr in Hal.
    exact Hal.
  - apply exec_eff_pmpCheck_machine_none.
    intro i. rewrite Lpmpc_s. exact (proj1 (Lpmp i)).
  - rewrite Lpma_s Hpa. exact Hmatch.
  - rewrite Hpa. exact Hal.
  - exact Hwrite.
  - rewrite Hpa.
    exact (exec_eff_within_clint_false ea 4 s
             (addr_is_ram_not_in_clint _ Hram) ltac:(lia)).
  - rewrite Hpa.
    exact (exec_eff_within_sig_false ea 4 s
             (addr_is_ram_not_in_sig _ Hram) ltac:(lia)).
  - rewrite Hpa. exact (exec_eff_within_htif_w_false ea 4 s Lhtif_s).
  - rewrite Hpa. exact (addr_is_ram_not_dev _ Hram).
Qed.

(** The successor's register frame is [WeakLeafWin.store_regs_facts] —
    width-independent (a store writes no register; the [MState] wrapper is
    conversion) — reused, not cloned. *)

(** *** 2d. THE [wP_eff] HALF, as a standalone lemma over the resources. *)

Section wP_eff_half.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wP_eff_sw4 (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rs2 : mword 5) (imm : mword 12)
      (ea : Arch.pa) (vold : bv 32) (vs : SailStdpp.Values.mword 64)
      (vw : bv 32) (dq : dfrac) (D : register -> bool) (dst : mstate) :
    wlog_wf (wm_log σ) ->
    (* --- the M-mode config tower, at σ's own registers --- *)
    register_lookup PC (wm_regs σ) = pc ->
    register_lookup cur_privilege (wm_regs σ) = Machine ->
    pmp_all_off (register_lookup pmpcfg_n (wm_regs σ)) ->
    pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
    register_lookup htif_tohost_base (wm_regs σ) = None ->
    register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ)))
      = PMM_Disabled ->
    eq_vec (register_lookup elp (wm_regs σ))
           (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (* --- the instruction's pure geometry --- *)
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (sign_extend' 64 imm) = ea ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) (wm_regs σ))
      = vs ->
    subrange_vec_dec vs 31 0 = vw ->
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) ->
    (* --- the decode, exactly as the decode library states it --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), dst) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_Base w) -∗
    vwp_hold (wpt4 ea dq vold) (wm_ws σ) -∗
    ⌜wP_eff (Some cid)
       ([WEread wak_plain pc 4] ++ [WEwrite wak_plain ea 4 vw]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp
           Hal4 HnotRVC Hea Hvs Hvw Hram4 Hagree HDmi Hgood Hdec.
    iIntros "Hlat #Hbs Hpt".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iDestruct (winstr_bytes_lookup σ pc (F_Base w) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpinpc.
    iDestruct (wpt4_flat_pin σ ea dq vold Hwf with "Hlat Hpt")
      as %[Haccea Hflatpin].
    iDestruct (wpt4_align with "Hpt") as %Halea.
    iPureIntro.
    assert (Hpinea : forall j : nat, (j < 4)%nat ->
              pinned_read σ (acc_addr ea j))
      by (intros j Hj; exact (proj2 (Hflatpin j Hj))).
    destruct Hfok as (Hal2 & Hrampc & w' & [Hww _] & Htext). subst w'.
    apply (wP_eff_of_leaf_base cid σ (wwin pc ea 4) pc w
             (STORE (imm, Regidx rs2, Regidx rs1, 4))
             [WEwrite wak_plain ea 4 vw] D dst).
    - exact Hwf.
    - exact (wwin_nonzero pc ea 4 Hrampc Hram4).
    - exact (wwin_pinned σ pc ea 4 Haccpc Haccea Hpinpc Hpinea).
    - exact Lpc.
    - exact Lpriv.
    - exact (pmp_all_off_allows_all _ Lpmp).
    - exact Lpma.
    - exact Lhtif.
    - exact Lhart.
    - exact LmisaS.
    - exact LmIE.
    - exact Lelp.
    - exact Hal4.
    - exact Hrampc.
    - exact (wwin_conf_text σ pc ea 4 w Htext).
    - exact HnotRVC.
    - exact Hagree.
    - exact HDmi.
    - exact Hgood.
    - exact Hdec.
    - reflexivity.
    - intro b. eexists. split_and!.
      + exact (exec_eff_sw4_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 4))
                    (wm_dev σ)) b pc rs1 rs2 imm ea vs vw
                 Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hvs Hvw Halea Hram4).
      + exact (eq_trans (proj1 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 4))
                      (wm_dev σ)) b (add_vec_int pc 4))) Lhart).
      + exact (proj1 (proj2 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 4))
                      (wm_dev σ)) b (add_vec_int pc 4)))).
      + exact (wwin_wdom σ pc ea 4 vw).
  Qed.

End wP_eff_half.

(* ====================================================================== *)
(** ** 3. THE LEAF

    Read the statement against [WeakLeafSd8.wwp_sd8_leaf]: the width and the
    resource changed ([↦w₈] → [↦w₄]) and the stored value is the truncation
    [vw] (tied to [rs2v] by the [subrange_vec_dec rs2v 31 0 = vw] premise);
    everything else — the release payload [R], the leaf-chosen timestamp
    [T = S (length (wm_log σ))] with its per-byte floor fact, the forced FULL
    fraction — is the 8-byte statement verbatim. *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_sw4_leaf Φ
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rs2 : mword 5) (imm : mword 12)
      (ea : Arch.pa) (vold : bv 32) (vw : bv 32) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v rs2v npc0 : SailStdpp.Values.mword 64)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    subrange_vec_dec rs2v 31 0 = vw ->
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), t)) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt4 ea (DfracOwn 1) vold) ws -∗
    vwp_hold R ws -∗
    (∀ (ws' : wstate) (T : nat),
       ⌜ws_le ws ws'⌝ -∗
       ⌜forall j : nat, (j < 4)%nat ->
          (T <= flr (ws_view ws') (acc_addr ea j))%nat⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt4 ea (DfracOwn 1) vw) ws' -∗
       monPred_at R (view_scl T) -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal4 Hrs1nz Hrs2nz Hea Hvw Hram4 Hdecf Hagree HDmi
           Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* THE WHOLE config goes to the funnel: it hands the reads back. *)
    iApply (wwp_instr Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 4))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 ([WEread wak_plain pc 4] ++ [WEwrite wak_plain ea 4 vw]))
              (wQ_store (Some (fin_to_nat cpu_id)) ea vw)
              Hgid Haccpc (pmp_all_off_allows_all _ Hpmp)
              (wcert_store_base4 (fin_to_nat cpu_id) pc wak_plain ea vw)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (STORE (imm, Regidx rs2, Regidx rs1, 4))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    (* the config, as the funnel read it (seam 2) *)
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    (* the TWO registers the funnel does not read: base and data *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a)   as Lrs1.
    iDestruct (reg_valid with "Hreg Hrs2c") as %Lrs2_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs2))) σ b eq_refl))
                  Lrs2_a)   as Lrs2.
    (* the effective address and the stored value, at σ's own register file *)
    assert (Hea_σ : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            (wm_regs σ)) (sign_extend' 64 imm) = ea).
    { rewrite (proj2 (Z.eqb_neq (uint rs1) 0) Hrs1nz) Lrs1. exact Hea. }
    assert (Hvs_σ : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                            (wm_regs σ)) = rs2v).
    { rewrite (proj2 (Z.eqb_neq (uint rs2) 0) Hrs2nz). exact Lrs2. }
    (* the agreement, at σ's registers *)
    assert (Hag_σ : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)).
    { apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]. }
    (* ---- the certificate's precondition (§2d) ---- *)
    iDestruct (wP_eff_sw4 (fin_to_nat cpu_id) σ pc w rs1 rs2 imm ea vold rs2v
                 vw (DfracOwn 1) D dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) Lpma
                 Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp Hal4 HnotRVC Hea_σ
                 Hvs_σ Hvw Hram4 Hag_σ HDmi Hgood Hdec with "Hlat Hbs Hpt")
      as %HP.
    iDestruct (wpt4_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state: the SC [execute] fact ---- *)
    pose proof (exec_eff_sw4_at (wflat_st σ) b pc rs1 rs2 imm ea rs2v vw Lpriv
                  Lmprv Lpmm ltac:(rewrite Lpmpc; exact Hpmp) Lpma Lhtif Hea_σ
                  Hvs_σ Hvw Halea Hram4) as Hexf.
    (* ---- the ONE register write the wrapper expects: nextPC ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (MState (sregs (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4)))
                    (write_bytes (mem (wflat_st σ)) ea 4 vw)
                    (mdev (wflat_st σ))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    (* the device frame (seam 1): the [execute] moved no device *)
    assert (Hdevt : mdev t = wm_dev σ) by (rewrite Hdevt0; reflexivity).
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf'
                       & Hbnd').
    destruct HQ as (HQi & HQl & HQle & HQv).
    (* the release deposit: freeze R at the store's own timestamp *)
    iDestruct (wwp_release_deposit R σ Hbnd with "HR") as "HRdep".
    (* THE WINDOW UPDATE: retarget the four elements at the message [wQ_store]
       names (failure mode 3 of the porting guide, discharged) *)
    iDestruct (wpt4_at_elems with "Hpt") as "(%Halea2 & %Haccea & Hels)".
    iDestruct "Hels" as (t0 t1 t2 t3) "(H0 & H1 & H2 & H3)".
    iMod (wlat4_store_prim (Some (fin_to_nat cpu_id)) σ ea vw
            with "Hlat H0 H1 H2 H3") as "[Hlat Hl4]".
    (* the log authority grows by the SAME message *)
    iMod (wlog_update (wm_log σ)
            [wwrite_msg (Some (fin_to_nat cpu_id)) ea 4 vw]
            with "Hlogauth") as "Hlogauth".
    (* the hart's own view cell moves to σ' *)
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+4] *)
    iEval (cbn [sregs]) in "Hpc'".
    iEval (rewrite (proj2 (proj2 (store_regs_facts (wflat_st σ) b
             (add_vec_int pc 4))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    (* the config comes back WHOLE from the funnel: nothing to recombine *)
    iApply ("Hcont" $! (wm_ws σ') (S (length (wm_log σ))) with
              "[%] [%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hrs2c Hhws [Hl4] HRdep").
    - exact Hwsle.
    - intros j Hj. apply HQv. exact Hj.
    - (* the window, rebuilt at the successor's view AT THE STORED VALUE:
         [wQ_store]'s view conjunct is exactly [wlat4_wpt4]'s floor premise *)
      iApply (wlat4_wpt4 ea (DfracOwn 1) (S (length (wm_log σ))) vw
                (wm_ws σ') Halea2 Haccea
                ltac:(intros j Hj; apply HQv; exact Hj) with "Hl4").
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions wcert_store_base4.
Print Assumptions wP_eff_sw4.
Print Assumptions wwp_sw4_leaf.
