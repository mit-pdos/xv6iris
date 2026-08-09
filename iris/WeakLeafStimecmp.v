(** * WeakLeafStimecmp.v — the weak leaf for [csrw stimecmp] (0x14D)

    The one register-only csrw whose [write_CSR] is NOT confined to its own
    CSR: the 0x14D clause runs [clint_dispatch false] between the register
    write and the read-back, which refreshes mip.MTIP (from mtimecmp <=u
    mtime) and — under Sstc with menvcfg.STCE — mip.STIP (from stimecmp <=u
    mtime).  So the successor state carries an EXTRA [mip] write whose value
    is existential, and the leaf has to move a cell it does not own: [mip]
    lives in [MinstretInv.clock_inv], bundled inside [minstret_inv].

    Two consequences shape this file, and neither shows up in
    [WeakLeafCsrw2]'s register-only template:

      - §1  every [exec_eff] mirror below the [execute] is EXISTENTIAL in the
            mip value ([exec_eff_write_CSR_stimecmp],
            [exec_eff_execute_csrw_stimecmp]), and the successor register
            tower is FOUR deep
            ([minstret_increment] / [nextPC] / [stimecmp] / [mip]), which is
            why this file states its own [stimecmp_sexec_facts] rather than
            reusing [WeakLeafRegOnly.csrw_sexec_facts_r] (three deep).

      - §2  the leaf OPENS [clock_inv] inside the funnel callback.  The
            callback's goal is [|={⊤ ∖ ↑minstretN, ∅}=> …] and
            [↑clockN ⊆ ⊤ ∖ ↑minstretN], so the open/update/close fits
            entirely BEFORE the [fupd_mask_intro] that drops to [∅]; see the
            comment at the [iInv] below for the exact sequence.  Getting at
            the invariant costs one destructuring of [mmode_config] at the
            top of the leaf ([hw_config] / [minstret_inv] are persistent) and
            an [mmode_config_rebuild] to hand the bundle to [wwp_instr]
            unchanged.

    §1 is the token-for-token [exec_eff] twin of [WpGprCsrwB]'s SC scripts
    ([exec_is_stimecmp_accessible_M] … [exec_execute_csrw_stimecmp]) under
    the usual substitutions ([exec_bind_Some] → [exec_eff_bind_nil],
    [exec_returnM] → [exec_eff_returnM], …), and the [clint_dispatch false]
    mirror it rests on is NOT restated here: [WeakTickEff] already proves
    [exec_eff_clint_dispatch_false] (the tick needs it too), so this file
    reuses it. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr.
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
Require Import WpGprCsrwCommon WpGprCsrwA WpGprCsrwB.
Require Import WeakLeafCsrw WeakLeafRegOnly.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The [exec_eff] mirrors, trace [[]] *)

(** *** 1a. The Sstc gate.

    [WeakLeafEffCommon] §2 stops at Ext_S / Ext_U / Zicsr / Zicfilp / Sv32 /
    Sv39; the [stimecmp] accessibility predicate is the only consumer of
    Ext_Sstc in the weak tree, and [WeakTickEff]'s copies of these two are
    [Local].  Same three-line script as every other [hartSupports] leaf. *)

Lemma exec_eff_hartSupports_Sstc s :
  exec_eff (hartSupports Ext_Sstc) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_currentlyEnabled_Sstc s :
  exec_eff (currentlyEnabled Ext_Sstc) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  cbn match. apply exec_eff_hartSupports_Sstc.
Qed.

(** *** 1b. Accessibility ([WpGprCsrwB.exec_is_stimecmp_accessible_M] /
    [exec_is_CSR_accessible_stimecmp]). *)

Lemma exec_eff_is_stimecmp_accessible_M s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (is_stimecmp_accessible Machine) s = Some (true, s, []).
Proof.
  intro HS. unfold is_stimecmp_accessible.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Sstc s)).
  cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_is_CSR_accessible_stimecmp s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (is_CSR_accessible csr_stimecmp Machine CSRWrite) s
    = Some (true, s, []).
Proof.
  intro HS. unfold is_CSR_accessible.
  skip_csr_false_clauses_eff.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  apply (exec_eff_is_stimecmp_accessible_M s HS).
Qed.

(** *** 1c. [write_CSR], existential in the mip value.

    [WpGprCsrwB.exec_write_CSR_stimecmp] verbatim.  Its two structural moves
    are load-bearing and replayed as-is:

      - [remember (clint_dispatch false) as CD] (NOT [set]): the CSR-clause
        peel's rewrites zeta-expand a let-bound body, and the moment
        [clint_dispatch] is exposed the surrounding [exec_eff] reduces it into
        a raw monad-bind fixpoint that no [rewrite] can fold back.  A
        body-less variable cannot be expanded.  ([remember] abstracts [Hcd]
        too, so [Hcd] is already stated at [CD] below.)
      - the [assert (HM …) by reflexivity] that folds the two binds the peel
        left delta-unfolded back into [Defs.bind]/[Defs.bind0] form. *)

Lemma exec_eff_write_CSR_stimecmp (v : mword 64) s :
  exists mp : mword 64,
  exec_eff (write_CSR csr_stimecmp v) s
    = Some (Ok (subrange_vec_dec
                  (stimecmp_legalized (register_lookup stimecmp s.(sregs)) v)
                  (Z.sub xlen 1) 0),
            set_reg (set_reg s stimecmp
                       (stimecmp_legalized
                          (register_lookup stimecmp s.(sregs)) v)) mip mp,
            []).
Proof.
  destruct (WeakTickEff.exec_eff_clint_dispatch_false
              (set_reg s stimecmp
                 (stimecmp_legalized (register_lookup stimecmp s.(sregs)) v)))
    as [mp Hcd].
  exists mp.
  unfold stimecmp_legalized in Hcd |- *.
  unfold write_CSR.
  remember (clint_dispatch false) as CD eqn:HCD.
  skip_csr_false_clauses_eff.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg stimecmp s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg stimecmp _ s)).
  (* the peel left the remaining two binds delta-unfolded into the raw monad
     fixpoint; [reflexivity] folds them back *)
  match goal with |- exec_eff ?M ?st = _ =>
    assert (HM : M = Defs.bind (Defs.bind0 CD (Defs.read_reg stimecmp))
                       (fun w : mword 64 =>
                          returnM (Ok (subrange_vec_dec w (Z.sub xlen 1) 0))))
      by reflexivity end.
  rewrite HM.
  match goal with |- exec_eff (Defs.bind ?A _) ?st = _ =>
    assert (Hin : exec_eff A st
                  = Some (register_lookup stimecmp st.(sregs),
                          set_reg st mip mp, [])) end.
  { rewrite (exec_eff_bind0_nil _ _ _ _ _ Hcd).
    rewrite (exec_eff_read_reg stimecmp _).
    rewrite sregs_set_reg.
    rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hin).
  rewrite sregs_set_reg. rewrite register_lookup_set.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_stimecmp (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_stimecmp d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_stimecmp d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

(** *** 1d. THE END-TO-END [execute] MIRROR, existential in mip.

    [WpGprCsrwB.exec_execute_csrw_stimecmp], stated at [execute (CSRReg …)]
    (the shape [wwp_cb] asks for) rather than at [execute_CSRReg]; the check
    goes through [WeakLeafRegOnly]'s csr-generic dispatchers, exactly as the
    SC proof goes through [exec_check_CSR_result_csrw]/[exec_check_CSR_csrw]. *)

Lemma exec_eff_execute_csrw_stimecmp (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exists mp : mword 64,
  exec_eff (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg s stimecmp
              (stimecmp_legalized (register_lookup stimecmp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    s.(sregs)))) mip mp,
            []).
Proof.
  intros Hrs1 Hpriv HS.
  change (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  destruct (exec_eff_write_CSR_stimecmp
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                      s.(sregs)) s)
    as [mp Hw].
  exists mp.
  apply (exec_eff_execute_csrw_gpr_p Machine csr_stimecmp rs1 s _
           (subrange_vec_dec
              (stimecmp_legalized (register_lookup stimecmp s.(sregs))
                 (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                         s.(sregs))) (Z.sub xlen 1) 0)).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_p Machine csr_stimecmp s).
    apply exec_eff_check_CSR_csrw_p;
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | apply (exec_eff_is_CSR_accessible_stimecmp s HS)
      | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exact Hw.
  - apply exec_eff_csr_id_write_callback_stimecmp.
Qed.

(* ====================================================================== *)
(** ** 1e. The FOUR-deep successor register frame

    [WeakLeafRegOnly.csrw_sexec_facts_r] with the extra [mip] write on top:
    the same five conclusions, one [set_lookup_ne] deeper.  (The generic
    lemma cannot be used directly — it is stated for a THREE-deep tower.) *)

Lemma stimecmp_sexec_facts (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) (v : type_of_register stimecmp)
    (p : type_of_register mip) :
  let s_exec :=
    set_reg (set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b)
                        nextPC npc) stimecmp v) mip p in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ mem s_exec = s0.(mem)
  /\ mdev s_exec = s0.(mdev)
  /\ register_lookup nextPC (sregs s_exec) = npc.
Proof.
  cbn zeta. split_and!.
  - rewrite (set_lookup_ne hart_state mip _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne hart_state stimecmp _ _ ltac:(reg_ne)).
    by rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne))
               (set_lookup_ne hart_state (R_bool minstret_increment)
                  _ _ ltac:(reg_ne)).
  - rewrite (set_lookup_ne (R_bool minstret_increment) mip _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne (R_bool minstret_increment) stimecmp
               _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - by rewrite !mem_set_reg.
  - by rewrite !mdev_set_reg.
  - rewrite (set_lookup_ne nextPC mip _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne nextPC stimecmp _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(* ====================================================================== *)
(** ** 2. THE LEAF

    [WeakLeafCsrw2]'s medeleg template with three deltas: the extra
    [stimecmp] cell, the four-deep successor, and the [clock_inv] block. *)

Section leaf_stimecmp.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrw_stimecmp_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (rs1v npc0 : SailStdpp.Values.mword 64)
      (stimecmp0 : type_of_register stimecmp)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       stimecmp ↦ᵣ stimecmp_legalized stimecmp0 rs1v -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
    (* THE CLOCK INVARIANT, HOISTED.  [mip] is written by this instruction's
       [write_CSR] but owned by nobody here: it lives in [clock_inv], which
       [mmode_config] carries (persistently) inside [minstret_inv].  Take a
       copy now and rebuild the bundle for [wwp_instr] -- [hw_config] and
       [minstret_inv] are persistent, so nothing is consumed. *)
    iDestruct "Hmm" as "(#Hhw & #Hmiv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (mstatus0) "(Hms & %HmIE0 & %HMPRV0 & %HSXL0 & %HKF0)".
    iDestruct (mmode_config_rebuild (DfracOwn q) mstatus0
                 HmIE0 HMPRV0 HSXL0 HKF0 with "Hhw Hmiv Hhs Hpriv Hms")
      as "Hmm".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* the funnel: certificate = nowrite at the fetch-only trace *)
    iApply (wwp_instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the two registers the funnel does not read: the source and the CSR *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat stimecmp σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ----
       its own existential [mp'] is destructed HERE and never related to the
       flat run's: the confined and flat states differ in memory, so the two
       [clint_dispatch]es may well compute different mip values, and neither
       recipe asks for a relation. *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hcsrc : register_lookup stimecmp
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = stimecmp0).
      { rewrite (set_lookup_ne stimecmp nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne stimecmp (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lcsr. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      destruct (exec_eff_execute_csrw_stimecmp rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HSc) as [mp' He].
      rewrite Hcsrc Hrs1c' in He.
      destruct (stimecmp_sexec_facts s0c b' (add_vec_int pc 4)
                  (stimecmp_legalized stimecmp0 rs1v) mp')
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hcsrf : register_lookup stimecmp
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = stimecmp0).
    { rewrite (set_lookup_ne stimecmp nextPC _ _ ltac:(reg_ne)).
      exact Lcsr_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    (* the mip value the funnel's successor carries comes out HERE, before the
       invariant is opened -- the close below re-supplies it. *)
    destruct (exec_eff_execute_csrw_stimecmp rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HSf) as [mp Hef].
    rewrite Hcsrf Hrs1f in Hef.
    (* ---- the three register writes the [execute] performs ----
       THE CLOCK-INVARIANT BLOCK.  The goal here is
       [|={⊤ ∖ ↑minstretN, ∅}=> …] and [↑clockN ⊆ ⊤ ∖ ↑minstretN], so [iInv]
       lands the goal at [|={(⊤ ∖ ↑minstretN) ∖ ↑clockN, ∅}=> …] with a
       closing wand back up to [⊤ ∖ ↑minstretN].  Doing both register updates
       and the close BEFORE [fupd_mask_intro] puts the mask back at
       [⊤ ∖ ↑minstretN], which is exactly [fupd_mask_intro]'s source. *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct "Hmiv" as "(_ & #Hclk & _)".
    iInv "Hclk" as ">Hcb" "Hclosec".
    iDestruct "Hcb" as (c0 t0 p0) "(Hc & Ht & Hp)".
    iMod (reg_update _ stimecmp _ (stimecmp_legalized stimecmp0 rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iMod (reg_update _ mip _ mp with "Hreg Hp") as "[Hreg Hp]".
    iMod ("Hclosec" with "[Hc Ht Hp]") as "_".
    { iNext. iExists c0, t0, mp. iFrame "Hc Ht Hp". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     stimecmp (stimecmp_legalized stimecmp0 rs1v)) mip mp).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (stimecmp_sexec_facts (wflat_st σ) b (add_vec_int pc 4)
                (stimecmp_legalized stimecmp0 rs1v) mp)
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_stimecmp.

(* ====================================================================== *)
(** ** 3. Soundness check *)

Print Assumptions exec_eff_execute_csrw_stimecmp.
Print Assumptions wwp_csrw_stimecmp_leaf.
