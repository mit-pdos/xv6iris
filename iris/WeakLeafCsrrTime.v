(** * WeakLeafCsrrTime.v — the weak [csrr a5, time] leaf (M4, start/timerinit)

    Seam 3 of the weak [start()]/[timerinit()] port: the weak twin of
    [WpGprCsrrB.wp_csrr_time_gpr], the CSR-READ counterpart of
    [WeakLeafCsrw2]'s register-only csrw leaves.

    THE ONE DESIGN FACT worth restating (it is what makes this leaf a
    register-only leaf and not an invariant-opening one): [mtime] lives in
    [clock_inv] and advances nondeterministically with the clock tick, so
    this leaf owns NO mtime cell and cannot pin the value the instruction
    reads — and it does NOT need to.  The [exec_eff] witness reads [mtime]
    straight off the abstract step state σ, so the leaf opens NO invariant
    anywhere; the read value [tv] is simply ∀-QUANTIFIED in the
    continuation, exactly as in the SC leaf, and instantiated in the proof
    with [wtime_val σ] — the mtime lookup at the callback's own σ, peeled
    past the funnel's two pre-writes so that the CONFINED-state and the
    FLAT-state [execute] instantiations produce the SAME value.

    Layout:

      §1  the [exec_eff] mirror of the csrr-time [execute] cone, at trace
          [[]] — [WpGprCsrrB]'s whole [time] block plus the CSR-READ spine
          ([WpGprCsrrCommon]'s [csrr_read_step_p] /
          [exec_check_CSR_read_p] / [exec_check_CSR_result_read_p] and the
          [read_CSR] dispatch walk [drive_csr]) mirrored under the usual
          substitutions ([exec_bind_Some] → [exec_eff_bind_nil], … ).  The
          spine is CSR-GENERIC, so a further csrr leaf owes only its own
          [read_CSR] mirror.  The PURE items ([csr_time], [time_rdval],
          [csr_access_type_CSRRS_true], [csr_dispatch_eq]) are REUSED from
          the SC files.
      §1b [wtime_val] / [time_rdval_prewrite] — the mtime peel past the
          funnel's [minstret_increment] and [nextPC] pre-writes.
      §2  the leaf [wwp_csrr_time_leaf], alignment-generic: the
          [WeakLeafCsrw2] medeleg TEMPLATE with the CSR/rs1 cells replaced
          by the single DESTINATION cell, on the plain funnel
          [WeakFunnel.wwp_instr], through the register-only kit
          ([WeakLeafRegOnly]) and the load-shape successor frame
          ([WeakLeafWin.load_sexec_facts]). *)
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
Require Import WpGprCsrrCommon WpGprCsrrB.
Require Import WeakLeafCsrw WeakLeafRegOnly.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE [exec_eff] MIRROR OF THE csrr-time CONE (trace [])

    Token-for-token replays of [WpGprCsrrB]'s [time] block and of
    [WpGprCsrrCommon]'s CSR-read spine, under the name swaps
    [exec_bind_Some] → [exec_eff_bind_nil], [exec_bind0_Some] →
    [exec_eff_bind0_nil], [exec_and_boolM_Some] → [exec_eff_and_boolM_nil],
    [exec_returnM]/[exec_returnm] → [exec_eff_returnM]/[exec_eff_returnm],
    [exec_read_reg]/[exec_write_reg] → their eff twins,
    [exec_wX_bits_gpr] → [WeakLeafEffCommon.exec_eff_wX_bits_gpr], and
    [drive_csr] → [drive_csr_eff] below.  The enablement chain
    ([exec_eff_currentlyEnabled_S] / [_U] / [_hartSupports_Zicsr] … ) is
    [WeakLeafEffCommon] §2's. *)

(** *** 1a. The Zicntr enablement chain (Zicntr is not in the shared kit —
    only the csrr-time path asks for it). *)

Lemma exec_eff_hartSupports_Zicntr s :
  exec_eff (hartSupports Ext_Zicntr) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicntr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_currentlyEnabled_Zicntr s :
  exec_eff (currentlyEnabled Ext_Zicntr) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicntr) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Zicntr s)).
  cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s));
    cbn match
  end.
  apply exec_eff_hartSupports_Zicntr.
Qed.

(** At Machine the counter gate is unconditionally open — neither
    [mcounteren] nor [scounteren] is consulted (both are read, and both
    reads are register-only, hence trace [[]]). *)
Lemma exec_eff_counter_enabled_machine (index : Z) s :
  exec_eff (counter_enabled index Machine) s = Some (true, s, []).
Proof.
  unfold counter_enabled.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mcounteren s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg scounteren s)).
  unfold feature_enabled_for_priv_bool.
  rewrite (exec_eff_bind_nil _ _ _ _ _
    (_ : exec_eff (feature_enabled_for_priv Machine _ _ _) s
         = Some (FEATURE_ENABLED, s, []))).
  2:{ unfold feature_enabled_for_priv. apply exec_eff_returnM. }
  apply exec_eff_returnM.
Qed.

(** *** 1b. The [read_CSR] dispatch walk, at [exec_eff]
    ([WpGprCsrrCommon.drive_csr]'s twin: [WeakLeafCsrw]'s batched
    false-clause peels first, then the single-clause loop that also settles
    the TRUE guard). *)

Ltac drive_csr_eff :=
  unfold read_CSR;
  repeat (erewrite exec_eff_if_false_g16 by (vm_compute; reflexivity));
  repeat (erewrite exec_eff_if_false_g4 by (vm_compute; reflexivity));
  repeat first
    [ erewrite exec_eff_if_false_g by (vm_compute; reflexivity)
    | match goal with
      | |- context[if ?g then _ else _] =>
          let v := eval vm_compute in g in
          lazymatch v with
          | true  => replace g with true by (vm_compute; reflexivity)
          | false => replace g with false by (vm_compute; reflexivity)
          end
      end; cbn match ].

Lemma exec_eff_read_CSR_time s :
  exec_eff (read_CSR csr_time) s
    = Some (subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0,
            s, []).
Proof.
  drive_csr_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mtime s)).
  apply exec_eff_returnM.
Qed.

(** *** 1c. The CSR-READ check kit, csr-generic
    ([WpGprCsrrCommon.exec_check_CSR_read_p] /
    [exec_check_CSR_result_read_p]'s mirrors; the CSRWrite twins are
    [WeakLeafRegOnly] §3's). *)

Lemma exec_eff_check_CSR_read_p (p : Privilege) (csr : mword 12) s :
  exec_eff (check_CSR_priv csr p) s = Some (true, s, []) ->
  check_CSR_access csr CSRRead = true ->
  exec_eff (is_CSR_accessible csr p CSRRead) s = Some (true, s, []) ->
  exec_eff (stateen_allows_CSR_access csr p CSRRead) s = Some (true, s, []) ->
  exec_eff (check_CSR csr p CSRRead) s = Some (true, s, []).
Proof.
  intros Hpriv Hca Hacc Hst. unfold check_CSR.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hpriv). cbn match.
  assert (HB : exec_eff (returnM (check_CSR_access csr CSRRead) : M bool) s
               = Some (true, s, []))
    by (rewrite exec_eff_returnM; rewrite Hca; reflexivity).
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ HB). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hacc). cbn match.
  exact Hst.
Qed.

Lemma exec_eff_check_CSR_result_read_p (p : Privilege) (csr : mword 12) s :
  exec_eff (check_CSR csr p CSRRead) s = Some (true, s, []) ->
  exec_eff (check_CSR_result csr p CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intro Hcc. unfold check_CSR_result.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hcc). cbn match.
  apply exec_eff_returnm.
Qed.

(** *** 1d. time's accessibility / check / callback *)

Lemma exec_eff_is_CSR_accessible_time s :
  exec_eff (is_CSR_accessible csr_time Machine CSRRead) s
    = Some (true, s, []).
Proof.
  assert (Hred : is_CSR_accessible csr_time Machine CSRRead
                 = Defs.and_boolM (currentlyEnabled Ext_Zicntr)
                                  (counter_enabled 1 Machine))
    by csr_dispatch_eq.
  rewrite Hred.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Zicntr s)).
  cbn match.
  apply exec_eff_counter_enabled_machine.
Qed.

Lemma exec_eff_check_CSR_result_time s :
  exec_eff (check_CSR_result csr_time Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  apply exec_eff_check_CSR_result_read_p.
  apply exec_eff_check_CSR_read_p.
  - assert (H : check_CSR_priv csr_time Machine = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
  - vm_compute; reflexivity.
  - apply exec_eff_is_CSR_accessible_time.
  - assert (H : stateen_allows_CSR_access csr_time Machine CSRRead
                = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
Qed.

Lemma exec_eff_csr_id_read_callback_time s (d : mword 64) :
  exec_eff (csr_id_read_callback csr_time d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_read_callback csr_time d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

(** The x0 source read the csrr spine starts with, DERIVED from the shared
    kit's [exec_eff_rX_bits_gpr] rather than re-proved ([WkEntryEff] keeps an
    identical private copy, proved from scratch; the statements agree). *)
Lemma exec_eff_rX_bits_x0 (i : mword 5) s :
  uint i = 0 -> exec_eff (rX_bits (Regidx i)) s = Some (zero_reg, s, []).
Proof. intro H. rewrite (exec_eff_rX_bits_gpr i s). by rewrite H. Qed.

(** *** 1e. The csrr SPINE ([WpGprCsrrCommon.csrr_read_step_p]'s mirror) —
    CSR-generic, privilege-generic; a further csrr leaf owes only its own
    [read_CSR] / accessibility / callback mirrors. *)

Lemma exec_eff_csrr_read_step_p (p : Privilege) (csr : mword 12)
    (rd : mword 5) (readval : mword 64) (s s_w : mstate) :
  register_lookup cur_privilege s.(sregs) = p ->
  exec_eff (check_CSR_result csr p CSRRead) s
    = Some (CSR_Check_OK tt, s, []) ->
  ext_check_CSR csr p CSRRead = true ->
  exec_eff (read_CSR csr) s = Some (readval, s, []) ->
  eq_vec csr ((Ox"344") : mword 12) = false ->
  eq_vec csr ((Ox"144") : mword 12) = false ->
  exec_eff (csr_id_read_callback csr readval) s = Some (tt, s, []) ->
  exec_eff (wX_bits (Regidx rd) readval) s = Some (tt, s_w, []) ->
  exec_eff (execute_CSRReg csr zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS, s_w, []).
Proof.
  intros Hpriv Hchk Hext Hread H344 H144 Hcb Hwx.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRS
             (SailStdpp.Instances.generic_eq (Regidx rd) zreg)
             (SailStdpp.Instances.generic_eq zreg zreg)) with CSRRead
    by (replace (SailStdpp.Instances.generic_eq zreg zreg) with true
          by (vm_compute; reflexivity);
        symmetry; apply csr_access_type_CSRRS_true).
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_rX_bits_x0 (zero_extend' 5 ('b"00")) s
                ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext. change (Riscv.rv64d.not true) with false. cbn match.
  replace (if SailStdpp.Instances.generic_neq CSRRead CSRWrite
           then read_CSR csr else returnM (zeros' 64))
    with (read_CSR csr) by reflexivity.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hread).
  rewrite H344 H144. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM readval s)).
  replace (SailStdpp.Instances.generic_eq CSRRead CSRRead) with true
    by reflexivity. cbn match.
  rewrite (exec_eff_bind0_nil _ _ _ _ _
    (_ : exec_eff (Defs.bind0 (csr_id_read_callback csr readval)
                     (wX_bits (Regidx rd) readval)) s
         = Some (tt, s_w, []))).
  2:{ rewrite (exec_eff_bind0_nil _ _ _ _ _ Hcb). exact Hwx. }
  apply exec_eff_returnM.
Qed.

(** *** 1f. The end-to-end csrr-time [execute], trace [] *)

Lemma exec_eff_execute_csrr_time_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (execute (CSRReg (csr_time, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (time_rdval s)), []).
Proof.
  intros Hrd Hpriv.
  change (execute (CSRReg (csr_time, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_time zreg (Regidx rd) CSRRS).
  apply (exec_eff_csrr_read_step_p Machine csr_time rd (time_rdval s) s _
           Hpriv).
  - apply (exec_eff_check_CSR_result_time s).
  - vm_compute; reflexivity.
  - apply exec_eff_read_CSR_time.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_csr_id_read_callback_time.
  - rewrite (exec_eff_wX_bits_gpr rd (time_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ====================================================================== *)
(** ** 1b. THE mtime PEEL

    The value the instruction reads, PINNED at the callback's own σ: the
    funnel hands the [execute] a state with two pre-writes on top
    ([minstret_increment] and [nextPC]), and neither touches [mtime], so the
    [time_rdval] of BOTH instantiations — the confined
    [MState (wm_regs σ) …] one (at the ∀-quantified flag [b']) and the flat
    [wflat_st σ] one (at the funnel's [b]) — is this ONE value.  That is
    what lets the leaf hand the same [tv] to the certificate, to the run,
    and to the continuation. *)

Definition wtime_val (σ : wmstate) : SailStdpp.Values.mword 64 :=
  subrange_vec_dec (register_lookup mtime (wm_regs σ)) (Z.sub xlen 1) 0.

Lemma time_rdval_prewrite (σ : wmstate) (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) :
  sregs s0 = wm_regs σ ->
  time_rdval (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
    = wtime_val σ.
Proof.
  intro Hs. unfold time_rdval, wtime_val.
  rewrite (set_lookup_ne mtime nextPC _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne mtime (R_bool minstret_increment) _ _ ltac:(reg_ne)).
  by rewrite Hs.
Qed.

(* ====================================================================== *)
(** ** 2. THE LEAF

    [WeakLeafCsrw2]'s medeleg template with three deltas and nothing else:
    the instruction is [CSRReg (csr_time, zreg, Regidx rd, CSRRS)] (no rs1,
    so the only operand premise is [uint rd <> 0]); the cells are the single
    DESTINATION GPR (no CSR cell — [mtime] is unowned, it lives in
    [clock_inv]); and the continuation is ∀-quantified over the read value
    [tv].  No invariant is opened. *)

Section leaf_csrr_time.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrr_time_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rd : mword 5) (rd0 npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_time, zreg, Regidx rd, CSRRS), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_time, zreg, Regidx rd, CSRRS), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ (tv : SailStdpp.Values.mword 64) (ws' : wstate),
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg tv -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrdc #Hbs Hhws Hcont".
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
    iApply (wwp_instr pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_time, zreg, Regidx rd, CSRRS))
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
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_time, zreg, Regidx rd, CSRRS)))
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
      pose proof (exec_eff_execute_csrr_time_gpr rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrdnz Hprivc) as He.
      rewrite (time_rdval_prewrite σ s0c b' (add_vec_int pc 4) eq_refl) in He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg (wtime_val σ)))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) D dst).
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
    pose proof (exec_eff_execute_csrr_time_gpr rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrdnz Hprivf) as Hef.
    rewrite (time_rdval_prewrite σ (wflat_st σ) b (add_vec_int pc 4) eq_refl)
      in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (wtime_val σ)) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (wtime_val σ))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg (wtime_val σ)))
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
    iApply ("Hcont" $! (wtime_val σ) (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrdc Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_csrr_time.

(* ====================================================================== *)
(** ** 3. Soundness check *)

Print Assumptions exec_eff_execute_csrr_time_gpr.
Print Assumptions wwp_csrr_time_leaf.
