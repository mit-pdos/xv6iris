(* WpMmodeCsrSwp.v -- the CSR-write instructions' [swp] machinery.

   [execute_CSRReg csr rs1 zreg CSRRW] splits into exactly three kinds of
   step, and each gets the route its kind allows:

   - [check_CSR_result csr Machine CSRWrite] is READ-ONLY (its exec fact
     returns the state unchanged) but four levels of guarded recursion deep
     ([currentlyEnabled Ext_S] is a nested [and_boolM] chain).  So it goes
     through [HartGoodb.hval_of_goodb], exactly as [update_elp_state] does in
     WpMmodeJump: [goodb] is [vm_compute]d at [dstateM] and the exec fact is
     the one the exec-based stack already proved.  Its read set is
     [WpDecodeBridge.D_m] = cur_privilege / mseccfg / misa, which is why
     [cw_Dro] is exactly those three and no widening is needed.

   - [rX_bits rs1] is at a SYMBOLIC index, so no walker takes it; the leaf
     peels it with [HartMFrame.swp_rX_file].

   - [write_CSR csr v] WRITES, so [goodb] is unavailable -- but at a CONCRETE
     csr it reduces to three nodes at that one register, so [hfrun] walks it.
     That is the only per-CSR work, ~10 lines each.

   [csr_id_write_callback csr d] needs no route at all: at a concrete csr it
   is [returnM tt] by [vm_compute], a pure term equation. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        HartSpanChar HartRegNode HartMCycle RegFile WpGpr.
Require Import ColdBoot.
Require Import RiscvExtras RiscvFetchExec WpMmodeLeafBase HartMFrame
        ExecCommon HartMRun HartGoodb WpDecodeBridge.
Local Open Scope Z_scope.

(* collapse the closed [Z.eqb] tests of the model's rX/wX cascades *)
Local Ltac zt :=

  repeat match goal with
  | |- context [ if ?b then _ else _ ] =>
      assert_fails (is_var b);
      let x := eval vm_compute in b in
      lazymatch x with true => change b with true
                     | false => change b with false end
  end.


Require Import WpMmodeJump WpGprCsrwCommon.

Section csrw.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the file: the written CSR on top of the three config pins *)
  Definition cw_rs (r : register) (v0 : type_of_register r) : regstate :=
    register_set r v0
      (register_set misa MISA_C
         (register_set mseccfg (Values.mword_of_int 0)
            (register_set cur_privilege Machine init_regstate))).

  (* "the written register is none of the three config pins" -- every CSR leaf
     discharges this by [vm_compute] *)
  Definition cw_fresh (r : register) : Prop :=
    register_beq misa r = false /\
    register_beq mseccfg r = false /\
    register_beq cur_privilege r = false.

  Lemma cw_rs_r (r : register) (v0 : type_of_register r) :
    register_lookup r (cw_rs r v0) = v0.
  Proof. rewrite /cw_rs. apply register_lookup_set. Qed.

  Lemma cw_rs_misa (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup misa (cw_rs r v0) = MISA_C.
  Proof.
    intros (H1 & _ & _). rewrite /cw_rs.
    etransitivity; [apply irrelevant_register_set; exact H1|].
    apply register_lookup_set.
  Qed.

  Lemma cw_rs_sec (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup mseccfg (cw_rs r v0) = Values.mword_of_int 0.
  Proof.
    intros (_ & H2 & _). rewrite /cw_rs.
    etransitivity; [apply irrelevant_register_set; exact H2|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  Lemma cw_rs_priv (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup cur_privilege (cw_rs r v0) = Machine.
  Proof.
    intros (_ & _ & H3). rewrite /cw_rs.
    etransitivity; [apply irrelevant_register_set; exact H3|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  Definition cw_Df (dq : dfrac) : register -> dfrac := fun r' =>
    if decide (r' = (misa : register)) then DfracDiscarded
    else if decide (r' = (mseccfg : register)) then DfracDiscarded
    else dq.

  Ltac cwdf :=
    unfold cw_Df;
    repeat first [ rewrite decide_True; [reflexivity|reflexivity]
                 | rewrite decide_False; [|discriminate] ];
    reflexivity.

  Lemma cw_Df_misa dq : cw_Df dq misa = DfracDiscarded.
  Proof. cwdf. Qed.
  Lemma cw_Df_sec dq : cw_Df dq mseccfg = DfracDiscarded.
  Proof. cwdf. Qed.
  Lemma cw_Df_priv dq : cw_Df dq cur_privilege = dq.
  Proof. cwdf. Qed.

  Lemma cw_disj (r : register) : cw_fresh r -> cw_Drw r ## cw_Dro.
  Proof.
    intros (H1 & H2 & H3). rewrite /cw_Drw /cw_Dro.
    apply disjoint_singleton_l. intro Hin.
    repeat (apply elem_of_union in Hin as [Hin|Hin]);
      apply elem_of_singleton in Hin; subst r.
    all: first [ vm_compute in H1; discriminate
               | vm_compute in H2; discriminate
               | vm_compute in H3; discriminate ].
  Qed.

  Lemma cw_w_r (r : register) : r ∈ cw_Drw r.
  Proof. rewrite /cw_Drw. set_solver. Qed.
  Lemma cw_in_r (r : register) : r ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Drw. set_solver. Qed.
  Lemma cw_in_priv (r : register) : (cur_privilege : register) ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.
  Lemma cw_in_sec (r : register) : (mseccfg : register) ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.
  Lemma cw_in_misa (r : register) : (misa : register) ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.

  (* cells <-> the four-cell frame *)
  Lemma cw_frames (dq : dfrac) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame (cw_rs r v0) (cw_Drw r) ∗
     hreg_frame_ro (cw_Df dq) (cw_rs r v0) cw_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto r (DfracOwn 1) v0 ∗
        reg_pointsto cur_privilege dq Machine ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hfr.
    rewrite /hreg_frame /hreg_frame_ro /cw_Drw /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite cw_rs_r (cw_rs_priv r v0 Hfr) (cw_rs_sec r v0 Hfr)
      (cw_rs_misa r v0 Hfr).
    rewrite (cw_Df_priv dq) (cw_Df_sec dq) (cw_Df_misa dq).
    by rewrite !bi.sep_assoc.
  Qed.

  (* the read-only prefix, transported by [goodb] from the exec stack's fact *)
  Lemma hval_check_CSR_result_csrw (D Drw : gset register) (rs : regstate)
      (csr : SailStdpp.Values.mword 12) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    goodb D_m (check_CSR_result csr Machine CSRWrite) dstateM = true ->
    exec (check_CSR_result csr Machine CSRWrite) dstateM
      = Some (CSR_Check_OK tt, dstateM) ->
    hval D Drw rs (check_CSR_result csr Machine CSRWrite)
      (CSR_Check_OK tt) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm Hgb Hex.
    exact (hval_of_goodb D_m D Drw _ dstateM rs (CSR_Check_OK tt)
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm) Hgb Hex).
  Qed.

  (* [Ox"..."] is not available in this import context (stdpp's monadic
     pattern notation shadows the literal syntaxes), so the two mip/sip CSR
     numbers are spelled out. *)
  Local Notation csr344 :=
    (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 12)
       (HexString.Raw.to_N "344" 0)).
  Local Notation csr144 :=
    (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 12)
       (HexString.Raw.to_N "144" 0)).

  (* ------------------------------------------------------------------ *)
  (* [doCSR] at CSRRW with rd = x0, peeled.  Mirrors                      *)
  (* [WpGprCsrwCommon.exec_doCSR_csrw_p] step for step; the per-CSR facts  *)
  (* (the check's goodb + exec, the write's hfrun, the callback's pure     *)
  (* equation) are premises, so this lemma is written once for all ten.    *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_doCSR_csrw (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rs' : regstate) (csr : SailStdpp.Values.mword 12)
      (v cfinal : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    ext_check_CSR csr Machine CSRWrite = true ->
    goodb D_m (check_CSR_result csr Machine CSRWrite) dstateM = true ->
    exec (check_CSR_result csr Machine CSRWrite) dstateM
      = Some (CSR_Check_OK tt, dstateM) ->
    (if eq_vec csr csr344 then read_mip IncludePlatformInterrupts
     else if eq_vec csr csr144 then read_sip IncludePlatformInterrupts
     else returnM (zeros' 64)) = (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* the write as an OBLIGATION, not an [hfrun] fact: medeleg and mcounteren
       are three nodes at one register and discharge it by [swp_hfrun], but
       menvcfg and mepc wrap a READ-ONLY legalization several [hartSupports] /
       [currentlyEnabled] levels deep around their store -- goodb territory --
       and since that sits INSIDE a function that writes, goodb cannot take
       [write_CSR] whole.  So the lemma stops naming HOW the write happens. *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr v)
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)) -∗
    swp (doCSR csr v zreg CSRRW CSRWrite)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa Hext Hgb Hex Hmip Hcb.
    iIntros "#Hcert Hrw Hro Hwr".
    unfold doCSR.
    (* 1. cur_privilege *)
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p) "(-> & Hrw & Hro)". rewrite Hpriv.
    (* 2. the legality check, goodb-transported *)
    iApply (swp_bind_use (check_CSR_result csr Machine CSRWrite) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ (CSR_Check_OK tt) Hdisj
                (hval_check_CSR_result_csrw (Drw ∪ Dro) Drw rs csr HDpriv
                   HDsec HDmisa Hpriv Hsec Hmisa Hgb Hex)
                with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". cbn match.
    (* 3. cur_privilege again, then the pure gates *)
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p2) "(-> & Hrw & Hro)". rewrite Hpriv Hext.
    change (Riscv.rv64d.not true) with false. cbn match.
    replace (if Instances.generic_neq CSRWrite CSRWrite then read_CSR csr
             else returnM (zeros' 64))
      with (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) by reflexivity.
    iApply (swp_bind_use (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = zeros' 64⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (rv) "(-> & Hrw & Hro)".
    rewrite Hmip.
    iApply (swp_bind_use (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = zeros' 64⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (rv2) "(-> & Hrw & Hro)".
    replace (Instances.generic_eq CSRWrite CSRRead) with false
      by reflexivity. cbn match.
    (* 4. the write -- a computed walk at the ONE concrete CSR *)
    iApply (swp_bind_use (write_CSR csr v) _ _ _ with "[Hwr Hrw Hro] [-]").
    { iApply ("Hwr" with "Hrw Hro"). }
    iIntros (wres) "(-> & Hrw & Hro)". cbn match.
    (* 5. the discarded x0 write and the pure callback *)
    iApply (swp_bind0_use _ _
              (fun _ => hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)%I _
                with "[Hrw Hro] [-]").
      { change (wX_bits zreg (zeros' 64)) with (Defs.returnm tt : M unit).
        iApply swp_ret. by iFrame. }
      iIntros (u) "[Hrw Hro]". rewrite Hcb. iApply swp_ret. by iFrame. }
    iIntros (u2) "[Hrw Hro]". iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [execute_CSRReg csr rs1 x0 CSRRW]: peel the ONE symbolic-index node    *)
  (* and hand the rest to [swp_doCSR_csrw].  [gpr_file] rides beside the    *)
  (* frame -- the GPRs are deliberately NOT in the footprint.               *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_execute_CSRReg_csrw (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate) (m : regfile)
      (csr : SailStdpp.Values.mword 12) (rs1 : SailStdpp.Values.mword 5)
      (cfinal : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    ext_check_CSR csr Machine CSRWrite = true ->
    goodb D_m (check_CSR_result csr Machine CSRWrite) dstateM = true ->
    exec (check_CSR_result csr Machine CSRWrite) dstateM
      = Some (CSR_Check_OK tt, dstateM) ->
    (if eq_vec csr csr344 then read_mip IncludePlatformInterrupts
     else if eq_vec csr csr144 then read_sip IncludePlatformInterrupts
     else returnM (zeros' 64)) = (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr (m !!! Regidx rs1))
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)) -∗
    swp (execute_CSRReg csr (Regidx rs1) zreg CSRRW)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa Hext Hgb Hex Hmip Hcb.
    iIntros "#Hcert Hf Hrw Hro Hwr".
    unfold execute_CSRReg.
    replace (csr_access_type CSRRW (Instances.generic_eq zreg zreg)
               (Instances.generic_eq (Regidx rs1) zreg))
      with CSRWrite
      by (replace (Instances.generic_eq zreg zreg) with true by reflexivity;
          reflexivity).
    iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs1 m with "Hcert Hf"). }
    iIntros (v) "[-> Hf]".
    iApply (swp_mono with "[Hf] [Hrw Hro Hwr]");
      [| iApply (swp_doCSR_csrw Drw Dro Df rs rs' csr (m !!! Regidx rs1)
                   cfinal Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa Hext
                   Hgb Hex Hmip Hcb with "Hcert Hrw Hro Hwr") ].
    iIntros (e) "(-> & Hrw & Hro)". iSplitR; [done|]. iFrame.
  Qed.

  (* the post-write file: [write_CSR] leaves a [register_set], which agrees
     with the tower that simply NAMES the new value *)
  Lemma cw_set_agree (r : register) (v0 vnew : type_of_register r) :
    cw_fresh r ->
    reg_agree_on (cw_Drw r ∪ cw_Dro)
      (register_set r vnew (cw_rs r v0)) (cw_rs r vnew).
  Proof.
    intros Hfr r' Hr'.
    pose proof Hfr as Hfr2. destruct Hfr2 as (H1 & H2 & H3).
    rewrite /cw_Drw /cw_Dro in Hr'.
    repeat (apply elem_of_union in Hr' as [Hr'|Hr']);
      apply elem_of_singleton in Hr'; subst r'.
    - etransitivity; [apply register_lookup_set|]. symmetry. apply cw_rs_r.
    - etransitivity; [apply irrelevant_register_set; exact H3|].
      etransitivity; [apply (cw_rs_priv r v0 Hfr)|].
      symmetry. apply (cw_rs_priv r vnew Hfr).
    - etransitivity; [apply irrelevant_register_set; exact H2|].
      etransitivity; [apply (cw_rs_sec r v0 Hfr)|].
      symmetry. apply (cw_rs_sec r vnew Hfr).
    - etransitivity; [apply irrelevant_register_set; exact H1|].
      etransitivity; [apply (cw_rs_misa r v0 Hfr)|].
      symmetry. apply (cw_rs_misa r vnew Hfr).
  Qed.

  Lemma cw_frames_in (dq : dfrac) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    reg_pointsto r (DfracOwn 1) v0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (cw_rs r v0) (cw_Drw r) ∗
     hreg_frame_ro (cw_Df dq) (cw_rs r v0) cw_Dro : iProp Σ).
  Proof. intros Hfr. iIntros "H1 H2 H3 H4". rewrite (cw_frames dq r v0 Hfr). iFrame. Qed.

  Lemma cw_frames_out (dq : dfrac) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame (cw_rs r v0) (cw_Drw r) ∗
     hreg_frame_ro (cw_Df dq) (cw_rs r v0) cw_Dro : iProp Σ) -∗
    (reg_pointsto r (DfracOwn 1) v0 ∗
     reg_pointsto cur_privilege dq Machine ∗
     reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof. intros Hfr. rewrite (cw_frames dq r v0 Hfr). iIntros "H". iExact "H". Qed.

  Lemma cw_rw_ext (r : register) (rs rs' : regstate) :
    reg_agree_on (cw_Drw r) rs rs' ->
    hreg_frame rs (cw_Drw r) -∗ (hreg_frame rs' (cw_Drw r) : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ (cw_Drw r) Hag).
    iIntros "H". iExact "H".
  Qed.

  Lemma cw_ro_ext (dq : dfrac) (rs rs' : regstate) :
    reg_agree_on cw_Dro rs rs' ->
    hreg_frame_ro (cw_Df dq) rs cw_Dro -∗
    (hreg_frame_ro (cw_Df dq) rs' cw_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext (cw_Df dq) _ _ cw_Dro Hag).
    iIntros "H". iExact "H".
  Qed.

End csrw.
