(* HartSCsr.v -- the CSR instructions' [swp] machinery, PRIVILEGE-GENERIC.

   [WpMmodeCsrSwp] is this file at [pr := Machine], with the legality check's
   reference state hard-wired to [dstateM] and the read set to
   [WpDecodeBridge.D_m].  Neither of those survives a move to Supervisor: the
   S CSRs' [check_CSR_result] reads {cur_privilege, menvcfg, misa}
   ([WpDecodeBridge.D_s]) off [dstateS], and satp's reads mstatus on top.  So
   the three things that were constants down there are PARAMETERS here:

     - the PRIVILEGE [pr].  It occurs only as the value [doCSR]'s two
       [cur_privilege] reads return and as the index of [check_CSR_result] /
       [ext_check_CSR]; nothing in the walk looks at it.
     - the certificate's READ SET [Db] and its REFERENCE STATE [dst].
       [HartGoodb.hval_of_goodb] already takes both -- [WpMmodeCsrSwp]'s
       [hval_check_CSR_result] simply instantiated them.
     - the ACCESS TYPE, via three engines rather than one.  [doCSR] branches
       on it twice (whether the CSR is read, and whether it is written), and
       both branches are decided by CONVERSION at a concrete access type,
       so splitting is free and keeps every [generic_eq] side condition a
       [reflexivity].  The three are exactly the three the kernel executes:
       CSRRead (a csrr), CSRWrite (a csrw, or a csrsi/csrci with rd = x0),
       and CSRReadWrite (a csrsi/csrci with rd <> x0).

   WHAT IS AN OBLIGATION AND WHY.  The same three as at M-mode, for the same
   reasons ([WpMmodeCsrSwp]'s header):
     - [check_CSR_result] is READ-ONLY however deep, so it rides the [goodb]
       certificate -- but as an [hval] PREMISE, so a caller whose check reads
       an unowned cell can supply it by a ∀-peel instead;
     - [read_CSR csr] is read-only too, but its VALUE is the caller's own
       register content, which [goodb] cannot transport (the reference state
       does not pin it).  So it is an obligation;
     - [write_CSR csr v] WRITES, which [goodb] rejects outright.  Obligation.
     - [wX_bits rd] is at a SYMBOLIC index, which no walker takes.  Obligation
       too, so that the same engine serves rd = x0 ([WpMmodeJump.swp_wX_zero])
       and rd <> x0 ([HartMFrame.swp_wX_file]) with no branch inside it. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        HartSpanChar HartRegNode HartMCycle RegFile WpGpr.
Require Import RiscvExtras RiscvFetchExec WpMmodeLeafBase HartMFrame
        ExecCommon HartMRun HartGoodb WpDecodeBridge.
Require Import WpMmodeJump WpMmodeCsrSwp.
Local Open Scope Z_scope.

Section HartSCsr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [Ox"..."] is not available in this import context (stdpp's monadic
     pattern notation shadows the literal syntaxes), so the two mip/sip CSR
     numbers are spelled elaborated, exactly as WpMmodeCsrSwp spells them. *)
  Local Notation csr344 :=
    (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 12)
       (HexString.Raw.to_N "344" 0)).
  Local Notation csr144 :=
    (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 12)
       (HexString.Raw.to_N "144" 0)).

  (* ================================================================== *)
  (* §1 THE LEGALITY CHECK, transported from ANY reference state.        *)
  (* [WpMmodeCsrSwp.hval_check_CSR_result] is this at                    *)
  (* [Db := D_m, dst := dstateM, pr := Machine].                         *)
  (* ================================================================== *)
  Lemma hval_check_CSR_result_p (Db : register -> bool) (D Drw : gset register)
      (rs : regstate) (dst : mstate) (csr : SailStdpp.Values.mword 12)
      (pr : Privilege) (at_ : CSRAccessType) :
    (forall r : register, Db r = true -> r ∈ D) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    goodb Db (check_CSR_result csr pr at_) dst = true ->
    exec (check_CSR_result csr pr at_) dst = Some (CSR_Check_OK tt, dst) ->
    hval D Drw rs (check_CSR_result csr pr at_) (CSR_Check_OK tt) rs.
  Proof.
    intros HD Hag Hgb Hex.
    exact (hval_of_goodb Db D Drw _ dst rs (CSR_Check_OK tt) HD Hag Hgb Hex).
  Qed.

  (* ================================================================== *)
  (* §2 THE READ ENGINE: [doCSR] at CSRRead.  [WpMmodeCsrSwp.               *)
  (* swp_doCSR_csrr_gen] with [Machine] replaced by [pr] -- the walk never   *)
  (* looks at the privilege, it only forwards what the two [cur_privilege]   *)
  (* reads answered.                                                        *)
  (* ================================================================== *)
  Lemma swp_doCSR_r_p (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (m : regfile) (csr : SailStdpp.Values.mword 12)
      (pr : Privilege) (rd : SailStdpp.Values.mword 5) (op : csrop)
      (rs1_val : SailStdpp.Values.mword 64)
      (Q : SailStdpp.Values.mword 64 -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pr ->
    uint rd <> 0 ->
    ext_check_CSR csr pr CSRRead = true ->
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr pr CSRRead)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    (forall x, csr_id_read_callback csr x = Defs.returnm tt) ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => Q x ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (doCSR csr rs1_val (Regidx rd) op CSRRead)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                ∃ x : SailStdpp.Values.mword 64, Q x ∗
                gpr_file (<[Regidx rd := regval_into_reg x]> m) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hrd Hext Hchk H344 H144 Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr".
    unfold doCSR.
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p0) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_bind_use (check_CSR_result csr pr CSRRead) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ (CSR_Check_OK tt) Hdisj Hchk
                with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p2) "(-> & Hrw & Hro)". rewrite Hpriv Hext.
    change (Riscv.rv64d.not true) with false. cbn match.
    (* the CSR read -- the caller's obligation *)
    replace (if Instances.generic_neq CSRRead CSRWrite then read_CSR csr
             else returnM (zeros' 64))
      with (read_CSR csr : M (SailStdpp.Values.mword 64)) by reflexivity.
    iApply (swp_bind_use (read_CSR csr) _ _ _ with "[Hrdcsr Hrw Hro] [-]").
    { iApply ("Hrdcsr" with "Hrw Hro"). }
    iIntros (rv) "(HQ & Hrw & Hro)".
    rewrite H344 H144.
    iApply (swp_bind_use (returnM rv : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = rv⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (dv) "(-> & Hrw & Hro)".
    replace (Instances.generic_eq CSRRead CSRRead) with true
      by reflexivity. cbn match.
    iApply (swp_bind0_use _ _
              (fun _ => gpr_file (<[Regidx rd := regval_into_reg rv]> m) ∗
                        hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
              with "[Hf Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => gpr_file m ∗
                          hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                with "[Hf Hrw Hro] [-]").
      { rewrite (Hcb rv). iApply swp_ret. by iFrame. }
      iIntros (u) "(Hf & Hrw & Hro)".
      iApply (swp_mono with "[Hrw Hro] [-]");
        [| iApply (swp_wX_file rd m rv Hrd with "Hcert Hf") ].
      iIntros (u2) "Hf". by iFrame. }
    iIntros (u3) "(Hf & Hrw & Hro)". iApply swp_ret.
    iSplitR; [done|]. iExists rv. iFrame.
  Qed.

  (* the PINNED corollary: the read value is named, so no existential
     reaches the leaf. *)
  Lemma swp_doCSR_r_pin_p (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (m : regfile) (csr : SailStdpp.Values.mword 12)
      (pr : Privilege) (rd : SailStdpp.Values.mword 5) (op : csrop)
      (rs1_val : SailStdpp.Values.mword 64)
      (readval : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pr ->
    uint rd <> 0 ->
    ext_check_CSR csr pr CSRRead = true ->
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr pr CSRRead)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    (forall x, csr_id_read_callback csr x = Defs.returnm tt) ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => ⌜x = readval⌝ ∗ hreg_frame rs Drw ∗
                   hreg_frame_ro Df rs Dro)) -∗
    swp (doCSR csr rs1_val (Regidx rd) op CSRRead)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg readval]> m) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hrd Hext Hchk H344 H144 Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_doCSR_r_p Drw Dro Df rs m csr pr rd op rs1_val
                   (fun x => ⌜x = readval⌝)%I Hdisj HDpriv Hpriv Hrd Hext
                   Hchk H344 H144 Hcb with "Hcert Hf Hrw Hro Hrdcsr") ].
    iIntros (e) "(-> & H)".
    iDestruct "H" as (x) "(-> & Hf & Hrw & Hro)". by iFrame.
  Qed.

  (* ================================================================== *)
  (* §3 THE WRITE ENGINE: [doCSR] at CSRWrite with rd = x0 -- a csrw, or  *)
  (* a csrsi/csrci whose destination is x0.  The CSR is NOT read (the     *)
  (* model returns zeros for [read_val]), so the written value is a       *)
  (* function of [rs1_val] alone and is taken as a PREMISE equation.      *)
  (* ================================================================== *)
  Lemma swp_doCSR_w_p (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rs' : regstate) (csr : SailStdpp.Values.mword 12) (pr : Privilege)
      (op : csrop) (rs1_val wval cfinal : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pr ->
    ext_check_CSR csr pr CSRWrite = true ->
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr pr CSRWrite)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    match op with
    | CSRRW => rs1_val
    | CSRRS => or_vec (zeros' 64) rs1_val
    | CSRRC => and_vec (zeros' 64) (not_vec rs1_val)
    end = wval ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr wval)
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)) -∗
    swp (doCSR csr rs1_val zreg op CSRWrite)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hext Hchk H344 H144 Hwv Hcb.
    iIntros "#Hcert Hrw Hro Hwr".
    unfold doCSR.
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p0) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_bind_use (check_CSR_result csr pr CSRWrite) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ (CSR_Check_OK tt) Hdisj Hchk
                with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". cbn match.
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
    rewrite H344 H144.
    iApply (swp_bind_use (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = zeros' 64⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (rv2) "(-> & Hrw & Hro)".
    replace (Instances.generic_eq CSRWrite CSRRead) with false
      by reflexivity. cbn match.
    rewrite Hwv.
    iApply (swp_bind_use (write_CSR csr wval) _ _ _ with "[Hwr Hrw Hro] [-]").
    { iApply ("Hwr" with "Hrw Hro"). }
    iIntros (wres) "(-> & Hrw & Hro)". cbn match.
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

  (* ================================================================== *)
  (* §4 THE READ-MODIFY-WRITE ENGINE: [doCSR] at CSRReadWrite -- a        *)
  (* csrsi/csrci with rd <> x0.  Both the CSR read and the CSR write are  *)
  (* obligations, and the OLD value the read produced is what the written *)
  (* value is computed from, so the two are chained through [readval].    *)
  (* ================================================================== *)
  Lemma swp_doCSR_rw_p (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rs' : regstate) (m : regfile) (csr : SailStdpp.Values.mword 12)
      (pr : Privilege) (rd : SailStdpp.Values.mword 5) (op : csrop)
      (rs1_val readval wval cfinal : SailStdpp.Values.mword 64)
      (m' : regfile) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pr ->
    ext_check_CSR csr pr CSRReadWrite = true ->
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr pr CSRReadWrite)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    match op with
    | CSRRW => rs1_val
    | CSRRS => or_vec readval rs1_val
    | CSRRC => and_vec readval (not_vec rs1_val)
    end = wval ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => ⌜x = readval⌝ ∗ hreg_frame rs Drw ∗
                   hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr wval)
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)) -∗
    (* THE rd WRITE IS AN OBLIGATION TOO, and that is what lets the same
       engine serve both a csrsi/csrci with a real destination
       ([HartMFrame.swp_wX_file], [m'] the inserted map) and one at x0
       ([WpMmodeJump.swp_wX_zero], [m'] the map unchanged).  At CSRReadWrite
       the model runs the rd write whatever rd is, so branching inside the
       engine would only duplicate it. *)
    (gpr_file m -∗ swp (wX_bits (Regidx rd) readval) (fun _ => gpr_file m')) -∗
    swp (doCSR csr rs1_val (Regidx rd) op CSRReadWrite)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m' ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hext Hchk H344 H144 Hwv Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr Hwr Hwx".
    unfold doCSR.
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p0) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_bind_use (check_CSR_result csr pr CSRReadWrite) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ (CSR_Check_OK tt) Hdisj Hchk
                with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p2) "(-> & Hrw & Hro)". rewrite Hpriv Hext.
    change (Riscv.rv64d.not true) with false. cbn match.
    replace (if Instances.generic_neq CSRReadWrite CSRWrite then read_CSR csr
             else returnM (zeros' 64))
      with (read_CSR csr : M (SailStdpp.Values.mword 64)) by reflexivity.
    iApply (swp_bind_use (read_CSR csr) _ _ _ with "[Hrdcsr Hrw Hro] [-]").
    { iApply ("Hrdcsr" with "Hrw Hro"). }
    iIntros (rv) "(-> & Hrw & Hro)".
    rewrite H344 H144.
    iApply (swp_bind_use (returnM readval : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = readval⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (dv) "(-> & Hrw & Hro)".
    replace (Instances.generic_eq CSRReadWrite CSRRead) with false
      by reflexivity. cbn match.
    rewrite Hwv.
    iApply (swp_bind_use (write_CSR csr wval) _ _ _ with "[Hwr Hrw Hro] [-]").
    { iApply ("Hwr" with "Hrw Hro"). }
    iIntros (wres) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_bind0_use _ _
              (fun _ => gpr_file m' ∗
                        hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)%I _
              with "[Hf Hwx Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => gpr_file m' ∗
                          hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)%I _
                with "[Hf Hwx Hrw Hro] [-]").
      { iApply (swp_mono with "[Hrw Hro] [-]"); [| iApply ("Hwx" with "Hf") ].
        iIntros (u) "Hf". by iFrame. }
      iIntros (u) "(Hf & Hrw & Hro)". rewrite Hcb.
      iApply swp_ret. by iFrame. }
    iIntros (u3) "(Hf & Hrw & Hro)". iApply swp_ret. by iFrame.
  Qed.

  (* ================================================================== *)
  (* §5 THE execute-LEVEL WRAPPERS: peel the ONE symbolic-index operand   *)
  (* node and resolve [csr_access_type], which is where a leaf's          *)
  (* instruction shape turns into one of the three engines above.         *)
  (* ================================================================== *)

  (* [csrr rd, csr] -- CSRReg with the SOURCE at x0, so the access is a
     plain read whatever rd is. *)
  Lemma swp_execute_CSRReg_r_p (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (m : regfile)
      (csr : SailStdpp.Values.mword 12) (pr : Privilege)
      (rd : SailStdpp.Values.mword 5)
      (readval : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pr ->
    uint rd <> 0 ->
    ext_check_CSR csr pr CSRRead = true ->
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr pr CSRRead)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    (forall x, csr_id_read_callback csr x = Defs.returnm tt) ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => ⌜x = readval⌝ ∗ hreg_frame rs Drw ∗
                   hreg_frame_ro Df rs Dro)) -∗
    swp (execute_CSRReg csr zreg (Regidx rd) CSRRS)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg readval]> m) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hrd Hext Hchk H344 H144 Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr".
    unfold execute_CSRReg.
    replace (csr_access_type CSRRS (Instances.generic_eq (Regidx rd) zreg)
               (Instances.generic_eq zreg zreg))
      with CSRRead
      by (replace (Instances.generic_eq zreg zreg) with true by reflexivity;
          destruct (Instances.generic_eq (Regidx rd) zreg); reflexivity).
    change zreg with (Regidx cli_rs1).
    iApply (swp_bind_use (rX_bits (Regidx cli_rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file cli_rs1 m with "Hcert Hf"). }
    iIntros (v) "[-> Hf]".
    iApply (swp_doCSR_r_pin_p Drw Dro Df rs m csr pr rd CSRRS _ readval
              Hdisj HDpriv Hpriv Hrd Hext Hchk H344 H144 Hcb
              with "Hcert Hf Hrw Hro Hrdcsr").
  Qed.

  (* [csrw csr, rs1] -- CSRReg with the DESTINATION at x0, so the access is
     a plain write.  The written value is the source register's content. *)
  Lemma swp_execute_CSRReg_w_p (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate) (m : regfile)
      (csr : SailStdpp.Values.mword 12) (pr : Privilege)
      (rs1 : SailStdpp.Values.mword 5)
      (cfinal : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pr ->
    ext_check_CSR csr pr CSRWrite = true ->
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr pr CSRWrite)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
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
    intros Hdisj HDpriv Hpriv Hext Hchk H344 H144 Hcb.
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
      [| iApply (swp_doCSR_w_p Drw Dro Df rs rs' csr pr CSRRW
                   (m !!! Regidx rs1) (m !!! Regidx rs1) cfinal Hdisj HDpriv
                   Hpriv Hext Hchk H344 H144 eq_refl Hcb
                   with "Hcert Hrw Hro Hwr") ].
    iIntros (e) "(-> & Hrw & Hro)". iSplitR; [done|]. iFrame.
  Qed.

  (* [csrsi/csrci csr, imm] with a NONZERO immediate -- CSRImm, which is a
     read-modify-write whatever rd is ([csr_access_type]'s last two
     clauses), so it takes the rmw engine and the rd write rides the
     obligation. *)
  Lemma swp_execute_CSRImm_rw_p (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate) (m m' : regfile)
      (csr : SailStdpp.Values.mword 12) (pr : Privilege)
      (imm rd : SailStdpp.Values.mword 5) (op : csrop)
      (readval wval cfinal : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = pr ->
    eq_vec imm (zeros' 5) = false ->
    (forall bb : bool, csr_access_type op bb false = CSRReadWrite) ->
    ext_check_CSR csr pr CSRReadWrite = true ->
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr pr CSRReadWrite)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    match op with
    | CSRRW => zero_extend' 64 imm
    | CSRRS => or_vec readval (zero_extend' 64 imm)
    | CSRRC => and_vec readval (not_vec (zero_extend' 64 imm))
    end = wval ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => ⌜x = readval⌝ ∗ hreg_frame rs Drw ∗
                   hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr wval)
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)) -∗
    (gpr_file m -∗ swp (wX_bits (Regidx rd) readval) (fun _ => gpr_file m')) -∗
    swp (execute_CSRImm csr imm (Regidx rd) op)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m' ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Himm Hat Hext Hchk H344 H144 Hwv Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr Hwr Hwx".
    unfold execute_CSRImm. rewrite Himm (Hat _).
    iApply (swp_doCSR_rw_p Drw Dro Df rs rs' m csr pr rd op
              (zero_extend' 64 imm) readval wval cfinal m' Hdisj HDpriv Hpriv
              Hext Hchk H344 H144 Hwv Hcb
              with "Hcert Hf Hrw Hro Hrdcsr Hwr Hwx").
  Qed.

  (* ================================================================== *)
  (* §6 THE FRAME KIT AT A PARAMETRIC PRIVILEGE.                          *)
  (*                                                                     *)
  (* Exactly [WpMmodeCsrSwp]'s [cw_*] / [cr_*] kit, and all of it is       *)
  (* REUSED here unchanged -- [cw_Drw], [cw_Dro], [cw_Df], [cw_fresh],     *)
  (* [cr_Dro], [cr_Df] and every membership lemma are privilege-free.      *)
  (* The ONE thing that is not is the reference TOWER [cw_rs], whose        *)
  (* innermost [register_set] pins cur_privilege to [Machine].  So this     *)
  (* section is that tower with the privilege as a parameter, plus the      *)
  (* four lemmas whose statements mention it.                              *)
  (* ================================================================== *)
  Definition pw_rs (pr : Privilege) (r : register) (v0 : type_of_register r)
      : regstate :=
    register_set r v0
      (register_set misa MISA_C
         (register_set mseccfg (Values.mword_of_int 0)
            (register_set cur_privilege pr init_regstate))).

  Definition pw0_rs (pr : Privilege) : regstate :=
    register_set misa MISA_C
      (register_set mseccfg (Values.mword_of_int 0)
         (register_set cur_privilege pr init_regstate)).

  Lemma pw_rs_r (pr : Privilege) (r : register) (v0 : type_of_register r) :
    register_lookup r (pw_rs pr r v0) = v0.
  Proof. rewrite /pw_rs. apply register_lookup_set. Qed.

  Lemma pw_rs_misa (pr : Privilege) (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup misa (pw_rs pr r v0) = MISA_C.
  Proof.
    intros (H1 & _ & _). rewrite /pw_rs.
    etransitivity; [apply irrelevant_register_set; exact H1|].
    apply register_lookup_set.
  Qed.

  Lemma pw_rs_sec (pr : Privilege) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    register_lookup mseccfg (pw_rs pr r v0) = Values.mword_of_int 0.
  Proof.
    intros (_ & H2 & _). rewrite /pw_rs.
    etransitivity; [apply irrelevant_register_set; exact H2|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  Lemma pw_rs_priv (pr : Privilege) (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup cur_privilege (pw_rs pr r v0) = pr.
  Proof.
    intros (_ & _ & H3). rewrite /pw_rs.
    etransitivity; [apply irrelevant_register_set; exact H3|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  Lemma pw0_rs_misa (pr : Privilege) : register_lookup misa (pw0_rs pr) = MISA_C.
  Proof. rewrite /pw0_rs. apply register_lookup_set. Qed.
  Lemma pw0_rs_sec (pr : Privilege) :
    register_lookup mseccfg (pw0_rs pr) = Values.mword_of_int 0.
  Proof.
    rewrite /pw0_rs.
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.
  Lemma pw0_rs_priv (pr : Privilege) :
    register_lookup cur_privilege (pw0_rs pr) = pr.
  Proof.
    rewrite /pw0_rs.
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  (* the WRITE-side frames: the CSR cell writable, the three pins read-only *)
  Lemma pw_frames (pr : Privilege) (dq : dfrac) (r : register)
      (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame (pw_rs pr r v0) (cw_Drw r) ∗
     hreg_frame_ro (cw_Df dq) (pw_rs pr r v0) cw_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto r (DfracOwn 1) v0 ∗
        reg_pointsto cur_privilege dq pr ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hfr.
    rewrite /hreg_frame /hreg_frame_ro /cw_Drw /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite pw_rs_r (pw_rs_priv pr r v0 Hfr) (pw_rs_sec pr r v0 Hfr)
      (pw_rs_misa pr r v0 Hfr).
    rewrite (cw_Df_priv dq) (cw_Df_sec dq) (cw_Df_misa dq).
    by rewrite !bi.sep_assoc.
  Qed.

  (* the READ-side frames: nothing writable, the CSR cell among the pins *)
  Lemma pr_frames (pr : Privilege) (dqp dqc : dfrac) (r : register)
      (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame_ro (cr_Df dqp dqc r) (pw_rs pr r v0) (cr_Dro r) : iProp Σ)
    ⊣⊢ (reg_pointsto r dqc v0 ∗
        reg_pointsto cur_privilege dqp pr ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hfr.
    rewrite /hreg_frame_ro /cr_Dro.
    rewrite (big_sepS_union _ (cw_Drw r) cw_Dro (cw_disj r Hfr)).
    rewrite /cw_Drw /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite pw_rs_r (pw_rs_priv pr r v0 Hfr) (pw_rs_sec pr r v0 Hfr)
      (pw_rs_misa pr r v0 Hfr).
    rewrite (cr_Df_r dqp dqc r Hfr) (cr_Df_priv dqp dqc r Hfr)
      (cr_Df_sec dqp dqc r) (cr_Df_misa dqp dqc r).
    by rewrite !bi.sep_assoc.
  Qed.

  (* the THREE PINS ALONE, for an instruction that touches no CSR cell the
     leaf owns (a csrw whose target is the leaf's own cell goes through
     [pw_frames]; a read of an unowned cell -- [time] -- goes here). *)
  Lemma pr0_frames (pr : Privilege) (dqp : dfrac) :
    (hreg_frame_ro (cw_Df dqp) (pw0_rs pr) cw_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto cur_privilege dqp pr ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    rewrite /hreg_frame_ro /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite pw0_rs_priv pw0_rs_sec pw0_rs_misa.
    rewrite (cw_Df_priv dqp) (cw_Df_sec dqp) (cw_Df_misa dqp).
    by rewrite !bi.sep_assoc.
  Qed.

  (* the post-write file: [write_CSR] leaves a [register_set] tower, which
     agrees with the tower that simply NAMES the new value *)
  Lemma pw_set_agree (pr : Privilege) (r : register)
      (v0 vnew : type_of_register r) :
    cw_fresh r ->
    reg_agree_on (cw_Drw r ∪ cw_Dro)
      (register_set r vnew (pw_rs pr r v0)) (pw_rs pr r vnew).
  Proof.
    intros Hfr r' Hr'.
    pose proof Hfr as Hfr2. destruct Hfr2 as (H1 & H2 & H3).
    rewrite /cw_Drw /cw_Dro in Hr'.
    repeat (apply elem_of_union in Hr' as [Hr'|Hr']);
      apply elem_of_singleton in Hr'; subst r'.
    - etransitivity; [apply register_lookup_set|]. symmetry. apply pw_rs_r.
    - etransitivity; [apply irrelevant_register_set; exact H3|].
      etransitivity; [apply (pw_rs_priv pr r v0 Hfr)|].
      symmetry. apply (pw_rs_priv pr r vnew Hfr).
    - etransitivity; [apply irrelevant_register_set; exact H2|].
      etransitivity; [apply (pw_rs_sec pr r v0 Hfr)|].
      symmetry. apply (pw_rs_sec pr r vnew Hfr).
    - etransitivity; [apply irrelevant_register_set; exact H1|].
      etransitivity; [apply (pw_rs_misa pr r v0 Hfr)|].
      symmetry. apply (pw_rs_misa pr r vnew Hfr).
  Qed.

  (* ================================================================== *)
  (* §7 THE LEGALITY CHECK AT SUPERVISOR.                                 *)
  (*                                                                     *)
  (* THE READ SET IS [D_m], NOT [D_s], and that is measured rather than    *)
  (* guessed: [goodb D_m (check_CSR_result csr Supervisor at_) dstateS] is *)
  (* [true] for every S CSR the kernel touches.  The stateen gate that     *)
  (* would have read menvcfg is off at [MENVCFG_S], so the check reads the *)
  (* same three cells at Supervisor as at Machine -- which is why the      *)
  (* whole [cw_*] footprint kit carries over unchanged and the S leaves    *)
  (* need no extra cell in the frame.                                     *)
  (*                                                                     *)
  (* satp is the ONE exception ([check_TVM_SATP] reads mstatus.TVM); its   *)
  (* leaf supplies the [hval] premise by its own route.                    *)
  (* ================================================================== *)
  Lemma agree_dm_S (rs : regstate) :
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    forall r : register, D_m r = true ->
      register_lookup r rs = register_lookup r dstateS.(sregs).
  Proof.
    intros Hp Hs Hm r Hr. unfold D_m in Hr.
    apply orb_prop in Hr as [Hr|Hr]; [apply orb_prop in Hr as [Hr|Hr]|];
      apply register_beq_eq in Hr; subst r; [rewrite Hp|rewrite Hs|rewrite Hm];
      vm_compute; reflexivity.
  Qed.

  Lemma hval_check_CSR_result_S (D Drw : gset register) (rs : regstate)
      (csr : SailStdpp.Values.mword 12) (at_ : CSRAccessType) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    goodb D_m (check_CSR_result csr Supervisor at_) dstateS = true ->
    exec (check_CSR_result csr Supervisor at_) dstateS
      = Some (CSR_Check_OK tt, dstateS) ->
    hval D Drw rs (check_CSR_result csr Supervisor at_) (CSR_Check_OK tt) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm Hgb Hex.
    exact (hval_check_CSR_result_p D_m D Drw rs dstateS csr Supervisor at_
             (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm) Hgb Hex).
  Qed.

End HartSCsr.
