(* WpGprCsrwStimecmp.v -- the ONE csrw leaf that writes a cell the WRAPPER
   owns.

   [write_CSR csr_stimecmp] is [read stimecmp; write stimecmp;
   clint_dispatch false; read stimecmp], and [clint_dispatch] REFRESHES mip
   from the CLINT: it reads mtime / mtimecmp / stimecmp / the plic wires --
   none of which any leaf owns, so those are ∀-peels ([swp_read_reg_any];
   the walker cannot cover them, there is no cell to pin) -- and then WRITES
   mip, whose cell lives in [pc_is]'s [clock_res] and therefore goes wholly
   to the cycle wrapper.  A leaf cannot write a cell it does not hold, so
   this leaf needs the wrapper to LEND it mip and take back an arbitrary new
   value.  That is sound and not even hard to see why:
   [InstrBytes.mm_tick_agree] already constrains the post-file only OFF
   [tk_clock3], and mip ∈ tk_clock3 -- the tick's own mip write is exactly
   as nondeterministic.

   [WpInstrMip.wp_instr_mip] is the wrapper that lends it, built on the
   predicate-post-file engines ([HartStepAny.swp_exec_step_any] under
   [WpInstrRun.swp_run_hart_active_instr_ex]).

   Two things live here rather than in [WpMmodeCsrSwp] / [WpGprCsrwB]
   because this is their only client:

   - [swp_clint_dispatch_false], the ∀-peeled walk of the CLINT refresh: it
     touches NO framed register, so it returns the caller's frames untouched
     and the mip cell at a value nobody names;
   - [swp_doCSR_csrw_r] / [swp_execute_CSRReg_csrw_r], the csrw engines with
     a RIDER [Rr] threaded from the [write_CSR] obligation out to the
     conclusion.  The rider is what carries the re-existentialised mip cell
     past the engine, whose post-FILE is a parameter and so cannot name it.
     They are otherwise [WpMmodeCsrSwp.swp_doCSR_csrw] /
     [swp_execute_CSRReg_csrw] verbatim and should absorb them at a fold-back
     (the rider-free reading is [Rr := emp]).

   The leaf is parked here, out of WpGprCsrwB, so that the four csrw leaves
   which do not touch the wrapper's cells (mideleg / sie / satp / pmpaddr0)
   are not held red behind it.  Everything it needs from the exec side is
   still in WpGprCsrwB. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec ExecCommon WpGpr.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpInstrMip.
Require Import MinstretInv.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartMCycle
        HartMFrame HartGoodb WpDecodeBridge WpMmodeJump WpMmodeCsrSwp.
Require Import WpGprCsrrCommon.
Require Import WpGprCsrwB.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* the walker's view of the write: the pruned term, so no goal ever carries
   the 4096-way dispatch.  Read OFF the pruned goal, never hand-associated. *)
Lemma write_CSR_stimecmp_red (v : mword 64) :
  write_CSR csr_stimecmp v
  = Defs.bind (Defs.read_reg stimecmp)
      (fun o : mword 64 =>
         Defs.bind
           (Defs.bind0
              (Defs.bind0 (Defs.write_reg stimecmp (stimecmp_legalized o v))
                 (clint_dispatch false))
              (Defs.read_reg stimecmp))
           (fun c : mword 64 =>
              returnM (Ok (subrange_vec_dec c (Z.sub xlen 1) 0)))).
Proof.
  unfold write_CSR, csr_stimecmp, stimecmp_legalized.
  drive_csr_term. reflexivity.
Qed.

Section WpCsrwStimecmp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (* The two config gates the CLINT refresh runs, transported from the    *)
  (* reference state: both read only cells [D_m] pins, so [goodb] takes    *)
  (* them whole.                                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma hval_cE_Sstc (D Drw : gset register) (rs : regstate) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (currentlyEnabled Ext_Sstc) true rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateM rs true
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm)).
    - vm_compute. reflexivity.
    - apply exec_currentlyEnabled_Sstc.
  Qed.

  Lemma hval_cE_S (D Drw : gset register) (rs : regstate) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (currentlyEnabled Ext_S) true rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateM rs true
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm)).
    - vm_compute. reflexivity.
    - rewrite (exec_currentlyEnabled_S dstateM).
      replace (eq_vec (_get_Misa_S (register_lookup misa dstateM.(sregs)))
                 ('b"1")) with true by (vm_compute; reflexivity).
      reflexivity.
  Qed.

  (* the mip write-callback: pure, so the reference state carries it too *)
  Lemma hval_cb_mip (D Drw : gset register) (rs : regstate) (V : mword 64) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (csr_name_write_callback "mip" V) tt rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateM rs tt
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm)).
    - vm_compute. reflexivity.
    - apply exec_csr_name_write_callback_mip.
  Qed.

  (* ==================================================================== *)
  (* THE CLINT REFRESH, ∀-PEELED.                                          *)
  (*                                                                      *)
  (* Every register it READS is either a config cell the caller's frame     *)
  (* pins (misa, through the two [currentlyEnabled] gates) or one NOBODY    *)
  (* owns -- mtime, mtimecmp, menvcfg, the plic wires [sig_meip] /          *)
  (* [sig_seip], and mip and stimecmp, whose values are dead here.  The     *)
  (* unowned ones are ∀-peeled by [swp_read_reg_any]: the node steps (the   *)
  (* span's read case is ungated), it just answers a value nobody can name. *)
  (* The one WRITE is mip, on the cell the wrapper lent, and the value it   *)
  (* lands on is therefore existential.  The caller's FRAMES come back      *)
  (* untouched: mip is not in them.                                        *)
  (* ==================================================================== *)
  Lemma swp_clint_dispatch_false (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (ip : mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    gen_cert -∗
    (R_bitvector_64 mip) ↦ᵣ ip -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (clint_dispatch false)
      (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa.
    iIntros "#Hcert Hip Hrw Hro".
    unfold clint_dispatch.
    (* old_mip, then the three value-dead reads: the four registers the
       refresh consults before it decides what mip becomes *)
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
      by iIntros (?). }
    iIntros (old_mip) "_".
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
      by iIntros (?). }
    iIntros (w0) "_".
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mtimecmp) with "Hcert").
      by iIntros (?). }
    iIntros (w1) "_".
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mtime) with "Hcert").
      by iIntros (?). }
    iIntros (w2) "_".
    (* the MTIP write on the lent cell, then the Sstc/STCE gate *)
    iApply (swp_bind_use _ _
              (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
              with "[Hip Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => ∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I _
                with "[Hip] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_cell (R_bitvector_64 mip) ip _
                       with "Hcert Hip") ].
        iIntros (u) "Hip". by iExists _. }
      iIntros (u) "Hip".
      unfold Defs.and_boolM.
      iApply (swp_bind_use _ _
                (fun b => ⌜b = true⌝ ∗ hreg_frame rs Drw ∗
                          hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
      { iApply (swp_span Drw Dro Df rs rs _ true Hdisj
                  (hval_cE_Sstc (Drw ∪ Dro) Drw rs HDpriv HDsec HDmisa
                     Hpriv Hsec Hmisa) with "Hcert Hrw Hro"). }
      iIntros (b) "(-> & Hrw & Hro)". cbn match.
      iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
      { iApply (swp_read_reg_any (R_bitvector_64 menvcfg) with "Hcert").
        by iIntros (?). }
      iIntros (w4) "_". iApply swp_ret. iFrame. }
    iIntros (w5) "(Hip & Hrw & Hro)".
    (* the STIP arm, the (off) print hook, and the "did mip change?" test *)
    iApply (swp_bind_use _ _
              (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
              with "[Hip Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                with "[Hip Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => ∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I _
                  with "[Hip] [-]").
        { destruct w5.
          - iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
            { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
              by iIntros (?). }
            iIntros (w6) "_".
            iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
            { iApply (swp_read_reg_any (R_bitvector_64 stimecmp) with "Hcert").
              by iIntros (?). }
            iIntros (w7) "_".
            iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
            { iApply (swp_read_reg_any (R_bitvector_64 mtime) with "Hcert").
              by iIntros (?). }
            iIntros (w8) "_".
            iDestruct "Hip" as (z1) "Hip".
            iApply (swp_mono with "[] [-]");
              [| iApply (swp_write_reg_cell (R_bitvector_64 mip) z1 _
                           with "Hcert Hip") ].
            iIntros (u2) "Hip". by iExists _.
          - iApply swp_ret. iExact "Hip". }
        iIntros (u2) "Hip".
        change (get_config_print_clint tt) with false. cbn match.
        iApply swp_ret. iFrame. }
      iIntros (u3) "(Hip & Hrw & Hro)".
      unfold Defs.or_boolM.
      iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
      { iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
        { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
          by iIntros (?). }
        iIntros (w10) "_". iApply swp_ret. done. }
      iIntros (b2) "_". destruct b2; iApply swp_ret; iFrame. }
    iIntros (w11) "(Hip & Hrw & Hro)".
    (* the callback arm: [read_mip] ORs in the plic wires, then a pure
       callback.  Nothing here writes. *)
    destruct w11.
    - unfold read_mip.
      iApply (swp_bind_use _ _
                (fun _ => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
        { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
          by iIntros (?). }
        iIntros (w12) "_".
        unfold external_interrupts_pending.
        iApply (swp_bind_use _ _
                  (fun _ => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
          { iApply (swp_read_reg_any (R_bitvector_1 sig_meip) with "Hcert").
            by iIntros (?). }
          iIntros (w13) "_".
          iApply (swp_bind_use _ _
                    (fun b => ⌜b = true⌝ ∗ hreg_frame rs Drw ∗
                              hreg_frame_ro Df rs Dro)%I _
                    with "[Hrw Hro] [-]").
          { iApply (swp_span Drw Dro Df rs rs _ true Hdisj
                      (hval_cE_S (Drw ∪ Dro) Drw rs HDpriv HDsec HDmisa
                         Hpriv Hsec Hmisa) with "Hcert Hrw Hro"). }
          iIntros (b) "(-> & Hrw & Hro)". cbn match.
          iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
          { iApply (swp_read_reg_any (R_bitvector_1 sig_seip) with "Hcert").
            by iIntros (?). }
          iIntros (w14) "_". iApply swp_ret. iFrame. }
        iIntros (w15) "(Hrw & Hro)". iApply swp_ret. iFrame. }
      iIntros (w16) "(Hrw & Hro)".
      iApply (swp_mono with "[Hip] [Hrw Hro]");
        [| iApply (swp_span Drw Dro Df rs rs _ tt Hdisj
                     (hval_cb_mip (Drw ∪ Dro) Drw rs w16 HDpriv HDsec HDmisa
                        Hpriv Hsec Hmisa) with "Hcert Hrw Hro") ].
      iIntros (u4) "(_ & Hrw & Hro)". iFrame.
    - iApply swp_ret. iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE WRITE, at the four-cell csrw frame plus the lent mip cell.         *)
  (* ==================================================================== *)
  Lemma swp_write_CSR_stimecmp (dq : dfrac) (stimecmp0 v ip : mword 64) :
    cw_fresh stimecmp ->
    gen_cert -∗
    (R_bitvector_64 mip) ↦ᵣ ip -∗
    hreg_frame (cw_rs stimecmp stimecmp0) (cw_Drw stimecmp) -∗
    hreg_frame_ro (cw_Df dq) (cw_rs stimecmp stimecmp0) cw_Dro -∗
    swp (write_CSR csr_stimecmp v)
      (fun x => ⌜x = Ok (subrange_vec_dec (stimecmp_legalized stimecmp0 v)
                           (Z.sub xlen 1) 0)⌝ ∗
         hreg_frame (cw_rs stimecmp (stimecmp_legalized stimecmp0 v))
           (cw_Drw stimecmp) ∗
         hreg_frame_ro (cw_Df dq)
           (cw_rs stimecmp (stimecmp_legalized stimecmp0 v)) cw_Dro ∗
         ∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z).
  Proof.
    intros Hfresh. iIntros "#Hcert Hip Hrw Hro".
    rewrite write_CSR_stimecmp_red.
    (* the old value *)
    iApply (swp_bind_use _ _
              (fun o => ⌜o = stimecmp0⌝ ∗
                 hreg_frame (cw_rs stimecmp stimecmp0) (cw_Drw stimecmp) ∗
                 hreg_frame_ro (cw_Df dq) (cw_rs stimecmp stimecmp0) cw_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw stimecmp) cw_Dro (cw_Df dq)
                     (cw_rs stimecmp stimecmp0) stimecmp
                     (cw_disj stimecmp Hfresh) (cw_in_r stimecmp)
                     with "Hcert Hrw Hro") ].
      iIntros (o) "(-> & Hrw & Hro)".
      rewrite (cw_rs_r stimecmp stimecmp0). by iFrame. }
    iIntros (o) "(-> & Hrw & Hro)".
    (* the write, the CLINT refresh and the read-back: one left-nested
       [bind0] spine under the value bind *)
    iApply (swp_bind_use _ _
              (fun c => ⌜c = stimecmp_legalized stimecmp0 v⌝ ∗
                 hreg_frame (cw_rs stimecmp (stimecmp_legalized stimecmp0 v))
                   (cw_Drw stimecmp) ∗
                 hreg_frame_ro (cw_Df dq)
                   (cw_rs stimecmp (stimecmp_legalized stimecmp0 v)) cw_Dro ∗
                 ∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I
              _ with "[Hip Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ =>
                   hreg_frame (cw_rs stimecmp (stimecmp_legalized stimecmp0 v))
                     (cw_Drw stimecmp) ∗
                   hreg_frame_ro (cw_Df dq)
                     (cw_rs stimecmp (stimecmp_legalized stimecmp0 v)) cw_Dro ∗
                   ∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I
                _ with "[Hip Hrw Hro] [-]").
      { (* the register write, then the CLINT refresh *)
        iApply (swp_bind0_use _ _
                  (fun _ =>
                     hreg_frame (cw_rs stimecmp (stimecmp_legalized stimecmp0 v))
                       (cw_Drw stimecmp) ∗
                     hreg_frame_ro (cw_Df dq)
                       (cw_rs stimecmp (stimecmp_legalized stimecmp0 v)) cw_Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono with "[] [-]");
            [| iApply (swp_write_reg_owned (cw_Drw stimecmp) cw_Dro (cw_Df dq)
                         (cw_rs stimecmp stimecmp0) stimecmp _
                         (cw_disj stimecmp Hfresh) (cw_w_r stimecmp)
                         with "Hcert Hrw Hro") ].
          iIntros (u) "[Hrw Hro]".
          iDestruct (cw_rw_ext stimecmp _ _
                       (reg_agree_l _ _ _ _
                          (cw_set_agree stimecmp stimecmp0 _ Hfresh))
                       with "Hrw") as "Hrw".
          iDestruct (cw_ro_ext dq _ _
                       (reg_agree_r _ _ _ _
                          (cw_set_agree stimecmp stimecmp0 _ Hfresh))
                       with "Hro") as "Hro".
          by iFrame. }
        iIntros (u) "[Hrw Hro]".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_clint_dispatch_false (cw_Drw stimecmp) cw_Dro
                       (cw_Df dq)
                       (cw_rs stimecmp (stimecmp_legalized stimecmp0 v)) ip
                       (cw_disj stimecmp Hfresh) (cw_in_priv stimecmp)
                       (cw_in_sec stimecmp) (cw_in_misa stimecmp)
                       (cw_rs_priv stimecmp _ Hfresh)
                       (cw_rs_sec stimecmp _ Hfresh)
                       (cw_rs_misa stimecmp _ Hfresh)
                       with "Hcert Hip Hrw Hro") ].
        iIntros (u2) "(Hip & Hrw & Hro)". iFrame. }
      iIntros (u2) "(Hrw & Hro & Hip)".
      (* the read-back *)
      iApply (swp_mono with "[Hip] [Hrw Hro]");
        [| iApply (swp_read_reg_pinned (cw_Drw stimecmp) cw_Dro (cw_Df dq)
                     (cw_rs stimecmp (stimecmp_legalized stimecmp0 v)) stimecmp
                     (cw_disj stimecmp Hfresh) (cw_in_r stimecmp)
                     with "Hcert Hrw Hro") ].
      iIntros (c) "(-> & Hrw & Hro)".
      rewrite (cw_rs_r stimecmp (stimecmp_legalized stimecmp0 v)).
      by iFrame. }
    iIntros (c) "(-> & Hrw & Hro & Hip)".
    iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE csrw ENGINES WITH A RIDER.  Verbatim                              *)
  (* [WpMmodeCsrSwp.swp_doCSR_csrw] / [swp_execute_CSRReg_csrw] but for an  *)
  (* [Rr : iProp] threaded from the [write_CSR] obligation's postcondition  *)
  (* out to the conclusion: the post-FILE is a parameter of those rules, so *)
  (* a cell whose value the write does not determine cannot ride in it.     *)
  (* ==================================================================== *)
  Lemma swp_doCSR_csrw_r (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rs' : regstate) (csr : SailStdpp.Values.mword 12)
      (v cfinal : SailStdpp.Values.mword 64) (Rr : iProp Σ) :
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
    (if eq_vec csr (Values.mword_of_int 0x344)
     then read_mip IncludePlatformInterrupts
     else if eq_vec csr (Values.mword_of_int 0x144)
     then read_sip IncludePlatformInterrupts
     else returnM (zeros' 64))
      = (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr v)
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗ Rr)) -∗
    swp (doCSR csr v zreg CSRRW CSRWrite)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗ Rr).
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
                (hval_check_CSR_result (Drw ∪ Dro) Drw rs csr CSRWrite HDpriv
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
    (* 4. the write *)
    iApply (swp_bind_use (write_CSR csr v) _ _ _ with "[Hwr Hrw Hro] [-]").
    { iApply ("Hwr" with "Hrw Hro"). }
    iIntros (wres) "(-> & Hrw & Hro & HRr)". cbn match.
    (* 5. the discarded x0 write and the pure callback *)
    iApply (swp_bind0_use _ _
              (fun _ => hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗ Rr)%I _
              with "[Hrw Hro HRr] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗ Rr)%I
                _ with "[Hrw Hro HRr] [-]").
      { change (wX_bits zreg (zeros' 64)) with (Defs.returnm tt : M unit).
        iApply swp_ret. by iFrame. }
      iIntros (u) "(Hrw & Hro & HRr)". rewrite Hcb. iApply swp_ret. by iFrame. }
    iIntros (u2) "(Hrw & Hro & HRr)". iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_execute_CSRReg_csrw_r (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate) (m : regfile)
      (csr : SailStdpp.Values.mword 12) (rs1 : SailStdpp.Values.mword 5)
      (cfinal : SailStdpp.Values.mword 64) (Rr : iProp Σ) :
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
    (if eq_vec csr (Values.mword_of_int 0x344)
     then read_mip IncludePlatformInterrupts
     else if eq_vec csr (Values.mword_of_int 0x144)
     then read_sip IncludePlatformInterrupts
     else returnM (zeros' 64))
      = (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr (m !!! Regidx rs1))
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗ Rr)) -∗
    swp (execute_CSRReg csr (Regidx rs1) zreg CSRRW)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗ Rr).
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
      [| iApply (swp_doCSR_csrw_r Drw Dro Df rs rs' csr (m !!! Regidx rs1)
                   cfinal Rr Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa Hext
                   Hgb Hex Hmip Hcb with "Hcert Hrw Hro Hwr") ].
    iIntros (e) "(-> & Hrw & Hro & HRr)". iSplitR; [done|]. iFrame.
  Qed.

  (* ---- stimecmp ---- *)
  Lemma wp_csrw_stimecmp_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (stimecmp0 : type_of_register stimecmp)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh stimecmp)
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_stimecmp Machine CSRWrite) dstateM
                   = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr_mip pc (add_vec_int pc 4) false
              (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros (ip) "Hf HPC HnPC Hip".
      iDestruct (cw_frames_in (DfracOwn (q/2)) stimecmp stimecmp0 Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro Hip]");
        [| iApply (swp_execute_CSRReg_csrw_r (cw_Drw stimecmp) cw_Dro
                     (cw_Df (DfracOwn (q/2))) (cw_rs stimecmp stimecmp0)
                     (cw_rs stimecmp
                        (stimecmp_legalized stimecmp0 (m !!! Regidx rs1))) m
                     csr_stimecmp rs1 _
                     (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I
                     (cw_disj stimecmp Hfresh)
                     (cw_in_priv stimecmp) (cw_in_sec stimecmp)
                     (cw_in_misa stimecmp)
                     (cw_rs_priv stimecmp stimecmp0 Hfresh)
                     (cw_rs_sec stimecmp stimecmp0 Hfresh)
                     (cw_rs_misa stimecmp stimecmp0 Hfresh)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hip]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro & Hip)".
        iDestruct (cw_frames_out (DfracOwn (q/2)) stimecmp _ Hfresh
                     with "[$Hrw $Hro]") as "(Hcsr & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC Hip".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hcsr".
      + iIntros "Hrw Hro".
        iApply (swp_write_CSR_stimecmp (DfracOwn (q/2)) stimecmp0
                  (m !!! Regidx rs1) ip Hfresh with "Hcert Hip Hrw Hro").
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

End WpCsrwStimecmp.
