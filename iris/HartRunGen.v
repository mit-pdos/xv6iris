(* HartRunGen.v -- [run_hart_active] WITHOUT A MODE AND WITHOUT AN ARM.

   [HartMRun]'s four rules bake in three things this one leaves open:

     - the PRIVILEGE.  It is read from the file and handed to
       [dispatchInterrupt]; nothing downstream of that read cares which one
       it is, so it is a parameter.

     - the DISPATCH.  In M-mode with mstatus.MIE clear it short-circuits
       before the PLIC wires and its answer is [None], which is what lets
       [wp_instr] offer a single retire arm.  In S-mode there is no such
       shortcut: [read_mip IncludePlatformInterrupts] ORs [sig_meip] /
       [sig_seip] into mip, those cells live in [WireInv.wire_inv], and
       another hart may move them BETWEEN this dispatch's nodes.  So the
       dispatch arrives as an OBLIGATION whose postcondition MATCHES on the
       answer, and the conclusion is a DISJUNCTION: the machine picks.

     - the FETCH.  M-mode's is a physical read; S-mode's walks Sv39 and may
       fill the TLB, so it WRITES.  Hence the fetch is an obligation too,
       and it is allowed to land on a different file [rsf] than it started
       from.  This is the one place the two modes genuinely differ.

   What is left in the rule is the SHAPE: the base decode (4 bytes, nextPC+4,
   one [execute]) and the compressed one (2 bytes, the [Ext_Zca] gate,
   nextPC+2, and the [ExecuteAs] second [execute]).  So there are TWO rules
   here where [HartMRun] had FOUR: the 4-aligned / 2-mod-4 split was never
   about [run_hart_active] at all -- it is how many chunks the physical fetch
   reads, and it belongs to the fetch obligation's discharge.

   [HartMRun]'s four rules are recovered as instances (dispatch :=
   [swp_dispatchInterrupt_M], fetch := one of [HartMFetch]'s three,
   [rsf := rs]), and their statements are unchanged: with the dispatch pinned
   to [None] the trap disjunct is [False] and drops out. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar.
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* Three pure facts the rules below need.  They are privilege-generic and were
   only ever parked in [HartMRun]'s preamble; they live here so that the
   generic file does not have to depend on the M-mode one. *)

(* the compressed-extension gate, as a read equation (HartMDecode carries the
   same fact for the pilot's decode; restated here so this file does not
   depend on the pilot) *)
Lemma cE_Zca_read :
  currentlyEnabled Ext_Zca
  = Defs.bind (Defs.read_reg misa)
      (fun v : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_C v) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.

Lemma hfrun_cE_Zca (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D ->
  eq_vec (_get_Misa_C (register_lookup misa rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hfrun 4 D Drw rs (currentlyEnabled Ext_Zca) = Some (true, rs).
Proof.
  intros HD HC. rewrite cE_Zca_read.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.returnm returnM].
  rewrite HC.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

(* the landing-pad gate: generic, and needed by every arm below (it was
   sitting in the pilot file, which no other caller can reach) *)
Lemma hfrun_lpad (D Drw : gset register) (rs : regstate) :
  (elp : register) ∈ D ->
  eq_vec (register_lookup elp rs)
    (landing_pad_bits_backwards LP_EXPECTED) = false ->
  hfrun 8 D Drw rs (is_landing_pad_expected tt) = Some (false, rs).
Proof.
  intros HD Help. unfold is_landing_pad_expected.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD) Help.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

Lemma mcer_early_return {E R A : Type} (r : R)
    (K : A -> Defs.monadR R E R) :
  Defs.catch_early_return (Defs.bind (Defs.early_return (A := A) r) K)
  = Interface.Ret r.
Proof. reflexivity. Qed.

Section rungen.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac r_glue :=
    cbn beta iota zeta delta
      [Defs.returnm returnM returnR Defs.returnR andb orb negb not
       Instances.generic_eq Instances.generic_neq get_config_rvfi
       get_config_print_instr].

  Lemma swp_run_hart_active_gen_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate)
      (Q : regstate -> Prop) (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (i : instruction) (nl : nat) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* THE DISPATCH, abstract: the machine picks the arm *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (* THE FETCH, abstract: this is the ONLY thing that differs by mode *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)⌝ ∗
                    ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)).
  Proof.
    intros Hdisj HDpriv HDpc HDnpc Hpriv Hpc Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hex".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt p) _ _ C HC
              with "[Hrw Hro Hdisp] [-]").
    { iApply ("Hdisp" with "Hrw Hro"). }
    iIntros (o) "Ho".
    destruct o as [[ii pr] |].
    - (* ---- THE TRAP ARM: early return, nothing else runs ---- *)
      cbn beta iota. rewrite mcer_early_return.
      iApply ("Hcont" $! (Step_Pending_Interrupt (ii, pr))).
      iLeft. iExists ii, pr. by iFrame.
    - (* ---- THE RETIRE ARM: on into the fetch ---- *)
      iDestruct "Ho" as "[Hrw Hro]".
      cbn beta iota. rewrite mbind0_ret.
      iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hfet] [-]").
      { iApply ("Hfet" with "Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)".
      cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
        fetch_callback get_config_print_instr].
      iApply (swp_use_cer (ext_decode w) _ _ C HC with "[Hrw Hro] [-]").
      { iApply (swp_span Drw Dro Df rsf rsf _ _ Hdisj Hdec
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". r_glue.
      rewrite mbind0_ret.
      iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_hfrun nl Drw Dro Df rsf rsf _ _ Hdisj Hlpad
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". r_glue.
      rewrite mbind_ret. r_glue.
      iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned Drw Dro Df rsf _ Hdisj HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
      iApply (swp_use_cer2
                (Defs.write_reg (R_bitvector_64 nextPC)
                   (add_vec_int pc 4)) _ _ _ C HC with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rsf _ _ Hdisj HDnpc
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hex] [-]").
      { iApply ("Hex" with "Hrw Hro"). }
      iIntros (v) "(-> & HEx)".
      iDestruct "HEx" as (rs2) "(%HQ & Hrw & Hro & HR)". r_glue.
      rewrite mcer_ret.
      iApply ("Hcont" $! (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w))).
      iRight. iSplitR "Hrw Hro HR"; [ by iPureIntro | ].
      iExists rs2. by iFrame.
  Qed.

  (* the fixed-post-file reading: the [_ex] rule at [Q := (= rs2)].  Every
     caller that knows its post file up front uses this one. *)
  Lemma swp_run_hart_active_gen (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf rs2 : regstate) (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (i : instruction) (nl : nat) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode w) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* THE DISPATCH, abstract: the machine picks the arm *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (* THE FETCH, abstract: this is the ONLY thing that differs by mode *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_Base w⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 4) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)).
  Proof.
    intros Hdisj HDpriv HDpc HDnpc Hpriv Hpc Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hex".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_gen_ex Drw Dro Df rs rsf
                   (fun r => r = rs2) p pc w i nl R Qi
                   Hdisj HDpriv HDpc HDnpc Hpriv Hpc Hdec Hlpad
                   with "Hcert Hrw Hro Hdisp Hfet [Hex]") ].
    - iIntros (st) "[Hi | (-> & Hr)]".
      { iLeft. iApply "Hi". }
      iDestruct "Hr" as (r2) "(-> & Hrw & Hro & HR)". iRight. by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hex" with "Hrw Hro") ].
      iIntros (e) "(-> & Hrw & Hro & HR)".
      iSplitR "Hrw Hro HR"; [ by iPureIntro | ]. iExists rs2. by iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE RVC TWIN.  Same three abstractions; the shape differences are the *)
  (* compressed decode, the [Ext_Zca] gate, nextPC+2, and the [ExecuteAs]  *)
  (* second execute.                                                      *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_gen_rvc_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate)
      (Q : regstate -> Prop) (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (i other : instruction) (nl : nat) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    eq_vec (_get_Misa_C (register_lookup misa rsf))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int pc 2) rsf) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int pc 2) rsf) Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute other)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h)⌝ ∗
                    ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)).
  Proof.
    intros Hdisj HDpriv HDmisa HDpc HDnpc Hpriv Hpc HmisaC Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hexp Hex".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt p) _ _ C HC
              with "[Hrw Hro Hdisp] [-]").
    { iApply ("Hdisp" with "Hrw Hro"). }
    iIntros (o) "Ho".
    destruct o as [[ii pr] |].
    - cbn beta iota. rewrite mcer_early_return.
      iApply ("Hcont" $! (Step_Pending_Interrupt (ii, pr))).
      iLeft. iExists ii, pr. by iFrame.
    - iDestruct "Ho" as "[Hrw Hro]".
      cbn beta iota. rewrite mbind0_ret.
      iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hfet] [-]").
      { iApply ("Hfet" with "Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)".
      cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
        fetch_callback get_config_print_instr].
      iApply (swp_use_cer (ext_decode_compressed h) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_span Drw Dro Df rsf rsf _ _ Hdisj Hdec
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". r_glue.
      rewrite mbind0_ret.
      iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_hfrun nl Drw Dro Df rsf rsf _ _ Hdisj Hlpad
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". r_glue.
      rewrite mbind_ret. r_glue.
      iApply (swp_use_cer (currentlyEnabled Ext_Zca) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_hfrun 4 Drw Dro Df rsf rsf _ _ Hdisj
                  (hfrun_cE_Zca (Drw ∪ Dro) Drw rsf HDmisa HmisaC)
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". r_glue.
      iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
                with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned Drw Dro Df rsf _ Hdisj HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
      iApply (swp_use_cer2
                (Defs.write_reg (R_bitvector_64 nextPC)
                   (add_vec_int pc 2)) _ _ _ C HC with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rsf _ _ Hdisj HDnpc
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hexp] [-]").
      { iApply ("Hexp" with "Hrw Hro"). }
      iIntros (v) "(-> & Hrw & Hro)". r_glue.
      iApply (swp_use_cer (execute other) _ _ C HC with "[Hrw Hro Hex] [-]").
      { iApply ("Hex" with "Hrw Hro"). }
      iIntros (v) "(-> & HEx)".
      iDestruct "HEx" as (rs2) "(%HQ & Hrw & Hro & HR)". r_glue.
      rewrite mcer_ret.
      iApply ("Hcont" $! (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h))).
      iRight. iSplitR "Hrw Hro HR"; [ by iPureIntro | ].
      iExists rs2. by iFrame.
  Qed.

  (* the fixed-post-file reading: the [_ex] rule at [Q := (= rs2)]. *)
  Lemma swp_run_hart_active_gen_rvc (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf rs2 : regstate) (p : Privilege)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (i other : instruction) (nl : nat) (R : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    register_lookup cur_privilege rs = p ->
    register_lookup (R_bitvector_64 PC) rsf = pc ->
    eq_vec (_get_Misa_C (register_lookup misa rsf))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hval (Drw ∪ Dro) Drw rsf (ext_decode_compressed h) i rsf ->
    hfrun nl (Drw ∪ Dro) Drw rsf (is_landing_pad_expected tt)
      = Some (false, rsf) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => match o with
                   | Some (ii, pr) => Qi ii pr
                   | None => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro
                   end)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (fetch tt)
         (fun r => ⌜r = F_RVC h⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int pc 2) rsf) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int pc 2) rsf) Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc 2) rsf) Dro -∗
     swp (execute other)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h)⌝ ∗
                    hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)).
  Proof.
    intros Hdisj HDpriv HDmisa HDpc HDnpc Hpriv Hpc HmisaC Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hdisp Hfet Hexp Hex".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_gen_rvc_ex Drw Dro Df rs rsf
                   (fun r => r = rs2) p pc h i other nl R Qi
                   Hdisj HDpriv HDmisa HDpc HDnpc Hpriv Hpc HmisaC Hdec Hlpad
                   with "Hcert Hrw Hro Hdisp Hfet Hexp [Hex]") ].
    - iIntros (st) "[Hi | (-> & Hr)]".
      { iLeft. iApply "Hi". }
      iDestruct "Hr" as (r2) "(-> & Hrw & Hro & HR)". iRight. by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hex" with "Hrw Hro") ].
      iIntros (e) "(-> & Hrw & Hro & HR)".
      iSplitR "Hrw Hro HR"; [ by iPureIntro | ]. iExists rs2. by iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE TRAP-ONLY COROLLARY.  Not an instance of the two above: a caller  *)
  (* that knows the dispatch traps has no instruction to fetch, so it owes *)
  (* neither the fetch nor the execute.                                    *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_intr_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (Q : regstate -> Prop) (p : Privilege)
      (ii : InterruptType) (pr : Privilege) (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = p ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => ⌜o = Some (ii, pr)⌝ ∗ ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                   hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗
                 ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R).
  Proof.
    intros Hdisj HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hdisp".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt p) _ _ C HC
              with "[Hrw Hro Hdisp] [-]").
    { iApply ("Hdisp" with "Hrw Hro"). }
    iIntros (v) "(-> & HEx)". cbn beta iota.
    rewrite mcer_early_return.
    iApply ("Hcont" $! (Step_Pending_Interrupt (ii, pr))).
    iSplitR "HEx"; [ by iPureIntro | ]. iExact "HEx".
  Qed.

  (* the fixed-post-file reading: the [_ex] rule at [Q := (= rs2)]. *)
  Lemma swp_run_hart_active_intr (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (p : Privilege)
      (ii : InterruptType) (pr : Privilege) (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = p ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (dispatchInterrupt p)
         (fun o => ⌜o = Some (ii, pr)⌝ ∗ hreg_frame rs Drw ∗
                   hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    intros Hdisj HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Hdisp".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_intr_ex Drw Dro Df rs (fun r => r = rs)
                   p ii pr R Hdisj HDpriv Hpriv
                   with "Hcert Hrw Hro [Hdisp]") ].
    - iIntros (st) "(-> & Hr)".
      iDestruct "Hr" as (r2) "(-> & Hrw & Hro & HR)". by iFrame.
    - iIntros "Hrw Hro".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hdisp" with "Hrw Hro") ].
      iIntros (o) "(-> & Hrw & Hro & HR)".
      iSplitR "Hrw Hro HR"; [ by iPureIntro | ]. iExists rs. by iFrame.
  Qed.

End rungen.
