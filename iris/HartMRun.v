(* HartMRun.v -- [run_hart_active] GENERIC IN THE INSTRUCTION: the [swp]
   replacement for the fetch/decode half of the old tree's
   [InstrBytes.wp_exec_step_decode_execute_inv] and
   [SmodeCore.wp_exec_step_decode_execute_inv_priv].

   THE SHAPE THIS FILE EXISTS TO GET RIGHT.  The old rules handed the caller
   the WHOLE machine state and asked for a successor in one fupd:

     ∀ σ, mstate_interp σ ={⊤∖↑minstretN}=∗ ∃ s_exec,
       ⌜exec (execute i) (set_reg σ nextPC …) = Some (RETIRE_SUCCESS, s_exec)⌝ ∗
       mstate_interp s_exec ∗ (… -∗ ▷ WP Loop)

   That is unsound per-node: other harts step between an instruction's nodes,
   so a successor computed from the σ you saw is stale unless you can name
   what you depend on -- which is a FOOTPRINT, i.e. a frame.  Here the
   obligation is instead one [swp] over [execute i] at the caller's own
   frames, and it is uniform: a register-only instruction discharges it by
   [swp_hfrun], a memory one by the event rules plus its memory obligation
   (HartMStore.swp_execute_STORE is the worked example).

   WHAT STAYS EXACTLY AS IT WAS: the decode arrives as a PURE equation the
   caller supplies, mirroring the old rules' [⌜exec (decode_fetch r) σf =
   Some (i, σf)⌝] premise one-for-one -- only the interpreter changes, from
   [exec] to the footprinted [hfrun].  Everything the fetch needs is
   [HartMFetch.swp_fetch_ram], which was already generic in [pc] and in the
   word. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMCycle HartMDispatch HartMPmp
        HartMFetch.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec.
Local Open Scope Z_scope.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Local Ltac r_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq get_config_rvfi].

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

Section run.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* THE 4-BYTE PATH.  No [Ext_Zca] gate and no [ExecuteAs] stage: the    *)
  (* base decode yields the instruction the caller executes directly.     *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_run_hart_active_base (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs2 : regstate)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (i : instruction) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n) (nl : nat) (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall j, pmpLocked (SailStdpp.Values.vec_access_dec pcfg j) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    is_aligned_paddr (Physaddr pc) 4 = true ->
    (* THE WIDTH: this is the 4-byte path *)
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* THE DECODE, as a pure footprinted characterization -- the caller's own
       premise, exactly where [⌜exec (decode_fetch r) σf = Some (i, σf)⌝] sat.
       [hval] rather than [hfrun] so NO FUEL reaches this interface;
       [HartGoodb.hval_of_goodb] is what the [instr] bundle supplies it
       with, off the decode catalogue's own [goodb] certificate. *)
    hval (Drw ∪ Dro) Drw rs (ext_decode w) i rs ->
    (* the landing-pad gate, likewise *)
    hfrun nl (Drw ∪ Dro) Drw rs (is_landing_pad_expected tt) = Some (false, rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pc 4 = Some w⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC) (add_vec_int pc 4) rs) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC) (add_vec_int pc 4) rs) Dro -∗
     swp (execute i)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R).
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg HDhtif
      Hpriv Hpc Hpma Hpcfg Hhtif HmisaS HmIE Hunlock Hpallow Hram
      Hb0 Hb1 Hva Hpa Hrvc Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hmem Hinstr".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt Machine) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_dispatchInterrupt_M Drw Dro Df rs _ _ Hdisj HDmisa HDmst
                HmisaS HmIE eq_refl eq_refl with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_fetch_ram Drw Dro Df rs pc pmar0 pcfg w Hdisj HDpc
                HDmst HDpriv HDpma HDcfg HDhtif Hpc Hpriv Hpma Hpcfg
                Hhtif Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hrvc. cbn beta iota.
    cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
      fetch_callback get_config_print_instr].
    iApply (swp_use_cer (ext_decode w) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hdec
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun nl Drw Dro Df rs rs _ _ Hdisj Hlpad
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    (* the [and_boolM] SHORT-CIRCUITS at [elp <> LP_EXPECTED]: the model
       never evaluates [is_lpad_instruction], so -- unlike the old
       exec-shaped rule -- no premise about it is needed. *)
    rewrite mbind_ret. r_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer2
              (Defs.write_reg (R_bitvector_64 nextPC)
                 (add_vec_int pc 4)) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HDnpc
                with "Hcert Hrw Hro"). }
    iIntros (u) "[Hrw Hro]".
    iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hinstr] [-]").
    { iApply ("Hinstr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro & HR)". r_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w))).
    by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE 2-BYTE PATH.  Two extra things the base path does not have: the  *)
  (* [Ext_Zca] gate (a misa.C read), and the [ExecuteAs] stage -- the     *)
  (* compressed form expands to a base instruction, which is what then    *)
  (* retires.  Both caller obligations mirror the old rule's F_RVC arm    *)
  (* one-for-one.                                                         *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_run_hart_active_rvc (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs2 : regstate)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (i other : instruction) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n) (nl : nat) (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    (forall j, pmpLocked (SailStdpp.Values.vec_access_dec pcfg j) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    is_aligned_paddr (Physaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    hval (Drw ∪ Dro) Drw rs
      (ext_decode_compressed (subrange_vec_dec w 15 0)) i rs ->
    hfrun nl (Drw ∪ Dro) Drw rs (is_landing_pad_expected tt) = Some (false, rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pc 4 = Some w⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int pc 2) rs) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int pc 2) rs) Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Dro -∗
     swp (execute other)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Execute (RETIRE_SUCCESS,
                         zero_extend' 32 (subrange_vec_dec w 15 0))⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R).
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg HDhtif
      Hpriv Hpc Hpma Hpcfg Hhtif HmisaS HmIE HmisaC Hunlock Hpallow Hram
      Hb0 Hb1 Hva Hpa Hrvc Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hmem Hexp Hinstr".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt Machine) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_dispatchInterrupt_M Drw Dro Df rs _ _ Hdisj HDmisa HDmst
                HmisaS HmIE eq_refl eq_refl with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_fetch_ram Drw Dro Df rs pc pmar0 pcfg w Hdisj HDpc
                HDmst HDpriv HDpma HDcfg HDhtif Hpc Hpriv Hpma Hpcfg
                Hhtif Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hrvc. cbn beta iota.
    cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
      fetch_callback get_config_print_instr].
    iApply (swp_use_cer (ext_decode_compressed (subrange_vec_dec w 15 0))
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hdec
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun nl Drw Dro Df rs rs _ _ Hdisj Hlpad
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    rewrite mbind_ret. r_glue.
    iApply (swp_use_cer (currentlyEnabled Ext_Zca) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_cE_Zca (Drw ∪ Dro) Drw rs HDmisa HmisaC)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer2
              (Defs.write_reg (R_bitvector_64 nextPC)
                 (add_vec_int pc 2)) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HDnpc
                with "Hcert Hrw Hro"). }
    iIntros (u) "[Hrw Hro]".
    iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hexp] [-]").
    { iApply ("Hexp" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    iApply (swp_use_cer (execute other) _ _ C HC
              with "[Hrw Hro Hinstr] [-]").
    { iApply ("Hinstr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro & HR)". r_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Step_Execute (RETIRE_SUCCESS,
                          zero_extend' 32 (subrange_vec_dec w 15 0)))).
    by iFrame.
  Qed.

  (* the 2-mod-4 twin: one HALFWORD fetch, no F_Base branch *)
  Lemma swp_run_hart_active_rvc2 (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs2 : regstate)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (i other : instruction) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n) (nl : nat) (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    (forall j, pmpLocked (SailStdpp.Values.vec_access_dec pcfg j) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram pc ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_paddr (Physaddr pc) 2 = true ->
    isRVC h = true ->
    hval (Drw ∪ Dro) Drw rs
      (ext_decode_compressed h) i rs ->
    hfrun nl (Drw ∪ Dro) Drw rs (is_landing_pad_expected tt) = Some (false, rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pc 2 = Some h⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Dro -∗
     swp (execute i)
       (fun e => ⌜e = ExecuteAs other⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int pc 2) rs) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int pc 2) rs) Dro)) -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC) (add_vec_int pc 2) rs) Dro -∗
     swp (execute other)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Execute (RETIRE_SUCCESS,
                         zero_extend' 32 h)⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R).
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg HDhtif
      Hpriv Hpc Hpma Hpcfg Hhtif HmisaS HmIE HmisaC Hunlock Hpallow Hram
      Hb0 Hb1 Hpa Hrvc Hdec Hlpad.
    iIntros "#Hcert Hrw Hro Hmem Hexp Hinstr".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt Machine) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_dispatchInterrupt_M Drw Dro Df rs _ _ Hdisj HDmisa HDmst
                HmisaS HmIE eq_refl eq_refl with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_fetch_ram_rvc2 Drw Dro Df rs pc pmar0 pcfg h Hdisj
                HDpc HDmst HDpriv HDmisa HDpma HDcfg HDhtif Hpc Hpriv Hpma
                Hpcfg Hhtif HmisaC Hunlock Hpallow Hram Hb0 Hb1 Hpa Hrvc
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
      fetch_callback get_config_print_instr].
    iApply (swp_use_cer (ext_decode_compressed h)
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hdec
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun nl Drw Dro Df rs rs _ _ Hdisj Hlpad
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    rewrite mbind_ret. r_glue.
    iApply (swp_use_cer (currentlyEnabled Ext_Zca) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_cE_Zca (Drw ∪ Dro) Drw rs HDmisa HmisaC)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer2
              (Defs.write_reg (R_bitvector_64 nextPC)
                 (add_vec_int pc 2)) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HDnpc
                with "Hcert Hrw Hro"). }
    iIntros (u) "[Hrw Hro]".
    iApply (swp_use_cer (execute i) _ _ C HC with "[Hrw Hro Hexp] [-]").
    { iApply ("Hexp" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". r_glue.
    iApply (swp_use_cer (execute other) _ _ C HC
              with "[Hrw Hro Hinstr] [-]").
    { iApply ("Hinstr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro & HR)". r_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Step_Execute (RETIRE_SUCCESS,
                          zero_extend' 32 h))).
    by iFrame.
  Qed.

End run.
