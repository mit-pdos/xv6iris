(* HartMLeaf.v -- THE LEAF: [WP Loop] from [WP Loop] through one real
   instruction, composed from the per-model-function [swp] facts.

   There is no new machinery here at all -- that is the point.  The file is
   [try_step]'s own spine, walked with [swp_bind_use] / [swp_use_cerN],
   with each call discharged by the fact that already exists for it, the
   register file threaded by [t_peel], and the leaf-local data (the word,
   the text bytes, the flag cell, the page-boundary and GPR equations)
   supplied as premises. *)
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
        HartMFetch HartMDecode HartMStore HartPilot.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec.
Local Open Scope Z_scope.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Local Ltac l_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq get_config_rvfi].

Local Lemma hfrun_cE_Zca (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D ->
  eq_vec (_get_Misa_C (register_lookup misa rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hfrun 4 D Drw rs (currentlyEnabled Ext_Zca) = Some (true, rs).
Proof.
  intros HD HC. rewrite cE_Zca_eq. d_cbn.
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD). d_cbn.
  rewrite HC. d_cbn. apply hfrun_ret.
Qed.

(* THE POST-STATE of one cycle body.  Three writes are PINNED -- the
   minstret_increment flag, nextPC (the compressed instruction is 2 bytes)
   and PC (tick_pc commits nextPC) -- and minstret is left as a parameter.
   Naming the file is what lets a caller say where the machine ended; an
   existential over the WHOLE file says only that the frames came back,
   which specifies nothing, since a frame constrains only its own
   footprint and agreement-on-nothing is vacuous.

   MINSTRET IS THE ONE CELL WORTH QUANTIFYING, and quantifying its VALUE
   rather than pinning it is what makes the statement branch-free: whether
   the counter bumps depends on a config bit, and BOTH branches are
   value-agnostic, so a caller that does not care what minstret holds
   needs no premise about it.  That is the raw-cell shadow of what design
   §5 actually prescribes -- minstret and minstret_increment belong in
   [MinstretInv], touched by single-node rules that open the invariant
   around exactly that node, and the invariant pins no value for exactly
   this reason.  [MinstretInv] is above the red line, so it cannot be
   named here yet; B′ replaces this parameter with the invariant. *)
Definition hp_post (rs : regstate) (mi : SailStdpp.Values.mword 64)
    : regstate :=
  register_set (R_bitvector_64 minstret) mi
    (register_set (R_bitvector_64 PC) (add_vec_int hp_pc 2)
       (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
          (register_set (R_bool minstret_increment)
             (minstret_inc_flag
                (register_lookup (R_bitvector_32 mcountinhibit) rs)
                (register_lookup (R_bitvector_64 minstretcfg) rs)) rs))).

(* setting a register to the value it already has changes no lookup *)
Lemma reg_set_id_agree (D : gset register) (r : register) (rs : regstate) :
  reg_agree_on D (register_set r (register_lookup r rs) rs) rs.
Proof.
  intros r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - by rewrite register_lookup_set.
  - by rewrite (irrelevant_register_set r' r rs _
                  (register_beq_false r' r Hne)).
Qed.


(* ====================================================================== *)
(* THE FOOTPRINTS.  One [Drw] now (the old file needed two, a span one and *)
(* a batch one; [swp] takes a single pair everywhere), and the read-only   *)
(* pins.  RAW-CELL form: the counter and clock cells are OWNED here        *)
(* because [MinstretInv]/[clock_inv] are above the red line; B′ moves them *)
(* into the invariants and they leave [Drw].                               *)
(* ====================================================================== *)

Definition ml_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register);
     (R_bitvector_64 x14 : register); (R_bitvector_64 x15 : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 minstret : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

Definition ml_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register); (misa : register);
     (hart_state : register); (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register);
     (R_bitvector_64 mcyclecfg : register); (pma_regions : register);
     (pmpcfg_n : register); (htif_tohost_base : register);
     (elp : register); (mseccfg : register);
     (R_bitvector_64 mtimecmp : register);
     (R_bitvector_64 stimecmp : register);
     (R_bitvector_64 menvcfg : register) ]}.

Lemma ml_disj : ml_Drw ## ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.

Lemma ml_in_priv : (cur_privilege : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_misa : (misa : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mst : (mstatus : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_hart : (hart_state : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_cycfg : (R_bitvector_64 mcyclecfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_pma : (pma_regions : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_pcfg : (pmpcfg_n : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_htif : (htif_tohost_base : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_tcmp : (R_bitvector_64 mtimecmp : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_menv : (R_bitvector_64 menvcfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_PC : (R_bitvector_64 PC : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_nPC : (R_bitvector_64 nextPC : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_ms : (R_bitvector_64 minstret : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mi : (R_bool minstret_increment : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_cy : (R_bitvector_64 mcycle : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_ti : (R_bitvector_64 mtime : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_ip : (R_bitvector_64 mip : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.

Lemma ml_w_PC : (R_bitvector_64 PC : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_nPC : (R_bitvector_64 nextPC : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_mi : (R_bool minstret_increment : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_ms : (R_bitvector_64 minstret : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_cy : (R_bitvector_64 mcycle : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_ti : (R_bitvector_64 mtime : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_ip : (R_bitvector_64 mip : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.

Section leaf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* THE DFRAC ASSIGNMENT for the read-only frame.  Five config cells are
     PERSISTENT in the tree's hw_config (misa, pma_regions,
     htif_tohost_base, elp, mseccfg); the rest are fractional.  Keeping
     the split faithful to that is what lets a caller hand over the cells
     it actually holds. *)
  Definition ml_Df (q : Qp) : register -> dfrac := fun r =>
    if decide (r = (misa : register)) then DfracDiscarded
    else if decide (r = (pma_regions : register)) then DfracDiscarded
    else if decide (r = (htif_tohost_base : register)) then DfracDiscarded
    else if decide (r = (elp : register)) then DfracDiscarded
    else if decide (r = (mseccfg : register)) then DfracDiscarded
    else DfracOwn q.

  Local Ltac dfq :=
    unfold ml_Df;
    repeat first [ rewrite decide_True; [reflexivity|reflexivity]
                 | rewrite decide_False; [|discriminate] ];
    reflexivity.

  Lemma ml_Df_misa q : ml_Df q misa = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_pma q : ml_Df q pma_regions = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_htif q : ml_Df q htif_tohost_base = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_elp q : ml_Df q elp = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_sec q : ml_Df q mseccfg = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_priv q : ml_Df q cur_privilege = DfracOwn q.
  Proof. dfq. Qed.


  (* THE FRAME <-> POINTS-TO BRIDGE.  A caller holds individual cells; the
     walk wants frames.  These are the only two lemmas that convert, and
     they are what make the leaf's statement something a caller can
     actually feed. *)
  Lemma ml_rw_split (rs : regstate) :
    hreg_frame rs ml_Drw ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs ∗
     (R_bitvector_64 x14) ↦ᵣ register_lookup (R_bitvector_64 x14) rs ∗
     (R_bitvector_64 x15) ↦ᵣ register_lookup (R_bitvector_64 x15) rs ∗
     (R_bool minstret_increment) ↦ᵣ
       register_lookup (R_bool minstret_increment) rs ∗
     (R_bitvector_64 minstret) ↦ᵣ
       register_lookup (R_bitvector_64 minstret) rs ∗
     (R_bitvector_64 mcycle) ↦ᵣ register_lookup (R_bitvector_64 mcycle) rs ∗
     (R_bitvector_64 mtime) ↦ᵣ register_lookup (R_bitvector_64 mtime) rs ∗
     (R_bitvector_64 mip) ↦ᵣ register_lookup (R_bitvector_64 mip) rs)%I.
  Proof.
    rewrite /hreg_frame /ml_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma ml_ro_split (q : Qp) (rs : regstate) :
    hreg_frame_ro (ml_Df q) rs ml_Dro ⊣⊢
    (reg_pointsto cur_privilege (DfracOwn q)
       (register_lookup cur_privilege rs) ∗
     reg_pointsto mstatus (DfracOwn q) (register_lookup mstatus rs) ∗
     reg_pointsto misa DfracDiscarded (register_lookup misa rs) ∗
     reg_pointsto hart_state (DfracOwn q) (register_lookup hart_state rs) ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) (DfracOwn q)
       (register_lookup (R_bitvector_32 mcountinhibit) rs) ∗
     reg_pointsto (R_bitvector_64 minstretcfg) (DfracOwn q)
       (register_lookup (R_bitvector_64 minstretcfg) rs) ∗
     reg_pointsto (R_bitvector_64 mcyclecfg) (DfracOwn q)
       (register_lookup (R_bitvector_64 mcyclecfg) rs) ∗
     reg_pointsto pma_regions DfracDiscarded
       (register_lookup pma_regions rs) ∗
     reg_pointsto pmpcfg_n (DfracOwn q) (register_lookup pmpcfg_n rs) ∗
     reg_pointsto htif_tohost_base DfracDiscarded
       (register_lookup htif_tohost_base rs) ∗
     reg_pointsto elp DfracDiscarded (register_lookup elp rs) ∗
     reg_pointsto mseccfg DfracDiscarded (register_lookup mseccfg rs) ∗
     reg_pointsto (R_bitvector_64 mtimecmp) (DfracOwn q)
       (register_lookup (R_bitvector_64 mtimecmp) rs) ∗
     reg_pointsto (R_bitvector_64 stimecmp) (DfracOwn q)
       (register_lookup (R_bitvector_64 stimecmp) rs) ∗
     reg_pointsto (R_bitvector_64 menvcfg) (DfracOwn q)
       (register_lookup (R_bitvector_64 menvcfg) rs))%I.
  Proof.
    rewrite /hreg_frame_ro /ml_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite !(ml_Df_misa q) !(ml_Df_pma q) !(ml_Df_htif q) !(ml_Df_elp q)
      !(ml_Df_sec q).
    unfold ml_Df.
    repeat (rewrite decide_False; [|discriminate]).
    by rewrite !bi.sep_assoc.
  Qed.

  (* the read-only frame's counterpart of [hreg_frame_ext] (HartSpan keeps
     its copy Local) *)
  Local Lemma hreg_frame_ro_ext' (Df : register -> dfrac) (rs rs' : regstate)
      (Dro : gset register) :
    reg_agree_on Dro rs rs' ->
    hreg_frame_ro Df rs Dro ⊣⊢ hreg_frame_ro Df rs' Dro.
  Proof.
    intros Hag. rewrite /hreg_frame_ro. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.

  (* [run_hart_active] at the pilot's word: dispatch, fetch, decode,
     execute.  Everything below the [swp_use_cer] peels is a fact that
     already exists. *)
  Lemma swp_run_hart_active_hp (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n)
      (pa : SailStdpp.Values.mword 64) (d : SailStdpp.Values.mword 64) :
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
    register_lookup (R_bitvector_64 PC) rs = hp_pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hfrun 8 (Drw ∪ Dro) Drw rs (is_landing_pad_expected tt)
      = Some (false, rs) ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram hp_pc ->
    neq_vec (access_vec_dec hp_pc 0) zerobit = false ->
    neq_vec (access_vec_dec hp_pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr hp_pc) 4 = true ->
    is_aligned_paddr (Physaddr hp_pc) 4 = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    hfrun 4 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
      (rX_bits (creg2reg_idx
                  (encdec_creg_backwards (subrange_vec_dec hp_half 4 2))))
      = Some (d, register_set (R_bitvector_64 nextPC)
                    (add_vec_int hp_pc 2) rs) ->
    hfrun 8 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
      (get_transformed_data_addr
         (creg2reg_idx (encdec_creg_backwards (subrange_vec_dec hp_half 9 7)))
         (sign_extend' 64
            (zero_extend' 12
               (concat_vec
                  (concat_vec
                     (concat_vec (subrange_vec_dec hp_half 5 5)
                        (subrange_vec_dec hp_half 12 10))
                     (subrange_vec_dec hp_half 6 6))
                  (MachineWord.MachineWord.N_to_word
                     (MachineWord.MachineWord.Z_idx 2)
                     (BinaryString.Raw.to_N "00" 0))))) (Store Data) 4)
      = Some (Ext_DataAddr_OK (Virtaddr pa),
              register_set (R_bitvector_64 nextPC)
                (add_vec_int hp_pc 2) rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) hp_pc 4 = Some hp_wf⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value
                      (mwrite_req pa
                         (TypeCasts.autocast (subrange_vec_dec d 31 0)))))
                σ.(mdev)))) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Execute (RETIRE_SUCCESS,
                        zero_extend' 32 hp_half)⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int hp_pc 2) rs) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int hp_pc 2) rs) Dro).
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg HDhtif
      Hpriv Hpc Hpma Hpcfg Hhtif HmisaS HmIE HmisaC Hlpad Hunlock Hpallow
      Hram
      Hb0 Hb1 Hva Hpa Hmprv Hsram Hsva Hspa Hsplit Hrx Hgta.
    iIntros "#Hcert Hrw Hro Hmem Hwmem".
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
    { iApply (swp_fetch_ram Drw Dro Df rs hp_pc pmar0 pcfg hp_wf Hdisj HDpc
                HDmst HDpriv HDpma HDcfg HDhtif Hpc Hpriv Hpma Hpcfg
                Hhtif Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite hp_isRVC. cbn beta iota.
    cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
      fetch_callback get_config_print_instr].
    iApply (swp_use_cer (ext_decode_compressed hp_half) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_decode_hp Drw Dro Df rs Hdisj HDmisa HmisaC
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 8 Drw Dro Df rs rs _ _ Hdisj Hlpad
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    rewrite mbind_ret. l_glue.
    iApply (swp_use_cer (currentlyEnabled Ext_Zca) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_cE_Zca (Drw ∪ Dro) Drw rs HDmisa HmisaC)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer2
              (Defs.write_reg (R_bitvector_64 nextPC)
                 (add_vec_int hp_pc 2)) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HDnpc
                with "Hcert Hrw Hro"). }
    iIntros (u) "[Hrw Hro]".
    iApply (swp_use_cer _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_execute_C_SW Drw Dro Df _ _ _ _ Hdisj
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    cbn beta iota zeta delta [execute].
    iApply (swp_use_cer _ _ _ C HC with "[Hrw Hro Hwmem] [-]").
    { iApply (swp_execute_STORE Drw Dro Df
                (register_set (R_bitvector_64 nextPC)
                   (add_vec_int hp_pc 2) rs) _ _ _ d pa pmar0 pcfg Hdisj
                HDmst HDpriv HDpma HDcfg HDhtif
                ltac:(t_peel; exact Hpriv) ltac:(t_peel; exact Hpma)
                ltac:(t_peel; exact Hpcfg) ltac:(t_peel; exact Hhtif)
                ltac:(t_peel; exact Hmprv) Hunlock Hpallow Hsram Hsva Hspa
                Hsplit Hrx Hgta with "Hcert Hrw Hro Hwmem"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Step_Execute (RETIRE_SUCCESS,
                                      zero_extend' 32 hp_half))).
    by iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE LEAF.  [WP Loop] from [WP Loop], through the honest wrapper at     *)
  (* BOTH ticks, for one real instruction.                                  *)
  (* ==================================================================== *)

  Lemma swp_try_step_hp (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n)
      (pa : SailStdpp.Values.mword 64) (d : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    (R_bool minstret_increment : register) ∈ Drw ->
    (R_bool minstret_increment : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstret : register) ∈ Drw ->
    (R_bitvector_64 minstret : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup hart_state rs = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 PC) rs = hp_pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    hfrun 8 (Drw ∪ Dro) Drw
      (register_set (R_bool minstret_increment)
         (minstret_inc_flag
            (register_lookup (R_bitvector_32 mcountinhibit) rs)
            (register_lookup (R_bitvector_64 minstretcfg) rs)) rs)
      (is_landing_pad_expected tt)
      = Some (false, register_set (R_bool minstret_increment)
                       (minstret_inc_flag
                          (register_lookup (R_bitvector_32 mcountinhibit) rs)
                          (register_lookup (R_bitvector_64 minstretcfg) rs))
                       rs) ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram hp_pc ->
    neq_vec (access_vec_dec hp_pc 0) zerobit = false ->
    neq_vec (access_vec_dec hp_pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr hp_pc) 4 = true ->
    is_aligned_paddr (Physaddr hp_pc) 4 = true ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    hfrun 4 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
         (register_set (R_bool minstret_increment)
            (minstret_inc_flag
               (register_lookup (R_bitvector_32 mcountinhibit) rs)
               (register_lookup (R_bitvector_64 minstretcfg) rs)) rs))
      (rX_bits (creg2reg_idx
                  (encdec_creg_backwards (subrange_vec_dec hp_half 4 2))))
      = Some (d, register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
                   (register_set (R_bool minstret_increment)
                      (minstret_inc_flag
                         (register_lookup (R_bitvector_32 mcountinhibit) rs)
                         (register_lookup (R_bitvector_64 minstretcfg) rs))
                      rs)) ->
    hfrun 8 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
         (register_set (R_bool minstret_increment)
            (minstret_inc_flag
               (register_lookup (R_bitvector_32 mcountinhibit) rs)
               (register_lookup (R_bitvector_64 minstretcfg) rs)) rs))
      (get_transformed_data_addr
         (creg2reg_idx (encdec_creg_backwards (subrange_vec_dec hp_half 9 7)))
         (sign_extend' 64
            (zero_extend' 12
               (concat_vec
                  (concat_vec
                     (concat_vec (subrange_vec_dec hp_half 5 5)
                        (subrange_vec_dec hp_half 12 10))
                     (subrange_vec_dec hp_half 6 6))
                  (MachineWord.MachineWord.N_to_word
                     (MachineWord.MachineWord.Z_idx 2)
                     (BinaryString.Raw.to_N "00" 0))))) (Store Data) 4)
      = Some (Ext_DataAddr_OK (Virtaddr pa),
              register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
                (register_set (R_bool minstret_increment)
                   (minstret_inc_flag
                      (register_lookup (R_bitvector_32 mcountinhibit) rs)
                      (register_lookup (R_bitvector_64 minstretcfg) rs))
                   rs)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) hp_pc 4 = Some hp_wf⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value
                      (mwrite_req pa
                         (TypeCasts.autocast (subrange_vec_dec d 31 0)))))
                σ.(mdev)))) -∗
    swp (try_step 0 false)
      (fun _ => ∃ mi : SailStdpp.Values.mword 64,
                  hreg_frame (hp_post rs mi) Drw ∗
                  hreg_frame_ro Df (hp_post rs mi) Dro)%I.
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDhart HDmc HDcfg HDmi HDmi'
      HDms HDms'
      HWpc HDpc HDnpc HDnpc' HDpma HDcfg2 HDhtif
      Hpriv Hhart Hpc Hpma Hpcfg Hhtif HmisaS HmisaC HmIE Hmprv Hlpad
      Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa Hsram Hsva Hspa Hsplit Hrx Hgta.
    iIntros "#Hcert Hrw Hro Hmem Hwmem".
    unfold try_step. cbn beta iota zeta delta [ext_pre_step_hook].
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_bind_use (should_inc_minstret Machine) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_should_inc_minstret Drw Dro Df rs Hdisj HDmc HDcfg
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use
                (Defs.write_reg (R_bool minstret_increment)
                   (minstret_inc_flag
                      (register_lookup (R_bitvector_32 mcountinhibit) rs)
                      (register_lookup (R_bitvector_64 minstretcfg) rs)))
                _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HDmi
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    t_peel. rewrite Hhart.
    (* THE INSTRUCTION *)
    iApply (swp_bind_use (run_hart_active 0) _ _ _
              with "[Hrw Hro Hmem Hwmem] [-]").
    { iApply (swp_run_hart_active_hp Drw Dro Df
                (register_set (R_bool minstret_increment)
                   (minstret_inc_flag
                      (register_lookup (R_bitvector_32 mcountinhibit) rs)
                      (register_lookup (R_bitvector_64 minstretcfg) rs)) rs)
                pmar0 pcfg pa d Hdisj
                HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg2 HDhtif
                ltac:(t_peel; exact Hpriv) ltac:(t_peel; exact Hpc)
                ltac:(t_peel; exact Hpma) ltac:(t_peel; exact Hpcfg)
                ltac:(t_peel; exact Hhtif)
                ltac:(t_peel; exact HmisaS) ltac:(t_peel; exact HmIE)
                ltac:(t_peel; exact HmisaC) Hlpad
                Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa
                ltac:(t_peel; exact Hmprv) Hsram Hsva Hspa Hsplit Hrx Hgta
                with "Hcert Hrw Hro Hmem Hwmem"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    (* the tail: the hart_state assert, tick_pc, the minstret bump *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                with "[Hrw Hro] [-]").
      { iApply (swp_bind_use (Defs.read_reg hart_state) _ _ _
                  with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                    with "Hcert Hrw Hro"). }
        iIntros (v) "(-> & Hrw & Hro)". t_peel. rewrite Hhart.
        cbn beta iota zeta delta [hart_is_active Defs.assert_exp].
        iApply swp_ret. iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". t_peel. rewrite Hhart. l_glue.
    iApply (swp_bind0_use (tick_pc tt) _
              (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
              _ with "[Hrw Hro] [-]").
    { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc' HWpc HDpc
                with "Hcert Hrw Hro"). }
    iIntros (u) "[Hrw Hro]".
    unfold Defs.and_boolM. rewrite /returnM mbind_ret. l_glue.
    iApply (swp_bind_use (Defs.read_reg (R_bool minstret_increment))
              _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDmi'
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". t_peel. l_glue.
    (* THE MINSTRET BUMP.  The branch is left OPEN: both arms reach the
       same post-state shape, differing only in what minstret holds, and
       the postcondition quantifies that value.  A caller that does not
       care what the counter reads therefore needs no premise about the
       config bit at all -- which is the raw-cell shadow of minstret
       living in an invariant that pins no value. *)
    destruct (minstret_inc_flag
                (register_lookup (R_bitvector_32 mcountinhibit) rs)
                (register_lookup (R_bitvector_64 minstretcfg) rs)) eqn:Hmi.
    - iApply (swp_bind0_use _ _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                with "[Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 minstret))
                    _ _ _ with "[Hrw Hro] [-]").
          { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDms'
                      with "Hcert Hrw Hro"). }
          iIntros (v0) "(-> & Hrw & Hro)".
          iApply (swp_write_reg_owned Drw Dro Df _ _ _ Hdisj HDms
                    with "Hcert Hrw Hro"). }
        iIntros (u0) "[Hrw Hro]". l_glue. iApply swp_ret. iFrame. }
      iIntros (u1) "[Hrw Hro]".
      iEval (t_peel) in "Hrw". iEval (t_peel) in "Hro".
      iApply swp_ret. iExists _. unfold hp_post. rewrite Hmi. iFrame.
    - iApply (swp_bind0_use _ _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                with "[Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                  with "[Hrw Hro] [-]").
        { iApply swp_ret. iFrame. }
        iIntros (u2) "[Hrw Hro]". l_glue. iApply swp_ret. iFrame. }
      iIntros (u3) "[Hrw Hro]".
      iEval (t_peel) in "Hrw". iEval (t_peel) in "Hro".
      iApply swp_ret.
      iExists (register_lookup (R_bitvector_64 minstret)
                 (register_set (R_bitvector_64 PC) (add_vec_int hp_pc 2)
                    (register_set (R_bitvector_64 nextPC)
                       (add_vec_int hp_pc 2)
                       (register_set (R_bool minstret_increment)
                          false rs)))).
      unfold hp_post. rewrite Hmi.
      rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree Drw _ _)).
      rewrite (hreg_frame_ro_ext' Df _ _ Dro (reg_set_id_agree Dro _ _)).
      iFrame.
  Qed.

End leaf.
