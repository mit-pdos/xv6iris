(* WpIntrInv.v -- the S-mode INTERRUPT-ABSORBING STEP ENGINE, per node.

   THE DESIGN OF THE SIE GHOST.  The SIE ghost variable is CANONICAL per hart
   -- [IntrDefs.sie_gname] = [sie_name cpu_id], exactly like [reg_name] /
   [strans_name] -- so nothing in this tier carries a ghost argument: the
   ambient [CpuId] determines the ghost.  It is split into THREE pieces:

     - 1/2 rides with the mstatus cell, tied to the LIVE [mstatus.SIE] bit
       (the half [sconf] bundles);
     - 1/4 is the KERNEL-CODE token: client code keeps it to reason about
       whether interrupts are currently enabled or disabled (push_off /
       pop_off bookkeeping);
     - 1/4 rides inside [IntrDefs.intr_res], together with the [stvec]
       register and -- keyed on the ghost value being 1 -- a WP for running
       the interrupt handler ([intr_handler_spec], under a [▷]).

   Changing SIE therefore requires ALL THREE pieces (1/2 + 1/4 + 1/4 = 1,
   [sie_ghost_flip]), so interrupts cannot be enabled without the installed
   handler resource in hand.

   THE ENGINE.  [wp_exec_step_intr] runs ONE S-mode instruction at [pc0] with
   interrupts enabled, absorbing an arbitrary number of pending interrupts
   first (Löb induction over the trap + handler round trip).  It is a
   per-NODE engine now: one iteration is one [HartStepAny.swp_exec_step_any]
   at an S-mode frame, whose body is the fetch/decode/execute walk
   ([HartRunGen.swp_run_hart_active_gen] and its three siblings) with the
   dispatch discharged by [WpIntrCore.swp_dispatchInterrupt_S] and the fetch
   by [HartSTrans.swp_fetch_S*] over the converted page walk.  The two arms:

     - PENDING: the trap itself is [swp_handle_interrupt_S] (WpIntrCore.v),
       a hand-walk of [handle_interrupt i Supervisor] over the trap CSRs
       ([sie_cap]'s enabled arm supplies sepc/scause/stval/stvec).  After the
       cycle's own tail the engine flips the SIE ghost, updates [sret_bits],
       assembles [ihs_entry_of], runs [intr_handler_spec_apply] and re-enters
       the Löb ON THE HART THE HANDLER RETURNED TO;
     - RETIRE: the caller's obligation gets the S-mode bundles as CELLS and
       owes one [swp (execute i)].

   THE FOOTPRINT SPLIT, and why it is not [WpSFrames]'s.  The cycle rule
   needs a frame for the WHOLE cycle -- the boundary, the prelude, the tick.
   The leaf needs [sconf] and [sie_cap] DURING the instruction, and those own
   cells ([cur_privilege], [mstatus], [mie], [mideleg], [menvcfg], [satp],
   [tlb], the two PMP cells) that no frame may hold at the same time.  The
   resolution is that only the cells nothing else claims stay in the cycle's
   frame -- [i_Drw] / [i_Dro] below -- and the frame is ENLARGED to
   [HartSFrame]'s [s_Drw] / [s_Dro] exactly around the dispatch, the fetch
   and the trap, where the bundle is open anyway.

   [nextPC] IS THE ONE CELL HELD AT A HALF, and that is load-bearing rather
   than an economy.  The cycle rule's continuation only says that the file it
   lands on agrees with [wrap_post rs2 mi] for SOME [rs2] the body chose, so
   the landing pc is an existential and the resources the arms carry (the
   leaf's continuation, the handler's entry package) are indexed by it.  The
   second half of [nextPC], kept out of the frame by the arm, turns that
   existential into an EQUATION by [reg_pointsto_agree] -- one cell doing the
   job a stronger cycle rule would otherwise have to do.

   The per-trap frame is the CONCRETE [intr_frame]: [stack_own] of depth AT
   LEAST [kv_frame_slots] below the interrupted sp -- the kernel must
   maintain that much free stack at every interrupts-enabled instruction.
   [kernelvec_handler_spec] proves the real kernelvec ([wp_kernelvec],
   ProofKernelvec.v) satisfies the contract; [SpecKernelvec.v] is the
   interface, [LinkKernelvec.v] the instantiation. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
From iris.bi.lib Require Import fractional.
From iris.program_logic Require Import language lifting weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr RegFile HartTp.
Require Import HartSwp HartLift HartSpan HartSpanChar HartRegNode
        HartMCycle HartStepAny HartRunGen HartSFrame HartSTrans.
Require Import SmodeCore WpSFrames KptShare KptPt KMap SRegime StackOwn.
Require Import MstatusBits WpIntrCore.
Require Export IntrDefs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE CYCLE'S OWN FOOTPRINT.                                          *)
(*                                                                       *)
(* Exactly the cells [HartStepAny.swp_exec_step_any] demands and nothing  *)
(* else: PC / nextPC / the two minstret cells / the three clock cells /   *)
(* hart_state / cur_privilege / the two counter-config cells.  Every      *)
(* other S-mode cell belongs to [sconf] or [sie_cap] and is lent to the   *)
(* frame only for the stretches that need it (§2).                        *)
(* ===================================================================== *)
Definition i_Drw : gset register :=
  {[ (R_bitvector_64 PC : register);
     (R_bitvector_64 minstret : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

Definition i_Dro : gset register :=
  {[ (R_bitvector_64 nextPC : register);
     (hart_state : register);
     (cur_privilege : register);
     (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register) ]}.

Lemma i_disj : i_Drw ## i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.

Lemma i_w_PC : (R_bitvector_64 PC : register) ∈ i_Drw.
Proof. rewrite /i_Drw. set_solver. Qed.
Lemma i_w_ms : (R_bitvector_64 minstret : register) ∈ i_Drw.
Proof. rewrite /i_Drw. set_solver. Qed.
Lemma i_w_mi : (R_bool minstret_increment : register) ∈ i_Drw.
Proof. rewrite /i_Drw. set_solver. Qed.
Lemma i_w_cy : (R_bitvector_64 mcycle : register) ∈ i_Drw.
Proof. rewrite /i_Drw. set_solver. Qed.
Lemma i_w_ti : (R_bitvector_64 mtime : register) ∈ i_Drw.
Proof. rewrite /i_Drw. set_solver. Qed.
Lemma i_w_ip : (R_bitvector_64 mip : register) ∈ i_Drw.
Proof. rewrite /i_Drw. set_solver. Qed.

Lemma i_in_PC : (R_bitvector_64 PC : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.
Lemma i_in_nPC : (R_bitvector_64 nextPC : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.
Lemma i_in_ms : (R_bitvector_64 minstret : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.
Lemma i_in_mi : (R_bool minstret_increment : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.
Lemma i_in_priv : (cur_privilege : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.
Lemma i_in_hart : (hart_state : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.
Lemma i_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.
Lemma i_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ i_Drw ∪ i_Dro.
Proof. rewrite /i_Drw /i_Dro. set_solver. Qed.

(* the two counter-config cells are frozen ([minstret_res] holds them at
   [↦ᵣ□]); [nextPC] is the HALF (see the header). *)
Definition i_Df : register -> dfrac := fun r =>
  if decide (r = (R_bitvector_32 mcountinhibit : register)) then DfracDiscarded
  else if decide (r = (R_bitvector_64 minstretcfg : register)) then DfracDiscarded
  else if decide (r = (R_bitvector_64 nextPC : register)) then DfracOwn (1/2)
  else DfracOwn 1.

Lemma i_Df_mc : i_Df (R_bitvector_32 mcountinhibit) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma i_Df_micfg : i_Df (R_bitvector_64 minstretcfg) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma i_Df_nPC : i_Df (R_bitvector_64 nextPC) = DfracOwn (1/2).
Proof. reflexivity. Qed.

Section IFrames.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma i_rw_split (rs : regstate) :
    (hreg_frame rs i_Drw : iProp Σ) ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 minstret) ↦ᵣ register_lookup (R_bitvector_64 minstret) rs ∗
     (R_bool minstret_increment) ↦ᵣ
       register_lookup (R_bool minstret_increment) rs ∗
     (R_bitvector_64 mcycle) ↦ᵣ register_lookup (R_bitvector_64 mcycle) rs ∗
     (R_bitvector_64 mtime) ↦ᵣ register_lookup (R_bitvector_64 mtime) rs ∗
     (R_bitvector_64 mip) ↦ᵣ register_lookup (R_bitvector_64 mip) rs)%I.
  Proof.
    rewrite /hreg_frame /i_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma i_ro_split (rs : regstate) :
    (hreg_frame_ro i_Df rs i_Dro : iProp Σ) ⊣⊢
    (reg_pointsto (R_bitvector_64 nextPC) (DfracOwn (1/2))
       (register_lookup (R_bitvector_64 nextPC) rs) ∗
     reg_pointsto hart_state (DfracOwn 1) (register_lookup hart_state rs) ∗
     reg_pointsto cur_privilege (DfracOwn 1)
       (register_lookup cur_privilege rs) ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded
       (register_lookup (R_bitvector_32 mcountinhibit) rs) ∗
     reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded
       (register_lookup (R_bitvector_64 minstretcfg) rs))%I.
  Proof.
    rewrite /hreg_frame_ro /i_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite !i_Df_nPC !i_Df_mc !i_Df_micfg.
    unfold i_Df.
    repeat (rewrite decide_False; [|discriminate]).
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma i_agree_rw (rs rs' : regstate) :
    reg_agree_on (i_Drw ∪ i_Dro) rs rs' -> reg_agree_on i_Drw rs rs'.
  Proof. intros Hag r Hr. apply Hag. set_solver. Qed.

  Lemma i_agree_ro (rs rs' : regstate) :
    reg_agree_on (i_Drw ∪ i_Dro) rs rs' -> reg_agree_on i_Dro rs rs'.
  Proof. intros Hag r Hr. apply Hag. set_solver. Qed.

  Lemma i_rw_ext (rs rs' : regstate) :
    reg_agree_on (i_Drw ∪ i_Dro) rs rs' ->
    hreg_frame rs i_Drw -∗ (hreg_frame rs' i_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ i_Drw (i_agree_rw _ _ Hag)).
    iIntros "H". iExact "H".
  Qed.

  Lemma i_ro_ext (rs rs' : regstate) :
    reg_agree_on (i_Drw ∪ i_Dro) rs rs' ->
    hreg_frame_ro i_Df rs i_Dro -∗ (hreg_frame_ro i_Df rs' i_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext _ _ _ i_Dro (i_agree_ro _ _ Hag)).
    iIntros "H". iExact "H".
  Qed.

  (* the half-cell calculus [nextPC] rides on *)
  Lemma reg_half (r : register) (v : type_of_register r) :
    (reg_pointsto r (DfracOwn 1) v : iProp Σ) ⊣⊢
    (reg_pointsto r (DfracOwn (1/2)) v ∗ reg_pointsto r (DfracOwn (1/2)) v).
  Proof.
    rewrite -(fractional (Φ := fun q => reg_pointsto r (DfracOwn q) v)
                (1/2)%Qp (1/2)%Qp).
    by rewrite Qp.half_half.
  Qed.

  Lemma reg_half_join (r : register) (v : type_of_register r) :
    reg_pointsto r (DfracOwn (1/2)) v -∗ reg_pointsto r (DfracOwn (1/2)) v -∗
    (reg_pointsto r (DfracOwn 1) v : iProp Σ).
  Proof. rewrite reg_half. iIntros "H1 H2". iFrame. Qed.

  Lemma reg_half_split (r : register) (v : type_of_register r) :
    reg_pointsto r (DfracOwn 1) v -∗
    (reg_pointsto r (DfracOwn (1/2)) v ∗
     reg_pointsto r (DfracOwn (1/2)) v : iProp Σ).
  Proof. rewrite reg_half. iIntros "H". iExact "H". Qed.


  (* ------------------------------------------------------------------ *)
  (* THE ENLARGEMENT.  [x_cells] is exactly what [HartSFrame]'s footprint  *)
  (* has and the cycle's does not: the config cells [sconf] owns, the      *)
  (* translation cells [tlb_res_pt] owns, the [hw_config] pins -- and the  *)
  (* SECOND HALF of nextPC.  Joining it to the cycle frame gives the       *)
  (* S-mode frame every dispatch / fetch / trap rule is stated at.         *)
  (* ------------------------------------------------------------------ *)
  Definition x_cells (rs : regstate) : iProp Σ :=
    (reg_pointsto (R_bitvector_64 nextPC) (DfracOwn (1/2))
       (register_lookup (R_bitvector_64 nextPC) rs) ∗
     reg_pointsto mstatus (DfracOwn 1) (register_lookup mstatus rs) ∗
     reg_pointsto mie (DfracOwn 1) (register_lookup mie rs) ∗
     reg_pointsto mideleg (DfracOwn 1) (register_lookup mideleg rs) ∗
     reg_pointsto menvcfg (DfracOwn 1) (register_lookup menvcfg rs) ∗
     reg_pointsto satp (DfracOwn 1) (register_lookup satp rs) ∗
     reg_pointsto tlb (DfracOwn 1) (register_lookup tlb rs) ∗
     reg_pointsto pmpcfg_n (DfracOwn 1) (register_lookup pmpcfg_n rs) ∗
     reg_pointsto pmpaddr_n (DfracOwn 1) (register_lookup pmpaddr_n rs) ∗
     reg_pointsto misa DfracDiscarded (register_lookup misa rs) ∗
     reg_pointsto mseccfg DfracDiscarded (register_lookup mseccfg rs) ∗
     reg_pointsto pma_regions DfracDiscarded (register_lookup pma_regions rs) ∗
     reg_pointsto htif_tohost_base DfracDiscarded
       (register_lookup htif_tohost_base rs) ∗
     reg_pointsto elp DfracDiscarded (register_lookup elp rs) ∗
     reg_pointsto senvcfg DfracDiscarded (register_lookup senvcfg rs))%I.

  Lemma i_to_s (rs : regstate) :
    hreg_frame rs i_Drw -∗ hreg_frame_ro i_Df rs i_Dro -∗ x_cells rs -∗
    (hreg_frame rs s_Drw ∗ hreg_frame_ro (s_Df (DfracOwn 1)) rs s_Dro : iProp Σ).
  Proof.
    rewrite i_rw_split i_ro_split s_rw_split s_ro_split /x_cells.
    iIntros "(HPC & Hms & Hmi & Hcy & Hti & Hip)".
    iIntros "(HnP1 & Hhs & Hpriv & Hmc & Hmicfg)".
    iIntros "(HnP2 & Hmst & Hmie & Hmdl & Hmenv & Hsatp & Htlb & Hpcfg &
              Hpaddr & Hmisa & Hsec & Hpma & Hhtif & Help & Hsenv)".
    iDestruct (reg_half_join (R_bitvector_64 nextPC) _ with "HnP1 HnP2")
      as "HnP".
    iFrame.
  Qed.

  Lemma s_to_i (rs : regstate) :
    hreg_frame rs s_Drw -∗ hreg_frame_ro (s_Df (DfracOwn 1)) rs s_Dro -∗
    (hreg_frame rs i_Drw ∗ hreg_frame_ro i_Df rs i_Dro ∗ x_cells rs : iProp Σ).
  Proof.
    rewrite i_rw_split i_ro_split s_rw_split s_ro_split /x_cells.
    iIntros "(HPC & HnP & Hms & Hmi & Hcy & Hti & Hip & Htlb)".
    iIntros "(Hpriv & Hmst & Hhs & Hpcfg & Hpaddr & Hmc & Hmicfg & Hmisa &
              Hsec & Hpma & Hhtif & Help & Hsenv & Hsatp & Hmie & Hmdl & Hmenv)".
    iDestruct (reg_half_split (R_bitvector_64 nextPC) _ with "HnP")
      as "[HnP1 HnP2]".
    iFrame.
  Qed.

End IFrames.

(* ===================================================================== *)
(* §2 THE TRAP, AS A WALK.                                                *)
(*                                                                       *)
(* [WpIntrCore.exec_handle_interrupt_S] is the same fact on the exec      *)
(* side; this is its per-node twin, at a frame that must additionally     *)
(* hold the four trap CSRs ([sie_cap]'s enabled arm owns sepc / scause /  *)
(* stval, and [intr_res] owns stvec).  [goodb] cannot carry it -- the     *)
(* stretch WRITES -- so it is a hand walk, and it SPLITS at the zicfilp   *)
(* elp reset, the one write to a cell no frame may own                    *)
(* ([HartRegNode.swp_write_reg_same]; the other client is MRET's).        *)
(* ===================================================================== *)
Definition trap_rs (rs : regstate) (ii : InterruptType)
    (pc0 sc_old stvec_v ms_v : mword 64) (elp_v : mword 1) : regstate :=
  register_set (R_bitvector_64 nextPC) (stvec_base stvec_v)
 (register_set cur_privilege Supervisor
 (register_set sepc pc0
 (register_set stval (zeros' 64)
 (register_set scause (trap_scause sc_old ii)
 (register_set mstatus (trap_ms elp_v ms_v) rs))))).

(* every S-mode tower lookup, in one tactic *)
Ltac srs :=
  rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
    ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
    ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
    ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
    ?s_rs_menv.

Section IntrEngine.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_handle_interrupt_S (ii : InterruptType)
      (pc0 ms_v sc_old sv_old se_old np_old stvec_v misa0 : mword 64)
      (elp_v : mword 1) {dqp dqm dqv : dfrac} :
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct ->
    gen_cert -∗
    reg_pointsto (R_bitvector_64 PC) dqp pc0 -∗
    reg_pointsto misa dqm misa0 -∗
    reg_pointsto stvec dqv stvec_v -∗
    reg_pointsto elp DfracDiscarded elp_v -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_old -∗
    stval ↦ᵣ sv_old -∗
    sepc ↦ᵣ se_old -∗
    cur_privilege ↦ᵣ Supervisor -∗
    (R_bitvector_64 nextPC) ↦ᵣ np_old -∗
    swp (handle_interrupt ii Supervisor)
      (fun _ =>
         reg_pointsto (R_bitvector_64 PC) dqp pc0 ∗
         reg_pointsto misa dqm misa0 ∗
         reg_pointsto stvec dqv stvec_v ∗
         mstatus ↦ᵣ trap_ms elp_v ms_v ∗
         scause ↦ᵣ trap_scause sc_old ii ∗
         stval ↦ᵣ (zeros' 64) ∗
         sepc ↦ᵣ pc0 ∗
         cur_privilege ↦ᵣ Supervisor ∗
         (R_bitvector_64 nextPC) ↦ᵣ stvec_base stvec_v).
  Proof.
  Admitted.

  (* ==================================================================== *)
  (* §3 THE S-MODE CYCLE BODY: [run_hart_active] FROM THE [instr] BUNDLE.  *)
  (*                                                                      *)
  (* [WpInstrRun.swp_run_hart_active_instr_ex]'s S-mode twin: the fetch    *)
  (* shape is read off [instr] and the fetch obligation is discharged by   *)
  (* [HartSTrans.swp_fetch_S] / [_S_rvc2] / [_S_base2] over the walking    *)
  (* translation ([SRegime.kpt_swp_translate]) and the text window         *)
  (* ([InstrBytes.text_fetch_obl] at the TRANSLATED pa).  The dispatch is  *)
  (* [WpIntrCore.swp_dispatchInterrupt_S], so the conclusion is the        *)
  (* disjunction the machine picks between.                               *)
  (*                                                                      *)
  (* THE LANDING FILE IS EXISTENTIAL: a walking fetch may FILL the TLB, so *)
  (* the file the execute runs at is [rs] or [rs] with [tlb] rewritten,    *)
  (* and the [tlb_snap_ok] the caller gets back is at the landing file's   *)
  (* tlb -- which is exactly what the fill's own rule re-establishes.      *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_instr_S (rs : regstate) (root_ppn : mword 44)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mip_v mdv_v ms_v : mword 64) (W Rr : iProp Σ)
      (Qi : InterruptType -> Privilege -> iProp Σ) :
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup misa rs = MISA_C ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup menvcfg rs = MENVCFG_S ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup mstatus rs = ms_v ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = MIE_S ->
    register_lookup mideleg rs = mdv_v ->
    and_vec MIE_S (not_vec mdv_v) = zeros' 64 ->
    register_lookup elp rs = landing_pad_bits_backwards NO_LP_EXPECTED ->
    pma_allows_all (register_lookup pma_regions rs) ->
    _get_Satp64_Mode (Mk_Satp64 (register_lookup satp rs))
      = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid
      (autocast (T := mword) (register_lookup satp rs) : mword 64))
      = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn
      (autocast (T := mword) (register_lookup satp rs) : mword 64)) = root_ppn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n rs) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n rs) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n rs) 0))
      ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n rs) 0))
      ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n rs) 0))
      ('b"1") = true ->
    (ram_base + ram_size
       <= uint (vec_access_dec (register_lookup pmpaddr_n rs) 0) * 4)%Z ->
    gen_cert -∗
    kmap_static_claims -∗
    instr pc is_rvc i -∗
    kpt_inv root_ppn -∗
    tlb_snap_ok (register_lookup tlb rs) -∗
    resv_frag cpu_id None -∗
    W -∗
    hreg_frame rs s_Drw -∗
    hreg_frame_ro (s_Df (DfracOwn 1)) rs s_Dro -∗
    (* the trap payload: the dispatch answered [Some], nothing has run *)
    (∀ ii pr,
       ⌜∃ meip seip : mword 1,
          s_dispatch mip_v meip seip MIE_S mdv_v ms_v = Some (ii, pr)⌝ -∗
       W -∗
       hreg_frame rs s_Drw -∗ hreg_frame_ro (s_Df (DfracOwn 1)) rs s_Dro -∗
       tlb_snap_ok (register_lookup tlb rs) -∗ resv_frag cpu_id None -∗
       Qi ii pr) -∗
    (* the instruction: at the fetch's landing file, nextPC committed *)
    (∀ rsf : regstate,
       ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ -∗
       W -∗
       hreg_frame (register_set (R_bitvector_64 nextPC)
                     (add_vec_int pc (if is_rvc then 2 else 4)) rsf) s_Drw -∗
       hreg_frame_ro (s_Df (DfracOwn 1))
         (register_set (R_bitvector_64 nextPC)
            (add_vec_int pc (if is_rvc then 2 else 4)) rsf) s_Dro -∗
       tlb_snap_ok (register_lookup tlb rsf) -∗
       resv_any cpu_id -∗
       swp (execute i) (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ Rr)) -∗
    swp (run_hart_active 0)
      (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                 ∨ (∃ w : mword 32,
                      ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗ Rr)).
  Proof.
  Admitted.


  (* ------------------------------------------------------------------ *)
  (* THE 25 CELLS, both ways.  [WpSFrames.s_frames_intro] / [_elim] do    *)
  (* this WITH the bundles; the engine needs the bare cell form as well,  *)
  (* because it re-forms the bundles in the middle of a cycle (to hand    *)
  (* them to the leaf) and takes them apart again afterwards.             *)
  (* ------------------------------------------------------------------ *)

  Section SCells.
    Context (pc npc ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
            (pcfg : type_of_register pmpcfg_n)
            (paddr : type_of_register pmpaddr_n)
            (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
            (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
            (satp0 mie0 mdv0 menv0 : mword 64)
            (tlbv : type_of_register tlb).

    Local Notation SRS :=
      (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv).

    Definition s_cells : iProp Σ :=
      ((R_bitvector_64 PC) ↦ᵣ pc ∗ (R_bitvector_64 nextPC) ↦ᵣ npc ∗
       (R_bitvector_64 minstret) ↦ᵣ ms ∗ (R_bool minstret_increment) ↦ᵣ bmi ∗
       (R_bitvector_64 mcycle) ↦ᵣ cy ∗ (R_bitvector_64 mtime) ↦ᵣ ti ∗
       (R_bitvector_64 mip) ↦ᵣ ip ∗ tlb ↦ᵣ tlbv ∗
       cur_privilege ↦ᵣ Supervisor ∗ mstatus ↦ᵣ mst0 ∗
       hart_state ↦ᵣ HART_ACTIVE tt ∗ pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
       reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded mc ∗
       reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded micfg ∗
       reg_pointsto misa DfracDiscarded misa0 ∗
       reg_pointsto mseccfg DfracDiscarded mseccfg0 ∗
       reg_pointsto pma_regions DfracDiscarded pmar0 ∗
       reg_pointsto htif_tohost_base DfracDiscarded None ∗
       reg_pointsto elp DfracDiscarded elp0 ∗
       reg_pointsto senvcfg DfracDiscarded senv0 ∗
       satp ↦ᵣ satp0 ∗ mie ↦ᵣ mie0 ∗ mideleg ↦ᵣ mdv0 ∗ menvcfg ↦ᵣ menv0)%I.

    Lemma s_frames_cells :
      (hreg_frame SRS s_Drw ∗ hreg_frame_ro (s_Df (DfracOwn 1)) SRS s_Dro
       : iProp Σ) ⊣⊢ s_cells.
    Proof.
      rewrite s_rw_split s_ro_split /s_cells. srs.
      iSplit.
      - iIntros "(H1 & H2)".
        iDestruct "H1" as "(?&?&?&?&?&?&?&?)".
        iDestruct "H2" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?)".
        iFrame.
      - iIntros "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?)".
        iFrame.
    Qed.
  End SCells.

  (* ------------------------------------------------------------------ *)
  (* [sconf] and [tlb_res_pt] as CELLS + FACTS.  Both directions, because  *)
  (* the engine opens them for the fetch and closes them for the leaf.     *)
  (* Unlike [WpSFrames.s_frames_intro] these EXPORT the PMP and satp facts *)
  (* rather than swallowing them: the walking fetch's own rule asks for    *)
  (* every one of them.                                                   *)
  (* ------------------------------------------------------------------ *)
  Lemma sconf_to_cells :
    sconf -∗ ∃ mst0 mdv0 : mword 64,
      ⌜ sconf_ms_facts mst0 ⌝ ∗
      ⌜ and_vec MIE_S (not_vec mdv0) = zeros' 64 ⌝ ∗
      hw_config ∗ minstret_inv ∗
      cur_privilege ↦ᵣ Supervisor ∗ mstatus ↦ᵣ mst0 ∗
      ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) ∗ sret_tie mst0 ∗
      mie ↦ᵣ MIE_S ∗ mideleg ↦ᵣ mdv0 ∗ menvcfg ↦ᵣ MENVCFG_S.
  Proof.
    iIntros "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (mst0) "(Hms & Hhalf & Htie & %Hmsf)".
    iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvx" as (menv0) "(Hmenv & _ & _ & _ & _ & %Hmenvval)".
    subst menv0. iExists mst0, mdv0.
    iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
    iPureIntro. split; assumption.
  Qed.

  Lemma sconf_of_cells (mst0 mdv0 : mword 64) :
    sconf_ms_facts mst0 ->
    and_vec MIE_S (not_vec mdv0) = zeros' 64 ->
    hw_config -∗ minstret_inv -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mst0 -∗
    ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) -∗ sret_tie mst0 -∗
    mie ↦ᵣ MIE_S -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ MENVCFG_S -∗ sconf.
  Proof.
    intros Hmsf Hmm.
    iIntros "#Hhw #Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
    rewrite /sconf. iFrame "Hhw Hminv Hpriv".
    iSplitL "Hms Hhalf Htie".
    { iExists mst0. iFrame "Hms Hhalf Htie". iPureIntro. exact Hmsf. }
    iSplitL "Hmie Hmdl".
    { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
    iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
    split_and!; try reflexivity; vm_compute; reflexivity.
  Qed.

  Definition pmp_facts (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) : Prop :=
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR /\
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false /\
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true /\
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true /\
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true /\
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z.

  Definition satp_facts (satp0 : mword 64) (root_ppn : mword 44) : Prop :=
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) /\
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) /\
    autocast (T := mword)
      (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn.

  Lemma tlb_res_to_cells (root_ppn : mword 44) :
    tlb_res_pt root_ppn -∗
    ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜ satp_facts satp0 root_ppn ⌝ ∗ ⌜ pmp_facts pcfg paddr ⌝ ∗
      satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      tlb_snap_ok tlbv ∗ kpt_inv root_ppn.
  Proof.
    iIntros "H". iDestruct "H" as (satp0 tlbv)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & Hsnap & Hpmp & #Hkinv)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iExists satp0, tlbv, pcfg, paddr.
    iFrame "Hsatp Htlb Hpcfg Hpaddr Hsnap Hkinv".
    iPureIntro. split.
    - rewrite /satp_facts. split_and!; assumption.
    - rewrite /pmp_facts. split_and!; assumption.
  Qed.

  Lemma tlb_res_of_cells (root_ppn : mword 44) (satp0 : mword 64)
      (tlbv : type_of_register tlb) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    satp_facts satp0 root_ppn -> pmp_facts pcfg paddr ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
    pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    tlb_snap_ok tlbv -∗ kpt_inv root_ppn -∗ tlb_res_pt root_ppn.
  Proof.
    intros (Hmode & Hasid & Hppn) (HA & Hord & HX & HW & HR & Hcov).
    iIntros "Hsatp Htlb Hpcfg Hpaddr Hsnap #Hkinv".
    iExists satp0, tlbv. iFrame "Hsatp Htlb Hsnap Hkinv".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iApply (pmp_config_intro root_ppn pcfg paddr HA Hord HX HW HR Hcov
              with "Hpcfg Hpaddr").
  Qed.

End IntrEngine.

(* ===================================================================== *)
(* §4 THE ENGINE: one S-mode instruction at [pc0] with interrupts ON.     *)
(*                                                                       *)
(* OUTSIDE THE SECTION, and it has to be: the Löb is taken over a         *)
(* statement that QUANTIFIES the hart ([iLöb as "IH" forall (CID0)]), so  *)
(* the binder must be dischargeable -- a section variable is not.  That   *)
(* also means every hart-indexed term written fresh in the proof below    *)
(* means [CID0], the hart the loop is currently on, which is what the     *)
(* re-entry at [c'] has to be careful about.                             *)
(*                                                                       *)
(* IT TAKES THE FOLDED BUNDLE AND ITS CALLBACK IS HART-GENERIC, and those *)
(* two facts are the same fact.  A trap can park the interrupted thread   *)
(* (kerneltrap yields on a timer tick when this cpu has a current proc),  *)
(* so the instruction after the absorbing loop executes on the hart the   *)
(* LAST trap returned to -- hence the callback sits inside               *)
(* [WpNext.wp_next true p].                                              *)
(*                                                                       *)
(* THE CALLBACK'S [▷] IS OUTERMOST, and that placement is forced.  The    *)
(* engine's own machine step offers exactly ONE later, at                 *)
(* [HartMCycle.wp_loop_cycle]'s body; the Löb hypothesis and the caller's *)
(* continuation both have to be stripped by it, and only what is in the   *)
(* CONTEXT when that [iNext] runs can be.  A [▷] sitting inside the       *)
(* callback (on the leaf's own [WP Loop], where the whole-cycle engine    *)
(* used to put it) would arrive through the cycle rule's [Psi] slot,      *)
(* AFTER the [iNext], and could never be discharged.  Outermost is also   *)
(* the WEAKEST premise -- [P ⊢ ▷ P] -- so no caller pays for the move.    *)
(* ===================================================================== *)
Definition intr_Q (flag : bool) (rs2 : regstate) : Prop :=
  register_lookup hart_state rs2 = HART_ACTIVE tt /\
  register_lookup (R_bool minstret_increment) rs2 = flag /\
  register_lookup cur_privilege rs2 = Supervisor.

Lemma wp_exec_step_intr `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId} `{CID0 : CpuId}
    {kt : ktier} (pc0 : mword 64) (m : regfile) (av : nat) (p : mword 64)
    (is_rvc : bool) (i : instruction)
    (R : mword 64 -> regfile -> nat -> iProp Σ) :
  ret_pc pc0 = pc0 ->
  sie_cap_gpr kt m av true p -∗
  pc_is pc0 -∗
  instr pc0 is_rvc i -∗
  ▷ wp_next true p (fun CID =>
      (sconf -∗
       sie_cap kt m av true p -∗
       gpr_file (tp_pin m) -∗
       (R_bitvector_64 PC) ↦ᵣ pc0 -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc0 (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            ∃ (npc : mword 64) (m' : regfile) (av' : nat),
              (R_bitvector_64 PC) ↦ᵣ pc0 ∗
              (R_bitvector_64 nextPC) ↦ᵣ npc ∗
              resv_any cpu_id ∗
              sconf ∗ sie_cap kt m' av' true p ∗ gpr_file (tp_pin m') ∗
              R npc m' av'))
      ∗ (∀ (npc : mword 64) (m' : regfile) (av' : nat),
           sie_cap_gpr kt m' av' true p -∗ pc_is npc -∗ R npc m' av' -∗
           WP (Loop : expr riscv_lang))) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros Hpc0.
  iIntros "Hcg Hpc #Hinstr Hbody".
  iRevert "Hcg Hpc Hbody".
  iLöb as "IH" forall (CID0).
  iIntros "Hcg Hpc Hbody".
  (* ---- open the bundle: cells out, non-cell residue kept aside ---- *)
  iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
  iDestruct (sie_cap_on_kpt with "Hcap") as (root_ppn)
    "(Hstk & Hbit1 & Htlbres & Harm & #Hwit)".
  rewrite {1}/sie_arm.
  iDestruct "Harm" as
    "(Hq1 & Hires & #Hkpt & Hsepcx & Hscausex & Hstvalx & Hsppc & Hclm & Hcpu)".
  (* the installed handler comes out ONCE, at the top: [#Hsp] is persistent
     and therefore survives every later split, which is what lets the trap
     arm apply the contract in the cycle's continuation. *)
  iEval (rewrite /intr_res) in "Hires".
  iDestruct "Hires" as (handler vb) "(%Htvd & %Hsb & Hq4 & Hstv & #Hsp)".
  iDestruct "Hsepcx" as (se_old) "Hsepc".
  iDestruct "Hscausex" as (sc_old) "Hscause".
  iDestruct "Hstvalx" as (sv_old) "Hstval".
  iDestruct "Hsppc" as (vca vcb) "Hsppc".
  iDestruct (sconf_to_cells with "Hsc") as (mst0 mdv0)
    "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie & Hmdl &
      Hmenv)".
  iDestruct (ghost_var_agree with "Hhalf Hq1") as %HSIE1.
  iDestruct (tlb_res_to_cells with "Htlbres") as (satp0 tlbv pcfg paddr)
    "(%Hsatpf & %Hpmpf & Hsatp & Htlb & Hpcfg & Hpaddr & Hsnap & #Hkinv)".
  iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr & Hresv)".
  iDestruct "Hmr" as (msr bmi mc micfg) "(Hmsr & Hmi & #Hmc & #Hmicfg)".
  iDestruct "Hcr" as (cy ti ip) "(Hcy & Hti & Hip)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmS & %HmC &
      %HmU & %HmM & %Hpmaall & %Hsec1 & %Hsec2 & %Helpnp & %HmA &
      %Hmisaval & %Hsecval & #Hkmapb)".
  iDestruct (hw_config_cert with "Hhw") as "#Hcert".
  pose proof (elp_no_lp elp0 Helpnp) as Help0.
  (* ---- the cycle's own frame: the six writable cells, the five read-only
         ones, and the SECOND HALF of nextPC kept back (see the header) ---- *)
  iDestruct (reg_half_split (R_bitvector_64 nextPC) pc0 with "HnPC")
    as "[HnP1 HnP2]".
  iAssert (hreg_frame (s_rs pc0 pc0 msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
            (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbv) i_Drw)
    with "[HPC Hmsr Hmi Hcy Hti Hip]" as "Hirw".
  { rewrite i_rw_split. srs. iFrame. }
  iAssert (hreg_frame_ro i_Df (s_rs pc0 pc0 msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
            (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbv) i_Dro)
    with "[HnP1 Hhs Hpriv]" as "Hiro".
  { rewrite i_ro_split. srs. iFrame "HnP1 Hhs Hpriv Hmc Hmicfg". }
  iApply (wp_loop_cycle i_Drw i_Dro i_Df
            (fun rsx => exists (rs2 : regstate) (mi : mword 64),
               intr_Q (minstret_inc_flag mc micfg Supervisor) rs2 /\
               rsx = wrap_post rs2 mi)
            ((* --- RETIRE: the leaf kept the bundles; the wrapper kept the pc half --- *)
             (∃ (npc : mword 64) (m' : regfile) (av' : nat),
                reg_pointsto (R_bitvector_64 nextPC) (DfracOwn (1/2)) npc ∗
                sconf_priv_closer ∗ (∃ ms : mword 64, sconf_msown ms) ∗
                sie_cap kt m' av' true p ∗ gpr_file (tp_pin m') ∗
                resv_any cpu_id ∗ R npc m' av' ∗
                (∀ (npc0 : mword 64) (m0 : regfile) (av0 : nat),
                   sie_cap_gpr kt m0 av0 true p -∗ pc_is npc0 -∗
                   R npc0 m0 av0 -∗ WP (Loop : expr riscv_lang)))
             ∨
             (* --- TRAP: the entry package, minus what the frame holds --- *)
             (∃ (hv sc mstT mdvT : mword 64),
                ⌜ s_cause_ok sc ⌝ ∗ ⌜ sconf_ms_facts mstT ⌝ ∗
                ⌜ and_vec MIE_S (not_vec mdvT) = zeros' 64 ⌝ ∗
                reg_pointsto (R_bitvector_64 nextPC) (DfracOwn (1/2)) hv ∗
                mstatus ↦ᵣ mstT ∗
                ghost_var sie_gname (1/2) (_get_Mstatus_SIE mstT) ∗
                sret_tie mstT ∗
                mie ↦ᵣ MIE_S ∗ mideleg ↦ᵣ mdvT ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                sret_bits ('b"1" : mword 1) ('b"1" : mword 1) ∗
                sepc ↦ᵣ pc0 ∗ scause ↦ᵣ sc ∗ stval ↦ᵣ (zeros' 64) ∗
                sie_cap kt m (trap_res true + av) false p ∗
                kpt_on cpu_id ∗ cpu_hart 0 false p ∅ ∗ cpu_claim p ∗
                intr_res kt ∗ intr_handler_spec kt hv ∗
                gpr_file (tp_pin m) ∗ resv_any cpu_id ∗
                wp_next true p (fun CID =>
                  (sconf -∗ sie_cap kt m av true p -∗ gpr_file (tp_pin m) -∗
                   (R_bitvector_64 PC) ↦ᵣ pc0 -∗
                   (R_bitvector_64 nextPC) ↦ᵣ
                     (add_vec_int pc0 (if is_rvc then 2 else 4)) -∗
                   resv_any cpu_id -∗
                   swp (execute i)
                     (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                        ∃ (npc : mword 64) (m' : regfile) (av' : nat),
                          (R_bitvector_64 PC) ↦ᵣ pc0 ∗
                          (R_bitvector_64 nextPC) ↦ᵣ npc ∗
                          resv_any cpu_id ∗
                          sconf ∗ sie_cap kt m' av' true p ∗
                          gpr_file (tp_pin m') ∗ R npc m' av'))
                  ∗ (∀ (npc : mword 64) (m' : regfile) (av' : nat),
                       sie_cap_gpr kt m' av' true p -∗ pc_is npc -∗
                       R npc m' av' -∗ WP (Loop : expr riscv_lang)))))%I
            i_disj i_w_cy i_w_ti i_w_ip
            with "Hcert Hresv [-] []").
  { admit. }
  { admit. }
Admitted.
