(* WpIntrInv.v -- the GENERAL S-mode interrupt invariant and the
   interrupt-absorbing step engine (the tick-aware redesign of the old
   pinned-cell interrupt capstone).

   THE DESIGN.  The SIE ghost variable [γ] (the same [γ] that is the argument
   of [smode_config]) is split into THREE pieces:

     - 1/2 rides with the mstatus cell, tied to the LIVE [mstatus.SIE] bit
       (this is the half [smode_config] bundles; in the interrupts-ENABLED
       regime the client holds it inside [intr_config], the SIE=1 mirror of
       [smode_config]);
     - 1/4 is the KERNEL-CODE token: client code keeps it to reason about
       whether interrupts are currently enabled or disabled (push_off /
       pop_off bookkeeping);
     - 1/4 lives in the interrupt INVARIANT [intr_inv] below, together with
       the [stvec] register and -- keyed on the ghost value being 1 -- a
       persistent WP for running the interrupt handler ([intr_handler_spec]).

   Changing SIE therefore requires ALL THREE pieces (1/2 + 1/4 + 1/4 = 1,
   [sie_ghost_flip]); the flipping instruction opens [intr_inv] across its
   own step to borrow the invariant quarter.

   THE ENGINE.  [wp_exec_step_intr] slots into the clock_inv / minstret_inv
   reduction machinery: it is a Löb loop over the joint step rule
   [wp_exec_step_retire_or_intr] (built on [wp_exec_step_minstret], so the
   clock tick is already absorbed one layer down).  At each step it reads the
   dispatch inputs mip / sig_meip / sig_seip DIRECTLY OFF the machine state σ
   (they live in [clock_inv] / [wire_inv] and can never be pinned by cells --
   a tick may rewrite MTIP/STIP at every step, the PLIC wire step may flip
   sig_seip at any time), and cases on the outcome:

     - PENDING: it takes the interrupt -- borrows [stvec] and the handler WP
       from [intr_inv] for the trap step, drives the trap tower
       ([exec_handle_interrupt_S]), runs the handler via the invariant's
       [intr_handler_spec] (which returns idempotently to the interrupted
       pc with SIE re-enabled and the frame [intr_frame] intact), and re-enters
       itself by Löb induction -- so an ARBITRARY number of back-to-back
       interrupts is absorbed;
     - NONE: it hands the caller's σ-callback the PURE fact
       [exec (dispatchInterrupt Supervisor) σ = Some (None, σ)] -- no
       interrupt needs to be taken -- so the higher-level per-instruction
       logic runs the instruction WITHOUT owning mip or the wire pins, and
       without fupd-style specs passing an interrupt-pending cell around.

   The per-trap frame is the CONCRETE [intr_frame]: [stack_own] of depth AT
   LEAST [kv_frame_slots] below the interrupted sp -- the kernel must
   maintain that much free stack at every interrupts-enabled instruction --
   plus menvcfg and tlb_inv_pt.  [kernelvec_handler_spec] proves the real
   kernelvec ([wp_kernelvec], WpKernelvecNew.v) satisfies the contract. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr WpMmodeLeafBase StackOwn.
Require Import SmodeCore WpSmodeSret KernelText.
Require Import WpKernelvecNew.
Require Import WpIntrBits WpIntrCore.
(* legalize_sie_clear_idem + have_nom_val: kept QUALIFIED (no Import) so the
   WpGprCsrwCommon/C namespaces don't shadow anything here. *)
Require WpGprCsrwCommon WpGprCsrwC.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import PtAdBits PtTree PtTreeAdue KptTree SmodeCorePt.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMem WpSmodePtMemWrap WpSmodePtLock WpSmodePtUart.
Import Defs.

(* ===================================================================== *)
(* §1 Pure layer: the mstatus fact set carried across the trap+SRET       *)
(* round trip, and dispatch-outcome helpers.                              *)
(* ===================================================================== *)

(* the mstatus fact set of the interrupts-ENABLED regime: SIE=1 plus the
   ambient MPRV/SXL/MXR/TSR facts, plus the ext-state / dirty / MPP
   well-formedness needed to discharge [legalize_sie_clear_idem] on the
   trapped mstatus.  Preserved by the trap+SRET round trip
   ([intr_ms_facts_roundtrip]; the SIE=1 restoration is the headline
   [roundtrip_SIE_true]). *)
Definition intr_ms_facts (ms : mword 64) : Prop :=
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = true /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false /\
  _get_Mstatus_XS ms = extStatus_map_forwards Off /\
  _get_Mstatus_FS ms = extStatus_map_forwards Off /\
  _get_Mstatus_VS ms = extStatus_map_forwards Off /\
  _get_Mstatus_SD ms = 'b"0" /\
  WpGprCsrwCommon.have_nom_val (_get_Mstatus_MPP ms) = true.

Lemma intr_ms_facts_roundtrip (elp_v : mword 1) (ms : mword 64) :
  intr_ms_facts ms -> intr_ms_facts (sret_ms5 (trap_ms elp_v ms)).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [exact (roundtrip_SIE_true elp_v ms H1) |].
  split; [exact (roundtrip_MPRV_false elp_v ms) |].
  split; [exact (roundtrip_SXL_eq elp_v ms H3) |].
  split; [exact (roundtrip_MXR_true elp_v ms H4) |].
  split; [exact (roundtrip_TSR_false elp_v ms H5) |].
  split; [rewrite roundtrip_XS; exact H6 |].
  split; [rewrite roundtrip_FS; exact H7 |].
  split; [rewrite roundtrip_VS; exact H8 |].
  split; [rewrite roundtrip_SD; exact H9 |].
  rewrite roundtrip_MPP; exact H10.
Qed.

(* SIE off ⇒ no dispatch (any pending set). *)
Lemma s_dispatch_None_of_SIE_false (mip_v : mword 64) (meip seip : mword 1)
    (mie_v mdv0 ms : mword 64) :
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ->
  s_dispatch mip_v meip seip mie_v mdv0 ms = None.
Proof. intros H. unfold s_dispatch. rewrite H. reflexivity. Qed.

(* empty pending set ⇒ no dispatch (any SIE) -- the "supervisor interrupt
   pending register is zero" form a higher-level client may prefer. *)
Lemma s_dispatch_None_of_pending_zero (mip_v : mword 64) (meip seip : mword 1)
    (mie_v mdv0 ms : mword 64) :
  s_pending mip_v meip seip mie_v mdv0 = zeros' 64 ->
  s_dispatch mip_v meip seip mie_v mdv0 ms = None.
Proof.
  intros H. unfold s_dispatch. rewrite H.
  replace (neq_vec (zeros' 64 : mword 64) (zeros' 64)) with false
    by (vm_compute; reflexivity).
  rewrite andb_false_r. reflexivity.
Qed.

(* the kernelvec trap-vector facts (Direct mode, base = itself) -- feed
   [intr_inv_alloc] when the handler is kernelvec. *)
Lemma kernelvec_tv_direct :
  trapVectorMode_forwards
    (_get_Mtvec_Mode (mword_of_int KernelSyms.kernelvec : mword 64)) = TV_Direct.
Proof. vm_compute. reflexivity. Qed.

Lemma kernelvec_stvec_base :
  stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)
    = (mword_of_int KernelSyms.kernelvec : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* kernelvec's sparse positive-offset save slots, re-addressed as [pa_stk]
   slots below the INTERRUPTED sp: kv_sp1 = sp - 256, so the window at
   kv_sp1 + 8j is stack slot 32 - j. *)
Lemma kv_slot_addr (m : gmap regidx (mword 64)) (off : mword 64) (k : nat) :
  add_vec (sign_extend' 64 (caddi16sp_imm kv_imm1)) off
    = (mword_of_int (- (8 * Z.of_nat k)) : mword 64) ->
  add_vec (kv_sp1 m) off = pa_stk (m !!! Regidx csp_rs1) k.
Proof.
  intros H.
  assert (Hr : kv_sp1 m
               = add_vec (m !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm kv_imm1))) by reflexivity.
  rewrite Hr kv_addv_assoc H. unfold pa_stk, add_vec_int. reflexivity.
Qed.

Lemma kv_slot_addr0 (m : gmap regidx (mword 64)) :
  kv_sp1 m = pa_stk (m !!! Regidx csp_rs1) 32.
Proof.
  assert (Hr : kv_sp1 m
               = add_vec (m !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm kv_imm1))) by reflexivity.
  rewrite Hr. unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq. vm_compute. reflexivity.
Qed.

Section WpIntrInv.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (* §2 The SIE ghost choreography: 1/2 (live-bit tie) + 1/4 (kernel-code *)
  (* token) + 1/4 (invariant).                                            *)
  (* =================================================================== *)

  Lemma sie_ghost_alloc (v : mword 1) :
    ⊢ |==> ∃ γ : gname,
        ghost_var γ (1/2) v ∗ ghost_var γ (1/4) v ∗ ghost_var γ (1/4) v.
  Proof.
    iMod (ghost_var_alloc v) as (γ) "Hg".
    iEval (rewrite -Qp.half_half) in "Hg".
    iDestruct (ghost_var_split with "Hg") as "[H1 H2]".
    iEval (rewrite -Qp.quarter_quarter) in "H2".
    iDestruct (ghost_var_split with "H2") as "[H2 H3]".
    iModIntro. iExists γ. iFrame.
  Qed.

  (* flipping SIE needs all three pieces (used by a future push_off/pop_off
     integration: the csr-write leaf opens [intr_inv] across its step to
     borrow the invariant quarter). *)
  Lemma sie_ghost_flip (γ : gname) (v1 v2 v3 w : mword 1) :
    ghost_var γ (1/2) v1 -∗ ghost_var γ (1/4) v2 -∗ ghost_var γ (1/4) v3 ==∗
    ghost_var γ (1/2) w ∗ ghost_var γ (1/4) w ∗ ghost_var γ (1/4) w.
  Proof.
    iIntros "H1 H2 H3".
    iCombine "H2 H3" as "H23".
    iEval (rewrite Qp.quarter_quarter) in "H23".
    iMod (ghost_var_update_2 w with "H1 H23") as "[H1 H23]".
    { rewrite Qp.half_half //. }
    iEval (rewrite -Qp.quarter_quarter) in "H23".
    iDestruct (ghost_var_split with "H23") as "[H2 H3]".
    iModIntro. iFrame.
  Qed.

  (* =================================================================== *)
  (* §3 [intr_config] -- the interrupts-ENABLED ambient configuration:    *)
  (* the SIE=1 mirror of [smode_config] (whose SIE=0 fact makes it        *)
  (* unusable here).  All cells at FULL ownership -- the trap writes      *)
  (* mstatus / cur_privilege / sepc / scause / stval.  The three trap     *)
  (* CSRs are value-agnostic (every round trip scribbles them).           *)
  (* [hart_state] is NOT bundled: the step engine holds it across the     *)
  (* σ-callback (exactly as in [wp_exec_step_hart_active_inv]), so it     *)
  (* travels beside the bundle.                                           *)
  (* =================================================================== *)
  Definition intr_config (γ : gname) : iProp Σ :=
    (hw_config ∗ minstret_inv ∗
     cur_privilege ↦ᵣ Supervisor ∗
     (∃ ms : mword 64,
        mstatus ↦ᵣ ms ∗
        ghost_var γ (1/2) (_get_Mstatus_SIE ms) ∗
        ⌜ intr_ms_facts ms ⌝) ∗
     (∃ mie_v mdv0 : mword 64,
        mie ↦ᵣ mie_v ∗ mideleg ↦ᵣ mdv0 ∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝) ∗
     (∃ v : mword 64, sepc ↦ᵣ v) ∗
     (∃ v : mword 64, scause ↦ᵣ v) ∗
     (∃ v : mword 64, stval ↦ᵣ v))%I.

  (* =================================================================== *)
  (* §4 [intr_frame] + the handler contract.                               *)
  (*                                                                       *)
  (* [intr_frame] is THE per-trap frame the interrupt handler consumes     *)
  (* and re-establishes: THE KERNEL MUST MAINTAIN [stack_own] OF DEPTH AT  *)
  (* LEAST [kv_frame_slots] (32 slots = 256 bytes, kernelvec's c.addi16sp  *)
  (* frame) BELOW SP AT EVERY INTERRUPTS-ENABLED INSTRUCTION -- the trap   *)
  (* saves its 17 caller-saved registers into the top of that region --    *)
  (* plus the allocation-fixed menvcfg cell and tlb_inv_pt.  The depth is a   *)
  (* BOUND (existential), so a client simply packs in however much free    *)
  (* stack it currently owns below sp.  The frame exists because the       *)
  (* handler genuinely USES m-dependent resources beyond the register      *)
  (* file: they can neither sit in the fixed invariant (sp varies per      *)
  (* trap) nor be framed around the handler WP.                            *)
  (*                                                                       *)
  (* [intr_handler_spec] is the handler contract.  Persistent (□), so it   *)
  (* lives freely inside the invariant.  Reading: for any interrupted pc   *)
  (* [pc0] (instruction-aligned, so [sret_tgt pc0 = pc0]), any mstatus     *)
  (* [ms] with the SIE=1 fact set, and any register file [m]: if we are    *)
  (* AT [handler] in the trapped mstatus [trap_ms elp_v ms] with           *)
  (* sepc = pc0, [gpr_file m] and [intr_frame ... m], then the machine     *)
  (* returns to pc0 with mstatus [sret_ms5 (trap_ms elp_v ms)] (SIE        *)
  (* restored to 1 by [roundtrip_SIE]), the SAME register file, and the    *)
  (* frame intact -- exactly what re-entering the interrupted instruction  *)
  (* needs.  [stvec] is NOT threaded (it stays inside [intr_inv] across    *)
  (* the handler run; the handler never touches it).  [s_dispatch] reads   *)
  (* mie/mideleg, so the handler spec owns them explicitly.                *)
  (* =================================================================== *)
  Definition kv_frame_slots : nat := 32.

  Definition intr_frame (root_ppn : mword 44) (menvcfg0 : mword 64)
      (m : gmap regidx (mword 64)) : iProp Σ :=
    (menvcfg ↦ᵣ menvcfg0 ∗
     tlb_inv_pt root_ppn ∗
     (∃ n : nat, ⌜ (kv_frame_slots <= n)%nat ⌝ ∗
                 stack_own (m !!! Regidx csp_rs1) n))%I.

  Definition intr_handler_spec (handler : mword 64)
      (root_ppn : mword 44) (menvcfg0 : mword 64) : iProp Σ :=
    (□ ∀ (elp_v : mword 1) (ms pc0 mie_v mdv0 : mword 64)
         (m : gmap regidx (mword 64)) (Φ : mval -> iProp Σ),
        ⌜ intr_ms_facts ms ⌝ -∗
        ⌜ sret_tgt pc0 = pc0 ⌝ -∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝ -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        cur_privilege ↦ᵣ Supervisor -∗
        mstatus ↦ᵣ trap_ms elp_v ms -∗
        mie ↦ᵣ mie_v -∗
        mideleg ↦ᵣ mdv0 -∗
        sepc ↦ᵣ pc0 -∗
        pc_is handler -∗
        gpr_file m -∗
        intr_frame root_ppn menvcfg0 m -∗
        ( hart_state ↦ᵣ HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ Supervisor -∗
          mstatus ↦ᵣ sret_ms5 (trap_ms elp_v ms) -∗
          mie ↦ᵣ mie_v -∗
          mideleg ↦ᵣ mdv0 -∗
          (∃ v : mword 64, sepc ↦ᵣ v) -∗
          pc_is pc0 -∗
          gpr_file m -∗
          intr_frame root_ppn menvcfg0 m -∗
          WP (Loop : expr riscv_lang) {{ Φ }} ) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I.

  Global Instance intr_handler_spec_persistent handler root_ppn menvcfg0 :
    Persistent (intr_handler_spec handler root_ppn menvcfg0).
  Proof. apply _. Qed.

  (* =================================================================== *)
  (* §5 THE INVARIANT: a quarter of the SIE ghost (its value [b] mirrors   *)
  (* the live mstatus.SIE bit, via agreement with the mstatus-tied half),  *)
  (* the stvec register, and -- when interrupts are enabled -- the         *)
  (* persistent handler WP.  The two pure facts about [handler] (a         *)
  (* Direct-mode vector whose base is itself) ride OUTSIDE the inv, fixed  *)
  (* at allocation.                                                        *)
  (* =================================================================== *)

  Definition intrN : namespace := nroot .@ "intr".

  Definition intr_inv_body (γ : gname) (handler : mword 64)
      (root_ppn : mword 44) (menvcfg0 : mword 64) : iProp Σ :=
    (∃ b : mword 1,
       ghost_var γ (1/4) b ∗
       stvec ↦ᵣ handler ∗
       □ (⌜ b = ('b"1" : mword 1) ⌝ -∗ intr_handler_spec handler root_ppn menvcfg0))%I.

  Definition intr_inv (γ : gname) (handler : mword 64)
      (root_ppn : mword 44) (menvcfg0 : mword 64) : iProp Σ :=
    (⌜ trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ⌝ ∗
     ⌜ stvec_base handler = handler ⌝ ∗
     inv intrN (intr_inv_body γ handler root_ppn menvcfg0))%I.

  Global Instance intr_inv_persistent γ handler root_ppn menvcfg0 :
    Persistent (intr_inv γ handler root_ppn menvcfg0).
  Proof. apply _. Qed.

  Lemma intr_inv_alloc E (γ : gname) (b : mword 1) (handler : mword 64)
      (root_ppn : mword 44) (menvcfg0 : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    ghost_var γ (1/4) b -∗
    stvec ↦ᵣ handler -∗
    □ (⌜ b = ('b"1" : mword 1) ⌝ -∗ intr_handler_spec handler root_ppn menvcfg0) ={E}=∗
    intr_inv γ handler root_ppn menvcfg0.
  Proof.
    iIntros (Htvd Hsb) "Hq Hstv #Hspec".
    iMod (inv_alloc intrN E (intr_inv_body γ handler root_ppn menvcfg0)
            with "[Hq Hstv]") as "#Hi".
    { iNext. rewrite /intr_inv_body. iExists b. iFrame "Hq Hstv". iExact "Hspec". }
    iModIntro. iSplit; [done |]. iSplit; [done |]. iExact "Hi".
  Qed.

  (* allocation with interrupts DISABLED needs no handler spec: the guarded
     implication is vacuous. *)
  Lemma intr_inv_alloc_off E (γ : gname) (handler : mword 64)
      (root_ppn : mword 44) (menvcfg0 : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    ghost_var γ (1/4) ('b"0" : mword 1) -∗
    stvec ↦ᵣ handler ={E}=∗
    intr_inv γ handler root_ppn menvcfg0.
  Proof.
    iIntros (Htvd Hsb) "Hq Hstv".
    iApply (intr_inv_alloc E γ _ handler root_ppn menvcfg0 Htvd Hsb with "Hq Hstv").
    iModIntro. iIntros (Hb).
    exfalso. apply (f_equal (@bv_unsigned _)) in Hb.
    vm_compute in Hb. discriminate.
  Qed.

  (* =================================================================== *)
  (* §6 The dispatch outcome read straight off σ.  mip lives in            *)
  (* [clock_inv] and the wire pins in [wire_inv], so no cell can name      *)
  (* their values; but [dispatchInterrupt] is a FUNCTION of σ, so the      *)
  (* outcome is [s_dispatch] of σ's OWN lookups -- no ownership needed     *)
  (* beyond the client's misa/mie/mideleg/mstatus pins.                    *)
  (* =================================================================== *)
  Lemma dispatch_S_transient (σ : mstate) (misa0 mie_v mdv0 ms : mword 64)
      {dqm dqi dqd dqs : dfrac} :
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    mstate_interp σ -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    mie ↦ᵣ{ dqi } mie_v -∗
    mideleg ↦ᵣ{ dqd } mdv0 -∗
    mstatus ↦ᵣ{ dqs } ms -∗
    ⌜ exec (dispatchInterrupt Supervisor) σ
        = Some (s_dispatch (register_lookup mip σ.(sregs))
                           (register_lookup sig_meip σ.(sregs))
                           (register_lookup sig_seip σ.(sregs))
                           mie_v mdv0 ms, σ) ⌝.
  Proof.
    iIntros (HmisaS Hmm) "[Hreg Hmem] Hmisa Hmie Hmdl Hms".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl") as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iPureIntro.
    apply exec_dispatchInterrupt_S_reduce;
      [ | reflexivity | reflexivity | reflexivity
        | exact Lmie | exact Lmdl | exact Lms | exact Hmm ].
    rewrite exec_currentlyEnabled_S Lmisa HmisaS. reflexivity.
  Qed.

  (* =================================================================== *)
  (* §7 The joint step rule: ONE machine step that either RETIRES an       *)
  (* instruction or TAKES a pending interrupt -- the σ-callback chooses    *)
  (* the branch AFTER seeing σ (the dispatch inputs are functions of σ,    *)
  (* unknowable outside the step).  Merge of [wp_exec_step_hart_active_inv]*)
  (* (MinstretInv.v) and [wp_exec_step_interrupt_inv] (WpIntrCore.v),      *)
  (* directly over [wp_exec_step_minstret]: retire bumps minstret, an      *)
  (* interrupt does not; both continuations come back under the step's ▷.  *)
  (* =================================================================== *)
  Lemma wp_exec_step_retire_or_intr Φ {dq : dfrac} :
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ,
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ( (* the instruction retires *)
         ∃ (retval : mword 32) (s_exec : mstate),
           ⌜ exec (run_hart_active 0) σ
               = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec) ⌝ ∗
           PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
           mstate_interp s_exec ∗
           (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
            PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
            ▷ WP (Loop : expr riscv_lang) {{ Φ }}) )
       ∨
       ( (* a pending interrupt is taken (no fetch, no retire, no bump) *)
         ∃ (i : InterruptType) (p : Privilege) (s_trap : mstate),
           ⌜ exec (run_hart_active 0) σ = Some (Step_Pending_Interrupt (i, p), σ) ⌝ ∗
           ⌜ exec (handle_interrupt i p) σ = Some (tt, s_trap) ⌝ ∗
           PC ↦ᵣ (register_lookup PC s_trap.(sregs)) ∗
           mstate_interp s_trap ∗
           ▷ (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
              PC ↦ᵣ (register_lookup nextPC s_trap.(sregs)) -∗
              WP (Loop : expr riscv_lang) {{ Φ }}) )) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hinv Hhs H".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) Φ with "Hinv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) with "[Hreg Hmem]")
      as "[Hret | Hintr]".
    { rewrite /mstate_interp. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    - (* ---- retire: verbatim wp_exec_step_hart_active_inv continuation ---- *)
      iDestruct "Hret" as (retval s_exec) "(%Hha & Hpc & [Hreg Hmem] & Hcont)".
      iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_exec.
      iDestruct (reg_valid with "Hreg Hmi") as %Hmi_exec.
      assert (Hhart_a :
        register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
          = HART_ACTIVE tt).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
      iDestruct (reg_valid with "Hreg Hmst") as %Lmst_e.
      iMod (reg_update _ PC _ (register_lookup nextPC s_exec.(sregs)) with "Hreg Hpc")
        as "[Hreg Hpc]".
      assert (Hmst_tick :
        register_lookup minstret
          (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs) = mst).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Lmst_e | reflexivity]. }
      iDestruct ("Hcont" with "Hhs Hpc") as "HWP".
      destruct b.
      + iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst")
          as "[Hreg Hmst]".
        iModIntro. iExists _. iSplitR.
        { iPureIntro.
          exact (exec_riscv_step_hart_active σ s_exec retval true
                   Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
        iNext.
        iModIntro. rewrite /mstate_interp. cbn [sregs mem]. rewrite Hmst_tick.
        unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi".
        { iExists (add_vec_int mst 1), true. iFrame. }
        iExact "HWP".
      + iModIntro. iExists _. iSplitR.
        { iPureIntro.
          exact (exec_riscv_step_hart_active σ s_exec retval false
                   Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
        iNext.
        iModIntro. rewrite /mstate_interp. unfold set_reg; cbn [sregs mem].
        iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi".
        { iExists mst, false. iFrame. }
        iExact "HWP".
    - (* ---- interrupt: verbatim wp_exec_step_interrupt_inv continuation ---- *)
      iDestruct "Hintr" as (i p s_trap) "(%Hha & %Hhi & Hpc & [Hreg Hmem] & Hcont)".
      iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_trap.
      assert (Hhart_a :
        register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
          = HART_ACTIVE tt).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
      iModIntro. iExists _. iSplitR.
      { iPureIntro.
        exact (exec_riscv_step_interrupt σ s_trap i p b
                 Hsi Hhart_a Hha Hhi Hhart_trap). }
      iNext.
      iMod (reg_update _ PC _ (register_lookup nextPC s_trap.(sregs)) with "Hreg Hpc")
        as "[Hreg Hpc]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists mst, b. iFrame. }
      iApply ("Hcont" with "Hhs Hpc").
  Qed.

  (* =================================================================== *)
  (* §8 THE ENGINE: run the point just before an instruction at [pc0]     *)
  (* with interrupts ENABLED, under the interrupt invariant.  Takes an    *)
  (* arbitrary number of pending interrupts (Löb induction over the       *)
  (* trap + handler round trip), then hands the caller's σ-callback the   *)
  (* pure no-pending fact and lets the instruction execute.  Every        *)
  (* threaded resource comes back to the callback UNCHANGED; the          *)
  (* callback's obligation is [wp_exec_step_hart_active_inv]'s.           *)
  (* =================================================================== *)
  Lemma wp_exec_step_intr (γ : gname) (handler pc0 : mword 64)
      (root_ppn : mword 44) (menvcfg0 : mword 64)
      (m : gmap regidx (mword 64))
      (Φ : mval -> iProp Σ) :
    sret_tgt pc0 = pc0 ->
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc0 -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    (∀ σ,
       ⌜ exec (dispatchInterrupt Supervisor) σ = Some (None, σ) ⌝ -∗
       intr_config γ -∗
       pc_is pc0 -∗
       gpr_file m -∗
       intr_frame root_ppn menvcfg0 m -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (retval : mword 32) (s_exec : mstate),
         ⌜ exec (run_hart_active 0) σ
             = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec) ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hpc0.
    iIntros "#Hintr Hhs Hcfg Hpc Hfile HF Hbody".
    iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
    iRevert "Hhs Hcfg Hpc Hfile HF Hbody".
    iLöb as "IH".
    iIntros "Hhs Hcfg Hpc Hfile HF Hbody".
    iDestruct "Hcfg" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hsepcx & Hscausex & Hstvalx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hsie & %Hmsf)".
    iDestruct "Hmiex" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iApply (wp_exec_step_retire_or_intr Φ with "Hminv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (dispatch_S_transient σ misa0 mie_v mdv0 ms HmisaS Hmm
                 with "Hsi Hmisa Hmie Hmdl Hms") as %Hdisp0.
    match type of Hdisp0 with _ = Some (?D, _) =>
      destruct D as [[i p] |] eqn:Hdres end.
    - (* ---- an interrupt is pending: take it, run the handler, Löb ---- *)
      pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hdres); subst p.
      (* the destruct folded [Hdres] into [Hdisp0]:
         Hdisp0 : exec (dispatchInterrupt Supervisor) σ = Some (Some (i, Supervisor), σ) *)
      (* borrow the invariant for this step: stvec (read by the trap), the
         invariant quarter (agreement pins b = SIE ms = 1), the handler WP *)
      iInv "Hinv_i" as (b) "(>Hq & >Hstv & #Hspec)" "Hclose".
      iDestruct (ghost_var_agree with "Hsie Hq") as %Hbv.
      assert (Hb1 : b = ('b"1" : mword 1)).
      { rewrite <- Hbv. apply eq_vec_true_iff. exact HSIE1. }
      iDestruct "Hsepcx" as (sepc_old) "Hsepc".
      iDestruct "Hscausex" as (scause_old) "Hscause".
      iDestruct "Hstvalx" as (stval_old) "Hstval".
      iDestruct "Hpc" as "[Hpcr Hnpc]".
      iDestruct "Hsi" as "[Hreg Hmem]".
      iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
      iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
      iDestruct (reg_valid with "Hreg Hms") as %Lms.
      iDestruct (reg_valid with "Hreg Hscause") as %Lsc.
      iDestruct (reg_valid with "Hreg Hstv") as %Lstvec.
      iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
      iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
      assert (HmisaS' : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaS).
      pose proof (exec_run_hart_active_pending σ i Supervisor Lpriv Hdisp0) as Hha.
      pose proof (exec_handle_interrupt_S σ i pc0 ms scause_old handler elp0
                    Lpriv Lms Lsc Lstvec Lelp HmisaS' Htvd Lpc) as Hhi.
      match type of Hhi with _ = Some (_, ?T) => set (s_trap := T) in Hhi end.
      (* thread the trap's writes through the ghost cells, in tower order *)
      pose (ms_e := update_subrange_vec_dec ms 23 23 elp0).
      pose (c1v := update_subrange_vec_dec scause_old (64 - 1) (64 - 1)
                     (bool_to_bit (trapCause_is_interrupt (Interrupt i)))).
      pose (c2v := update_subrange_vec_dec c1v (64 - 2) 0
                     (zero_extend' (64 - 1) (trapCause_bits_forwards (Interrupt i)))).
      pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
      pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
      pose (ms_c := update_subrange_vec_dec ms_b 8 8 ('b"1")).
      iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
      assert (Hlkelp : register_lookup elp (register_set mstatus ms_e σ.(sregs))
                       = landing_pad_bits_backwards NO_LP_EXPECTED).
      { rewrite irrelevant_register_set; [ rewrite Lelp; exact Help0 | vm_compute; reflexivity ]. }
      iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
      iMod (reg_update _ scause _ c1v with "Hreg Hscause") as "[Hreg Hscause]".
      iMod (reg_update _ scause _ c2v with "Hreg Hscause") as "[Hreg Hscause]".
      iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
      iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
      iMod (reg_update _ mstatus _ ms_c with "Hreg Hms") as "[Hreg Hms]".
      iMod (reg_update _ stval _ (zeros' 64) with "Hreg Hstval") as "[Hreg Hstval]".
      iMod (reg_update _ sepc _ pc0 with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base handler) with "Hreg Hnpc") as "[Hreg Hnpc]".
      (* re-seal the invariant (same ghost value; the spec is persistent) *)
      iMod ("Hclose" with "[Hq Hstv]") as "_".
      { iNext. iExists b. iFrame "Hq Hstv". iExact "Hspec". }
      iModIntro. iRight.
      iExists i, Supervisor, s_trap.
      iSplitR; [iPureIntro; exact Hha |].
      iSplitR; [iPureIntro; exact Hhi |].
      assert (LpcT : register_lookup PC s_trap.(sregs) = pc0).
      { unfold s_trap. lk. exact Lpc. }
      rewrite LpcT.
      iSplitL "Hpcr"; [iExact "Hpcr" |].
      iSplitL "Hreg Hmem".
      { unfold s_trap, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iNext.
      iIntros "Hhs Hpcr".
      assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base handler).
      { unfold s_trap. lk. reflexivity. }
      iEval (rewrite LnT Hsb) in "Hpcr".
      iEval (rewrite Hsb) in "Hnpc".
      assert (Htm : ms_c = trap_ms elp0 ms) by reflexivity.
      iEval (rewrite Htm) in "Hms".
      (* ---- the invariant's handler WP discharges the whole handler ---- *)
      iAssert (intr_handler_spec handler root_ppn menvcfg0) with "[]" as "#Hsp".
      { iApply "Hspec". iPureIntro. exact Hb1. }
      iApply ("Hsp" $! elp0 ms pc0 mie_v mdv0 m Φ
                with "[%] [%] [%] Hhs Hpriv Hms Hmie Hmdl Hsepc [$Hpcr $Hnpc] Hfile HF").
      { exact Hmsf. }
      { exact Hpc0. }
      { exact Hmm. }
      (* the handler's return continuation: re-establish the frame + Löb *)
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hsepcx Hpc Hfile HF".
      assert (Hs1 : _get_Mstatus_SIE (sret_ms5 (trap_ms elp0 ms)) = ('b"1" : mword 1))
        by (apply eq_vec_true_iff; exact (roundtrip_SIE_true elp0 ms HSIE1)).
      assert (Hs2 : _get_Mstatus_SIE ms = ('b"1" : mword 1))
        by (apply eq_vec_true_iff; exact HSIE1).
      iEval (rewrite Hs2 -Hs1) in "Hsie".
      iApply ("IH" with "Hhs [Hpriv Hms Hsie Hmie Hmdl Hsepcx Hscause Hstval] Hpc Hfile HF Hbody").
      iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hsie".
      { iExists (sret_ms5 (trap_ms elp0 ms)). iFrame "Hms Hsie".
        iPureIntro. exact (intr_ms_facts_roundtrip elp0 ms Hmsf). }
      iSplitL "Hmie Hmdl".
      { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iFrame "Hsepcx".
      iSplitL "Hscause". { iExists c2v. iFrame "Hscause". }
      iExists (zeros' 64). iFrame "Hstval".
    - (* ---- nothing pending: the caller's instruction executes ----
         (the destruct folded [Hdres] into [Hdisp0]:
          Hdisp0 : exec (dispatchInterrupt Supervisor) σ = Some (None, σ)) *)
      iSpecialize ("Hbody" $! σ with "[%]"); [exact Hdisp0 |].
      iMod ("Hbody" with "[Hpriv Hms Hsie Hmie Hmdl Hsepcx Hscausex Hstvalx] Hpc Hfile HF Hsi")
        as (retval s_exec) "(%Hha & Hpc' & Hsi' & Hcont)".
      { iFrame "Hhw Hminv Hpriv".
        iSplitL "Hms Hsie".
        { iExists ms. iFrame "Hms Hsie". iPureIntro. exact Hmsf. }
        iSplitL "Hmie Hmdl".
        { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
        iFrame "Hsepcx Hscausex Hstvalx". }
      iModIntro. iLeft.
      iExists retval, s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      iFrame "Hpc' Hsi'". iExact "Hcont".
  Qed.

  (* =================================================================== *)
  (* §9 kernelvec satisfies the handler contract.  The proof peels the    *)
  (* top [kv_frame_slots] slots off the frame's [stack_own] (the depth is *)
  (* only a lower bound; the deeper remainder rides along untouched),     *)
  (* re-addresses kernelvec's 17 sparse save windows as [pa_stk] slots,   *)
  (* and drives [wp_kernelvec].  hw_config / minstret_inv / kernel_text   *)
  (* are persistent and captured at spec-creation time.  The SIE ghost    *)
  (* kernelvec's spec consumes is a FRESH per-trap name [γk] (allocated   *)
  (* here, tied to the trapped SIE=0 and discarded at the sret) -- the    *)
  (* REAL [γ]'s pieces stay outside the handler run, untouched, so the    *)
  (* live-bit tie is restored for free when SRET brings SIE back to 1.    *)
  (* =================================================================== *)
  Lemma kernelvec_handler_spec (root_ppn : mword 44) (menvcfg0 : mword 64) :
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    kernel_text -∗
    intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64)
      root_ppn menvcfg0.
  Proof.
    intros HPBMTE Hmenvval0 Hpmm Hlpe0 HFIOM.
    iIntros "#Hhw #Hinv #Htext".
    iModIntro.
    iIntros (elp_v ms pc0 mie_v mdv0 m Φ)
      "%Hfacts %Hpc0 %Hmm Hhs Hpriv Hms Hmie Hmdl Hsepc Hpc Hfile HF Hcont".
    pose proof Hfacts as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "HF" as "(Hmenv & Htlbinv & Hstkx)".
    iDestruct "Hstkx" as (nstk) "[%Hn Hstk]".
    (* peel the handler's 32 slots off the top; the deeper remainder rides *)
    iDestruct (stack_own_split_1 (m !!! Regidx csp_rs1) kv_frame_slots nstk Hn
                 with "Hstk") as "[Hstk Hdeep]".
    (* re-address kernelvec's 17 sparse save windows as [pa_stk] slots *)
    pose proof (kv_slot_addr0 m) as Hb32.
    assert (Hb30 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 30)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb28 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 28)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb27 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 27)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb26 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 26)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb23 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 23)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb22 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 22)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb21 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 21)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb20 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 20)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb19 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 19)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb18 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 18)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb17 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 17)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb16 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 16)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb5 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 5)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb4 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 4)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb3 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 3)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb2 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 2)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    (* open the 32-slot frame and pull out the 17 save slots *)
    iEval (rewrite /kv_frame_slots stack_own_slots; cbn [seq]) in "Hstk".
    iDestruct "Hstk" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 &
      S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 &
      S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31 & S32 & _)".
    iDestruct "S32" as (w1) "Hw1".   iEval (rewrite -Hb32) in "Hw1".
    iDestruct "S30" as (w2) "Hw2".   iEval (rewrite -Hb30) in "Hw2".
    iDestruct "S28" as (w3) "Hw3".   iEval (rewrite -Hb28) in "Hw3".
    iDestruct "S27" as (w4) "Hw4".   iEval (rewrite -Hb27) in "Hw4".
    iDestruct "S26" as (w5) "Hw5".   iEval (rewrite -Hb26) in "Hw5".
    iDestruct "S23" as (w6) "Hw6".   iEval (rewrite -Hb23) in "Hw6".
    iDestruct "S22" as (w7) "Hw7".   iEval (rewrite -Hb22) in "Hw7".
    iDestruct "S21" as (w8) "Hw8".   iEval (rewrite -Hb21) in "Hw8".
    iDestruct "S20" as (w9) "Hw9".   iEval (rewrite -Hb20) in "Hw9".
    iDestruct "S19" as (w10) "Hw10". iEval (rewrite -Hb19) in "Hw10".
    iDestruct "S18" as (w11) "Hw11". iEval (rewrite -Hb18) in "Hw11".
    iDestruct "S17" as (w12) "Hw12". iEval (rewrite -Hb17) in "Hw12".
    iDestruct "S16" as (w13) "Hw13". iEval (rewrite -Hb16) in "Hw13".
    iDestruct "S5" as (w14) "Hw14".  iEval (rewrite -Hb5) in "Hw14".
    iDestruct "S4" as (w15) "Hw15".  iEval (rewrite -Hb4) in "Hw15".
    iDestruct "S3" as (w16) "Hw16".  iEval (rewrite -Hb3) in "Hw16".
    iDestruct "S2" as (w17) "Hw17".  iEval (rewrite -Hb2) in "Hw17".
    (* clearing SIE on the trap-time mstatus is idempotent under legalization
       (the ext-state / dirty / MPP well-formedness rides in via intr_ms_facts) *)
    assert (Hleg_trap :
      WpGprCsrwCommon.legalize_sstatus_val (trap_ms elp_v ms)
        (WpGprCsrwCommon.sstatus_write_val (trap_ms elp_v ms) (mword_of_int 2))
      = trap_ms elp_v ms).
    { apply WpGprCsrwC.legalize_sie_clear_idem.
      - apply trap_ms_SIE.
      - rewrite trap_ms_XS; exact HXS.
      - rewrite trap_ms_FS; exact HFS.
      - rewrite trap_ms_VS; exact HVS.
      - rewrite trap_ms_SD; exact HSD.
      - rewrite trap_ms_MPP; exact HMPP. }
    (* kernelvec's spec assumes a SIE ghost half tied to ITS entering mstatus
       (SIE=0); the real γ's pieces stay outside the handler run, so allocate
       a fresh per-trap name and hand kernelvec one half. *)
    iMod (ghost_var_alloc (_get_Mstatus_SIE (trap_ms elp_v ms))) as (γk) "Hg".
    iEval (rewrite -Qp.half_half) in "Hg".
    iDestruct (ghost_var_split with "Hg") as "[Hsie _]".
    iApply (wp_kernelvec root_ppn γk m (trap_ms elp_v ms) mie_v mdv0 menvcfg0 pc0
              w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 Φ
              (trap_ms_SIE_false elp_v ms)
              (trap_ms_MPRV_false elp_v ms HMPRV0)
              (trap_ms_SXL_eq elp_v ms HSXL)
              Hmm HPBMTE Hmenvval0
              (trap_ms_MXR_true elp_v ms HMXR)
              Hpmm
              (trap_ms_TSR_false elp_v ms HTSR)
              (sret_newpriv_trap_ms elp_v ms)
              Hlpe0
              HFIOM
              Hleg_trap
              with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hsepc
                    Hpc Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile
             Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite Hpc0) in "Hpc".
    (* the save slots come back holding [m]'s registers; re-address them as
       [pa_stk] slots and rebuild the 32-slot [stack_own] frame *)
    iEval (rewrite Hb32) in "Hw1".
    iEval (rewrite Hb30) in "Hw2".
    iEval (rewrite Hb28) in "Hw3".
    iEval (rewrite Hb27) in "Hw4".
    iEval (rewrite Hb26) in "Hw5".
    iEval (rewrite Hb23) in "Hw6".
    iEval (rewrite Hb22) in "Hw7".
    iEval (rewrite Hb21) in "Hw8".
    iEval (rewrite Hb20) in "Hw9".
    iEval (rewrite Hb19) in "Hw10".
    iEval (rewrite Hb18) in "Hw11".
    iEval (rewrite Hb17) in "Hw12".
    iEval (rewrite Hb16) in "Hw13".
    iEval (rewrite Hb5) in "Hw14".
    iEval (rewrite Hb4) in "Hw15".
    iEval (rewrite Hb3) in "Hw16".
    iEval (rewrite Hb2) in "Hw17".
    iAssert (stack_own (m !!! Regidx csp_rs1) kv_frame_slots)
      with "[S1 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S24 S25 S29 S31
            Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17]"
      as "Hstk".
    2:{ iDestruct (stack_own_split_2 (m !!! Regidx csp_rs1) kv_frame_slots nstk Hn
                     with "[$Hstk $Hdeep]") as "Hstk".
        iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl [Hsepc] Hpc Hfile [Hmenv Htlbinv Hstk]").
        { iExists pc0. iFrame "Hsepc". }
        iFrame "Hmenv Htlbinv".
        iExists nstk. iSplitR; [iPureIntro; exact Hn |]. iExact "Hstk". }
    rewrite /kv_frame_slots stack_own_slots. cbn [seq].
    iSplitL "S1"; [iExact "S1" |].
    iSplitL "Hw17"; [by iExists _ |].
    iSplitL "Hw16"; [by iExists _ |].
    iSplitL "Hw15"; [by iExists _ |].
    iSplitL "Hw14"; [by iExists _ |].
    iSplitL "S6"; [iExact "S6" |].
    iSplitL "S7"; [iExact "S7" |].
    iSplitL "S8"; [iExact "S8" |].
    iSplitL "S9"; [iExact "S9" |].
    iSplitL "S10"; [iExact "S10" |].
    iSplitL "S11"; [iExact "S11" |].
    iSplitL "S12"; [iExact "S12" |].
    iSplitL "S13"; [iExact "S13" |].
    iSplitL "S14"; [iExact "S14" |].
    iSplitL "S15"; [iExact "S15" |].
    iSplitL "Hw13"; [by iExists _ |].
    iSplitL "Hw12"; [by iExists _ |].
    iSplitL "Hw11"; [by iExists _ |].
    iSplitL "Hw10"; [by iExists _ |].
    iSplitL "Hw9"; [by iExists _ |].
    iSplitL "Hw8"; [by iExists _ |].
    iSplitL "Hw7"; [by iExists _ |].
    iSplitL "Hw6"; [by iExists _ |].
    iSplitL "S24"; [iExact "S24" |].
    iSplitL "S25"; [iExact "S25" |].
    iSplitL "Hw5"; [by iExists _ |].
    iSplitL "Hw4"; [by iExists _ |].
    iSplitL "Hw3"; [by iExists _ |].
    iSplitL "S29"; [iExact "S29" |].
    iSplitL "Hw2"; [by iExists _ |].
    iSplitL "S31"; [iExact "S31" |].
    iSplitL "Hw1"; [by iExists _ |].
    done.
  Qed.

End WpIntrInv.
