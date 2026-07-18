(* IntrDefs.v -- the interrupt-stack DEFINITIONS, at leaf altitude.

   Holds everything a leaf-level S-mode WP file needs to STATE
   interrupt-aware specs, split out of WpIntrInv.v (which keeps the
   step ENGINES and imports high-altitude machinery no leaf may pull):

     - the SIE ghost choreography (1/2 live-bit tie + 1/4 kernel-code
       token + 1/4 invariant quarter): [sie_ghost_alloc]/[sie_ghost_flip];
     - the interrupts-ENABLED regime: [intr_ms_facts], [intr_config],
       [intr_frame] (+[intr_frame_retarget]), [intr_handler_spec],
       [intr_inv] (+allocation);
     - the SIE-AGNOSTIC v2 bundle (the smode_config successor):
       [sconf_ms_facts] (the SIE-free common fact set), [sconf]
       (SIE unpinned, ghost half tied to the live bit, menvcfg bundled),
       and the kernel-code capability [sie_cap] -- the '0' arm is the
       bare quarter token, the '1' arm carries the quarter + the
       interrupt invariant + the trap-scratch CSRs + the >= 32-slot
       free-stack bound below sp, i.e. exactly the extra obligations of
       running with interrupts enabled;
     - the conversions [intr_config_of_v2] / [v2_of_intr_config] the
       agnostic engines use to enter/exit the absorbing step engine.   *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr WpMmodeLeafBase StackOwn.
Require Import SmodeCore KptTree.
Require Import WpSmodeSret WpIntrBits WpIntrCore.
(* have_nom_val: kept QUALIFIED (no Import) so the WpGprCsrwCommon
   namespace doesn't shadow anything here. *)
Require WpGprCsrwCommon.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Pure layer: the mstatus fact sets.                                  *)
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

(* the SIE-AGNOSTIC common fact set: [intr_ms_facts] minus the SIE pin.
   The '0' regime recovers the legalize fixpoint smode_config carried via
   [legalize_sie_clear_idem] (WpGprCsrwC.v) from ghost-derived SIE=0 +
   the XS/FS/VS/SD/MPP conjuncts. *)
Definition sconf_ms_facts (ms : mword 64) : Prop :=
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false /\
  _get_Mstatus_XS ms = extStatus_map_forwards Off /\
  _get_Mstatus_FS ms = extStatus_map_forwards Off /\
  _get_Mstatus_VS ms = extStatus_map_forwards Off /\
  _get_Mstatus_SD ms = 'b"0" /\
  WpGprCsrwCommon.have_nom_val (_get_Mstatus_MPP ms) = true.

Lemma intr_ms_facts_iff (ms : mword 64) :
  intr_ms_facts ms
  <-> (eq_vec (_get_Mstatus_SIE ms) ('b"1") = true /\ sconf_ms_facts ms).
Proof. unfold intr_ms_facts, sconf_ms_facts. tauto. Qed.

Section IntrDefs.
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
  (* plus the allocation-fixed menvcfg cell and tlb_inv_pt.  The depth is  *)
  (* a BOUND (existential), so a client simply packs in however much free  *)
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

  (* [intr_frame] depends on [m] only through sp: any register write that
     PRESERVES sp transports the frame to the new map.  (An sp-moving
     instruction instead re-carves its stack explicitly.) *)
  Lemma intr_frame_retarget (root_ppn : mword 44) (menvcfg0 : mword 64)
      (m m' : gmap regidx (mword 64)) :
    m !!! Regidx csp_rs1 = m' !!! Regidx csp_rs1 ->
    intr_frame root_ppn menvcfg0 m -∗ intr_frame root_ppn menvcfg0 m'.
  Proof.
    iIntros (Hsp) "(Hmenv & Htlbinv & Hstk)".
    iFrame "Hmenv Htlbinv". iDestruct "Hstk" as (n) "[%Hn Hstk]".
    iExists n. iSplit; [iPureIntro; exact Hn |]. rewrite Hsp. iExact "Hstk".
  Qed.

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
  (* §6 THE V2 BUNDLE [sconf]: the SIE-AGNOSTIC smode_config successor.   *)
  (* [intr_config] + the menvcfg conjunct, SIE unpinned; full ownership   *)
  (* (the trap writes its cells); the trap CSRs are NOT bundled (they     *)
  (* ride in [sie_cap]'s '1' arm -- SIE=0 code owns sepc explicitly).     *)
  (* [hart_state] travels beside the bundle, as in [intr_config].         *)
  (* =================================================================== *)
  Definition sconf (γ : gname) : iProp Σ :=
    (hw_config ∗ minstret_inv ∗
     cur_privilege ↦ᵣ Supervisor ∗
     (∃ ms : mword 64,
        mstatus ↦ᵣ ms ∗
        ghost_var γ (1/2) (_get_Mstatus_SIE ms) ∗
        ⌜ sconf_ms_facts ms ⌝) ∗
     (∃ mie_v mdv0 : mword 64,
        mie ↦ᵣ mie_v ∗ mideleg ↦ᵣ mdv0 ∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝) ∗
     (∃ menvcfg0 : mword 64,
        menvcfg ↦ᵣ menvcfg0 ∗
        ⌜ eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ⌝ ∗
        ⌜ pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ⌝ ∗
        ⌜ bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ⌝ ∗
        ⌜ eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ⌝ ∗
        ⌜ menvcfg0 = MENVCFG_S ⌝))%I.

  (* [sie_cap] -- the kernel-code capability that DISCRIMINATES the SIE
     mode by the ghost QUARTER's value (agreement with [sconf]'s tied
     half pins the live bit).  The '1' arm carries exactly the extra
     obligations of interrupts-enabled execution: the interrupt
     invariant (handler existential -- no client names the handler), the
     trap-scratch CSRs (any trap scribbles them, so enabled code cannot
     pin their values), and the free-stack bound below sp. *)
  Definition sie_cap (γ : gname) (root_ppn : mword 44)
      (m : gmap regidx (mword 64)) : iProp Σ :=
    (ghost_var γ (1/4) ('b"0" : mword 1) ∨
     (ghost_var γ (1/4) ('b"1" : mword 1) ∗
      (∃ handler : mword 64, intr_inv γ handler root_ppn MENVCFG_S) ∗
      (∃ v : mword 64, sepc ↦ᵣ v) ∗
      (∃ v : mword 64, scause ↦ᵣ v) ∗
      (∃ v : mword 64, stval ↦ᵣ v) ∗
      (∃ n : nat, ⌜ (kv_frame_slots <= n)%nat ⌝ ∗
                  stack_own (m !!! Regidx csp_rs1) n)))%I.

  (* build an sp-MOVING transformer: the '0' arm is m-blind, so a
     caller only re-carves the '1' arm's stack bound at the new sp
     (pure [stack_own] splitting, where function proofs already do
     their stack bookkeeping). *)
  Lemma sie_cap_recarve (γ : gname) (root_ppn : mword 44)
      (m m' : gmap regidx (mword 64)) :
    ( ∀ n : nat, ⌜ (kv_frame_slots <= n)%nat ⌝ -∗
      stack_own (m !!! Regidx csp_rs1) n -∗
      ∃ n' : nat, ⌜ (kv_frame_slots <= n')%nat ⌝ ∗
                  stack_own (m' !!! Regidx csp_rs1) n' ) -∗
    sie_cap γ root_ppn m -∗ sie_cap γ root_ppn m'.
  Proof.
    iIntros "Hcarve [H0 | (Hq & Hinv & Hsepc & Hscause & Hstval & Hstk)]".
    - iLeft. iExact "H0".
    - iRight. iFrame "Hq Hinv Hsepc Hscause Hstval".
      iDestruct "Hstk" as (n) "[%Hn Hstk]".
      iApply ("Hcarve" $! n with "[%] Hstk"). exact Hn.
  Qed.

  (* [sie_cap] depends on [m] only through sp (same as [intr_frame]). *)
  Lemma sie_cap_retarget (γ : gname) (root_ppn : mword 44)
      (m m' : gmap regidx (mword 64)) :
    m !!! Regidx csp_rs1 = m' !!! Regidx csp_rs1 ->
    sie_cap γ root_ppn m -∗ sie_cap γ root_ppn m'.
  Proof.
    iIntros (Hsp) "[H0 | (Hq & Hinv & Hsepc & Hscause & Hstval & Hstk)]".
    - iLeft. iExact "H0".
    - iRight. iFrame "Hq Hinv Hsepc Hscause Hstval".
      iDestruct "Hstk" as (n) "[%Hn Hstk]".
      iExists n. iSplit; [iPureIntro; exact Hn |]. rewrite Hsp. iExact "Hstk".
  Qed.

  (* =================================================================== *)
  (* §7 The v2 <-> interrupts-enabled conversions: the agnostic engines'  *)
  (* '1' arm assembles [intr_config]/[intr_frame] for the absorbing step  *)
  (* engine and disassembles them back around its σ-callback.  Ghost      *)
  (* agreement (tied half vs the quarter-'1' token) pins SIE=1; the       *)
  (* quarter and the menvcfg cell come back out (the absorbing engine     *)
  (* threads neither).                                                    *)
  (* =================================================================== *)
  Lemma intr_config_of_v2 (γ : gname) :
    sconf γ -∗
    ghost_var γ (1/4) ('b"1" : mword 1) -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    intr_config γ ∗ ghost_var γ (1/4) ('b"1" : mword 1) ∗ menvcfg ↦ᵣ MENVCFG_S.
  Proof.
    iIntros "Hsc Hq Hsepc Hscause Hstval".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & %Hmsf)".
    iDestruct (ghost_var_agree with "Hhalf Hq") as %Hb1.
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & _ & _ & _ & _ & %Hval)".
    subst menvcfg0.
    iFrame "Hq Hmenv Hhw Hminv Hpriv Hmiex Hsepc Hscause Hstval".
    iExists ms. iFrame "Hms Hhalf".
    iPureIntro. apply intr_ms_facts_iff. split; [ | exact Hmsf ].
    rewrite Hb1. vm_compute. reflexivity.
  Qed.

  Lemma v2_of_intr_config (γ : gname) :
    intr_config γ -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    sconf γ ∗
    (∃ v : mword 64, sepc ↦ᵣ v) ∗
    (∃ v : mword 64, scause ↦ᵣ v) ∗
    (∃ v : mword 64, stval ↦ᵣ v).
  Proof.
    iIntros "Hic Hmenv".
    iDestruct "Hic" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hsepc & Hscause & Hstval)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & %Hmsf)".
    pose proof (proj1 (intr_ms_facts_iff ms) Hmsf) as [_ Hcommon].
    iFrame "Hsepc Hscause Hstval Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf".
    { iExists ms. iFrame "Hms Hhalf". iPureIntro. exact Hcommon. }
    iExists MENVCFG_S. iFrame "Hmenv".
    iPureIntro.
    repeat split; vm_compute; reflexivity.
  Qed.

End IntrDefs.
