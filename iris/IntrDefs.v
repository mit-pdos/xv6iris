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
       the kernel-code capability [sie_cap γ m avail] -- the
       [kv_frame_slots + avail] free-stack slots below sp (sp moves trade
       against [avail] via [sie_cap_push]/[sie_cap_pop]), the TRANSLATION
       SLOT [strans_inv] (Bare-with-stvec ∨ ∃root kernel-PT, consumed
       foldedly via the derived regime [strans_regime]), and the SIE arm
       ('0' = the bare eighth; '1' adds the interrupt invariant + trap
       CSRs); the ambient bundle [sie_cap_gpr] = hart_state ∗ sconf ∗
       sie_cap ∗ gpr_file;
     - the push/pop counting token [intr_count γ n eb] (§6b: eb = the
       saved base-enable state; eb=true payload is the persistent
       [intr_handler_avail]; the trap CSRs ride [trap_csrs_pay] on
       unbalanced specs only);
     - the conversions [intr_config_of_v2] / [v2_of_intr_config] the
       agnostic engines use to enter/exit the absorbing step engine.   *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var ghost_map invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import KptPt.
Require Import MinstretInv InstrBytes.
Require Import RegFile.
Require Import WpGpr WpMmodeLeafBase StackOwn.
Require Import SmodeCore KptTree.
Require Import KMap.   (* kmap_static_claims, extracted from the config bundle *)
Require Import KptGhost.   (* kptN: named in the mask premise *)
Require Import KptShare.   (* tlb_res_pt: the SHARED table's per-hart residue *)
Require Import SRegime.
Require Import MstatusBits WpIntrCore.
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
  WpGprCsrwCommon.have_nom_val (_get_Mstatus_MPP ms) = true /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false.

Lemma intr_ms_facts_roundtrip (elp_v : mword 1) (ms : mword 64) :
  intr_ms_facts ms -> intr_ms_facts (sret_ms5 (trap_ms elp_v ms)).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  split; [exact (roundtrip_SIE_true elp_v ms H1) |].
  split; [exact (roundtrip_MPRV_false elp_v ms) |].
  split; [exact (roundtrip_SXL_eq elp_v ms H3) |].
  split; [exact (roundtrip_MXR_true elp_v ms H4) |].
  split; [exact (roundtrip_TSR_false elp_v ms H5) |].
  split; [rewrite roundtrip_XS; exact H6 |].
  split; [rewrite roundtrip_FS; exact H7 |].
  split; [rewrite roundtrip_VS; exact H8 |].
  split; [rewrite roundtrip_SD; exact H9 |].
  split; [rewrite roundtrip_MPP; exact H10 |].
  exact (roundtrip_TVM_false elp_v ms H11).
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
  WpGprCsrwCommon.have_nom_val (_get_Mstatus_MPP ms) = true /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false.

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

  (* '1'->'0' (csrci): gather 1/2 + 1/8(cap) + 1/8(count) + 1/4(inv),
     come back the same shape at '0'. *)
  Lemma sie_ghost_flip_off (γ : gname) (v1 v2a v2b v3 : mword 1) :
    ghost_var γ (1/2) v1 -∗ ghost_var γ (1/4/2)%Qp v2a -∗ ghost_var γ (1/4/2)%Qp v2b -∗
    ghost_var γ (1/4) v3 ==∗
    ghost_var γ (1/2) ('b"0" : mword 1) ∗ ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) ∗
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) ∗ ghost_var γ (1/4) ('b"0" : mword 1).
  Proof.
    iIntros "H1 H2a H2b H3".
    iCombine "H2a H2b" as "H2".
    iMod (sie_ghost_flip γ v1 v2a v3 ('b"0") with "H1 H2 H3") as "(H1 & H2 & H3)".
    iAssert (⌜(1/4 = 1/4/2 + 1/4/2)%Qp⌝)%I as %Hq.
    { iPureIntro. apply (bool_decide_unpack _). by compute. }
    iEval (rewrite Hq) in "H2".
    iDestruct (ghost_var_split with "H2") as "[H2a H2b]".
    iModIntro. iFrame.
  Qed.

  (* '0'->'1' (csrsi): gather the same four pieces, come back at '1'
     (cap eighth + count eighth + invariant quarter). *)
  Lemma sie_ghost_flip_on (γ : gname) (v1 v2a v2b v3 : mword 1) :
    ghost_var γ (1/2) v1 -∗ ghost_var γ (1/4/2)%Qp v2a -∗ ghost_var γ (1/4/2)%Qp v2b -∗
    ghost_var γ (1/4) v3 ==∗
    ghost_var γ (1/2) ('b"1" : mword 1) ∗ ghost_var γ (1/4/2)%Qp ('b"1" : mword 1) ∗
    ghost_var γ (1/4/2)%Qp ('b"1" : mword 1) ∗ ghost_var γ (1/4) ('b"1" : mword 1).
  Proof.
    iIntros "H1 H2a H2b H3".
    iCombine "H2a H2b" as "H2".
    iMod (sie_ghost_flip γ v1 v2a v3 ('b"1") with "H1 H2 H3") as "(H1 & H2 & H3)".
    iAssert (⌜(1/4 = 1/4/2 + 1/4/2)%Qp⌝)%I as %Hq.
    { iPureIntro. apply (bool_decide_unpack _). by compute. }
    iEval (rewrite Hq) in "H2".
    iDestruct (ghost_var_split with "H2") as "[H2a H2b]".
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
  (* EXACTLY [kv_frame_slots]: an exact carve keeps sp-move re-carving     *)
  (* deterministic (an existential bound would make a downward sp move     *)
  (* unprovable -- the mover could never extract its frame slots from an   *)
  (* unknown-depth pack); clients keep any deeper free stack OUTSIDE the   *)
  (* frame, adjacent below it.  The frame exists because the               *)
  (* handler genuinely USES m-dependent resources beyond the register      *)
  (* file: they can neither sit in the fixed invariant (sp varies per      *)
  (* trap) nor be framed around the handler WP.                            *)
  (*                                                                       *)
  (* [intr_handler_spec] is the handler contract.  Persistent (□), so it   *)
  (* lives freely inside the invariant.  Reading: for any interrupted pc   *)
  (* [pc0] (instruction-aligned, so [ret_pc pc0 = pc0]), any mstatus     *)
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

  (* menvcfg is pinned to [MENVCFG_S] here rather than parameterized: the
     handler contract below is only PROVABLE at that value (its own fetches
     need [cfg_ok], the PT walk needs PBMTE=0 / ADUE), and S-mode never runs
     at any other value, so a parameter would only ever be instantiated at
     [MENVCFG_S] anyway. *)
  (* [intr_frame] carries [tlb_res_pt] -- the KPT arm of the translation
     slot -- rather than the slot itself, and that is deliberate: xv6
     enables interrupts only after kvminithart has installed the kernel
     table, so an interrupt can never be taken under Bare.  (Bare with
     SIE = '1' is also refuted concretely: [bare_inv]'s stvec cell
     contradicts [intr_inv]'s.)  So there is nothing to gain from making
     this slot-generic. *)
  Definition intr_frame (root_ppn : mword 44)
      (m : regfile) : iProp Σ :=
    (menvcfg ↦ᵣ MENVCFG_S ∗
     tlb_res_pt root_ppn ∗
     stack_own (m !!! Regidx csp_rs1) kv_frame_slots)%I.

  (* [intr_frame] depends on [m] only through sp: any register write that
     PRESERVES sp transports the frame to the new map.  (An sp-moving
     instruction instead re-carves its stack explicitly.) *)
  Lemma intr_frame_retarget (root_ppn : mword 44)
      (m m' : regfile) :
    m !!! Regidx csp_rs1 = m' !!! Regidx csp_rs1 ->
    intr_frame root_ppn m -∗ intr_frame root_ppn m'.
  Proof.
    iIntros (Hsp) "(Hmenv & Htlbinv & Hstk)".
    iFrame "Hmenv Htlbinv". rewrite Hsp. iExact "Hstk".
  Qed.

  (* [root_ppn] is UNIVERSAL, per trap: the handler's proof (kernelvec +
     the kerneltrap contract) is uniform in the kernel root, and quantifying
     it here -- rather than parameterizing the spec -- is what lets every
     resource above ([intr_inv]/[intr_restore]/[intr_count]/[sie_arm]) be
     root-free: an interrupted instruction instantiates the spec at whatever
     root its translation slot ([strans_inv]) is currently holding. *)
  Definition intr_handler_spec (handler : mword 64) : iProp Σ :=
    (□ ∀ (root_ppn : mword 44) (elp_v : mword 1) (ms pc0 mie_v mdv0 : mword 64)
         (m : regfile) (Φ : mval -> iProp Σ),
        ⌜ intr_ms_facts ms ⌝ -∗
        ⌜ ret_pc pc0 = pc0 ⌝ -∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝ -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        cur_privilege ↦ᵣ Supervisor -∗
        mstatus ↦ᵣ trap_ms elp_v ms -∗
        mie ↦ᵣ mie_v -∗
        mideleg ↦ᵣ mdv0 -∗
        sepc ↦ᵣ pc0 -∗
        pc_is handler -∗
        gpr_file m -∗
        intr_frame root_ppn m -∗
        ( hart_state ↦ᵣ HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ Supervisor -∗
          mstatus ↦ᵣ sret_ms5 (trap_ms elp_v ms) -∗
          mie ↦ᵣ mie_v -∗
          mideleg ↦ᵣ mdv0 -∗
          (∃ v : mword 64, sepc ↦ᵣ v) -∗
          pc_is pc0 -∗
          gpr_file m -∗
          intr_frame root_ppn m -∗
          WP (Loop : expr riscv_lang) {{ Φ }} ) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I.

  Global Instance intr_handler_spec_persistent handler :
    Persistent (intr_handler_spec handler).
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

  Definition intr_inv_body (γ : gname) (handler : mword 64) : iProp Σ :=
    (∃ b : mword 1,
       ghost_var γ (1/4) b ∗
       stvec ↦ᵣ handler ∗
       □ (⌜ b = ('b"1" : mword 1) ⌝ -∗ intr_handler_spec handler))%I.

  Definition intr_inv (γ : gname) (handler : mword 64) : iProp Σ :=
    (⌜ trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ⌝ ∗
     ⌜ stvec_base handler = handler ⌝ ∗
     inv intrN (intr_inv_body γ handler))%I.

  Global Instance intr_inv_persistent γ handler :
    Persistent (intr_inv γ handler).
  Proof. apply _. Qed.

  Lemma intr_inv_alloc E (γ : gname) (b : mword 1) (handler : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    ghost_var γ (1/4) b -∗
    stvec ↦ᵣ handler -∗
    □ (⌜ b = ('b"1" : mword 1) ⌝ -∗ intr_handler_spec handler) ={E}=∗
    intr_inv γ handler.
  Proof.
    iIntros (Htvd Hsb) "Hq Hstv #Hspec".
    iMod (inv_alloc intrN E (intr_inv_body γ handler)
            with "[Hq Hstv]") as "#Hi".
    { iNext. rewrite /intr_inv_body. iExists b. iFrame "Hq Hstv". iExact "Hspec". }
    iModIntro. iSplit; [done |]. iSplit; [done |]. iExact "Hi".
  Qed.

  (* allocation with interrupts DISABLED needs no handler spec: the guarded
     implication is vacuous. *)
  Lemma intr_inv_alloc_off E (γ : gname) (handler : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    ghost_var γ (1/4) ('b"0" : mword 1) -∗
    stvec ↦ᵣ handler ={E}=∗
    intr_inv γ handler.
  Proof.
    iIntros (Htvd Hsb) "Hq Hstv".
    iApply (intr_inv_alloc E γ _ handler Htvd Hsb with "Hq Hstv").
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
     half pins the live bit).  It owns ALL the free stack below the
     CURRENT sp -- [kv_frame_slots + avail] slots, factored OUT of the
     disjunction and held at BOTH arms (harmless: the ABI never writes
     below sp).  [avail] is the number of slots AVAILABLE to kernel code;
     the other [kv_frame_slots] are reserved for a potential interrupt
     frame.  An sp DECREMENT by k slots consumes k from [avail] (k <=
     avail -- you cannot go below zero) and hands the freed frame region
     [sp', sp) to the client ([sie_cap_push]); an sp INCREMENT feeds the
     frame back and returns k to [avail] ([sie_cap_pop]).  The '1' arm
     carries the remaining extra obligations of interrupts-enabled
     execution: the interrupt invariant (handler existential -- no client
     names the handler) and the trap-scratch CSRs (any trap scribbles
     them, so enabled code cannot pin their values). *)
  (* the kernel-code interrupts-OFF token: between a csrci flip and the
     matching csrsi restore, kernel code holds this eighth; agreement
     with the capability's eighth (or the bundle's tied half) pins the
     arm at '0' wherever the token travels -- pop_off-style code needs
     exactly this to refute its own panic checks.  At the '1' arm the
     capability holds the FULL quarter (no token outstanding). *)
  Definition intr_off_tok (γ : gname) : iProp Σ :=
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1).

  Definition sie_arm (γ : gname) : iProp Σ :=
    (ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) ∨
     (ghost_var γ (1/4/2)%Qp ('b"1" : mword 1) ∗
      (∃ handler : mword 64, intr_inv γ handler) ∗
      (∃ v : mword 64, sepc ↦ᵣ v) ∗
      (∃ v : mword 64, scause ↦ᵣ v) ∗
      (∃ v : mword 64, stval ↦ᵣ v)))%I.

  (* [strans_inv] -- THE TRANSLATION SLOT of the capability: the ambient
     S-mode translation invariant, regime and root hidden.  Clients thread
     the capability and never name either; engines and data/device leaves
     consume the slot FOLDED through the derived regime instance
     [strans_regime] below.
       - BARE (boot): satp Mode = Bare, plus ownership of STVEC -- no trap
         handler is installed yet.  The stvec cell is what refutes
         "interrupts enabled while Bare": the SIE arm's '1' branch carries
         [intr_inv], whose invariant owns [stvec ↦ᵣ handler], and two full
         cells conflict ([reg_pointsto_conflict]).  Installing the handler
         (trapinithart) is only possible after this arm is dissolved.
       - KPT: the kernel table installed at some root.  Says NOTHING about
         stvec: between kvminithart (Bare→Sv39) and trapinithart the cell
         rides client-side (Sv39, no handler, SIE=0 -- a legal state).
     The Bare→KPT move happens once, at kvminithart: dissolve the left arm
     (it owns the satp cell the switch writes), build [tlb_inv_pt], hand the
     stvec cell out to the boot code.
     GHOST-TRACKED ARM: each arm carries half of a [ghost_var strans_name]
     bit ('b"0" = Bare, 'b"1" = kernel PT installed); the bit is the arm
     INDICATOR.  A client that holds the matching half pins the arm
     (agreement -- the "still-Bare receipt"), and the kvminithart switch
     flips it with both halves.  In practice the flip is one-way: the boot
     receipt is the only outside half ever minted, so the arm only ever
     moves Bare→KPT. *)
  (* PER-HART (strans_name is a [CPU -> gname]): this is the AMBIENT hart's
     translation-slot arm bit, exactly as [reg_pointsto] is the ambient
     hart's register. *)
  Definition strans_bit (b : mword 1) : iProp Σ :=
    ghost_var (strans_name cpu_id) (1/2)%Qp b.

  Definition strans_inv : iProp Σ :=
    ((strans_bit ('b"0") ∗ bare_inv ∗ (∃ v : mword 64, stvec ↦ᵣ v))
     ∨ (strans_bit ('b"1") ∗ ∃ root_ppn : mword 44, tlb_res_pt root_ppn))%I.

  Lemma strans_inv_intro (root_ppn : mword 44) :
    strans_bit ('b"1") -∗ tlb_res_pt root_ppn -∗ strans_inv.
  Proof. iIntros "Hbit H". iRight. iFrame "Hbit". iExists root_ppn. iExact "H". Qed.

  Lemma strans_inv_intro_bare (v : mword 64) :
    strans_bit ('b"0") -∗ bare_inv -∗ stvec ↦ᵣ v -∗ strans_inv.
  Proof. iIntros "Hbit Hb Hstv". iLeft. iFrame "Hbit Hb". iExists v. iExact "Hstv". Qed.

  Lemma strans_bit_agree b b' : strans_bit b -∗ strans_bit b' -∗ ⌜b = b'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %He. done.
  Qed.

  (* the receipt pins the arm at Bare and opens it, returning BOTH halves
     (the client's + the arm's) so the switch can flip the bit. *)
  Lemma strans_inv_acc_bare :
    strans_bit ('b"0") -∗ strans_inv -∗
    strans_bit ('b"0") ∗ strans_bit ('b"0") ∗ bare_inv ∗ (∃ v : mword 64, stvec ↦ᵣ v).
  Proof.
    iIntros "Hrcpt [(Hbit & Hb & Hstv) | (Hbit & _)]".
    - iFrame "Hrcpt Hbit Hb Hstv".
    - iDestruct (strans_bit_agree with "Hrcpt Hbit") as %Hbad.
      exfalso. apply (f_equal (@bv_unsigned _)) in Hbad.
      vm_compute in Hbad. discriminate.
  Qed.

  (* both halves -> flip to '1', split back into two halves. *)
  Lemma strans_bit_flip :
    strans_bit ('b"0") -∗ strans_bit ('b"0") ==∗ strans_bit ('b"1") ∗ strans_bit ('b"1").
  Proof.
    iIntros "H1 H2".
    iMod (ghost_var_update_halves ('b"1" : mword 1) with "H1 H2") as "[H1 H2]".
    iModIntro. iFrame.
  Qed.

  (* two FULL cells of the same register cannot coexist -- the Bare∧SIE='1'
     refutation's engine (the dq-generic second cell lets a borrowed
     invariant copy conflict with the slot's full cell). *)
  Lemma reg_pointsto_conflict (r : register) (dq : dfrac)
      (v1 v2 : type_of_register r) :
    r ↦ᵣ v1 -∗ r ↦ᵣ{ dq } v2 -∗ ⌜ False ⌝.
  Proof.
    rewrite /reg_pointsto. iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne.
    iPureIntro. exact (Hne eq_refl).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [strans_regime] -- the slot packaged as a DERIVED [s_regime]: each    *)
  (* field destructs the disjunct and delegates to the proven              *)
  (* [bare_regime] / [kpt_share_regime root] fields, so every engine+leaf  *)
  (* built on the R-generic machinery serves BOTH regimes with the slot    *)
  (* kept folded (no skolem-root open/repack at leaf level).               *)
  (* ------------------------------------------------------------------- *)
  Lemma strans_absorb :
    forall acc va pa (ppn : mword 44) (pc : kperm) σ (E : coPset), s_acc_ok acc ->
      kperm_allows pc acc ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      kadm_ident va ppn ->
      ↑kptN ⊆ E ->
      ⊢ kmap_at (svpn_of va) ppn pc -∗
        reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ strans_inv ={E}=∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ strans_inv.
  Proof.
    intros acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall Hadm HE.
    iIntros "Hat Hri Hgh [(Hbit & Hb & Hstv) | (Hbit & Hk)]".
    - iMod (bare_absorb acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall Hadm HE
              with "Hat Hri Hgh Hb") as (σ') "(%Htr & %Hmdev & %Hsh & %Hpmp & Hri & Hgh & Hb)".
      iModIntro. iExists σ'.
      iSplit; [done |]. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
      iFrame "Hri Hgh". iLeft. iFrame "Hbit Hb Hstv".
    - iDestruct "Hk" as (root_ppn) "Ht".
      iMod (res_absorb root_ppn acc va pa ppn pc σ E Hacc Hallow Hcanon Hconcat Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall I HE
              with "Hat Hri Hgh Ht") as (σ') "(%Htr & %Hmdev & %Hsh & %Hpmp & Hri & Hgh & Ht)".
      iModIntro. iExists σ'.
      iSplit; [done |]. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
      iFrame "Hri Hgh". iRight. iFrame "Hbit". iExists root_ppn. iExact "Ht".
  Qed.

  Lemma strans_transform :
    forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ strans_inv -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝.
  Proof.
    intros acc ea σ Hacc Hcp HSXL Heff Hpml.
    iIntros "Hri [(_ & Hb & _) | (_ & Hk)]".
    - iApply (bare_transform acc ea σ Hacc Hcp HSXL Heff Hpml with "Hri Hb").
    - iDestruct "Hk" as (root_ppn) "Ht".
      iApply (res_transform root_ppn acc ea σ Hacc Hcp HSXL Heff Hpml with "Hri Ht").
  Qed.

  Definition strans_regime : s_regime :=
    SRegime strans_inv kadm_ident (fun _ _ H => H)
            strans_absorb strans_transform.

  (* [sr_inv strans_regime] is definitionally [strans_inv] -- the bridge the
     leaf/engine call sites use without unfolding the record. *)
  Lemma strans_regime_inv : sr_inv strans_regime ⊣⊢ strans_inv.
  Proof. reflexivity. Qed.

  Definition sie_cap (γ : gname) (m : regfile) (avail : nat) : iProp Σ :=
    (stack_own (m !!! Regidx csp_rs1) (kv_frame_slots + avail) ∗
     strans_inv ∗
     sie_arm γ)%I.

  (* [sie_cap_gpr] bundles [sie_cap] with the register file [gpr_file m], so a
     caller threads ONE resource carrying the register file [m] once, instead of
     [sie_cap] and [gpr_file] each re-carrying [m] separately.  Kept a FOLDED
     [Definition] (not a notation): while threaded through a whole-function proof
     the map [m] appears once (halving the per-instruction map unification /
     [iEval rewrite]).  Leaves unfold it to read/update [gpr_file]; the
     [IntoSep]/[FromSep] instances make [iDestruct "H" as "[Hcap Hfile]"] and
     providing [$Hcap $Hfile] just work while it stays folded elsewhere. *)
  (* [sie_cap_gpr] -- THE ambient kernel-execution bundle: everything an
     S-mode whole-function spec threads besides pc / instr / kernel_text.
     hart_state (ACTIVE) + the v2 config [sconf] + the capability [sie_cap]
     (stack carve + translation slot + SIE arm) + the register file
     [gpr_file m].  Kept a FOLDED [Definition] (not a notation): while
     threaded through a whole-function proof the map [m] appears once
     (halving the per-instruction map unification / [iEval rewrite]).
     Leaves unfold it via [sie_cap_gpr_split]/[_join]; NOTE the σ-callback
     of the step engines threads only the hart_state-LESS residue
     ([sconf] + [sie_cap] + [gpr_file]) -- the engine holds hart_state
     across the step and hands it back to the final continuation. *)
  (* BOOT ENTRY: the capability at the Bare regime, from raw boot
     resources -- the free-stack carve, satp still Bare + PMP, the
     UNWRITTEN stvec cell (no trap handler installed), the translation
     slot's Bare arm-bit half [strans_bit ('b"0")] (its twin is kept boot
     side as the still-Bare receipt), and the SIE ghost's kernel-code
     eighth at '0'.  Nothing here requires the
     kernel page table, an interrupt handler, or the trap CSRs: this is
     what makes the whole sconf-tier (memset, the lock/kalloc cone via
     [cpu_own γ 0 false p C], ...) callable during early boot. *)
  Lemma sie_cap_intro_bare (γ : gname) (m : regfile) (avail : nat)
      (v : mword 64) :
    stack_own (m !!! Regidx csp_rs1) (kv_frame_slots + avail) -∗
    strans_bit ('b"0") -∗
    bare_inv -∗
    stvec ↦ᵣ v -∗
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) -∗
    sie_cap γ m avail.
  Proof.
    iIntros "Hstk Hbit Hb Hstv Htok".
    iFrame "Hstk".
    iSplitL "Hbit Hb Hstv".
    { iApply (strans_inv_intro_bare with "Hbit Hb Hstv"). }
    iLeft. iExact "Htok".
  Qed.

  Definition sie_cap_gpr (γ : gname)
      (m : regfile) (avail : nat) : iProp Σ :=
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     sconf γ ∗
     sie_cap γ m avail ∗
     gpr_file m)%I.

  Global Instance sie_cap_gpr_into_sep γ m avail :
    IntoSep (sie_cap_gpr γ m avail)
            (hart_state ↦ᵣ HART_ACTIVE tt)
            (sconf γ ∗ sie_cap γ m avail ∗ gpr_file m).
  Proof. rewrite /IntoSep /sie_cap_gpr. by iIntros "($ & $ & $ & $)". Qed.

  Global Instance sie_cap_gpr_from_sep γ m avail :
    FromSep (sie_cap_gpr γ m avail)
            (hart_state ↦ᵣ HART_ACTIVE tt)
            (sconf γ ∗ sie_cap γ m avail ∗ gpr_file m).
  Proof. rewrite /FromSep /sie_cap_gpr. by iIntros "[$ [$ [$ $]]]". Qed.

  (* Foolproof split/join for the ports (no instance-resolution surprises). *)
  Lemma sie_cap_gpr_split γ m avail :
    sie_cap_gpr γ m avail -∗
    hart_state ↦ᵣ HART_ACTIVE tt ∗ sconf γ ∗ sie_cap γ m avail ∗ gpr_file m.
  Proof. by iIntros "$". Qed.

  Lemma sie_cap_gpr_join γ m avail :
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap γ m avail -∗
    gpr_file m -∗
    sie_cap_gpr γ m avail.
  Proof. iIntros "Hhs Hsc Hcap Hfile". rewrite /sie_cap_gpr. iFrame. Qed.

  (* [hw_config] is persistent and rides at the head of [sconf]; a
     whole-function proof threading [sie_cap_gpr] can pull it out (keeping the
     bundle intact) whenever it needs the ambient static-claims bundle for a
     ghost conversion between instructions (e.g. the walk's kalloc-page ->
     PT-node ↦ₘ→↦ₚ disassembly, which needs [kmap_static_claims]). *)
  Lemma sie_cap_gpr_dup_hw_config γ m avail :
    sie_cap_gpr γ m avail -∗ hw_config ∗ sie_cap_gpr γ m avail.
  Proof.
    iIntros "Hcg".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hsie & Hgpr)".
    iEval (rewrite /sconf) in "Hsc". iDestruct "Hsc" as "(#Hhw & Hrest)".
    iAssert (sconf γ) with "[Hrest]" as "Hsc".
    { rewrite /sconf. iSplitR; [iExact "Hhw" | iExact "Hrest"]. }
    iSplitR; [iExact "Hhw"|].
    rewrite /sie_cap_gpr.
    iSplitL "Hhs"; [iExact "Hhs"|].
    iSplitL "Hsc"; [iExact "Hsc"|].
    iSplitL "Hsie"; [iExact "Hsie" | iExact "Hgpr"].
  Qed.

  (* [kmap_static_claims] at the sconf / sie_cap_gpr altitudes.  It rides in
     [hw_config], which rides at the head of [sconf], which rides inside
     [sie_cap_gpr]; these two extractions are how a DRIVER-level proof reaches
     the ↦ₚ⇄↦ₘ tier bridges (KMap.v) between instructions, without either
     destructing [hw_config]'s conjuncts by position or carrying a private
     copy of the bundle in its own geometry resource.  Both are persistent
     conclusions and CONSUME NOTHING -- the bundle is handed straight back, so
     the call is [iDestruct (… with "Hcg") as "[#Hkm Hcg]"]. *)
  Lemma sconf_kmap_claims γ :
    sconf γ -∗ kmap_static_claims ∗ sconf γ.
  Proof.
    iIntros "Hsc".
    iEval (rewrite /sconf) in "Hsc". iDestruct "Hsc" as "(#Hhw & Hrest)".
    iDestruct (hw_config_kmap_claims with "Hhw") as "#Hkm".
    iSplitR; [iExact "Hkm"|].
    rewrite /sconf. iSplitR; [iExact "Hhw" | iExact "Hrest"].
  Qed.

  Lemma sie_cap_gpr_kmap_claims γ m avail :
    sie_cap_gpr γ m avail -∗ kmap_static_claims ∗ sie_cap_gpr γ m avail.
  Proof.
    iIntros "Hcg".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct (hw_config_kmap_claims with "Hhw") as "#Hkm".
    iSplitR; [iExact "Hkm" | iExact "Hcg"].
  Qed.

  (* the [gpr_file_x0] fact at the bundled altitude: a whole-function proof
     threading [sie_cap_gpr] can read the map's x0 slot and keep the bundle. *)
  Lemma sie_cap_gpr_x0 γ m avail (i : mword 5) :
    uint i = 0 ->
    sie_cap_gpr γ m avail -∗
    ⌜ m !!! Regidx i = zero_reg ⌝ ∗ sie_cap_gpr γ m avail.
  Proof.
    intro Hi. iIntros "Hcg".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 m i Hi with "Hfile") as "[%Hx Hfile]".
    iSplitR; [ iPureIntro; exact Hx | ].
    iApply (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile").
  Qed.

  (* the funnel's accessor: split off the exact reserved carve (the
     [intr_frame] stack conjunct); the deep [avail] slots ride outside. *)
  Lemma sie_cap_acc (γ : gname)
      (m : regfile) (avail : nat) :
    sie_cap γ m avail ⊣⊢
    stack_own (m !!! Regidx csp_rs1) kv_frame_slots ∗
    stack_own (pa_stk (m !!! Regidx csp_rs1) kv_frame_slots) avail ∗
    strans_inv ∗
    sie_arm γ.
  Proof.
    rewrite /sie_cap stack_own_app. iSplit.
    - iIntros "[[Hkv Hdeep] [Htr Harm]]". iFrame.
    - iIntros "(Hkv & Hdeep & Htr & Harm)". iFrame.
  Qed.

  (* [sie_cap] depends on [m] only through sp (same as [intr_frame]). *)
  Lemma sie_cap_retarget (γ : gname)
      (m m' : regfile) (avail : nat) :
    m !!! Regidx csp_rs1 = m' !!! Regidx csp_rs1 ->
    sie_cap γ m avail -∗ sie_cap γ m' avail.
  Proof.
    iIntros (Hsp) "(Hstk & Htr & Harm)". iFrame "Htr Harm". rewrite Hsp. iExact "Hstk".
  Qed.

  (* sp DECREMENT by k slots (sp' = sp - 8k, a prologue's frame
     allocation): k comes off [avail] (the k <= avail premise is the
     can't-go-below-zero check) and the freed frame region [sp', sp) --
     the top k slots, ABOVE the new sp and therefore trap-stable --
     comes OUT for the client. *)
  Lemma sie_cap_push (γ : gname)
      (m m' : regfile) (avail k : nat) :
    (k <= avail)%nat ->
    m' !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) k ->
    sie_cap γ m avail -∗
    sie_cap γ m' (avail - k) ∗ stack_own (m !!! Regidx csp_rs1) k.
  Proof.
    iIntros (Hk Hsp') "(Hstk & Htr & Harm)". iFrame "Htr Harm".
    replace (kv_frame_slots + avail)%nat
      with (k + (kv_frame_slots + (avail - k)))%nat by lia.
    iDestruct (stack_own_app with "Hstk") as "[Htop Hrest]".
    iFrame "Htop". rewrite Hsp'. iExact "Hrest".
  Qed.

  (* sp INCREMENT by k slots (sp' = sp + 8k, an epilogue's frame
     release): the function's frame [sp, sp') = the top k slots at sp'
     is fed back IN and k returns to [avail]. *)
  Lemma sie_cap_pop (γ : gname)
      (m m' : regfile) (avail k : nat) :
    m !!! Regidx csp_rs1 = pa_stk (m' !!! Regidx csp_rs1) k ->
    stack_own (m' !!! Regidx csp_rs1) k -∗
    sie_cap γ m avail -∗
    sie_cap γ m' (avail + k).
  Proof.
    iIntros (Hsp) "Hframe (Hstk & Htr & Harm)". iFrame "Htr Harm".
    replace (kv_frame_slots + (avail + k))%nat
      with (k + (kv_frame_slots + avail))%nat by lia.
    iApply stack_own_app. iFrame "Hframe". rewrite -Hsp. iExact "Hstk".
  Qed.

  (* custody transfer at the DEEP end (no sp move): absorb k adjacent
     slots below the owned region into [avail]... *)
  Lemma sie_cap_grow (γ : gname)
      (m : regfile) (avail k : nat) :
    stack_own (pa_stk (m !!! Regidx csp_rs1) (kv_frame_slots + avail)) k -∗
    sie_cap γ m avail -∗
    sie_cap γ m (avail + k).
  Proof.
    iIntros "Hdeep (Hstk & Htr & Harm)". iFrame "Htr Harm".
    rewrite Nat.add_assoc. iApply stack_own_app. iFrame "Hstk Hdeep".
  Qed.

  (* ... and release the k deepest slots back out. *)
  Lemma sie_cap_shrink (γ : gname)
      (m : regfile) (avail k : nat) :
    (k <= avail)%nat ->
    sie_cap γ m avail -∗
    sie_cap γ m (avail - k) ∗
    stack_own (pa_stk (m !!! Regidx csp_rs1) (kv_frame_slots + (avail - k))) k.
  Proof.
    iIntros (Hk) "(Hstk & Htr & Harm)". iFrame "Htr Harm".
    replace (kv_frame_slots + avail)%nat
      with ((kv_frame_slots + (avail - k)) + k)%nat by lia.
    iDestruct (stack_own_app with "Hstk") as "[Htop Hdeep]".
    iFrame "Htop Hdeep".
  Qed.

  (* =================================================================== *)
  (* §6b THE PUSH/POP COUNTING TOKEN.  [intr_count γ n eb] is the       *)
  (* per-cpu interrupt-disable bookkeeping token push_off/pop_off manage *)
  (* (n mirrors the noff nesting depth; [eb] is xv6's saved intena --    *)
  (* the BASE enable state recorded at the 0→1 push).  It carries the    *)
  (* COMPLEMENTARY EIGHTH of the SIE ghost at every level -- the other   *)
  (* half of the capability's eighth at either arm -- so arm knowledge   *)
  (* is pure ghost agreement wherever the token travels: n > 0 implies   *)
  (* interrupts are disabled ('0'-eighth), and at n = 0 the eighth       *)
  (* mirrors the LIVE bit, which is [eb] itself.  The RESTORE payload    *)
  (* (invariant copy + later'd handler spec + the trap CSRs) is carried  *)
  (* ONLY at n ≥ 1 with eb = true -- exactly what the final pop's        *)
  (* re-enable flip consumes.  At eb = false the token is JUST the       *)
  (* eighth: push_off/pop_off from an interrupts-disabled base state are *)
  (* no-ops on SIE and need no handler, no stvec, no trap CSRs -- the    *)
  (* early-boot discipline ([intr_count γ 0 false] = [intr_off_tok γ]).  *)
  (* =================================================================== *)
  Definition sie_bit (eb : bool) : mword 1 := if eb then 'b"1" else 'b"0".

  (* the persistent half of the old restore payload: an interrupt handler
     is installed and its contract is available.  Persistent (intr_inv and
     the □ handler spec both are), hence duplicable -- a crossing retune
     (sched's intena restore) can drop or re-duplicate it freely. *)
  Definition intr_handler_avail (γ : gname) : iProp Σ :=
    (∃ handler : mword 64,
        intr_inv γ handler ∗
        ▷ intr_handler_spec handler)%I.

  Global Instance intr_handler_avail_persistent γ :
    Persistent (intr_handler_avail γ).
  Proof. rewrite /intr_handler_avail. apply _. Qed.

  (* the LINEAR half: the trap-scratch CSRs.  They live in the SIE arm's
     '1' branch while interrupts are enabled, and are threaded EXPLICITLY
     at SIE=0 -- they ride on the UNBALANCED specs only (bare push_off /
     pop_off, acquire's post / release's pre, the flip leaves), via
     [trap_csrs_pay]: owed exactly at a level-0 boundary with an enabled
     base.  Push/pop-balanced functions never mention them. *)
  Definition trap_csrs : iProp Σ :=
    ((∃ v : mword 64, sepc ↦ᵣ v) ∗
     (∃ v : mword 64, scause ↦ᵣ v) ∗
     (∃ v : mword 64, stval ↦ᵣ v))%I.

  Definition trap_csrs_pay (n : nat) (eb : bool) : iProp Σ :=
    (match n with
     | O => if eb then trap_csrs else emp
     | S _ => emp
     end)%I.

  Definition intr_restore (γ : gname) : iProp Σ :=
    (intr_handler_avail γ ∗ trap_csrs)%I.

  Definition intr_count (γ : gname) (n : nat) (eb : bool) : iProp Σ :=
    match n with
    | O => ghost_var γ (1/4/2)%Qp (sie_bit eb)
    | S _ => (ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) ∗
              (if eb then intr_handler_avail γ else emp))%I
    end.

  (* crossing retunes (the sched intena restore): the payload is
     persistent-or-empty, so both directions are loss-free. *)
  Lemma intr_count_retune_off (γ : gname) (n : nat) (eb : bool) :
    intr_count γ (S n) eb -∗ intr_count γ (S n) false.
  Proof. iIntros "[Htok _]". iFrame. Qed.

  Lemma intr_count_retune_on (γ : gname) (n : nat) (eb : bool) :
    intr_handler_avail γ -∗
    intr_count γ (S n) eb -∗ intr_count γ (S n) true.
  Proof. iIntros "#Ha [Htok _]". iFrame "Htok Ha". Qed.

  (* enter the boot discipline: base state OFF, nothing but the eighth *)
  Lemma intr_count_init_off (γ : gname) :
    intr_off_tok γ -∗ intr_count γ 0 false.
  Proof. iIntros "H". iExact "H". Qed.

  (* n > 0 implies interrupts disabled: any fraction of '0' pins the arm *)
  Lemma intr_count_pos_off (γ : gname) (n : nat) (eb : bool) :
    intr_count γ (S n) eb -∗
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) ∗ (if eb then intr_handler_avail γ else emp).
  Proof. iIntros "[Htok Hres]". iFrame. Qed.

  (* the '0'-arm PUSH (csrci with interrupts already off): the level just
     increments -- at n = 0 ghost agreement with the capability's '0'
     eighth pins eb = false, so the payload owed at level 1 is [emp]. *)
  Lemma intr_count_push_off (γ : gname) (n : nat) (eb : bool) :
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) -∗
    intr_count γ n eb -∗
    ⌜ n = 0%nat -> eb = false ⌝ ∗
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) ∗ intr_count γ (S n) eb.
  Proof.
    iIntros "Hcap Hcnt". destruct n.
    - iDestruct (ghost_var_agree with "Hcap Hcnt") as %Hb.
      destruct eb.
      + exfalso. apply (f_equal (@bv_unsigned _)) in Hb.
        vm_compute in Hb. discriminate.
      + iSplitR; [done |]. iFrame "Hcap". iFrame "Hcnt".
    - iDestruct "Hcnt" as "[Htok Hres]".
      iSplitR; [iPureIntro; discriminate |]. iFrame.
  Qed.

  (* the '0'-arm POP at eb = false (never re-enables): level decrement *)
  Lemma intr_count_pop_off (γ : gname) (n : nat) :
    intr_count γ (S n) false -∗ intr_count γ n false.
  Proof.
    iIntros "[Htok _]". destruct n; [iExact "Htok" | iFrame; done].
  Qed.

  (* an interior POP (n+1 ≥ 2 → n+1 ≥ 1): payload carried through *)
  Lemma intr_count_dec (γ : gname) (n : nat) (eb : bool) :
    intr_count γ (S (S n)) eb -∗ intr_count γ (S n) eb.
  Proof. iIntros "[Htok Hres]". iFrame. Qed.

  (* at the '1' arm (cap-eighth-'1'), [intr_count n eb] forces n = 0 and
     eb = true, and yields the two '1' eighths -- the S-case and the
     n = 0 eb = false case both carry a '0' eighth, refuted by agreement. *)
  Lemma intr_count_get_on (γ : gname) (n : nat) (eb : bool) :
    ghost_var γ (1/4/2)%Qp ('b"1" : mword 1) -∗
    intr_count γ n eb -∗
    ⌜ n = 0%nat /\ eb = true ⌝ ∗
    ghost_var γ (1/4/2)%Qp ('b"1" : mword 1) ∗
    ghost_var γ (1/4/2)%Qp ('b"1" : mword 1).
  Proof.
    iIntros "Hcap Hcnt". destruct n.
    - destruct eb.
      + iFrame. done.
      + iDestruct (ghost_var_agree with "Hcap Hcnt") as %Hbad.
        exfalso. apply (f_equal (@bv_unsigned _)) in Hbad. vm_compute in Hbad. discriminate.
    - iDestruct "Hcnt" as "[Hc0 _]".
      iDestruct (ghost_var_agree with "Hcap Hc0") as %Hbad.
      exfalso. apply (f_equal (@bv_unsigned _)) in Hbad. vm_compute in Hbad. discriminate.
  Qed.

  (* rebuild [intr_restore] from its pieces, re-introducing the later on
     the persistent handler spec (needed after a branch's [iNext] strips
     it). *)
  Lemma intr_restore_intro (γ : gname) (h : mword 64) :
    intr_inv γ h -∗
    intr_handler_spec h -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    intr_restore γ.
  Proof.
    iIntros "#Hi #Hs Hsep Hsca Hstv". iFrame "Hsep Hsca Hstv".
    iExists h. iFrame "Hi". iNext. iExact "Hs".
  Qed.

  (* pack a count eighth-'0' + the persistent avail into level S n *)
  Lemma intr_count_pack_S_on (γ : gname) (n : nat) :
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) -∗ intr_handler_avail γ -∗
    intr_count γ (S n) true.
  Proof. iIntros "Hc0 #Ha". iFrame "Hc0 Ha". Qed.

  (* ... and the disabled-base level S n needs only the eighth *)
  Lemma intr_count_pack_S_off (γ : gname) (n : nat) :
    ghost_var γ (1/4/2)%Qp ('b"0" : mword 1) -∗
    intr_count γ (S n) false.
  Proof. iIntros "Hc0". iFrame. Qed.

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
    ghost_var γ (1/4/2)%Qp ('b"1" : mword 1) -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    intr_config γ ∗ ghost_var γ (1/4/2)%Qp ('b"1" : mword 1) ∗ menvcfg ↦ᵣ MENVCFG_S.
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
