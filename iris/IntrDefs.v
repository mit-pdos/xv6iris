(* IntrDefs.v -- the interrupt-stack DEFINITIONS, at leaf altitude.

   Holds everything a leaf-level S-mode WP file needs to STATE
   interrupt-aware specs, split out of WpIntrInv.v (which keeps the
   step ENGINES and imports high-altitude machinery no leaf may pull):

     - the SIE ghost choreography (1/2 live-bit tie + 1/4 kernel-code
       token + 1/4 invariant quarter): [sie_ghost_alloc]/[sie_ghost_flip].
       The NAME is CANONICAL per hart -- [sie_gname] = [sie_name cpu_id]
       (RiscvPtsto.v) -- which is why nothing in the sconf tier below takes
       a ghost argument: the ambient hart determines the ghost;
     - the interrupts-ENABLED regime: [intr_ms_facts], [intr_config],
       [intr_frame] (+[intr_frame_retarget]), [intr_handler_spec],
       [intr_inv] (+allocation);
     - the SIE-AGNOSTIC v2 bundle (the smode_config successor):
       [sconf_ms_facts] (the SIE-free common fact set), [sconf]
       (SIE unpinned, ghost half tied to the live bit, menvcfg bundled),
       the kernel-code capability [sie_cap m avail] -- the
       [kv_frame_slots + avail] free-stack slots below sp (sp moves trade
       against [avail] via [sie_cap_push]/[sie_cap_pop]), the TRANSLATION
       SLOT [strans_inv] (Bare-with-stvec ∨ ∃root kernel-PT, consumed
       foldedly via the derived regime [strans_regime]), and the SIE arm
       INDEX [sie_arm b] (b = false: the bare eighth; b = true adds the
       interrupt invariant + trap CSRs); the ambient bundle
       [sie_cap_gpr m avail b] = hart_state ∗ sconf ∗ sie_cap ∗
       gpr_file (tp_pin m);
     - the push/pop counting token [intr_count n eb] (§6b: eb = the
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
Require Import RegFile HartTp.
Require Import WpGpr WpMmodeLeafBase StackOwn.
Require Import SmodeCore.
Require Import KMap.   (* kmap_static_claims, extracted from the config bundle *)
Require Import KptGhost.   (* kptN: named in the mask premise *)
Require Import KptShare.   (* tlb_res_pt: the SHARED table's per-hart residue *)
Require Import SRegime.
Require Import ProcGeom.   (* a_cpu_noff / a_cpu_int / a_cpu_proc: the enabled arm owns them *)
Require Import MstatusBits WpIntrCore.
Require Import MstatusFacts.
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

(* THE ONE-WAY BRIDGE from the M-mode side's fact bundle.
   [MstatusFacts.mstatus_kernel_facts] (which [InstrBytes.mmode_config]
   carries, so the M-mode boot contract's post exposes it) is
   [sconf_ms_facts] plus the SIE pin, with MPP stated down there as the BIT
   DISEQUALITY -- [have_nom_val] lives in WpGprCsrwCommon, above
   MstatusFacts.  This is the only step that needs proving, and it is the
   reason [sconf_ms_facts] keeps its verbatim statement (it is inside [sconf];
   changing it would change [sconf]). *)
Lemma sconf_ms_facts_of_kernel (ms : mword 64) :
  mstatus_kernel_facts ms -> sconf_ms_facts ms.
Proof.
  intros (_ & HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  unfold sconf_ms_facts. split_and!; try assumption.
  (* MPP: the reserved encoding 'b"10" is the ONLY one [have_nom_val] rejects *)
  unfold WpGprCsrwCommon.have_nom_val.
  destruct (eq_vec (_get_Mstatus_MPP ms) ('b"00")); [reflexivity |].
  destruct (eq_vec (_get_Mstatus_MPP ms) ('b"01")); [reflexivity |].
  rewrite HMPP. reflexivity.
Qed.

Lemma intr_ms_facts_iff (ms : mword 64) :
  intr_ms_facts ms
  <-> (eq_vec (_get_Mstatus_SIE ms) ('b"1") = true /\ sconf_ms_facts ms).
Proof. unfold intr_ms_facts, sconf_ms_facts. tauto. Qed.

Section IntrDefs.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* =================================================================== *)
  (* §2 The SIE ghost choreography: 1/2 (live-bit tie) + 1/4 (kernel-code *)
  (* token) + 1/4 (invariant).                                            *)
  (* =================================================================== *)

  (* THE SIE GHOST NAME OF THE AMBIENT HART.  Canonical, exactly like
     [reg_name] / [strans_name]: mstatus.SIE is a per-hart register, so which
     value the choreography is at is a per-hart fact and the hart DETERMINES
     the ghost.  That is what lets every resource below ([sconf], [sie_cap],
     [sie_cap_gpr], [sie_arm], [intr_inv], [intr_count], [intr_off_tok],
     [intr_handler_avail], [intr_restore], [intr_config]) be stated with no
     ghost argument at all, and what lets a step's continuation (WpNext.v)
     rebind the ghost by rebinding [CID] alone.

     (Written without an explicit [`{GEN : GenId} `{CID : CpuId}] binder because the section
     already fixes one and Rocq refuses to rebind a section variable's name;
     the section closes it over exactly [riscvGS] and [CpuId] regardless.) *)
  Definition sie_gname : gname := sie_name cpu_id.

  (* mstatus.SPP's ghost MIRROR (RiscvPtsto.era_spp_name), canonical per hart
     for the same reason [sie_gname] is.  TWO halves: one TIED inside [sconf]
     to [_get_Mstatus_SPP ms], one travelling with [trap_csrs] -- existential
     while the enabled arm holds it (a trap rewrites SPP whenever it likes)
     and PINNED while interrupts-off code does.  [spp_agree] is what turns
     the held half into a fact about the live bit, and it is what lets a trap
     handler still know SPP = 1 several instructions after entry, which the
     instruction funnel's [exists ms] would otherwise have destroyed. *)
  Definition spp_gname : gname := spp_name cpu_id.
  Definition spie_gname : gname := spie_name cpu_id.

  (* THE TWO BITS AN [sret] READS, as one resource.  SPP decides the
     privilege it returns to and SPIE the SIE it restores; both are written
     by the trap, neither is touched by an SIE flip, and no consumer ever
     wants one without the other -- so they are held together and the whole
     tier sees ONE conjunct rather than two. *)
  Definition sret_bits (spp spie : mword 1) : iProp Σ :=
    (ghost_var spp_gname (1/2) spp ∗ ghost_var spie_gname (1/2) spie)%I.

  Lemma sret_bits_agree (a b a' b' : mword 1) :
    sret_bits a b -∗ sret_bits a' b' -∗ ⌜ a = a' /\ b = b' ⌝.
  Proof.
    iIntros "[H1 H2] [H1' H2']".
    iDestruct (ghost_var_agree with "H1 H1'") as %->.
    iDestruct (ghost_var_agree with "H2 H2'") as %->.
    done.
  Qed.

  Lemma sret_bits_update (a b a' b' wa wb : mword 1) :
    sret_bits a b -∗ sret_bits a' b' ==∗ sret_bits wa wb ∗ sret_bits wa wb.
  Proof.
    iIntros "[H1 H2] [H1' H2']".
    iMod (ghost_var_update_2 wa with "H1 H1'") as "[Ha Ha']";
      [ rewrite Qp.half_half // |].
    iMod (ghost_var_update_2 wb with "H2 H2'") as "[Hb Hb']";
      [ rewrite Qp.half_half // |].
    iModIntro. iFrame "Ha Hb Ha' Hb'".
  Qed.

  (* the tie, as it sits inside [sconf] *)
  Definition sret_tie (ms : mword 64) : iProp Σ :=
    sret_bits (_get_Mstatus_SPP ms) (_get_Mstatus_SPIE ms).

  (* MOVING THE TIE ACROSS AN mstatus CHANGE THAT LEAVES BOTH BITS ALONE --
     which is every SIE flip (the mask is bit 1; SPP is bit 8 and SPIE bit
     5).  This is why push_off / pop_off need no ghost movement at all: the
     tie is merely re-expressed at the new mstatus. *)
  Lemma sret_tie_congr (ms ms' : mword 64) :
    _get_Mstatus_SPP ms' = _get_Mstatus_SPP ms ->
    _get_Mstatus_SPIE ms' = _get_Mstatus_SPIE ms ->
    sret_tie ms -∗ sret_tie ms'.
  Proof. intros H1 H2. rewrite /sret_tie H1 H2. iIntros "$". Qed.

  (* [sie_ghost_alloc] / [sie_ghost_flip]* stay GHOST-GENERIC: they are
     statements about a raw [ghost_var], with no sconf-tier resource in
     sight, and one of their consumers (the per-trap tie ProofKernelvec.v
     mints) is deliberately NOT the canonical name.  Callers in the sconf
     tier instantiate them at [sie_gname]. *)
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
  Definition intr_config : iProp Σ :=
    (hw_config ∗ minstret_inv ∗
     cur_privilege ↦ᵣ Supervisor ∗
     (∃ ms : mword 64,
        mstatus ↦ᵣ ms ∗
        ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms) ∗
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
  (* LEAST [kv_frame_slots] (78 slots: kernelvec's 32-slot c.addi16sp     *)
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
  (* THE RESERVED CARVE MUST COVER THE WHOLE TRAP PATH, not just
     kernelvec's own frame.  A trap taken at an interrupts-enabled
     instruction runs kernelvec (32 slots = 256 bytes, its c.addi16sp frame)
     AND everything kernelvec calls, which is kerneltrap and its cone
     ([SpecKerneltrap.kerneltrap_stack] = 46: its own 6-slot frame plus
     devintr's 40).  So 32 + 46 = 78.

     The literal is written out because [kerneltrap_stack] lives ABOVE this
     file; [SpecKerneltrap.kt_carve_fits] ties the two together so the pair
     cannot drift silently -- growing kerneltrap's cone without growing this
     would otherwise still compile and only fail deep inside the handler
     proof. *)
  Definition kv_frame_slots : nat := 78.

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

  Definition intr_inv_body (handler : mword 64) : iProp Σ :=
    (∃ b : mword 1,
       ghost_var sie_gname (1/4) b ∗
       stvec ↦ᵣ handler ∗
       □ (⌜ b = ('b"1" : mword 1) ⌝ -∗ intr_handler_spec handler))%I.

  Definition intr_inv (handler : mword 64) : iProp Σ :=
    (⌜ trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ⌝ ∗
     ⌜ stvec_base handler = handler ⌝ ∗
     inv intrN (intr_inv_body handler))%I.

  Global Instance intr_inv_persistent handler :
    Persistent (intr_inv handler).
  Proof. apply _. Qed.

  Lemma intr_inv_alloc E (b : mword 1) (handler : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    ghost_var sie_gname (1/4) b -∗
    stvec ↦ᵣ handler -∗
    □ (⌜ b = ('b"1" : mword 1) ⌝ -∗ intr_handler_spec handler) ={E}=∗
    intr_inv handler.
  Proof.
    iIntros (Htvd Hsb) "Hq Hstv #Hspec".
    iMod (inv_alloc intrN E (intr_inv_body handler)
            with "[Hq Hstv]") as "#Hi".
    { iNext. rewrite /intr_inv_body. iExists b. iFrame "Hq Hstv". iExact "Hspec". }
    iModIntro. iSplit; [done |]. iSplit; [done |]. iExact "Hi".
  Qed.

  (* allocation with interrupts DISABLED needs no handler spec: the guarded
     implication is vacuous. *)
  Lemma intr_inv_alloc_off E (handler : mword 64) :
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    stvec ↦ᵣ handler ={E}=∗
    intr_inv handler.
  Proof.
    iIntros (Htvd Hsb) "Hq Hstv".
    iApply (intr_inv_alloc E _ handler Htvd Hsb with "Hq Hstv").
    iModIntro. iIntros (Hb).
    exfalso. apply (f_equal (@bv_unsigned _)) in Hb.
    vm_compute in Hb. discriminate.
  Qed.

  (* =================================================================== *)
  (* §6 THE V2 BUNDLE [sconf]: the SIE-AGNOSTIC smode_config successor.   *)
  (* [intr_config] + the menvcfg conjunct, SIE unpinned; full ownership   *)
  (* (the trap writes its cells); the trap CSRs are NOT bundled (they     *)
  (* ride in [sie_cap]'s [b = true] arm -- SIE=0 code owns sepc itself).  *)
  (* [hart_state] travels beside the bundle, as in [intr_config].         *)
  (* =================================================================== *)
  Definition sconf : iProp Σ :=
    (hw_config ∗ minstret_inv ∗
     cur_privilege ↦ᵣ Supervisor ∗
     (∃ ms : mword 64,
        mstatus ↦ᵣ ms ∗
        ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms) ∗
        sret_tie ms ∗
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

  (* ------------------------------------------------------------------- *)
  (* §6' THE mstatus-EXPOSING FLAVOUR [sconf_at].                          *)
  (*                                                                       *)
  (* [sconf] hides mstatus behind an existential, which is right for       *)
  (* almost everything -- no leaf and no whole-function spec cares WHICH   *)
  (* mstatus it is running at, only that the fact set holds.  Two places   *)
  (* do care: a leaf that WRITES sstatus (what the instruction did to      *)
  (* SPP/SPIE is its entire content), and the trap handler's own contract, *)
  (* because kernelvec's [sret] reads exactly those two fields.            *)
  (* [sconf_at ms] is [sconf] with the mstatus cell pulled OUT at a named  *)
  (* value.                                                                *)
  (*                                                                       *)
  (* IT IS AN ACCESSOR, NOT A SECOND COPY OF [sconf]'s BODY: the payload   *)
  (* is the mstatus triple plus a wand that swallows any REPLACEMENT       *)
  (* triple and gives [sconf] back.  So there is nothing to keep in sync   *)
  (* when [sconf] grows a conjunct, and [sconf] itself is untouched --     *)
  (* every existing destructuring of it still works.                       *)
  (*                                                                       *)
  (* USE IT ONLY AT BOUNDARIES.  A function threads plain [sie_cap_gpr]    *)
  (* through its body and switches to the [_at] flavour on the OUTPUT side *)
  (* of the one instruction (or the one contract) whose mstatus effect is  *)
  (* the point.  Giving every leaf an [_at] twin would be the leaf x       *)
  (* mstatus cross-product the guiding principle exists to prevent.        *)
  (* ------------------------------------------------------------------- *)
  Definition sconf_msown (ms : mword 64) : iProp Σ :=
    (mstatus ↦ᵣ ms ∗
     ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms) ∗
     sret_tie ms ∗
     ⌜ sconf_ms_facts ms ⌝)%I.

  Definition sconf_at (ms : mword 64) : iProp Σ :=
    (sconf_msown ms ∗ (∀ ms' : mword 64, sconf_msown ms' -∗ sconf))%I.

  Lemma sconf_at_close (ms : mword 64) : sconf_at ms -∗ sconf.
  Proof. iIntros "[Hown Hcl]". iApply ("Hcl" with "Hown"). Qed.

  Lemma sconf_at_open : sconf -∗ ∃ ms : mword 64, sconf_at ms.
  Proof.
    iIntros "(#Hhw & #Hminv & Hpriv & Hmsx & Hmie & Hmenv)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Hspp & %Hmsf)".
    iExists ms. iSplitL "Hms Hhalf Hspp".
    { iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
    iIntros (ms') "(Hms' & Hhalf' & Hspp' & %Hmsf')".
    iFrame "Hhw Hminv Hpriv Hmie Hmenv".
    iExists ms'. iFrame "Hms' Hhalf' Hspp'". iPureIntro. exact Hmsf'.
  Qed.

  (* the mstatus facts are readable straight off the flavour, without
     closing it -- what a caller reasoning about SPP/SPIE needs. *)
  Lemma sconf_at_facts (ms : mword 64) :
    sconf_at ms -∗ ⌜ sconf_ms_facts ms ⌝.
  Proof. iIntros "[(_ & _ & _ & %H) _]". iPureIntro. exact H. Qed.

  (* READING THE TWO sret BITS OFF THE BUNDLE.  A holder of the travelling
     half turns it into a fact about the LIVE mstatus by agreement with the
     tie -- which is the whole point of the mirror: it is what survives the
     instruction funnel's [exists ms], and so it is how a trap handler
     entered from S-mode still knows SPP = 1 several instructions later. *)
  Lemma sconf_at_sret (ms : mword 64) (a b : mword 1) :
    sconf_at ms -∗ sret_bits a b -∗
    ⌜ _get_Mstatus_SPP ms = a /\ _get_Mstatus_SPIE ms = b ⌝.
  Proof.
    iIntros "[(_ & _ & Htie & _) _] Hc".
    iDestruct (sret_bits_agree with "Htie Hc") as %[-> ->]. done.
  Qed.

  (* [sie_cap] -- the kernel-code capability that EXPOSES the SIE mode as
     its index [b], backed by the ghost QUARTER's value (agreement with
     [sconf]'s tied half pins the live bit).  It owns ALL the free stack
     below the CURRENT sp -- [kv_frame_slots + avail] slots, factored OUT
     of the arm and held at BOTH indices (harmless: the ABI never writes
     below sp).  [avail] is the number of slots AVAILABLE to kernel code;
     the other [kv_frame_slots] are reserved for a potential interrupt
     frame.  An sp DECREMENT by k slots consumes k from [avail] (k <=
     avail -- you cannot go below zero) and hands the freed frame region
     [sp', sp) to the client ([sie_cap_push]); an sp INCREMENT feeds the
     frame back and returns k to [avail] ([sie_cap_pop]).  The [b = true]
     arm carries the remaining extra obligations of interrupts-enabled
     execution: the interrupt invariant (handler existential -- no client
     names the handler) and the trap-scratch CSRs (any trap scribbles
     them, so enabled code cannot pin their values). *)
  (* the kernel-code interrupts-OFF token: between a csrci flip and the
     matching csrsi restore, kernel code holds this eighth; agreement
     with the capability's eighth (or the bundle's tied half) pins the
     arm at '0' wherever the token travels -- pop_off-style code needs
     exactly this to refute its own panic checks.  At the [b = true] arm
     the capability holds the FULL quarter (no token outstanding). *)
  Definition intr_off_tok : iProp Σ :=
    ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1).

  (* =================================================================== *)
  (* §6a THE PUSH/POP COUNTING TOKEN and THE PER-CPU CELLS.               *)
  (* Hoisted ABOVE [sie_arm] because the interrupts-ENABLED arm OWNS      *)
  (* them (see [sie_arm]): while SIE = 1 a trap can migrate the thread,   *)
  (* so the resuming hart's [cpus[cid]] cells have to be re-delivered by  *)
  (* the crossing, and the only vehicle that crosses is the arm.          *)
  (* =================================================================== *)

  Definition sie_bit (eb : bool) : mword 1 := if eb then 'b"1" else 'b"0".

  (* the persistent half of the old restore payload: an interrupt handler
     is installed and its contract is available.  Persistent (intr_inv and
     the □ handler spec both are), hence duplicable -- a crossing retune
     (sched's intena restore) can drop or re-duplicate it freely. *)
  Definition intr_handler_avail : iProp Σ :=
    (∃ handler : mword 64,
        intr_inv handler ∗
        ▷ intr_handler_spec handler)%I.

  Global Instance intr_handler_avail_persistent :
    Persistent (intr_handler_avail).
  Proof. rewrite /intr_handler_avail. apply _. Qed.

  (* the LINEAR half: the trap-scratch CSRs.  They live in the SIE arm's
     '1' branch while interrupts are enabled, and are threaded EXPLICITLY
     at SIE=0 -- they ride on the UNBALANCED specs only (bare push_off /
     pop_off, acquire's post / release's pre, the flip leaves), via
     [trap_csrs_pay]: owed exactly at a level-0 boundary with an enabled
     base.  Push/pop-balanced functions never mention them. *)
  (* WHAT A TRAP SCRIBBLES.  sepc / scause / stval are whole registers, so
     they move as cells; mstatus.SPP is a BIT inside a register [sconf] has
     to keep, so its travelling half moves as the ghost mirror [sret_bits].
     All four belong to the same discipline and travel together: existential
     inside [sie_arm true] (a trap can rewrite any of them between two
     instructions), pinned in the hands of interrupts-off code. *)
  Definition trap_csrs : iProp Σ :=
    ((∃ v : mword 64, sepc ↦ᵣ v) ∗
     (∃ v : mword 64, scause ↦ᵣ v) ∗
     (∃ v : mword 64, stval ↦ᵣ v) ∗
     (∃ a b : mword 1, sret_bits a b))%I.

  Definition trap_csrs_pay (n : nat) (eb : bool) : iProp Σ :=
    (match n with
     | O => if eb then trap_csrs else emp
     | S _ => emp
     end)%I.

  (* THE COMPLEMENT OF [trap_csrs_pay] AT LEVEL 0: what a caller has to
     BRING because the bundle does not already own it.  At level 0 the arm
     index and the saved base coincide, so at [eb = true] the enabled arm
     owns the trap CSRs and the caller brings nothing, while at
     [eb = false] nothing in the bundle owns them and the caller brings the
     whole set.

     A function that PARKS needs the set unconditionally -- sched's crossing
     takes it and re-delivers the RESUMING hart's, because sepc/scause/stval
     are PER-HART registers and framing them around a migration would be
     unsound.  So yield takes [trap_csrs_pay 0 eb] out of its own push_off
     and [trap_csrs_ext eb] from its caller, and exactly one of the two is
     [emp].  The [eb = false] case is kerneltrap's: the trap cleared SIE, so
     the pushing acquire records intena = 0 and hands out nothing, and the
     handler is holding the trap CSRs itself because the TRAP gave them to
     it. *)
  Definition trap_csrs_ext (eb : bool) : iProp Σ :=
    (if eb then emp else trap_csrs)%I.

  Lemma trap_csrs_ext_split (eb : bool) :
    trap_csrs_pay 0 eb ∗ trap_csrs_ext eb ⊣⊢ trap_csrs.
  Proof.
    destruct eb; rewrite /trap_csrs_pay /trap_csrs_ext.
    - by rewrite bi.sep_emp.
    - by rewrite bi.emp_sep.
  Qed.

  Definition intr_restore : iProp Σ :=
    (intr_handler_avail ∗ trap_csrs)%I.

  Definition intr_count (n : nat) (eb : bool) : iProp Σ :=
    match n with
    | O => ghost_var sie_gname (1/4/2)%Qp (sie_bit eb)
    | S _ => (ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) ∗
              (if eb then intr_handler_avail else emp))%I
    end.

  (* ------------------------------------------------------------------- *)
  (* THE PER-CPU CELLS of [cpus[cid]] a running kernel thread owns: the   *)
  (* push/pop level cell [noff], the saved base-enable [intena], and the  *)
  (* current-process field [proc].  Split out of [CpuOwn.cpu_own] and     *)
  (* moved down here for the same reason as §6a.                          *)
  (*                                                                      *)
  (* [proc] is held at HALF ([ProcGeom.cpu_proc_half]): the other half is *)
  (* permanently owned by [SchedCtx.scheds_inv]'s slot for this hart, so  *)
  (* that the global parked-scheduler protocol can read "the proc running *)
  (* on hart h is p".  Keeping the FULL cell here would make that         *)
  (* protocol's take-out move vacuous -- see                              *)
  (* [SchedCtx.cpu_own_full_is_vacuous].  The two [c->proc] STORES the    *)
  (* scheduler makes therefore have to reassemble the cell out of the     *)
  (* invariant, which is what [SchedCtx.scheds_dispatch] /                *)
  (* [scheds_reclaim] are.                                                *)
  (* ------------------------------------------------------------------- *)
  Definition noff_val (n : nat) : mword 32 := mword_of_int (Z.of_nat n).
  Definition intena_val (eb : bool) : mword 32 :=
    if eb then mword_of_int 1 else mword_of_int 0.

  Definition cpu_cells (n : nat) (eb : bool) (p : mword 64) : iProp Σ :=
    (⌜ (Z.of_nat n < 2 ^ 31)%Z ⌝ ∗
     a_cpu_noff cid_word ↦₄ noff_val n ∗
     (match n with
      | O => (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv)%I
      | S _ => a_cpu_int cid_word ↦₄ intena_val eb
      end) ∗
     cpu_proc_half cpu_id p)%I.

  (* the cells PLUS the counting token -- the whole per-cpu bundle minus
     the caller's context-slot payload [C] (which is an ordinary caller
     FRAME: an opaque [iProp Σ] crosses a migration for free, and every
     live instantiation that can reach the enabled arm is [emp]).  This is
     exactly what push_off / pop_off move between the arm and the code. *)
  Definition cpu_hart (n : nat) (eb : bool) (p : mword 64) : iProp Σ :=
    (cpu_cells n eb p ∗ intr_count n eb)%I.

  (* THE SIE ARM IS AN INDEX, NOT AN INTERNAL DISJUNCTION.  It used to be
     [A ∨ B], which made every leaf SIE-agnostic at the price of hiding the
     one fact a leaf statement now has to expose: whether an interrupt can be
     taken at this instruction, and therefore whether execution can resume on
     a DIFFERENT hart.  The old form is recoverable as [∃ b, sie_arm b], and
     a leaf's case split on the disjunction becomes a case split on [b], so
     nothing inside the leaves changed shape.  See [wp_next].

     THE ENABLED ARM ALSO OWNS THIS HART'S [cpus[cid]] BOOKKEEPING
     ([cpu_hart 0 true p], §6a).  Rationale: with SIE = 1 a trap can be
     taken at any instruction and the thread can resume on a DIFFERENT
     hart, so every hart-indexed resource a caller holds across such an
     instruction must ride the crossing -- and the only thing that crosses
     is what a leaf's [wp_next] re-delivers, i.e. [sie_cap_gpr].  The
     level and the base-enable come for FREE: the arm's own eighth is at
     '1' and [intr_count]'s complementary eighth is at [sie_bit eb] (n=0)
     or '0' (n>0), so ghost agreement pins [n = 0] and [eb = true]
     ([intr_count_get_on]) -- the arm needs neither as a parameter.  What
     it does need is [p], the value of [cpus[cid].proc]: that value is a
     THREAD invariant (the dispatcher sets the resuming hart's field to
     the same proc), so it is threaded like the register map [m] and no
     transport or agreement ghost is required.  The context-slot payload
     [C] does NOT ride here: it is an opaque [iProp Σ], hence an ordinary
     caller frame that crosses for free.  This matches the C: a thread
     touches c->noff / c->intena / c->proc only with interrupts disabled,
     which is precisely what push_off exists for. *)
  Definition sie_arm (b : bool) (p : mword 64) : iProp Σ :=
    (if b
     then (ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) ∗
           (∃ handler : mword 64, intr_inv handler) ∗
           (∃ v : mword 64, sepc ↦ᵣ v) ∗
           (∃ v : mword 64, scause ↦ᵣ v) ∗
           (∃ v : mword 64, stval ↦ᵣ v) ∗
           (∃ a b : mword 1, sret_bits a b) ∗
           cpu_hart 0 true p)
     else ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1))%I.

  (* THE ARM INDEX IS THE LIVE BIT, at either index and without a case split
     at the call site.  [sconf]'s tied half and the arm's eighth are
     fragments of the same ghost, so agreement reads the live SIE off the
     index -- which is what every leaf that has to know whether interrupts
     are on (the sstatus reads, the sstatus RESTORE) actually needs. *)
  Lemma sie_arm_half_agree (b : bool) (px : mword 64) (ms : mword 64) :
    ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms) -∗
    sie_arm b px -∗
    ⌜ _get_Mstatus_SIE ms = sie_bit b ⌝.
  Proof.
    iIntros "Hhalf Harm". rewrite /sie_arm. destruct b.
    - iDestruct "Harm" as "(Hq & _ & _ & _ & _ & _)".
      iDestruct (ghost_var_agree with "Hhalf Hq") as %H. iPureIntro. exact H.
    - iDestruct (ghost_var_agree with "Hhalf Harm") as %H. iPureIntro. exact H.
  Qed.

  Lemma sie_arm_of_ex (p : mword 64) :
    (∃ b : bool, sie_arm b p) ⊣⊢
    (ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) ∨
     (ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) ∗
      (∃ handler : mword 64, intr_inv handler) ∗
      (∃ v : mword 64, sepc ↦ᵣ v) ∗
      (∃ v : mword 64, scause ↦ᵣ v) ∗
      (∃ v : mword 64, stval ↦ᵣ v) ∗
      (∃ a b : mword 1, sret_bits a b) ∗
      cpu_hart 0 true p)).
  Proof.
    iSplit.
    - iIntros "H". iDestruct "H" as ([]) "H"; [ iRight | iLeft ]; iExact "H".
    - iIntros "[H|H]"; [ iExists false | iExists true ]; iExact "H".
  Qed.

  (* THE TWO MOVES push_off / pop_off make.  The enabled arm's per-cpu
     bookkeeping comes OUT (push_off, right after its [csrci] has already
     flipped the live bit -- the eighth it hands back is the one the flip
     produced) and goes back IN (pop_off's final [csrsi]).  Everything
     else in the arm is untouched, so these are pure re-associations. *)
  Lemma sie_arm_on_out (p : mword 64) :
    sie_arm true p -∗
    ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) ∗
    (∃ handler : mword 64, intr_inv handler) ∗
    trap_csrs ∗
    cpu_hart 0 true p.
  Proof. iIntros "(Hbit & Hinv & Hsep & Hsca & Hstv & Hspp & Hcpu)". iFrame. Qed.

  Lemma sie_arm_on_in (p : mword 64) :
    ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) -∗
    (∃ handler : mword 64, intr_inv handler) -∗
    trap_csrs -∗
    cpu_hart 0 true p -∗
    sie_arm true p.
  Proof. iIntros "Hbit Hinv (Hsep & Hsca & Hstv & Hspp) Hcpu". iFrame. Qed.

  (* [strans_inv] -- THE TRANSLATION SLOT of the capability: the ambient
     S-mode translation invariant, regime and root hidden.  Clients thread
     the capability and never name either; engines and data/device leaves
     consume the slot FOLDED through the derived regime instance
     [strans_regime] below.
       - BARE (boot): satp Mode = Bare, plus ownership of STVEC -- no trap
         handler is installed yet.  PER-HART and holding nothing global, so
         EVERY hart can be in this arm at once (claude-notes/projects/
         bare-inv-generic.md): what makes claim honoring provable here is
         the regime's [sr_adm] premise ("the claim is the identity"), which
         each consumer discharges from its own [↦ₘ]/[↦ₓ] datum.  The stvec cell is what refutes
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

  Lemma strans_tmode :
    forall (σ : mstate),
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      ⊢ reg_interp σ.(sregs) -∗ strans_inv -∗
        ⌜ exists md, exec (translationMode Supervisor) σ = Some (md, σ) ⌝.
  Proof.
    intros σ HSXL.
    iIntros "Hri [(_ & Hb & _) | (_ & Hk)]".
    - iApply (bare_tmode σ HSXL with "Hri Hb").
    - iDestruct "Hk" as (root_ppn) "Ht".
      iApply (res_tmode root_ppn σ HSXL with "Hri Ht").
  Qed.

  Definition strans_regime : s_regime :=
    SRegime strans_inv kadm_ident (fun _ _ H => H)
            strans_absorb strans_transform strans_tmode.

  (* [sr_inv strans_regime] is definitionally [strans_inv] -- the bridge the
     leaf/engine call sites use without unfolding the record. *)
  Lemma strans_regime_inv : sr_inv strans_regime ⊣⊢ strans_inv.
  Proof. reflexivity. Qed.

  Definition sie_cap (m : regfile) (avail : nat) (b : bool)
      (p : mword 64) : iProp Σ :=
    (stack_own (m !!! Regidx csp_rs1) (kv_frame_slots + avail) ∗
     strans_inv ∗
     sie_arm b p)%I.

  (* THE WRITE-SIDE PREMISE of every gpr-writing leaf.  Replaces the old
     [rd <> csp_rs1] IN PLACE (same premise slot, so no call site changes
     arity): [sie_cap] is keyed on sp, and the register file pins tp
     (HartTp.v), so neither may be a generic write's destination.  Discharge
     with [ltac:(rdok)] wherever [ltac:(vm_compute; discriminate)] used to sit. *)
  Definition rd_ok (rd : mword 5) : Prop :=
    rd <> csp_rs1 /\ Regidx rd <> Regidx Rtp.

  Lemma rd_ok_sp (rd : mword 5) : rd_ok rd -> rd <> csp_rs1.
  Proof. by intros [H _]. Qed.
  Lemma rd_ok_tp (rd : mword 5) : rd_ok rd -> Regidx rd <> Regidx Rtp.
  Proof. by intros [_ H]. Qed.

  (* THE sp BRIDGE.  The bundle owns [gpr_file (tp_pin m)] while [sie_cap] and
     [intr_frame] are keyed on [m !!! Regidx csp_rs1], and a step engine takes
     ONE map -- so every funnel that feeds an engine has to reconcile the two.
     Hoisted here (rather than re-derived per file with a hand-rolled [Regidx]
     disequality) because it is the single most repeated seam in the port. *)
  Lemma tp_pin_sp (m : regfile) : tp_pin m !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof.
    apply (rget_ne m csp_rs1).
    intro He. injection He as He2. vm_compute in He2. congruence.
  Qed.

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
     eighth at '0' -- i.e. the capability comes out at the [b = false]
     arm, interrupts off.  Nothing here requires the
     kernel page table, an interrupt handler, or the trap CSRs: this is
     what makes the whole sconf-tier (memset, the lock/kalloc cone via
     [cpu_own γ 0 false p C], ...) callable during early boot. *)
  Lemma sie_cap_intro_bare (m : regfile) (avail : nat)
      (v : mword 64) {p : mword 64} :
    stack_own (m !!! Regidx csp_rs1) (kv_frame_slots + avail) -∗
    strans_bit ('b"0") -∗
    bare_inv -∗
    stvec ↦ᵣ v -∗
    ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) -∗
    sie_cap m avail false p.
  Proof.
    iIntros "Hstk Hbit Hb Hstv Htok".
    iFrame "Hstk".
    iSplitL "Hbit Hb Hstv".
    { iApply (strans_inv_intro_bare with "Hbit Hb Hstv"). }
    rewrite /sie_arm. iExact "Htok".
  Qed.

  (* NOTE [gpr_file (tp_pin m)]: the bundle owns this hart's registers, whose
     [tp] is [cid_word_of cpu_id] -- the map's [tp] slot is ignored (HartTp.v).
     That is what lets a migration hand back the SAME map [m] at the new hart
     instead of an [rf_upd m Rtp …] layer per instruction. *)
  Definition sie_cap_gpr
      (m : regfile) (avail : nat) (b : bool) (p : mword 64) : iProp Σ :=
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     sconf ∗
     sie_cap m avail b p ∗
     gpr_file (tp_pin m))%I.

  (* the [sie_cap_gpr] flavour with mstatus exposed -- see [sconf_at].
     Boundary use only; [sie_cap_gpr_at_close] is how it rejoins the
     ordinary threading. *)
  Definition sie_cap_gpr_at (ms : mword 64)
      (m : regfile) (avail : nat) (b : bool) (p : mword 64) : iProp Σ :=
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     sconf_at ms ∗
     sie_cap m avail b p ∗
     gpr_file (tp_pin m))%I.

  Lemma sie_cap_gpr_at_close (ms : mword 64) m avail b p :
    sie_cap_gpr_at ms m avail b p -∗ sie_cap_gpr m avail b p.
  Proof.
    iIntros "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (sconf_at_close with "Hsc") as "Hsc".
    rewrite /sie_cap_gpr. iFrame "Hhs Hsc Hcap Hfile".
  Qed.

  Lemma sie_cap_gpr_at_open m avail b p :
    sie_cap_gpr m avail b p -∗ ∃ ms : mword 64, sie_cap_gpr_at ms m avail b p.
  Proof.
    iIntros "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (sconf_at_open with "Hsc") as (ms) "Hsc".
    iExists ms. iFrame "Hhs Hsc Hcap Hfile".
  Qed.

  Global Instance sie_cap_gpr_into_sep m avail b p :
    IntoSep (sie_cap_gpr m avail b p)
            (hart_state ↦ᵣ HART_ACTIVE tt)
            (sconf ∗ sie_cap m avail b p ∗ gpr_file (tp_pin m)).
  Proof. rewrite /IntoSep /sie_cap_gpr. by iIntros "($ & $ & $ & $)". Qed.

  Global Instance sie_cap_gpr_from_sep m avail b p :
    FromSep (sie_cap_gpr m avail b p)
            (hart_state ↦ᵣ HART_ACTIVE tt)
            (sconf ∗ sie_cap m avail b p ∗ gpr_file (tp_pin m)).
  Proof. rewrite /FromSep /sie_cap_gpr. by iIntros "[$ [$ [$ $]]]". Qed.

  (* Foolproof split/join for the ports (no instance-resolution surprises). *)
  Lemma sie_cap_gpr_split m avail b p :
    sie_cap_gpr m avail b p -∗
    hart_state ↦ᵣ HART_ACTIVE tt ∗ sconf ∗ sie_cap m avail b p ∗
    gpr_file (tp_pin m).
  Proof. by iIntros "$". Qed.

  Lemma sie_cap_gpr_join m avail b p :
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf -∗
    sie_cap m avail b p -∗
    gpr_file (tp_pin m) -∗
    sie_cap_gpr m avail b p.
  Proof. iIntros "Hhs Hsc Hcap Hfile". rewrite /sie_cap_gpr. iFrame. Qed.

  (* [hw_config] is persistent and rides at the head of [sconf]; a
     whole-function proof threading [sie_cap_gpr] can pull it out (keeping the
     bundle intact) whenever it needs the ambient static-claims bundle for a
     ghost conversion between instructions (e.g. the walk's kalloc-page ->
     PT-node ↦ₘ→↦ₚ disassembly, which needs [kmap_static_claims]). *)
  Lemma sie_cap_gpr_dup_hw_config m avail b p :
    sie_cap_gpr m avail b p -∗ hw_config ∗ sie_cap_gpr m avail b p.
  Proof.
    iIntros "Hcg".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hsie & Hgpr)".
    iEval (rewrite /sconf) in "Hsc". iDestruct "Hsc" as "(#Hhw & Hrest)".
    iAssert (sconf) with "[Hrest]" as "Hsc".
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
  Lemma sconf_kmap_claims :
    sconf -∗ kmap_static_claims ∗ sconf.
  Proof.
    iIntros "Hsc".
    iEval (rewrite /sconf) in "Hsc". iDestruct "Hsc" as "(#Hhw & Hrest)".
    iDestruct (hw_config_kmap_claims with "Hhw") as "#Hkm".
    iSplitR; [iExact "Hkm"|].
    rewrite /sconf. iSplitR; [iExact "Hhw" | iExact "Hrest"].
  Qed.

  Lemma sie_cap_gpr_kmap_claims m avail b p :
    sie_cap_gpr m avail b p -∗ kmap_static_claims ∗ sie_cap_gpr m avail b p.
  Proof.
    iIntros "Hcg".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
    iDestruct (hw_config_kmap_claims with "Hhw") as "#Hkm".
    iSplitR; [iExact "Hkm" | iExact "Hcg"].
  Qed.

  (* the [gpr_file_x0] fact at the bundled altitude: a whole-function proof
     threading [sie_cap_gpr] can read the map's x0 slot and keep the bundle. *)
  Lemma sie_cap_gpr_x0 m avail b p (i : mword 5) :
    uint i = 0 ->
    sie_cap_gpr m avail b p -∗
    ⌜ m !!! Regidx i = zero_reg ⌝ ∗ sie_cap_gpr m avail b p.
  Proof.
    intro Hi. iIntros "Hcg".
    (* x0 is not tp, so the pinned file's x0 slot IS the map's. *)
    assert (Hne : Regidx i <> Regidx Rtp).
    { intro He. injection He as He2. rewrite He2 in Hi.
      vm_compute in Hi. discriminate. }
    pose proof (rget_ne m i Hne) as Hr. unfold rget in Hr.
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 (tp_pin m) i Hi with "Hfile") as "[%Hx Hfile]".
    rewrite Hr in Hx.
    iSplitR; [ iPureIntro; exact Hx | ].
    iApply (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile").
  Qed.

  (* the funnel's accessor: split off the exact reserved carve (the
     [intr_frame] stack conjunct); the deep [avail] slots ride outside. *)
  Lemma sie_cap_acc
      (m : regfile) (avail : nat) (b : bool) (p : mword 64) :
    sie_cap m avail b p ⊣⊢
    stack_own (m !!! Regidx csp_rs1) kv_frame_slots ∗
    stack_own (pa_stk (m !!! Regidx csp_rs1) kv_frame_slots) avail ∗
    strans_inv ∗
    sie_arm b p.
  Proof.
    rewrite /sie_cap stack_own_app. iSplit.
    - iIntros "[[Hkv Hdeep] [Htr Harm]]". iFrame.
    - iIntros "(Hkv & Hdeep & Htr & Harm)". iFrame.
  Qed.

  (* [sie_cap] depends on [m] only through sp (same as [intr_frame]). *)
  Lemma sie_cap_retarget
      (m m' : regfile) (avail : nat) (b : bool) {p : mword 64} :
    m !!! Regidx csp_rs1 = m' !!! Regidx csp_rs1 ->
    sie_cap m avail b p -∗ sie_cap m' avail b p.
  Proof.
    iIntros (Hsp) "(Hstk & Htr & Harm)". iFrame "Htr Harm". rewrite Hsp. iExact "Hstk".
  Qed.

  (* sp DECREMENT by k slots (sp' = sp - 8k, a prologue's frame
     allocation): k comes off [avail] (the k <= avail premise is the
     can't-go-below-zero check) and the freed frame region [sp', sp) --
     the top k slots, ABOVE the new sp and therefore trap-stable --
     comes OUT for the client. *)
  Lemma sie_cap_push
      (m m' : regfile) (avail k : nat) (b : bool) {p : mword 64} :
    (k <= avail)%nat ->
    m' !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) k ->
    sie_cap m avail b p -∗
    sie_cap m' (avail - k) b p ∗ stack_own (m !!! Regidx csp_rs1) k.
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
  Lemma sie_cap_pop
      (m m' : regfile) (avail k : nat) (b : bool) {p : mword 64} :
    m !!! Regidx csp_rs1 = pa_stk (m' !!! Regidx csp_rs1) k ->
    stack_own (m' !!! Regidx csp_rs1) k -∗
    sie_cap m avail b p -∗
    sie_cap m' (avail + k) b p.
  Proof.
    iIntros (Hsp) "Hframe (Hstk & Htr & Harm)". iFrame "Htr Harm".
    replace (kv_frame_slots + (avail + k))%nat
      with (k + (kv_frame_slots + avail))%nat by lia.
    iApply stack_own_app. iFrame "Hframe". rewrite -Hsp. iExact "Hstk".
  Qed.

  (* custody transfer at the DEEP end (no sp move): absorb k adjacent
     slots below the owned region into [avail]... *)
  Lemma sie_cap_grow
      (m : regfile) (avail k : nat) (b : bool) {p : mword 64} :
    stack_own (pa_stk (m !!! Regidx csp_rs1) (kv_frame_slots + avail)) k -∗
    sie_cap m avail b p -∗
    sie_cap m (avail + k) b p.
  Proof.
    iIntros "Hdeep (Hstk & Htr & Harm)". iFrame "Htr Harm".
    rewrite Nat.add_assoc. iApply stack_own_app. iFrame "Hstk Hdeep".
  Qed.

  (* ... and release the k deepest slots back out. *)
  Lemma sie_cap_shrink
      (m : regfile) (avail k : nat) (b : bool) {p : mword 64} :
    (k <= avail)%nat ->
    sie_cap m avail b p -∗
    sie_cap m (avail - k) b p ∗
    stack_own (pa_stk (m !!! Regidx csp_rs1) (kv_frame_slots + (avail - k))) k.
  Proof.
    iIntros (Hk) "(Hstk & Htr & Harm)". iFrame "Htr Harm".
    replace (kv_frame_slots + avail)%nat
      with ((kv_frame_slots + (avail - k)) + k)%nat by lia.
    iDestruct (stack_own_app with "Hstk") as "[Htop Hdeep]".
    iFrame "Htop Hdeep".
  Qed.

  (* =================================================================== *)
  (* §6b THE PUSH/POP COUNTING TOKEN.  [intr_count n eb] is the       *)
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
  (* early-boot discipline ([intr_count 0 false] = [intr_off_tok]).  *)
  (* =================================================================== *)
  (* crossing retunes (the sched intena restore): the payload is
     persistent-or-empty, so both directions are loss-free. *)
  Lemma intr_count_retune_off (n : nat) (eb : bool) :
    intr_count (S n) eb -∗ intr_count (S n) false.
  Proof. iIntros "[Htok _]". iFrame. Qed.

  Lemma intr_count_retune_on (n : nat) (eb : bool) :
    intr_handler_avail -∗
    intr_count (S n) eb -∗ intr_count (S n) true.
  Proof. iIntros "#Ha [Htok _]". iFrame "Htok Ha". Qed.

  (* enter the boot discipline: base state OFF, nothing but the eighth *)
  Lemma intr_count_init_off :
    intr_off_tok -∗ intr_count 0 false.
  Proof. iIntros "H". iExact "H". Qed.

  (* n > 0 implies interrupts disabled: any fraction of '0' pins the arm *)
  Lemma intr_count_pos_off (n : nat) (eb : bool) :
    intr_count (S n) eb -∗
    ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) ∗ (if eb then intr_handler_avail else emp).
  Proof. iIntros "[Htok Hres]". iFrame. Qed.

  (* the '0'-arm PUSH (csrci with interrupts already off): the level just
     increments -- at n = 0 ghost agreement with the capability's '0'
     eighth pins eb = false, so the payload owed at level 1 is [emp]. *)
  Lemma intr_count_push_off (n : nat) (eb : bool) :
    ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) -∗
    intr_count n eb -∗
    ⌜ n = 0%nat -> eb = false ⌝ ∗
    ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) ∗ intr_count (S n) eb.
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
  Lemma intr_count_pop_off (n : nat) :
    intr_count (S n) false -∗ intr_count n false.
  Proof.
    iIntros "[Htok _]". destruct n; [iExact "Htok" | iFrame; done].
  Qed.

  (* an interior POP (n+1 ≥ 2 → n+1 ≥ 1): payload carried through *)
  Lemma intr_count_dec (n : nat) (eb : bool) :
    intr_count (S (S n)) eb -∗ intr_count (S n) eb.
  Proof. iIntros "[Htok Hres]". iFrame. Qed.

  (* at the '1' arm (cap-eighth-'1'), [intr_count n eb] forces n = 0 and
     eb = true, and yields the two '1' eighths -- the S-case and the
     n = 0 eb = false case both carry a '0' eighth, refuted by agreement. *)
  Lemma intr_count_get_on (n : nat) (eb : bool) :
    ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) -∗
    intr_count n eb -∗
    ⌜ n = 0%nat /\ eb = true ⌝ ∗
    ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) ∗
    ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1).
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
  Lemma intr_restore_intro (h : mword 64) :
    intr_inv h -∗
    intr_handler_spec h -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    (∃ a b : mword 1, sret_bits a b) -∗
    intr_restore.
  Proof.
    iIntros "#Hi #Hs Hsep Hsca Hstv Hspp".
    iFrame "Hsep Hsca Hstv Hspp".
    iExists h. iFrame "Hi". iNext. iExact "Hs".
  Qed.

  (* pack a count eighth-'0' + the persistent avail into level S n *)
  Lemma intr_count_pack_S_on (n : nat) :
    ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) -∗ intr_handler_avail -∗
    intr_count (S n) true.
  Proof. iIntros "Hc0 #Ha". iFrame "Hc0 Ha". Qed.

  (* ... and the disabled-base level S n needs only the eighth *)
  Lemma intr_count_pack_S_off (n : nat) :
    ghost_var sie_gname (1/4/2)%Qp ('b"0" : mword 1) -∗
    intr_count (S n) false.
  Proof. iIntros "Hc0". iFrame. Qed.

  (* =================================================================== *)
  (* §7 The v2 <-> interrupts-enabled conversions: the agnostic engines'  *)
  (* '1' arm assembles [intr_config]/[intr_frame] for the absorbing step  *)
  (* engine and disassembles them back around its σ-callback.  Ghost      *)
  (* agreement (tied half vs the quarter-'1' token) pins SIE=1; the       *)
  (* quarter and the menvcfg cell come back out (the absorbing engine     *)
  (* threads neither).                                                    *)
  (* =================================================================== *)
  Lemma intr_config_of_v2 :
    sconf -∗
    ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    intr_config ∗ ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1) ∗ menvcfg ↦ᵣ MENVCFG_S ∗
    (* THE SPP TIE COMES OUT.  [intr_config] carries no SPP tie, and it must
       not: a trap sets SPP := 1 and the matching sret sets it back to 0, so
       across the engine the bit MOVES.  The funnel holds this half and the
       travelling one (out of [sie_arm true]) and re-ties both to the final
       mstatus when it converts back -- which is the whole reason the enabled
       arm holds SPP at an EXISTENTIAL value. *)
    (∃ a b : mword 1, sret_bits a b).
  Proof.
    iIntros "Hsc Hq Hsepc Hscause Hstval".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Hspp & %Hmsf)".
    iDestruct (ghost_var_agree with "Hhalf Hq") as %Hb1.
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & _ & _ & _ & _ & %Hval)".
    subst menvcfg0.
    iFrame "Hq Hmenv Hhw Hminv Hpriv Hmiex Hsepc Hscause Hstval".
    iSplitR "Hspp"; [| iExists (_get_Mstatus_SPP ms), (_get_Mstatus_SPIE ms); iExact "Hspp" ].
    iExists ms. iFrame "Hms Hhalf".
    iPureIntro. apply intr_ms_facts_iff. split; [ | exact Hmsf ].
    rewrite Hb1. vm_compute. reflexivity.
  Qed.

  Lemma v2_of_intr_config (vta vtb vca vcb : mword 1) :
    intr_config -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    (* BOTH SPP halves, at ARBITRARY values -- the tie one this conversion's
       dual handed out, and the travelling one from [sie_arm true].  A trap
       and its sret move SPP, so neither is about the mstatus coming back;
       holding both is what lets this re-tie them to it.  That is also why
       the enabled arm holds SPP existentially: while interrupts are on, its
       value is not the client's to know. *)
    sret_bits vta vtb -∗ sret_bits vca vcb ==∗
    sconf ∗
    (∃ a b : mword 1, sret_bits a b) ∗
    (∃ v : mword 64, sepc ↦ᵣ v) ∗
    (∃ v : mword 64, scause ↦ᵣ v) ∗
    (∃ v : mword 64, stval ↦ᵣ v).
  Proof.
    iIntros "Hic Hmenv Ht Hc".
    iDestruct "Hic" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hsepc & Hscause & Hstval)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & %Hmsf)".
    pose proof (proj1 (intr_ms_facts_iff ms) Hmsf) as [_ Hcommon].
    iMod (sret_bits_update vta vtb vca vcb
            (_get_Mstatus_SPP ms) (_get_Mstatus_SPIE ms) with "Ht Hc") as "[Ht Hc]".
    iModIntro.
    iSplitR "Hc Hsepc Hscause Hstval".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf Ht".
      { iExists ms. iFrame "Hms Hhalf Ht". iPureIntro. exact Hcommon. }
      iExists MENVCFG_S. iFrame "Hmenv".
      iPureIntro. repeat split; vm_compute; reflexivity. }
    iFrame "Hsepc Hscause Hstval".
    iExists (_get_Mstatus_SPP ms), (_get_Mstatus_SPIE ms). iExact "Hc".
  Qed.

End IntrDefs.

(* ===================================================================== *)
(* TRANSPORTING [trap_csrs_ext] ACROSS A MIGRATION -- the [cpu_own]       *)
(* transport's twin, and needed for the same reason.  sepc/scause/stval   *)
(* are PER-HART registers, so [trap_csrs_ext] is hart-indexed and cannot  *)
(* simply be framed around a step that can move the hart.  It transports  *)
(* anyway, by the two halves of what such a step gives you: at            *)
(* [eb = true] the proposition is [emp], which mentions no hart at all;   *)
(* at [eb = false] no trap can have been taken, so [wp_next]'s            *)
(* conditional equality pins the hart.  Chain the per-step equalities     *)
(* with [wp_next_chain] and apply this once, exactly as for [cpu_own].    *)
(* ===================================================================== *)
Lemma trap_csrs_ext_transport `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId}
    (CID0 CID1 : CpuId) (eb : bool) (p : mword 64) :
  (eb = false \/ p = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
  trap_csrs_ext (CID := CID0) eb -∗ trap_csrs_ext (CID := CID1) eb.
Proof.
  intros Heq. destruct eb.
  - (* [emp]: no hart in the term *) rewrite /trap_csrs_ext. iIntros "$".
  - rewrite (_ : CID1 = CID0); [ iIntros "$" | exact (Heq (or_introl eq_refl)) ].
Qed.

(* ==================================================================== *)
(* THE PORT'S STANDARD TACTICS (outside the section: an [Ltac] defined   *)
(* inside one is discharged over its variables and unusable downstream). *)
(* ==================================================================== *)

(* Re-fold a leaf's own gpr write under the tp pin, turning the engine's
   output [<[Regidx rd := v]> (tp_pin m)] into the [tp_pin (<[Regidx rd := v]>
   m)] the bundle wants.  Every gpr-WRITING leaf needs exactly this one line;
   [Hrdtp] is [rd_ok_tp] applied to the leaf's [rd_ok] premise. *)
Ltac tp_refold Hrdtp H := iEval (rewrite (tp_pin_upd _ _ _ Hrdtp)) in H.

(* THE call-site discharge for [rd_ok], replacing the [ltac:(vm_compute;
   discriminate)] that used to sit in the [rd <> csp_rs1] premise slot.
   Written name-free: an Ltac body cannot reference a hypothesis by literal
   name (durable-notes).  The two conjuncts need DIFFERENT scripts --
   [rd <> csp_rs1] is an [mword 5] disequality [vm_compute; discriminate]
   settles, while [Regidx rd <> Regidx Rtp] has to go through [Regidx]'s
   injectivity first. *)
Ltac rdok :=
  split;
  [ vm_compute; discriminate
  | let H1 := fresh in let H2 := fresh in
    intro H1; injection H1 as H2; vm_compute in H2; congruence ].

(* THE READ-SIDE TWIN of [rdok]: rewrite [rget m k] to [m !!! Regidx k] at a
   non-tp index, discharging the [Regidx] injectivity side condition with the
   same script.  A consumer needs this wherever an existing register-value fact
   has to meet a leaf's [rget]-spelled premise; without it the script gets
   copy-pasted into every proof file. *)
Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

(* CAUTION, ORDER MATTERS in an endgame peel loop: a [rewrite Htp] for the tp
   slot must come BEFORE [rgne].  Otherwise [rewrite rget_ne] instantiates at
   the tp occurrence, its side condition fails, [first] falls through, and the
   whole [repeat] stops early leaving the goal un-normalised:
     repeat first [ rewrite upd_eq
                  | rewrite upd_ne; [| vm_compute; discriminate]
                  | rewrite Htp
                  | rgne ]. *)

(* The two projections are wanted TOGETHER in essentially every gpr-writing
   leaf -- [Hrdsp] for the sp [congruence]s the old proofs already do, [Hrdtp]
   to feed [tp_refold] -- so pose both at once.  The single most repeated pair
   in the sweep. *)
Ltac rdok_split Hrdok :=
  pose proof (rd_ok_sp _ Hrdok);
  pose proof (rd_ok_tp _ Hrdok).
