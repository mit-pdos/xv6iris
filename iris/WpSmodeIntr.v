(* WpSmodeIntr.v -- the SIE=1 instruction step engine and the SIE-AGNOSTIC
   funnel over [sconf] + [sie_cap], at the PER-NODE layer.

   LAYER 1 [wp_instr_s_intr] IS [WpIntrInv.wp_exec_step_intr] VERBATIM.  The
   engine already speaks the bundle, so the wrapper is one [exact]; it is kept
   as a name because [wp_instr_s_sconf]'s '1' arm and 68 call sites use it.

   LAYER 2 [wp_instr_s_sconf]: THE SIE-AGNOSTIC FUNNEL.  It cases on the
   capability's SIE INDEX [b] -- an index, not an internal disjunction, so a
   caller can say which arm it is in -- and BOTH arms present the SAME
   leaf-facing obligation [sconf_step_obl], which is why everything above this
   file is SIE-blind:
     - [b = true]: [wp_instr_s_intr].  The sret-target premise is DERIVED from
       [instr_bytes]' 2-alignment ([update_bit0_zero_of_aligned2]), so no call
       site carries it;
     - [b = false]: [wp_instr_s_sconf_off_clock], which inlines the cycle
       ([HartSwp.swp_loop] + [HartMCycle.swp_tick_wrap_ex]) so that the
       callback's outermost [▷] is stripped BEFORE the body is supplied,
       runs [WpIntrInv.swp_run_hart_active_instr_S_res] at the regime
       residue, and refutes the dispatch from the capability's SIE ghost.
       See the note at the lemma for why it is not
       [SmodeCorePt.wp_instr_s_config_regime] instead.

   WHAT THE PER-NODE PORT CHANGED IN THE SHAPES, and why:
     - the leaf hands the bundles BACK inside the [swp (execute i)]
       postcondition, and its continuation is a separate rider-indexed
       premise.  The wrapper needs [sconf]'s and [sie_cap]'s CELLS for the
       cycle's own boundary / prelude / tick, so the leaf borrows them for the
       instruction rather than keeping them;
     - the whole callback sits under ONE outermost [▷].  The cycle offers
       exactly one later ([HartMCycle.wp_loop_cycle_ex]'s body) and only what
       is in the context when that [iNext] runs can be stripped; a [▷] inside
       the callback would arrive through the rider, after it.  Outermost is
       also the WEAKEST premise ([P ⊢ ▷ P]), so no caller pays for the move;
     - the leaf is given [resv_any cpu_id], not [resv_frag cpu_id None]: the
       walking fetch's PTE read is EXCLUSIVE and supersedes the boundary's
       clear.

   AND ONE PREMISE CHANGE, in [wp_gpr_write_s_sconf] / [_base]: the
   [forall s_pc, <lookups> -> exec (execute base) s_pc = ...] premise became a
   [swp] obligation.  It had to.  An [exec] fact constrains the START state
   only, while a per-node walk may be interfered with BETWEEN nodes, so
   nothing bridges the two -- and the exec premise cannot be re-derived,
   because a footprint walker cannot run an instruction at a SYMBOLIC register
   index, which is what [rd] / [rsa] / [rsb] are here.  Every other statement
   in the file is byte-identical, [wp_cli_s_sconf] included.

   The bundle owns [gpr_file (tp_pin m)] (HartTp.v), so the engines below are
   fed [tp_pin m] as THEIR map; [sie_cap] stays stated at [m] (it depends on
   it only through sp, which the pin does not move).  All the leaves hand
   their continuation back through [wp_next b] -- with interrupts enabled the
   instruction can be trapped and the thread resumed on a DIFFERENT hart, and
   the rebound [CID] binder makes every resource about that hart.  That is
   also why the READ side of [ops_ok] exists, and why the instruction's own
   obligation is ∀-quantified over the hart: [tp_pin] is hart-indexed.

   TWO CpuId INSTANCES IN ONE CONTEXT IS A REAL HAZARD, and it is what the
   [rename CID into CID0] dance leaves behind.  After the rename BOTH harts
   are ordinary context entries of class [CpuId], and resolution for a lemma
   or a term written by HAND may pick either -- the failure is an [iApply]
   that "cannot apply" a goal printing identically to the one it was given.
   Terms coming from a STATEMENT are fine (they were elaborated at the right
   hart); anything spelled out after the rename takes an explicit
   [(CID := ...)], including inside its arguments ([tp_pin (CID := CID) m]). *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile HartTp WpNext WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
(* [SmodeCorePt] is NOT imported yet ON PURPOSE: the only thing this file
   wants from it is [wp_instr_s_config_regime], and that is exactly the
   surface still moving there.  The '0' arm below is stated and isolated so
   that adding the import back is a one-line change. *)
Require Import RiscvExtras.
Require Import AlignBits.
Require Import HartSwp WpMmodeSwpBase.
(* the SIE=0 arm inlines the cycle: [swp_loop]'s later is taken by hand, and
   the S-mode footprint's frames/agreements come from these three. *)
Require Import HartLift HartSpan HartMCycle HartStepAny WpSFrames HartSFrame SRegime WpIntrCore.
Require Import IntrDefs WpIntrInv.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

Section WpSmodeIntr.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* =================================================================== *)
  (* §1 THE STEP ENGINE at SIE=1, over the FOLDED BUNDLE.  Everything it   *)
  (* used to take piecewise ([intr_res], [intr_config], [gpr_file],        *)
  (* [intr_frame]) is inside [sie_cap_gpr] now, and the σ-callback it hands *)
  (* on is the funnel's own -- which is why §2's '1' arm is three lines.    *)
  (*                                                                      *)
  (* THE CALLBACK IS HART-GENERIC, inherited from                          *)
  (* [WpIntrInv.wp_exec_step_intr]: the absorbing loop can park the thread, *)
  (* so the instruction executes on the hart the last trap returned to.    *)
  (* The proof therefore does the standard rename -- the STATEMENT never    *)
  (* sees it, so callers that name this lemma's hart keep working -- and    *)
  (* everything after it means the REBOUND hart by instance resolution.     *)
  (* =================================================================== *)
  (* the CLOCK-BORROWING reading: the leaf also gets the three clock cells,
     at existential values, and hands them back.  They are stable across the
     instruction (the tick runs at the cycle BOUNDARY), so lending them costs
     the engine nothing -- and [csrr time] / [csrr sip] / [csrw stimecmp]
     cannot be written without them. *)
  Lemma wp_instr_s_intr_clock (m : regfile) (n : nat)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (b' : bool)
      (R : CpuId -> mword 64 -> mword 64 -> regfile -> nat -> iProp Σ) :
    ret_pc pc = pc ->
    sie_cap_gpr kt m n true p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    ▷ wp_next true p (fun (CID : CpuId) =>
        intr_cb_clock kt m n p pc is_rvc i b' R (CID := CID)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_exec_step_intr_clock pc m n p is_rvc i b' R). Qed.


  (* =================================================================== *)
  (* §2 THE SIE-AGNOSTIC FUNNEL over [sconf] + [sie_cap]: the capability's *)
  (* SIE INDEX [b] picks the arm.  Both arms present the SAME leaf-facing  *)
  (* obligation, which is the point of the bundle: nothing above this      *)
  (* lemma mentions the mode.                                             *)
  (*                                                                      *)
  (* THE '0' ARM IS STATED, NOT PROVED (below), and it is isolated ON      *)
  (* PURPOSE: it is [SmodeCorePt.wp_instr_s_config_regime] at              *)
  (* [strans_regime].  The regime-generic surface it will be instantiated  *)
  (* through is now [WpSmodePtFetch.wp_instr_s_config_folded], which takes *)
  (* and returns [sr_inv R] FOLDED.  Everything else here is proved, so    *)
  (* the instantiation is the ONLY edit left.                             *)
  (* =================================================================== *)
  Definition sconf_step_obl_clock (m : regfile) (n : nat) (b b' : bool)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : CpuId -> mword 64 -> mword 64 -> regfile -> nat -> iProp Σ)
      (CID : CpuId) : iProp Σ :=
    ((sconf -∗
      sie_cap kt m n b p -∗
      gpr_file (tp_pin m) -∗
      (R_bitvector_64 PC) ↦ᵣ pc -∗
      (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      resv_any cpu_id -∗
      clock_res -∗
      swp (execute i)
        (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
           ∃ (npc ms' : mword 64) (m' : regfile) (n' : nat),
             (R_bitvector_64 PC) ↦ᵣ pc ∗
             (R_bitvector_64 nextPC) ↦ᵣ npc ∗
             resv_any cpu_id ∗ clock_res ∗
             sconf_at_priv ms' ∗ sie_cap kt m' n' b' p ∗
             gpr_file (tp_pin m') ∗ R CID npc ms' m' n'))
     ∗ (∀ (npc ms' : mword 64) (m' : regfile) (n' : nat),
          sie_cap_gpr_at kt ms' m' n' b' p -∗ pc_is npc -∗ R CID npc ms' m' n' -∗
          WP (Loop : expr riscv_lang)))%I.

  Definition sconf_step_obl (m : regfile) (n : nat) (b b' : bool)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : CpuId -> mword 64 -> mword 64 -> regfile -> nat -> iProp Σ)
      (CID : CpuId) : iProp Σ :=
    ((sconf -∗
      sie_cap kt m n b p -∗
      gpr_file (tp_pin m) -∗
      (R_bitvector_64 PC) ↦ᵣ pc -∗
      (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      resv_any cpu_id -∗
      swp (execute i)
        (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
           ∃ (npc ms' : mword 64) (m' : regfile) (n' : nat),
             (R_bitvector_64 PC) ↦ᵣ pc ∗
             (R_bitvector_64 nextPC) ↦ᵣ npc ∗
             resv_any cpu_id ∗
             sconf_at_priv ms' ∗ sie_cap kt m' n' b' p ∗
             gpr_file (tp_pin m') ∗ R CID npc ms' m' n'))
     ∗ (∀ (npc ms' : mword 64) (m' : regfile) (n' : nat),
          sie_cap_gpr_at kt ms' m' n' b' p -∗ pc_is npc -∗ R CID npc ms' m' n' -∗
          WP (Loop : expr riscv_lang)))%I.

  (* the landing family of the SIE=0 arm: the tower at whatever the
     instruction left in the cells it may write.  Every component the leaf
     can move is existential here -- mstatus and mideleg (csrci/csrsi
     sstatus, sret), satp / the two PMP cells / the tlb (the capability's
     own slot), the landing pc and the three clock cells -- which is what
     lets the rider [WpIntrInv.intr_ret] be keyed on the file. *)
  Definition off_Q (pc msr : mword 64) (mc : mword 32)
      (micfg misa0 mseccfg0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp) (rs2 : regstate) : Prop :=
    exists (npc ms1 mdv1 cy1 ti1 ip1 satp1 : mword 64)
      (pcfg1 : type_of_register pmpcfg_n)
      (paddr1 : type_of_register pmpaddr_n) (tlb1 : type_of_register tlb),
      sconf_ms_facts ms1 /\
      and_vec MIE_S (not_vec mdv1) = zeros' 64 /\
      strans_satp_ok satp1 /\ pmp_ent0_ok pcfg1 paddr1 /\
      rs2 = s_rs pc npc msr (minstret_inc_flag mc micfg Supervisor)
              cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0
              (mword_of_int 0) pmar0 elp0 satp1 MIE_S mdv1 MENVCFG_S tlb1.

  (* THE SLOT'S CLOSER, KEYED ON THE LANDING FILE.  The translation slot is
     re-opened INSIDE the leaf's own postcondition -- the landing frames want
     its satp / PMP cells at the file the instruction landed on -- and
     re-sealed OUTSIDE, after the tick.  So the closer has to RIDE, and it
     rides beside [WpIntrInv.intr_ret] in the cycle's own rider: at the Bare
     arm it is where the tlb cell is PARKED, so there is nothing at the far
     end to rebuild it from.  Every value it pins is read off the landing
     file, which is what lets the continuation name it. *)
  Definition off_close (SD : gset register) (rs2 : regstate) : iProp Σ :=
    (∀ (m' : regfile) (av' : nat) (b'' : bool) (tv' : type_of_register tlb),
       ⌜ SD = s_Drwb -> tv' = register_lookup tlb rs2 ⌝ -∗
       satp ↦ᵣ register_lookup satp rs2 -∗ s_tlb_at SD tv' -∗
       pmpcfg_n ↦ᵣ register_lookup pmpcfg_n rs2 -∗
       pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs2 -∗
       strans_res_at (register_lookup satp rs2) tv' -∗
       sie_cap_rest kt m' av' b'' p -∗
       sie_cap kt m' av' b'' p)%I.

  Definition off_ret (SD : gset register) (b' : bool)
      (R : CpuId -> mword 64 -> mword 64 -> regfile -> nat -> iProp Σ)
      (rs2 : regstate) : iProp Σ :=
    (intr_ret kt p b' R rs2 ∗ off_close SD rs2)%I.

  (* THE SIE=0 ARM, PROVED HERE RATHER THAN ON [SmodeCorePt]'s WRAPPER.
     The wrapper ([wp_instr_s_config_regime]) now has everything this arm
     needs on the leaf side -- the borrowed [clock_res] and an existential
     post mstatus/mideleg, which this funnel cannot do without (csrci/csrsi
     sstatus and sret MOVE SIE, and at [b = false] moving it IS the
     [b' = true] transition) -- but not the LATER.  This funnel takes its
     callback under one outermost [▷], because the cycle offers exactly one
     and a [▷] inside the callback would arrive through the rider, after it;
     the wrapper takes its leaf obligation with no [▷] at all, and the only
     later in the whole chain ([HartSwp.swp_loop]'s) is stripped three
     layers inside it -- i.e. after the obligation has had to be handed
     over.  [▷ (swp e Φ) ⊢ swp e Φ] does not hold, so there is no way to
     supply it from outside.

     So this arm INLINES [HartMCycle.wp_loop_cycle_ex]'s own two lines
     ([swp_loop] then [swp_tick_wrap_ex]) and takes that later HERE.  The
     rest is the SIE=1 engine's plumbing with the trap arm deleted:
       - the bundle opens into the cells ([WpIntrInv.sconf_to_cells] and
         [WpIntrInv.sie_cap_frame_acc]).  The SLOT is where the two
         translation arms are told apart, and this is the only funnel that
         has to: the accessor hands out [s_tlb_at SD] rather than the tlb
         cell, so the Bare slot before kvminithart need not fund one;
       - SIE=0 is read off the capability's ghost quarter, which is what
         the index [b = false] MEANS, and it makes [s_dispatch] [None] --
         so the run rule's trap payload is instantiated at [False];
       - the body is [WpIntrInv.swp_run_hart_active_instr_S_res] at the KPT
         arm and [_res_b] at the Bare one -- two CONCRETE branches, because
         a write set in a parameter position makes the [iApply] diverge --
         and the rider is [WpIntrInv.intr_ret] with the slot's closer
         beside it ([off_ret]): the frames go back at the landing tower and
         the non-cell residue rides beside them. *)
  Lemma wp_instr_s_sconf_off_clock (m : regfile) (n : nat)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (b' : bool)
      (R : CpuId -> mword 64 -> mword 64 -> regfile -> nat -> iProp Σ) :
    sie_cap_gpr kt m n false p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    ▷ wp_next false p (sconf_step_obl_clock m n false b' pc is_rvc i R) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc #Hinstr Hbody".
    (* ---- the bundle, into the 25 cells ---- *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (sconf_to_cells with "Hsc") as (mst0 mdv0)
      "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
        Hmdl & Hmenv)".
    (* THE SLOT, THROUGH THE ARM-AWARE ACCESSOR.  [sie_cap_to_cells] hands
       out the tlb CELL unconditionally, and that is exactly what forces the
       Bare arm to fund one; [WpIntrInv.sie_cap_frame_acc] hands out
       [s_tlb_at SD] instead -- the cell at the kernel table, [emp] under
       Bare -- with the arm as a PURE fact and the re-seal as a closer.  See
       claude-notes/projects/kvminithart-tlb-lane.md. *)
    iDestruct (sie_cap_frame_acc with "Hcap") as (SD satp0 tlbv pcfg paddr)
      "(%Harm & %Hpok & #Hwitk & Hsatp & Htlb & Hpcfg & Hpaddr & Hres &
        Hrest & Hclose)".
    pose proof (s_arm_satp_ok _ _ Harm) as Hsok.
    (* SIE = 0 IS READ OFF THE CAPABILITY'S OWN GHOST QUARTER, which is what
       the arm index [b = false] MEANS.  It is what makes the dispatch's
       [Some] arm refutable below, so the whole trap payload is [False]. *)
    iDestruct "Hrest" as "(Hstk & Harm & #Htc & #Hwit)".
    iEval (rewrite /sie_arm) in "Harm".
    iDestruct (ghost_var_agree with "Hhalf Harm") as %HSIE0.
    assert (HSIE : eq_vec (_get_Mstatus_SIE mst0) ('b"1") = false)
      by (rewrite HSIE0; vm_compute; reflexivity).
    iAssert (sie_cap_rest kt m n false p) with "[Hstk Harm]" as "Hrest".
    { rewrite /sie_cap_rest /sie_arm. iFrame "Hstk Harm Htc Hwit". }
    iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr & Hresv)".
    iDestruct "Hmr" as (msr bmi mc micfg) "(Hmsr & Hmi & #Hmc & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hcy & Hti & Hip)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmS & %HmC &
        %HmU & %HmM & %Hpmaall & %Hsec1 & %Hsec2 & %Helpnp & %HmA &
        %Hmisaval & %Hsecval & #Hkmapb)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    pose proof Hmsf as Hmsf'. destruct Hmsf' as (HMPRV & HSXL & _).
    (* ---- THE ARM, SPLIT HERE AND NOWHERE ELSE.  Both branches are
       CONCRETE in the write set, and they have to be: an [iApply] of a cycle
       engine whose write set sits in a PARAMETER position does not terminate
       against this goal, however concrete the argument (kvminithart-tlb-lane
       .md §3).  Nothing under the split mentions [SD], and the two branches
       differ only in the set, its memberships, and the engine's name. ---- *)
    destruct Harm as [[-> Hbsok] | [-> Hksok]].
    { (* ===================== THE BARE ARM, at [s_Drwb] ==================
         [translateAddr]'s [Bare] arm is a bare [returnR] -- it neither reads
         nor writes the TLB -- so the fetch's frame does not contain the cell
         and nothing has to fund one.  It stays in the slot, parked in the
         accessor's closer. ============================================== *)
      (* ---- the cycle's frame, at the tower the cells make ---- *)
      iAssert (hreg_frame (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg
                   misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                   MENVCFG_S tlbv) s_Drwb ∗
               hreg_frame_ro (s_Df (DfracOwn 1))
                 (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                    mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                    MENVCFG_S tlbv) s_Dro)%I
        with "[HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg Hpaddr
               Hsatp Hmie Hmdl Hmenv]" as "[Hsrw Hsro]".
      { rewrite (s_frames_cells_D pc pc msr bmi cy ti ip mst0 pcfg paddr mc
                   micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0
                   MIE_S mdv0 MENVCFG_S tlbv s_Drwb (or_intror eq_refl)).
        rewrite /s_cells_D. srs.
        iFrame "HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg Hpaddr
                Hsatp Hmie Hmdl Hmenv".
        iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv". }
      (* ---- THE CYCLE, WITH THE LATER STRIPPED BY HAND.
         [HartMCycle.wp_loop_cycle_ex] is inlined ([swp_loop] + [swp_tick_wrap_ex],
         its own two lines) for ONE reason: this funnel's callback sits under an
         outermost [▷], and [swp_loop]'s later is the only one in the whole
         chain -- taking it here is what puts the leaf's obligation in hand
         BEFORE the body has to be supplied. ---- *)
      iDestruct "Hresv" as (rr) "Hfrag".
      iApply (swp_loop rr with "Hcert Hfrag").
      iNext. iIntros (tick) "Hfrag".
      iApply (swp_mono _ _ (fun _ => WP (Loop : expr riscv_lang))%I
                with "[] [-]").
      2:{ iApply (swp_tick_wrap_ex s_Drwb s_Dro (s_Df (DfracOwn 1))
                    (fun rsx => exists (rs2 : regstate) (mi : mword 64),
                       off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0 rs2 /\
                       rsx = wrap_post rs2 mi)
                    (fun rsx => ∃ (rs2 : regstate) (mi : mword 64),
                       ⌜off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0 rs2 /\
                        rsx = wrap_post rs2 mi⌝ ∗ off_ret s_Drwb b' R rs2)%I
                    tick s_disj_b s_w_cy_b s_w_ti_b s_w_ip_b
                    with "Hcert [-]").
          (* [swp_try_step_any_ex] lands at [wrap_post rs2 mi] with the two
             existentials OUTSIDE; the tick wants them inside its [rs1]. *)
          iApply (swp_mono with "[] [-]").
          2:{ iApply (swp_try_step_any_ex s_Drwb s_Dro (s_Df (DfracOwn 1))
                    (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                       mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                       MENVCFG_S tlbv)
                    (off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0)
                    (off_ret s_Drwb b' R)
                    s_disj_b s_in_priv_b s_in_hart_b s_in_mc_b
                    s_in_micfg_b s_w_mi_b s_in_mi_b s_w_ms_b s_in_ms_b
                    s_w_PC_b s_in_PC_b s_in_nPC_b
                    ltac:(by srs)
                    ltac:(intros rs2 HQ; destruct HQ as (npc & ms1 & mdv1 & cy1
                            & ti1 & ip1 & satp1 & pcfg1 & paddr1 & tlb1 & _ & _
                            & _ & _ & ->); by srs)
                    ltac:(intros rs2 HQ; destruct HQ as (npc & ms1 & mdv1 & cy1
                            & ti1 & ip1 & satp1 & pcfg1 & paddr1 & tlb1 & _ & _
                            & _ & _ & ->);
                          rewrite s_rs_mc s_rs_micfg s_rs_priv; by srs)
                    with "Hcert Hsrw Hsro [-]").
          iIntros "Hrw Hro".
          (* the prelude's file, re-anchored on the tower *)
          pose proof (s_pre_agree pc msr bmi cy ti ip mst0 pcfg paddr mc micfg
                        misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S
                        mdv0 MENVCFG_S tlbv) as Hpre.
          iDestruct (s_rw_ext_D s_Drwb s_frame_ok_Drwb _ _ Hpre
                       with "Hrw") as "Hrw".
          iDestruct (s_ro_ext (DfracOwn 1) _ _ Hpre with "Hro") as "Hro".
          iApply (swp_mono with "[] [-]").
          2:{ iApply (swp_run_hart_active_instr_S_res_b pc msr
                        (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                        pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0)
                        pmar0 elp0 satp0 mdv0 tlbv is_rvc i
                        (off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0)
                        (off_ret s_Drwb b' R)
                        (* THE SLOT'S CLOSER TRAVELS IN [W]: the leaf is
                           handed a FOLDED capability, and the closer is
                           the only thing that can build one -- at the Bare
                           arm it is holding the tlb cell. *)
                        (wp_next false p
                           (sconf_step_obl_clock m n false b' pc is_rvc i R)
                         ∗ ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0)
                         ∗ sret_tie mst0 ∗ sie_cap_rest kt m n false p
                         ∗ gpr_file (tp_pin m)
                         ∗ (∀ (m1 : regfile) (av1 : nat) (b1 : bool)
                              (tv1 : type_of_register tlb),
                              satp ↦ᵣ satp0 -∗ s_tlb_at s_Drwb tv1 -∗
                              pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
                              strans_res_at satp0 tv1 -∗
                              sie_cap_rest kt m1 av1 b1 p -∗
                              sie_cap kt m1 av1 b1 p))%I
                        (fun _ _ => False)%I
                        Hmisaval HSXL HMPRV Hmm Helpnp (pma_all_ram Hpmaall)
                        Hbsok Hpok
                        with "Hcert Hinstr Hres Hfrag
                              [$Hbody $Hhalf $Htie $Hrest $Hfile $Hclose]
                              Hrw Hro
                              [] []").
              (* ---------- NO TRAP: SIE = 0 makes [s_dispatch] [None] ------- *)
              { iIntros (ii pr) "%Hd _ _ _ _ _".
                iPureIntro. destruct Hd as (meip & seip & Hd).
                rewrite /s_dispatch HSIE in Hd. cbn [andb] in Hd. discriminate. }
              (* ---------- THE INSTRUCTION ---------- *)
              iIntros (tv') "HW HRes Hany Hrw Hro".
              iDestruct "HW" as "(Hwn & Hhalf & Htie & Hrest & Hfile & Hclose)".
              pose proof (s_rs_set_nPC pc pc
                         (add_vec_int pc (if is_rvc then 2 else 4)) msr
                         (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                         pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0)
                         pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tv') as Hagf.
              iDestruct (s_rw_ext_D s_Drwb s_frame_ok_Drwb _ _ Hagf
                           with "Hrw") as "Hrw".
              iDestruct (s_ro_ext (DfracOwn 1) _ _ Hagf with "Hro") as "Hro".
              iAssert (s_cells_D pc (add_vec_int pc (if is_rvc then 2 else 4))
                         msr (minstret_inc_flag mc micfg Supervisor) cy ti ip
                         mst0 pcfg paddr mc micfg misa0 mseccfg0
                         (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                         MENVCFG_S tv' s_Drwb)
                with "[Hrw Hro]" as "Hcells".
              { rewrite -(s_frames_cells_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                            _ _ _ _ _ s_Drwb (or_intror eq_refl)). iFrame. }
              iEval (rewrite /s_cells_D) in "Hcells".
              iDestruct "Hcells" as
                "(HPC & HnPC & Hmsr & Hmi & Hcy & Hti & Hip & Htlb & Hpriv &
                  Hms & Hhs & Hpcfg & Hpaddr & ? & ? & ? & ? & ? & ? & ? & ? &
                  Hsatp & Hmie & Hmdl & Hmenv)".
              iAssert (sconf) with "[Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv]"
                as "Hsc".
              { iApply (sconf_of_cells mst0 mdv0 Hmsf Hmm
                          with "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl
                                Hmenv"). }
              iAssert (sie_cap kt m n false p)
                with "[Hsatp Htlb Hpcfg Hpaddr HRes Hrest Hclose]" as "Hcap".
              { iApply ("Hclose" $! m n false tv'
                          with "Hsatp Htlb Hpcfg Hpaddr HRes Hrest"). }
              iAssert (clock_res) with "[Hcy Hti Hip]" as "Hclk".
              { iExists cy, ti, ip. iFrame. }
              iDestruct (wp_next_at false p _ CID (fun _ => eq_refl) with "Hwn")
                as "[Hobl Hcont]".
              iApply (swp_mono with "[Hmsr Hmi Hhs Hcont] [-]").
              2:{ iApply ("Hobl" with "Hsc Hcap Hfile HPC HnPC Hany Hclk"). }
              iIntros (e) "(-> & Hr)".
              iDestruct "Hr" as (npc ms' m' av')
                "(HPC & HnPC & Hresv2 & Hclk & Hsc' & Hcap' & Hfile' & HRv)".
              iDestruct "Hclk" as (cy' ti' ip') "(Hcy & Hti & Hip)".
              iDestruct "Hsc'" as (mdv') "(%Hmsf' & %Hmm' & _ & _ & Hpriv' &
                                           Hms' & Hhalf' & Htie' & Hmie' &
                                           Hmdl' & Hmenv')".
              iDestruct (sie_cap_cells_at s_Drwb kt m' av' b' p (or_intror eq_refl)
                           with "Hwitk Hcap'")
                as (satp1 tlb1 pcfg1 paddr1)
                   "(%Hsok1 & %Hpok1 & Hsatp1 & Htlb1 & Hpcfg1 & Hpaddr1 &
                     Hres1 & Hrest1 & Hclose1)".
              iSplitR; [done|].
              iExists (s_rs pc npc msr (minstret_inc_flag mc micfg Supervisor)
                     cy' ti' ip' ms' pcfg1 paddr1 mc micfg misa0 mseccfg0
                     (mword_of_int 0) pmar0 elp0 satp1 MIE_S mdv' MENVCFG_S
                     tlb1).
              iSplitR.
              { iPureIntro.
                exists npc, ms', mdv', cy', ti', ip', satp1, pcfg1, paddr1, tlb1.
                split_and!; try assumption; reflexivity. }
              iAssert (hreg_frame (s_rs pc npc msr
                         (minstret_inc_flag mc micfg Supervisor) cy' ti' ip' ms'
                         pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0)
                         pmar0 elp0 satp1 MIE_S mdv' MENVCFG_S tlb1) s_Drwb ∗
                       hreg_frame_ro (s_Df (DfracOwn 1)) (s_rs pc npc msr
                         (minstret_inc_flag mc micfg Supervisor) cy' ti' ip' ms'
                         pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0)
                         pmar0 elp0 satp1 MIE_S mdv' MENVCFG_S tlb1) s_Dro)%I
                with "[HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb1 Hpriv' Hms' Hhs
                       Hpcfg1 Hpaddr1 Hsatp1 Hmie' Hmdl' Hmenv']"
                as "[Hrw2 Hro2]".
              { rewrite (s_frames_cells_D pc npc msr
                           (minstret_inc_flag mc micfg Supervisor) cy' ti' ip'
                           ms' pcfg1 paddr1 mc micfg misa0 mseccfg0
                           (mword_of_int 0) pmar0 elp0 satp1 MIE_S mdv'
                           MENVCFG_S tlb1 s_Drwb (or_intror eq_refl)).
                rewrite /s_cells_D. srs.
                iFrame "HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb1 Hpriv' Hms' Hhs
                        Hpcfg1 Hpaddr1 Hsatp1 Hmie' Hmdl' Hmenv'".
                iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv". }
              iFrame "Hrw2 Hro2".
              rewrite /off_ret. iSplitR "Hclose1".
              { rewrite /intr_ret. srs. iExists m', av'.
                iFrame "Hhalf' Htie' Hres1 Hrest1 Hfile' Hresv2 HRv Hcont". }
              rewrite /off_close. srs. iExact "Hclose1". }
          iIntros (st) "[Hi | Hr]".
          - iDestruct "Hi" as (ii pr) "(-> & %Hf)". destruct Hf.
          - iDestruct "Hr" as (w) "(-> & Hr)".
            iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HRet)".
            iExists rs2. iSplitR; [done|]. iFrame. }
          iIntros (u). iDestruct 1 as (rs2 mi) "(%HQ & Hrw & Hro & HRet)".
          iExists (wrap_post rs2 mi).
          iSplitR; [iPureIntro; by exists rs2, mi |].
          iFrame "Hrw Hro". iExists rs2, mi. iFrame "HRet".
          iPureIntro. by split. }
      (* ---- THE CYCLE'S CONTINUATION ---- *)
      iIntros (u). iDestruct 1 as (rs3 rs1) "((%HP & %Hag) & Hrw & Hro & HRet)".
      iDestruct "HRet" as (rs2 mi) "((%HQ & %Heq) & HRet)".
      subst rs1.
      destruct HQ as (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 & pcfg1 &
                      paddr1 & tlb1 & Hmsf1 & Hmm1 & Hsok1 & Hpok1 & ->).
      iEval (rewrite /off_ret) in "HRet".
      iDestruct "HRet" as "(HRet & Hclose1)".
      iEval (rewrite /intr_ret) in "HRet".
      iEval (srs) in "HRet".
      iEval (rewrite /off_close) in "Hclose1".
      iEval (srs) in "Hclose1".
      iDestruct "HRet" as (m' av')
        "(Hhalf1 & Htie1 & Hres1 & Hrest1 & Hfile1 & Hresv1 & HRv & Hcont)".
      pose proof (s_tick_agree_b pc npc msr
                    (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                    pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0
                    elp0 satp1 MIE_S mdv1 MENVCFG_S tlb1 mi rs3 Hag) as Hag'.
      iDestruct (s_rw_ext_D s_Drwb s_frame_ok_Drwb _ _ Hag'
                   with "Hrw") as "Hrw".
      iDestruct (s_ro_ext (DfracOwn 1) _ _ Hag' with "Hro") as "Hro".
      iAssert (s_cells_D npc npc mi (minstret_inc_flag mc micfg Supervisor)
                 (register_lookup (R_bitvector_64 mcycle) rs3)
                 (register_lookup (R_bitvector_64 mtime) rs3)
                 (register_lookup (R_bitvector_64 mip) rs3)
                 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0)
                 pmar0 elp0 satp1 MIE_S mdv1 MENVCFG_S
                 (register_lookup tlb rs3) s_Drwb)
        with "[Hrw Hro]" as "Hcells".
      { rewrite -(s_frames_cells_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    _ _ s_Drwb (or_intror eq_refl)). iFrame. }
      iEval (rewrite /s_cells_D) in "Hcells".
      iDestruct "Hcells" as
        "(HPC & HnPC & Hmsr3 & Hmi3 & Hcy3 & Hti3 & Hip3 & Htlb3 & Hpriv3 &
          Hms3 & Hhs3 & Hpcfg3 & Hpaddr3 & ? & ? & ? & ? & ? & ? & ? & ? &
          Hsatp3 & Hmie3 & Hmdl3 & Hmenv3)".
      iEval (rewrite s_tlb_at_bare) in "Htlb3".
      iAssert (s_tlb_at s_Drwb tlb1) with "[Htlb3]" as "Htlb3".
      { rewrite s_tlb_at_bare. iExact "Htlb3". }
      iApply ("Hcont" $! npc ms1 m' av' with
                "[Hhs3 Hpriv3 Hms3 Hhalf1 Htie1 Hmie3 Hmdl3 Hmenv3 Hsatp3
                  Htlb3 Hpcfg3 Hpaddr3 Hres1 Hrest1 Hfile1 Hclose1]
                 [HPC HnPC Hmsr3 Hmi3 Hcy3 Hti3 Hip3 Hresv1] HRv").
      - rewrite /sie_cap_gpr_at. iFrame "Hhs3 Hfile1".
        iSplitL "Hpriv3 Hms3 Hhalf1 Htie1 Hmie3 Hmdl3 Hmenv3".
        { iApply (sconf_at_of_cells ms1 mdv1 Hmsf1 Hmm1
                    with "Hhw Hminv Hpriv3 Hms3 Hhalf1 Htie1 Hmie3 Hmdl3
                          Hmenv3"). }
        iApply ("Hclose1" $! m' av' b' tlb1 with "[%] Hsatp3 Htlb3 Hpcfg3
                  Hpaddr3 Hres1 Hrest1").
        intros _. reflexivity.
      - rewrite /pc_is. iFrame "HPC HnPC Hresv1".
        iSplitL "Hmsr3 Hmi3".
        { iExists mi, (minstret_inc_flag mc micfg Supervisor), mc, micfg.
          by iFrame "Hmsr3 Hmi3 Hmc Hmicfg". }
        iExists (register_lookup (R_bitvector_64 mcycle) rs3),
                (register_lookup (R_bitvector_64 mtime) rs3),
                (register_lookup (R_bitvector_64 mip) rs3).
        by iFrame "Hcy3 Hti3 Hip3".
    }
    { (* ===================== THE KPT ARM, at [s_Drw] ====================
         a Sv39 fetch's walk FILLS the TLB ([CommonWalk]'s [vec_update_dec]),
         so [tlb ∈ s_Drw] is genuinely needed and [tlb_res_pt] funds the
         cell. ========================================================= *)
      (* ---- the cycle's frame, at the tower the cells make ---- *)
      iAssert (hreg_frame (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg
                   misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                   MENVCFG_S tlbv) s_Drw ∗
               hreg_frame_ro (s_Df (DfracOwn 1))
                 (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                    mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                    MENVCFG_S tlbv) s_Dro)%I
        with "[HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg Hpaddr
               Hsatp Hmie Hmdl Hmenv]" as "[Hsrw Hsro]".
      { rewrite (s_frames_cells_D pc pc msr bmi cy ti ip mst0 pcfg paddr mc
                   micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0
                   MIE_S mdv0 MENVCFG_S tlbv s_Drw (or_introl eq_refl)).
        rewrite /s_cells_D. srs.
        iFrame "HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg Hpaddr
                Hsatp Hmie Hmdl Hmenv".
        iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv". }
      (* ---- THE CYCLE, WITH THE LATER STRIPPED BY HAND.
         [HartMCycle.wp_loop_cycle_ex] is inlined ([swp_loop] + [swp_tick_wrap_ex],
         its own two lines) for ONE reason: this funnel's callback sits under an
         outermost [▷], and [swp_loop]'s later is the only one in the whole
         chain -- taking it here is what puts the leaf's obligation in hand
         BEFORE the body has to be supplied. ---- *)
      iDestruct "Hresv" as (rr) "Hfrag".
      iApply (swp_loop rr with "Hcert Hfrag").
      iNext. iIntros (tick) "Hfrag".
      iApply (swp_mono _ _ (fun _ => WP (Loop : expr riscv_lang))%I
                with "[] [-]").
      2:{ iApply (swp_tick_wrap_ex s_Drw s_Dro (s_Df (DfracOwn 1))
                    (fun rsx => exists (rs2 : regstate) (mi : mword 64),
                       off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0 rs2 /\
                       rsx = wrap_post rs2 mi)
                    (fun rsx => ∃ (rs2 : regstate) (mi : mword 64),
                       ⌜off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0 rs2 /\
                        rsx = wrap_post rs2 mi⌝ ∗ off_ret s_Drw b' R rs2)%I
                    tick s_disj s_w_cy s_w_ti s_w_ip with "Hcert [-]").
          (* [swp_try_step_any_ex] lands at [wrap_post rs2 mi] with the two
             existentials OUTSIDE; the tick wants them inside its [rs1]. *)
          iApply (swp_mono with "[] [-]").
          2:{ iApply (swp_try_step_any_ex s_Drw s_Dro (s_Df (DfracOwn 1))
                    (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                       mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                       MENVCFG_S tlbv)
                    (off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0)
                    (off_ret s_Drw b' R)
                    s_disj s_in_priv s_in_hart s_in_mc s_in_micfg s_w_mi
                    s_in_mi s_w_ms s_in_ms s_w_PC s_in_PC s_in_nPC
                    ltac:(by srs)
                    ltac:(intros rs2 HQ; destruct HQ as (npc & ms1 & mdv1 & cy1
                            & ti1 & ip1 & satp1 & pcfg1 & paddr1 & tlb1 & _ & _
                            & _ & _ & ->); by srs)
                    ltac:(intros rs2 HQ; destruct HQ as (npc & ms1 & mdv1 & cy1
                            & ti1 & ip1 & satp1 & pcfg1 & paddr1 & tlb1 & _ & _
                            & _ & _ & ->);
                          rewrite s_rs_mc s_rs_micfg s_rs_priv; by srs)
                    with "Hcert Hsrw Hsro [-]").
          iIntros "Hrw Hro".
          (* the prelude's file, re-anchored on the tower *)
          pose proof (s_pre_agree pc msr bmi cy ti ip mst0 pcfg paddr mc micfg
                        misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S
                        mdv0 MENVCFG_S tlbv) as Hpre.
          iDestruct (s_rw_ext _ _ Hpre with "Hrw") as "Hrw".
          iDestruct (s_ro_ext (DfracOwn 1) _ _ Hpre with "Hro") as "Hro".
          iApply (swp_mono with "[] [-]").
          2:{ iApply (swp_run_hart_active_instr_S_res pc msr
                        (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                        pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0)
                        pmar0 elp0 satp0 mdv0 tlbv is_rvc i
                        (off_Q pc msr mc micfg misa0 mseccfg0 pmar0 elp0)
                        (off_ret s_Drw b' R)
                        (* THE SLOT'S CLOSER TRAVELS IN [W]: the leaf is
                           handed a FOLDED capability, and the closer is
                           the only thing that can build one -- at the Bare
                           arm it is holding the tlb cell. *)
                        (wp_next false p
                           (sconf_step_obl_clock m n false b' pc is_rvc i R)
                         ∗ ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0)
                         ∗ sret_tie mst0 ∗ sie_cap_rest kt m n false p
                         ∗ gpr_file (tp_pin m)
                         ∗ (∀ (m1 : regfile) (av1 : nat) (b1 : bool)
                              (tv1 : type_of_register tlb),
                              satp ↦ᵣ satp0 -∗ s_tlb_at s_Drw tv1 -∗
                              pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
                              strans_res_at satp0 tv1 -∗
                              sie_cap_rest kt m1 av1 b1 p -∗
                              sie_cap kt m1 av1 b1 p))%I
                        (fun _ _ => False)%I
                        Hmisaval HSXL HMPRV Hmm Helpnp (pma_all_ram Hpmaall)
                        Hsok Hpok
                        with "Hcert Hinstr Hres Hfrag
                              [$Hbody $Hhalf $Htie $Hrest $Hfile $Hclose]
                              Hrw Hro
                              [] []").
              (* ---------- NO TRAP: SIE = 0 makes [s_dispatch] [None] ------- *)
              { iIntros (ii pr) "%Hd _ _ _ _ _".
                iPureIntro. destruct Hd as (meip & seip & Hd).
                rewrite /s_dispatch HSIE in Hd. cbn [andb] in Hd. discriminate. }
              (* ---------- THE INSTRUCTION ---------- *)
              iIntros (tv') "HW HRes Hany Hrw Hro".
              iDestruct "HW" as "(Hwn & Hhalf & Htie & Hrest & Hfile & Hclose)".
              pose proof (s_rs_set_nPC pc pc
                         (add_vec_int pc (if is_rvc then 2 else 4)) msr
                         (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                         pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0)
                         pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tv') as Hagf.
              iDestruct (s_rw_ext _ _ Hagf with "Hrw") as "Hrw".
              iDestruct (s_ro_ext (DfracOwn 1) _ _ Hagf with "Hro") as "Hro".
              iAssert (s_cells_D pc (add_vec_int pc (if is_rvc then 2 else 4))
                         msr (minstret_inc_flag mc micfg Supervisor) cy ti ip
                         mst0 pcfg paddr mc micfg misa0 mseccfg0
                         (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                         MENVCFG_S tv' s_Drw)
                with "[Hrw Hro]" as "Hcells".
              { rewrite -(s_frames_cells_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                            _ _ _ _ _ s_Drw (or_introl eq_refl)). iFrame. }
              iEval (rewrite /s_cells_D) in "Hcells".
              iDestruct "Hcells" as
                "(HPC & HnPC & Hmsr & Hmi & Hcy & Hti & Hip & Htlb & Hpriv &
                  Hms & Hhs & Hpcfg & Hpaddr & ? & ? & ? & ? & ? & ? & ? & ? &
                  Hsatp & Hmie & Hmdl & Hmenv)".
              iAssert (sconf) with "[Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv]"
                as "Hsc".
              { iApply (sconf_of_cells mst0 mdv0 Hmsf Hmm
                          with "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl
                                Hmenv"). }
              iAssert (sie_cap kt m n false p)
                with "[Hsatp Htlb Hpcfg Hpaddr HRes Hrest Hclose]" as "Hcap".
              { iApply ("Hclose" $! m n false tv'
                          with "Hsatp Htlb Hpcfg Hpaddr HRes Hrest"). }
              iAssert (clock_res) with "[Hcy Hti Hip]" as "Hclk".
              { iExists cy, ti, ip. iFrame. }
              iDestruct (wp_next_at false p _ CID (fun _ => eq_refl) with "Hwn")
                as "[Hobl Hcont]".
              iApply (swp_mono with "[Hmsr Hmi Hhs Hcont] [-]").
              2:{ iApply ("Hobl" with "Hsc Hcap Hfile HPC HnPC Hany Hclk"). }
              iIntros (e) "(-> & Hr)".
              iDestruct "Hr" as (npc ms' m' av')
                "(HPC & HnPC & Hresv2 & Hclk & Hsc' & Hcap' & Hfile' & HRv)".
              iDestruct "Hclk" as (cy' ti' ip') "(Hcy & Hti & Hip)".
              iDestruct "Hsc'" as (mdv') "(%Hmsf' & %Hmm' & _ & _ & Hpriv' &
                                           Hms' & Hhalf' & Htie' & Hmie' &
                                           Hmdl' & Hmenv')".
              iDestruct (sie_cap_cells_at s_Drw kt m' av' b' p (or_introl eq_refl)
                           with "Hwitk Hcap'")
                as (satp1 tlb1 pcfg1 paddr1)
                   "(%Hsok1 & %Hpok1 & Hsatp1 & Htlb1 & Hpcfg1 & Hpaddr1 &
                     Hres1 & Hrest1 & Hclose1)".
              iSplitR; [done|].
              iExists (s_rs pc npc msr (minstret_inc_flag mc micfg Supervisor)
                     cy' ti' ip' ms' pcfg1 paddr1 mc micfg misa0 mseccfg0
                     (mword_of_int 0) pmar0 elp0 satp1 MIE_S mdv' MENVCFG_S
                     tlb1).
              iSplitR.
              { iPureIntro.
                exists npc, ms', mdv', cy', ti', ip', satp1, pcfg1, paddr1, tlb1.
                split_and!; try assumption; reflexivity. }
              iAssert (hreg_frame (s_rs pc npc msr
                         (minstret_inc_flag mc micfg Supervisor) cy' ti' ip' ms'
                         pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0)
                         pmar0 elp0 satp1 MIE_S mdv' MENVCFG_S tlb1) s_Drw ∗
                       hreg_frame_ro (s_Df (DfracOwn 1)) (s_rs pc npc msr
                         (minstret_inc_flag mc micfg Supervisor) cy' ti' ip' ms'
                         pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0)
                         pmar0 elp0 satp1 MIE_S mdv' MENVCFG_S tlb1) s_Dro)%I
                with "[HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb1 Hpriv' Hms' Hhs
                       Hpcfg1 Hpaddr1 Hsatp1 Hmie' Hmdl' Hmenv']"
                as "[Hrw2 Hro2]".
              { rewrite (s_frames_cells_D pc npc msr
                           (minstret_inc_flag mc micfg Supervisor) cy' ti' ip'
                           ms' pcfg1 paddr1 mc micfg misa0 mseccfg0
                           (mword_of_int 0) pmar0 elp0 satp1 MIE_S mdv'
                           MENVCFG_S tlb1 s_Drw (or_introl eq_refl)).
                rewrite /s_cells_D. srs.
                iFrame "HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb1 Hpriv' Hms' Hhs
                        Hpcfg1 Hpaddr1 Hsatp1 Hmie' Hmdl' Hmenv'".
                iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv". }
              iFrame "Hrw2 Hro2".
              rewrite /off_ret. iSplitR "Hclose1".
              { rewrite /intr_ret. srs. iExists m', av'.
                iFrame "Hhalf' Htie' Hres1 Hrest1 Hfile' Hresv2 HRv Hcont". }
              rewrite /off_close. srs. iExact "Hclose1". }
          iIntros (st) "[Hi | Hr]".
          - iDestruct "Hi" as (ii pr) "(-> & %Hf)". destruct Hf.
          - iDestruct "Hr" as (w) "(-> & Hr)".
            iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HRet)".
            iExists rs2. iSplitR; [done|]. iFrame. }
          iIntros (u). iDestruct 1 as (rs2 mi) "(%HQ & Hrw & Hro & HRet)".
          iExists (wrap_post rs2 mi).
          iSplitR; [iPureIntro; by exists rs2, mi |].
          iFrame "Hrw Hro". iExists rs2, mi. iFrame "HRet".
          iPureIntro. by split. }
      (* ---- THE CYCLE'S CONTINUATION ---- *)
      iIntros (u). iDestruct 1 as (rs3 rs1) "((%HP & %Hag) & Hrw & Hro & HRet)".
      iDestruct "HRet" as (rs2 mi) "((%HQ & %Heq) & HRet)".
      subst rs1.
      destruct HQ as (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 & pcfg1 &
                      paddr1 & tlb1 & Hmsf1 & Hmm1 & Hsok1 & Hpok1 & ->).
      iEval (rewrite /off_ret) in "HRet".
      iDestruct "HRet" as "(HRet & Hclose1)".
      iEval (rewrite /intr_ret) in "HRet".
      iEval (srs) in "HRet".
      iEval (rewrite /off_close) in "Hclose1".
      iEval (srs) in "Hclose1".
      iDestruct "HRet" as (m' av')
        "(Hhalf1 & Htie1 & Hres1 & Hrest1 & Hfile1 & Hresv1 & HRv & Hcont)".
      pose proof (s_tick_agree pc npc msr
                    (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                    pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0
                    elp0 satp1 MIE_S mdv1 MENVCFG_S tlb1 mi rs3 Hag) as Hag'.
      iDestruct (s_rw_ext _ _ Hag' with "Hrw") as "Hrw".
      iDestruct (s_ro_ext (DfracOwn 1) _ _ Hag' with "Hro") as "Hro".
      iAssert (s_cells_D npc npc mi (minstret_inc_flag mc micfg Supervisor)
                 (register_lookup (R_bitvector_64 mcycle) rs3)
                 (register_lookup (R_bitvector_64 mtime) rs3)
                 (register_lookup (R_bitvector_64 mip) rs3)
                 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 (mword_of_int 0)
                 pmar0 elp0 satp1 MIE_S mdv1 MENVCFG_S tlb1 s_Drw)
        with "[Hrw Hro]" as "Hcells".
      { rewrite -(s_frames_cells_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    _ _ s_Drw (or_introl eq_refl)). iFrame. }
      iEval (rewrite /s_cells_D) in "Hcells".
      iDestruct "Hcells" as
        "(HPC & HnPC & Hmsr3 & Hmi3 & Hcy3 & Hti3 & Hip3 & Htlb3 & Hpriv3 &
          Hms3 & Hhs3 & Hpcfg3 & Hpaddr3 & ? & ? & ? & ? & ? & ? & ? & ? &
          Hsatp3 & Hmie3 & Hmdl3 & Hmenv3)".
      iApply ("Hcont" $! npc ms1 m' av' with
                "[Hhs3 Hpriv3 Hms3 Hhalf1 Htie1 Hmie3 Hmdl3 Hmenv3 Hsatp3
                  Htlb3 Hpcfg3 Hpaddr3 Hres1 Hrest1 Hfile1 Hclose1]
                 [HPC HnPC Hmsr3 Hmi3 Hcy3 Hti3 Hip3 Hresv1] HRv").
      - rewrite /sie_cap_gpr_at. iFrame "Hhs3 Hfile1".
        iSplitL "Hpriv3 Hms3 Hhalf1 Htie1 Hmie3 Hmdl3 Hmenv3".
        { iApply (sconf_at_of_cells ms1 mdv1 Hmsf1 Hmm1
                    with "Hhw Hminv Hpriv3 Hms3 Hhalf1 Htie1 Hmie3 Hmdl3
                          Hmenv3"). }
        iApply ("Hclose1" $! m' av' b' tlb1 with "[%] Hsatp3 Htlb3 Hpcfg3
                  Hpaddr3 Hres1 Hrest1").
        intros _. reflexivity.
      - rewrite /pc_is. iFrame "HPC HnPC Hresv1".
        iSplitL "Hmsr3 Hmi3".
        { iExists mi, (minstret_inc_flag mc micfg Supervisor), mc, micfg.
          by iFrame "Hmsr3 Hmi3 Hmc Hmicfg". }
        iExists (register_lookup (R_bitvector_64 mcycle) rs3),
                (register_lookup (R_bitvector_64 mtime) rs3),
                (register_lookup (R_bitvector_64 mip) rs3).
        by iFrame "Hcy3 Hti3 Hip3".
    }
  Qed.

  Lemma wp_instr_s_sconf_clock
      (m : regfile) (n : nat) (b b' : bool)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : CpuId -> mword 64 -> mword 64 -> regfile -> nat -> iProp Σ) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    ▷ wp_next b p (sconf_step_obl_clock m n b b' pc is_rvc i R) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr H".
    destruct b.
    - (* ---- b = true: the interrupt-absorbing engine.  The whole bundle goes
           in and the callback goes on unchanged -- the shapes coincide, which
           is what the bundle bought. ---- *)
      iAssert (⌜ is_aligned_vaddr (Virtaddr pc) 2 = true ⌝)%I as %Hal2.
      { iDestruct "Hinstr" as "[%Hnlpad Hr]".
        iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
        iEval (rewrite /instr_bytes) in "Hbytes".
        iDestruct "Hbytes" as "[%H2al _]". iPureIntro. exact H2al. }
      assert (Hpc0 : ret_pc pc = pc)
        by (unfold ret_pc; exact (update_bit0_zero_of_aligned2 pc Hal2)).
      iApply (wp_instr_s_intr_clock m n pc is_rvc i b' R Hpc0
                with "Hcg Hpc Hinstr").
      iExact "H".
    - (* ---- b = false: the dispatch-None engine, SIE=0 from the ghost ---- *)
      iApply (wp_instr_s_sconf_off_clock m n pc is_rvc i b' R
                with "Hcg Hpc Hinstr").
      iExact "H".
  Qed.

  (* ...and the CLOCK-FREE reading, which is what the 68 call sites use. *)
  Lemma wp_instr_s_sconf
      (m : regfile) (n : nat) (b b' : bool)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : CpuId -> mword 64 -> mword 64 -> regfile -> nat -> iProp Σ) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    ▷ wp_next b p (sconf_step_obl m n b b' pc is_rvc i R) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr H".
    iApply (wp_instr_s_sconf_clock m n b b' pc is_rvc i R
              with "Hcg Hpc Hinstr [H]").
    (* the rename has to come AFTER the sibling application; see §3 *)
    rename CID into CID0.
    iNext. iIntros (CID Hs).
    iDestruct (wp_next_at b p _ CID Hs with "H") as "Hb".
    iEval (rewrite /sconf_step_obl) in "Hb".
    iDestruct "Hb" as "[Hobl Hcont]".
    rewrite /sconf_step_obl_clock.
    iSplitR "Hcont"; [| iExact "Hcont" ].
    iIntros "Hsc Hcap Hfile HPC HnPC Hresv Hclk".
    iApply (swp_mono (CID := CID) with "[Hclk] [-]");
      [| iApply ("Hobl" with "Hsc Hcap Hfile HPC HnPC Hresv") ].
    iIntros (e) "(-> & Hres)".
    iDestruct "Hres" as (npc ms' m' n')
      "(HPC & HnPC & Hresv2 & Hsc' & Hcap' & Hfile' & HRv)".
    iSplitR; [done|]. iExists npc, ms', m', n'. iFrame.
  Qed.

  (* =================================================================== *)
  (* §3 The generic gpr-write engines over the funnel.  Premise              *)
  (* [ops_ok b rd rsa rsb] (IntrDefs.v), which occupies the slot the old     *)
  (* [rd <> csp_rs1] did, so no call site changes arity:                     *)
  (*   - WRITE side, its [rd_ok rd] conjunct: [sie_cap] is keyed on sp and   *)
  (*     transported across non-sp writes by [sie_cap_retarget] (sp-moving   *)
  (*     instructions re-carve their stack explicitly instead), and the      *)
  (*     register file PINS tp (HartTp.v), so a generic write may target     *)
  (*     neither.                                                           *)
  (*   - READ side, its two [src_ok b] conjuncts: the engine reads           *)
  (*     [rget m rsa] / [rget m rsb], and [rget] depends on the AMBIENT HART *)
  (*     at exactly tp.  Nothing here consumes that yet -- the σ-callback    *)
  (*     below still sits at the caller's hart, so the two spellings         *)
  (*     coincide.  It is landed now because the LATER move of that callback *)
  (*     inside [wp_next] is what makes them differ, and doing the leaf      *)
  (*     sweep separately keeps the two changes independently reviewable.    *)
  (*     DO NOT DROP IT AS REDUNDANT; see IntrDefs.rget_src_indep for the    *)
  (*     fact it buys.                                                      *)
  (* The continuation is wrapped in [wp_next b]: at [b = true] the           *)
  (* instruction can be trapped and the thread resumed on a DIFFERENT hart,  *)
  (* and every resource inside the lambda is then about THAT hart (the       *)
  (* binder is named [CID]) -- which is precisely why the read side needs a  *)
  (* premise at [b = true] and needs nothing at [b = false].                 *)
  (* =================================================================== *)
  (* =================================================================== *)
  (* §3 The generic gpr-write engines over the funnel.  Premise
     [ops_ok b rd rsa rsb] (IntrDefs.v) is unchanged and keeps both its jobs:
     its [rd_ok rd] conjunct (the WRITE side) is what [sie_cap_retarget] and
     the tp pin need, and its two [src_ok b] conjuncts (the READ side) are
     what let a caller state [wval] in terms of [rget m rs] at ITS hart while
     the walk below runs at the hart a trap returned to.                     *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    (* THE INSTRUCTION'S OWN OBLIGATION, at the [swp] layer.  It replaces the
       [forall s_pc, <three lookups> -> exec (execute base) s_pc = ...] premise
       the whole-cycle engine took, and it HAD to: an [exec] fact quantifies
       over the START state only, while a per-node walk may be interfered with
       between nodes, so nothing bridges the two.  [WpMmodeSwpBase]'s
       catalogue is how a caller discharges this in one line per instruction
       family.
       IT IS ∀-QUANTIFIED OVER THE HART because the engine delivers
       [gpr_file (tp_pin m)] at the hart the LAST trap returned to, and
       [tp_pin] is hart-indexed; away from tp the walk does not see the
       difference, which is exactly what [ops_ok]'s source guards say. *)
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   gpr_file (<[Regidx rd := regval_into_reg wval]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops) "Hex Hcg Hpc Hinstr Hcont".
    pose proof (ops_ok_rd _ _ _ _ Hops) as Hrdok.
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_instr_s_sconf m n b b pc true base
              (fun _ npc ms' m' n' => ⌜npc = add_vec_int pc 2⌝ ∗
                                ⌜m' = <[Regidx rd := regval_into_reg wval]> m⌝ ∗
                                ⌜n' = n⌝)%I
              with "Hcg Hpc Hinstr [Hex Hcont]").
    iNext.
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside the proof, so [rename] moves it out of
       the way -- which the STATEMENT never sees, so every caller that names
       this leaf's hart as [(CID := ...)] keeps working.  It has to come AFTER
       the funnel application: inside a Section, a reference to a SIBLING
       lemma is resolved through the section variables BY NAME. *)
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "Hex".
    - (* the instruction: hand the walk the file, take the written one back *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iDestruct ("Hex" $! CID with "Hcert Hfile") as "Hexx".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap HPC HnPC Hresv] [Hexx]");
        [| iExact "Hexx" ].
      iIntros (e) "(-> & Hfile)".
      iSplitR; [done|].
      iAssert (sconf (CID := CID)) with "[Hsc]" as "Hsc2".
      { rewrite /sconf. iFrame "Hhw Hminv Hsc". }
      iDestruct (sconf_at_priv_open (CID := CID) with "Hsc2") as (ms') "Hscp".
      iExists (add_vec_int pc 2), ms',
              (<[Regidx rd := regval_into_reg wval]> m), n.
      iFrame "HPC HnPC Hresv Hscp".
      iSplitL "Hcap".
      { iApply (sie_cap_retarget m
                  (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap"). }
      iSplitL "Hfile".
      { iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp))
          in "Hfile". iExact "Hfile". }
      done.
    - (* the continuation: the engine resumes on the hart [Hs] names *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & ->)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* the 4-byte (base-encoding) variant: pc advances by 4 *)

  (* =================================================================== *)
  (* §4 PILOT leaves + the straight-line pilot: the same three chained    *)
  (* instructions as the old SIE=1-only pilot, now SIE-AGNOSTIC -- the    *)
  (* proof is identical at either SIE value, and needs NO sret-target or  *)
  (* menvcfg premises (both derived inside the funnel).                   *)
  (* =================================================================== *)

  Lemma wp_cli_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 6) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Hwval) "Hcg Hpc Hinstr Hcont".
    (* c.li reads x0 and nothing else, so the engine's source guard is
       DERIVED here rather than demanded of the caller: this leaf keeps its
       plain [rd_ok rd] premise. *)
    pose proof (ops_ok_conc b rd (zero_extend' 5 ('b"00"))
                  (zero_extend' 5 ('b"00")) Hrdok
                  ltac:(rdok_tpne) ltac:(rdok_tpne)) as Hops.
    iApply (wp_gpr_write_s_sconf pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) wval m n b
              Hrd Hops with "[] Hcg Hpc Hinstr Hcont").
    rename CID into CID0.
    (* THE INSTRUCTION, at any hart: read rs1 = x0, add the immediate, write
       rd.  [WpMmodeSwpBase.swp_execute_rw] is the node shape; the [eq_refl]
       is the model's own spelling of ITYPE's reduction. *)
    iIntros (CID) "#Hcert Hf".
    iDestruct (gpr_file_x0 (CID := CID) (tp_pin (CID := CID) m)
                 (zero_extend' 5 ('b"00"))
                 ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    iApply (swp_mono (CID := CID) with "[] [Hf]");
      [| iApply (swp_execute_rw (CID := CID) (zero_extend' 5 ('b"00")) rd
                   (tp_pin (CID := CID) m)
                   (execute (ITYPE (sign_extend' 12 imm,
                                    Regidx (zero_extend' 5 ('b"00") : mword 5),
                                    Regidx rd, ADDI)))
                   RETIRE_SUCCESS
                   (fun a => add_vec a (sign_extend' 64 (sign_extend' 12 imm)))
                   eq_refl Hrd with "Hcert Hf") ].
    iIntros (e) "[-> Hf]". iSplitR; [done|].
    rewrite Hx0 Hwval. iExact "Hf".
  Qed.

  (* straight line of THREE instructions -- addi a5,a5,imm1 (4 bytes);
     c.li a4,imm2 (2 bytes); addi a4,a4,imm3 (4 bytes) -- at EITHER SIE
     value: with interrupts enabled an arbitrary number of pending
     interrupts is absorbed before each instruction, with them disabled
     this is the ordinary dispatch-None execution; the proof does not
     mention the mode. *)

End WpSmodeIntr.
