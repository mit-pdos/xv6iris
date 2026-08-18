(* UserStepFull.v -- the UNIFIED STEP WRAPPER of the safety tier: the one
   place that turns [UserExec.user_step_obligation_active] into a single
   per-node cycle.

   POST-PORT SHAPE.  There is no [wp_exec_step_minstret] and no
   [mstate_interp] any more, so this file no longer names a machine state,
   a fupd mask or a step relation.  It drives ONE rule --
   [HartStepFull.swp_exec_step_full], the six-armed cycle -- at the user
   tier's footprint [UserFrame.u_Drw]/[u_Dro]/[u_Df], and everything below
   the cycle (the dispatch, the fetch, the decode, the execute and the four
   trap towers) is the obligation [active_class], discharged in
   UserActiveClass.v.

   THE WIRES ARE NOT BORROWED HERE ANY MORE.  [wire_inv] survives as a
   premise (the statement of [wp_user_step_active] is unchanged) but is
   UNUSED: per-node stepping answers [dispatchInterrupt]'s two wire reads
   from the hart's own read-only frame ([HartRunFull.swp_run_hart_active_U]
   takes the wire VALUES and a [goodb] certificate for them), so no
   invariant has to be opened across the step.  [minstret_inv] is [emp] and
   [active_class]' mask parameter [Ei] is likewise dead; both are kept so
   that no consumer of this file has to change.

   THE THREE PIECES.

   §1 [u_land] -- the pure [Q] the cycle rule is instantiated at.  It says
      exactly what [swp_exec_step_full] DEMANDS of the landing file and
      nothing more (the hart is still ACTIVE, and [minstret_increment]
      holds the flag the prelude computed); everything else the wrapper
      needs to know about the outcome rides in the payload instead, because
      only the classification knows which of the six arms ran.

   §2 [u_step_psi] -- the payload [Psi].  It is a CLOSER: hand it the file
      the cycle landed on, the frame at that file and the two
      continuations, and it produces the [WP].  Making the payload a closer
      rather than a description is what keeps this file short: the wrapper
      never has to case-split on the arm, and the classification -- which
      does know the arm, the new tree and the new byte map -- re-establishes
      [user_inv] or [user_trap_frame] itself.

   §3 [u_open] + [active_class] + [wp_user_step_active].  [u_open] is
      everything the user machine owns BESIDE the register frame: the pmp
      re-intro wand, the six persistent config cells, the page-table claims,
      the bytes and the closer that puts [user_pt_inv] back together at
      whatever tree/map the step lands on.  [active_class] is literally
      [swp_exec_step_full]'s body slot at this instantiation. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv WireInv WpGpr RegFile.
Require Import SmodeCore WpIntrCore.
Require Import HartSwp HartLift HartSpan HartMCycle HartStepFull HartRunFull.
Require Import UserFrame UserClassifyAsm.
Require Import PtreeType PtTree SmodePte UptTree UserPtTree UserExec.
Require Import HartMemRun PtBytes UserBytes UserStep.
Local Open Scope Z_scope.
Import Defs.

Section UserStepFull.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  (* ------------------------------------------------------------------- *)
  (* §1 [Q]: the two facts [swp_exec_step_full] asks of the landing file.  *)
  (* ------------------------------------------------------------------- *)
  Definition u_land (rs1 : regstate) (_ : Step) (rs2 : regstate) : Prop :=
    register_lookup hart_state rs2 = HART_ACTIVE tt /\
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1).

  (* ------------------------------------------------------------------- *)
  (* §2 [Psi]: the payload, as a CLOSER.                                   *)
  (*                                                                       *)
  (* [rs2] is the file the ARM landed on; [rs3] is the file after the       *)
  (* cycle's tail (the pc tick and the minstret bump), which the rule       *)
  (* relates to [rs2] only up to [tsf_post] and agreement off the three     *)
  (* clock cells -- so the closer takes that relation as its first          *)
  (* argument.  It also carries the reservation back: the cycle rule's      *)
  (* continuation does not return one (the cycle boundary drops it), and    *)
  (* [user_inv]'s [pc_is] needs it.                                          *)
  (* ------------------------------------------------------------------- *)
  Definition u_step_psi (rs1 rs2 : regstate) : iProp Σ :=
    (resv_any cpu_id ∗
     (∀ rs3 : regstate,
        ⌜∃ rsP : regstate, tsf_post (u_land rs1) rs2 rsP /\
           reg_agree_on ((u_Drw ∪ u_Dro) ∖ tk_clock3) rs3 rsP⌝ -∗
        hreg_frame rs3 u_Drw -∗
        hreg_frame_ro (u_Df (uc_dqc C)) rs3 u_Dro -∗
        resv_any cpu_id -∗
        ((user_inv C pt Rut -∗ WP (Loop : expr riscv_lang)) ∧
         (user_trap_frame C pt Rut -∗ WP (Loop : expr riscv_lang))) -∗
        WP (Loop : expr riscv_lang)))%I.

  (* ------------------------------------------------------------------- *)
  (* §3a Everything the user machine owns BESIDE the register frame.       *)
  (* Exactly [UserStep.u_close_inv]'s non-frame premise list.              *)
  (* ------------------------------------------------------------------- *)
  Definition u_open (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter) : iProp Σ :=
    ((pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗ pmp_config (ud_root pt)) ∗
     medeleg ↦ᵣ□ uc_medeleg C ∗
     senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) ∗
     mstateen0 ↦ᵣ□ (mword_of_int 0 : mword 64) ∗
     (R_bitvector_32 sstateen0) ↦ᵣ□ (mword_of_int 0 : mword 32) ∗
     (R_bitvector_32 mcounteren) ↦ᵣ□ mcenv ∗
     (R_bitvector_32 scounteren) ↦ᵣ□ scenv ∗
     mhpmcounter ↦ᵣ□ hpm ∗
     pt_claims 2 t ∗ bytes_own mm ∗
     (∀ (t' : ptree) (mm' : PtBytes.pamap) (tlbvec' : type_of_register tlb),
        ⌜u_mem_step pt t t' mm mm'⌝ -∗
        ⌜tlb_ok_pt (mword_of_int 0) t' tlbvec'⌝ -∗
        upt_regs pt usatp tlbvec' -∗ bytes_own mm' -∗ user_pt_inv pt))%I.

  (* ------------------------------------------------------------------- *)
  (* §3b The classification obligation.                                    *)
  (*                                                                       *)
  (* This IS [HartStepFull.swp_exec_step_full]'s body slot, at the user     *)
  (* tier's footprint and at [Q := u_land rs1] / [Psi := u_step_psi rs1].   *)
  (* Everything is stated at [rs1] -- the file BEFORE the cycle's minstret  *)
  (* prelude -- and the frame arrives at [rsA], the file after it, with     *)
  (* the agreement between them as a premise: the prelude writes only       *)
  (* [minstret_increment], so every pin transports, and stating the pins    *)
  (* at [rs1] is what lets the wrapper discharge them all by [reflexivity]  *)
  (* at its concrete entry file.                                            *)
  (*                                                                       *)
  (* [Ei] IS DEAD.  The swp layer is not mask-indexed; the parameter is     *)
  (* kept only so that [wp_user_step_active]'s statement does not move.     *)
  (* ------------------------------------------------------------------- *)
  Definition u_arm_res (rs1 rs2 : regstate) : iProp Σ :=
    (hreg_frame rs2 u_Drw ∗ hreg_frame_ro (u_Df (uc_dqc C)) rs2 u_Dro ∗
     u_step_psi rs1 rs2)%I.

  Definition u_step_post (rs1 : regstate) (st : Step) : iProp Σ :=
    (∃ rs2 : regstate, ⌜u_land rs1 st rs2⌝ ∗
       match st with
       | Step_Execute (Retire_Success tt, _) => u_arm_res rs1 rs2
       | Step_Pending_Interrupt (i, p) =>
           swp (handle_interrupt i p) (fun _ => u_arm_res rs1 rs2)
       | Step_Execute (Illegal_Instruction tt, ib) =>
           swp (handle_exception (zero_extend' 64 ib) (E_Illegal_Instr tt))
             (fun _ => u_arm_res rs1 rs2)
       | Step_Execute (rv64d_types.Trap (p, exc, pcx), _) =>
           swp (Defs.bind (exception_handler p exc pcx) set_next_pc)
             (fun _ => u_arm_res rs1 rs2)
       | Step_Fetch_Failure (Virtaddr xv, e) =>
           swp (handle_exception xv e) (fun _ => u_arm_res rs1 rs2)
       | Step_Execute (Enter_Wait wr, ib) =>
           ⌜wait_is_nop wr = false⌝ ∗ u_arm_res rs1 rs2
       | _ => False
       end)%I.

  Definition active_class (Ei : coPset) : iProp Σ :=
    (□ (∀ (rs1 rsA : regstate) (t : ptree) (mm : PtBytes.pamap)
          (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
          (paddr : type_of_register pmpaddr_n) (mcenv scenv : mword 32)
          (hpm : type_of_register mhpmcounter),
        ⌜register_lookup hart_state rs1 = HART_ACTIVE tt⌝ -∗
        ⌜register_lookup cur_privilege rs1 = User⌝ -∗
        ⌜user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs1)⌝ -∗
        ⌜register_lookup (R_bitvector_64 PC) rs1
           = register_lookup (R_bitvector_64 nextPC) rs1⌝ -∗
        ⌜register_lookup (R_bitvector_64 stvec) rs1 = uc_stvec C⌝ -∗
        ⌜register_lookup (R_bitvector_64 mie) rs1 = uc_mie C⌝ -∗
        ⌜register_lookup (R_bitvector_64 mideleg) rs1 = uc_mideleg C⌝ -∗
        ⌜register_lookup (R_bitvector_64 menvcfg) rs1 = MENVCFG_S⌝ -∗
        ⌜register_lookup (R_bitvector_64 satp) rs1 = usatp⌝ -∗
        ⌜register_lookup pmpcfg_n rs1 = pcfg⌝ -∗
        ⌜register_lookup pmpaddr_n rs1 = paddr⌝ -∗
        ⌜u_exec_pins pt t rs1⌝ -∗
        ⌜u_mem_wf pt t mm⌝ -∗
        ⌜reg_agree_on (u_Drw ∪ u_Dro) (wrap_pre rs1) rsA⌝ -∗
        resv_frag cpu_id None -∗
        hreg_frame rsA u_Drw -∗
        hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
        u_open t mm usatp pcfg paddr mcenv scenv hpm -∗
        Rut pt -∗
        swp (run_hart_active 0) (u_step_post rs1)))%I.


  (* ------------------------------------------------------------------- *)
  (* §3c THE WRAPPER.  Statement unchanged from the pre-port file; the      *)
  (* proof is now four moves: open the three bundles into one register      *)
  (* file, drive [swp_exec_step_full] once, hand its body slot to           *)
  (* [active_class], and let the payload's closer finish.  There is no      *)
  (* case analysis on the arm here -- that is the point of making [Psi] a   *)
  (* closer.                                                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_user_step_active :
    hw_config -∗
    minstret_inv -∗
    wire_inv -∗
    active_class (⊤ ∖ ↑minstretN ∖ ↑wireN ∖ ↑clockN) -∗
    user_step_obligation_active C pt Rut.
  Proof.
    iIntros "#Hhw #Hmin #Hwinv #Hclass".
    iIntros "!>" (ms_v sc_v stval_v sepc_v va g) "%Hmsok Hregs Hupt Hcfg Hrut Hk".
    (* ---- take the three bundles apart ---- *)
    rewrite /user_regs u_regs_open.
    iDestruct "Hregs" as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & HPC & HnPC
                           & Hgpr & Hmr & Hcr & Hresv)".
    iDestruct "Hmr" as (mst mi mc micfg) "(Hminstret & Hmincr & #Hmcnt & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hmcycle & Hmtime & Hmip)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & #Hmedl & Hmenv & #Hsenv &
                          #Hmste & #Hsste & Hctr & Hhpmb)".
    iDestruct "Hctr" as (mcenv scenv) "[#Hmcen #Hscen]".
    iDestruct "Hhpmb" as (hpm) "#Hhpm".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenvhw &
        _ & _ & _ & _ & %Hpmaall & _ & _ & %Helpne & _ &
        %Hmisaeq & %Hseceq & _ & #Hcert)".
    iDestruct (user_pt_inv_bytes pt with "Hupt") as (t mm usatp tlbvec)
      "(%Hwf & %Hsatpok & %Htlbok & (Hsatp & Htlb & Hpmp) & #Hclaims & Hbytes
        & Hclose)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HpA & %Hpord & %HpX & %HpW & %HpR & %Hpcov)".
    iAssert (pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗ pmp_config (ud_root pt))%I
      as "Hpmpi".
    { iApply (pmp_config_intro (ud_root pt) pcfg paddr
                HpA Hpord HpX HpW HpR Hpcov). }
    (* ---- the entry file ---- *)
    set (RS := u_rs g (HART_ACTIVE tt) mi mc (mword_of_int 0 : mword 32)
                 mcenv scenv hpm elp0 pmar0 None pcfg paddr tlbvec
                 va va ms_v sc_v stval_v sepc_v mst cy ti ip micfg
                 misa0 mseccfg0 (mword_of_int 0 : mword 64)
                 (uc_stvec C) (uc_mie C) (uc_mideleg C) (uc_medeleg C)
                 MENVCFG_S (mword_of_int 0 : mword 64) usatp).
    iDestruct (u_frames_intro RS (uc_dqc C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (u_rs_pins_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_tick _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_cfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_hw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_pt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 with "Hhs Hpriv Hms Hsc Hstval Hsepc HPC HnPC Hgpr
                       Hminstret Hmincr Hmcnt Hmicfg Hmcycle Hmtime Hmip
                       Hstvec Hmie Hmdl Hmedl Hmenv Hmste Hsste
                       Hmcen Hscen Hhpm
                       Hmisa Hmseccfg Hpma Hhtif Help Hsenv
                       Hsatp Htlb Hpcfg Hpaddr")
      as "[Hrw Hro]".
    (* ---- the ambient pins, all [reflexivity] at the entry file ---- *)
    assert (Hpins : u_exec_pins pt t RS).
    { rewrite /u_exec_pins /u_hw_pins /u_cfg_pins /u_pt_pins.
      split_and!;
        [ exact Hmisaeq | exact Hseceq | reflexivity | reflexivity
        | exact Hpmaall | exact Helpne
        | reflexivity | reflexivity
        | exists usatp; split; [ exact Hsatpok | reflexivity ]
        | exact HpA | exact Hpord | exact HpX | exact HpW | exact HpR
        | exact Hpcov
        | exact Htlbok ]. }
    (* ---- the one cycle ---- *)
    iApply (swp_exec_step_full u_Drw u_Dro (u_Df (uc_dqc C)) RS (wrap_pre RS)
              (u_land RS) (u_step_psi RS)
              u_disj u_w_cy u_w_ti u_w_ip u_in_priv u_w_hart u_in_hart
              u_in_mc u_in_micfg u_w_mi u_in_mi u_w_ms u_in_ms
              u_w_PC u_in_PC u_in_nPC
              (eq_refl : register_lookup hart_state RS = HART_ACTIVE tt)
              ltac:(intros st rs2 H; exact (proj1 H))
              ltac:(intros st rs2 H; exact (proj2 H))
              ltac:(intros r _; reflexivity)
              with "Hcert Hresv Hrw Hro [Hpmpi Hbytes Hclose Hrut] [Hk]").
    - (* the classification, with everything the machine owns beside the frame *)
      iIntros "Hfrag Hrw Hro".
      iApply ("Hclass" $! RS (wrap_pre RS) t mm usatp pcfg paddr mcenv scenv hpm
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      Hfrag Hrw Hro [Hpmpi Hbytes Hclose] Hrut");
        [ reflexivity | reflexivity | exact Hmsok | reflexivity | reflexivity
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | exact Hpins | exact Hwf | intros r _; reflexivity
        | rewrite /u_open;
          iFrame "Hpmpi Hmedl Hsenv Hmste Hsste Hmcen Hscen Hhpm Hclaims
                  Hbytes Hclose" ].
    - (* the payload's closer does the rest *)
      iNext. iIntros (rs3 rs2) "%Hag Hrw Hro [Hresv Hcl]".
      iApply ("Hcl" $! rs3 with "[%] Hrw Hro Hresv Hk"). exact Hag.
  Qed.

End UserStepFull.
