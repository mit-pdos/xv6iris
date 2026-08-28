(* WpSFrames.v -- the S-mode BUNDLE ⇄ FRAMES bridge.

   [InstrBytes.mm_frames_intro] / [_elim] is the M-mode twin, and this is the
   same job one mode over: it is the ONLY place the S-mode resource algebra is
   touched.  Above it, everything speaks in frames ([HartSFrame.s_rs] and its
   footprint); below it, everything speaks in the kernel's bundles.

   FOUR OWNERS, and between them they cover the tower exactly:

     [sconf]                 cur_privilege (Supervisor), mstatus, mie,
                             mideleg, menvcfg -- and [hw_config] with the
                             pinned misa / mseccfg / pma_regions / htif /
                             elp / senvcfg inside it
     [pc_is]                 PC, nextPC, minstret, minstret_increment,
                             mcountinhibit, minstretcfg, mcycle, mtime, mip
     [KptShare.tlb_res_pt]   satp and tlb -- the two cells M-mode does not
                             have -- plus [pmp_config] (pmpcfg_n, pmpaddr_n)
     [hart_state ↦ᵣ]         handed in separately, as the M-mode twin does

   WHAT COMES BACK OUT UNUSED is as important as what goes in: the mstatus
   SIE ghost and [sret_tie], [tlb_snap_ok], [kpt_inv] and [minstret_inv] are
   not cells and cannot ride in a frame, so they are returned to the caller
   untouched.  [tlb_snap_ok] is what a later TLB HIT needs (it says the entry
   found is legitimate for the installed tree) and [kpt_inv] is what a MISS
   needs (it supplies the PTE reads), so both must survive the round trip
   rather than be consumed here. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv.
Require Import HartSwp HartLift HartSpan HartSFrame.
Require Import HartMCycle HartStepAny HartRunGen HartSTrans.
Require Import SmodeCore.
(* [smode_config] lives in SmodeCore; its bridge is below *)
Require Import InstrBytes IntrDefs KptShare.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* the misalignment tests' spelling, as [HartMFetch] and [HartSTrans] use it *)

Section sframes.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ------------------------------------------------------------------ *)
  (* ...and back.  [InstrBytes.mm_frames_elim]'s twin.  The non-cell       *)
  (* resources come back IN (they never rode in the frames), and the two    *)
  (* files may differ: the fetch may have filled the TLB, so [tlbv'] is a   *)
  (* fresh parameter and it is [tlb_snap_ok tlbv'] the caller owes -- which *)
  (* is precisely what the fill's own rule must re-establish.               *)
  (* ------------------------------------------------------------------ *)


  (* ------------------------------------------------------------------ *)
  (* The two tower transports the cycle rule consumes, [InstrBytes]'s      *)
  (* [mm_tick_agree] / [mm_pre_agree] one for one.  Each is ONE            *)
  (* [s_rs_agree] application, so the 25-way set reasoning is paid here     *)
  (* rather than inside the wrapper's arms.                                *)
  (* ------------------------------------------------------------------ *)

  (* the tail: [wrap_post] commits nextPC into PC and sets minstret, then the
     tick moves mcycle/mtime/mip -- which is exactly what the [∖ tk_clock3]
     in the incoming agreement leaves unpinned *)
  Lemma s_tick_agree (pc npc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) (tlbv : type_of_register tlb)
      (mi : mword 64) (rs : regstate) :
    reg_agree_on ((s_Drw ∪ s_Dro) ∖ tk_clock3) rs
      (wrap_post (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                    mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) mi) ->
    reg_agree_on (s_Drw ∪ s_Dro) rs
      (s_rs npc npc mi bmi
         (register_lookup (R_bitvector_64 mcycle) rs)
         (register_lookup (R_bitvector_64 mtime) rs)
         (register_lookup (R_bitvector_64 mip) rs)
         mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0
         satp0 mie0 mdv0 menv0 tlbv).
  Proof.
    intros Hag. apply s_rs_agree.
    all: try reflexivity.
    all: (etransitivity;
          [ apply Hag; rewrite /s_Drw /s_Dro /tk_clock3; set_solver | ]).
    all: try (by rewrite wrap_post_PC s_rs_nPC).
    all: try (by rewrite wrap_post_ms).
    all: rewrite wrap_post_other;
      [| vm_compute; reflexivity | vm_compute; reflexivity ].
    all: by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
              ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
              ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec
              ?s_rs_pma ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp
              ?s_rs_mie ?s_rs_mdl ?s_rs_menv.
  Qed.

  (* [s_tick_agree] AT THE BARE FRAME.  The tick hands its
     agreement back over [(Drw ∪ Dro) ∖ tk_clock3], and at [s_Drwb] that set
     has NO tlb in it -- so the landing tower cannot name the value the cycle
     started with and names the landing file's instead.  That is sound
     exactly because a frame at [s_Drwb] does not contain the cell; the proof
     is [s_tick_agree]'s with the tlb case closed by [reflexivity]. *)
  Lemma s_tick_agree_b (pc npc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) (tlbv : type_of_register tlb)
      (mi : mword 64) (rs : regstate) :
    reg_agree_on ((s_Drwb ∪ s_Dro) ∖ tk_clock3) rs
      (wrap_post (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                    mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv)
         mi) ->
    reg_agree_on (s_Drw ∪ s_Dro) rs
      (s_rs npc npc mi bmi
         (register_lookup (R_bitvector_64 mcycle) rs)
         (register_lookup (R_bitvector_64 mtime) rs)
         (register_lookup (R_bitvector_64 mip) rs)
         mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0
         satp0 mie0 mdv0 menv0 (register_lookup tlb rs)).
  Proof.
    intros Hag. apply s_rs_agree.
    all: try reflexivity.
    all: (etransitivity;
          [ apply Hag; rewrite /s_Drwb /s_Dro /tk_clock3; set_solver | ]).
    all: try (by rewrite wrap_post_PC s_rs_nPC).
    all: try (by rewrite wrap_post_ms).
    all: rewrite wrap_post_other;
      [| vm_compute; reflexivity | vm_compute; reflexivity ].
    all: by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
              ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
              ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec
              ?s_rs_pma ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp
              ?s_rs_mie ?s_rs_mdl ?s_rs_menv.
  Qed.

  (* the head: [wrap_pre] overwrites minstret_increment and nothing else *)
  Lemma s_pre_agree (pc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) (tlbv : type_of_register tlb) :
    reg_agree_on (s_Drw ∪ s_Dro)
      (wrap_pre (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv))
      (s_rs pc pc ms
         (minstret_inc_flag mc micfg Supervisor)
         cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0
         satp0 mie0 mdv0 menv0 tlbv).
  Proof.
    apply s_rs_agree.
    all: try (rewrite wrap_pre_mi;
              by rewrite s_rs_mc s_rs_micfg s_rs_priv).
    all: try (rewrite wrap_pre_other; [| vm_compute; reflexivity ]).
    all: by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_cy ?s_rs_ti ?s_rs_ip
              ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
              ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec
              ?s_rs_pma ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp
              ?s_rs_mie ?s_rs_mdl ?s_rs_menv.
  Qed.


  (* ==================================================================== *)
  (* s_cycle -- THE S-MODE INSTANCE of [swp_exec_step_decode_execute].      *)
  (*                                                                      *)
  (* [WpInstr.mm_cycle]'s twin, and its header predicted exactly this: the *)
  (* S-mode wrapper writes its own thirty-line twin of THAT rule and reuses *)
  (* the generic one unchanged.  So it does.  Everything about the cycle    *)
  (* -- boundary, interrupt check, minstret, tick, PC commit -- is in the  *)
  (* generic rule, which knows nothing about privilege regimes; all this   *)
  (* adds is the two bundle<->frame bridges above.                         *)
  (* ==================================================================== *)
  Local Ltac srs :=
    by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
       ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
       ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
       ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
       ?s_rs_menv.



  (* ==================================================================== *)
  (* wp_instr_s -- AND WHY [s_cycle] IS THE WRONG BASE FOR IT.              *)
  (*                                                                      *)
  (* I built [s_cycle] as [WpInstr.mm_cycle]'s mirror and then tried to     *)
  (* fill its body with [HartRunGen.swp_run_hart_active_gen].  It does not  *)
  (* fit, and the mismatch is the point rather than an accident:            *)
  (*                                                                      *)
  (*   [s_cycle] sits on [HartMCycle.swp_exec_step_decode_execute], whose   *)
  (*   body is RETIRE-ONLY -- one arm, [Step_Execute (RETIRE_SUCCESS, w)].  *)
  (*   [swp_run_hart_active_gen]'s conclusion is a DISJUNCTION, because at  *)
  (*   Supervisor the dispatch reads the PLIC wires and the machine, not    *)
  (*   the caller, picks the arm.                                          *)
  (*                                                                      *)
  (* M-mode gets away with the one-armed base for a real reason             *)
  (* ([HartMDispatch.swp_dispatchInterrupt_M] short-circuits before the     *)
  (* wires, so [None] is pinned).  S-MODE HAS NO SUCH SHORTCUT, so the      *)
  (* general wrapper must sit on [HartStepAny.swp_exec_step_any] instead --  *)
  (* whose body already MATCHES on the step and whose trap arm carries       *)
  (* [swp (handle_interrupt i p) ..], which is exactly what                  *)
  (* [swp_run_hart_active_gen]'s [Qi] slot is for.                          *)
  (*                                                                      *)
  (* SO THE NEXT PIECE IS [s_cycle_any]: this file's [s_cycle] with          *)
  (* [swp_exec_step_any] in place of [swp_exec_step_decode_execute] and the  *)
  (* post-file a PREDICATE [Q] rather than a parameter (the two arms land on *)
  (* different files).  Everything else here is reusable unchanged: the      *)
  (* bridges, the three transports, the frame extensions.                   *)
  (*                                                                      *)
  (* [s_cycle] IS NOT WASTED.  It is exactly right wherever a caller CAN     *)
  (* rule out a trap -- a critical section with SIE clear -- and it is the   *)
  (* cheaper rule there.  It is simply not the general case at Supervisor.  *)
  (* ==================================================================== *)

  (* ==================================================================== *)
  (* s_cycle_any -- THE TWO-ARMED S-MODE CYCLE, and the base the general    *)
  (* wrapper actually needs (see the note above for why [s_cycle] is not).  *)
  (*                                                                      *)
  (* [HartStepAny.swp_exec_step_any] at the S-mode footprint and tower.     *)
  (* The post-file is a PREDICATE [Q], so the frames come back at an        *)
  (* ARBITRARY [rs3] agreeing with [wrap_post rs2 mi] off the clock cells   *)
  (* -- not at a tower.  The bundle rebuild ([s_frames_elim]) therefore     *)
  (* belongs to the CALLER, who knows which arm their [Q] admits and what   *)
  (* file it lands on; handing back a tower here would be pinning the arm   *)
  (* this rule exists not to pin.                                          *)
  (* ==================================================================== *)


  (* the reservation, carried past a body that does not see it: the frag
     the cycle handed the wrapper rides beside [Psi] into the continuation,
     through both arms of the dispatch. *)

  (* ==================================================================== *)
  (* wp_instr_s -- THE S-MODE WRAPPER, on the base that fits.              *)
  (*                                                                      *)
  (* [s_cycle_any] with the body filled by                                 *)
  (* [HartRunGen.swp_run_hart_active_gen], whose dispatch obligation the    *)
  (* caller discharges with [WpIntrCore.swp_dispatchInterrupt_S] and whose  *)
  (* fetch obligation [HartSTrans.swp_fetch_S] discharges.                  *)
  (*                                                                      *)
  (* THE TRAP ARM'S PAYLOAD IS THE CALLER'S [Qi], and its shape is forced:  *)
  (* the ∃ over the post-handler file sits OUTSIDE the [swp], because       *)
  (* [swp_exec_step_any]'s body puts it there -- a caller names the file    *)
  (* its handler lands on before running the handler, which is what a       *)
  (* handler spec gives it.                                               *)
  (*                                                                      *)
  (* Stated at the 4-ALIGNED NON-COMPRESSED shape; the other three are the  *)
  (* same rule over [swp_fetch_S_rvc2] / [_S_base2] and                     *)
  (* [swp_run_hart_active_gen_rvc].                                        *)
  (* ==================================================================== *)


  (* ==================================================================== *)
  (* wp_instr_s_rvc -- THE COMPRESSED SHAPE, same rule one shape over.      *)
  (*                                                                      *)
  (* Two differences from [wp_instr_s], both the model's rather than the    *)
  (* port's: nextPC is pc+2, and there are TWO execute obligations, because *)
  (* a compressed instruction EXPANDS -- [execute i] answers [ExecuteAs     *)
  (* other] and it is [other] that retires.  The fetch is the SAME rule     *)
  (* ([swp_fetch_S]): its [if isRVC] conclusion gives [F_RVC] here and      *)
  (* [F_Base] there, so 4-alignment needs no second fetch lemma.           *)
  (* ==================================================================== *)


  (* ==================================================================== *)
  (* wp_instr_s_rvc2 -- the 2-mod-4 COMPRESSED shape.                      *)
  (*                                                                      *)
  (* Identical to [wp_instr_s_rvc] but for the fetch: at a 2-mod-4 pc the   *)
  (* model reads ONE HALFWORD ([swp_fetch_S_rvc2]), so the text obligation  *)
  (* is a 2-byte read at the translated address rather than a 4-byte one.   *)
  (* The alignment premises invert accordingly, and misa.C is read by the   *)
  (* fetch itself here (the misalignment test does not short-circuit).      *)
  (* ==================================================================== *)


  (* ==================================================================== *)
  (* wp_instr_s_base2 -- the 2-mod-4 BASE shape, and the last of the four.  *)
  (*                                                                      *)
  (* THE ONLY ONE WITH TWO TRANSLATIONS, because it reads two halfwords at  *)
  (* two addresses -- and therefore the only one that threads an            *)
  (* INTERMEDIATE FILE: the first walk may already have filled the TLB, so  *)
  (* the second starts where the first landed.  Three TLB values appear in  *)
  (* the statement for that reason ([tlbv] -> [tlbv1] -> [tlbv']), which is *)
  (* the [rsf] thread at its widest.                                       *)
  (* ==================================================================== *)


  (* ==================================================================== *)
  (* THE OTHER S-MODE BUNDLE: [SmodeCore.smode_config].                    *)
  (*                                                                      *)
  (* [SmodeCorePt]'s engine runs over this one rather than [sconf], and the *)
  (* differences are all visible in the statement: its cells are held at a  *)
  (* FRACTION [dq] (which is why the cycle and wrapper rules above became   *)
  (* fraction-generic), its SIE ghost is at a PARAMETER gname, its [mie] is *)
  (* existential rather than pinned at [MIE_S] -- and it PINS SIE = false,   *)
  (* so a caller holding it can rule out a trap.  That last fact is why     *)
  (* [s_cycle] (one-armed) is the right base there and [s_cycle_any] is not *)
  (* needed.                                                              *)
  (*                                                                      *)
  (* The satp/tlb/pmp cells come from the same place as before, and at the  *)
  (* Sv39 instance that place IS the regime: [SRegime.kpt_share_regime_inv] *)
  (* proves [sr_inv (kpt_share_regime root) ⊣⊢ tlb_res_pt root] by          *)
  (* [reflexivity].                                                        *)
  (* ==================================================================== *)


End sframes.
