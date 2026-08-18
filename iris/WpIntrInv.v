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

     - PENDING: the trap itself is [swp_handle_interrupt_S] (§2 below; it is
       HERE rather than in [WpIntrCore] only so that iterating on it does not
       rebuild that file's ~600-file cone), a hand-walk of
       [handle_interrupt i Supervisor] over the trap CSRs
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

   THE RIDER IS KEYED ON THE BODY'S POST-FILE, and it has to be.  Both arms
   carry resources indexed by the file the cycle landed on -- the leaf's
   continuation by the pc it chose, the handler's entry package by the trap
   vector -- and a rider that is a bare [iProp] cannot say which file that
   was: the cycle rule's continuation only knows SOME [rs2] the body chose.
   [HartMCycle.wp_loop_cycle_ex] / [HartStepAny.swp_try_step_any_ex] hand
   [Psi rs2] back beside [rs2] itself, so the landing pc is an equation
   rather than an existential.

   THE CLOCK-BORROWING READING IS THE PRIMITIVE.  [wp_exec_step_intr_clock]
   lends the leaf the three clock cells (mcycle / mtime / mip) and takes them
   back; [wp_exec_step_intr] is that with the cells passed straight through.
   They live in the cycle's own footprint because the TICK writes them, but
   the tick runs at the cycle BOUNDARY, so within the instruction they are
   stable and lending them costs the engine nothing -- and [csrr time],
   [csrr sip] and [csrw stimecmp] (whose new mip comes out of device state)
   cannot be written without them.  The cycle rule's continuation constrains
   the landing file only OFF [tk_clock3], so nothing downstream sees it.
   The leaf-facing callback is ONE definition ([intr_cb_clock] / [intr_cb]),
   not three spelled copies: it appears in the engine's premise, in the
   rider's trap arm, and in the resource the S-mode run rule threads to
   whichever arm the machine picks.

   §5 adds [strans_regime_swp], the swp-layer instance of the S-mode tier's
   COMBINED translation slot -- see its own header for why each arm's satp
   MODE has to sit in the residue and not only in the side condition.

   The per-trap frame is the CONCRETE [intr_frame]: [stack_own] of depth AT
   LEAST [kv_frame_slots] below the interrupted sp -- the kernel must
   maintain that much free stack at every interrupts-enabled instruction.
   [kernelvec_handler_spec] proves the real kernelvec ([wp_kernelvec],
   ProofKernelvec.v) satisfies the contract; [SpecKernelvec.v] is the
   interface, [LinkKernelvec.v] the instantiation. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap
        ghost_map.
From iris.bi.lib Require Import fractional.
From iris.program_logic Require Import language lifting weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr RegFile HartTp WpMmodeLeafBase.
Require Import HartSwp HartLift HartSpan HartSpanChar HartRegNode
        HartMCycle HartStepAny HartRunGen HartSFrame HartSTrans HartMFrame
        HartGoodb WpDecodeBridge WpDecode DecodeTotalU CommonWalk ExecCommon
        WpGprMret.
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
  else DfracOwn 1.

Lemma i_Df_mc : i_Df (R_bitvector_32 mcountinhibit) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma i_Df_micfg : i_Df (R_bitvector_64 minstretcfg) = DfracDiscarded.
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
    ((R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs ∗
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
    rewrite !i_Df_mc !i_Df_micfg.
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

End IFrames.

Lemma i_sub_s : i_Drw ∪ i_Dro ⊆ s_Drw ∪ s_Dro.
Proof. rewrite /i_Drw /i_Dro /s_Drw /s_Dro. set_solver. Qed.

Lemma i_ck_PC : (R_bitvector_64 PC : register) ∈ (i_Drw ∪ i_Dro) ∖ tk_clock3.
Proof. rewrite /i_Drw /i_Dro /tk_clock3. set_solver. Qed.
Lemma i_ck_nPC : (R_bitvector_64 nextPC : register) ∈ (i_Drw ∪ i_Dro) ∖ tk_clock3.
Proof. rewrite /i_Drw /i_Dro /tk_clock3. set_solver. Qed.
Lemma i_ck_hart : (hart_state : register) ∈ (i_Drw ∪ i_Dro) ∖ tk_clock3.
Proof. rewrite /i_Drw /i_Dro /tk_clock3. set_solver. Qed.
Lemma i_ck_priv : (cur_privilege : register) ∈ (i_Drw ∪ i_Dro) ∖ tk_clock3.
Proof. rewrite /i_Drw /i_Dro /tk_clock3. set_solver. Qed.

(* every S-mode tower lookup, in one tactic *)
Ltac srs :=
  rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
    ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
    ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
    ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
    ?s_rs_menv.

(* THE TOWER IS OPAQUE TO UNIFICATION, and it has to be: [s_rs] is itself a
   25-deep [register_set] tower, so a [rewrite register_lookup_set] whose
   unifier may delta-unfold it peels INTO the tower and ends up comparing
   [cold_regs] against a value -- a hang, not an error. *)
#[local] Opaque s_rs.

(* peel a [register_set] tower down to a tower lookup.
   THE CLOSER IS TARGETED, and that is not a style choice: closing such a
   goal with the 25-way [srs] chain instead of the ONE lookup lemma it needs
   costs >100 s per goal (measured), because every failing [rewrite ?s_rs_x]
   unfolds the tower to look for its pattern. *)
Ltac peel1 :=
  first
    [ rewrite register_lookup_set
    | rewrite irrelevant_register_set; [ | vm_compute; reflexivity ] ].
(* EXACTLY TWO STEPS, never [repeat]: [s_rs] is itself a [register_set]
   tower, and a [repeat] peels straight into it. *)
Ltac peelset := try peel1; try peel1.
Ltac lkp L := peelset; rewrite L; reflexivity.
Ltac lkp0 := peelset; reflexivity.

(* the ONE file transport the engine needs: the cycle commits nextPC and the
   fetch may have filled the tlb, and the result is the tower again. *)
Lemma s_rs_set_nPC_tlb (pc npc npc' ms : mword 64) (bmi : bool)
    (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n) (mc : mword 32)
    (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
    (elp0 : type_of_register elp) (satp0 mie0 mdv0 menv0 : mword 64)
    (tlbv tv : type_of_register tlb) :
  reg_agree_on (s_Drw ∪ s_Dro)
    (register_set (R_bitvector_64 nextPC) npc'
       (register_set tlb tv
          (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
             senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv)))
    (s_rs pc npc' ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
       senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv).
Proof.
  apply s_rs_agree;
    [ lkp s_rs_PC | lkp0 | lkp s_rs_ms | lkp s_rs_mi | lkp s_rs_cy
    | lkp s_rs_ti | lkp s_rs_ip | lkp0 | lkp s_rs_priv | lkp s_rs_mst
    | lkp s_rs_hart | lkp s_rs_pcfg | lkp s_rs_paddr | lkp s_rs_mc
    | lkp s_rs_micfg | lkp s_rs_misa | lkp s_rs_sec | lkp s_rs_pma
    | lkp s_rs_htif | lkp s_rs_elp | lkp s_rs_senv | lkp s_rs_satp
    | lkp s_rs_mie | lkp s_rs_mdl | lkp s_rs_menv ].
Qed.

(* ===================================================================== *)
(* §2 THE TRAP, AS A WALK.

   [WpIntrCore.exec_handle_interrupt_S] is the same fact on the exec side;
   this is its per-node twin, stated over the caller's INDIVIDUAL register
   cells rather than a reference state.  [goodb] cannot carry the whole of
   it -- the stretch WRITES -- so the walk is by hand over its own small
   footprint ([ti_Drw] / [ti_Dro], six written cells and four read ones),
   with the read-only sub-monads ([hartSupports Ext_Zicfilp],
   [currentlyEnabled Ext_S], [track_trap]) carried by the certificate; and
   it SPLITS at the zicfilp elp reset, the one write to a cell no frame may
   own ([HartRegNode.swp_write_reg_same]; the other client is MRET's).       *)
(* ===================================================================== *)
(* ==================================================================== *)
(* THE FOOTPRINT.                                                        *)
(* ==================================================================== *)
Definition ti_Drw : gset register :=
  {[ (mstatus : register); (scause : register); (stval : register);
     (sepc : register); (cur_privilege : register);
     (R_bitvector_64 nextPC : register) ]}.
Definition ti_Dro : gset register :=
  {[ (R_bitvector_64 PC : register); (misa : register); (stvec : register);
     (elp : register) ]}.

Definition ti_Df (dqp dqm dqv : dfrac) : register -> dfrac := fun r =>
  if decide (r = (R_bitvector_64 PC : register)) then dqp
  else if decide (r = (misa : register)) then dqm
  else if decide (r = (stvec : register)) then dqv
  else DfracDiscarded.

Definition ti_rs (ms sc sv se : mword 64) (p : Privilege)
    (npc pc0 mis stv : mword 64) (e : mword 1) : regstate :=
  register_set mstatus ms
  (register_set scause sc
  (register_set stval sv
  (register_set sepc se
  (register_set cur_privilege p
  (register_set (R_bitvector_64 nextPC) npc
  (register_set (R_bitvector_64 PC) pc0
  (register_set misa mis
  (register_set stvec stv
  (register_set elp e init_regstate))))))))).

Local Ltac tt1 := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Lemma ti_rs_ms ms sc sv se p npc pc0 mis stv e :
  register_lookup mstatus (ti_rs ms sc sv se p npc pc0 mis stv e) = ms.
Proof. rewrite /ti_rs. apply register_lookup_set. Qed.
Lemma ti_rs_sc ms sc sv se p npc pc0 mis stv e :
  register_lookup scause (ti_rs ms sc sv se p npc pc0 mis stv e) = sc.
Proof. rewrite /ti_rs. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_sv ms sc sv se p npc pc0 mis stv e :
  register_lookup stval (ti_rs ms sc sv se p npc pc0 mis stv e) = sv.
Proof. rewrite /ti_rs. tt1. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_se ms sc sv se p npc pc0 mis stv e :
  register_lookup sepc (ti_rs ms sc sv se p npc pc0 mis stv e) = se.
Proof. rewrite /ti_rs. tt1. tt1. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_priv ms sc sv se p npc pc0 mis stv e :
  register_lookup cur_privilege (ti_rs ms sc sv se p npc pc0 mis stv e) = p.
Proof. rewrite /ti_rs. tt1. tt1. tt1. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_npc ms sc sv se p npc pc0 mis stv e :
  register_lookup (R_bitvector_64 nextPC) (ti_rs ms sc sv se p npc pc0 mis stv e) = npc.
Proof. rewrite /ti_rs. tt1. tt1. tt1. tt1. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_pc ms sc sv se p npc pc0 mis stv e :
  register_lookup (R_bitvector_64 PC) (ti_rs ms sc sv se p npc pc0 mis stv e) = pc0.
Proof. rewrite /ti_rs. tt1. tt1. tt1. tt1. tt1. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_misa ms sc sv se p npc pc0 mis stv e :
  register_lookup misa (ti_rs ms sc sv se p npc pc0 mis stv e) = mis.
Proof. rewrite /ti_rs. tt1. tt1. tt1. tt1. tt1. tt1. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_stvec ms sc sv se p npc pc0 mis stv e :
  register_lookup stvec (ti_rs ms sc sv se p npc pc0 mis stv e) = stv.
Proof. rewrite /ti_rs. tt1. tt1. tt1. tt1. tt1. tt1. tt1. tt1. apply register_lookup_set. Qed.
Lemma ti_rs_elp ms sc sv se p npc pc0 mis stv e :
  register_lookup elp (ti_rs ms sc sv se p npc pc0 mis stv e) = e.
Proof. rewrite /ti_rs. tt1. tt1. tt1. tt1. tt1. tt1. tt1. tt1. tt1.
       apply register_lookup_set. Qed.

Lemma ti_disj : ti_Drw ## ti_Dro.
Proof. rewrite /ti_Drw /ti_Dro. set_solver. Qed.

Lemma ti_w_ms : (mstatus : register) ∈ ti_Drw.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_w_sc : (scause : register) ∈ ti_Drw.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_w_sv : (stval : register) ∈ ti_Drw.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_w_se : (sepc : register) ∈ ti_Drw.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_w_priv : (cur_privilege : register) ∈ ti_Drw.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_w_npc : (R_bitvector_64 nextPC : register) ∈ ti_Drw.
Proof. rewrite /ti_Drw. set_solver. Qed.

Lemma ti_in_ms : (mstatus : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_in_sc : (scause : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_in_sv : (stval : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_in_se : (sepc : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_in_priv : (cur_privilege : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_in_npc : (R_bitvector_64 nextPC : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Drw. set_solver. Qed.
Lemma ti_in_pc : (R_bitvector_64 PC : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Dro. set_solver. Qed.
Lemma ti_in_misa : (misa : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Dro. set_solver. Qed.
Lemma ti_in_stvec : (stvec : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Dro. set_solver. Qed.
Lemma ti_in_elp : (elp : register) ∈ ti_Drw ∪ ti_Dro.
Proof. rewrite /ti_Dro. set_solver. Qed.

Local Ltac tidf :=
  unfold ti_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.
Lemma ti_Df_pc dqp dqm dqv : ti_Df dqp dqm dqv (R_bitvector_64 PC) = dqp.
Proof. tidf. Qed.
Lemma ti_Df_misa dqp dqm dqv : ti_Df dqp dqm dqv misa = dqm.
Proof. tidf. Qed.
Lemma ti_Df_stvec dqp dqm dqv : ti_Df dqp dqm dqv stvec = dqv.
Proof. tidf. Qed.
Lemma ti_Df_elp dqp dqm dqv : ti_Df dqp dqm dqv elp = DfracDiscarded.
Proof. tidf. Qed.

(* the six write-normalizations *)
Local Ltac tiag :=
  intros r Hr; rewrite /ti_Drw /ti_Dro in Hr;
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
  apply elem_of_singleton in Hr; subst r;
  first [ rewrite register_lookup_set | tt1 ];
  rewrite ?ti_rs_ms ?ti_rs_sc ?ti_rs_sv ?ti_rs_se ?ti_rs_priv ?ti_rs_npc
          ?ti_rs_pc ?ti_rs_misa ?ti_rs_stvec ?ti_rs_elp;
  reflexivity.

Lemma ti_set_ms ms ms' sc sv se p npc pc0 mis stv e :
  reg_agree_on (ti_Drw ∪ ti_Dro)
    (register_set mstatus ms' (ti_rs ms sc sv se p npc pc0 mis stv e))
    (ti_rs ms' sc sv se p npc pc0 mis stv e).
Proof. tiag. Qed.
Lemma ti_set_sc ms sc sc' sv se p npc pc0 mis stv e :
  reg_agree_on (ti_Drw ∪ ti_Dro)
    (register_set scause sc' (ti_rs ms sc sv se p npc pc0 mis stv e))
    (ti_rs ms sc' sv se p npc pc0 mis stv e).
Proof. tiag. Qed.
Lemma ti_set_sv ms sc sv sv' se p npc pc0 mis stv e :
  reg_agree_on (ti_Drw ∪ ti_Dro)
    (register_set stval sv' (ti_rs ms sc sv se p npc pc0 mis stv e))
    (ti_rs ms sc sv' se p npc pc0 mis stv e).
Proof. tiag. Qed.
Lemma ti_set_se ms sc sv se se' p npc pc0 mis stv e :
  reg_agree_on (ti_Drw ∪ ti_Dro)
    (register_set sepc se' (ti_rs ms sc sv se p npc pc0 mis stv e))
    (ti_rs ms sc sv se' p npc pc0 mis stv e).
Proof. tiag. Qed.
Lemma ti_set_priv ms sc sv se p p' npc pc0 mis stv e :
  reg_agree_on (ti_Drw ∪ ti_Dro)
    (register_set cur_privilege p' (ti_rs ms sc sv se p npc pc0 mis stv e))
    (ti_rs ms sc sv se p' npc pc0 mis stv e).
Proof. tiag. Qed.
Lemma ti_set_npc ms sc sv se p npc npc' pc0 mis stv e :
  reg_agree_on (ti_Drw ∪ ti_Dro)
    (register_set (R_bitvector_64 nextPC) npc' (ti_rs ms sc sv se p npc pc0 mis stv e))
    (ti_rs ms sc sv se p npc' pc0 mis stv e).
Proof. tiag. Qed.

(* ==================================================================== *)
(* PURE MONAD EQUATIONS for the constant extension probes, and the       *)
(* [goodb] certificates for the three read-only sub-monads the trap runs. *)
(* ==================================================================== *)
Lemma hS_Zicfilp_ret : hartSupports Ext_Zicfilp = returnM true.
Proof. unfold hartSupports. destruct (Defs.Zwf_guarded _). reflexivity. Qed.

Lemma hS_S_ret : hartSupports Ext_S = returnM true.
Proof. unfold hartSupports. destruct (Defs.Zwf_guarded _). reflexivity. Qed.

Lemma hS_Zicsr_ret : hartSupports Ext_Zicsr = returnM true.
Proof. unfold hartSupports. destruct (Defs.Zwf_guarded _). reflexivity. Qed.

Lemma rec_cE_Zicsr_ret (acc : Acc (Zwf 0) 0) :
  _rec_currentlyEnabled Ext_Zicsr 0 acc = returnM true.
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  apply hS_Zicsr_ret.
Qed.

Lemma goodb_of_ret (Db : register -> bool) {X : Type} (m : M X) (x : X)
    (s : mstate) : m = returnM x -> goodb Db m s = true.
Proof. intros ->. reflexivity. Qed.

Lemma goodb_cE_S (Db : register -> bool) (s : mstate) :
  Db misa = true -> goodb Db (currentlyEnabled Ext_S) s = true.
Proof.
  intro HD. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  apply goodb_bind_forall; [reflexivity|]. intros ?.
  apply goodb_and_boolM.
  - apply (goodb_of_ret _ _ true), hS_S_ret.
  - apply goodb_and_boolM.
    + apply goodb_bind_read_reg; [exact HD|]. reflexivity.
    + apply (goodb_of_ret _ _ true), rec_cE_Zicsr_ret.
Qed.

Lemma goodb_hS_Zicfilp (Db : register -> bool) (s : mstate) :
  goodb Db (hartSupports Ext_Zicfilp) s = true.
Proof. apply (goodb_of_ret _ _ true), hS_Zicfilp_ret. Qed.

Lemma cb_mstatus (V : mword 64) :
  long_csr_write_callback "mstatus" "mstatush" V = returnM tt.
Proof. vm_compute. reflexivity. Qed.
Lemma cb_scause (V : mword 64) : csr_name_write_callback "scause" V = returnM tt.
Proof. vm_compute. reflexivity. Qed.
Lemma cb_stval (V : mword 64) : csr_name_write_callback "stval" V = returnM tt.
Proof. vm_compute. reflexivity. Qed.
Lemma cb_sepc (V : mword 64) : csr_name_write_callback "sepc" V = returnM tt.
Proof. vm_compute. reflexivity. Qed.

Lemma bind0_retM {Y : Type} (n : M Y) : Defs.bind0 (returnM tt) n = n.
Proof. reflexivity. Qed.

Lemma bind_returnM {X Y : Type} (x : X) (f : X -> M Y) :
  Defs.bind (returnM x) f = f x.
Proof. reflexivity. Qed.

(* Sail parses [W >> R >>= K] LEFT-nested; a WRITE node re-associates by
   CONVERSION (it is one [Next] carrying a [Ret] continuation), so one
   rewrite puts the write back at the head where the node rules want it. *)
Lemma bind_bind0_wr {X Y : Type} (r : register) (v : type_of_register r)
    (n : M X) (K : X -> M Y) :
  Defs.bind (Defs.bind0 (Defs.write_reg r v) n) K
  = Defs.bind0 (Defs.write_reg r v) (Defs.bind n K).
Proof. reflexivity. Qed.

Lemma bind0_bind0_wr {X : Type} (r : register) (v : type_of_register r)
    (n : M unit) (K : M X) :
  Defs.bind0 (Defs.bind0 (Defs.write_reg r v) n) K
  = Defs.bind0 (Defs.write_reg r v) (Defs.bind0 n K).
Proof. reflexivity. Qed.

Lemma goodb_track_trap_S (Db : register -> bool) (is_i : bool) (cause : mword 6)
    (s : mstate) :
  Db mstatus = true -> Db scause = true -> Db stval = true -> Db sepc = true ->
  goodb Db (track_trap Supervisor is_i cause) s = true.
Proof.
  intros H1 H2 H3 H4. unfold track_trap.
  apply goodb_bind_read_reg; [exact H1|].
  rewrite cb_mstatus. rewrite bind0_retM. cbn match.
  apply goodb_bind_read_reg; [exact H2|].
  rewrite cb_scause. rewrite bind0_retM.
  apply goodb_bind_read_reg; [exact H3|].
  rewrite cb_stval. rewrite bind0_retM.
  apply goodb_bind_read_reg; [exact H4|].
  rewrite cb_sepc. reflexivity.
Qed.

(* ==================================================================== *)
(* The three read-only sub-monads as FOOTPRINTED facts, at the leaf's     *)
(* OWN file (no reference state: misa is generic here, only its S bit is  *)
(* pinned, so [dstateM] transport is unavailable).                        *)
(* ==================================================================== *)
Definition ti_Db (r : register) : bool :=
  register_beq r (misa : register) || register_beq r (mstatus : register)
  || register_beq r (scause : register) || register_beq r (stval : register)
  || register_beq r (sepc : register).

Lemma ti_Db_misa : ti_Db misa = true. Proof. reflexivity. Qed.
Lemma ti_Db_ms : ti_Db mstatus = true. Proof. reflexivity. Qed.
Lemma ti_Db_sc : ti_Db scause = true. Proof. reflexivity. Qed.
Lemma ti_Db_sv : ti_Db stval = true. Proof. reflexivity. Qed.
Lemma ti_Db_se : ti_Db sepc = true. Proof. reflexivity. Qed.

Lemma ti_Db_in (r : register) : ti_Db r = true -> r ∈ ti_Drw ∪ ti_Dro.
Proof.
  unfold ti_Db. intros Hr.
  repeat (apply orb_true_elim in Hr as [Hr|Hr]);
    apply register_beq_eq in Hr; subst r;
    first [ exact ti_in_misa | exact ti_in_ms | exact ti_in_sc
          | exact ti_in_sv | exact ti_in_se ].
Qed.

Lemma hval_at_ti {X : Type} (D Drw : gset register) (rs : regstate)
    (m : M X) (x : X) :
  (forall r : register, ti_Db r = true -> r ∈ D) ->
  goodb ti_Db m (MState rs ∅ dev0_state) = true ->
  exec m (MState rs ∅ dev0_state) = Some (x, MState rs ∅ dev0_state) ->
  hval D Drw rs m x rs.
Proof.
  intros HD Hg He.
  exact (hval_of_goodb ti_Db D Drw m (MState rs ∅ dev0_state) rs x
           HD (fun r _ => eq_refl) Hg He).
Qed.

Lemma hval_hS_Zicfilp_ti (D Drw : gset register) (rs : regstate) :
  (forall r : register, ti_Db r = true -> r ∈ D) ->
  hval D Drw rs (hartSupports Ext_Zicfilp) true rs.
Proof.
  intros HD. apply (hval_at_ti D Drw rs _ true HD).
  - apply goodb_hS_Zicfilp.
  - apply exec_hartSupports_Zicfilp.
Qed.

Lemma hval_cE_S_ti (D Drw : gset register) (rs : regstate) :
  (forall r : register, ti_Db r = true -> r ∈ D) ->
  eq_vec (_get_Misa_S (register_lookup misa rs)) ('b"1") = true ->
  hval D Drw rs (currentlyEnabled Ext_S) true rs.
Proof.
  intros HD Hm. apply (hval_at_ti D Drw rs _ true HD).
  - apply goodb_cE_S, ti_Db_misa.
  - rewrite (exec_currentlyEnabled_S (MState rs ∅ dev0_state)).
    cbn [sregs]. rewrite Hm. reflexivity.
Qed.

Lemma hval_track_trap_ti (D Drw : gset register) (rs : regstate)
    (is_i : bool) (cause : mword 6) :
  (forall r : register, ti_Db r = true -> r ∈ D) ->
  hval D Drw rs (track_trap Supervisor is_i cause) tt rs.
Proof.
  intros HD. apply (hval_at_ti D Drw rs _ tt HD).
  - apply goodb_track_trap_S;
      [ apply ti_Db_ms | apply ti_Db_sc | apply ti_Db_sv | apply ti_Db_se ].
  - apply exec_track_trap_S.
Qed.

(* ==================================================================== *)
(* The mstatus / scause towers the trap builds, in the model's order.    *)
(* ==================================================================== *)
Definition ti_ms1 (e : mword 1) (ms : mword 64) : mword 64 :=
  update_subrange_vec_dec ms 23 23 e.
Definition ti_ms2 (e : mword 1) (ms : mword 64) : mword 64 :=
  update_subrange_vec_dec (ti_ms1 e ms) 5 5 (_get_Mstatus_SIE (ti_ms1 e ms)).
Definition ti_ms3 (e : mword 1) (ms : mword 64) : mword 64 :=
  update_subrange_vec_dec (ti_ms2 e ms) 1 1 ('b"0").
Definition ti_ms4 (e : mword 1) (ms : mword 64) : mword 64 :=
  update_subrange_vec_dec (ti_ms3 e ms) 8 8 ('b"1").
Lemma ti_ms4_trap (e : mword 1) (ms : mword 64) : ti_ms4 e ms = trap_ms e ms.
Proof. reflexivity. Qed.

Definition ti_sc1 (sc : mword 64) (i : InterruptType) : mword 64 :=
  update_subrange_vec_dec sc (64 - 1) (64 - 1)
    (bool_to_bit (trapCause_is_interrupt (Interrupt i))).
Definition ti_sc2 (sc : mword 64) (i : InterruptType) : mword 64 :=
  update_subrange_vec_dec (ti_sc1 sc i) (64 - 2) 0
    (zero_extend' (64 - 1) (trapCause_bits_forwards (Interrupt i))).
Lemma ti_sc2_trap (sc : mword 64) (i : InterruptType) :
  ti_sc2 sc i = trap_scause sc i.
Proof. reflexivity. Qed.

Lemma hregwrite_val_at_write_reg (r : register) (v : type_of_register r) :
  hregwrite_val_at r (Defs.write_reg r v) = Some v.
Proof.
  cbn [Defs.write_reg hregwrite_val_at].
  match goal with
  | |- context [ match ?d with | left _ => _ | right _ => _ end ] =>
      destruct d as [Heq|Hne]
  end; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel. reflexivity.
Qed.

Lemma hregwrite_resume_write_reg (r : register) (v : type_of_register r) :
  hregwrite_resume (Defs.write_reg r v) = Interface.Ret tt.
Proof. reflexivity. Qed.

Section TrapSwp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma ti_frames (dqp dqm dqv : dfrac) (ms sc sv se : mword 64)
      (p : Privilege) (npc pc0 mis stv : mword 64) (e : mword 1) :
    (hreg_frame (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Drw ∗
     hreg_frame_ro (ti_Df dqp dqm dqv)
       (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Dro : iProp Σ)
    ⊣⊢ (mstatus ↦ᵣ ms ∗ scause ↦ᵣ sc ∗ stval ↦ᵣ sv ∗ sepc ↦ᵣ se ∗
         cur_privilege ↦ᵣ p ∗ (R_bitvector_64 nextPC) ↦ᵣ npc ∗
         reg_pointsto (R_bitvector_64 PC) dqp pc0 ∗
         reg_pointsto misa dqm mis ∗ reg_pointsto stvec dqv stv ∗
         reg_pointsto elp DfracDiscarded e).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /ti_Drw /ti_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite ti_rs_ms ti_rs_sc ti_rs_sv ti_rs_se ti_rs_priv ti_rs_npc
            ti_rs_pc ti_rs_misa ti_rs_stvec ti_rs_elp.
    rewrite ti_Df_pc ti_Df_misa ti_Df_stvec ti_Df_elp.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma ti_frames_in (dqp dqm dqv : dfrac) (ms sc sv se : mword 64)
      (p : Privilege) (npc pc0 mis stv : mword 64) (e : mword 1) :
    mstatus ↦ᵣ ms -∗ scause ↦ᵣ sc -∗ stval ↦ᵣ sv -∗ sepc ↦ᵣ se -∗
    cur_privilege ↦ᵣ p -∗ (R_bitvector_64 nextPC) ↦ᵣ npc -∗
    reg_pointsto (R_bitvector_64 PC) dqp pc0 -∗
    reg_pointsto misa dqm mis -∗ reg_pointsto stvec dqv stv -∗
    reg_pointsto elp DfracDiscarded e -∗
    (hreg_frame (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Drw ∗
     hreg_frame_ro (ti_Df dqp dqm dqv)
       (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Dro : iProp Σ).
  Proof.
    iIntros "H1 H2 H3 H4 H5 H6 H7 H8 H9 H10". rewrite ti_frames. iFrame.
  Qed.

  Lemma ti_frames_out (dqp dqm dqv : dfrac) (ms sc sv se : mword 64)
      (p : Privilege) (npc pc0 mis stv : mword 64) (e : mword 1) :
    (hreg_frame (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Drw ∗
     hreg_frame_ro (ti_Df dqp dqm dqv)
       (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Dro : iProp Σ) -∗
    (mstatus ↦ᵣ ms ∗ scause ↦ᵣ sc ∗ stval ↦ᵣ sv ∗ sepc ↦ᵣ se ∗
     cur_privilege ↦ᵣ p ∗ (R_bitvector_64 nextPC) ↦ᵣ npc ∗
     reg_pointsto (R_bitvector_64 PC) dqp pc0 ∗
     reg_pointsto misa dqm mis ∗ reg_pointsto stvec dqv stv ∗
     reg_pointsto elp DfracDiscarded e).
  Proof. rewrite ti_frames. iIntros "H". iExact "H". Qed.

  Lemma ti_rw_ext (rs rs' : regstate) :
    reg_agree_on (ti_Drw ∪ ti_Dro) rs rs' ->
    hreg_frame rs ti_Drw -∗ (hreg_frame rs' ti_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ ti_Drw
      (reg_agree_mono (ti_Drw ∪ ti_Dro) ti_Drw _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  Lemma ti_ro_ext (Df : register -> dfrac) (rs rs' : regstate) :
    reg_agree_on (ti_Drw ∪ ti_Dro) rs rs' ->
    hreg_frame_ro Df rs ti_Dro -∗ (hreg_frame_ro Df rs' ti_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext Df _ _ ti_Dro
      (reg_agree_mono (ti_Drw ∪ ti_Dro) ti_Dro _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  Local Ltac tinorm L :=
    iDestruct (ti_rw_ext _ _ (L _ _ _ _ _ _ _ _ _ _ _) with "Hrw") as "Hrw";
    iDestruct (ti_ro_ext _ _ _ (L _ _ _ _ _ _ _ _ _ _ _) with "Hro") as "Hro".

  (* ------------------------------------------------------------------ *)
  (* [zicfilp_preserve_elp_on_trap Supervisor]: mstatus.SPELP := elp, then *)
  (* THE WRITE THE SPAN CANNOT TAKE -- [reset_elp], writing elp with the   *)
  (* value the [hw_config] pin already fixes.                              *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_zicfilp_trap_S (dqp dqm dqv : dfrac) (ms sc sv se : mword 64)
      (p : Privilege) (npc pc0 mis stv : mword 64) (e : mword 1) :
    e = landing_pad_bits_backwards NO_LP_EXPECTED ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded e -∗
    hreg_frame (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Drw -∗
    hreg_frame_ro (ti_Df dqp dqm dqv)
      (ti_rs ms sc sv se p npc pc0 mis stv e) ti_Dro -∗
    swp (zicfilp_preserve_elp_on_trap Supervisor)
      (fun _ =>
         hreg_frame (ti_rs (ti_ms1 e ms) sc sv se p npc pc0 mis stv e) ti_Drw ∗
         hreg_frame_ro (ti_Df dqp dqm dqv)
           (ti_rs (ti_ms1 e ms) sc sv se p npc pc0 mis stv e) ti_Dro).
  Proof.
    intros He. iIntros "#Hcert #Help Hrw Hro".
    unfold zicfilp_preserve_elp_on_trap. cbn match.
    iApply (swp_bind0_use _ _
              (fun _ : unit =>
                 hreg_frame (ti_rs (ti_ms1 e ms) sc sv se p npc pc0 mis stv e)
                   ti_Drw ∗
                 hreg_frame_ro (ti_Df dqp dqm dqv)
                   (ti_rs (ti_ms1 e ms) sc sv se p npc pc0 mis stv e) ti_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ mstatus
                  ti_disj ti_in_ms with "Hcert Hrw Hro"). }
      iIntros (w2) "(-> & Hrw & Hro)". rewrite ti_rs_ms.
      iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ elp
                  ti_disj ti_in_elp with "Hcert Hrw Hro"). }
      iIntros (w3) "(-> & Hrw & Hro)". rewrite ti_rs_elp.
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ mstatus (ti_ms1 e ms)
                     ti_disj ti_w_ms with "Hcert Hrw Hro") ].
      iIntros (u) "[Hrw Hro]".
      iDestruct (ti_rw_ext _ _
        (ti_set_ms ms (ti_ms1 e ms) sc sv se p npc pc0 mis stv e)
        with "Hrw") as "Hrw".
      iDestruct (ti_ro_ext _ _ _
        (ti_set_ms ms (ti_ms1 e ms) sc sv se p npc pc0 mis stv e)
        with "Hro") as "Hro". iFrame. }
    iIntros (u) "[Hrw Hro]". unfold reset_elp. subst e.
    iApply (swp_write_reg_same elp DfracDiscarded _ _ _
              (hregwrite_val_at_write_reg elp _) with "Hcert Help [-]").
    iIntros "_". rewrite hregwrite_resume_write_reg.
    iApply swp_ret. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE TRAP.  [trap_handler Supervisor (Interrupt ii) pc0 None None]     *)
  (* node by node along the model's own binds -- the [swp] twin of         *)
  (* [WpIntrCore.exec_trap_handler_S_intr].                                *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_trap_handler_S_intr (dqp dqm dqv : dfrac) (ii : InterruptType)
      (ms sc sv se npc pc0 mis stv : mword 64) (e : mword 1) :
    e = landing_pad_bits_backwards NO_LP_EXPECTED ->
    eq_vec (_get_Misa_S mis) ('b"1") = true ->
    trapVectorMode_forwards (_get_Mtvec_Mode stv) = TV_Direct ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded e -∗
    hreg_frame (ti_rs ms sc sv se Supervisor npc pc0 mis stv e) ti_Drw -∗
    hreg_frame_ro (ti_Df dqp dqm dqv)
      (ti_rs ms sc sv se Supervisor npc pc0 mis stv e) ti_Dro -∗
    swp (trap_handler Supervisor (Interrupt ii) pc0 None None)
      (fun tgt => ⌜tgt = stvec_base stv⌝ ∗
         hreg_frame (ti_rs (ti_ms4 e ms) (ti_sc2 sc ii) (zeros' 64) pc0
                       Supervisor npc pc0 mis stv e) ti_Drw ∗
         hreg_frame_ro (ti_Df dqp dqm dqv)
           (ti_rs (ti_ms4 e ms) (ti_sc2 sc ii) (zeros' 64) pc0
              Supervisor npc pc0 mis stv e) ti_Dro).
  Proof.
    intros He HmisaS Htvd. iIntros "#Hcert #Help Hrw Hro".
    unfold trap_handler. cbn zeta.
    change (orb (get_config_print_exception tt) (get_config_print_interrupt tt))
      with false.
    cbn match. rewrite bind0_retM.
    (* -- hartSupports Ext_Zicfilp -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span ti_Drw ti_Dro _ _ _ _ true ti_disj
                (hval_hS_Zicfilp_ti (ti_Drw ∪ ti_Dro) ti_Drw
                   (ti_rs ms sc sv se Supervisor npc pc0 mis stv e) ti_Db_in)
                with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". cbn match.
    (* -- zicfilp_preserve_elp_on_trap Supervisor (incl. the elp reset) -- *)
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_zicfilp_trap_S dqp dqm dqv ms sc sv se Supervisor npc pc0
                mis stv e He with "Hcert Help Hrw Hro"). }
    iIntros (u0) "[Hrw Hro]". cbn match.
    (* -- currentlyEnabled Ext_S, then the assertion -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span ti_Drw ti_Dro _ _ _ _ true ti_disj
                (hval_cE_S_ti (ti_Drw ∪ ti_Dro) ti_Drw
                   (ti_rs (ti_ms1 e ms) sc sv se Supervisor npc pc0 mis stv e)
                   ti_Db_in
                   ltac:(rewrite ti_rs_misa; exact HmisaS))
                with "Hcert Hrw Hro"). }
    iIntros (w2) "(-> & Hrw & Hro)".
    unfold Defs.assert_exp'. cbn match. rewrite bind_returnM.
    (* -- scause: read, write c1, read, write c2 -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ scause
                ti_disj ti_in_sc with "Hcert Hrw Hro"). }
    iIntros (w3) "(-> & Hrw & Hro)". rewrite ti_rs_sc.
    rewrite bind_bind0_wr.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ scause (ti_sc1 sc ii)
                ti_disj ti_w_sc with "Hcert Hrw Hro"). }
    iIntros (u1) "[Hrw Hro]". tinorm ti_set_sc.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ scause
                ti_disj ti_in_sc with "Hcert Hrw Hro"). }
    iIntros (w4) "(-> & Hrw & Hro)". rewrite ti_rs_sc.
    rewrite bind_bind0_wr.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ scause (ti_sc2 sc ii)
                ti_disj ti_w_sc with "Hcert Hrw Hro"). }
    iIntros (u2) "[Hrw Hro]". tinorm ti_set_sc.
    (* -- mstatus: SPIE := SIE -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ mstatus
                ti_disj ti_in_ms with "Hcert Hrw Hro"). }
    iIntros (w5) "(-> & Hrw & Hro)". rewrite ti_rs_ms.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ mstatus
                ti_disj ti_in_ms with "Hcert Hrw Hro"). }
    iIntros (w6) "(-> & Hrw & Hro)". rewrite ti_rs_ms.
    rewrite bind_bind0_wr.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ mstatus (ti_ms2 e ms)
                ti_disj ti_w_ms with "Hcert Hrw Hro"). }
    iIntros (u3) "[Hrw Hro]". tinorm ti_set_ms.
    (* -- mstatus: SIE := 0 -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ mstatus
                ti_disj ti_in_ms with "Hcert Hrw Hro"). }
    iIntros (w7) "(-> & Hrw & Hro)". rewrite ti_rs_ms.
    rewrite bind_bind0_wr.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ mstatus (ti_ms3 e ms)
                ti_disj ti_w_ms with "Hcert Hrw Hro"). }
    iIntros (u4) "[Hrw Hro]". tinorm ti_set_ms.
    (* -- mstatus: SPP := 1 (via the cur_privilege read) -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ mstatus
                ti_disj ti_in_ms with "Hcert Hrw Hro"). }
    iIntros (w8) "(-> & Hrw & Hro)". rewrite ti_rs_ms.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ cur_privilege
                ti_disj ti_in_priv with "Hcert Hrw Hro"). }
    iIntros (w9) "(-> & Hrw & Hro)". rewrite ti_rs_priv. cbn match.
    rewrite bind_returnM.
    (* -- the four writes: mstatus SPP, stval, sepc, cur_privilege -- *)
    repeat rewrite bind0_bind0_wr.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ mstatus (ti_ms4 e ms)
                ti_disj ti_w_ms with "Hcert Hrw Hro"). }
    iIntros (u5) "[Hrw Hro]". tinorm ti_set_ms.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ stval (zeros' 64)
                ti_disj ti_w_sv with "Hcert Hrw Hro"). }
    iIntros (u6) "[Hrw Hro]". tinorm ti_set_sv.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ sepc pc0
                ti_disj ti_w_se with "Hcert Hrw Hro"). }
    iIntros (u7) "[Hrw Hro]". tinorm ti_set_se.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ cur_privilege Supervisor
                ti_disj ti_w_priv with "Hcert Hrw Hro"). }
    iIntros (u8) "[Hrw Hro]". tinorm ti_set_priv.
    (* -- track_trap, the scause read-back, prepare_trap_vector -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_span ti_Drw ti_Dro _ _ _ _ tt ti_disj
                  (hval_track_trap_ti (ti_Drw ∪ ti_Dro) ti_Drw
                     (ti_rs (ti_ms4 e ms) (ti_sc2 sc ii) (zeros' 64) pc0
                        Supervisor npc pc0 mis stv e) _ _ ti_Db_in)
                  with "Hcert Hrw Hro"). }
      iIntros (u9) "(_ & Hrw & Hro)".
      iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ scause
                ti_disj ti_in_sc with "Hcert Hrw Hro"). }
    iIntros (w10) "(-> & Hrw & Hro)".
    unfold prepare_trap_vector. cbn match.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ stvec
                ti_disj ti_in_stvec with "Hcert Hrw Hro"). }
    iIntros (w11) "(-> & Hrw & Hro)". rewrite ti_rs_stvec.
    unfold tvec_addr. rewrite Htvd. cbn match.
    iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [handle_interrupt ii Supervisor] at the frame: PC read, the trap,     *)
  (* [set_next_pc].                                                        *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_handle_interrupt_S_frame (dqp dqm dqv : dfrac) (ii : InterruptType)
      (ms sc sv se npc pc0 mis stv : mword 64) (e : mword 1) :
    e = landing_pad_bits_backwards NO_LP_EXPECTED ->
    eq_vec (_get_Misa_S mis) ('b"1") = true ->
    trapVectorMode_forwards (_get_Mtvec_Mode stv) = TV_Direct ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded e -∗
    hreg_frame (ti_rs ms sc sv se Supervisor npc pc0 mis stv e) ti_Drw -∗
    hreg_frame_ro (ti_Df dqp dqm dqv)
      (ti_rs ms sc sv se Supervisor npc pc0 mis stv e) ti_Dro -∗
    swp (handle_interrupt ii Supervisor)
      (fun _ =>
         hreg_frame (ti_rs (ti_ms4 e ms) (ti_sc2 sc ii) (zeros' 64) pc0
                       Supervisor (stvec_base stv) pc0 mis stv e) ti_Drw ∗
         hreg_frame_ro (ti_Df dqp dqm dqv)
           (ti_rs (ti_ms4 e ms) (ti_sc2 sc ii) (zeros' 64) pc0
              Supervisor (stvec_base stv) pc0 mis stv e) ti_Dro).
  Proof.
    intros He HmisaS Htvd. iIntros "#Hcert #Help Hrw Hro".
    unfold handle_interrupt.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned ti_Drw ti_Dro _ _ (R_bitvector_64 PC)
                ti_disj ti_in_pc with "Hcert Hrw Hro"). }
    iIntros (w0) "(-> & Hrw & Hro)". rewrite ti_rs_pc.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_trap_handler_S_intr dqp dqm dqv ii ms sc sv se npc pc0
                mis stv e He HmisaS Htvd with "Hcert Help Hrw Hro"). }
    iIntros (tgt) "(-> & Hrw & Hro)".
    unfold set_next_pc. cbn match.
    iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned ti_Drw ti_Dro _ _ (R_bitvector_64 nextPC)
                (stvec_base stv) ti_disj ti_w_npc with "Hcert Hrw Hro"). }
    iIntros (u) "[Hrw Hro]". tinorm ti_set_npc.
    iApply swp_ret. iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE HEADLINE, at the caller's individual cells.                       *)
  (* ==================================================================== *)
  Lemma swp_handle_interrupt_S (ii : InterruptType)
      (pc0 ms_v sc_old sv_old se_old np_old stvec_v misa0 : mword 64)
      (elp_v : mword 1) {dqp dqm dqv : dfrac} :
    eq_vec elp_v (landing_pad_bits_backwards LP_EXPECTED) = false ->
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
    intros Hnp HmisaS Htvd.
    pose proof (elp_no_lp elp_v Hnp) as He.
    iIntros "#Hcert HPC Hmisa Hstv #Help Hms Hsc Hsv Hse Hpriv Hnpc".
    iDestruct (ti_frames_in dqp dqm dqv ms_v sc_old sv_old se_old Supervisor
                 np_old pc0 misa0 stvec_v elp_v
                 with "Hms Hsc Hsv Hse Hpriv Hnpc HPC Hmisa Hstv Help")
      as "[Hrw Hro]".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_handle_interrupt_S_frame dqp dqm dqv ii ms_v sc_old
                   sv_old se_old np_old pc0 misa0 stvec_v elp_v
                   He HmisaS Htvd with "Hcert Help Hrw Hro") ].
    iIntros (u) "[Hrw Hro]".
    iDestruct (ti_frames_out with "[$Hrw $Hro]")
      as "(Hms & Hsc & Hsv & Hse & Hpriv & Hnpc & HPC & Hmisa & Hstv & _)".
    rewrite ti_ms4_trap ti_sc2_trap. iFrame.
  Qed.

End TrapSwp.

Section IntrEngine.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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
    (∀ tlbf : type_of_register tlb,
       W -∗
       hreg_frame (register_set (R_bitvector_64 nextPC)
                     (add_vec_int pc (if is_rvc then 2 else 4))
                     (register_set tlb tlbf rs)) s_Drw -∗
       hreg_frame_ro (s_Df (DfracOwn 1))
         (register_set (R_bitvector_64 nextPC)
            (add_vec_int pc (if is_rvc then 2 else 4))
            (register_set tlb tlbf rs)) s_Dro -∗
       tlb_snap_ok tlbf -∗
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

(* THE LEAF-FACING CALLBACK, once.  It is spelled in three places (the
   engine's premise, the rider's trap arm, and the resource the S-mode
   run rule threads to whichever arm the machine picks), so it is a
   definition rather than three copies that can drift.
   [_clock] is the general one: the leaf ALSO borrows the three clock
   cells.  They are stable across the instruction -- the tick runs at the
   cycle boundary, not inside it -- so lending them costs the engine
   nothing, and [csrr time] / [csrr sip] / [csrw stimecmp] cannot be
   written without them. *)
Definition intr_cb_clock `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId}
    (kt : ktier) (m : regfile) (av : nat) (p pc0 : mword 64) (is_rvc : bool)
    (i : instruction) (R : mword 64 -> regfile -> nat -> iProp Σ)
    `{CID : CpuId} : iProp Σ :=
  ((sconf -∗
    sie_cap kt m av true p -∗
    gpr_file (tp_pin m) -∗
    (R_bitvector_64 PC) ↦ᵣ pc0 -∗
    (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc0 (if is_rvc then 2 else 4)) -∗
    resv_any cpu_id -∗
    clock_res -∗
    swp (execute i)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
         ∃ (npc : mword 64) (m' : regfile) (av' : nat),
           (R_bitvector_64 PC) ↦ᵣ pc0 ∗
           (R_bitvector_64 nextPC) ↦ᵣ npc ∗
           resv_any cpu_id ∗ clock_res ∗
           sconf ∗ sie_cap kt m' av' true p ∗ gpr_file (tp_pin m') ∗
           R npc m' av'))
   ∗ (∀ (npc : mword 64) (m' : regfile) (av' : nat),
        sie_cap_gpr kt m' av' true p -∗ pc_is npc -∗ R npc m' av' -∗
        WP (Loop : expr riscv_lang)))%I.

(* ...and the CLOCK-FREE reading, for the leaves that never touch a clock
   cell: the same callback with the three cells passed straight through. *)
Definition intr_cb `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId}
    (kt : ktier) (m : regfile) (av : nat) (p pc0 : mword 64) (is_rvc : bool)
    (i : instruction) (R : mword 64 -> regfile -> nat -> iProp Σ)
    `{CID : CpuId} : iProp Σ :=
  ((sconf -∗
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
        WP (Loop : expr riscv_lang)))%I.

(* the CYCLE'S RIDER, keyed on the file the body landed on ([rs2]): its
   [nextPC] is the pc the cycle commits, so both arms name their landing pc
   by reading it off rather than by an existential the continuation could
   not tie down. *)
Definition intr_psi `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (m : regfile) (av : nat) (p pc0 : mword 64) (is_rvc : bool)
    (i : instruction) (R : mword 64 -> regfile -> nat -> iProp Σ)
    (rs2 : regstate) : iProp Σ :=
  ((* --- RETIRE: the leaf kept the bundles, at its own map --- *)
                (∃ (m' : regfile) (av' : nat),
                   sconf_priv_closer ∗ (∃ ms : mword 64, sconf_msown ms) ∗
                   sie_cap kt m' av' true p ∗ gpr_file (tp_pin m') ∗
                   resv_any cpu_id ∗
                   R (register_lookup (R_bitvector_64 nextPC) rs2) m' av' ∗
                   (∀ (npc0 : mword 64) (m0 : regfile) (av0 : nat),
                      sie_cap_gpr kt m0 av0 true p -∗ pc_is npc0 -∗
                      R npc0 m0 av0 -∗ WP (Loop : expr riscv_lang)))
                ∨
                (* --- TRAP: the entry package, minus what the frame holds --- *)
                (∃ (sc mstT mdvT : mword 64),
                   ⌜ s_cause_ok sc ⌝ ∗ ⌜ sconf_ms_facts mstT ⌝ ∗
                   ⌜ and_vec MIE_S (not_vec mdvT) = zeros' 64 ⌝ ∗
                   mstatus ↦ᵣ mstT ∗
                   ghost_var sie_gname (1/2) (_get_Mstatus_SIE mstT) ∗
                   sret_tie mstT ∗
                   mie ↦ᵣ MIE_S ∗ mideleg ↦ᵣ mdvT ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                   sret_bits ('b"1" : mword 1) ('b"1" : mword 1) ∗
                   sepc ↦ᵣ pc0 ∗ scause ↦ᵣ sc ∗ stval ↦ᵣ (zeros' 64) ∗
                   sie_cap kt m (trap_res true + av) false p ∗
                   kpt_on cpu_id ∗ cpu_hart 0 false p ∅ ∗ cpu_claim p ∗
                   intr_res kt ∗
                   intr_handler_spec kt
                     (register_lookup (R_bitvector_64 nextPC) rs2) ∗
                   gpr_file (tp_pin m) ∗ resv_any cpu_id ∗
                   wp_next true p (fun CID =>
                     intr_cb_clock kt m av p pc0 is_rvc i R (CID := CID))))%I.

Lemma wp_exec_step_intr_clock `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId} `{CID0 : CpuId}
    {kt : ktier} (pc0 : mword 64) (m : regfile) (av : nat) (p : mword 64)
    (is_rvc : bool) (i : instruction)
    (R : mword 64 -> regfile -> nat -> iProp Σ) :
  ret_pc pc0 = pc0 ->
  sie_cap_gpr kt m av true p -∗
  pc_is pc0 -∗
  instr pc0 is_rvc i -∗
  ▷ wp_next true p (fun CID =>
      intr_cb_clock kt m av p pc0 is_rvc i R (CID := CID)) -∗
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
  iDestruct (hw_config_kmap with "Hhw") as "#Hkm".
  pose proof (elp_no_lp elp0 Helpnp) as Help0.
  destruct Hsatpf as (Hmode & Hasid & Hppn).
  destruct Hpmpf as (HA & Hord & HX & HW & HR & Hcov).
  pose proof Hmsf as Hmsf'. destruct Hmsf' as (_ & HSXL & _).
  (* ---- the cycle's own frame: the six writable cells and the five
         read-only ones.  Everything else stays in this proof's hands and is
         lent to the walk (and to the leaf) below. ---- *)
  iAssert (hreg_frame (s_rs pc0 pc0 msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbv) i_Drw)
    with "[HPC Hmsr Hmi Hcy Hti Hip]" as "Hirw".
  { rewrite i_rw_split. srs. iFrame. }
  iAssert (hreg_frame_ro i_Df (s_rs pc0 pc0 msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbv) i_Dro)
    with "[HnPC Hhs Hpriv]" as "Hiro".
  { rewrite i_ro_split. srs. iFrame "HnPC Hhs Hpriv Hmc Hmicfg". }
  iApply (wp_loop_cycle_ex i_Drw i_Dro i_Df
            (fun rsx => exists (rs2 : regstate) (mi : mword 64),
               intr_Q (minstret_inc_flag mc micfg Supervisor) rs2 /\
               rsx = wrap_post rs2 mi)
            (fun rsx => ∃ (rs2 : regstate) (mi : mword 64),
               ⌜intr_Q (minstret_inc_flag mc micfg Supervisor) rs2 /\
                rsx = wrap_post rs2 mi⌝ ∗ intr_psi kt m av p pc0 is_rvc i R rs2)%I
            i_disj i_w_cy i_w_ti i_w_ip
            with "Hcert Hresv [-] []").
  { (* ==================== THE CYCLE'S BODY ==================== *)
    iNext. iIntros "Hfrag".
    iApply (swp_mono with "[] [-]").
    2:{ iApply (swp_try_step_any_ex i_Drw i_Dro i_Df
                  (s_rs pc0 pc0 msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbv)
                  (intr_Q (minstret_inc_flag mc micfg Supervisor))
                  (intr_psi kt m av p pc0 is_rvc i R)
                  i_disj i_in_priv i_in_hart i_in_mc i_in_micfg i_w_mi
                  i_in_mi i_w_ms i_in_ms i_w_PC i_in_PC i_in_nPC
                  ltac:(by srs)
                  ltac:(intros rs2 HQ; exact (proj1 HQ))
                  ltac:(intros rs2 HQ; rewrite (proj1 (proj2 HQ)); by srs)
                  with "Hcert Hirw Hiro [-]").
        iIntros "Hrw Hro".
        (* the prelude's file, re-anchored on the tower *)
        pose proof (reg_agree_mono (s_Drw ∪ s_Dro) (i_Drw ∪ i_Dro) _ _ i_sub_s
                      (s_pre_agree pc0 msr bmi cy ti ip mst0 pcfg paddr mc
                         micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0
                         satp0 MIE_S mdv0 MENVCFG_S tlbv)) as Hpre.
        iDestruct (i_rw_ext _ _ Hpre with "Hrw") as "Hrw".
        iDestruct (i_ro_ext _ _ Hpre with "Hro") as "Hro".
        (* ...and enlarged to the S-mode footprint for the walk *)
        iEval (rewrite i_rw_split) in "Hrw".
        iDestruct "Hrw" as "(HPC & Hmsr & Hmi & Hcy & Hti & Hip)".
        iEval (rewrite i_ro_split) in "Hro".
        iDestruct "Hro" as "(HnPC & Hhs & Hpriv & _ & _)".
        iAssert (hreg_frame (s_rs pc0 pc0 msr (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0 pcfg
         paddr mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S
         mdv0 MENVCFG_S tlbv) s_Drw ∗
                 hreg_frame_ro (s_Df (DfracOwn 1)) (s_rs pc0 pc0 msr (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0 pcfg
         paddr mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S
         mdv0 MENVCFG_S tlbv) s_Dro)%I
          with "[HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg Hpaddr
                 Hsatp Hmie Hmdl Hmenv]" as "[Hsrw Hsro]".
        { rewrite (s_frames_cells pc0 pc0 msr
                     (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0 pcfg
                     paddr mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0
                     satp0 MIE_S mdv0 MENVCFG_S tlbv).
          rewrite /s_cells. srs.
          iFrame "HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg
                  Hpaddr Hsatp Hmie Hmdl Hmenv".
          iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv". }
        iApply (swp_mono with "[] [-]").
        2:{ iApply (swp_run_hart_active_instr_S (s_rs pc0 pc0 msr (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0 pcfg
         paddr mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S
         mdv0 MENVCFG_S tlbv) root_ppn pc0 is_rvc i
                      ip mdv0 mst0
                      (wp_next true p (fun CID =>
                         intr_cb_clock kt m av p pc0 is_rvc i R (CID := CID))
                       ∗ ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0)
                       ∗ sret_tie mst0
                       ∗ stack_own (KTR := kt) (m !!! Regidx csp_rs1)
                           (trap_res true + av)
                       ∗ strans_kpt
                       ∗ ghost_var sie_gname (1/4/2)%Qp ('b"1" : mword 1)
                       ∗ ghost_var sie_gname (1/4) vb ∗ stvec ↦ᵣ handler
                       ∗ (∃ v : mword 64, sepc ↦ᵣ v)
                       ∗ (∃ v : mword 64, scause ↦ᵣ v)
                       ∗ (∃ v : mword 64, stval ↦ᵣ v)
                       ∗ (∃ a b : mword 1, sret_bits a b)
                       ∗ cpu_claim p ∗ cpu_hart 0 true p ∅
                       ∗ gpr_file (tp_pin m))%I
                      (∃ rs2 : regstate,
                        ⌜intr_Q (minstret_inc_flag mc micfg Supervisor) rs2⌝ ∗
                        hreg_frame rs2 i_Drw ∗ hreg_frame_ro i_Df rs2 i_Dro ∗
                        intr_psi kt m av p pc0 is_rvc i R rs2)%I
                      (fun ii pr => ∃ rs2 : regstate,
                        ⌜intr_Q (minstret_inc_flag mc micfg Supervisor) rs2⌝ ∗
                        swp (handle_interrupt ii pr)
                          (fun _ => hreg_frame rs2 i_Drw ∗
                                    hreg_frame_ro i_Df rs2 i_Dro ∗
                                    intr_psi kt m av p pc0 is_rvc i R rs2))%I
                      ltac:(by srs) ltac:(by srs)
                      ltac:(srs; exact Hmisaval)
                      ltac:(srs; exact Hsecval)
                      ltac:(by srs) ltac:(by srs) ltac:(by srs) HSXL
                      ltac:(by srs) ltac:(by srs) ltac:(by srs) Hmm
                      ltac:(srs; exact Help0)
                      ltac:(srs; exact Hpmaall)
                      ltac:(srs; exact Hmode) ltac:(srs; exact Hasid)
                      ltac:(srs; exact Hppn)
                      ltac:(srs; exact HA) ltac:(srs; exact Hord)
                      ltac:(srs; exact HX) ltac:(srs; exact HW)
                      ltac:(srs; exact HR) ltac:(srs; exact Hcov)
                      with "Hcert Hkm Hinstr Hkinv [Hsnap] Hfrag
                            [$Hbody $Hhalf $Htie $Hstk $Hbit1 $Hq1 $Hq4 $Hstv
                             $Hsepcx $Hscausex $Hstvalx $Hsppc $Hclm $Hcpu
                             $Hfile]
                            Hsrw Hsro [] []").
            { srs. iExact "Hsnap". }
            (* ---------- THE TRAP ---------- *)
            iIntros (ii pr) "%Hd HW Hsrw Hsro Hsnap' Hfrag".
            destruct Hd as (meip & seip & Hd).
            pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hd) as Hpr.
            subst pr.
            iDestruct "HW" as "(Hwn & Hhalf & Htie & Hstk & Hbit1 & Hq1 & Hq4 &
                                Hstv & Hsepcx & Hscausex & Hstvalx & Hsppc &
                                Hclm & Hcpu & Hfile)".
            iDestruct "Hsepcx" as (se_old) "Hsepc".
            iDestruct "Hscausex" as (sc_old) "Hscause".
            iDestruct "Hstvalx" as (sv_old) "Hstval".
            iDestruct "Hsppc" as (vca vcb) "Hsppc".
            pose proof (s_cause_ok_of_dispatch ip mdv0 mst0 sc_old meip seip
                          ii Supervisor Hd) as Hcause.
            iAssert (s_cells pc0 pc0 msr (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0 pcfg paddr
                       mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0
                       MIE_S mdv0 MENVCFG_S tlbv) with "[Hsrw Hsro]" as "Hcells".
            { rewrite -s_frames_cells. iFrame. }
            iEval (rewrite /s_cells) in "Hcells".
            iDestruct "Hcells" as
              "(HPC & HnPC & Hmsr & Hmi & Hcy & Hti & Hip & Htlb & Hpriv &
                Hms & Hhs & Hpcfg & Hpaddr & ? & ? & ? & ? & ? & ? & ? & ? &
                Hsatp & Hmie & Hmdl & Hmenv)".
            iExists (s_rs pc0 (stvec_base handler) msr (minstret_inc_flag mc micfg Supervisor) cy ti ip
                       (trap_ms elp0 mst0) pcfg paddr mc micfg misa0 mseccfg0
                       (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbv).
            iSplitR. { iPureIntro. rewrite /intr_Q. split_and!; by srs. }
            iApply swp_fupd_post.
            iApply (swp_mono with
                      "[-HPC Hstv Hms Hscause Hstval Hsepc Hpriv HnPC]
                       [HPC Hstv Hms Hscause Hstval Hsepc Hpriv HnPC]").
            2:{ iApply (swp_handle_interrupt_S ii pc0 mst0 sc_old sv_old se_old
                          pc0 handler misa0 elp0 Helpnp HmS Htvd
                          with "Hcert HPC Hmisa Hstv Help Hms Hscause Hstval
                                Hsepc Hpriv HnPC"). }
            iIntros (u)
              "(HPC & _ & Hstv & Hms & Hscause & Hstval & Hsepc & Hpriv &
                HnPC)".
            (* THE GHOST FLIP '1' -> '0', with all four fractions in hand:
               the tied half, the arm's eighth, the count's eighth and
               [intr_res]'s quarter -- and each of the four goes to a
               DIFFERENT conjunct of what the handler is handed. *)
            iDestruct "Hcpu" as "(Hcells & Hcnt)".
            iEval (rewrite /intr_count) in "Hcnt".
            iMod (sie_ghost_flip_off sie_gname (_get_Mstatus_SIE mst0)
                    ('b"1") ('b"1") vb with "Hhalf Hq1 Hcnt Hq4")
              as "(Hhalf & Hq1 & Hcnt & Hq4)".
            (* ...and the SPP/SPIE mirror MOVES with it, which no SIE flip
               does: the trap writes SPP := 1 and SPIE := old SIE = 1. *)
            iEval (rewrite /sret_tie) in "Htie".
            iMod (sret_bits_update _ _ vca vcb ('b"1" : mword 1)
                    ('b"1" : mword 1) with "Htie Hsppc") as "[Htie Hsppc]".
            iModIntro.
            iSplitL "HPC Hmsr Hmi Hcy Hti Hip".
            { rewrite i_rw_split. srs. iFrame. }
            iSplitL "HnPC Hhs Hpriv".
            { rewrite i_ro_split. srs. iFrame "HnPC Hhs Hpriv Hmc Hmicfg". }
            iRight.
            iExists (trap_scause sc_old ii), (trap_ms elp0 mst0), mdv0.
            iSplitR; [iPureIntro; exact Hcause |].
            iSplitR; [iPureIntro; exact (sconf_ms_facts_trap elp0 mst0 Hmsf) |].
            iSplitR; [iPureIntro; exact Hmm |].
            assert (Htie_eq : sret_tie (trap_ms elp0 mst0)
                              = sret_bits ('b"1" : mword 1) ('b"1" : mword 1)).
            { rewrite /sret_tie trap_ms_SPP trap_ms_SPIE HSIE1. reflexivity. }
            rewrite Htie_eq trap_ms_SIE.
            iFrame "Hms Hhalf Htie Hmie Hmdl Hmenv Hsppc Hsepc Hscause Hstval".
            iSplitL "Hstk Hbit1 Hsatp Htlb Hpcfg Hpaddr Hsnap' Hq1".
            { rewrite /sie_cap. iFrame "Hstk Hwit".
              iSplitL "Hbit1 Hsatp Htlb Hpcfg Hpaddr Hsnap'".
              { iApply (strans_inv_intro root_ppn with "Hbit1").
                iApply (tlb_res_of_cells root_ppn satp0 _ pcfg paddr
                          (conj Hmode (conj Hasid Hppn))
                          (conj HA (conj Hord (conj HX (conj HW
                             (conj HR Hcov)))))
                          with "Hsatp Htlb Hpcfg Hpaddr Hsnap' Hkinv"). }
              rewrite /sie_arm. iExact "Hq1". }
            iFrame "Hkpt".
            iSplitL "Hcells Hcnt".
            { rewrite /cpu_hart /intr_count. iFrame "Hcells Hcnt". }
            iFrame "Hclm".
            iSplitL "Hq4 Hstv".
            { iApply (intr_res_intro handler ('b"0" : mword 1) Htvd Hsb
                        with "Hq4 Hstv"). iNext. iExact "Hsp". }
            srs. rewrite Hsb.
            iFrame "Hsp Hfile Hwn".
            iApply (resv_any_intro with "Hfrag").
            (* ---------- THE INSTRUCTION ---------- *)
            iIntros (tlbf) "HW Hsrw Hsro Hsnap' Hresv'".
            iDestruct "HW" as "(Hwn & Hhalf & Htie & Hstk & Hbit1 & Hq1 &
                                Hq4 & Hstv & Hsepcx & Hscausex & Hstvalx &
                                Hsppc & Hclm & Hcpu & Hfile)".
            pose proof (s_rs_set_nPC_tlb pc0 pc0 (add_vec_int pc0 (if is_rvc then 2 else 4)) msr (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                       pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0
                       satp0 MIE_S mdv0 MENVCFG_S tlbv tlbf) as Hagf.
            iDestruct (s_rw_ext _ _ Hagf with "Hsrw") as "Hsrw".
            iDestruct (s_ro_ext (DfracOwn 1) _ _ Hagf with "Hsro") as "Hsro".
            iAssert (s_cells pc0 (add_vec_int pc0 (if is_rvc then 2 else 4)) msr (minstret_inc_flag mc micfg Supervisor) cy ti ip
                   mst0 pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0)
                   pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbf) with "[Hsrw Hsro]" as "Hcells".
            { rewrite -s_frames_cells. iFrame. }
            iEval (rewrite /s_cells) in "Hcells".
            iDestruct "Hcells" as
              "(HPC & HnPC & Hmsr & Hmi & Hcy & Hti & Hip & Htlb & Hpriv &
                Hms & Hhs & Hpcfg & Hpaddr & ? & ? & ? & ? & ? & ? & ? & ? &
                Hsatp & Hmie & Hmdl & Hmenv)".
            iAssert (sconf) with "[Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv]"
              as "Hsc".
            { iApply (sconf_of_cells mst0 mdv0 Hmsf Hmm
                        with "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl
                              Hmenv"). }
            iAssert (sie_cap kt m av true p)
              with "[Hstk Hbit1 Hsatp Htlb Hpcfg Hpaddr Hsnap' Hq1 Hq4 Hstv
                     Hsepcx Hscausex Hstvalx Hsppc Hclm Hcpu]" as "Hcap".
            { rewrite /sie_cap. iFrame "Hstk Hwit".
              iSplitL "Hbit1 Hsatp Htlb Hpcfg Hpaddr Hsnap'".
              { iApply (strans_inv_intro root_ppn with "Hbit1").
                iApply (tlb_res_of_cells root_ppn satp0 _ pcfg paddr
                          (conj Hmode (conj Hasid Hppn))
                          (conj HA (conj Hord (conj HX (conj HW
                             (conj HR Hcov)))))
                          with "Hsatp Htlb Hpcfg Hpaddr Hsnap' Hkinv"). }
              rewrite /sie_arm.
              iFrame "Hq1 Hkpt Hsepcx Hscausex Hstvalx Hsppc Hclm Hcpu".
              iApply (intr_res_intro handler vb Htvd Hsb with "Hq4 Hstv").
              iNext. iExact "Hsp". }
            iDestruct (wp_next_at true p _ CID0 (fun _ => eq_refl) with "Hwn")
              as "[Hobl Hcont]".
            (* THE CLOCK CELLS ARE LENT, NOT KEPT: [csrr time] reads mtime and
               [csrw stimecmp] rewrites mip, and both are inside the cycle's
               own frame.  They are stable across the instruction (the tick
               runs at the boundary), so the leaf gets them at existential
               values and hands them back at whatever it left. *)
            iAssert (clock_res) with "[Hcy Hti Hip]" as "Hclk".
            { iExists cy, ti, ip. iFrame. }
            iApply (swp_mono with "[Hmsr Hmi Hhs Hcont] [-]").
            2:{ iApply ("Hobl" with "Hsc Hcap Hfile HPC HnPC Hresv' Hclk"). }
            iIntros (e) "(-> & Hres)".
            iDestruct "Hres" as (npc m' av')
              "(HPC & HnPC & Hresv2 & Hclk & Hsc' & Hcap' & Hfile' & HRv)".
            iDestruct "Hclk" as (cy' ti' ip') "(Hcy & Hti & Hip)".
            iDestruct (sconf_priv_open with "Hsc'") as (msT)
              "(Hcl & Hpriv' & Hmsown)".
            iSplitR; [done|].
            iExists (s_rs pc0 npc msr (minstret_inc_flag mc micfg Supervisor)
                   cy' ti' ip'
                   mst0 pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0)
                   pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbf).
            iSplitR.
            { iPureIntro. rewrite /intr_Q. split_and!; by srs. }
            iSplitL "HPC Hmsr Hmi Hcy Hti Hip".
            { rewrite i_rw_split. srs. iFrame. }
            iSplitL "HnPC Hhs Hpriv'".
            { rewrite i_ro_split. srs. iFrame "HnPC Hhs Hpriv' Hmc Hmicfg". }
            iLeft. iExists m', av'.
            iFrame "Hcl Hcap' Hfile' Hresv2 Hcont".
            iSplitL "Hmsown"; [ by iExists msT |].
            srs. iExact "HRv". }
        iIntros (st) "[Hi | Hr]".
        - iDestruct "Hi" as (ii pr) "(-> & Hq)".
          iDestruct "Hq" as (rs2) "(%HQ & Hh)".
          iExists rs2. iSplitR; [done|]. iExact "Hh".
        - iDestruct "Hr" as (w) "(-> & Hr)".
          iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HPsi)".
          iExists rs2. iSplitR; [done|]. iFrame. }
    iIntros (u). iDestruct 1 as (rs2 mi) "(%HQ & Hrw & Hro & HPsi)".
    iExists (wrap_post rs2 mi). iSplitR; [iPureIntro; by exists rs2, mi|].
    iFrame "Hrw Hro". iExists rs2, mi. iFrame "HPsi". iPureIntro. by split. }
  { (* ================= THE CYCLE'S CONTINUATION ================= *)
    iNext. iIntros (rs3 rs1) "%Hag Hirw Hiro Hpsi".
    destruct Hag as ((rs2x & mix & _ & _) & Hag).
    iDestruct "Hpsi" as (rs2 mi) "((%HQ & %Heq) & Hpsi)".
    destruct HQ as (Hha2 & Hmi2 & Hpv2). subst rs1.
    assert (L3hs : register_lookup hart_state rs3 = HART_ACTIVE tt).
    { rewrite (Hag hart_state i_ck_hart)
        (wrap_post_other hart_state rs2 mi eq_refl eq_refl). exact Hha2. }
    assert (L3priv : register_lookup cur_privilege rs3 = Supervisor).
    { rewrite (Hag cur_privilege i_ck_priv)
        (wrap_post_other cur_privilege rs2 mi eq_refl eq_refl). exact Hpv2. }
    assert (L3pc : register_lookup (R_bitvector_64 PC) rs3
                   = register_lookup (R_bitvector_64 nextPC) rs2).
    { rewrite (Hag (R_bitvector_64 PC) i_ck_PC). apply wrap_post_PC. }
    assert (L3npc : register_lookup (R_bitvector_64 nextPC) rs3
                    = register_lookup (R_bitvector_64 nextPC) rs2).
    { rewrite (Hag (R_bitvector_64 nextPC) i_ck_nPC).
      apply (wrap_post_other (R_bitvector_64 nextPC) rs2 mi eq_refl eq_refl). }
    iEval (rewrite i_rw_split) in "Hirw".
    iDestruct "Hirw" as "(HPC & Hmsr3 & Hmi3 & Hcy3 & Hti3 & Hip3)".
    iEval (rewrite i_ro_split) in "Hiro".
    iDestruct "Hiro" as "(HnPC & Hhs3 & Hpriv3 & #Hmc3 & #Hmicfg3)".
    rewrite L3hs L3priv L3pc L3npc.
    iAssert (∀ Rres : iProp Σ,
               (pc_is (register_lookup (R_bitvector_64 nextPC) rs2) -∗ Rres) -∗
               resv_any cpu_id -∗ Rres)%I
      with "[HPC HnPC Hmsr3 Hmi3 Hcy3 Hti3 Hip3]" as "Hmkpc".
    { iIntros (Rres) "Hk Hresv". iApply "Hk". rewrite /pc_is.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hmsr3 Hmi3".
      { iExists (register_lookup (R_bitvector_64 minstret) rs3),
                (register_lookup (R_bool minstret_increment) rs3),
                (register_lookup (R_bitvector_32 mcountinhibit) rs3),
                (register_lookup (R_bitvector_64 minstretcfg) rs3).
        by iFrame "Hmsr3 Hmi3 Hmc3 Hmicfg3". }
      iExists (register_lookup (R_bitvector_64 mcycle) rs3),
              (register_lookup (R_bitvector_64 mtime) rs3),
              (register_lookup (R_bitvector_64 mip) rs3).
      by iFrame. }
    iDestruct "Hpsi" as "[HRet | HTrap]".
    - (* ---- the instruction retired: hand the caller its own bundles ---- *)
      iDestruct "HRet" as (m' av')
        "(Hcl & Hmsown & Hcap' & Hfile' & Hresv' & HRv & Hcont)".
      iDestruct "Hmsown" as (msT) "Hmsown".
      iApply ("Hmkpc" with "[Hhs3 Hpriv3 Hcl Hmsown Hcap' Hfile' HRv Hcont]
                            Hresv'").
      iIntros "Hpc'".
      iApply ("Hcont" with "[Hhs3 Hpriv3 Hcl Hmsown Hcap' Hfile'] Hpc' HRv").
      rewrite /sie_cap_gpr. iFrame "Hhs3 Hcap' Hfile'".
      iApply ("Hcl" with "Hpriv3 Hmsown").
    - (* ---- a trap was taken: run the handler and re-enter the loop ---- *)
      iDestruct "HTrap" as (sc mstT mdvT)
        "(%HscT & %HmsfT & %HmmT & HmsT & HhalfT & HtieT & HmieT &
          HmdlT & HmenvT & Hsret & HsepcT & HscauseT & HstvalT & HcapT &
          #HkptT & HcpuT & HclmT & HiresT & HspT & HfileT & HresvT & Hwn)".
      iAssert (sconf) with "[Hpriv3 HmsT HhalfT HtieT HmieT HmdlT HmenvT]"
        as "HscT".
      { iApply (sconf_of_cells mstT mdvT HmsfT HmmT
                  with "Hhw Hminv Hpriv3 HmsT HhalfT HtieT HmieT HmdlT
                        HmenvT"). }
      iApply ("Hmkpc" with "[-HresvT] HresvT"). iIntros "Hpc'".
      iAssert (ihs_entry_of kt (ires_of (ihs kt)) m av p pc0 sc (zeros' 64)
                 (register_lookup (R_bitvector_64 nextPC) rs2))
        with "[Hhs3 HscT HcapT HfileT Hsret HsepcT HscauseT HstvalT HcpuT
               HclmT HiresT Hpc']" as "Hentry".
      { rewrite /ihs_entry_of /sie_cap_gpr_of.
        iFrame "Hhs3 HscT HcapT HfileT Hsret HsepcT HscauseT HstvalT HkptT
                HcpuT HclmT Hpc'".
        iEval (rewrite intr_res_of_eq) in "HiresT". iExact "HiresT". }
      iApply (intr_handler_spec_apply
                (register_lookup (R_bitvector_64 nextPC) rs2) m av p pc0 sc
                (zeros' 64) Hpc0 HscT with "HspT Hentry").
      iIntros (c' Hs'). rewrite /ihs_post_of. iIntros "Hcg Hpc".
      iDestruct (wp_next_retarget CID0 c' true p _ Hs' with "Hwn") as "Hwn".
      iApply ("IH" $! c' with "Hcg Hpc [Hwn]"). iNext. iExact "Hwn". }
Qed.

(* ===================================================================== *)
(* §4' THE CLOCK-FREE READING.  The three clock cells go straight through,
   which is what every leaf that does not name one wants -- and it is what
   keeps the 68 call sites of the funnel unchanged.                        *)
(* ===================================================================== *)
Lemma wp_exec_step_intr `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId} `{CID0 : CpuId}
    {kt : ktier} (pc0 : mword 64) (m : regfile) (av : nat) (p : mword 64)
    (is_rvc : bool) (i : instruction)
    (R : mword 64 -> regfile -> nat -> iProp Σ) :
  ret_pc pc0 = pc0 ->
  sie_cap_gpr kt m av true p -∗
  pc_is pc0 -∗
  instr pc0 is_rvc i -∗
  ▷ wp_next true p (fun CID => intr_cb kt m av p pc0 is_rvc i R (CID := CID)) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros Hpc0. iIntros "Hcg Hpc Hinstr Hbody".
  iApply (wp_exec_step_intr_clock pc0 m av p is_rvc i R Hpc0
            with "Hcg Hpc Hinstr [Hbody]").
  iNext. iIntros (CID Hs).
  iDestruct (wp_next_at true p _ CID Hs with "Hbody") as "Hb".
  iEval (rewrite /intr_cb) in "Hb".
  iDestruct "Hb" as "[Hobl Hcont]".
  rewrite /intr_cb_clock.
  iSplitR "Hcont"; [| iExact "Hcont" ].
  iIntros "Hsc Hcap Hfile HPC HnPC Hresv Hclk".
  iApply (swp_mono (CID := CID) with "[Hclk] [-]");
    [| iApply ("Hobl" with "Hsc Hcap Hfile HPC HnPC Hresv") ].
  iIntros (e) "(-> & Hres)".
  iDestruct "Hres" as (npc m' av')
    "(HPC & HnPC & Hresv2 & Hsc' & Hcap' & Hfile' & HRv)".
  iSplitR; [done|]. iExists npc, m', av'. iFrame.
Qed.

(* ===================================================================== *)
(* §5 THE COMBINED S-MODE REGIME AT THE [swp] LAYER.                      *)
(*                                                                       *)
(* [IntrDefs.strans_regime] is the hart's translation slot as a DISJUNCTION *)
(* -- Bare before kvminithart, the shared kernel table after -- and its    *)
(* exec-side fields dispatch on the ghost bit.  This is the same           *)
(* dispatch one layer up, onto [SRegime.bare_regime_swp] /                 *)
(* [kpt_share_regime_swp].                                                *)
(*                                                                       *)
(* WHAT MOVES FROM THE SIDE CONDITION INTO THE RESIDUE, and it is the     *)
(* whole design of the instance: each arm's satp MODE.  The side condition *)
(* is a Prop the CALLER picks and the residue is the ghost's own arm, so   *)
(* without the mode in the residue the two cross cases (caller says Bare,  *)
(* slot is KPT, and back) are live and unprovable -- the Bare translate    *)
(* would have to hand back a KPT residue at a file it does not know did    *)
(* not fill the TLB.  With the mode in BOTH, 'b"0000" vs 'b"1000" refutes  *)
(* the crossings outright and only the two matching cases remain.         *)
(* ===================================================================== *)
Section StransSwp.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the KPT arm's root is a FUNCTION of satp, so the instance needs no
     existential for it -- which is what lets the residue and the side
     condition name the same one, and what makes the residue statable at
     the two CELL VALUES rather than at the file ([sr_swp_res_agree]). *)
  Definition strans_root_of (satp0 : mword 64) : mword 44 :=
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)).

  Definition strans_root (rs : regstate) : mword 44 :=
    strans_root_of (register_lookup satp rs).

  Definition strans_res_at (satp0 : mword 64) (tv : type_of_register tlb)
      : iProp Σ :=
    ((strans_pending ∗ (∃ v : mword 64, stvec ↦ᵣ v) ∗ ⌜ bare_satp_ok satp0 ⌝)
     ∨ (strans_kpt ∗
        ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
        kpt_res_at (strans_root_of satp0) satp0 tv))%I.

  Definition strans_swp_res (rs : regstate) : iProp Σ :=
    strans_res_at (register_lookup satp rs) (register_lookup tlb rs).

  (* the regime's own constraint on the satp VALUE: whichever arm the ghost
     is in, and NOTHING that picks the arm -- the arm is the ghost's. *)
  Definition strans_satp_ok (satp0 : mword 64) : Prop :=
    bare_satp_ok satp0 \/ kpt_satp_ok (strans_root_of satp0) satp0.

  Lemma strans_swp_res_agree (rs : regstate) :
    strans_res_at (register_lookup satp rs) (register_lookup tlb rs)
    ⊣⊢ strans_swp_res rs.
  Proof. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE BUNDLE FACE.  [strans_inv] hides the four cells the swp engine    *)
  (* needs in its FRAME; open/close dispatch on the ghost bit and delegate *)
  (* to the two instances' own faces.  The cross cases are refuted the     *)
  (* same way the translate's are: the pure satp_ok says Bare while the    *)
  (* residue's ghost says KPT, or the other way, and the two modes differ. *)
  (* ------------------------------------------------------------------ *)
  Lemma strans_swp_open :
    strans_inv -∗
    ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜ strans_satp_ok satp0 ⌝ ∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
      satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      strans_res_at satp0 tlbv.
  Proof.
    iIntros "[(Hpend & Hb & Hstv) | (Hkpt & Hk)]".
    - iDestruct (bare_swp_open with "Hb") as (satp0 tlbv pcfg paddr)
        "(%Hmode & %Hpmp & Hsatp & Htlb & Hpcfg & Hpaddr & _)".
      iExists satp0, tlbv, pcfg, paddr.
      iSplitR; [iPureIntro; left; exact Hmode |].
      iSplitR; [iPureIntro; exact Hpmp |].
      iFrame "Hsatp Htlb Hpcfg Hpaddr".
      rewrite /strans_res_at. iLeft. iFrame "Hpend Hstv".
      iPureIntro. exact Hmode.
    - iDestruct "Hk" as (root_ppn) "Ht".
      iDestruct (kpt_swp_open root_ppn with "Ht") as (satp0 tlbv pcfg paddr)
        "(%Hsok & %Hpmp & Hsatp & Htlb & Hpcfg & Hpaddr & Hres)".
      pose proof Hsok as Hsok'. destruct Hsok' as (Hmode & Hasid & Hppn).
      subst root_ppn.
      iExists satp0, tlbv, pcfg, paddr.
      iSplitR; [iPureIntro; right; exact Hsok |].
      iSplitR; [iPureIntro; exact Hpmp |].
      iFrame "Hsatp Htlb Hpcfg Hpaddr".
      rewrite /strans_res_at. iRight. iFrame "Hkpt Hres".
      iPureIntro. exact Hmode.
  Qed.

  Lemma strans_swp_close (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    strans_satp_ok satp0 ->
    pmp_ent0_ok pcfg paddr ->
    ⊢ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
      pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
      strans_res_at satp0 tlbv -∗ strans_inv.
  Proof.
    intros Hsok Hpmp. iIntros "Hsatp Htlb Hpcfg Hpaddr Hres".
    rewrite /strans_res_at.
    iDestruct "Hres" as "[(Hpend & Hstv & %Hmb) | (Hkpt & %Hmk & Hres)]".
    - iLeft. iFrame "Hpend Hstv".
      iApply (bare_swp_close satp0 tlbv pcfg paddr Hmb Hpmp
                with "Hsatp Htlb Hpcfg Hpaddr [//]").
    - destruct Hsok as [Hbad | Hsok].
      { exfalso. rewrite /bare_satp_ok in Hbad. rewrite Hmk in Hbad.
        vm_compute in Hbad. discriminate. }
      iRight. iFrame "Hkpt". iExists (strans_root_of satp0).
      iApply (kpt_swp_close (strans_root_of satp0) satp0 tlbv pcfg paddr
                Hsok Hpmp with "Hsatp Htlb Hpcfg Hpaddr Hres").
  Qed.

  Definition strans_swp_side (acc : MemoryAccessType mem_payload)
      (va : mword 64) (ppn : mword 44) (kp : kperm) (Db : register -> bool)
      (Drw Dro : gset register) (rs : regstate) (dst : mstate) : Prop :=
    bare_swp_side acc va ppn kp Db Drw Dro rs dst
    \/ kpt_swp_side (strans_root rs) acc va ppn kp Db Drw Dro rs dst.

  (* satp survives a translation: the walk's only write is the TLB fill. *)
  Lemma strans_satp_landing (rs rsf : regstate) :
    (rsf = rs \/ exists tv, rsf = register_set tlb tv rs) ->
    register_lookup satp rsf = register_lookup satp rs.
  Proof.
    intros [-> | (tv & ->)]; [reflexivity |].
    rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ].
  Qed.

  Lemma strans_root_landing (rs rsf : regstate) :
    (rsf = rs \/ exists tv, rsf = register_set tlb tv rs) ->
    strans_root rsf = strans_root rs.
  Proof.
    intros H. rewrite /strans_root (strans_satp_landing rs rsf H). reflexivity.
  Qed.

  Lemma strans_swp_translate :
    forall (acc : MemoryAccessType mem_payload)
        (Drw Dro : gset register) (Df : register -> dfrac)
        (rs : regstate) (dst : mstate) (Db : register -> bool)
        (va pa : mword 64) (ppn : mword 44) (kp : kperm) (rr : option resv),
      Drw ## Dro ->
      s_acc_ok acc ->
      kperm_allows kp acc ->
      (mstatus : register) ∈ Drw ∪ Dro ->
      (cur_privilege : register) ∈ Drw ∪ Dro ->
      (satp : register) ∈ Drw ∪ Dro ->
      (tlb : register) ∈ Drw ->
      (pma_regions : register) ∈ Drw ∪ Dro ->
      (pmpcfg_n : register) ∈ Drw ∪ Dro ->
      (pmpaddr_n : register) ∈ Drw ∪ Dro ->
      (htif_tohost_base : register) ∈ Drw ∪ Dro ->
      (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, Db r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
      (forall r : register, D_leafchk r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
      register_lookup cur_privilege rs = Supervisor ->
      register_lookup htif_tohost_base rs = None ->
      register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
      register_lookup misa dst.(sregs) = MISA_C ->
      register_lookup menvcfg dst.(sregs) = MENVCFG_S ->
      _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor) dst
        = Some (Supervisor, dst) ->
      goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor)
        dst = true ->
      exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
      goodb Db (is_shadow_stack_access acc) dst = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                            (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa ->
      sr_adm strans_regime va ppn ->
      strans_swp_side acc va ppn kp Db Drw Dro rs dst ->
      ⊢ kmap_at (svpn_of va) ppn kp -∗ gen_cert -∗ resv_frag cpu_id rr -∗
        strans_swp_res rs -∗
        hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
        swp (translateAddr (Virtaddr va) acc)
          (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                    ∃ rsf : regstate,
                      ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                      hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                      strans_swp_res rsf ∗ resv_any cpu_id).
  Proof.
    intros acc Drw Dro Df rs dst Db va pa ppn kp rr Hdisj Hacc Hallow
      HDmst HDpriv HDsatp HWtlb HDpma HDcfg HDaddr HDhtif HDb Hag HDlc Haglc
      Hcp Hhtif Hmstag Hmisa Hmenv HSXL Heff Heffg Hss Hssg Hcanon Hconcat
      Hadm Hside.
    iIntros "#Hat #Hcert Hfrag Hres Hrw Hro".
    iEval (rewrite /strans_swp_res /strans_res_at) in "Hres".
    iDestruct "Hres" as "[(Hpend & Hstv & %Hmb) | (Hkpt & %Hmk & Hres)]".
    - (* ---- the slot is BARE ---- *)
      destruct Hside as [Hbs | Hks].
      2:{ destruct Hks as (Hmode & _). rewrite Hmb in Hmode.
          exfalso. vm_compute in Hmode. discriminate. }
      iApply (swp_mono with "[Hpend Hstv] [-]");
        [| iApply (bare_swp_translate acc Drw Dro Df rs dst Db va pa ppn kp rr
                     Hdisj Hacc Hallow HDmst HDpriv HDsatp HWtlb HDpma HDcfg
                     HDaddr HDhtif HDb Hag HDlc Haglc Hcp Hhtif Hmstag Hmisa
                     Hmenv HSXL Heff Heffg Hss Hssg Hcanon Hconcat Hadm Hbs
                     with "Hat Hcert Hfrag [//] Hrw Hro") ].
      iIntros (r) "(-> & %rsf & %Hshape & Hrw & Hro & _ & Hany)".
      iSplitR; [done |]. iExists rsf. iFrame "Hrw Hro Hany".
      iSplitR; [iPureIntro; exact Hshape |].
      rewrite /strans_swp_res /strans_res_at.
      iLeft. iFrame "Hpend Hstv". iPureIntro.
      rewrite (strans_satp_landing rs rsf Hshape). exact Hmb.
    - (* ---- the slot is the SHARED KERNEL TABLE ---- *)
      destruct Hside as [Hbs | Hks].
      { destruct Hbs as (Hmode & _). rewrite Hmk in Hmode.
        exfalso. vm_compute in Hmode. discriminate. }
      iApply (swp_mono with "[Hkpt] [-]");
        [| iApply (kpt_swp_translate (strans_root rs) acc Drw Dro Df rs dst Db
                     va pa ppn kp rr
                     Hdisj Hacc Hallow HDmst HDpriv HDsatp HWtlb HDpma HDcfg
                     HDaddr HDhtif HDb Hag HDlc Haglc Hcp Hhtif Hmstag Hmisa
                     Hmenv HSXL Heff Heffg Hss Hssg Hcanon Hconcat I Hks
                     with "Hat Hcert Hfrag Hres Hrw Hro") ].
      iIntros (r) "(-> & %rsf & %Hshape & Hrw & Hro & Hres & Hany)".
      iSplitR; [done |]. iExists rsf. iFrame "Hrw Hro Hany".
      iSplitR; [iPureIntro; exact Hshape |].
      rewrite /strans_swp_res /strans_res_at.
      rewrite (strans_satp_landing rs rsf Hshape).
      iRight. iFrame "Hkpt". iFrame "Hres".
      iPureIntro. exact Hmk.
  Qed.

  Definition strans_regime_swp : s_regime_swp strans_regime :=
    SRegimeSwp strans_regime strans_swp_res strans_swp_side
      strans_swp_translate strans_res_at strans_satp_ok strans_swp_res_agree
      strans_swp_open strans_swp_close.

End StransSwp.
