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
     - [b = false]: [wp_instr_s_sconf_off], STATED AND NOT PROVED, and
       deliberately isolated -- it is [SmodeCorePt.wp_instr_s_config_regime] at
       [strans_regime], whose surface is still moving in that file.  When it
       lands, that lemma's proof is the ONLY edit here.

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
Require Import SmodeCore.
Require Import AlignBits.
Require Import HartSwp HartMFrame WpMmodeSwpBase.
Require Import IntrDefs WpIntrInv.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section WpSmodeIntr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
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
  Lemma wp_instr_s_intr (m : regfile) (n : nat)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : mword 64 -> regfile -> nat -> iProp Σ) :
    ret_pc pc = pc ->
    sie_cap_gpr kt m n true p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    ▷ wp_next true p (fun (CID : CpuId) =>
        (sconf -∗
         sie_cap kt m n true p -∗
         gpr_file (tp_pin m) -∗
         (R_bitvector_64 PC) ↦ᵣ pc -∗
         (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
         resv_any cpu_id -∗
         swp (execute i)
           (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
              ∃ (npc : mword 64) (m' : regfile) (n' : nat),
                (R_bitvector_64 PC) ↦ᵣ pc ∗
                (R_bitvector_64 nextPC) ↦ᵣ npc ∗
                resv_any cpu_id ∗
                sconf ∗ sie_cap kt m' n' true p ∗ gpr_file (tp_pin m') ∗
                R npc m' n'))
        ∗ (∀ (npc : mword 64) (m' : regfile) (n' : nat),
             sie_cap_gpr kt m' n' true p -∗ pc_is npc -∗ R npc m' n' -∗
             WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_exec_step_intr pc m n p is_rvc i R). Qed.

  (* =================================================================== *)
  (* §2 THE SIE-AGNOSTIC FUNNEL over [sconf] + [sie_cap]: the capability's *)
  (* SIE INDEX [b] picks the arm.  Both arms present the SAME leaf-facing  *)
  (* obligation, which is the point of the bundle: nothing above this      *)
  (* lemma mentions the mode.                                             *)
  (*                                                                      *)
  (* THE '0' ARM IS STATED, NOT PROVED (below), and it is isolated ON      *)
  (* PURPOSE: it is [SmodeCorePt.wp_instr_s_config_regime] at              *)
  (* [strans_regime], whose surface is mid-change in that file (the        *)
  (* [sr_swp_open] / [sr_swp_close] regime fields that put [sr_inv R] back *)
  (* on it).  Everything else here is proved, so when that lands the       *)
  (* instantiation is the ONLY edit.                                      *)
  (* =================================================================== *)
  Definition sconf_step_obl (m : regfile) (n : nat) (b : bool)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : mword 64 -> regfile -> nat -> iProp Σ) (CID : CpuId) : iProp Σ :=
    ((sconf -∗
      sie_cap kt m n b p -∗
      gpr_file (tp_pin m) -∗
      (R_bitvector_64 PC) ↦ᵣ pc -∗
      (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      resv_any cpu_id -∗
      swp (execute i)
        (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
           ∃ (npc : mword 64) (m' : regfile) (n' : nat),
             (R_bitvector_64 PC) ↦ᵣ pc ∗
             (R_bitvector_64 nextPC) ↦ᵣ npc ∗
             resv_any cpu_id ∗
             sconf ∗ sie_cap kt m' n' b p ∗ gpr_file (tp_pin m') ∗
             R npc m' n'))
     ∗ (∀ (npc : mword 64) (m' : regfile) (n' : nat),
          sie_cap_gpr kt m' n' b p -∗ pc_is npc -∗ R npc m' n' -∗
          WP (Loop : expr riscv_lang)))%I.

  (* THE SIE=0 ARM.  STATED, NOT PROVED -- see the note above; it is
     [SmodeCorePt.wp_instr_s_config_regime strans_regime] once that file's
     regime-open/close fields land, with SIE=0 read off the ghost. *)
  Lemma wp_instr_s_sconf_off (m : regfile) (n : nat)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : mword 64 -> regfile -> nat -> iProp Σ) :
    sie_cap_gpr kt m n false p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    ▷ wp_next false p (sconf_step_obl m n false pc is_rvc i R) -∗
    WP (Loop : expr riscv_lang).
  Proof.
  Admitted.

  Lemma wp_instr_s_sconf
      (m : regfile) (n : nat) (b : bool)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (R : mword 64 -> regfile -> nat -> iProp Σ) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    ▷ wp_next b p (sconf_step_obl m n b pc is_rvc i R) -∗
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
      iApply (wp_instr_s_intr m n pc is_rvc i R Hpc0 with "Hcg Hpc Hinstr").
      iExact "H".
    - (* ---- b = false: the dispatch-None engine, SIE=0 from the ghost ---- *)
      iApply (wp_instr_s_sconf_off m n pc is_rvc i R with "Hcg Hpc Hinstr").
      iExact "H".
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
    iApply (wp_instr_s_sconf m n b pc true base
              (fun npc m' n' => ⌜npc = add_vec_int pc 2⌝ ∗
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
      iExists (add_vec_int pc 2),
              (<[Regidx rd := regval_into_reg wval]> m), n.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hsc". { iFrame "Hhw Hminv Hsc". }
      iSplitL "Hcap".
      { iApply (sie_cap_retarget m
                  (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap"). }
      iSplitL "Hfile".
      { iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp))
          in "Hfile". iExact "Hfile". }
      done.
    - (* the continuation: the engine resumes on the hart [Hs] names *)
      iIntros (npc m' n') "Hcg' Hpc' (-> & -> & ->)".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* the 4-byte (base-encoding) variant: pc advances by 4 *)
  Lemma wp_gpr_write_s_sconf_base
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
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
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
    iApply (wp_instr_s_sconf m n b pc false base
              (fun npc m' n' => ⌜npc = add_vec_int pc 4⌝ ∗
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
      iExists (add_vec_int pc 4),
              (<[Regidx rd := regval_into_reg wval]> m), n.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hsc". { iFrame "Hhw Hminv Hsc". }
      iSplitL "Hcap".
      { iApply (sie_cap_retarget m
                  (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap"). }
      iSplitL "Hfile".
      { iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp))
          in "Hfile". iExact "Hfile". }
      done.
    - (* the continuation: the engine resumes on the hart [Hs] names *)
      iIntros (npc m' n') "Hcg' Hpc' (-> & -> & ->)".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

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
