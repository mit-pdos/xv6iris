(* HartMLeaf.v -- THE FIRST PER-WORD LEAF CONVERSION (worklist 0f′(a)):
   the pilot's instruction, [c.sw a4,0(a5)] at [main+0xb0], proven
   BOUNDARY TO BOUNDARY -- WP Loop from WP Loop -- through the real
   wrapper: restart at both ticks, span + the segment-1 characterization,
   the minstret_increment chop, span + the fetch characterization, the
   fetch event from persistent TEXT bytes, the two-footprint batch through
   decode + execute, the store event, and the batch through the tail
   (including, on tick = true, the whole tick_clock stretch).

   RAW-CELL FORM, deliberately: the [mmode_config]/[pc_is]/[minstret_inv]
   bundles live above the red line until B′, and owning the counter/clock
   cells directly both matches what a pre-B′ statement can say and lets
   the tail batch functionally (every register the tail touches is owned
   or pinned -- no ∀-reads).  The B′ wrappers re-introduce the invariant
   openings around the corresponding single nodes.

   What this file evidences: the whole kit composes end to end on a real
   kernel instruction with the honest wrapper -- the design doc's Phase B
   gate in its per-word form -- and its coqc -time is the per-leaf cost
   model for Phase C. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec
        HartLift HartRegNode HartSpan HartSpanChar HartLift2
        HartEvents HartMCycle HartMDispatch HartMPmp HartMFetch HartPilot.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 0. The concrete facts of this word (closed; vm).  [hp_pc]/[hp_flag]/    *)
(*    [hp_wf]/[hp_one] are HartPilot's.                                    *)
(* ====================================================================== *)

Lemma ml_align_v : is_aligned_vaddr (Virtaddr hp_pc) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ml_align_p : is_aligned_paddr (Physaddr hp_pc) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ml_ram : addr_is_ram hp_pc.
Proof.
  rewrite /addr_is_ram. split; [apply Z.leb_le|apply Z.ltb_lt];
    vm_cast_no_check (eq_refl true).
Qed.

(* ====================================================================== *)
(* 1. The footprints.                                                      *)
(* ====================================================================== *)

(* the span footprint: what the wrapper may write that we own *)
Definition ml_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register) ]}.

(* the read-only pins (span [Dro] and batch [Dro] alike) *)
Definition ml_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register); (misa : register);
     (hart_state : register); (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register); (pma_regions : register);
     (pmpcfg_n : register); (htif_tohost_base : register);
     (elp : register); (mseccfg : register);
     (R_bitvector_64 mtimecmp : register);
     (R_bitvector_64 stimecmp : register) ]}.

(* the LEAF batch's exclusive footprint: the span's, plus the GPRs this
   word touches, plus the counter/clock cells (raw-cell form) *)
Definition ml_DrwL : gset register :=
  ml_Drw ∪
  {[ (R_bitvector_64 x14 : register); (R_bitvector_64 x15 : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 minstret : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

(* ====================================================================== *)
(* 2. The statement.                                                       *)
(* ====================================================================== *)

Section leaf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_word_main_b0
      (q1 q2 q3 q4 q5 q6 q7 q8 : Qp)
      (mst0 misa0 mcfg : SailStdpp.Values.mword 64)
      (mc : SailStdpp.Values.mword 32)
      (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp)
      (tcmp scmp : SailStdpp.Values.mword 64)
      (mi0 : bool) (ms0 cy0 ti0 ip0 : SailStdpp.Values.mword 64)
      (vold : bv 32) :
    eq_vec (_get_Misa_S misa0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE mst0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Mstatus_MPRV mst0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    cur_privilege ↦ᵣ{DfracOwn q1} Machine -∗
    mstatus ↦ᵣ{DfracOwn q2} mst0 -∗
    misa ↦ᵣ□ misa0 -∗
    hart_state ↦ᵣ{DfracOwn q3} HART_ACTIVE tt -∗
    (R_bitvector_32 mcountinhibit) ↦ᵣ{DfracOwn q4} mc -∗
    (R_bitvector_64 minstretcfg) ↦ᵣ{DfracOwn q5} mcfg -∗
    pma_regions ↦ᵣ□ pmar0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q6} pcfg -∗
    htif_tohost_base ↦ᵣ□ None -∗
    elp ↦ᵣ□ elp0 -∗
    mseccfg ↦ᵣ□ (SailStdpp.Values.mword_of_int 0) -∗
    (R_bitvector_64 mtimecmp) ↦ᵣ{DfracOwn q7} tcmp -∗
    (R_bitvector_64 stimecmp) ↦ᵣ{DfracOwn q8} scmp -∗
    (R_bitvector_64 PC) ↦ᵣ hp_pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ hp_pc -∗
    (R_bitvector_64 x14) ↦ᵣ (SailStdpp.Values.mword_of_int 1) -∗
    (R_bitvector_64 x15) ↦ᵣ hp_flag -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗
    (R_bitvector_64 minstret) ↦ᵣ ms0 -∗
    (R_bitvector_64 mcycle) ↦ᵣ cy0 -∗
    (R_bitvector_64 mtime) ↦ᵣ ti0 -∗
    (R_bitvector_64 mip) ↦ᵣ ip0 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add hp_pc j) ↦ₓ□ nth_byte hp_wf j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte vold j) -∗
    gen_cert -∗
    (* THE CONTINUATION: the machine one instruction later.  PC/nextPC at
       pc+2 (a compressed store); the stored word at 1; the counter cells
       moved as the wrapper moves them; the clock cells at SOME values
       (tick-dependent -- existential, exactly the value-agnosticism the
       B′ invariants will encode); every pin returned untouched. *)
    (∀ (mi1 : bool) (ms1 cy1 ti1 ip1 : SailStdpp.Values.mword 64),
       cur_privilege ↦ᵣ{DfracOwn q1} Machine -∗
       mstatus ↦ᵣ{DfracOwn q2} mst0 -∗
       hart_state ↦ᵣ{DfracOwn q3} HART_ACTIVE tt -∗
       (R_bitvector_32 mcountinhibit) ↦ᵣ{DfracOwn q4} mc -∗
       (R_bitvector_64 minstretcfg) ↦ᵣ{DfracOwn q5} mcfg -∗
       pmpcfg_n ↦ᵣ{DfracOwn q6} pcfg -∗
       (R_bitvector_64 mtimecmp) ↦ᵣ{DfracOwn q7} tcmp -∗
       (R_bitvector_64 stimecmp) ↦ᵣ{DfracOwn q8} scmp -∗
       (R_bitvector_64 PC) ↦ᵣ (add_vec_int hp_pc 2) -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int hp_pc 2) -∗
       (R_bitvector_64 x14) ↦ᵣ (SailStdpp.Values.mword_of_int 1) -∗
       (R_bitvector_64 x15) ↦ᵣ hp_flag -∗
       (R_bool minstret_increment) ↦ᵣ mi1 -∗
       (R_bitvector_64 minstret) ↦ᵣ ms1 -∗
       (R_bitvector_64 mcycle) ↦ᵣ cy1 -∗
       (R_bitvector_64 mtime) ↦ᵣ ti1 -∗
       (R_bitvector_64 mip) ↦ᵣ ip1 -∗
       ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte hp_one j) -∗
       WP (LoopE gen_id cpu_id : expr riscv_lang)) -∗
    WP (LoopE gen_id cpu_id : expr riscv_lang).
  Proof.
    (* TODO(agent): the full chain -- the plan, stage by stage, with the
       worked exemplar for each in parentheses:
       0. iApply wp_hart_restart (RiscvExec); iNext; iIntros (tick);
          rewrite (mwrap_riscv_step tick).  Let KT := the tick's tail.
       1. ASSEMBLE THE FRAMES from the cells: hreg_frame <anchor> ml_Drw
          from the PC/nextPC cells and hreg_frame_ro Df <anchor> ml_Dro
          from the thirteen pins, where the ANCHOR file is chosen as a
          set-tower pinning exactly the framed registers' values (any file
          with those lookups; build with register_set over an arbitrary
          base -- e.g. (cold_regs (mword_of_int 0)) -- and prove the
          lookups by register_lookup_set/irrelevant_register_set chains;
          keep the tower as a local Definition).  Df maps the □-pins to
          DfracDiscarded and the qN ones to DfracOwn qN.  big_sepS over the
          literal sets assembles by repeated big_sepS_insert (the sets are
          concrete; membership/non-membership side goals by set_solver --
          SAFE here: no cursor equations are ever in context in this proof;
          keep it that way, or use bool_decide computations).
       2. wp_hart_span ml_Drw ml_Dro (HartSpan) at (mwrap KT); its
          stops-false side fact via a local hregread_at-based bridge
          (HartMCycle has the pattern as a Local; re-derive).  In the
          landing continuation: mseg1_charK (HartMCycle) with the pins
          read off the anchor tower.
       3. The chop: wp_hart_regwrite (HartRegNode) at the
          minstret_increment write (projection from the char), with the
          caller's raw cell: in the σ-callback, reg_update the cell to
          (mseg1_b mc mcfg); mstate_interp (set_reg ...) re-established
          directly (no invariant in the raw-cell form).
       4. wp_hart_span again from (mseg2_startK KT); mfetch_charK
          (HartMFetch) gives the walker-pinned landing W, the fetch
          request projection, and the agreement.
       5. The fetch event: wp_hart_ram_read (HartEvents) at
          (mfetch_req hp_pc); the read_bytes witness from text_read_bytes
          (HartLift2) on the ↦ₓ□ premise; dev_addr false from ml_ram
          (addr_is_ram → not dev_addr: find the geometry lemma -- grep
          dev_addr lemmas in DevModel/RiscvPtsto; if none exists inline a
          vm_cast fact at the concrete address).
       6. The leaf batch: wp_hart_batch2 (HartLift2) with ml_DrwL/ml_Dro
          from the enlarged frame (add the five counter/clock cells and
          the two GPRs to the rw-frame; anchor tower extended
          correspondingly), at the cursor
          (anchor', hread_resume (bv_unsigned hp_wf) W).  Its landing
          projections: hwrite_req_at for the STORE event -- computed with
          the INCANTATION (HartMCycle's comment) + premise rewrites; W's
          spine reduction is the expensive part (~a minute, the per-leaf
          cost model -- measure it).  NOTE hp_reqw (HartPilot) already
          names the store request; the landing should project to it.
       7. The store event: wp_hart_ram_write (HartEvents) + phys_upd_window
          (HartPilot) moving the four bytes to hp_one.
       8. The tail batch: wp_hart_batch2 again to Ret -- on tick = false
          the landing is Ret after the minstret bookkeeping; on tick = true
          it runs through tick_clock as well (mtimecmp/stimecmp/
          mcountinhibit are pinned, the three clock cells are in ml_DrwL).
          hnode_tag landing = 0 (per-tick projection facts), destruct the
          unit, rewrite /LoopE.
       9. Fire the continuation with the cells extracted BACK out of the
          frames (big_sepS deletes) at the final tower's values; the
          existentials mi1/ms1/cy1/ti1/ip1 take whatever the tower says
          (mi1 := mseg1_b mc mcfg, ms1 := the bump-or-not, clock cells per
          tick).
       PROOF-ENGINEERING RULES: everything in the design doc's GOTCHA --
       rule/instance shape not needed here (this IS the instance; the
       spans/chars carry the abstraction), but the cursor discipline is:
       every batch at a pair literal or named Definition one delta from
       it; landing folds via have-by-reflexivity in the definitions' own
       spelling; clear folding equations immediately; empty_subseteq for
       masks; never vm past a resume; the incantation for open spines.
       If the per-leaf reduction (stage 6/8) exceeds ~3 minutes of tactic
       time, or any Qed exceeds ~5 minutes, STOP and report numbers. *)
  Admitted.

End leaf.
