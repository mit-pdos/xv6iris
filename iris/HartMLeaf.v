(* HartMLeaf.v -- THE LEAF: [WP Loop] from [WP Loop] through one real
   instruction, composed from the per-model-function [swp] facts.

   There is no new machinery here at all -- that is the point.  The file is
   [try_step]'s own spine, walked with [swp_bind_use] / [swp_use_cerN],
   with each call discharged by the fact that already exists for it, the
   register file threaded by [t_peel], and the leaf-local data (the word,
   the text bytes, the flag cell, the page-boundary and GPR equations)
   supplied as premises. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartRunGen HartEvents HartMCycle HartMDispatch HartMPmp
        HartMFetch HartMDecode HartMStore HartMRun HartPilot.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec HartLift2.
Require Import SailStdpp.Base.
Local Open Scope Z_scope.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Local Ltac l_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq get_config_rvfi].

Local Lemma hfrun_cE_Zca (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D ->
  eq_vec (_get_Misa_C (register_lookup misa rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hfrun 4 D Drw rs (currentlyEnabled Ext_Zca) = Some (true, rs).
Proof.
  intros HD HC. rewrite cE_Zca_eq. d_cbn.
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD). d_cbn.
  rewrite HC. d_cbn. apply hfrun_ret.
Qed.

(* THE POST-STATE of one cycle body.  Three writes are PINNED -- the
   minstret_increment flag, nextPC (the compressed instruction is 2 bytes)
   and PC (tick_pc commits nextPC) -- and minstret is left as a parameter.
   Naming the file is what lets a caller say where the machine ended; an
   existential over the WHOLE file says only that the frames came back,
   which specifies nothing, since a frame constrains only its own
   footprint and agreement-on-nothing is vacuous.

   MINSTRET IS THE ONE CELL WORTH QUANTIFYING, and quantifying its VALUE
   rather than pinning it is what makes the statement branch-free: whether
   the counter bumps depends on a config bit, and BOTH branches are
   value-agnostic, so a caller that does not care what minstret holds
   needs no premise about it.  That is the raw-cell shadow of what design
   §5 actually prescribes -- minstret and minstret_increment belong in
   [MinstretInv], touched by single-node rules that open the invariant
   around exactly that node, and the invariant pins no value for exactly
   this reason.  [MinstretInv] is above the red line, so it cannot be
   named here yet; B′ replaces this parameter with the invariant. *)
Definition hp_post (rs : regstate) (mi : SailStdpp.Values.mword 64)
    : regstate :=
  register_set (R_bitvector_64 minstret) mi
    (register_set (R_bitvector_64 PC) (add_vec_int hp_pc 2)
       (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
          (register_set (R_bool minstret_increment)
             (minstret_inc_flag
                (register_lookup (R_bitvector_32 mcountinhibit) rs)
                (register_lookup (R_bitvector_64 minstretcfg) rs)
                (register_lookup cur_privilege rs)) rs))).

(* [hp_post] IS the generic wrapper's post-file at this word: the
   instruction leaves [nextPC] at pc+2 over the prelude's file, and the
   tail commits it into PC and bumps minstret.  One [register_lookup_set]
   away from syntactic identity -- which is what makes [swp_try_step_hp]
   a corollary of [swp_try_step_gen] rather than a re-proof. *)
Lemma wrap_post_hp (rs : regstate) (mi : SailStdpp.Values.mword 64) :
  wrap_post (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
               (wrap_pre rs)) mi
  = hp_post rs mi.
Proof.
  unfold wrap_post, hp_post, wrap_pre. by rewrite register_lookup_set.
Qed.

(* what one cycle body does to a single cell: four named writes, and
   nothing else -- so a caller reads the post-file off cell by cell *)
Lemma hp_post_PC (rs : regstate) (mi : SailStdpp.Values.mword 64) :
  register_lookup (R_bitvector_64 PC) (hp_post rs mi) = add_vec_int hp_pc 2.
Proof.
  unfold hp_post.
  rewrite (irrelevant_register_set (R_bitvector_64 PC)
             (R_bitvector_64 minstret) _ _ eq_refl).
  by rewrite register_lookup_set.
Qed.

Lemma hp_post_nPC (rs : regstate) (mi : SailStdpp.Values.mword 64) :
  register_lookup (R_bitvector_64 nextPC) (hp_post rs mi)
  = add_vec_int hp_pc 2.
Proof.
  unfold hp_post.
  rewrite (irrelevant_register_set (R_bitvector_64 nextPC)
             (R_bitvector_64 minstret) _ _ eq_refl).
  rewrite (irrelevant_register_set (R_bitvector_64 nextPC)
             (R_bitvector_64 PC) _ _ eq_refl).
  by rewrite register_lookup_set.
Qed.

Lemma hp_post_ms (rs : regstate) (mi : SailStdpp.Values.mword 64) :
  register_lookup (R_bitvector_64 minstret) (hp_post rs mi) = mi.
Proof. unfold hp_post. by rewrite register_lookup_set. Qed.

Lemma hp_post_mi (rs : regstate) (mi : SailStdpp.Values.mword 64) :
  register_lookup (R_bool minstret_increment) (hp_post rs mi)
  = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
      (register_lookup (R_bitvector_64 minstretcfg) rs)
      (register_lookup cur_privilege rs).
Proof.
  unfold hp_post.
  rewrite (irrelevant_register_set (R_bool minstret_increment)
             (R_bitvector_64 minstret) _ _ eq_refl).
  rewrite (irrelevant_register_set (R_bool minstret_increment)
             (R_bitvector_64 PC) _ _ eq_refl).
  rewrite (irrelevant_register_set (R_bool minstret_increment)
             (R_bitvector_64 nextPC) _ _ eq_refl).
  by rewrite register_lookup_set.
Qed.

Lemma hp_post_other (r : register) (rs : regstate)
    (mi : SailStdpp.Values.mword 64) :
  register_beq r (R_bitvector_64 minstret) = false ->
  register_beq r (R_bitvector_64 PC) = false ->
  register_beq r (R_bitvector_64 nextPC) = false ->
  register_beq r (R_bool minstret_increment) = false ->
  register_lookup r (hp_post rs mi) = register_lookup r rs.
Proof.
  intros H1 H2 H3 H4. unfold hp_post.
  by rewrite (irrelevant_register_set _ _ _ _ H1)
     (irrelevant_register_set _ _ _ _ H2)
     (irrelevant_register_set _ _ _ _ H3)
     (irrelevant_register_set _ _ _ _ H4).
Qed.

(* setting a register to the value it already has changes no lookup *)
Lemma reg_set_id_agree (D : gset register) (r : register) (rs : regstate) :
  reg_agree_on D (register_set r (register_lookup r rs) rs) rs.
Proof.
  intros r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - by rewrite register_lookup_set.
  - by rewrite (irrelevant_register_set r' r rs _
                  (register_beq_false r' r Hne)).
Qed.


(* ====================================================================== *)
(* THE FOOTPRINTS.  One [Drw] now (the old file needed two, a span one and *)
(* a batch one; [swp] takes a single pair everywhere), and the read-only   *)
(* pins.  RAW-CELL form: the counter and clock cells are OWNED here        *)
(* because [MinstretInv]/[clock_inv] are above the red line; B′ moves them *)
(* into the invariants and they leave [Drw].                               *)
(* ====================================================================== *)

Definition ml_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register);
     (R_bitvector_64 x14 : register); (R_bitvector_64 x15 : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 minstret : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

Definition ml_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register); (misa : register);
     (hart_state : register); (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register);
     (R_bitvector_64 mcyclecfg : register); (pma_regions : register);
     (pmpcfg_n : register); (htif_tohost_base : register);
     (elp : register); (mseccfg : register);
     (R_bitvector_64 mtimecmp : register);
     (R_bitvector_64 stimecmp : register);
     (R_bitvector_64 menvcfg : register) ]}.

Lemma ml_disj : ml_Drw ## ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.

Lemma ml_in_priv : (cur_privilege : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_misa : (misa : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mst : (mstatus : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_hart : (hart_state : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_cycfg : (R_bitvector_64 mcyclecfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_pma : (pma_regions : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_pcfg : (pmpcfg_n : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_htif : (htif_tohost_base : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_tcmp : (R_bitvector_64 mtimecmp : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_menv : (R_bitvector_64 menvcfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_PC : (R_bitvector_64 PC : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_nPC : (R_bitvector_64 nextPC : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_ms : (R_bitvector_64 minstret : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mi : (R_bool minstret_increment : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_cy : (R_bitvector_64 mcycle : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_ti : (R_bitvector_64 mtime : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_ip : (R_bitvector_64 mip : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_x14 : (R_bitvector_64 x14 : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_x15 : (R_bitvector_64 x15 : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_elp : (elp : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_sec : (mseccfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.


(* the same memberships MINUS the clock cells: what the tick's weakened
   agreement can be read at.  Standalone so each [set_solver] runs in an
   empty context -- inside the leaf's proof, with the towers in scope, the
   same goals cost orders of magnitude more. *)
Lemma ml_ind_PC : (R_bitvector_64 PC : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_nPC : (R_bitvector_64 nextPC : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_x14 : (R_bitvector_64 x14 : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_x15 : (R_bitvector_64 x15 : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_mi : (R_bool minstret_increment : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_ms : (R_bitvector_64 minstret : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_priv : (cur_privilege : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_mst : (mstatus : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_misa : (misa : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_hart : (hart_state : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_mc : (R_bitvector_32 mcountinhibit : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_micfg : (R_bitvector_64 minstretcfg : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_cycfg : (R_bitvector_64 mcyclecfg : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_pma : (pma_regions : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_pcfg : (pmpcfg_n : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_htif : (htif_tohost_base : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_elp : (elp : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_sec : (mseccfg : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_tcmp : (R_bitvector_64 mtimecmp : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_scmp : (R_bitvector_64 stimecmp : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.
Lemma ml_ind_menv : (R_bitvector_64 menvcfg : register) ∈ (ml_Drw ∪ ml_Dro) ∖ tk_clock3.
Proof. rewrite /ml_Drw /ml_Dro /tk_clock3. set_solver. Qed.

Lemma ml_w_PC : (R_bitvector_64 PC : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_nPC : (R_bitvector_64 nextPC : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_mi : (R_bool minstret_increment : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_ms : (R_bitvector_64 minstret : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_cy : (R_bitvector_64 mcycle : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_ti : (R_bitvector_64 mtime : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_w_ip : (R_bitvector_64 mip : register) ∈ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.

(* ====================================================================== *)
(* THE ANCHOR TOWER.  A register file is a total function, so a leaf that   *)
(* wants to name one has to build it; every cell OUTSIDE [ml_Drw ∪ ml_Dro]  *)
(* is irrelevant (no frame mentions it), so the base is the cold file and   *)
(* only the footprint's cells are set.  [pc] is a parameter because the     *)
(* post-file is the SAME tower two bytes on -- which is what lets the       *)
(* continuation be stated as a tower rather than as an agreement.          *)
(* ====================================================================== *)

Section tower.
  Context (pc : SailStdpp.Values.mword 64)
          (mst0 misa0 mcfg mccfg menv0 : SailStdpp.Values.mword 64)
          (mc : SailStdpp.Values.mword 32)
          (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
          (elp0 : type_of_register elp)
          (tcmp scmp : SailStdpp.Values.mword 64)
          (bmi : bool) (ms0 cy0 ti0 ip0 : SailStdpp.Values.mword 64).

  Definition ml_rs : regstate :=
    register_set (R_bitvector_64 PC) pc
    (register_set (R_bitvector_64 nextPC) pc
    (register_set (R_bitvector_64 x14) (SailStdpp.Values.mword_of_int 1)
    (register_set (R_bitvector_64 x15) hp_flag
    (register_set (R_bool minstret_increment) bmi
    (register_set (R_bitvector_64 minstret) ms0
    (register_set (R_bitvector_64 mcycle) cy0
    (register_set (R_bitvector_64 mtime) ti0
    (register_set (R_bitvector_64 mip) ip0
    (register_set cur_privilege Machine
    (register_set mstatus mst0
    (register_set misa misa0
    (register_set hart_state (HART_ACTIVE tt)
    (register_set (R_bitvector_32 mcountinhibit) mc
    (register_set (R_bitvector_64 minstretcfg) mcfg
    (register_set (R_bitvector_64 mcyclecfg) mccfg
    (register_set pma_regions pmar0
    (register_set pmpcfg_n pcfg
    (register_set htif_tohost_base None
    (register_set elp elp0
    (register_set mseccfg (SailStdpp.Values.mword_of_int 0)
    (register_set (R_bitvector_64 mtimecmp) tcmp
    (register_set (R_bitvector_64 stimecmp) scmp
    (register_set (R_bitvector_64 menvcfg) menv0
      (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0))))))))))))))))))))))))).

  Local Ltac lk :=
    unfold ml_rs;
    repeat first
      [ rewrite register_lookup_set; reflexivity
      | rewrite irrelevant_register_set; [ | reflexivity ] ].

  Lemma ml_rs_PC : register_lookup (R_bitvector_64 PC) ml_rs = pc.
  Proof. lk. Qed.
  Lemma ml_rs_nPC : register_lookup (R_bitvector_64 nextPC) ml_rs = pc.
  Proof. lk. Qed.
  Lemma ml_rs_x14 :
    register_lookup (R_bitvector_64 x14) ml_rs
    = SailStdpp.Values.mword_of_int 1.
  Proof. lk. Qed.
  Lemma ml_rs_x15 : register_lookup (R_bitvector_64 x15) ml_rs = hp_flag.
  Proof. lk. Qed.
  Lemma ml_rs_mi : register_lookup (R_bool minstret_increment) ml_rs = bmi.
  Proof. lk. Qed.
  Lemma ml_rs_ms : register_lookup (R_bitvector_64 minstret) ml_rs = ms0.
  Proof. lk. Qed.
  Lemma ml_rs_cy : register_lookup (R_bitvector_64 mcycle) ml_rs = cy0.
  Proof. lk. Qed.
  Lemma ml_rs_ti : register_lookup (R_bitvector_64 mtime) ml_rs = ti0.
  Proof. lk. Qed.
  Lemma ml_rs_ip : register_lookup (R_bitvector_64 mip) ml_rs = ip0.
  Proof. lk. Qed.
  Lemma ml_rs_priv : register_lookup cur_privilege ml_rs = Machine.
  Proof. lk. Qed.
  Lemma ml_rs_mst : register_lookup mstatus ml_rs = mst0.
  Proof. lk. Qed.
  Lemma ml_rs_misa : register_lookup misa ml_rs = misa0.
  Proof. lk. Qed.
  Lemma ml_rs_hart : register_lookup hart_state ml_rs = HART_ACTIVE tt.
  Proof. lk. Qed.
  Lemma ml_rs_mc : register_lookup (R_bitvector_32 mcountinhibit) ml_rs = mc.
  Proof. lk. Qed.
  Lemma ml_rs_micfg : register_lookup (R_bitvector_64 minstretcfg) ml_rs = mcfg.
  Proof. lk. Qed.
  Lemma ml_rs_cycfg : register_lookup (R_bitvector_64 mcyclecfg) ml_rs = mccfg.
  Proof. lk. Qed.
  Lemma ml_rs_pma : register_lookup pma_regions ml_rs = pmar0.
  Proof. lk. Qed.
  Lemma ml_rs_pcfg : register_lookup pmpcfg_n ml_rs = pcfg.
  Proof. lk. Qed.
  Lemma ml_rs_htif : register_lookup htif_tohost_base ml_rs = None.
  Proof. lk. Qed.
  Lemma ml_rs_elp : register_lookup elp ml_rs = elp0.
  Proof. lk. Qed.
  Lemma ml_rs_sec :
    register_lookup mseccfg ml_rs = SailStdpp.Values.mword_of_int 0.
  Proof. lk. Qed.
  Lemma ml_rs_tcmp : register_lookup (R_bitvector_64 mtimecmp) ml_rs = tcmp.
  Proof. lk. Qed.
  Lemma ml_rs_scmp : register_lookup (R_bitvector_64 stimecmp) ml_rs = scmp.
  Proof. lk. Qed.
  Lemma ml_rs_menv : register_lookup (R_bitvector_64 menvcfg) ml_rs = menv0.
  Proof. lk. Qed.

End tower.

(* ====================================================================== *)
(* THE LEAF-LOCAL DATA: the three [hfrun] equations this word needs at its  *)
(* anchor, and the concrete address facts.  Everything here is either a     *)
(* short walk over a model function whose reads the caller pins, or one     *)
(* VM-checked conversion at the two addresses.                              *)
(* ====================================================================== *)

Lemma ml_subrange_id (a : SailStdpp.Values.mword 64) :
  subrange_vec_dec a (xlen - 0 - 1) 0 = a.
Proof.
  apply bv_eq. unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (xlen - 0 - 1 - 0 + 1)) with 64%N.
  apply bv_wrap_bv_unsigned.
Qed.
Local Open Scope Z_scope.

Lemma ml_hfrun_rx (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 x14 : register) ∈ D ->
  hfrun 4 D Drw rs
    (rX_bits (creg2reg_idx
                (encdec_creg_backwards (subrange_vec_dec hp_half 4 2))))
  = Some (register_lookup (R_bitvector_64 x14) rs, rs).
Proof.
  intros HD.
  unfold rX_bits, rX. d_tests.
  cbn beta iota zeta delta [Defs.read_reg].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

Lemma ml_hfrun_gta (D Drw : gset register) (rs : regstate)
    (off : SailStdpp.Values.mword 64) :
  (R_bitvector_64 x15 : register) ∈ D ->
  (mstatus : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (mseccfg : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg rs))
    = PMM_Disabled ->
  hfrun 8 D Drw rs
    (get_transformed_data_addr
       (creg2reg_idx (encdec_creg_backwards (subrange_vec_dec hp_half 9 7)))
       off (Store Data) 4)
  = Some (Ext_DataAddr_OK
            (Virtaddr (add_vec (register_lookup (R_bitvector_64 x15) rs) off)),
          rs).
Proof.
  intros HD15 HDmst HDpriv HDsec Hpriv Hmprv Hpmm.
  unfold get_transformed_data_addr, ext_data_get_addr,
    transform_effective_address, effectivePrivilege, get_pmlen,
    is_pmm_applicable, get_pmm, translationMode.
  unfold rX_bits, rX. d_tests.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD15).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDmst).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDpriv).
  rewrite Hpriv.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not].
  rewrite Hmprv.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not].
  d_tests.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDsec).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not].
  rewrite Hpmm.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM Defs.and_boolM Defs.or_boolM
    andb orb negb not pm_transform_PA].
  d_tests.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.returnm returnM pm_transform_PA].
  rewrite zero_extend'_id ml_subrange_id.
  apply hfrun_ret.
Qed.



Lemma t_ram_pc : addr_is_ram hp_pc.
Proof.
  unfold addr_is_ram.
  assert (H : uint hp_pc = 2147487456) by (vm_cast_no_check (eq_refl 2147487456)).
  assert (Hb : ram_base = 2147483648) by (vm_cast_no_check (eq_refl 2147483648)).
  assert (Hs : ram_size = 134217728) by (vm_cast_no_check (eq_refl 134217728)).
  rewrite H Hb Hs. lia.
Qed.
Lemma t_ram_flag : addr_is_ram hp_flag.
Proof.
  unfold addr_is_ram.
  assert (H : uint hp_flag = 2147525284) by (vm_cast_no_check (eq_refl 2147525284)).
  assert (Hb : ram_base = 2147483648) by (vm_cast_no_check (eq_refl 2147483648)).
  assert (Hs : ram_size = 134217728) by (vm_cast_no_check (eq_refl 134217728)).
  rewrite H Hb Hs. lia.
Qed.


Lemma t_b0 : neq_vec (access_vec_dec hp_pc 0) zerobit = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma t_b1 : neq_vec (access_vec_dec hp_pc 1) zerobit = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma t_va_pc : is_aligned_vaddr (Virtaddr hp_pc) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma t_pa_pc : is_aligned_paddr (Physaddr hp_pc) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma t_va_flag : is_aligned_vaddr (Virtaddr hp_flag) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma t_pa_flag : is_aligned_paddr (Physaddr hp_flag) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma t_split :
  split_on_page_boundary (bits_of_virtaddr (Virtaddr hp_flag)) 4
  = returnM (4, 0).
Proof. vm_cast_no_check (eq_refl (returnM (4, 0))). Qed.

(* the compressed store's immediate at this word is ZERO: [c.sw a4,0(a5)] *)
Lemma t_off :
  add_vec hp_flag
    (sign_extend' 64
       (zero_extend' 12
          (concat_vec
             (concat_vec
                (concat_vec (subrange_vec_dec hp_half 5 5)
                   (subrange_vec_dec hp_half 12 10))
                (subrange_vec_dec hp_half 6 6))
             (MachineWord.MachineWord.N_to_word
                (MachineWord.MachineWord.Z_idx 2)
                (BinaryString.Raw.to_N "00" 0)))))
  = hp_flag.
Proof. vm_cast_no_check (eq_refl hp_flag). Qed.

(* the word the store actually commits: a4's low four bytes, which is 1 *)
Lemma t_stored :
  Interface.WriteReq.value
    (mwrite_req hp_flag
       (TypeCasts.autocast
          (subrange_vec_dec
             (SailStdpp.Values.mword_of_int 1 : SailStdpp.Values.mword 64)
             31 0)))
  = hp_one.
Proof. vm_cast_no_check (eq_refl hp_one). Qed.

(* [mseccfg = 0] leaves pointer masking off, so the store's effective
   address is the architectural one *)
Lemma t_pmm :
  pmm_mode_backwards
    (_get_Seccfg_PMM
       (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 64))
  = PMM_Disabled.
Proof. vm_cast_no_check (eq_refl PMM_Disabled). Qed.


Section leaf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* THE DFRAC ASSIGNMENT for the read-only frame.  Five config cells are
     PERSISTENT in the tree's hw_config (misa, pma_regions,
     htif_tohost_base, elp, mseccfg); the rest are fractional.  Keeping
     the split faithful to that is what lets a caller hand over the cells
     it actually holds. *)
  Definition ml_Df (q : Qp) : register -> dfrac := fun r =>
    if decide (r = (misa : register)) then DfracDiscarded
    else if decide (r = (pma_regions : register)) then DfracDiscarded
    else if decide (r = (htif_tohost_base : register)) then DfracDiscarded
    else if decide (r = (elp : register)) then DfracDiscarded
    else if decide (r = (mseccfg : register)) then DfracDiscarded
    else DfracOwn q.

  Local Ltac dfq :=
    unfold ml_Df;
    repeat first [ rewrite decide_True; [reflexivity|reflexivity]
                 | rewrite decide_False; [|discriminate] ];
    reflexivity.

  Lemma ml_Df_misa q : ml_Df q misa = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_pma q : ml_Df q pma_regions = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_htif q : ml_Df q htif_tohost_base = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_elp q : ml_Df q elp = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_sec q : ml_Df q mseccfg = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_priv q : ml_Df q cur_privilege = DfracOwn q.
  Proof. dfq. Qed.


  (* THE FRAME <-> POINTS-TO BRIDGE.  A caller holds individual cells; the
     walk wants frames.  These are the only two lemmas that convert, and
     they are what make the leaf's statement something a caller can
     actually feed. *)
  Lemma ml_rw_split (rs : regstate) :
    hreg_frame rs ml_Drw ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs ∗
     (R_bitvector_64 x14) ↦ᵣ register_lookup (R_bitvector_64 x14) rs ∗
     (R_bitvector_64 x15) ↦ᵣ register_lookup (R_bitvector_64 x15) rs ∗
     (R_bool minstret_increment) ↦ᵣ
       register_lookup (R_bool minstret_increment) rs ∗
     (R_bitvector_64 minstret) ↦ᵣ
       register_lookup (R_bitvector_64 minstret) rs ∗
     (R_bitvector_64 mcycle) ↦ᵣ register_lookup (R_bitvector_64 mcycle) rs ∗
     (R_bitvector_64 mtime) ↦ᵣ register_lookup (R_bitvector_64 mtime) rs ∗
     (R_bitvector_64 mip) ↦ᵣ register_lookup (R_bitvector_64 mip) rs)%I.
  Proof.
    rewrite /hreg_frame /ml_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma ml_ro_split (q : Qp) (rs : regstate) :
    hreg_frame_ro (ml_Df q) rs ml_Dro ⊣⊢
    (reg_pointsto cur_privilege (DfracOwn q)
       (register_lookup cur_privilege rs) ∗
     reg_pointsto mstatus (DfracOwn q) (register_lookup mstatus rs) ∗
     reg_pointsto misa DfracDiscarded (register_lookup misa rs) ∗
     reg_pointsto hart_state (DfracOwn q) (register_lookup hart_state rs) ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) (DfracOwn q)
       (register_lookup (R_bitvector_32 mcountinhibit) rs) ∗
     reg_pointsto (R_bitvector_64 minstretcfg) (DfracOwn q)
       (register_lookup (R_bitvector_64 minstretcfg) rs) ∗
     reg_pointsto (R_bitvector_64 mcyclecfg) (DfracOwn q)
       (register_lookup (R_bitvector_64 mcyclecfg) rs) ∗
     reg_pointsto pma_regions DfracDiscarded
       (register_lookup pma_regions rs) ∗
     reg_pointsto pmpcfg_n (DfracOwn q) (register_lookup pmpcfg_n rs) ∗
     reg_pointsto htif_tohost_base DfracDiscarded
       (register_lookup htif_tohost_base rs) ∗
     reg_pointsto elp DfracDiscarded (register_lookup elp rs) ∗
     reg_pointsto mseccfg DfracDiscarded (register_lookup mseccfg rs) ∗
     reg_pointsto (R_bitvector_64 mtimecmp) (DfracOwn q)
       (register_lookup (R_bitvector_64 mtimecmp) rs) ∗
     reg_pointsto (R_bitvector_64 stimecmp) (DfracOwn q)
       (register_lookup (R_bitvector_64 stimecmp) rs) ∗
     reg_pointsto (R_bitvector_64 menvcfg) (DfracOwn q)
       (register_lookup (R_bitvector_64 menvcfg) rs))%I.
  Proof.
    rewrite /hreg_frame_ro /ml_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite !(ml_Df_misa q) !(ml_Df_pma q) !(ml_Df_htif q) !(ml_Df_elp q)
      !(ml_Df_sec q).
    unfold ml_Df.
    repeat (rewrite decide_False; [|discriminate]).
    by rewrite !bi.sep_assoc.
  Qed.

  (* the read-only frame's counterpart of [hreg_frame_ext] (HartSpan keeps
     its copy Local) *)
  Local Lemma hreg_frame_ro_ext' (Df : register -> dfrac) (rs rs' : regstate)
      (Dro : gset register) :
    reg_agree_on Dro rs rs' ->
    hreg_frame_ro Df rs Dro ⊣⊢ hreg_frame_ro Df rs' Dro.
  Proof.
    intros Hag. rewrite /hreg_frame_ro. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE TWO MEMORY OBLIGATIONS, discharged from owned resources.        *)
  (*                                                                     *)
  (* The fetch's is PERSISTENT-friendly: the text bytes are [↦ₓ□], so    *)
  (* the obligation may be re-proved every cycle -- which is what makes a *)
  (* loop out of the leaf.  The store's is linear and hands the caller    *)
  (* back the UPDATED cells, which is the [R] the store chain threads.    *)
  (* ------------------------------------------------------------------ *)
  Lemma ml_fetch_obl :
    ([∗ list] j ∈ seq 0 4, (pa_add hp_pc j) ↦ₓ□ nth_byte hp_wf j) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ⌜read_bytes σ.(mem) hp_pc 4 = Some hp_wf⌝ ∗
       ▷ (|={∅,⊤}=> mstate_interp σ)).
  Proof.
    iIntros "#Htext" (σ) "Hσ". rewrite /mstate_interp.
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (text_read_bytes σ.(mem) hp_pc 4 hp_wf with "Hmem Htext")
      as %Hrb.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iSplitR; [done|]. iNext. iMod "Hmask" as "_". iModIntro. by iFrame.
  Qed.

  Lemma ml_store_obl (vold w : bv 32) :
    ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte vold j) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
            (MState σ.(sregs) (write_bytes σ.(mem) hp_flag 4 w) σ.(mdev)) ∗
          ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte w j))).
  Proof.
    iIntros "Hold" (σ) "Hσ". rewrite /mstate_interp.
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iNext. iMod "Hmask" as "_".
    iMod (phys_upd_window σ.(mem) hp_flag 4 vold w with "Hmem Hold")
      as "[Hmem Hnew]".
    iModIntro. by iFrame.
  Qed.

  (* [run_hart_active] at the pilot's word: dispatch, fetch, decode,
     execute.  Everything below the [swp_use_cer] peels is a fact that
     already exists. *)
  Lemma swp_run_hart_active_hp (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n)
      (pa : SailStdpp.Values.mword 64) (d : SailStdpp.Values.mword 64)
      (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup (R_bitvector_64 PC) rs = hp_pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hfrun 8 (Drw ∪ Dro) Drw rs (is_landing_pad_expected tt)
      = Some (false, rs) ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram hp_pc ->
    neq_vec (access_vec_dec hp_pc 0) zerobit = false ->
    neq_vec (access_vec_dec hp_pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr hp_pc) 4 = true ->
    is_aligned_paddr (Physaddr hp_pc) 4 = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    hfrun 4 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
      (rX_bits (creg2reg_idx
                  (encdec_creg_backwards (subrange_vec_dec hp_half 4 2))))
      = Some (d, register_set (R_bitvector_64 nextPC)
                    (add_vec_int hp_pc 2) rs) ->
    hfrun 8 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
      (get_transformed_data_addr
         (creg2reg_idx (encdec_creg_backwards (subrange_vec_dec hp_half 9 7)))
         (sign_extend' 64
            (zero_extend' 12
               (concat_vec
                  (concat_vec
                     (concat_vec (subrange_vec_dec hp_half 5 5)
                        (subrange_vec_dec hp_half 12 10))
                     (subrange_vec_dec hp_half 6 6))
                  (MachineWord.MachineWord.N_to_word
                     (MachineWord.MachineWord.Z_idx 2)
                     (BinaryString.Raw.to_N "00" 0))))) (Store Data) 4)
      = Some (Ext_DataAddr_OK (Virtaddr pa),
              register_set (R_bitvector_64 nextPC)
                (add_vec_int hp_pc 2) rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) hp_pc 4 = Some hp_wf⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value
                      (mwrite_req pa
                         (TypeCasts.autocast (subrange_vec_dec d 31 0)))))
                σ.(mdev)) ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Execute (RETIRE_SUCCESS,
                        zero_extend' 32 hp_half)⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int hp_pc 2) rs) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int hp_pc 2) rs) Dro ∗ R).
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg HDhtif
      Hpriv Hpc Hpma Hpcfg Hhtif HmisaS HmIE HmisaC Hlpad Hunlock Hpallow
      Hram
      Hb0 Hb1 Hva Hpa Hmprv Hsram Hsva Hspa Hsplit Hrx Hgta.
    iIntros "#Hcert Hrw Hro Hmem Hwmem".
    iApply (swp_run_hart_active_rvc Drw Dro Df rs
              (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
              hp_pc hp_wf _ _ pmar0 pcfg 8 R Hdisj
              HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg HDhtif
              Hpriv Hpc Hpma Hpcfg Hhtif HmisaS HmIE HmisaC
              Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa
              hp_isRVC
              (hfrun_hval 100 (Drw ∪ Dro) Drw rs _ _ rs
                 (hfrun_decode_hp (Drw ∪ Dro) Drw rs HDmisa HmisaC))
              Hlpad with "Hcert Hrw Hro Hmem [] [Hwmem]").
    - iIntros "Hrw Hro".
      iApply (swp_execute_C_SW Drw Dro Df _ _ _ _ Hdisj with "Hcert Hrw Hro").
    - iIntros "Hrw Hro".
      iApply (swp_execute_STORE Drw Dro Df
                (register_set (R_bitvector_64 nextPC)
                   (add_vec_int hp_pc 2) rs) _ _ _ d pa pmar0 pcfg R Hdisj
                HDmst HDpriv HDpma HDcfg HDhtif
                ltac:(t_peel; exact Hpriv) ltac:(t_peel; exact Hpma)
                ltac:(t_peel; exact Hpcfg) ltac:(t_peel; exact Hhtif)
                ltac:(t_peel; exact Hmprv) Hunlock Hpallow Hsram Hsva Hspa
                Hsplit Hrx Hgta with "Hcert Hrw Hro Hwmem").
  Qed.

  (* ==================================================================== *)
  (* THE LEAF.  [WP Loop] from [WP Loop], through the honest wrapper at     *)
  (* BOTH ticks, for one real instruction.                                  *)
  (* ==================================================================== *)

  Lemma swp_try_step_hp (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n)
      (pa : SailStdpp.Values.mword 64) (d : SailStdpp.Values.mword 64)
      (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    (R_bool minstret_increment : register) ∈ Drw ->
    (R_bool minstret_increment : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstret : register) ∈ Drw ->
    (R_bitvector_64 minstret : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup hart_state rs = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 PC) rs = hp_pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    hfrun 8 (Drw ∪ Dro) Drw
      (register_set (R_bool minstret_increment)
         (minstret_inc_flag
            (register_lookup (R_bitvector_32 mcountinhibit) rs)
            (register_lookup (R_bitvector_64 minstretcfg) rs)
            (register_lookup cur_privilege rs)) rs)
      (is_landing_pad_expected tt)
      = Some (false, register_set (R_bool minstret_increment)
                       (minstret_inc_flag
                          (register_lookup (R_bitvector_32 mcountinhibit) rs)
                          (register_lookup (R_bitvector_64 minstretcfg) rs)
                          (register_lookup cur_privilege rs))
                       rs) ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram hp_pc ->
    neq_vec (access_vec_dec hp_pc 0) zerobit = false ->
    neq_vec (access_vec_dec hp_pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr hp_pc) 4 = true ->
    is_aligned_paddr (Physaddr hp_pc) 4 = true ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    hfrun 4 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
         (register_set (R_bool minstret_increment)
            (minstret_inc_flag
               (register_lookup (R_bitvector_32 mcountinhibit) rs)
               (register_lookup (R_bitvector_64 minstretcfg) rs)
               (register_lookup cur_privilege rs)) rs))
      (rX_bits (creg2reg_idx
                  (encdec_creg_backwards (subrange_vec_dec hp_half 4 2))))
      = Some (d, register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
                   (register_set (R_bool minstret_increment)
                      (minstret_inc_flag
                         (register_lookup (R_bitvector_32 mcountinhibit) rs)
                         (register_lookup (R_bitvector_64 minstretcfg) rs)
                         (register_lookup cur_privilege rs))
                      rs)) ->
    hfrun 8 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
         (register_set (R_bool minstret_increment)
            (minstret_inc_flag
               (register_lookup (R_bitvector_32 mcountinhibit) rs)
               (register_lookup (R_bitvector_64 minstretcfg) rs)
               (register_lookup cur_privilege rs)) rs))
      (get_transformed_data_addr
         (creg2reg_idx (encdec_creg_backwards (subrange_vec_dec hp_half 9 7)))
         (sign_extend' 64
            (zero_extend' 12
               (concat_vec
                  (concat_vec
                     (concat_vec (subrange_vec_dec hp_half 5 5)
                        (subrange_vec_dec hp_half 12 10))
                     (subrange_vec_dec hp_half 6 6))
                  (MachineWord.MachineWord.N_to_word
                     (MachineWord.MachineWord.Z_idx 2)
                     (BinaryString.Raw.to_N "00" 0))))) (Store Data) 4)
      = Some (Ext_DataAddr_OK (Virtaddr pa),
              register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
                (register_set (R_bool minstret_increment)
                   (minstret_inc_flag
                      (register_lookup (R_bitvector_32 mcountinhibit) rs)
                      (register_lookup (R_bitvector_64 minstretcfg) rs)
                      (register_lookup cur_privilege rs))
                   rs)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) hp_pc 4 = Some hp_wf⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value
                      (mwrite_req pa
                         (TypeCasts.autocast (subrange_vec_dec d 31 0)))))
                σ.(mdev)) ∗ R)) -∗
    swp (try_step 0 false)
      (fun _ => ∃ mi : SailStdpp.Values.mword 64,
                  hreg_frame (hp_post rs mi) Drw ∗
                  hreg_frame_ro Df (hp_post rs mi) Dro ∗ R)%I.
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDhart HDmc HDcfg HDmi HDmi'
      HDms HDms'
      HWpc HDpc HDnpc HDnpc' HDpma HDcfg2 HDhtif
      Hpriv Hhart Hpc Hpma Hpcfg Hhtif HmisaS HmisaC HmIE Hmprv Hlpad
      Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa Hsram Hsva Hspa Hsplit Hrx Hgta.
    iIntros "#Hcert Hrw Hro Hmem Hwmem".
    iApply (swp_mono _ _ _ with "[] [-]").
    2:{ iApply (swp_try_step_gen Drw Dro Df rs
                  (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
                     (wrap_pre rs)) R Hdisj HDpriv HDhart HDmc HDcfg
                  HDmi HDmi' HDms HDms' HWpc HDpc HDnpc'
                  Hhart
                  ltac:(t_peel; rewrite /wrap_pre; t_peel; exact Hhart)
                  ltac:(t_peel; rewrite /wrap_pre; apply register_lookup_set)
                  with "Hcert Hrw Hro [Hmem Hwmem]").
        iIntros "Hrw Hro". iApply swp_step_ex.
        iApply (swp_run_hart_active_hp Drw Dro Df (wrap_pre rs)
                  pmar0 pcfg pa d R Hdisj
                  HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg2 HDhtif
                  ltac:(rewrite /wrap_pre; t_peel; exact Hpriv) ltac:(rewrite /wrap_pre; t_peel; exact Hpc)
                  ltac:(rewrite /wrap_pre; t_peel; exact Hpma) ltac:(rewrite /wrap_pre; t_peel; exact Hpcfg)
                  ltac:(rewrite /wrap_pre; t_peel; exact Hhtif)
                  ltac:(rewrite /wrap_pre; t_peel; exact HmisaS) ltac:(rewrite /wrap_pre; t_peel; exact HmIE)
                  ltac:(rewrite /wrap_pre; t_peel; exact HmisaC) Hlpad
                  Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa
                  ltac:(rewrite /wrap_pre; t_peel; exact Hmprv) Hsram Hsva Hspa Hsplit Hrx Hgta
                  with "Hcert Hrw Hro Hmem Hwmem"). }
    iIntros (u). iDestruct 1 as (mi) "(Hrw & Hro & HR)".
    iExists mi. rewrite wrap_post_hp. iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE WORD, boundary to boundary.                                       *)
  (* ==================================================================== *)

  Section word.
    Context (q : Qp)
            (mst0 misa0 mcfg mccfg menv0 : SailStdpp.Values.mword 64)
            (mc : SailStdpp.Values.mword 32)
            (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
            (elp0 : type_of_register elp)
            (tcmp scmp : SailStdpp.Values.mword 64)
            (bmi : bool) (ms0 cy0 ti0 ip0 : SailStdpp.Values.mword 64).

  Definition mlb_pre : regstate :=
      ml_rs hp_pc mst0 misa0 mcfg mccfg menv0 mc pcfg pmar0 elp0 tcmp scmp
        bmi ms0 cy0 ti0 ip0.

    Definition mlb_post (ms1 cy1 ti1 ip1 : SailStdpp.Values.mword 64)
        : regstate :=
      ml_rs (add_vec_int hp_pc 2) mst0 misa0 mcfg mccfg menv0 mc pcfg pmar0
        elp0 tcmp scmp (minstret_inc_flag mc mcfg Machine) ms1 cy1 ti1 ip1.

    (* the two intermediate files the wrapper reaches inside the cycle:
       after the [minstret_increment] write, and after [nextPC] *)
    (* NOTATIONS, not definitions: these are the files [swp_try_step_hp]
       spells out in its own premises, and a [Definition] here would make
       every premise a delta step away from the expected type -- which the
       conversion checker answers by unfolding [register_set] instead, and
       then it never comes back. *)
    Local Notation mlb_rs1 :=
      (register_set (R_bool minstret_increment)
         (minstret_inc_flag
            (register_lookup (R_bitvector_32 mcountinhibit) mlb_pre)
            (register_lookup (R_bitvector_64 minstretcfg) mlb_pre)
            (register_lookup cur_privilege mlb_pre)) mlb_pre).

    Local Notation mlb_rs2 :=
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) mlb_rs1).

    (* peel a lookup down to the anchor tower and read it off *)
    Local Ltac pk :=
      repeat (rewrite irrelevant_register_set; [|reflexivity]);
      rewrite /mlb_pre.

  (* NEVER [rewrite] between the two towers: ssreflect's matcher, having
       failed the keyed match, unfolds [register_set] and compares two
       record-update towers -- the 3^N bomb the notes warn about.  [apply]
       under [etransitivity] only ever unifies against ONE side, so every
       cell below is a constant-time step. *)
    Local Ltac cell_s H Hin L R :=
      etransitivity; [apply (H _ Hin)|];
      etransitivity; [apply L|]; symmetry; apply R.

    Local Ltac cell_o H Hin L :=
      etransitivity; [apply (H _ Hin)|];
      etransitivity; [apply hp_post_other; reflexivity|];
      etransitivity; [apply L|]; symmetry; apply L.

    Lemma mlb_agree (mi : SailStdpp.Values.mword 64) (rs2 : regstate) :
      reg_agree_on ((ml_Drw ∪ ml_Dro) ∖ tk_clock3) rs2 (hp_post mlb_pre mi) ->
      reg_agree_on (ml_Drw ∪ ml_Dro) rs2
        (mlb_post mi
           (register_lookup (R_bitvector_64 mcycle) rs2)
           (register_lookup (R_bitvector_64 mtime) rs2)
           (register_lookup (R_bitvector_64 mip) rs2)).
    Proof.
      intros Hag r Hr.
      unfold mlb_post.
      rewrite /ml_Drw /ml_Dro in Hr.
      repeat (apply elem_of_union in Hr as [Hr|Hr]);
        apply elem_of_singleton in Hr; subst r.
      - cell_s Hag ml_ind_PC hp_post_PC ml_rs_PC.
      - cell_s Hag ml_ind_nPC hp_post_nPC ml_rs_nPC.
      - cell_o Hag ml_ind_x14 ml_rs_x14.
      - cell_o Hag ml_ind_x15 ml_rs_x15.
      - etransitivity; [apply (Hag _ ml_ind_mi)|].
        etransitivity; [apply hp_post_mi|].
        symmetry. etransitivity; [apply ml_rs_mi|].
        f_equal.
      - cell_s Hag ml_ind_ms hp_post_ms ml_rs_ms.
      - symmetry. apply ml_rs_cy.
      - symmetry. apply ml_rs_ti.
      - symmetry. apply ml_rs_ip.
      - cell_o Hag ml_ind_priv ml_rs_priv.
      - cell_o Hag ml_ind_mst ml_rs_mst.
      - cell_o Hag ml_ind_misa ml_rs_misa.
      - cell_o Hag ml_ind_hart ml_rs_hart.
      - cell_o Hag ml_ind_mc ml_rs_mc.
      - cell_o Hag ml_ind_micfg ml_rs_micfg.
      - cell_o Hag ml_ind_cycfg ml_rs_cycfg.
      - cell_o Hag ml_ind_pma ml_rs_pma.
      - cell_o Hag ml_ind_pcfg ml_rs_pcfg.
      - cell_o Hag ml_ind_htif ml_rs_htif.
      - cell_o Hag ml_ind_elp ml_rs_elp.
      - cell_o Hag ml_ind_sec ml_rs_sec.
      - cell_o Hag ml_ind_tcmp ml_rs_tcmp.
      - cell_o Hag ml_ind_scmp ml_rs_scmp.
      - cell_o Hag ml_ind_menv ml_rs_menv.
    Qed.


    (* the cycle BODY at this word, with every premise of
       [swp_try_step_hp] discharged at the anchor tower and the two memory
       obligations discharged from the caller's own bytes *)
    Lemma mlb_body (vold : bv 32) :
      eq_vec (_get_Misa_S misa0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
      eq_vec (_get_Misa_C misa0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
      eq_vec (_get_Mstatus_MIE mst0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
      eq_vec (_get_Mstatus_MPRV mst0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
      eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
      (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
      pma_allows_ram pmar0 ->
      gen_cert -∗
      hreg_frame mlb_pre ml_Drw -∗
      hreg_frame_ro (ml_Df q) mlb_pre ml_Dro -∗
      ([∗ list] j ∈ seq 0 4, (pa_add hp_pc j) ↦ₓ□ nth_byte hp_wf j) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte vold j) -∗
      swp (try_step 0 false)
        (fun _ => ∃ mi : SailStdpp.Values.mword 64,
                    hreg_frame (hp_post mlb_pre mi) ml_Drw ∗
                    hreg_frame_ro (ml_Df q) (hp_post mlb_pre mi) ml_Dro ∗
                    [∗ list] j ∈ seq 0 4,
                      (pa_add hp_flag j) ↦ₚ nth_byte hp_one j)%I.
    Proof.
      intros HmS HmC HmIE Hmprv Help Hunlock Hpallow.
      assert (Hpriv : register_lookup cur_privilege mlb_pre = Machine)
        by apply ml_rs_priv.
      assert (Hhart : register_lookup hart_state mlb_pre = HART_ACTIVE tt)
        by apply ml_rs_hart.
      assert (Hpc : register_lookup (R_bitvector_64 PC) mlb_pre = hp_pc)
        by apply ml_rs_PC.
      assert (Hpma : register_lookup pma_regions mlb_pre = pmar0)
        by apply ml_rs_pma.
      assert (Hpcfg : register_lookup pmpcfg_n mlb_pre = pcfg)
        by apply ml_rs_pcfg.
      assert (Hhtif : register_lookup htif_tohost_base mlb_pre = None)
        by apply ml_rs_htif.
      assert (HmisaS : eq_vec (_get_Misa_S (register_lookup misa mlb_pre))
                         (MachineWord.MachineWord.N_to_word 1 1%N) = true)
        by (rewrite /mlb_pre ml_rs_misa; exact HmS).
      assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa mlb_pre))
                         (MachineWord.MachineWord.N_to_word 1 1%N) = true)
        by (rewrite /mlb_pre ml_rs_misa; exact HmC).
      assert (HmIE' : eq_vec (_get_Mstatus_MIE (register_lookup mstatus mlb_pre))
                        (MachineWord.MachineWord.N_to_word 1 1%N) = false)
        by (rewrite /mlb_pre ml_rs_mst; exact HmIE).
      assert (Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus mlb_pre))
                         (MachineWord.MachineWord.N_to_word 1 1%N) = false)
        by (rewrite /mlb_pre ml_rs_mst; exact Hmprv).
      (* the landing-pad check, the GPR read and the effective-address
         computation, at the two intermediate files the wrapper reaches *)
      assert (Help2 : eq_vec (register_lookup elp mlb_rs1)
                        (landing_pad_bits_backwards LP_EXPECTED) = false)
        by (pk; exact Help).
      pose proof (hfrun_lpad (ml_Drw ∪ ml_Dro) ml_Drw mlb_rs1
                    ml_in_elp Help2) as Hlpad.
      assert (Hx14 : register_lookup (R_bitvector_64 x14) mlb_rs2
                     = SailStdpp.Values.mword_of_int 1)
        by (pk; reflexivity).
      pose proof (ml_hfrun_rx (ml_Drw ∪ ml_Dro) ml_Drw mlb_rs2 ml_in_x14)
        as Hrx.
      rewrite Hx14 in Hrx.
      assert (Hx15 : register_lookup (R_bitvector_64 x15) mlb_rs2 = hp_flag)
        by (pk; reflexivity).
      assert (Hpriv2 : register_lookup cur_privilege mlb_rs2 = Machine)
        by (pk; reflexivity).
      assert (Hmprv2 : eq_vec (_get_Mstatus_MPRV
                                 (register_lookup mstatus mlb_rs2))
                         (MachineWord.MachineWord.N_to_word 1 1%N) = false)
        by (pk; exact Hmprv).
      assert (Hpmm2 : pmm_mode_backwards
                        (_get_Seccfg_PMM (register_lookup mseccfg mlb_rs2))
                      = PMM_Disabled)
        by (pk; exact t_pmm).
      pose proof (ml_hfrun_gta (ml_Drw ∪ ml_Dro) ml_Drw mlb_rs2
                    (sign_extend' 64
                       (zero_extend' 12
                          (concat_vec
                             (concat_vec
                                (concat_vec (subrange_vec_dec hp_half 5 5)
                                   (subrange_vec_dec hp_half 12 10))
                                (subrange_vec_dec hp_half 6 6))
                             (MachineWord.MachineWord.N_to_word
                                (MachineWord.MachineWord.Z_idx 2)
                                (BinaryString.Raw.to_N "00" 0)))))
                    ml_in_x15 ml_in_mst ml_in_priv ml_in_sec
                    Hpriv2 Hmprv2 Hpmm2) as Hgta.
      rewrite Hx15 t_off in Hgta.
      iIntros "#Hcert Hrw Hro #Htext Hflag".
      iApply (swp_try_step_hp ml_Drw ml_Dro (ml_Df q) mlb_pre pmar0
                pcfg hp_flag (SailStdpp.Values.mword_of_int 1)
                ([∗ list] j ∈ seq 0 4,
                   (pa_add hp_flag j) ↦ₚ nth_byte hp_one j)%I
                ml_disj ml_in_priv ml_in_misa ml_in_mst ml_in_hart
                ml_in_mc ml_in_micfg ml_w_mi ml_in_mi ml_w_ms
                ml_in_ms ml_w_PC ml_in_PC ml_w_nPC ml_in_nPC
                ml_in_pma ml_in_pcfg ml_in_htif
                Hpriv Hhart Hpc Hpma Hpcfg Hhtif HmisaS HmisaC HmIE' Hmprv'
                Hlpad Hunlock Hpallow t_ram_pc t_b0 t_b1 t_va_pc t_pa_pc
                t_ram_flag t_va_flag t_pa_flag t_split Hrx Hgta
                with "Hcert Hrw Hro [] [Hflag]").
      - iApply ml_fetch_obl. iApply "Htext".
      - rewrite t_stored. iApply (ml_store_obl vold hp_one with "Hflag").
    Qed.

    (* ------------------------------------------------------------------ *)
    (* THE LEAF.  [WP Loop] from [WP Loop], at BOTH ticks, for one real     *)
    (* kernel instruction -- the whole-cycle statement the pre-port tree    *)
    (* had, now discharged through the per-node language.                   *)
    (*                                                                     *)
    (* WHAT IT SAYS: the machine ends one instruction on -- PC/nextPC at    *)
    (* pc+2 (the store is compressed), the flag cell holding 1, every pin   *)
    (* returned at the value it came in with -- and the four cells the      *)
    (* wrapper and the tick own (minstret and the three clock cells) hold   *)
    (* SOME value, which is exactly the value-agnosticism [MinstretInv] /   *)
    (* [clock_inv] will encode when they leave [Drw].                       *)
    (* ------------------------------------------------------------------ *)
    Lemma wp_word_main_b0 (vold : bv 32) :
      eq_vec (_get_Misa_S misa0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
      eq_vec (_get_Misa_C misa0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
      eq_vec (_get_Mstatus_MIE mst0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
      eq_vec (_get_Mstatus_MPRV mst0)
        (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
      eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
      (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
      pma_allows_ram pmar0 ->
      gen_cert -∗
      hreg_frame mlb_pre ml_Drw -∗
      hreg_frame_ro (ml_Df q) mlb_pre ml_Dro -∗
      ([∗ list] j ∈ seq 0 4, (pa_add hp_pc j) ↦ₓ□ nth_byte hp_wf j) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte vold j) -∗
      ▷ (∀ ms1 cy1 ti1 ip1 : SailStdpp.Values.mword 64,
           hreg_frame (mlb_post ms1 cy1 ti1 ip1) ml_Drw -∗
           hreg_frame_ro (ml_Df q) (mlb_post ms1 cy1 ti1 ip1) ml_Dro -∗
           ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte hp_one j) -∗
           WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
    Proof.
      intros HmS HmC HmIE Hmprv Help Hunlock Hpallow.
      iIntros "#Hcert Hrw Hro #Htext Hflag Hcont".
      iApply (wp_loop_cycle ml_Drw ml_Dro (ml_Df q)
                (fun rs1 => exists mi, rs1 = hp_post mlb_pre mi)
                ([∗ list] j ∈ seq 0 4,
                   (pa_add hp_flag j) ↦ₚ nth_byte hp_one j)%I
                ml_disj ml_w_cy ml_w_ti ml_w_ip
                with "Hcert [Hrw Hro Hflag] [Hcont]").
      - iNext.
        iApply (swp_mono _ _ _ with "[] [-]").
        2:{ iApply (mlb_body vold HmS HmC HmIE Hmprv Help Hunlock Hpallow
                      with "Hcert Hrw Hro Htext Hflag"). }
        iIntros (u). iDestruct 1 as (mi) "(Hrw & Hro & Hnew)".
        iExists (hp_post mlb_pre mi). iFrame. iPureIntro. by exists mi.
      - iNext. iIntros (rs2 Hex) "Hrw Hro Hnew".
        destruct Hex as (rs1 & (mi & ->) & Hag).
        pose proof (mlb_agree mi rs2 Hag) as Hag2.
        iApply ("Hcont" $! mi
                  (register_lookup (R_bitvector_64 mcycle) rs2)
                  (register_lookup (R_bitvector_64 mtime) rs2)
                  (register_lookup (R_bitvector_64 mip) rs2)
                  with "[Hrw] [Hro] [Hnew]").
        + iApply (hreg_frame_ext rs2 _ ml_Drw
                    (reg_agree_mono _ ml_Drw _ _ (union_subseteq_l _ _) Hag2)
                   with "Hrw").
        + iApply (hreg_frame_ro_ext' (ml_Df q) rs2 _ ml_Dro
                    (reg_agree_mono _ ml_Dro _ _ (union_subseteq_r _ _) Hag2)
                   with "Hro").
        + iExact "Hnew".
    Qed.

  End word.

End leaf.
