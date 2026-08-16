(* HartMFrame.v -- GPR ACCESS FOR THE [swp] LAYER, at [gpr_pt] / [gpr_file],
   with NO frame and NO footprint.

   THIS FILE USED TO HOLD A FRAME BRIDGE ([mm_gpr_D] + a 31-way
   [big_sepS] split converting [gpr_file] to [hreg_frame]).  It is gone,
   and the reason is worth keeping:

   THE BRIDGE EXISTED ONLY TO PUT THE GPRs IN THE WRAPPER'S FOOTPRINT, and
   the only argument for doing that was "a leaf discharges its
   [swp (execute i)] by [swp_hfrun], which needs ONE frame".  That argument
   is FALSE for the leaves that matter.  [hfrun] answers a register read by
   [bool_decide (r ∈ D)], which does not compute at a SYMBOLIC register
   index -- and every instruction leaf in the tree is generic in its
   operands ([wp_or_gpr] quantifies [rs2 rs1 rd : mword 5]).  So [hfrun]
   was never going to run [execute (RTYPE (rs2, rs1, rd, OR))] anyway.
   What a leaf actually needs is per-NODE access at a symbolic index, which
   is [HartRegNode]'s σ-shaped [swp_hart_regread] / [swp_hart_regwrite] --
   and those need no frame at all.

   SO: the GPRs stay OUT of [Drw] and ride in the caller's [R]; [gpr_file]
   and [gpr_pt] keep their definitions (no change to [WpGpr], none to the
   32 sites that destructure them); and the two lemmas below are the whole
   interface, proved ONCE by the same 32-way [lia] case split that
   [WpGpr.exec_rX_bits_gpr] already uses.

   The shape is deliberately the [swp] twin of [exec_rX_bits_gpr] /
   [exec_wX_bits_gpr], so a leaf's proof reads as it does today. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        HartRegNode RegFile WpGpr.
Require Import ColdBoot.
Local Open Scope Z_scope.

(* collapse the closed [Z.eqb] tests of the model's rX/wX cascades *)
Local Ltac zt :=
  repeat match goal with
  | |- context [ if ?b then _ else _ ] =>
      assert_fails (is_var b);
      let x := eval vm_compute in b in
      lazymatch x with true => change b with true
                     | false => change b with false end
  end.

(* ====================================================================== *)
(* THE M-MODE WRAPPER'S FOOTPRINT.                                         *)
(*                                                                        *)
(* [mm_Drw] is SEVEN cells, not thirty-eight: the GPRs are not here (see   *)
(* the header -- they ride in the caller's [R] and are reached by          *)
(* [swp_rX_bits]/[swp_wX_bits]), and neither is the clock CONFIG, because  *)
(* [HartMCycle.tick_clock_hvalE] ∀-peels every read the tick makes and     *)
(* needs only the three clock CELLS owned.                                 *)
(*                                                                        *)
(* [mm_Dro] is what the wrapper, the fetch and the dispatch actually pin.  *)
(* EIGHT of the twelve are persistent: six are [hw_config]'s frozen cells,  *)
(* and mcountinhibit / minstretcfg are frozen too but arrive from           *)
(* [MinstretInv.minstret_res] -- they are read only by                      *)
(* [should_inc_minstret], so they live with the rest of the minstret facts  *)
(* rather than in the shared config bundle.  The four fractional ones are   *)
(* the genuinely M-mode-specific config, which is what lets [mmode_config]  *)
(* keep its [split]/[combine] (47 sites depend on it) -- the EXCLUSIVE      *)
(* cells go in [pc_is] instead.                                            *)
(* ====================================================================== *)

Definition mm_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register);
     (R_bitvector_64 minstret : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

Definition mm_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register);
     (hart_state : register); (pmpcfg_n : register);
     (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register);
     (misa : register); (mseccfg : register); (pma_regions : register);
     (htif_tohost_base : register); (elp : register);
     (senvcfg : register) ]}.

Lemma mm_disj : mm_Drw ## mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.

(* the wrapper's own memberships, precomputed (set_solver in an empty
   context is 7 ms; inside a leaf proof with towers in scope it is not) *)
Lemma mm_w_PC : (R_bitvector_64 PC : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_nPC : (R_bitvector_64 nextPC : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_ms : (R_bitvector_64 minstret : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_mi : (R_bool minstret_increment : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_cy : (R_bitvector_64 mcycle : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_ti : (R_bitvector_64 mtime : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_ip : (R_bitvector_64 mip : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.

Lemma mm_in_PC : (R_bitvector_64 PC : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_nPC : (R_bitvector_64 nextPC : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_ms : (R_bitvector_64 minstret : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_mi : (R_bool minstret_increment : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_priv : (cur_privilege : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_mst : (mstatus : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_hart : (hart_state : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_pcfg : (pmpcfg_n : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_misa : (misa : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_sec : (mseccfg : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_pma : (pma_regions : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_htif : (htif_tohost_base : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_elp : (elp : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.

(* ====================================================================== *)
(* THE ANCHOR TOWER.  A register file is a total function, so a rule that   *)
(* wants to name one has to build it; every cell outside [mm_Drw ∪ mm_Dro]  *)
(* is irrelevant (no frame mentions it), so the base is the cold file and   *)
(* only the footprint's nineteen cells are set.  Three of them are PINNED   *)
(* rather than parameters: this is the M-mode wrapper, so cur_privilege is  *)
(* Machine, hart_state is ACTIVE, and htif_tohost_base is None.            *)
(* ====================================================================== *)

Section tower.
  Context (pc npc ms : SailStdpp.Values.mword 64) (bmi : bool)
          (cy ti ip : SailStdpp.Values.mword 64)
          (mst0 : SailStdpp.Values.mword 64)
          (pcfg : type_of_register pmpcfg_n)
          (mc : SailStdpp.Values.mword 32)
          (micfg misa0 mseccfg0 : SailStdpp.Values.mword 64)
          (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
          (senv0 : SailStdpp.Values.mword 64).

  Definition mm_rs : regstate :=
    register_set (R_bitvector_64 PC) pc
    (    register_set (R_bitvector_64 nextPC) npc
    (    register_set (R_bitvector_64 minstret) ms
    (    register_set (R_bool minstret_increment) bmi
    (    register_set (R_bitvector_64 mcycle) cy
    (    register_set (R_bitvector_64 mtime) ti
    (    register_set (R_bitvector_64 mip) ip
    (    register_set cur_privilege Machine
    (    register_set mstatus mst0
    (    register_set hart_state (HART_ACTIVE tt)
    (    register_set pmpcfg_n pcfg
    (    register_set (R_bitvector_32 mcountinhibit) mc
    (    register_set (R_bitvector_64 minstretcfg) micfg
    (    register_set misa misa0
    (    register_set mseccfg mseccfg0
    (    register_set pma_regions pmar0
    (    register_set htif_tohost_base None
    (    register_set elp elp0
    (    register_set senvcfg senv0
    (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0)))))))))))))))))))).

  Local Ltac lk :=
    unfold mm_rs;
    repeat first
      [ rewrite register_lookup_set; reflexivity
      | rewrite irrelevant_register_set; [ | reflexivity ] ].

  Lemma mm_rs_PC : register_lookup (R_bitvector_64 PC) mm_rs = pc.
  Proof. lk. Qed.
  Lemma mm_rs_nPC : register_lookup (R_bitvector_64 nextPC) mm_rs = npc.
  Proof. lk. Qed.
  Lemma mm_rs_ms : register_lookup (R_bitvector_64 minstret) mm_rs = ms.
  Proof. lk. Qed.
  Lemma mm_rs_mi : register_lookup (R_bool minstret_increment) mm_rs = bmi.
  Proof. lk. Qed.
  Lemma mm_rs_cy : register_lookup (R_bitvector_64 mcycle) mm_rs = cy.
  Proof. lk. Qed.
  Lemma mm_rs_ti : register_lookup (R_bitvector_64 mtime) mm_rs = ti.
  Proof. lk. Qed.
  Lemma mm_rs_ip : register_lookup (R_bitvector_64 mip) mm_rs = ip.
  Proof. lk. Qed.
  Lemma mm_rs_priv : register_lookup cur_privilege mm_rs = Machine.
  Proof. lk. Qed.
  Lemma mm_rs_mst : register_lookup mstatus mm_rs = mst0.
  Proof. lk. Qed.
  Lemma mm_rs_hart : register_lookup hart_state mm_rs = (HART_ACTIVE tt).
  Proof. lk. Qed.
  Lemma mm_rs_pcfg : register_lookup pmpcfg_n mm_rs = pcfg.
  Proof. lk. Qed.
  Lemma mm_rs_mc : register_lookup (R_bitvector_32 mcountinhibit) mm_rs = mc.
  Proof. lk. Qed.
  Lemma mm_rs_micfg : register_lookup (R_bitvector_64 minstretcfg) mm_rs = micfg.
  Proof. lk. Qed.
  Lemma mm_rs_misa : register_lookup misa mm_rs = misa0.
  Proof. lk. Qed.
  Lemma mm_rs_sec : register_lookup mseccfg mm_rs = mseccfg0.
  Proof. lk. Qed.
  Lemma mm_rs_pma : register_lookup pma_regions mm_rs = pmar0.
  Proof. lk. Qed.
  Lemma mm_rs_htif : register_lookup htif_tohost_base mm_rs = None.
  Proof. lk. Qed.
  Lemma mm_rs_elp : register_lookup elp mm_rs = elp0.
  Proof. lk. Qed.
  Lemma mm_rs_senv : register_lookup senvcfg mm_rs = senv0.
  Proof. lk. Qed.

End tower.

Section gpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the model's GPR read, at a SYMBOLIC index, against the caller's own
     [gpr_pt] entry.  x0 is the [Ret] case (hardwired zero, nothing owned);
     x1..x31 are one [RegRead] node each. *)
  Lemma swp_rX_bits (i : SailStdpp.Values.mword 5)
      (v : SailStdpp.Values.mword 64) :
    gen_cert -∗
    gpr_pt (Regidx i) v -∗
    swp (rX_bits (Regidx i)) (fun w => ⌜w = v⌝ ∗ gpr_pt (Regidx i) v).
  Proof.
    iIntros "#Hcert Hpt".
    pose proof (uint5_lt i) as Hb.
    assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/
      uint i = 4 \/ uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/
      uint i = 9 \/ uint i = 10 \/ uint i = 11 \/ uint i = 12 \/
      uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
      uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/
      uint i = 21 \/ uint i = 22 \/ uint i = 23 \/ uint i = 24 \/
      uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
      uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
    unfold gpr_pt; cbn match.
    destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|
      [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
    1:{ (* x0: nothing owned, the model returns zero_reg *)
        rewrite H. cbn match. iDestruct "Hpt" as %->.
        unfold rX_bits, rX. rewrite H. cbn match.
        iApply swp_ret. by iSplit. }
    all: rewrite H; cbn match;
         unfold rX_bits, rX; rewrite H; cbn match;
         iApply (swp_hart_regread with "Hcert");
         [cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity|];
         iIntros (σ) "Hsi"; rewrite /mstate_interp;
         iDestruct "Hsi" as "(Hreg & Hmem & Hdev)";
         iDestruct (reg_valid with "Hreg Hpt") as %Lv;
         iApply fupd_mask_intro; [apply empty_subseteq|];
         iIntros "Hcl"; iNext; iMod "Hcl" as "_"; iModIntro;
         iSplitL "Hreg Hmem Hdev"; [by iFrame|];
         rewrite hregread_resume_red Lv;
         iApply swp_ret; by iFrame.
  Qed.

  Local Lemma hregwrite_val_at_red (r : register) (ak : option unit)
      (v : type_of_register r) (K : unit -> M unit) :
    hregwrite_val_at r (Interface.Next (Interface.RegWrite r ak v) K) = Some v.
  Proof.
    simpl. destruct (decide _) as [Heq|Hne]; [|congruence].
    assert (Heq = eq_refl) as -> by apply proof_irrel.
    reflexivity.
  Qed.

  (* the model's GPR write, likewise.  [uint i <> 0] is a premise rather
     than a case, because a write to x0 is discarded and the leaves that
     use this already carry the guard ([wp_or_gpr] and friends all require
     [uint rd <> 0]). *)
  Lemma swp_wX_bits (i : SailStdpp.Values.mword 5)
      (v w : SailStdpp.Values.mword 64) :
    uint i <> 0 ->
    gen_cert -∗
    gpr_pt (Regidx i) v -∗
    swp (wX_bits (Regidx i) w)
      (fun _ => gpr_pt (Regidx i) (regval_into_reg w)).
  Proof.
    intros Hnz. iIntros "#Hcert Hpt".
    pose proof (uint5_lt i) as Hb.
    assert (Hc : uint i = 1 \/ uint i = 2 \/ uint i = 3 \/
      uint i = 4 \/ uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/
      uint i = 9 \/ uint i = 10 \/ uint i = 11 \/ uint i = 12 \/
      uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
      uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/
      uint i = 21 \/ uint i = 22 \/ uint i = 23 \/ uint i = 24 \/
      uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
      uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
    unfold gpr_pt; cbn match.
    destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|
      [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
    all: rewrite H; cbn match;
         unfold wX_bits, wX; rewrite H;
         cbn beta iota zeta delta [Defs.bind0 Defs.bind Interface.iMon_bind
           Defs.write_reg Defs.returnm returnM Z.eqb Pos.eqb];
         lazymatch goal with
         | |- context [Interface.RegWrite ?rg] =>
             iApply (swp_hart_regwrite rg (regval_into_reg w) with "Hcert");
             [cbn [hregwrite_val_at Defs.write_reg];
              destruct (decide _) as [Heq|Hne]; [|congruence];
              assert (Heq = eq_refl) as -> by apply proof_irrel;
              reflexivity|];
             iIntros (σ) "Hsi"; rewrite /mstate_interp;
             iDestruct "Hsi" as "(Hreg & Hmem & Hdev)";
             iMod (reg_update _ rg _ (regval_into_reg w) with "Hreg Hpt")
               as "[Hreg Hpt]";
             iApply fupd_mask_intro; [apply empty_subseteq|];
             iIntros "Hcl"; iNext; iMod "Hcl" as "_"; iModIntro;
             iSplitL "Hreg Hmem Hdev";
             [rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg; by iFrame|];
             rewrite hregwrite_resume_red;
             iApply swp_ret; iExact "Hpt"
         end.
  Qed.

  (* THE DFRAC ASSIGNMENT for the read-only frame: [hw_config]'s six cells
     are persistent, the rest fractional at the caller's [q]. *)
  (* dfrac-generic, because [wp_instr] takes its fraction as a [dfrac]
     (the leaves pass [DfracOwn q]) *)
  Definition mm_Df (dq : dfrac) : register -> dfrac := fun r =>
    if decide (r = (misa : register)) then DfracDiscarded
    else if decide (r = (mseccfg : register)) then DfracDiscarded
    else if decide (r = (pma_regions : register)) then DfracDiscarded
    else if decide (r = (htif_tohost_base : register)) then DfracDiscarded
    else if decide (r = (elp : register)) then DfracDiscarded
    else if decide (r = (senvcfg : register)) then DfracDiscarded
    else if decide (r = (R_bitvector_32 mcountinhibit : register))
    then DfracDiscarded
    else if decide (r = (R_bitvector_64 minstretcfg : register))
    then DfracDiscarded
    else dq.

  Local Ltac dfq :=
    unfold mm_Df;
    repeat first [ rewrite decide_True; [reflexivity|reflexivity]
                 | rewrite decide_False; [|discriminate] ];
    reflexivity.

  Lemma mm_Df_misa dq : mm_Df dq misa = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma mm_Df_sec dq : mm_Df dq mseccfg = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma mm_Df_pma dq : mm_Df dq pma_regions = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma mm_Df_htif dq : mm_Df dq htif_tohost_base = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma mm_Df_elp dq : mm_Df dq elp = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma mm_Df_senv dq : mm_Df dq senvcfg = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma mm_Df_mc dq : mm_Df dq (R_bitvector_32 mcountinhibit) = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma mm_Df_micfg dq : mm_Df dq (R_bitvector_64 minstretcfg) = DfracDiscarded.
  Proof. dfq. Qed.

  (* THE FRAME <-> POINTS-TO BRIDGE, at the size it should have been all
     along: seven cells and twelve, not thirty-eight.  Instant. *)
  Lemma mm_rw_split (rs : regstate) :
    (hreg_frame rs mm_Drw : iProp Σ) ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs ∗
     (R_bitvector_64 minstret) ↦ᵣ
       register_lookup (R_bitvector_64 minstret) rs ∗
     (R_bool minstret_increment) ↦ᵣ
       register_lookup (R_bool minstret_increment) rs ∗
     (R_bitvector_64 mcycle) ↦ᵣ register_lookup (R_bitvector_64 mcycle) rs ∗
     (R_bitvector_64 mtime) ↦ᵣ register_lookup (R_bitvector_64 mtime) rs ∗
     (R_bitvector_64 mip) ↦ᵣ register_lookup (R_bitvector_64 mip) rs)%I.
  Proof.
    rewrite /hreg_frame /mm_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma mm_ro_split (dq : dfrac) (rs : regstate) :
    (hreg_frame_ro (mm_Df dq) rs mm_Dro : iProp Σ) ⊣⊢
    (reg_pointsto cur_privilege dq (register_lookup cur_privilege rs) ∗
     reg_pointsto mstatus dq (register_lookup mstatus rs) ∗
     reg_pointsto hart_state dq (register_lookup hart_state rs) ∗
     reg_pointsto pmpcfg_n dq (register_lookup pmpcfg_n rs) ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded
       (register_lookup (R_bitvector_32 mcountinhibit) rs) ∗
     reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded
       (register_lookup (R_bitvector_64 minstretcfg) rs) ∗
     reg_pointsto misa DfracDiscarded (register_lookup misa rs) ∗
     reg_pointsto mseccfg DfracDiscarded (register_lookup mseccfg rs) ∗
     reg_pointsto pma_regions DfracDiscarded
       (register_lookup pma_regions rs) ∗
     reg_pointsto htif_tohost_base DfracDiscarded
       (register_lookup htif_tohost_base rs) ∗
     reg_pointsto elp DfracDiscarded (register_lookup elp rs) ∗
     reg_pointsto senvcfg DfracDiscarded (register_lookup senvcfg rs))%I.
  Proof.
    rewrite /hreg_frame_ro /mm_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite !(mm_Df_misa dq) !(mm_Df_sec dq) !(mm_Df_pma dq) !(mm_Df_htif dq)
      !(mm_Df_elp dq) !(mm_Df_senv dq) !(mm_Df_mc dq) !(mm_Df_micfg dq).
    unfold mm_Df.
    repeat (rewrite decide_False; [|discriminate]).
    by rewrite !bi.sep_assoc.
  Qed.

End gpr.
