(* HartSFrame.v -- the S-MODE FOOTPRINT and its register tower.

   THE M-MODE TWIN IS [HartMFrame]'s [mm_Drw] / [mm_Dro] / [mm_rs], and this
   file is deliberately its mirror rather than a generalization of it, because
   the CELL SETS genuinely differ.  S-mode adds five:

     tlb      -- WRITTEN, and it is the whole reason the fetch obligation
                 upstream ([HartRunGen]) lets a fetch land on a different file:
                 a walk that misses fills the TLB
                 ([CommonWalk.hfrun_add_to_TLB_user]).
     satp     -- read by [translateAddr]'s front matter, for the root and asid.
     mie      -- read by the dispatch.  It is a PARAMETER here even though
                 [sconf] pins it at [MIE_S]: the pin is the kernel's fact, not
                 the footprint's, and [MIE_S] is defined above this layer.
                 The bundle supplies it at the frames bridge.
     mideleg  -- read by the dispatch; its VALUE is never needed, only
                 [and_vec MIE_S (not_vec mdv) = 0], so it stays a parameter.
     menvcfg  -- read by the walk's PBMTE gate and by [get_xLPE].

   WHAT IS NOT HERE, and on purpose: [sig_meip] / [sig_seip].  Those are the
   PLIC wires, and they are exactly the registers a frame CANNOT hold -- their
   points-to's live in [WireInv.wire_inv] and another hart may move them
   between this cycle's nodes.  The dispatch reads them OFF-FRAME, as ∀-bound
   reads ([WpIntrCore.swp_dispatchInterrupt_S]).  A tower that pinned them
   would be claiming the caller knows what the platform is about to do.

   WHERE THE CELLS COME FROM, which is what the bridge above this file has to
   assemble (checked, not assumed):

     hart_state, cur_privilege, mstatus, mie, mideleg, menvcfg
                          -- [IntrDefs.sie_cap_gpr] and the [sconf] inside it
     PC, nextPC, minstret, minstret_increment, mcountinhibit, minstretcfg,
     mcycle, mtime, mip
                          -- [pc_is] (its minstret_res / clock_res)
     misa, mseccfg, pma_regions, htif_tohost_base, elp, senvcfg
                          -- [hw_config], pinned and persistent
     satp, tlb            -- [KptShare.tlb_res_pt], which owns BOTH plus the
                             Sv39/asid/root facts about satp and
                             [tlb_snap_ok] about the entry set
     pmpcfg_n, pmpaddr_n  -- [pmp_config], inside the same [tlb_res_pt]

   So nothing has to be invented for the bridge: [tlb_res_pt] is already the
   S-mode owner of the two cells M-mode does not have, and its [tlb_snap_ok]
   is exactly what tells a HIT that the entry it found is a legitimate one --
   the S-mode analogue of what [instr] does for the text bytes.

   The GPRs are likewise absent, for [HartMFrame]'s reason: a leaf is generic
   in its operand indices, so [hfrun] would stall on [bool_decide (r ∈ D)] at
   a symbolic index anyway; they ride in the caller's [R] and are reached per
   node by [HartRegNode]. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        HartSpanChar.
Require Import ColdBoot.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The footprint.                                                         *)
(* ===================================================================== *)
Definition s_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register);
     (R_bitvector_64 minstret : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register);
     (tlb : register) ]}.

Definition s_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register);
     (hart_state : register); (pmpcfg_n : register); (pmpaddr_n : register);
     (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register);
     (misa : register); (mseccfg : register); (pma_regions : register);
     (htif_tohost_base : register); (elp : register); (senvcfg : register);
     (satp : register); (mie : register); (mideleg : register);
     (menvcfg : register) ]}.

Lemma s_disj : s_Drw ## s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.

(* the memberships, precomputed for the same reason [HartMFrame]'s are:
   [set_solver] in an empty context is milliseconds, inside a leaf proof with
   towers in scope it is not *)
Lemma s_w_PC : (R_bitvector_64 PC : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.
Lemma s_w_nPC : (R_bitvector_64 nextPC : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.
Lemma s_w_ms : (R_bitvector_64 minstret : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.
Lemma s_w_mi : (R_bool minstret_increment : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.
Lemma s_w_cy : (R_bitvector_64 mcycle : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.
Lemma s_w_ti : (R_bitvector_64 mtime : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.
Lemma s_w_ip : (R_bitvector_64 mip : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.
Lemma s_w_tlb : (tlb : register) ∈ s_Drw.
Proof. rewrite /s_Drw. set_solver. Qed.

Lemma s_in_PC : (R_bitvector_64 PC : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_nPC : (R_bitvector_64 nextPC : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_ms : (R_bitvector_64 minstret : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_mi : (R_bool minstret_increment : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_ip : (R_bitvector_64 mip : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_tlb : (tlb : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_priv : (cur_privilege : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_mst : (mstatus : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_hart : (hart_state : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_pcfg : (pmpcfg_n : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_paddr : (pmpaddr_n : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_misa : (misa : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_sec : (mseccfg : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_pma : (pma_regions : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_htif : (htif_tohost_base : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_elp : (elp : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_senv : (senvcfg : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_satp : (satp : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_mie : (mie : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_mdl : (mideleg : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.
Lemma s_in_menv : (menvcfg : register) ∈ s_Drw ∪ s_Dro.
Proof. rewrite /s_Drw /s_Dro. set_solver. Qed.

(* ===================================================================== *)
(* The tower.                                                             *)
(* ===================================================================== *)
Section STower.
  Context (pc npc ms : SailStdpp.Values.mword 64)
          (bmi : bool)
          (cy ti ip : SailStdpp.Values.mword 64)
          (mst0 : SailStdpp.Values.mword 64)
          (pcfg : type_of_register pmpcfg_n)
          (paddr : type_of_register pmpaddr_n)
          (mc : SailStdpp.Values.mword 32)
          (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
          (pmar0 : list PMA_Region)
          (elp0 : type_of_register elp)
          (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
          (tlbv : type_of_register tlb).

  Definition s_rs : regstate :=
    register_set (R_bitvector_64 PC) pc
    (    register_set (R_bitvector_64 nextPC) npc
    (    register_set (R_bitvector_64 minstret) ms
    (    register_set (R_bool minstret_increment) bmi
    (    register_set (R_bitvector_64 mcycle) cy
    (    register_set (R_bitvector_64 mtime) ti
    (    register_set (R_bitvector_64 mip) ip
    (    register_set tlb tlbv
    (    register_set cur_privilege Supervisor
    (    register_set mstatus mst0
    (    register_set hart_state (HART_ACTIVE tt)
    (    register_set pmpcfg_n pcfg
    (    register_set pmpaddr_n paddr
    (    register_set (R_bitvector_32 mcountinhibit) mc
    (    register_set (R_bitvector_64 minstretcfg) micfg
    (    register_set misa misa0
    (    register_set mseccfg mseccfg0
    (    register_set pma_regions pmar0
    (    register_set htif_tohost_base None
    (    register_set elp elp0
    (    register_set senvcfg senv0
    (    register_set satp satp0
    (    register_set mie mie0
    (    register_set mideleg mdv0
    (    register_set menvcfg menv0
    (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0)))))))))))))))))))))))))).

  Local Ltac lk :=
    unfold s_rs;
    repeat first
      [ apply register_lookup_set
      | rewrite irrelevant_register_set; [ | vm_compute; reflexivity ] ].

  Lemma s_rs_PC : register_lookup (R_bitvector_64 PC) s_rs = pc.
  Proof. lk. Qed.
  Lemma s_rs_nPC : register_lookup (R_bitvector_64 nextPC) s_rs = npc.
  Proof. lk. Qed.
  Lemma s_rs_ms : register_lookup (R_bitvector_64 minstret) s_rs = ms.
  Proof. lk. Qed.
  Lemma s_rs_mi : register_lookup (R_bool minstret_increment) s_rs = bmi.
  Proof. lk. Qed.
  Lemma s_rs_cy : register_lookup (R_bitvector_64 mcycle) s_rs = cy.
  Proof. lk. Qed.
  Lemma s_rs_ti : register_lookup (R_bitvector_64 mtime) s_rs = ti.
  Proof. lk. Qed.
  Lemma s_rs_ip : register_lookup (R_bitvector_64 mip) s_rs = ip.
  Proof. lk. Qed.
  Lemma s_rs_tlb : register_lookup tlb s_rs = tlbv.
  Proof. lk. Qed.
  Lemma s_rs_priv : register_lookup cur_privilege s_rs = Supervisor.
  Proof. lk. Qed.
  Lemma s_rs_mst : register_lookup mstatus s_rs = mst0.
  Proof. lk. Qed.
  Lemma s_rs_hart : register_lookup hart_state s_rs = HART_ACTIVE tt.
  Proof. lk. Qed.
  Lemma s_rs_pcfg : register_lookup pmpcfg_n s_rs = pcfg.
  Proof. lk. Qed.
  Lemma s_rs_paddr : register_lookup pmpaddr_n s_rs = paddr.
  Proof. lk. Qed.
  Lemma s_rs_mc : register_lookup (R_bitvector_32 mcountinhibit) s_rs = mc.
  Proof. lk. Qed.
  Lemma s_rs_micfg : register_lookup (R_bitvector_64 minstretcfg) s_rs = micfg.
  Proof. lk. Qed.
  Lemma s_rs_misa : register_lookup misa s_rs = misa0.
  Proof. lk. Qed.
  Lemma s_rs_sec : register_lookup mseccfg s_rs = mseccfg0.
  Proof. lk. Qed.
  Lemma s_rs_pma : register_lookup pma_regions s_rs = pmar0.
  Proof. lk. Qed.
  Lemma s_rs_htif : register_lookup htif_tohost_base s_rs = None.
  Proof. lk. Qed.
  Lemma s_rs_elp : register_lookup elp s_rs = elp0.
  Proof. lk. Qed.
  Lemma s_rs_senv : register_lookup senvcfg s_rs = senv0.
  Proof. lk. Qed.
  Lemma s_rs_satp : register_lookup satp s_rs = satp0.
  Proof. lk. Qed.
  Lemma s_rs_mie : register_lookup mie s_rs = mie0.
  Proof. lk. Qed.
  Lemma s_rs_mdl : register_lookup mideleg s_rs = mdv0.
  Proof. lk. Qed.
  Lemma s_rs_menv : register_lookup menvcfg s_rs = menv0.
  Proof. lk. Qed.

End STower.

(* SEALED, for [mm_rs]'s reason: a caller that unfolds a tower pays for a
   25-deep [register_set] chain in every conversion check it does afterwards,
   and the lookups above are the whole interface. *)
Global Opaque s_rs.

(* ===================================================================== *)
(* The frame splits.  [HartMFrame]'s [mm_Df] / [mm_rw_split] / [mm_ro_split] *)
(* one for one, over the larger footprint.                                *)
(* ===================================================================== *)
Section SFrames.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the persistent cells are exactly M-mode's: the hw_config pins plus the
     two counter-config cells.  Everything S-mode ADDS (satp, tlb, mie,
     mideleg, menvcfg) is OWNED, since a bundle hands it over. *)
  Definition s_Df (dq : dfrac) : register -> dfrac := fun r =>
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

  Lemma s_Df_misa (dq : dfrac) : s_Df dq misa = DfracDiscarded.
  Proof. reflexivity. Qed.
  Lemma s_Df_sec (dq : dfrac) : s_Df dq mseccfg = DfracDiscarded.
  Proof. reflexivity. Qed.
  Lemma s_Df_pma (dq : dfrac) : s_Df dq pma_regions = DfracDiscarded.
  Proof. reflexivity. Qed.
  Lemma s_Df_htif (dq : dfrac) : s_Df dq htif_tohost_base = DfracDiscarded.
  Proof. reflexivity. Qed.
  Lemma s_Df_elp (dq : dfrac) : s_Df dq elp = DfracDiscarded.
  Proof. reflexivity. Qed.
  Lemma s_Df_senv (dq : dfrac) : s_Df dq senvcfg = DfracDiscarded.
  Proof. reflexivity. Qed.
  Lemma s_Df_mc (dq : dfrac) :
    s_Df dq (R_bitvector_32 mcountinhibit) = DfracDiscarded.
  Proof. reflexivity. Qed.
  Lemma s_Df_micfg (dq : dfrac) :
    s_Df dq (R_bitvector_64 minstretcfg) = DfracDiscarded.
  Proof. reflexivity. Qed.

  Lemma s_rw_split (rs : regstate) :
    (hreg_frame rs s_Drw : iProp Σ) ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs ∗
     (R_bitvector_64 minstret) ↦ᵣ
       register_lookup (R_bitvector_64 minstret) rs ∗
     (R_bool minstret_increment) ↦ᵣ
       register_lookup (R_bool minstret_increment) rs ∗
     (R_bitvector_64 mcycle) ↦ᵣ register_lookup (R_bitvector_64 mcycle) rs ∗
     (R_bitvector_64 mtime) ↦ᵣ register_lookup (R_bitvector_64 mtime) rs ∗
     (R_bitvector_64 mip) ↦ᵣ register_lookup (R_bitvector_64 mip) rs ∗
     tlb ↦ᵣ register_lookup tlb rs)%I.
  Proof.
    rewrite /hreg_frame /s_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma s_ro_split (dq : dfrac) (rs : regstate) :
    (hreg_frame_ro (s_Df dq) rs s_Dro : iProp Σ) ⊣⊢
    (reg_pointsto cur_privilege dq (register_lookup cur_privilege rs) ∗
     reg_pointsto mstatus dq (register_lookup mstatus rs) ∗
     reg_pointsto hart_state dq (register_lookup hart_state rs) ∗
     reg_pointsto pmpcfg_n dq (register_lookup pmpcfg_n rs) ∗
     reg_pointsto pmpaddr_n dq (register_lookup pmpaddr_n rs) ∗
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
     reg_pointsto senvcfg DfracDiscarded (register_lookup senvcfg rs) ∗
     reg_pointsto satp dq (register_lookup satp rs) ∗
     reg_pointsto mie dq (register_lookup mie rs) ∗
     reg_pointsto mideleg dq (register_lookup mideleg rs) ∗
     reg_pointsto menvcfg dq (register_lookup menvcfg rs))%I.
  Proof.
    rewrite /hreg_frame_ro /s_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite !(s_Df_misa dq) !(s_Df_sec dq) !(s_Df_pma dq) !(s_Df_htif dq)
      !(s_Df_elp dq) !(s_Df_senv dq) !(s_Df_mc dq) !(s_Df_micfg dq).
    unfold s_Df.
    repeat (rewrite decide_False; [|discriminate]).
    by rewrite !bi.sep_assoc.
  Qed.

End SFrames.
