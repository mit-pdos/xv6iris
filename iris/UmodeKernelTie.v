(* ===================================================================== *)
(* UmodeKernelTie.v -- THE MOVERS between the KERNEL trap loop's resume     *)
(* vocabulary (UserFrame / UserPtTree / UserExec, what a user-execution WP  *)
(* slot is stated over) and the VERIFIED-EXECUTION tier's (UmodeCap's       *)
(* [uv_cap_gpr] + [pc_is], what a verified program's WP threads).           *)
(*                                                                         *)
(* See claude-notes/projects/user-wp-slot.md SS3, first bullet.  PROGRAM-   *)
(* GENERIC on purpose: every per-program slot constructor (USyncKernel.v is *)
(* the first) crosses the same seam, and the crossing is the same three     *)
(* observations every time --                                              *)
(*                                                                         *)
(*   * [user_pt_inv pt M] and [uv_lin]'s page half are THE SAME [pointsto]  *)
(*     bytes: [UserPtTree.umem_own] is definitionally                       *)
(*     [<<dom M = uva_dom pt>> * (big_sepM ... pointsto)] and [UmodeMem.umem] *)
(*     is that big_sepM.  The two pure conjuncts the Umode tier does not    *)
(*     read ([uva_pa_inj], [upt_acc_wf], and the domain equation) are       *)
(*     dropped -- affinely, and they are re-derivable from the table.       *)
(*   * [u_regs] at a CONCRETE resume state opens ([u_regs_pc_is]) into the  *)
(*     six machine cells, [pc_is va] and [gpr_file g]; [uv_regs] re-packs   *)
(*     the four CSR values existentially, so [ms_v]/[sc_v]/[stval_v]/       *)
(*     [sepc_v] are ABSORBED and only [user_mstatus_ok ms_v] is needed.     *)
(*   * [uv_amb] IS the slot's three persistent premises, in order.          *)
(*                                                                         *)
(* ONE AMBIENT HART throughout ([Context {CID}]): a slot's body has already *)
(* fixed [h] by the time these fire, and every resource here -- [hw_config],*)
(* [u_regs], [user_pt_inv], [user_cfg], [uv_cap_gpr] -- is that hart's.     *)
(* [uv_cap] itself is hart-FREE and simply rides through.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import InstrBytes RegFile WpGpr.
Require Import MinstretInv WireInv.
Require Import UptTree UserPtTree UserFrame UserExec.
Require Import UmodeMem UmodeCap.
Local Open Scope Z_scope.
Import Defs.

Section UmodeKernelTie.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* SS1 The page half.                                                    *)
  (* ------------------------------------------------------------------- *)

  (* [user_pt_inv] carries strictly more than the Umode tier's page half:
     the same tree invariant, the same bytes, plus three pure facts the
     verified engines never read.  One direction only -- this is a
     WEAKENING, and the pure facts are exactly what would be needed to go
     back. *)
  Lemma user_pt_inv_umode (pt : uptd) (M : gmap Z (bv 8)) :
    user_pt_inv pt M -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M.
  Proof.
    iIntros "(Htlb & [%Hdom Hmem] & _ & _)".
    rewrite /umem. iFrame "Htlb Hmem".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS2 The machine-cell half.                                            *)
  (* ------------------------------------------------------------------- *)

  (* the slot's concrete [u_regs] (PC and nextPC both at [va]) is
     [uv_regs] -- CSR values swallowed by its existentials -- plus the two
     resources every verified leaf threads separately. *)
  Lemma u_regs_uv_regs (ms_v sc_v stval_v sepc_v va : mword 64) (g : regfile) :
    user_mstatus_ok ms_v ->
    u_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g -∗
    uv_regs ∗ gpr_file g ∗ pc_is va.
  Proof.
    iIntros (Hms) "Hregs".
    iEval (rewrite u_regs_pc_is) in "Hregs".
    iDestruct "Hregs" as "(Hhs & Hpriv & Hmst & Hsc & Hstv & Hsep & Hpc & Hg)".
    rewrite /uv_regs.
    iFrame "Hg Hpc".
    iExists ms_v, sc_v, stval_v, sepc_v.
    iFrame "Hhs Hpriv Hmst Hsc Hstv Hsep".
    iPureIntro. exact Hms.
  Qed.

  (* the three persistent premises ARE [uv_amb] *)
  Lemma uv_amb_intro :
    hw_config -∗ minstret_inv -∗ wire_inv -∗ uv_amb.
  Proof. iIntros "Hhw Hmi Hwi". rewrite /uv_amb. iFrame "Hhw Hmi Hwi". Qed.

  (* ------------------------------------------------------------------- *)
  (* SS3 THE COMPOSITE: a slot's whole spatial premise set, plus the trap   *)
  (* capability, IS the verified tier's threading bundle at the same        *)
  (* concrete state.  Framed row by row (durable-notes: [iFrame] resolves    *)
  (* its instances up to delta, so a big bundle is fed named rows, never a   *)
  (* bare [iFrame]).                                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma uexec_state_uv_cap_gpr (C : ucfg) (pt : uptd) (Psi : usys_protocol Σ)
      (M : gmap Z (bv 8)) (g : regfile)
      (ms_v sc_v stval_v sepc_v va : mword 64) :
    user_mstatus_ok ms_v ->
    uv_cap C pt Psi -∗
    hw_config -∗ minstret_inv -∗ wire_inv -∗
    u_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g -∗
    user_pt_inv pt M -∗
    user_cfg C -∗
    uv_cap_gpr C pt Psi M g ∗ pc_is va.
  Proof.
    iIntros (Hms) "#Hcap Hhw Hmi Hwi Hregs Hpt Hcfg".
    iDestruct (uv_amb_intro with "Hhw Hmi Hwi") as "#Hamb".
    iDestruct (u_regs_uv_regs ms_v sc_v stval_v sepc_v va g Hms with "Hregs")
      as "(Hur & Hg & Hpc)".
    iDestruct (user_pt_inv_umode with "Hpt") as "(Htlb & Hmem)".
    iFrame "Hpc".
    rewrite /uv_cap_gpr /uv_lin.
    iFrame "Hcap".
    iFrame "Hamb".
    iFrame "Hur".
    iFrame "Htlb".
    iFrame "Hmem".
    iFrame "Hcfg".
    iFrame "Hg".
  Qed.

End UmodeKernelTie.
