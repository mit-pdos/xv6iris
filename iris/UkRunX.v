(* ===================================================================== *)
(* UkRunX.v -- THE DATA-RUN CONSTRUCTORS AT THE ENRICHED (exec) TIER, and *)
(* the run-level receipts a program proof needs to move between the two   *)
(* running predicates.                                                    *)
(*                                                                        *)
(* [UkRun.uslot_of_urun] / [_ro] turn a [urun]-level program proof into   *)
(* the plain slot [uslot W].  This file is their twins at                  *)
(* [UexecRetExec.uslot_x], with the program premise at [urun_x]: the same  *)
(* four pure premises, the same mint of the two heaps, the break and the   *)
(* descriptor authority, the same carve of the free stack -- only the      *)
(* fixpoint the bundle is read at changes.  [uslot_x_of_urun_all] is the   *)
(* general form (the data outside the carved frame is handed over          *)
(* EXCLUSIVELY, in two halves cut at the frame's base and at sp), and the   *)
(* two shapes UkRun.v has are read off it: [uslot_x_of_urun] drops both     *)
(* halves, [uslot_x_of_urun_ro] persists the upper one.                    *)
(*                                                                        *)
(* THE DIRECTION QUESTION.  [urun -∗ urun_x] is UexecRetExec's             *)
(* [urun_urun_x] (a plain kernel promise meets the enriched one).  The     *)
(* OTHER direction -- what a program proof written at [urun] needs when    *)
(* the entry hands it [urun_x] -- is not provable outright, for the reason  *)
(* UexecRetExec's header gives for [uslot W -∗ uslot_x W]: the enriched    *)
(* promise inside [urun_x] demands the exec bundle back at every future    *)
(* exec trap, and a plain [urun] proof never produces one.  It IS provable  *)
(* given a persistent supplier of the bundle at every key:                  *)
(*   [uslot_x_lift_bundle]  □ (∀ W, xbundle uslot_x W) -∗                  *)
(*                          □ (∀ W, uslot W -∗ uslot_x W)                   *)
(* by Loeb through the ▷ in [ukont_x] -- [UexecExecMint.uslot_x_lift_of]'s *)
(* proof with the supplier in place of the mint -- and then                *)
(*   [urun_x_urun_of_bundle]  □ (∀ W, xbundle uslot_x W) -∗                *)
(*                            urun_x … -∗ urun …                            *)
(* is the same postcomposition one level down, no Loeb needed.  The         *)
(* supplier is exactly the obligation the enriched tier adds to a plain     *)
(* program proof, so a slot built this way carries it as an explicit        *)
(* premise (UShKernel.v).                                                   *)
(*                                                                        *)
(* Also here (SS3): [UkStep.uvb_x0] / [UexecRet.ukc] / [uslot_ukc] /       *)
(* [uslot_bump_run] / [UkRun.urun_close(_upd)] restated at the enriched    *)
(* bundle, for UkRunSysX.v's ecall leaf.                                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile InstrBytes WpGpr.
Require Import UserPtTree UserExec ProcPtOwn.
Require Import UmodeMem UmodeArith UmodeText.
Require Import UserPerm UexecWp UexecSlot UexecRet.
Require Import UsysMemOk.
Require Import UmodeRegs.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WpMmodeLeafBase.
Require Import UptTree.
Require Import WpUmodeStore.
Require Import WpUmodeStep.
Require Import UkStep.
Require Import RiscvExtras.
Require Import UserHeap.
Require Import TsoCtx.
Require Import UserFd.
Require Import UkRun.
Require Import UexecRetExec.  (* [uslot_x] / [uvb_x] / [urun_x] -- REQUIRED
                                 DIRECTLY: both are [Typeclasses Opaque] *)
Local Open Scope Z_scope.
Import Defs.

Section UkRunX.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{XG : uexecXG Σ}.
  Context `{!ghost_varG Σ Z}.

  (* ===================================================================== *)
  (* SS1 THE ENTRY, at the enriched slot.                                  *)
  (* ===================================================================== *)

  (* [UserHeap.umap_split_at] at an arbitrary decidable cut: the data map
     split into the part satisfying [P] and its complement *)
  Local Lemma umap_split_pred (γd : gname) (D : gmap Z (bv 8)) (P : Z -> Prop)
      `{!forall a : Z, Decision (P a)} :
    ([∗ map] k ↦ b ∈ D, ubyte γd k b) -∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => P kv.1) D,
         ubyte γd k b) ∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => ~ P kv.1) D,
         ubyte γd k b).
  Proof.
    iIntros "H".
    rewrite -(big_sepM_union (fun k b => ubyte γd k b)
                (base.filter (fun kv : Z * bv 8 => P kv.1) D)
                (base.filter (fun kv : Z * bv 8 => ~ P kv.1) D)
                (map_disjoint_filter_complement _ D)).
    rewrite (map_filter_union_complement (fun kv : Z * bv 8 => P kv.1) D).
    iExact "H".
  Qed.

  (* THE GENERAL FORM (header): [UkRun.uslot_of_urun]'s mint and carve at
     [uslot_x], with the data OUTSIDE the frame handed over exclusively --
     the bytes below the frame's base and the bytes at or above sp.  A
     program whose static data (a .bss buffer, say) lies below its stack
     takes it out of the first half; an argument area is in the second. *)
  Lemma uslot_x_of_urun_all (W : uvis) (avail : nat) :
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (∀ (γt γd γs γfd : gname) (h : CpuId),
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz γs (uvis_sz W) -∗
       utext_all γt (uvis_M W) (uvis_perm W) -∗
       ustd γfd (take NSTD (uvis_fd W)) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                       - 8 * Z.of_nat avail)
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyte γd k b) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                ~ (kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyte γd k b) -∗
       urun_x γt γd γs γfd h (tf_resume_gpr0 (uvis_tf W))
         (tf_resume_pc (uvis_tf W)) avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot_x W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen. iIntros "Hprog". rewrite uslot_x_unfold.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    set (sz := uvis_sz W).
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb_x /uvb_x_F /user_ptm_inv_x.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hfrag & Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    iMod (ufd_alloc_std (uvis_fd W) ∅ Hfdlen (map_empty_subseteq _))
      as (γfd) "(Hufd & Hstd & _)".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    (* ---- the two cuts: at the frame's base, then at sp ---- *)
    set (sp := tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1).
    set (D := udata_lo (uvis_M W) (uvis_perm W) sz).
    set (base := (uint sp - 8 * Z.of_nat avail)%Z).
    iDestruct (umap_split_at γd D base with "Hd") as "[Dlo Dhi]".
    iDestruct (umap_split_pred γd _ (fun a : Z => a < uint sp) with "Dhi")
      as "[Dmid Dtop]".
    (* the upper half is [~ (k < sp)] on [D] itself: a key at or above sp
       is not below [base] *)
    iAssert ([∗ map] k ↦ b ∈ base.filter
                 (fun kv : Z * bv 8 => ~ (kv.1 < uint sp)) D, ubyte γd k b)%I
      with "[Dtop]" as "Dtop".
    { assert (E : base.filter (fun kv : Z * bv 8 => ~ (kv.1 < uint sp))
                    (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                  = base.filter (fun kv : Z * bv 8 => ~ (kv.1 < uint sp)) D).
      { rewrite map_filter_filter. apply map_filter_ext.
        intros k b _. cbn.
        split; [ intros [H _]; exact H | intro H; split; [ exact H | unfold base; lia ] ]. }
      rewrite E. iExact "Dtop". }
    (* ---- the frame, out of the middle ---- *)
    set (f := fun j : nat =>
                default (bv_0 8)
                  (base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                     (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                     !! (base + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < 8 * avail)%nat ->
                   base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                     (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                     !! (base + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hstk j Hj) as [b Hb].
      assert (Hb' : base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                      (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                      !! (base + Z.of_nat j)%Z = Some b).
      { apply umap_filter_lookup_lt; [ unfold base; lia | ].
        apply umap_filter_lookup_ge; [ lia | exact Hb ]. }
      unfold f. rewrite Hb'. reflexivity. }
    iDestruct (ubytes_of_map γd _ base (8 * avail) f Hf with "Dmid") as "Hbs".
    iDestruct (ustack_of_ubytes γd sp avail f Hal8 Hroom with "Hbs") as "Hstk".
    iSpecialize ("Hprog" $! γt γd γs γfd h with "[%] Hszf Ht Hstd Dlo Dtop");
      [ exact Hsz | ].
    iApply "Hprog".
    rewrite /urun_x.
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    iFrame "Hheap Hstk Hufd".
    rewrite /uvb_x /uvb_x_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

  (* [UkRun.uslot_of_urun] at [uslot_x]: the data outside the frame is
     dropped, affinely *)
  Lemma uslot_x_of_urun (W : uvis) (avail : nat) :
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (∀ (γt γd γs γfd : gname) (h : CpuId),
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz γs (uvis_sz W) -∗
       utext_all γt (uvis_M W) (uvis_perm W) -∗
       ustd γfd (take NSTD (uvis_fd W)) -∗
       urun_x γt γd γs γfd h (tf_resume_gpr0 (uvis_tf W))
         (tf_resume_pc (uvis_tf W)) avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot_x W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen. iIntros "Hprog".
    iApply (uslot_x_of_urun_all W avail Hal8 Hroom Hstk Hfdlen).
    iIntros (γt γd γs γfd h) "%Hsz Hszf #Ht Hstd _ _ Hrun".
    iApply ("Hprog" $! γt γd γs γfd h with "[%] Hszf Ht Hstd Hrun").
    exact Hsz.
  Qed.

  (* [UkRun.uslot_of_urun_ro] at [uslot_x]: the data at or above sp is
     persisted and handed over read-only *)
  Lemma uslot_x_of_urun_ro (W : uvis) (avail : nat) :
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (∀ (γt γd γs γfd : gname) (h : CpuId),
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz γs (uvis_sz W) -∗
       utext_all γt (uvis_M W) (uvis_perm W) -∗
       ustd γfd (take NSTD (uvis_fd W)) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                ~ (kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyteq γd DfracDiscarded k b) -∗
       urun_x γt γd γs γfd h (tf_resume_gpr0 (uvis_tf W))
         (tf_resume_pc (uvis_tf W)) avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot_x W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen. iIntros "Hprog".
    iApply (uslot_x_of_urun_all W avail Hal8 Hroom Hstk Hfdlen).
    iIntros (γt γd γs γfd h) "%Hsz Hszf #Ht Hstd _ Dhi Hrun".
    iMod (uarea_persist γd _ with "Dhi") as "#Dhi".
    iApply ("Hprog" $! γt γd γs γfd h with "[%] Hszf Ht Hstd Dhi Hrun").
    exact Hsz.
  Qed.

  (* ===================================================================== *)
  (* SS2 THE BUNDLE-SUPPLIED DOWNGRADE (header).                           *)
  (* ===================================================================== *)

  (* [UexecExecMint.uslot_x_lift_of]'s Loeb argument with the bundle
     SUPPLIED rather than minted -- so this file's cone stays clear of the
     fs tower, and the supplier is what a program proof states as its own
     exec obligation *)
  Lemma uslot_x_lift_bundle :
    □ (∀ W : uvis, xbundle uslot_x W) -∗
    □ (∀ W : uvis, uslot W -∗ uslot_x W).
  Proof.
    iIntros "#Hxb".
    iLöb as "IH".
    iIntros "!>" (W) "Hs".
    rewrite uslot_x_unfold.
    iEval (rewrite uslot_unfold) in "Hs".
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    iApply ("Hs" $! h xi C pt Rfd Rut HRut with "[%] [%] [-]");
      [exact Hlo | exact Hpm |].
    rewrite /uvb /uvb_F.
    iEval (rewrite /uvb_x /uvb_x_F) in "Hb".
    iDestruct "Hb" as
      "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut".
    iSplitR; [iPureIntro; exact Hsz |].
    rewrite /ukont_F.
    iEval (rewrite /ukont_x_F) in "Hk".
    iNext.
    rewrite /ukb_F.
    iEval (rewrite /ukb_x_F) in "Hk".
    iIntros (W' sc stv) "%Hp %Hs' %Hf' (Htm & Hfr & Hret)".
    iApply ("Hk" $! W' sc stv with "[%] [%] [%] [Htm Hfr Hret]");
      [exact Hp | exact Hs' | exact Hf' |].
    iFrame "Htm Hfr".
    iApply (uexec_ret_x_of_bundle with "IH [] Hret").
    iApply "Hxb".
  Qed.

  (* the enriched kernel promise builds the plain one, given the upgrader
     for the returned keys and the bundle for the exec arm: precompose the
     return with [uexec_ret_x_of_bundle] *)
  Lemma ukont_x_ukont_of `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg)
      (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) :
    □ (∀ W : uvis, uslot W -∗ uslot_x W) -∗
    □ (∀ W : uvis, xbundle uslot_x W) -∗
    ukont_x C pt Rfd Rut sz π fdv -∗ ukont C pt Rfd Rut sz π fdv.
  Proof.
    iIntros "#Hup #Hxb Hk". rewrite /ukont /ukont_F.
    iEval (rewrite /ukont_x /ukont_x_F) in "Hk".
    iNext. rewrite /ukb_F.
    iEval (rewrite /ukb_x_F) in "Hk".
    iIntros (W' sc stv) "%Hp %Hs %Hf (Htm & Hfr & Hret)".
    iApply ("Hk" $! W' sc stv with "[%] [%] [%] [Htm Hfr Hret]");
      [exact Hp | exact Hs | exact Hf |].
    iFrame "Htm Hfr".
    iApply (uexec_ret_x_of_bundle with "Hup [] Hret").
    iApply "Hxb".
  Qed.

  Lemma uvb_x_uvb_of `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) :
    □ (∀ W : uvis, uslot W -∗ uslot_x W) -∗
    □ (∀ W : uvis, xbundle uslot_x W) -∗
    uvb_x C pt Rfd Rut sz π fdv M m pc -∗
    uvb C pt Rfd Rut sz π fdv M m pc.
  Proof.
    iIntros "#Hup #Hxb Hb". rewrite /uvb /uvb_F.
    iEval (rewrite /uvb_x /uvb_x_F) in "Hb".
    iDestruct "Hb" as
      "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut".
    iSplitR; [iPureIntro; exact Hsz |].
    iApply (ukont_x_ukont_of with "Hup Hxb Hk").
  Qed.

  (* THE RUN-LEVEL RECEIPT (header): an enriched running bundle is a plain
     one, given the bundle supplier.  This is what lets a program proof
     written at [urun] be entered from [uslot_x_of_urun]. *)
  Lemma urun_x_urun_of_bundle (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    □ (∀ W : uvis, xbundle uslot_x W) -∗
    urun_x γt γd γs γfd h m pc avail -∗ urun γt γd γs γfd h m pc avail.
  Proof.
    iIntros "#Hxb H".
    iDestruct (uslot_x_lift_bundle with "Hxb") as "#Hup".
    rewrite /urun_x.
    iDestruct "H" as (xi C pt Rfd Rut sz M pm fdv)
      "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    rewrite /urun. iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv.
    iSplitR; [iPureIntro; exact Hlo |].
    iSplitR; [iPureIntro; exact Hpm |].
    iSplitR; [iPureIntro; exact HRut |].
    iFrame "Hheap Hstk Hufd".
    iApply (uvb_x_uvb_of with "Hup Hxb Hb").
  Qed.

  (* ===================================================================== *)
  (* SS3 THE ENRICHED BUNDLE'S FACTS AND CONTINUATION -- UkRunSysFs.v's    *)
  (* SS2/SS3 at [uvb_x] / [urun_x].                                        *)
  (* ===================================================================== *)

  (* x0 is pinned inside the bundle -- [UkStep.uvb_x0] at [uvb_x] *)
  Lemma uvb_x_x0 `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (fdv : list fdstate) :
    uvb_x C pt Rfd Rut sz π fdv M m pc -∗
    ⌜m !!! Regidx (mword_of_int 0) = zero_reg⌝ ∗
    uvb_x C pt Rfd Rut sz π fdv M m pc.
  Proof.
    rewrite /uvb_x /uvb_x_F.
    iIntros "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iDestruct (gpr_file_x0 m (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hg") as "[%Hx0 Hg]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut Hk";
      try (iPureIntro; exact Hsz).
  Qed.

  (* THE ENRICHED U-MODE CONTINUATION at a natural state -- [UexecRet.ukc]
     with the enriched bundle; the enriched slot IS this at the key's own
     state ([uslot_x_ukc]) *)
  Definition ukc_x (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
      (szv : Z) (fdv : list fdstate) (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd)
       (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
       (HRut : forall pt' : uptd,
                 ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                              (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) szv = π⌝ -∗
       uvb_x (CID := h) (XI := xi) C pt Rfd Rut szv π fdv M m pc -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma uslot_x_ukc (W : uvis) :
    uslot_x W ⊣⊢
    ukc_x (uvis_perm W) (uvis_M W) (uvis_sz W) (uvis_fd W)
      (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).
  Proof. exact (uslot_x_unfold W). Qed.

  (* the enriched slot at a BUMPED trap-out key: the continuation after the
     syscall returned (a0 := r, pc + 4) -- [UexecRet.uslot_bump_run] *)
  Lemma uslot_x_bump_run (m : regfile) (pc : mword 64)
      (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z)
      (fdv fdv' : list fdstate) (r : mword 64) :
    m !!! Regidx (mword_of_int 0) = zero_reg ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uslot_x (bump (uvis_of_run m pc M π szv fdv) r M' π' szv' fdv')
    ⊣⊢ ukc_x π' M' szv' fdv' (<[Regidx (mword_of_int 10) := r]> m)
             (add_vec_int pc 4).
  Proof.
    intros Hx0 Hal. rewrite uslot_x_ukc.
    rewrite (bump_run_gpr m pc M M' π π' szv szv' fdv fdv' r Hx0)
            (bump_run_pc m pc M M' π π' szv szv' fdv fdv' r Hal).
    reflexivity.
  Qed.

  (* THE RE-CLOSE, at [urun_x] -- [UkRun.urun_close(_upd)]'s twins *)
  Lemma urun_x_close (γt γd γs γfd : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (fdv : list fdstate)
      (m : regfile) (pc : mword 64) (avail : nat) :
    uheap γt γd γs M pm -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    ufd_auth γfd fdv -∗
    (∀ h : CpuId, urun_x γt γd γs γfd h m pc avail -∗ WP (Loop : expr riscv_lang)) -∗
    ukc_x pm M sz fdv m pc.
  Proof.
    iIntros "Hheap Hstk Hufd Hcont".
    rewrite /ukc_x. iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    iApply ("Hcont" $! h). rewrite /urun_x.
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv.
    iFrame "Hheap Hstk Hufd Hb". iPureIntro.
    split_and!; [ exact Hlo | exact Hpm | exact HRut ].
  Qed.

  Lemma urun_x_close_upd (γt γd γs γfd : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (m : regfile) (rd : mword 5) (v : mword 64)
      (sz : Z) (fdv : list fdstate) (pc' : mword 64) (avail : nat) :
    unot_sp rd ->
    uheap γt γd γs M pm -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    ufd_auth γfd fdv -∗
    (∀ h : CpuId, urun_x γt γd γs γfd h (<[Regidx rd := v]> m) pc' avail -∗
                  WP (Loop : expr riscv_lang)) -∗
    ukc_x pm M sz fdv (<[Regidx rd := v]> m) pc'.
  Proof.
    intros Hns. iIntros "Hheap Hstk Hufd Hcont".
    iApply (urun_x_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd v m Hns). iExact "Hstk".
  Qed.

End UkRunX.
