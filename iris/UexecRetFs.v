(* ===================================================================== *)
(* UexecRetFs.v -- THE ENRICHED TRAP CONTRACT (fd-row pilot): the          *)
(* user/kernel syscall arm with an fs PAYLOAD, as a PARALLEL FORM beside   *)
(* UexecRet.v.                                                             *)
(*                                                                         *)
(* Design of record: claude-notes/design/fd-row-pilot.md.  This is the     *)
(* Φ-refinement user-wp-slot.md part (A) parks (a later refinement adds   *)
(* an iProp premise under the same ∀ without changing the shape), landed  *)
(* in its DEPOSIT-DISJUNCT shape: for the syscall numbers in               *)
(* [FsFdMirror.uenr_dom] the returning-syscall arm offers, beside the      *)
(* plain arm VERBATIM, an enriched branch in which the process DEPOSITS    *)
(* its mirror half ([FsFdMirror.mcur]) and receives it back stepped by     *)
(* the row's pure relation ([FsFdMirror.ufs_step]).                        *)
(*                                                                         *)
(* TRANSITIONAL BY DESIGN (the SpecNamexEra precedent): at upstream        *)
(* adoption the one disjunct moves into [UexecRet.uexec_ret_F] (with the   *)
(* payload family behind a small ambient class so UexecRet's cone gains    *)
(* no fs import) and this file's fixpoint collapses into the original.     *)
(* The exact diff is the design note's section 6 item 1.                   *)
(*                                                                         *)
(* WHAT IS PROVEN HERE (the conservativity receipts):                      *)
(*   [uexec_ret_fs_of]  -- the plain return builds the enriched one (the   *)
(*                         left injection, every arm);                     *)
(*   [uslot_uslot_fs]   -- every plain-safe process is enriched-safe: the  *)
(*                         landed program proofs lift for free;            *)
(*   [ukont_fs_ukont] / [urun_fs_urun] -- the enriched kernel promise      *)
(*                         implies the plain one, so an enriched bundle    *)
(*                         can always fall back (losing the enrichment).   *)
(*                                                                         *)
(* WHAT IS SEALED, AND WHY THE SEAL IS SHAPED AS A LEAF AND NOT AS A       *)
(* WAND.  [FDROW_UKFS_ENGINE.wp_uk_ecall_fs] is the enriched ecall leaf    *)
(* (the [wp_uk_ecall_quiet] twin over [urun_fs]); its discharge is         *)
(* engine-level work against [uvb_fs]'s own ecall step and needs NO        *)
(* kernel enrichment -- the deposit arm is the PROCESS's to take.  The     *)
(* kernel-side enrichment -- who ever HANDS a process a [uvb_fs], i.e.     *)
(* the loop round that discharges the deposit arm from the AU receipts --  *)
(* is deliberately NOT sealed as a wand [mirror_boot ∗ uslot_fs -∗ uslot]: *)
(* such a wand is UNDISCHARGEABLE at its own altitude (from a plain        *)
(* [ukont] nothing can conjure the [ufs_step] tie -- the receipts live in  *)
(* the dispatcher's post, which only the LOOP's Löb sees), so sealing it   *)
(* would be the GAP-premise trap in Module-Type clothing.  The loop-       *)
(* altitude statement and its staging live in the worklist's FD-ROW        *)
(* PILOT section (stages P3/P5).                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes WpGpr.
Require Import AlignBits.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import UserExec.
Require Import SpecUserret.
Require Import UexecWp.
Require Import UexecSlot.
Require Import TfUser.
Require Import UsysMemOk.
Require Import UmodeRegs.
Require Import UserPerm.
Local Open Scope Z_scope.
Import Defs.
(* ...UexecRet.v's block above, VERBATIM (durable-notes: trimmed imports
   have OOM'd the build); the enrichment's own imports below. *)
From iris.base_logic.lib Require Import ghost_var ghost_map.
Require Import UexecRet.     (* the plain contract this file encloses --
                                REQUIRED DIRECTLY: [uslot]/[uvb] are
                                [Typeclasses Opaque] and the seal does not
                                travel through a re-export *)
Require Import WpMmodeLeafBase.   (* [csp_rs1] *)
Require Import UserHeap.     (* [uheap]/[ustack]/[ubytesq]/[uinstr_is] *)
Require Import UkRun.        (* [urun] -- the plain running predicate *)
Require Import TsoCtx.
Require Import FsFdMirror.   (* [umirror]/[mcur]/[ufs_step]/[uenr_dom] *)

Section UexecRetFs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.

  (* =================================================================== *)
  (* SS1 THE CONTRACT, as one guarded fixpoint -- UexecRet.v SS3 with the *)
  (* ONE disjunct spliced into the returning-syscall arm.                 *)
  (* =================================================================== *)

  (* (A) what user execution hands back, at the fixpoint variable [X].
     Differences from [UexecRet.uexec_ret_F], and there are exactly two:
     the returning-syscall arm case-splits on [uenr_dom n], and where that
     bit is set the arm is [plain ∨ enriched] -- the PROCESS supplies the
     return, so the disjunction is the process's choice and the plain
     branch is today's arm verbatim. *)
  Definition uexec_ret_fs_F (γm : gname) (X : uvis -d> iPropO Σ)
      (sc : mword 64) (W : uvis) : iProp Σ :=
    (if decide (sc = uecall_scause) then
       let n := usys_num (uvis_tf W) in
       if decide (n = UsysMemOk.USYS_exit) then emp
       else if decide (n = UsysMemOk.USYS_fork) then
         ((∀ r : mword 64, ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
             X (bump W r (uvis_M W) (uvis_perm W) (uvis_sz W))) ∗
          X (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W) (uvis_sz W)))
       else if uenr_dom n then
         ((∀ (r : mword 64) (M' : gmap Z (bv 8))
             (π' : gmap (mword 27) uperm) (szv' : Z),
             ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W)
                          (uvis_sz W) M' π' szv'⌝ -∗
             X (bump W r M' π' szv'))
          ∨ (∃ u : umirror,
               mcur γm u ∗
               (∀ (r : mword 64) (M' : gmap Z (bv 8))
                  (π' : gmap (mword 27) uperm) (szv' : Z) (u' : umirror),
                  ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W)
                               (uvis_sz W) M' π' szv'⌝ -∗
                  ⌜ufs_step n (uvis_tf W) (uvis_M W) r u u'⌝ -∗
                  mcur γm u' -∗
                  X (bump W r M' π' szv'))))
       else (∀ (r : mword 64) (M' : gmap Z (bv 8))
               (π' : gmap (mword 27) uperm) (szv' : Z),
               ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W)
                            (uvis_sz W) M' π' szv'⌝ -∗
               X (bump W r M' π' szv'))
     else X W)%I.

  (* (B) the kernel obligation, and (C) the bundle -- UexecRet.v verbatim
     at the enriched return *)
  Definition ukb_fs_F (γm : gname) (X : uvis -d> iPropO Σ) `{CID : CpuId}
      `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) : iProp Σ :=
    (∀ (W' : uvis) (sc stv : mword 64),
       ⌜uvis_perm W' = π⌝ -∗
       ⌜uvis_sz W' = sz⌝ -∗
       trapped_machine C pt Rut sz sc stv W' ∗ uexec_ret_fs_F γm X sc W' -∗
       WP (Loop : expr riscv_lang))%I.

  Definition ukont_fs_F (γm : gname) (X : uvis -d> iPropO Σ) `{CID : CpuId}
      `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) : iProp Σ :=
    (▷ ukb_fs_F γm X C pt Rut sz π)%I.

  Definition uvb_fs_F (γm : gname) (X : uvis -d> iPropO Σ) `{CID : CpuId}
      `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (uv_amb ∗ uv_regs ∗ ⌜usz_ok sz⌝ ∗ user_ptm_inv pt sz M ∗ user_cfg C ∗
     gpr_file m ∗ pc_is pc ∗ Rut pt ∗ ukont_fs_F γm X C pt Rut sz π)%I.

  Definition uslot_fs_F (γm : gname) (X : uvis -d> iPropO Σ)
      : uvis -d> iPropO Σ :=
    fun W =>
      (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd)
         (Rut : uptd -> iProp Σ),
         ⌜loop_ok C pt⌝ -∗
         ⌜perm_of (ud_um pt) (uvis_sz W) = uvis_perm W⌝ -∗
         uvb_fs_F γm X (CID := h) (XI := xi) C pt Rut (uvis_sz W) (uvis_perm W)
           (uvis_M W) (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         -∗
         WP (Loop : expr riscv_lang))%I.

  Local Instance uslot_fs_F_contractive (γm : gname) :
    Contractive (uslot_fs_F γm).
  Proof.
    rewrite /uslot_fs_F /uvb_fs_F /ukont_fs_F /ukb_fs_F /uexec_ret_fs_F.
    solve_contractive.
  Qed.

  Definition uslot_fs (γm : gname) : uvis -> iProp Σ :=
    fixpoint (uslot_fs_F γm).
  Definition uexec_ret_fs (γm : gname) : mword 64 -> uvis -> iProp Σ :=
    uexec_ret_fs_F γm (uslot_fs γm).
  Definition ukb_fs `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (γm : gname) (C : ucfg) (pt : uptd)
      (Rut : uptd -> iProp Σ) (sz : Z) (π : gmap (mword 27) uperm)
      : iProp Σ := ukb_fs_F γm (uslot_fs γm) C pt Rut sz π.
  Definition ukont_fs `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (γm : gname) (C : ucfg) (pt : uptd)
      (Rut : uptd -> iProp Σ) (sz : Z) (π : gmap (mword 27) uperm)
      : iProp Σ := ukont_fs_F γm (uslot_fs γm) C pt Rut sz π.
  Definition uvb_fs `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (γm : gname) (C : ucfg) (pt : uptd)
      (Rut : uptd -> iProp Σ) (sz : Z) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    uvb_fs_F γm (uslot_fs γm) C pt Rut sz π M m pc.

  Lemma uslot_fs_unfold (γm : gname) (W : uvis) :
    uslot_fs γm W ⊣⊢
    (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd)
       (Rut : uptd -> iProp Σ),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) (uvis_sz W) = uvis_perm W⌝ -∗
       uvb_fs (CID := h) (XI := xi) γm C pt Rut (uvis_sz W) (uvis_perm W)
         (uvis_M W)
         (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)) -∗
       WP (Loop : expr riscv_lang)).
  Proof. exact (fixpoint_unfold (uslot_fs_F γm) W). Qed.

  (* =================================================================== *)
  (* SS2 THE CONSERVATIVITY RECEIPTS.                                     *)
  (* =================================================================== *)

  (* the left injection, arm by arm: a plain return builds an enriched
     one, given a slot upgrader for the returned keys *)
  Lemma uexec_ret_fs_of (γm : gname) (sc : mword 64) (W : uvis) :
    □ (∀ W' : uvis, uslot W' -∗ uslot_fs γm W') -∗
    uexec_ret sc W -∗
    uexec_ret_fs γm sc W.
  Proof.
    rewrite /uexec_ret_fs /uexec_ret /uexec_ret_F /uexec_ret_fs_F.
    cbv zeta.
    iIntros "#Hup Hret".
    destruct (decide (sc = uecall_scause)); [| by iApply "Hup"].
    destruct (decide (usys_num (uvis_tf W) = UsysMemOk.USYS_exit));
      [done |].
    destruct (decide (usys_num (uvis_tf W) = UsysMemOk.USYS_fork)).
    { iDestruct "Hret" as "[Hp Hc]".
      iSplitL "Hp".
      - iIntros (r) "%Hr".
        iApply "Hup". iApply ("Hp" $! r with "[%]"). exact Hr.
      - iApply "Hup". iExact "Hc". }
    destruct (uenr_dom (usys_num (uvis_tf W))) eqn:He.
    - iLeft. iIntros (r M' π' szv') "%Hok".
      iApply "Hup".
      iApply ("Hret" $! r M' π' szv' with "[%]"). exact Hok.
    - iIntros (r M' π' szv') "%Hok".
      iApply "Hup".
      iApply ("Hret" $! r M' π' szv' with "[%]"). exact Hok.
  Qed.

  (* THE BRIDGE: every plain-safe process is enriched-safe.  This is what
     makes the enrichment a conservative extension -- every landed program
     proof lifts through it for free -- and it is the receipt the upstream
     diff (design section 6 item 1) rides on. *)
  Lemma uslot_uslot_fs (γm : gname) (W : uvis) :
    uslot W -∗ uslot_fs γm W.
  Proof.
    iLöb as "IH" forall (W).
    iIntros "Hs".
    rewrite uslot_fs_unfold.
    iIntros (h xi C pt Rut) "%Hlo %Hpm Hb".
    rewrite /uvb_fs /uvb_fs_F.
    iDestruct "Hb" as "(Hamb & Hur & %Hsz & Hpt & Hcfg & Hg & Hpc & Hrut & Hk)".
    iEval (rewrite uslot_unfold) in "Hs".
    iApply ("Hs" $! h xi C pt Rut with "[%] [%] [-]");
      [exact Hlo | exact Hpm |].
    rewrite /uvb /uvb_F.
    iFrame "Hamb Hur Hpt Hcfg Hg Hpc Hrut".
    iSplitR; [iPureIntro; exact Hsz |].
    (* the plain kernel promise, from the enriched one: precompose the
       return with the left injection *)
    rewrite /ukont_F.
    iEval (rewrite /ukont_fs_F) in "Hk".
    iNext.
    rewrite /ukb_F /ukb_fs_F.
    iIntros (W' sc stv) "%Hp %Hs' [Htm Hret]".
    iApply ("Hk" $! W' sc stv with "[%] [%] [Htm Hret]");
      [exact Hp | exact Hs' |].
    iFrame "Htm".
    iApply (uexec_ret_fs_of with "IH Hret").
  Qed.

  Lemma uexec_ret_to_fs (γm : gname) (sc : mword 64) (W : uvis) :
    uexec_ret sc W -∗ uexec_ret_fs γm sc W.
  Proof.
    iIntros "H". iApply (uexec_ret_fs_of with "[] H").
    iIntros "!>" (W') "Hs". iApply uslot_uslot_fs. iExact "Hs".
  Qed.

  (* ...and the fallback direction: the enriched kernel promise implies
     the plain one (the enrichment is FORGOTTEN, not refunded -- the
     one-way street the design note records) *)
  Lemma ukont_fs_ukont `{CID : CpuId} `{XIK : TsoCtx.CurCtx}
      (γm : gname) (C : ucfg) (pt : uptd)
      (Rut : uptd -> iProp Σ) (sz : Z) (π : gmap (mword 27) uperm) :
    ukont_fs γm C pt Rut sz π -∗ ukont C pt Rut sz π.
  Proof.
    iIntros "Hk". rewrite /ukont /ukont_F.
    iEval (rewrite /ukont_fs /ukont_fs_F) in "Hk".
    iNext. rewrite /ukb_F.
    iIntros (W' sc stv) "%Hp %Hs [Htm Hret]".
    iApply ("Hk" $! W' sc stv with "[%] [%] [Htm Hret]");
      [exact Hp | exact Hs |].
    iFrame "Htm".
    iApply (uexec_ret_to_fs with "Hret").
  Qed.

  (* =================================================================== *)
  (* SS3 THE ENRICHED RUNNING PREDICATE, and the string resource the      *)
  (* enriched leaf pins the fetched path with.                            *)
  (* =================================================================== *)

  Definition urun_fs (γm γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) : iProp Σ :=
    (∃ (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
       (sz : Z) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm),
       ⌜ loop_ok C pt ⌝ ∗ ⌜ perm_of (ud_um pt) sz = pm ⌝ ∗
       uheap γt γd γs M pm ∗
       ustack γd (m !!! Regidx csp_rs1) avail ∗
       uvb_fs (CID := h) (XI := xi) γm C pt Rut sz pm M m pc)%I.

  Lemma urun_fs_urun (γm γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    urun_fs γm γt γd γs h m pc avail -∗ urun γt γd γs h m pc avail.
  Proof.
    iIntros "H".
    iDestruct "H" as (xi C pt Rut sz M pm)
      "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    rewrite /urun. iExists xi, C, pt, Rut, sz, M, pm.
    iSplitR; [iPureIntro; exact Hlo |].
    iSplitR; [iPureIntro; exact Hpm |].
    iFrame "Hheap Hstk".
    rewrite /uvb /uvb_F /uvb_fs /uvb_fs_F.
    iDestruct "Hb" as "(Hamb & Hur & %Hsz & Hpt & Hcfg & Hg & Hpc & Hrut & Hk)".
    iFrame "Hamb Hur Hpt Hcfg Hg Hpc Hrut".
    iSplitR; [iPureIntro; exact Hsz |].
    iApply (ukont_fs_ukont with "Hk").
  Qed.

  (* the caller-owned NUL-terminated path string at [a]: the bytes, none
     of them NUL, with the terminator at index [length pl] *)
  Definition ustrq (γd : gname) (dq : dfrac) (a : Z) (pl : list (bv 8))
      : iProp Σ :=
    (⌜Forall (fun b : bv 8 => b <> unul) pl⌝ ∗
     ⌜(length pl < UMAXPATH)%nat⌝ ∗
     ubytesq γd dq a (S (length pl)) (ustr_bytes pl))%I.

  (* a run's bytes are present in the image at their own values --
     [UkRunSys.uheap_ubytes_run] minus the bound, restated here so this
     file's cone stops at UserHeap (the mirror-staleness note in the
     worklist records why) *)
  Local Lemma uheap_ubytes_pts (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (dq : dfrac) (a : Z) (nb : nat)
      (f : nat -> bv 8) :
    uheap γt γd γs M pmv -∗ ubytesq γd dq a nb f -∗
    ⌜ forall j : nat, (j < nb)%nat -> M !! (a + Z.of_nat j)%Z = Some (f j) ⌝.
  Proof.
    iInduction nb as [| kb IH] "IH"; iIntros "Hheap Hbs".
    { iPureIntro. intros j Hj. exfalso. lia. }
    iEval (rewrite /ubytesq seq_S big_sepL_app /=) in "Hbs".
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    iDestruct ("IH" with "Hheap Hlo") as %Hk.
    iDestruct (uheap_ubyte with "Hheap Hhi") as %(HM & _ & _).
    iPureIntro. intros j Hj.
    destruct (decide (j = kb)) as [-> | Hne]; [ exact HM | ].
    apply Hk. lia.
  Qed.

  (* owning the string is what makes the row's [ustr_read] arm CONCRETE:
     the resource half of FsFdMirror's [ustr_read_of] *)
  Lemma uheap_ustrq (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (dq : dfrac) (a : Z) (pl : list (bv 8)) :
    uheap γt γd γs M pm -∗ ustrq γd dq a pl -∗
    ⌜ustr_read M a = Some pl⌝.
  Proof.
    iIntros "Hheap (%Hall & %Hlen & Hbs)".
    iDestruct (uheap_ubytes_pts γt γd γs M pm dq a (S (length pl))
                 (ustr_bytes pl) with "Hheap Hbs") as %HM.
    iPureIntro. apply ustr_read_of; [exact Hlen | exact Hall |].
    intros j Hj. apply HM. lia.
  Qed.

  (* =================================================================== *)
  (* SS4 THE ENRICHED ECALL LEAF'S BODY (sealed below).                   *)
  (*                                                                      *)
  (* [wp_uk_ecall_quiet]'s calling convention over [urun_fs], with the     *)
  (* deposit taken from the caller and the continuation receiving the      *)
  (* stepped mirror beside the pure row tie at the CONCRETE path the       *)
  (* caller's string pins.  The prover discharges it against [uvb_fs]'s    *)
  (* own ecall step (a [UkStep.wp_uk_ecall] twin at the enriched bundle),  *)
  (* taking the RIGHT branch of the arm with the caller's deposit -- no    *)
  (* kernel-side enrichment is involved (header).                          *)
  (* =================================================================== *)
  Definition wp_uk_ecall_fs_body (γm γt γd γs : gname) (h : CpuId)
      (m : regfile) (pc : mword 64) (n : Z) (u : umirror)
      (pl : list (bv 8)) (dq : dfrac) (avail : nat) : iProp Σ :=
    (uinstr_is γt pc false (ECALL tt) -∗
     urun_fs γm γt γd γs h m pc avail -∗
     mcur γm u -∗
     ustrq γd dq (uint (m !!! Regidx (mword_of_int 10))) pl -∗
     (∀ (h' : CpuId) (r : mword 64) (u' : umirror),
        ⌜ufs_step_at n pl (tf_of m pc) r u u'⌝ -∗
        mcur γm u' -∗
        ustrq γd dq (uint (m !!! Regidx (mword_of_int 10))) pl -∗
        urun_fs γm γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
          (add_vec_int pc 4) avail -∗
        WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

End UexecRetFs.

(* the bundle wraps [gpr_file] and the slot wraps the bundle: sealed,
   exactly as UexecRet.v seals its own pair; consumers go through
   [uslot_fs_unfold] / [rewrite /uvb_fs /uvb_fs_F], and a file
   manipulating either must [Require Import UexecRetFs] directly *)
Global Typeclasses Opaque uslot_fs uvb_fs.

(* ===================================================================== *)
(* THE SEAL: what the prover lane discharges (worklist, FD-ROW PILOT      *)
(* stage P2).  Engine-level only -- see the header for why no kernel-side *)
(* wand is sealed here.                                                   *)
(* ===================================================================== *)
Module Type FDROW_UKFS_ENGINE.
  Parameter wp_uk_ecall_fs :
    forall `{!riscvGS Σ} `{GEN : GenId} `{XI : CurCtx}
           `{!ghost_varG Σ Z} `{!ghost_varG Σ umirror}
      (γm γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (n : Z) (u : umirror) (pl : list (bv 8)) (dq : dfrac) (avail : nat),
      usys_num (tf_of m pc) = n ->
      uenr_dom n = true ->
      is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
      ⊢ wp_uk_ecall_fs_body γm γt γd γs h m pc n u pl dq avail.
End FDROW_UKFS_ENGINE.
