(* ===================================================================== *)
(* UkStepGenFs.v -- THE PILOT'S ENGINE SEAL, DISCHARGED: the X-generic     *)
(* engine of UkStepGen.v instantiated at the ENRICHED slot family          *)
(* [(uexec_ret_fs_F γm, uslot_fs γm)].                                     *)
(*                                                                        *)
(* This is the second half of ask (4)'s compiled receipt.  UkStepGen.v     *)
(* showed the parameterised engine RECOVERS UkStep.v's exported            *)
(* [wp_uk_ecall] by [exact]; this file shows the same engine, with no      *)
(* further proof, produces [UkRunSysFs.FDROW_UKFS_STEP.                    *)
(* wp_uk_ecall_fs_step] -- the pilot's remaining machine-step seal --       *)
(* and therefore [UexecRetFs.FDROW_UKFS_ENGINE] through UkRunSysFs's own    *)
(* functor.  Both seals of stage P2 are now theorems.                      *)
(*                                                                        *)
(* WHAT THE INSTANCE COSTS, EXACTLY: the two facts of the section, each a  *)
(* handful of lines here --                                                *)
(*   [uslot_fs_unfold_gen]         = [UexecRetFs.uslot_fs_unfold] with the *)
(*                                   context binder re-quantified under    *)
(*                                   [Q := fun xi => xi = XI] (the pilot's *)
(*                                   fixpoint is pinned to ONE ambient     *)
(*                                   context; upstream's is not);          *)
(*   [uexec_ret_fs_transparent]    = the transparent arm, [destruct decide]*)
(* ...and the goodmb side condition the seal's statement leaves out, which *)
(* is [UserExecFacts.goodmb_execute_ECALL_U] exactly as UkRunSys.v passes  *)
(* it at the plain family.                                                 *)
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
Require Import HartMemRun.
Require Import WpUmodeStep.   (* [uv_redirect]/[uv_wrok]/[uv_exp]/[uv_upd] *)
Require Import UserExecFacts.
Require Import UserFrame.
Require Import SpecUserret.
Require Import UexecWp.
Require Import UexecSlot.
Require Import TfUser.
Require Import UsysMemOk.
Require Import UmodeRegs.
Require Import UserPerm.
Local Open Scope Z_scope.
Import Defs.
(* ...UkRunSysFs.v's block above, VERBATIM; this file's own below. *)
From iris.base_logic.lib Require Import ghost_var ghost_map.
Require Import UexecRet.
Require Import WpMmodeLeafBase.
Require Import UserHeap.
Require Import UkRun.
Require Import TsoCtx.
Require Import FdSlots.
Require Import FsFdMirror.
Require Import UkStep.
Require Import UexecRetFs.
Require Import UkRunSysFs.    (* [FDROW_UKFS_STEP], [FdRowUkfsEngineOfStep] *)
Require Import UkRunFsLeaf.   (* [FDROW_UKFS_RETIRE], [uk_gmb_at]/[uk_exec_at] *)
Require Import UkStepGen.     (* the X-generic engine *)

Local Open Scope Z_scope.

Section UkGenFs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.

  (* ---- FACT (i) at the enriched family ---------------------------------
     [UexecRetFs.uslot_fs_unfold], with the ambient-context binder put back
     in under [Q].  THE PILOT'S FIXPOINT IS PINNED TO ONE CONTEXT: its
     section takes [CurCtx] as an ambient, so [uslot_fs] says "safe at THIS
     context" where [uslot] says "safe at every context".  That is exactly
     what the generic engine's [Q] parameter is for; here [Q] is the
     singleton [fun xi => xi = XI]. *)
  Lemma uslot_fs_unfold_gen (γm : gname) (W : uvis) :
    uslot_fs γm W ⊣⊢
    ukc' (uexec_ret_fs_F γm) (uslot_fs γm) (fun xi : CurCtx => xi = XI)
      (uvis_perm W) (uvis_M W) (uvis_sz W) (uvis_fd W)
      (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).
  Proof.
    rewrite (uslot_fs_unfold γm W) /ukc'.
    iSplit.
    - iIntros "H" (h xi C pt Rfd Rut) "%Hxi %Hlo %Hpm Hb".
      subst xi.
      iApply ("H" $! h C pt Rfd Rut with "[%] [%] Hb");
        [ exact Hlo | exact Hpm ].
    - iIntros "H" (h C pt Rfd Rut) "%Hlo %Hpm Hb".
      iApply ("H" $! h XI C pt Rfd Rut with "[%] [%] [%] Hb");
        [ reflexivity | exact Hlo | exact Hpm ].
  Qed.

  (* ---- FACT (ii) at the enriched family --------------------------------
     the transparent arm.  [UexecRetFs] never stated it (nothing needed it
     before the generic engine); it is [UexecRet.uexec_ret_transparent]'s
     proof, and it is the whole reason a non-ecall trap costs the
     enrichment nothing. *)
  Lemma uexec_ret_fs_transparent (γm : gname) (sc : mword 64) (W : uvis) :
    sc <> uecall_scause ->
    uexec_ret_fs_F γm (uslot_fs γm) sc W ⊣⊢ uslot_fs γm W.
  Proof.
    intros Hne. rewrite /uexec_ret_fs_F.
    destruct (decide (sc = uecall_scause)); [ contradiction | reflexivity ].
  Qed.

  (* the ecall's goodmb side condition, as UkRunSys.v passes it *)
  Lemma uk_ecall_goodmb (pc : mword 64) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    register_lookup (R_bitvector_64 PC) s.(sregs) = pc ->
    goodmb Du_r Du_w (execute (ECALL tt)) s ∅ = true.
  Proof.
    exact (goodmb_execute_ECALL_U Du_r Du_w s pc
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
  Qed.

  (* ---- THE SEAL'S STATEMENT, PROVEN ---- *)
  Lemma wp_uk_ecall_fs_step_proved
      (γm : gname) (h : CpuId) (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z)
      (M : gmap Z (bv 8)) (fdv : list fdstate) (m : regfile) (pc : mword 64) :
    loop_ok C pt ->
    perm_of (ud_um pt) sz = π ->
    uk_instr π M pc false (ECALL tt) ->
    uvb_fs (CID := h) γm C pt Rfd Rut sz π fdv M m pc -∗
    uexec_ret_fs γm uecall_scause (uvis_of_run m pc M π sz fdv) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlo Hpm Hui.
    exact (wp_uk_ecall' (uexec_ret_fs_F γm) (uslot_fs γm)
             (fun xi : CurCtx => xi = XI)
             (uslot_fs_unfold_gen γm) (uexec_ret_fs_transparent γm)
             (CID := h) C pt Rfd Rut π sz Hlo Hpm eq_refl M m pc fdv Hui
             (uk_ecall_goodmb pc)).
  Qed.

  (* the enriched continuation, read at the generic form.  [ukc_fs] is
     [ukc'] with the ambient-context binder collapsed, so the two directions
     are the two directions of [Q]'s singleton. *)
  Lemma ukc_fs_gen (γm : gname) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (szv : Z) (fdv : list fdstate)
      (m : regfile) (pc : mword 64) :
    ukc_fs γm π M szv fdv m pc ⊣⊢
    ukc' (uexec_ret_fs_F γm) (uslot_fs γm) (fun xi : CurCtx => xi = XI)
      π M szv fdv m pc.
  Proof.
    rewrite /ukc_fs /ukc'.
    iSplit.
    - iIntros "H" (h xi C pt Rfd Rut) "%Hxi %Hlo %Hpm Hb".
      subst xi.
      iApply ("H" $! h C pt Rfd Rut with "[%] [%] Hb");
        [ exact Hlo | exact Hpm ].
    - iIntros "H" (h C pt Rfd Rut) "%Hlo %Hpm Hb".
      iApply ("H" $! h XI C pt Rfd Rut with "[%] [%] [%] Hb");
        [ reflexivity | exact Hlo | exact Hpm ].
  Qed.

  (* ---- THE RETIRE SEAL'S STATEMENT, PROVEN ---- *)
  Lemma wp_uk_retire_fs_later_proved
      (γm : gname) (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z) (fdv : list fdstate)
      `{CID : CpuId} :
    loop_ok C pt ->
    perm_of (ud_um pt) sz = π ->
    forall (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (is_rvc : bool)
      (i : instruction) (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)),
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_wrok wr ->
    uk_gmb_at m pc is_rvc i ->
    uk_gmb_at m pc is_rvc (uv_exp i o) ->
    uk_exec_at m pc is_rvc (uv_exp i o) jt wr ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv M m pc -∗
    ▷ ukc_fs γm π M sz fdv (uv_upd m wr)
        (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlo Hpm M m pc is_rvc i o jt wr Hui Hred Hlpad Hwrok Hg1 Hg2 Hex.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_later' (uexec_ret_fs_F γm) (uslot_fs γm)
              (fun xi : CurCtx => xi = XI)
              (uslot_fs_unfold_gen γm) (uexec_ret_fs_transparent γm)
              C pt Rfd Rut π sz Hlo Hpm eq_refl M m pc fdv is_rvc i o jt wr
              Hui Hred Hlpad Hwrok Hg1 Hg2 Hex with "Hb [Hcont]").
    iNext. iApply (ukc_fs_gen with "Hcont").
  Qed.

End UkGenFs.

(* ===================================================================== *)
(* THE SEAL, DISCHARGED.                                                   *)
(* ===================================================================== *)
Module FdRowUkfsStepGen <: FDROW_UKFS_STEP.
  Lemma wp_uk_ecall_fs_step :
    forall `{!riscvGS Σ} `{GEN : GenId} `{XI : CurCtx}
           `{!ghost_varG Σ Z} `{!ghost_varG Σ umirror}
      (γm : gname) (h : CpuId) (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z)
      (M : gmap Z (bv 8)) (fdv : list fdstate) (m : regfile) (pc : mword 64),
      loop_ok C pt ->
      perm_of (ud_um pt) sz = π ->
      uk_instr π M pc false (ECALL tt) ->
      uvb_fs (CID := h) γm C pt Rfd Rut sz π fdv M m pc -∗
      uexec_ret_fs γm uecall_scause (uvis_of_run m pc M π sz fdv) -∗
      WP (Loop : expr riscv_lang).
  Proof. intros. apply wp_uk_ecall_fs_step_proved; assumption. Qed.
End FdRowUkfsStepGen.

(* ...and P2's OTHER seal, [FDROW_UKFS_ENGINE], falls out of UkRunSysFs's
   own functor at it: the pilot's enriched ecall leaf is now a theorem
   with no [Declare Module] stand-in anywhere under it. *)
Module FdRowUkfsEngineGen := FdRowUkfsEngineOfStep FdRowUkfsStepGen.

(* ===================================================================== *)
(* THE SECOND SEAL: the RETIRE FUNNEL at the enriched bundle.  Stage P5's  *)
(* [FDROW_UKFS_RETIRE] is [wp_uk_retire_later] at the same instance -- the *)
(* collapse note's prediction, compiled.                                   *)
(* ===================================================================== *)
Module FdRowUkfsRetireGen <: FDROW_UKFS_RETIRE.
  Lemma wp_uk_retire_fs_later :
    forall `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
           `{!ghost_varG Σ Z} `{!ghost_varG Σ umirror}
      (γm : gname) (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z) (fdv : list fdstate),
      loop_ok C pt ->
      perm_of (ud_um pt) sz = π ->
      forall (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (is_rvc : bool)
        (i : instruction) (o : option instruction) (jt : option (mword 64))
        (wr : option (mword 5 * mword 64)),
      uk_instr π M pc is_rvc i ->
      uv_redirect i o ->
      is_lpad_instruction i = false ->
      uv_wrok wr ->
      uk_gmb_at m pc is_rvc i ->
      uk_gmb_at m pc is_rvc (uv_exp i o) ->
      uk_exec_at m pc is_rvc (uv_exp i o) jt wr ->
      uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv M m pc -∗
      ▷ ukc_fs γm π M sz fdv (uv_upd m wr)
          (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros. eapply wp_uk_retire_fs_later_proved; eassumption.
  Qed.
End FdRowUkfsRetireGen.

(* THE PILOT'S ENTIRE SEALED SURFACE IS NOW A THEOREM: the leaf tower of
   stage P5 applied at the two discharged seals.  Under upstream ask (4)
   landed IN PLACE, UkRunFsLeaf's SS2 (the re-derived per-kind wrappers)
   goes away entirely -- UkLeaf.v/UkBranch.v's own leaves instantiate. *)
Module FdRowUkfsLeafGen := FdRowUkfsLeaf FdRowUkfsRetireGen FdRowUkfsStepGen.
