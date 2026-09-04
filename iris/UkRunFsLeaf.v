(* ===================================================================== *)
(* UkRunFsLeaf.v -- THE ENRICHED LEAF TOWER (fd-row pilot, prover stage    *)
(* P5): the plain leaves init's console preamble uses, re-threaded on      *)
(* [UexecRetFs.urun_fs] / [UkRunSysFs.ukc_fs] instead of [UkRun.urun] /    *)
(* [UexecRet.ukc], plus the two enriched ecall leaves the preamble's       *)
(* syscall stubs take.                                                     *)
(*                                                                         *)
(* Design of record: claude-notes/design/fd-row-pilot.md; the prover plan   *)
(* is the "## FD-ROW PILOT" section of                                     *)
(* claude-notes/projects/fs-syscall-specs.md (stage P5).                   *)
(*                                                                         *)
(* WHY THE TWINS EXIST AT ALL, AND WHY THEY ARE CHEAP.  An enriched        *)
(* process runs on [urun_fs], whose bundle carries [ukont_fs] rather than  *)
(* [ukont]; the plain leaves are TYPED at [uvb]/[ukc], and [uslot_fs] does  *)
(* NOT imply [uslot] (UexecRetFs's finding 1), so a plain leaf cannot be    *)
(* fed an enriched bundle and cannot hand one back.  Two facts make the     *)
(* re-thread nearly free anyway:                                           *)
(*                                                                         *)
(*   (a) A NON-ECALL STEP NEVER TOUCHES THE RETURN CONTRACT'S ECALL ARM.    *)
(*       [UexecRet.uexec_ret_F] and [UexecRetFs.uexec_ret_fs_F] are         *)
(*       LITERALLY the same proposition off [sc = uecall_scause] -- both     *)
(*       are the transparent [X W] -- and the enrichment is a splice into   *)
(*       the ecall arm only.  So every non-ecall leaf's CONTENT is          *)
(*       untouched by the enrichment; only its TYPE moves.                  *)
(*   (b) The plumbing already exists: [UkRunSysFs] proved [ukc_fs],         *)
(*       [urun_fs_close(_upd)] and [uvb_fs_x0], which are the whole of what *)
(*       a [urun]-level wrapper does around a [uvb]-level leaf.             *)
(*                                                                         *)
(* WHAT IS SEALED HERE: ONE statement, [FDROW_UKFS_RETIRE.                  *)
(* wp_uk_retire_fs_later] = [UkStep.wp_uk_retire_later] with [uvb -> uvb_fs]*)
(* and [ukc -> ukc_fs].  Two type substitutions, ZERO fs content.  It is    *)
(* the RETIRE FUNNEL, and every leaf below -- register writes, auipc, the   *)
(* three jumps, and the conditional branches (which go through             *)
(* [UkBranch.wp_uk_btype_gen_later], itself one application of the retire   *)
(* funnel) -- is derived from it here, exactly as UkLeaf.v/UkBranch.v       *)
(* derive theirs from the plain funnel.  So the "one twin per leaf KIND"    *)
(* the plan budgeted collapses to ONE SEAL FOR ALL KINDS in this slice.     *)
(* Beside it stands P2's [FDROW_UKFS_STEP.wp_uk_ecall_fs_step]; those two   *)
(* are the entire sealed surface of the enriched walk.                      *)
(*                                                                         *)
(* WHY IT COULD NOT BE STATED AWAY.  Exactly P2's measurement, one funnel   *)
(* over: [UkStep]'s §3/§5 hardwire [uvb]/[ukb]/[ukc] into [uk_step_obl] /   *)
(* [uk_ih] / [wp_uk_step_gen], and the retiring arm REBUILDS the bundle at  *)
(* the new file ([uk_psi_active]) from the promise it opened -- so the      *)
(* enriched promise has to be the one the engine carries, and no transport  *)
(* recovers it.  The "smuggle the enriched promise through the bundle's own *)
(* [Rut] slot" route dies on a second, independent obstruction that is      *)
(* worth recording because it is NOT the one P2 found: [ukc] RE-BINDS [Rut] *)
(* universally, so whatever a leaf smuggles in does not come back out --    *)
(* the continuation receives a bundle at an arbitrary [Rut], and no fixed   *)
(* payload can be read off it.  The fix is upstream ask (4), the X-generic  *)
(* engine; with it this seal is [wp_uk_retire_later] at                     *)
(* [(uexec_ret_fs_F γm, uslot_fs γm)] -- one instantiation, no copy -- and  *)
(* this file's §2 becomes redundant with UkLeaf.v/UkBranch.v.               *)
(*                                                                         *)
(* WHAT IS *NOT* SEALED AND *NOT* HERE: the STORE funnel                    *)
(* ([UkStore.wp_uk_store_later]) is a second, independent driver over        *)
(* [UkStep.wp_uk_step], so a walk that re-walks main's PROLOGUE (the        *)
(* four [c.sdsp] spills) would cost a second seal.  The preamble slice      *)
(* starts at main's console arm (0xc), after the prologue, which is         *)
(* fs-inert; the cost of extending is recorded in the worklist, not paid    *)
(* here.                                                                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import WpGpr RegFile.
Require Import ExecCommon WpMmodeLeafBase WpMmodeShiftiop.
Require Import UserBits.
Require Import WpDecodeBridge DecodeTotalU.
Require Import HartMemRun UserFrame UserExecFacts.
Require UserTotalU.
Require Import UserPtTree UserExec.
Require Import WpUmodeStep WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UexecSlot.
Require Import UsysMemOk.
Require Import UserPerm UexecWp UexecRet UkStep.
Require Import UserHeap.
Require Import UkRun.
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.
(* ...UkLeaf.v / UkBranch.v / UkRunBr.v's blocks above; the pilot's own
   imports below. *)
Require Import FsFdMirror.   (* [umirror]/[mcur]/[ufs_step]/[uenr_dom] *)
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import UexecRetFs.   (* [uvb_fs]/[urun_fs]/[ustrq]/the engine seal *)
Require Import UkRunSys.     (* [ufd_auth_move] -- the untracked authority step *)
Require Import UkRunSysFs.   (* [ukc_fs]/[urun_fs_close]/[uvb_fs_x0]/P2's seal *)
Require Import UserFd.   (* [ufdG] -- MUST precede the first `{!ufdG Σ}:
                            an unbound name inside `{ } is auto-generalized
                            into a fresh opaque class instead. *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0 THE RETIRE FUNNEL'S THREE STATE-GUARDED PREMISES, FOLDED.           *)
(*                                                                        *)
(* [UkStep.wp_uk_retire_later] spells each of these out in full; folding   *)
(* them is what keeps the seal below readable and keeps this file from     *)
(* transcribing the same twelve lines six times.  They are DEFINITIONS,    *)
(* so every argument the plain leaves pass (the [fun s _ _ _ _ _ => …]     *)
(* lambdas, [uv_btype_cert], [goodmb_execute_*_total]) typechecks against  *)
(* them unchanged.                                                        *)
(* ===================================================================== *)

Definition uk_gmb_at (m : regfile) (pc : mword 64) (is_rvc : bool)
    (j : instruction) : Prop :=
  forall s_pc : mstate,
    register_lookup PC s_pc.(sregs) = pc ->
    register_lookup nextPC s_pc.(sregs)
      = add_vec_int pc (if is_rvc then 2 else 4) ->
    register_lookup cur_privilege s_pc.(sregs) = User ->
    agree_on D_u s_pc dstateU ->
    (forall r : mword 5,
       (if Z.eqb (uint r) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
       = m !!! Regidx r) ->
    goodmb Du_r Du_w (execute j) s_pc ∅ = true.

Definition uk_exec_at (m : regfile) (pc : mword 64) (is_rvc : bool)
    (j : instruction) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) : Prop :=
  forall s_pc : mstate,
    register_lookup PC s_pc.(sregs) = pc ->
    register_lookup nextPC s_pc.(sregs)
      = add_vec_int pc (if is_rvc then 2 else 4) ->
    register_lookup cur_privilege s_pc.(sregs) = User ->
    agree_on D_u s_pc dstateU ->
    (forall r : mword 5,
       (if Z.eqb (uint r) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
       = m !!! Regidx r) ->
    exec (execute j) s_pc = Some (RETIRE_SUCCESS, uv_post s_pc jt wr).

(* the plain funnel, in the folded spelling -- the compiled receipt that
   the folding is exactly [UkStep.wp_uk_retire_later]'s premise set and
   the seal below is that statement with two types swapped *)
Lemma wp_uk_retire_later_folded `{!riscvGS Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId}
    `{XI : CurCtx}
    (C : ucfg) (pt : uptd)
    (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
    (π : gmap (mword 27) uperm) (sz : Z) (fdv : list fdstate) (cw : Z) :
  loop_ok C pt ->
  perm_of (ud_um pt) sz = π ->
  (forall pt' : uptd,
     ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                  (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')) ->
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
  uvb (CID := CID) C pt Rfd Rut sz π fdv cw M m pc -∗
  ▷ ukc π M sz fdv cw (uv_upd m wr)
      (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros Hlo Hpm HRut M m pc is_rvc i o jt wr Hui Hred Hlpad Hwrok Hg1 Hg2 Hex.
  exact (wp_uk_retire_later C pt Rfd Rut π sz Hlo Hpm HRut M m pc fdv cw is_rvc i o jt wr
           Hui Hred Hlpad Hwrok Hg1 Hg2 Hex).
Qed.

(* ===================================================================== *)
(* §1 THE SEAL: the retire funnel at the enriched bundle.                 *)
(* ===================================================================== *)
Module Type FDROW_UKFS_RETIRE.
  Parameter wp_uk_retire_fs_later :
    forall `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
           `{!ghost_varG Σ Z} `{!ghost_varG Σ umirror}
      (γm : gname) (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z) (fdv : list fdstate) (cw : Z),
      loop_ok C pt ->
      perm_of (ud_um pt) sz = π ->
      (* A6.140: the loop borrows the running token out of [Rut pt] per step *)
      (forall pt' : uptd,
         ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                      (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')) ->
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
      uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
      ▷ ukc_fs γm π M sz fdv cw (uv_upd m wr)
          (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
      WP (Loop : expr riscv_lang).
End FDROW_UKFS_RETIRE.

(* ===================================================================== *)
(* THE TWO [Local] EXEC FACTS THE JUMP LEAVES NEED.                       *)
(*                                                                        *)
(* Verbatim copies of UkLeaf.v's [Local Lemma]s of the same names (which   *)
(* are themselves copies of WpSmodePtCtl.v's).  They are [Local] there, so *)
(* a PARALLEL leaf tower cannot reach them -- which is the second half of  *)
(* upstream ask (4)'s cost and is recorded as such: hoisting the           *)
(* operand-generic forms beside [exec_execute_JAL_gpr] in                  *)
(* WpMmodeLeafBase.v would delete these copies AND UkLeaf.v's.             *)
(* ===================================================================== *)
Local Lemma exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  match goal with |- context[Defs.bind0 ?wx _] =>
    assert (Hwx : exec wx (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  = Some (tt, set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                                (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (register_lookup nextPC s.(sregs)))))
  end.
  { rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs)) _).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

Local Lemma exec_execute_JAL_zreg_zca (imm : mword 21) s :
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm zreg) s
  = Some (RETIRE_SUCCESS,
          set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
Proof.
  intros Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  unfold zreg.
  rewrite (exec_bind0_Some _ _ _ _ _
    (exec_wX_bits_gpr (zero_extend' 5 ('b"00")) (register_lookup nextPC s.(sregs))
       (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))))).
  apply exec_returnm.
Qed.

(* ===================================================================== *)
(* THE LEAF TOWER, over the two seals.                                    *)
(* ===================================================================== *)
Module FdRowUkfsLeaf (R : FDROW_UKFS_RETIRE) (S : FDROW_UKFS_STEP).

(* --------------------------------------------------------------------- *)
(* §2 THE [uvb_fs]-LEVEL LEAVES: UkLeaf.v / UkBranch.v's, at the enriched  *)
(* bundle.  Each proof is its plain twin's, with [wp_uk_retire[_later]]    *)
(* replaced by the sealed enriched funnel; no other line differs.          *)
(* --------------------------------------------------------------------- *)
Section UkLeafFs.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.
  Context (γm : gname) (C : ucfg) (pt : uptd)
          (* [Rfd] beside [Rut], [fdv] beside [sz] -- section variables
             generalize per-lemma, so this is the same as binding them on
             each leaf, which is what [UkLeaf] does *)
          (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z) (fdv : list fdstate) (cw : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  (* the residue's TOKEN ACCESSOR (A6.140 / r12's [uk_ih] shape): every leaf
     borrows the running token out of [Rut] for its step and puts it back,
     and the callers below already pass it in this position *)
  Hypothesis (HRut : forall pt' : uptd,
                ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                             (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')).

  (* the later-FREE funnel, off the sealed one -- [wp_uk_retire]'s own
     derivation from [wp_uk_retire_later] *)
  Lemma wp_uk_retire_fs (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64)
      (is_rvc : bool) (i : instruction) (o : option instruction)
      (jt : option (mword 64)) (wr : option (mword 5 * mword 64)) :
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_wrok wr ->
    uk_gmb_at m pc is_rvc i ->
    uk_gmb_at m pc is_rvc (uv_exp i o) ->
    uk_exec_at m pc is_rvc (uv_exp i o) jt wr ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw (uv_upd m wr)
      (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hwrok Hg1 Hg2 Hex.
    iIntros "Hb Hcont".
    iApply (R.wp_uk_retire_fs_later γm C pt Rfd Rut π sz fdv cw Hlo Hpm HRut M m pc is_rvc
              i o jt wr Hui Hred Hlpad Hwrok Hg1 Hg2 Hex with "Hb [Hcont]").
    iNext. iExact "Hcont".
  Qed.

  (* ---- the two gpr-write families the slice uses ---------------------- *)

  Lemma wp_uk_alu0_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (o : option instruction) (rd : mword 5) (wval : mword 64) :
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uint rd <> 0 ->
    (forall s : mstate, goodmb Du_r Du_w (execute i) s ∅ = true) ->
    (forall s : mstate, goodmb Du_r Du_w (execute (uv_exp i o)) s ∅ = true) ->
    (forall s : mstate,
       register_lookup PC s.(sregs) = pc ->
       exec (execute (uv_exp i o)) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg wval))) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw (<[Regidx rd := regval_into_reg wval]> m)
      (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hrd Hg1 Hg2 Hop.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_fs M m pc is_rvc i o None (Some (rd, wval))
              Hui Hred Hlpad Hrd
              (fun s _ _ _ _ _ => Hg1 s) (fun s _ _ _ _ _ => Hg2 s)
              with "Hb Hcont").
    intros s_pc Lpc _ _ _ _.
    cbn [uv_post uv_jmp WpUmodeStep.uv_wr].
    rewrite (Hop s_pc Lpc).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
  Qed.

  Lemma wp_uk_alu1_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (o : option instruction) (rs1 rd : mword 5)
      (vf : mword 64 -> mword 64) (wval : mword 64) :
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uint rd <> 0 ->
    (forall s : mstate, goodmb Du_r Du_w (execute i) s ∅ = true) ->
    (forall s : mstate, goodmb Du_r Du_w (execute (uv_exp i o)) s ∅ = true) ->
    (forall s : mstate,
       exec (execute (uv_exp i o)) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (vf (gpr_src rs1 s))))) ->
    wval = vf (m !!! Regidx rs1) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw (<[Regidx rd := regval_into_reg wval]> m)
      (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hrd Hg1 Hg2 Hop Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_fs M m pc is_rvc i o None (Some (rd, wval))
              Hui Hred Hlpad Hrd
              (fun s _ _ _ _ _ => Hg1 s) (fun s _ _ _ _ _ => Hg2 s)
              with "Hb Hcont").
    intros s_pc _ _ _ _ Hvals.
    cbn [uv_post uv_jmp WpUmodeStep.uv_wr].
    rewrite (Hop s_pc).
    unfold gpr_src. rewrite (Hvals rs1).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hwval. reflexivity.
  Qed.

  (* ---- c.li ----------------------------------------------------------- *)
  Lemma wp_uk_cli_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uk_instr π M pc true (C_LI (imm, Regidx rd)) ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw (<[Regidx rd := regval_into_reg wval]> m)
      (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_fs M m pc true (C_LI (imm, Regidx rd))
              (Some (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)))
              None (Some (rd, wval)) Hui
              ltac:(intro s; apply exec_execute_C_LI)
              eq_refl Hrd
              (fun s _ _ _ _ _ => UserTotalU.goodmb_execute_C_LI Du_r Du_w imm (Regidx rd) s)
              (fun s _ _ _ _ _ => goodmb_execute_ITYPE_total Du_r Du_w
                          (sign_extend' 12 imm) (zero_extend' 5 ('b"00")) rd ADDI s
                          (Du_gpr_of_Z_r (zero_extend' 5 ('b"00"))) (Du_gpr_of_Z rd))
              with "Hb Hcont").
    intros s_pc _ _ _ _ _.
    cbn [uv_exp uv_post uv_jmp WpUmodeStep.uv_wr].
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd
               (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    rewrite Hwval. reflexivity.
  Qed.

  (* ---- addi / auipc --------------------------------------------------- *)
  Lemma wp_uk_addi_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uk_instr π M pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw (<[Regidx rd := regval_into_reg wval]> m)
      (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    assert (Hg : forall s : mstate,
              goodmb Du_r Du_w (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)))
                s ∅ = true)
      by (intro s; exact (goodmb_execute_ITYPE_total Du_r Du_w imm rs1 rd ADDI s
                            (Du_gpr_of_Z_r rs1) (Du_gpr_of_Z rd))).
    exact (wp_uk_alu1_fs M m pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
             None rs1 rd (fun a => add_vec a (sign_extend' 64 imm)) wval Hui
             (fun _ : mstate => I) eq_refl Hrd Hg Hg
             (fun s => exec_execute_ITYPE_ADDI_gpr rs1 rd imm s) Hwval).
  Qed.

  Lemma wp_uk_auipc_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 20) (rd : mword 5) (wval : mword 64) :
    uk_instr π M pc false (UTYPE (imm, Regidx rd, AUIPC)) ->
    uint rd <> 0 ->
    wval = add_vec pc (auipc_off imm) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw (<[Regidx rd := regval_into_reg wval]> m)
      (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    assert (Hg : forall s : mstate,
              goodmb Du_r Du_w (execute (UTYPE (imm, Regidx rd, AUIPC))) s ∅ = true)
      by (intro s; exact (goodmb_execute_UTYPE_total Du_r Du_w imm rd AUIPC s
                            UserTotalU.Du_r_PC (Du_gpr_of_Z rd))).
    apply (wp_uk_alu0_fs M m pc false (UTYPE (imm, Regidx rd, AUIPC)) None rd wval
             Hui (fun _ : mstate => I) eq_refl Hrd Hg Hg).
    intros s Lpc. rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s).
    rewrite Lpc. rewrite Hwval. reflexivity.
  Qed.

  (* ---- the three jumps ------------------------------------------------ *)
  Lemma wp_uk_jal_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 21) (rd : mword 5) (tgt wval : mword 64) :
    uk_instr π M pc false (JAL (imm, Regidx rd)) ->
    uint rd <> 0 ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    wval = add_vec_int pc 4 ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw (<[Regidx rd := regval_into_reg wval]> m) tgt -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Htgt Hwval Hal0.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_fs M m pc false (JAL (imm, Regidx rd)) None
              (Some tgt) (Some (rd, wval)) Hui
              ltac:(intro s; exact I)
              eq_refl Hrd
              ltac:(intros s Lpc _ _ Hag _;
                    exact (goodmb_execute_JAL_total Du_r Du_w imm rd s
                             UserTotalU.Du_r_nPC UserTotalU.Du_r_PC
                             UserTotalU.Du_w_nPC (Du_gpr_of_Z rd)
                             (UserTotalU.u_gm_zca s Hag) (agree_u_zca s Hag)
                             ltac:(rewrite Lpc; rewrite <- Htgt; exact Hal0)))
              ltac:(intros s Lpc _ _ Hag _;
                    exact (goodmb_execute_JAL_total Du_r Du_w imm rd s
                             UserTotalU.Du_r_nPC UserTotalU.Du_r_PC
                             UserTotalU.Du_w_nPC (Du_gpr_of_Z rd)
                             (UserTotalU.u_gm_zca s Hag) (agree_u_zca s Hag)
                             ltac:(rewrite Lpc; rewrite <- Htgt; exact Hal0)))
              with "Hb Hcont").
    intros s_pc Lpc Lnpc _ Hag _.
    cbn [uv_exp uv_post uv_jmp WpUmodeStep.uv_wr].
    change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
    rewrite (exec_execute_JAL_gpr_zca imm rd s_pc Hrd
               ltac:(rewrite Lpc; rewrite <- Htgt; exact Hal0)
               (agree_u_zca s_pc Hag)).
    rewrite Lpc Lnpc. rewrite <- Htgt. rewrite Hwval. reflexivity.
  Qed.

  Lemma wp_uk_cjr_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 : mword 5) (tgt : mword 64) :
    uk_instr π M pc true (C_JR (Regidx rs1)) ->
    uint rs1 <> 0 ->
    tgt = ret_pc (m !!! Regidx rs1) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw m tgt -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrs1 Htgt.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_fs M m pc true (C_JR (Regidx rs1))
              (Some (JALR (zeros' 12, Regidx rs1, zreg)))
              (Some tgt) None Hui
              ltac:(intro s; apply exec_execute_C_JR)
              eq_refl I
              (fun s _ _ _ _ _ =>
                 UserTotalU.goodmb_execute_C_JR Du_r Du_w (Regidx rs1) s)
              ltac:(intros s _ _ _ Hag _;
                    exact (goodmb_execute_JALR_total Du_r Du_w (zeros' 12) rs1
                             (zero_extend' 5 ('b"00")) s
                             UserTotalU.Du_r_nPC UserTotalU.Du_w_nPC
                             (Du_gpr_of_Z_r rs1)
                             (Du_gpr_of_Z (zero_extend' 5 ('b"00")))
                             (UserTotalU.u_gm_zicfilp s Hag) (agree_u_zicfilp s Hag)
                             (UserTotalU.u_gm_zca s Hag) (agree_u_zca s Hag)))
              with "Hb Hcont").
    intros s_pc _ _ _ Hag Hvals.
    cbn [uv_exp uv_post uv_jmp WpUmodeStep.uv_wr uv_upd].
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = m !!! Regidx rs1).
    { pose proof (Hvals rs1) as Hv.
      replace (Z.eqb (uint rs1) 0) with false in Hv
        by (symmetry; apply Z.eqb_neq; exact Hrs1).
      exact Hv. }
    change (execute (JALR (zeros' 12, Regidx rs1, zreg)))
      with (execute_JALR (zeros' 12) (Regidx rs1) zreg).
    change zreg with (Regidx cli_rs1).
    rewrite (exec_execute_JALR_ret_zca (zeros' 12) rs1 cli_rs1 s_pc Hrs1
               ltac:(vm_compute; reflexivity)
               (agree_u_zicfilp s_pc Hag) (agree_u_zca s_pc Hag)
               ltac:(apply bit0_update0_64)).
    rewrite Hrsv. rewrite ret_pc_jalr. rewrite Htgt. reflexivity.
  Qed.

  Lemma wp_uk_cj_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 11) (tgt : mword 64) :
    uk_instr π M pc true (C_J imm) ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0")))) ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw m tgt -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htgt Hal0.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_fs M m pc true (C_J imm)
              (Some (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)))
              (Some tgt) None Hui
              ltac:(intro s; apply exec_execute_C_J)
              eq_refl I
              (fun s _ _ _ _ _ => UserTotalU.goodmb_execute_C_J_U Du_r Du_w imm s)
              ltac:(intros s Lpc _ _ Hag _;
                    exact (goodmb_execute_JAL_total Du_r Du_w
                             (sign_extend' 21 (concat_vec imm ('b"0")))
                             (zero_extend' 5 ('b"00")) s
                             UserTotalU.Du_r_nPC UserTotalU.Du_r_PC
                             UserTotalU.Du_w_nPC
                             (Du_gpr_of_Z (zero_extend' 5 ('b"00")))
                             (UserTotalU.u_gm_zca s Hag) (agree_u_zca s Hag)
                             ltac:(rewrite Lpc; rewrite <- Htgt; exact Hal0)))
              with "Hb Hcont").
    intros s_pc Lpc _ _ Hag _.
    cbn [uv_exp uv_post uv_jmp WpUmodeStep.uv_wr uv_upd].
    change (execute (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)))
      with (execute_JAL (sign_extend' 21 (concat_vec imm ('b"0"))) zreg).
    rewrite (exec_execute_JAL_zreg_zca (sign_extend' 21 (concat_vec imm ('b"0"))) s_pc
               ltac:(rewrite Lpc; rewrite <- Htgt; exact Hal0)
               (agree_u_zca s_pc Hag)).
    rewrite Lpc. rewrite <- Htgt. reflexivity.
  Qed.

  (* ---- the conditional branch against x0 ------------------------------ *)
  Local Lemma uk_next_bool_fs (b : bool) (t d : mword 64) :
    uv_next (if b then Some t else None) d = (if b then t else d).
  Proof. destruct b; reflexivity. Qed.

  Lemma wp_uk_btype_gen_fs_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (o : option instruction) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uk_gmb_at m pc is_rvc i ->
    uv_exp i o = BTYPE (imm, Regidx rs2, Regidx rs1, op) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ▷ ukc_fs γm π M sz fdv cw m
        (if taken then tgt else add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hg1 Hexp Htaken Htgt Halign.
    iIntros "Hb Hcont".
    iAssert (▷ ukc_fs γm π M sz fdv cw (uv_upd m None)
               (uv_next (if taken then Some tgt else None)
                  (add_vec_int pc (if is_rvc then 2 else 4))))%I
      with "[Hcont]" as "Hcont".
    { iNext. rewrite uk_next_bool_fs. iExact "Hcont". }
    iApply (R.wp_uk_retire_fs_later γm C pt Rfd Rut π sz fdv cw Hlo Hpm HRut M m pc is_rvc i o
              (if taken then Some tgt else None) None
              Hui Hred Hlpad I Hg1
              ltac:(intros s_pc Lpc Lnpc Lcp Hag Hvals;
                    rewrite Hexp;
                    exact (uv_btype_cert M m pc is_rvc imm rs2 rs1 op taken tgt
                             Htaken Htgt Halign s_pc Lpc Lnpc Lcp Hag Hvals))
              with "Hb Hcont").
    intros s_pc Lpc _ _ Hag Hvals.
    rewrite Hexp.
    rewrite (exec_execute_BTYPE_gpr_zca imm rs2 rs1 op
               (m !!! Regidx rs1) (m !!! Regidx rs2) taken s_pc
               (Hvals rs1) (Hvals rs2) Htaken
               ltac:(intro Ht; rewrite Lpc; rewrite <- Htgt; exact (Halign Ht))
               (agree_u_zca s_pc Hag)).
    rewrite Lpc. rewrite <- Htgt. reflexivity.
  Qed.

  Lemma wp_uk_btype_fs_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ▷ ukc_fs γm π M sz fdv cw m (if taken then tgt else add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    exact (wp_uk_btype_gen_fs_later M m pc false
             (BTYPE (imm, Regidx rs2, Regidx rs1, op)) None
             imm rs2 rs1 op taken tgt
             Hui (fun _ => I) eq_refl
             (uv_btype_cert M m pc false imm rs2 rs1 op taken tgt
                Htaken Htgt Halign)
             eq_refl Htaken Htgt Halign).
  Qed.

  Lemma wp_uk_btype0_fs (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc false
      (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb_fs (CID := CID) γm C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc_fs γm π M sz fdv cw m (if taken then tgt else add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    iIntros "Hb Hcont".
    iDestruct (uvb_fs_x0 with "Hb") as "[%Hz Hb]".
    iApply (wp_uk_btype_fs_later M m pc imm (mword_of_int 0 : mword 5) rs1 op
              taken tgt Hui ltac:(rewrite Hz; exact Htaken) Htgt Halign
              with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

End UkLeafFs.

(* --------------------------------------------------------------------- *)
(* §3 THE [urun_fs]-LEVEL LEAVES: UkRunLeaf.v / UkRunBr.v's six-line       *)
(* re-thread, at the enriched running predicate.  Open [urun_fs], read the *)
(* instruction fact off the heap, apply the [uvb_fs] leaf, close with      *)
(* [UkRunSysFs.urun_fs_close(_upd)].                                       *)
(* --------------------------------------------------------------------- *)
Section UkRunFsLeaf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.

  Lemma wp_uk_cli_run_fs (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (rd : mword 5) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LI (imm, Regidx rd)) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun_fs γm γt γd γs γfd h'
         (<[Regidx rd := regval_into_reg (sign_extend' 64 imm : mword 64)]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Hrd. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (wp_uk_cli_fs γm C pt Rfd Rut pm sz fdv cw Hlo Hpm HRut M m pc imm rd
              (sign_extend' 64 imm) Hui Hrd (eq_sym (uimm6_norm imm))
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_fs_close_upd γm γt γd γs γfd M pm m rd _ sz fdv cw (add_vec_int pc 2)
              avail Hns with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_addi_run_fs (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64)
      (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun_fs γm γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Hrd Hwval. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (wp_uk_addi_fs γm C pt Rfd Rut pm sz fdv cw Hlo Hpm HRut M m pc imm rs1 rd wval
              Hui Hrd Hwval with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_fs_close_upd γm γt γd γs γfd M pm m rd _ sz fdv cw (add_vec_int pc 4)
              avail Hns with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_auipc_run_fs (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 20) (rd : mword 5) (wval : mword 64)
      (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec pc (auipc_off imm) ->
    uinstr_is γt pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun_fs γm γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Hrd Hwval. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (wp_uk_auipc_fs γm C pt Rfd Rut pm sz fdv cw Hlo Hpm HRut M m pc imm rd wval
              Hui Hrd Hwval with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_fs_close_upd γm γt γd γs γfd M pm m rd _ sz fdv cw (add_vec_int pc 4)
              avail Hns with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_jal_run_fs (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 21) (rd : mword 5) (tgt wval : mword 64)
      (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    wval = add_vec_int pc 4 ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is γt pc false (JAL (imm, Regidx rd)) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun_fs γm γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Hrd H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (wp_uk_jal_fs γm C pt Rfd Rut pm sz fdv cw Hlo Hpm HRut M m pc imm rd tgt wval
              Hui Hrd H2 H3 H4 with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_fs_close_upd γm γt γd γs γfd M pm m rd _ sz fdv cw tgt avail Hns
              with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_cjr_run_fs (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (rs1 : mword 5) (tgt : mword 64) (avail : nat) :
    uint rs1 <> 0 ->
    tgt = ret_pc (m !!! Regidx rs1) ->
    uinstr_is γt pc true (C_JR (Regidx rs1)) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun_fs γm γt γd γs γfd h' m tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (wp_uk_cjr_fs γm C pt Rfd Rut pm sz fdv cw Hlo Hpm HRut M m pc rs1 tgt Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_fs_close γm γt γd γs γfd M pm sz fdv cw m tgt avail
              with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_cj_run_fs (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 11) (tgt : mword 64) (avail : nat) :
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0")))) ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is γt pc true (C_J imm) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun_fs γm γt γd γs γfd h' m tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (wp_uk_cj_fs γm C pt Rfd Rut pm sz fdv cw Hlo Hpm HRut M m pc imm tgt Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_fs_close γm γt γd γs γfd M pm sz fdv cw m tgt avail
              with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_btype0_run_fs (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) (avail : nat) :
    taken = uv_btaken op (m !!! Regidx rs1) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc false
      (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, op)) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun_fs γm γt γd γs γfd h' m
         (if taken then tgt else add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (wp_uk_btype0_fs γm C pt Rfd Rut pm sz fdv cw Hlo Hpm HRut M m pc imm rs1 op
              taken tgt Hui H1 H2 H3 with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_fs_close γm γt γd γs γfd M pm sz fdv cw m
              (if taken then tgt else add_vec_int pc 4) avail
              with "Hheap Hstk Hufd Hcont").
  Qed.

  (* =================================================================== *)
  (* §4 THE STRING IN READ-ONLY TEXT, and the two enriched ecall leaves.  *)
  (*                                                                      *)
  (* P2's leaf pins the fetched path with [UexecRetFs.ustrq], a run of     *)
  (* WRITABLE data bytes.  init's "console" is not that: it sits in the    *)
  (* program's READ-ONLY image, whose bytes live on the text half          *)
  (* ([UserHeap.utext] / [utext_str]) -- so asking a walk for a [ustrq]    *)
  (* there would be an UNSATISFIABLE premise at the state init actually    *)
  (* runs in (durable-notes: a premise set can be unsatisfiable and still  *)
  (* compile).  [ustrt] is the same resource on the text half, and         *)
  (* [uheap_ustrt] is [uheap_ustrq]'s twin through [uheap_text].  It is    *)
  (* PERSISTENT, so the leaf need not hand it back.                        *)
  (* =================================================================== *)
  Definition ustrt (γt : gname) (a : Z) (pl : list (bv 8)) : iProp Σ :=
    (⌜Forall (fun b : bv 8 => b <> unul) pl⌝ ∗
     ⌜(length pl < UMAXPATH)%nat⌝ ∗
     utext_str γt a (length pl) (ustr_bytes pl))%I.

  Global Instance ustrt_persistent γt a pl : Persistent (ustrt γt a pl).
  Proof. apply _. Qed.

  (* [UexecRetFs.uheap_ubytes_pts] on the TEXT half, and by the same
     induction: the authority names each of a persistent run's bytes *)
  Local Lemma uheap_utext_pts (γt γd γs : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (a : Z) (nb : nat) (f : nat -> bv 8) :
    uheap γt γd γs M pmv -∗
    ([∗ list] j ∈ seq 0 nb, utext γt (a + Z.of_nat j) (f j)) -∗
    ⌜ forall j : nat, (j < nb)%nat -> M !! (a + Z.of_nat j)%Z = Some (f j) ⌝.
  Proof.
    iInduction nb as [| kb IH] "IH"; iIntros "Hheap Hbs".
    { iPureIntro. intros j Hj. exfalso. lia. }
    iEval (rewrite seq_S big_sepL_app /=) in "Hbs".
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    iDestruct ("IH" with "Hheap Hlo") as %Hk.
    iDestruct (uheap_text with "Hheap Hhi") as %(HM & _ & _).
    iPureIntro. intros j Hj.
    destruct (decide (j = kb)) as [-> | Hne]; [ exact HM | ].
    apply Hk. lia.
  Qed.

  Lemma uheap_ustrt (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (a : Z) (pl : list (bv 8)) :
    uheap γt γd γs M pm -∗ ustrt γt a pl -∗ ⌜ustr_read M a = Some pl⌝.
  Proof.
    iIntros "Hheap (%Hall & %Hlen & (_ & _ & Hbody & Hnul))".
    iDestruct (uheap_utext_pts γt γd γs M pm a (length pl) (ustr_bytes pl)
                 with "Hheap Hbody") as %Hbody.
    iDestruct (uheap_text with "Hheap Hnul") as %(HMn & _ & _).
    iPureIntro. apply ustr_read_of; [ exact Hlen | exact Hall | ].
    intros j Hj.
    destruct (decide (j < length pl)%nat) as [Hlt | Hge].
    - exact (Hbody j Hlt).
    - assert (Hje : j = length pl) by lia. subst j.
      assert (Hnth : ustr_bytes pl (length pl) = ubyte0).
      { unfold ustr_bytes. rewrite nth_overflow; [ | lia ].
        apply bv_eq. vm_compute. reflexivity. }
      rewrite Hnth. exact HMn.
  Qed.

  (* ---- THE PATH-ROW LEAF, at a text string.  P2's
     [wp_uk_ecall_fs_of_step] with [ustrq]/[uheap_ustrq] replaced by
     [ustrt]/[uheap_ustrt]; nothing else moves. ---- *)
  Lemma wp_uk_ecall_fs_text (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (n : Z) (u : umirror) (pl : list (bv 8)) (avail : nat) :
    usys_num (tf_of m pc) = n ->
    uenr_dom n = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    mcur γm u -∗
    ustrt γt (uint (m !!! Regidx (mword_of_int 10))) pl -∗
    (∀ (h' : CpuId) (r : mword 64) (u' : umirror),
       ⌜ufs_step_at n pl (tf_of m pc) r u u'⌝ -∗
       mcur γm u' -∗
       urun_fs γm γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hdom Hal4.
    iIntros "#Hi Hrun Hmc #Hstr Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw)
      "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_fs_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct (uheap_ustrt with "Hheap Hstr") as %Hread.
    assert (Hread0 : ustr_read M (uint (ufs_arg (tf_of m pc) 0)) = Some pl)
      by exact Hread.
    iApply (S.wp_uk_ecall_fs_step γm h C pt Rfd Rut pm sz M fdv cw m pc Hlo Hpm HRut Hui
              with "Hb").
    rewrite /uexec_ret_fs /uexec_ret_fs_F.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hc];
      [| exfalso; exact (Hc eq_refl) ].
    cbv zeta.
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw)) = n).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum.
    destruct (uenr_dom_rows n Hdom)
      as (Hexit & Hfork & Hexec & Hsbrk & Hwait & Hpipe & Hrd & Hfst).
    destruct (decide (n = USYS_exit)) as [He | _];
      [ exfalso; exact (Hexit He) |].
    destruct (decide (n = USYS_fork)) as [He | _];
      [ exfalso; exact (Hfork He) |].
    rewrite Hdom.
    iRight. iExists u. iFrame "Hmc".
    iIntros (r M' pm' sz' fdv' cw' u') "%Hok %Hfdok %Hpiperow %Hcwrow %Hstep Hmc".
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _
                Hexec Hsbrk Hwait Hpipe Hrd Hfst Hok) as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_sz uvis_of_run].
    (* the enriched rows include open and dup, so the table may have moved;
       the program is not tracking these descriptors, so the authority moves
       and no handle comes back ([UkRunSys.ufd_state_move]) *)
    iApply uslot_fs_bupd.
    iMod (ufd_state_move γfd n (tf_of m pc) r fdv fdv'
            (uenr_dom_ne_close n Hdom) Hfdok with "Hufd") as "Hufd".
    iModIntro.
    rewrite (uslot_fs_bump_run γm m pc M M pm pm sz sz fdv fdv' cw cw' r Hx0 Hal4).
    iApply (urun_fs_close_upd γm γt γd γs γfd M pm m (mword_of_int 10) r sz fdv' cw'
              (add_vec_int pc 4) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r u' with "[%] Hmc Hrun").
    cbn [uvis_tf uvis_M uvis_of_run] in Hstep.
    exact (ufs_step_pin n (tf_of m pc) M r u u' pl Hdom Hread0 Hstep).
  Qed.

  (* ---- THE NON-PATH ROW LEAF (dup).  Argument 0 is a descriptor
     NUMBER, so there is no string to own and none to pin: the row is
     [ufs_step_at n []] straight off [ufs_step_np]. ---- *)
  Lemma wp_uk_ecall_fs_nopath (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (n : Z) (u : umirror) (avail : nat) :
    usys_num (tf_of m pc) = n ->
    uenr_dom n = true ->
    uenr_path n = false ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun_fs γm γt γd γs γfd h m pc avail -∗
    mcur γm u -∗
    (∀ (h' : CpuId) (r : mword 64) (u' : umirror),
       ⌜ufs_step_at n [] (tf_of m pc) r u u'⌝ -∗
       mcur γm u' -∗
       urun_fs γm γt γd γs γfd h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hdom Hnp Hal4.
    iIntros "#Hi Hrun Hmc Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv cw)
      "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_fs_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (S.wp_uk_ecall_fs_step γm h C pt Rfd Rut pm sz M fdv cw m pc Hlo Hpm HRut Hui
              with "Hb").
    rewrite /uexec_ret_fs /uexec_ret_fs_F.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hc];
      [| exfalso; exact (Hc eq_refl) ].
    cbv zeta.
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw)) = n).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum.
    destruct (uenr_dom_rows n Hdom)
      as (Hexit & Hfork & Hexec & Hsbrk & Hwait & Hpipe & Hrd & Hfst).
    destruct (decide (n = USYS_exit)) as [He | _];
      [ exfalso; exact (Hexit He) |].
    destruct (decide (n = USYS_fork)) as [He | _];
      [ exfalso; exact (Hfork He) |].
    rewrite Hdom.
    iRight. iExists u. iFrame "Hmc".
    iIntros (r M' pm' sz' fdv' cw' u') "%Hok %Hfdok %Hpiperow %Hcwrow %Hstep Hmc".
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _
                Hexec Hsbrk Hwait Hpipe Hrd Hfst Hok) as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_sz uvis_of_run].
    (* the enriched rows include open and dup, so the table may have moved;
       the program is not tracking these descriptors, so the authority moves
       and no handle comes back ([UkRunSys.ufd_state_move]) *)
    iApply uslot_fs_bupd.
    iMod (ufd_state_move γfd n (tf_of m pc) r fdv fdv'
            (uenr_dom_ne_close n Hdom) Hfdok with "Hufd") as "Hufd".
    iModIntro.
    rewrite (uslot_fs_bump_run γm m pc M M pm pm sz sz fdv fdv' cw cw' r Hx0 Hal4).
    iApply (urun_fs_close_upd γm γt γd γs γfd M pm m (mword_of_int 10) r sz fdv' cw'
              (add_vec_int pc 4) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r u' with "[%] Hmc Hrun").
    cbn [uvis_tf uvis_M uvis_of_run] in Hstep.
    exact (ufs_step_np n (tf_of m pc) M r u u' [] Hnp Hstep).
  Qed.

End UkRunFsLeaf.
End FdRowUkfsLeaf.
