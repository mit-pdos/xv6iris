(* ===================================================================== *)
(* UkRunSysFs.v -- THE ENRICHED ECALL LEAF (fd-row pilot, prover stage    *)
(* P2): [UkRunSys.wp_uk_ecall_quiet]'s twin on [UexecRetFs.urun_fs], with  *)
(* the caller's mirror half DEPOSITED into the trap and handed back        *)
(* STEPPED by the row's pure relation.                                     *)
(*                                                                         *)
(* Design of record: claude-notes/design/fd-row-pilot.md; the prover plan   *)
(* is the "## FD-ROW PILOT" section of                                     *)
(* claude-notes/projects/fs-syscall-specs.md.                              *)
(*                                                                         *)
(* WHAT IS PROVEN HERE (all of the pilot's own leaf content):              *)
(*   [uvb_fs_x0]            -- x0 is pinned inside the enriched bundle;    *)
(*   [ukc_fs] / [uslot_fs_ukc] / [uslot_fs_bump_run]                       *)
(*                          -- the enriched continuation at a natural      *)
(*                             state, and the enriched slot at the BUMPED  *)
(*                             trap-out key (UexecRet's [ukc] /            *)
(*                             [uslot_bump_run] at [uslot_fs]);            *)
(*   [urun_fs_close] / [urun_fs_close_upd]                                 *)
(*                          -- the re-close (UkRun's, at [urun_fs]);       *)
(*   [uenr_dom_rows]        -- the enriched numbers are QUIET rows and are  *)
(*                             neither exit nor fork, so the arm's own      *)
(*                             case analysis lands on the enriched branch   *)
(*                             and [usys_mem_ok] pins the image;            *)
(*   [ufs_step_at_blanket] / [ufs_step_pin]                                *)
(*                          -- the row read at the CALLER'S string: owning  *)
(*                             [ustrq] turns the contract's [ufs_step]      *)
(*                             (which reads the path off the image) into    *)
(*                             the leaf's [ufs_step_at] at the pinned [pl]; *)
(*   [wp_uk_ecall_fs_of_step] -- THE LEAF: open [urun_fs], pin the path,    *)
(*                             take the arm's RIGHT (deposit) disjunct with *)
(*                             the caller's [mcur], read the quiet row,     *)
(*                             re-close at the bumped key.  This is the     *)
(*                             whole of [FDROW_UKFS_ENGINE.wp_uk_ecall_fs]  *)
(*                             except the machine step itself.              *)
(*                                                                         *)
(* WHAT REMAINS SEALED, AND WHY IT IS A STRICTLY SMALLER SEAL.             *)
(* [FDROW_UKFS_STEP.wp_uk_ecall_fs_step] is [UkStep.wp_uk_ecall] with       *)
(* [uvb] replaced by [uvb_fs] and [uexec_ret] by [uexec_ret_fs] -- two type *)
(* substitutions, ZERO fs content, and the discharge of                     *)
(* [FDROW_UKFS_ENGINE] from it is the functor at the bottom of this file.   *)
(*                                                                         *)
(* IT CANNOT BE DERIVED FROM [UkStep.wp_uk_ecall], AND THE OBSTRUCTION IS   *)
(* EXACT, not a budget question.  [UkStep.wp_uk_ecall] takes the PLAIN      *)
(* return [uexec_ret uecall_scause (uvis_of_run m pc M pi sz fdv)] as an        *)
(* argument.  Whatever the enriched bundle is transported to (the plain     *)
(* engine can be fed a [uvb] built from [uvb_fs] -- e.g. with the enriched  *)
(* promise smuggled through the bundle's own [Rut] slot, so that the        *)
(* trap-out closure applies [ukb_fs] with the enriched return and DISCARDS  *)
(* the plain one), that plain argument must still be INHABITED, and its     *)
(* ecall arm is [∀ r M' pi' szv', ⌜usys_mem_ok …⌝ -∗ uslot (bump …)]:      *)
(* "the process is PLAIN-safe after the syscall, at every return value".    *)
(* The pilot's caller is enriched-safe only -- its continuation consumes    *)
(* [urun_fs], and [urun_fs] cannot be rebuilt from the plain [uvb] a plain  *)
(* slot receives ([ukont] ⊬ [ukont_fs]: that is [uslot_fs ⊬ uslot], the     *)
(* direction the design's finding 1 already refutes).  Nor can the          *)
(* enrichment ride any other channel into the trap-out: [UkStep]'s          *)
(* [uk_step_obl] re-binds C / pt / Rut universally, so a fixed [ukb_fs] at  *)
(* one (C, pt, Rut) cannot travel in [Kc]; the bundle's own promise slot is *)
(* [ukb]-typed; and the [Rut] slot -- the one channel that IS re-bound with *)
(* the bundle -- is LATER-FREE in [uvb_F] while the enriched promise is     *)
(* [ukont_fs = ▷ ukb_fs], and no step between the bundle and the trap-out  *)
(* strips a later from inside the opaque payload.  The engine is therefore  *)
(* the ONE place the pilot cannot reuse, and the fix is a diff-shaped ask,  *)
(* filed in the                                                             *)
(* worklist: parameterise UkStep's sections 3/5/8 over the slot family      *)
(* (X, RetF) with the two facts they actually use -- X's fixpoint           *)
(* unfolding and RetF's transparency off the ecall cause.  Both hold for    *)
(* [uslot] / [uexec_ret_F] and for [uslot_fs] / [uexec_ret_fs_F], and no    *)
(* engine proof inspects either.                                            *)
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
(* ...UexecRetFs.v's block above, VERBATIM (durable-notes: trimmed imports
   have OOM'd the build); the leaf's own imports below. *)
From iris.base_logic.lib Require Import ghost_var ghost_map.
Require Import UexecRet.     (* the plain contract, and [bump] / [tf_of_*] *)
Require Import WpMmodeLeafBase.   (* [csp_rs1] *)
Require Import UserHeap.     (* [uheap]/[ustack]/[ubytesq]/[uinstr_is] *)
Require Import UkRun.        (* [urun_close]'s twin's vocabulary: [unot_sp] *)
Require Import TsoCtx.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import FsFdMirror.   (* [umirror]/[mcur]/[ufs_step]/[uenr_dom] *)
Require Import UkStep.       (* [uk_instr] -- the ecall step's decode premise;
                                loaded already through UkRun, IMPORTED here
                                because the seal's statement names it *)
Require Import UexecRetFs.   (* the enriched contract this leaf runs on *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 THE ENRICHED NUMBERS ARE QUIET ROWS.                                *)
(*                                                                        *)
(* open = 15 and mknod = 17 are neither of the two numbers the arm's own   *)
(* case analysis takes first (exit, fork) nor any of the six the memory    *)
(* row treats specially (exec, sbrk, wait, pipe, read, fstat) -- so the    *)
(* leaf reaches the enriched branch, and [usys_mem_ok_quiet] pins the      *)
(* image, the permission map and the break across the trap.                *)
(* ===================================================================== *)
Lemma uenr_path_num (n : Z) :
  uenr_path n = true -> n = FsFdMirror.USYS_open \/ n = FsFdMirror.USYS_mknod.
Proof.
  unfold uenr_path. intros H.
  apply orb_true_iff in H. destruct H as [H | H];
    apply bool_decide_eq_true in H; [ left | right ]; exact H.
Qed.

Lemma uenr_dom_num (n : Z) :
  uenr_dom n = true ->
  n = FsFdMirror.USYS_open \/ n = FsFdMirror.USYS_mknod
  \/ n = FsFdMirror.USYS_dup.
Proof.
  unfold uenr_dom. intros H.
  apply orb_true_iff in H. destruct H as [H | H].
  - destruct (uenr_path_num n H) as [H' | H']; [ left | right; left ];
      exact H'.
  - right. right. apply bool_decide_eq_true in H. exact H.
Qed.

Lemma uenr_dom_rows (n : Z) :
  uenr_dom n = true ->
  n <> USYS_exit /\ n <> USYS_fork /\ n <> USYS_exec /\ n <> USYS_sbrk /\
  n <> USYS_wait /\ n <> USYS_pipe /\ n <> USYS_read /\ n <> USYS_fstat.
Proof.
  intros H. destruct (uenr_dom_num n H) as [-> | [-> | ->]];
    unfold FsFdMirror.USYS_open, FsFdMirror.USYS_mknod, FsFdMirror.USYS_dup,
           USYS_exit, USYS_fork, USYS_exec, USYS_sbrk,
           USYS_wait, USYS_pipe, USYS_read, USYS_fstat;
    split_and!; discriminate.
Qed.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UkRunSys.  (* [ufd_auth_move] -- the untracked authority step *)
Section StepPin.
  Context `{XI : CurCtx}.

  (* the honest blanket, at either enriched row: -1 moves nothing *)
  Lemma ufs_step_at_blanket (n : Z) (pl : list (bv 8)) (tf : list (mword 64))
      (u : umirror) :
    uenr_dom n = true ->
    ufs_step_at n pl tf (mword_of_int (-1) : mword 64) u u.
  Proof.
    intros H. unfold ufs_step_at.
    destruct (uenr_dom_num n H) as [-> | [-> | ->]].
    - destruct (decide (FsFdMirror.USYS_open = FsFdMirror.USYS_open))
        as [_ | Hc]; [| exfalso; exact (Hc eq_refl) ].
      left. exact (conj eq_refl eq_refl).
    - destruct (decide (FsFdMirror.USYS_mknod = FsFdMirror.USYS_open))
        as [Hc | _]; [ discriminate Hc |].
      destruct (decide (FsFdMirror.USYS_mknod = FsFdMirror.USYS_mknod))
        as [_ | Hc]; [| exfalso; exact (Hc eq_refl) ].
      left. exact (conj eq_refl eq_refl).
    - destruct (decide (FsFdMirror.USYS_dup = FsFdMirror.USYS_open))
        as [Hc | _]; [ discriminate Hc |].
      destruct (decide (FsFdMirror.USYS_dup = FsFdMirror.USYS_mknod))
        as [Hc | _]; [ discriminate Hc |].
      destruct (decide (FsFdMirror.USYS_dup = FsFdMirror.USYS_dup))
        as [_ | Hc]; [| exfalso; exact (Hc eq_refl) ].
      left. exact (conj eq_refl eq_refl).
  Qed.

  (* THE NON-PATH ENRICHED ROW (dup): its step reads no image at all, so
     the contract's [ufs_step] IS the row, at any [pl] -- [ufs_step_at]
     does not mention [pl] off the path rows. *)
  Lemma ufs_step_np (n : Z) (tf : list (mword 64)) (Mi : gmap Z (bv 8))
      (r : mword 64) (u u' : umirror) (pl : list (bv 8)) :
    uenr_path n = false ->
    ufs_step n tf Mi r u u' ->
    ufs_step_at n pl tf r u u'.
  Proof.
    intros Hnp Hst. unfold ufs_step in Hst. rewrite Hnp in Hst.
    unfold ufs_step_at in Hst |- *.
    destruct (decide (n = FsFdMirror.USYS_open)) as [-> | _].
    { exfalso. unfold uenr_path in Hnp.
      rewrite (bool_decide_eq_true_2 (FsFdMirror.USYS_open
                                      = FsFdMirror.USYS_open) eq_refl)
        in Hnp. discriminate Hnp. }
    destruct (decide (n = FsFdMirror.USYS_mknod)) as [-> | _].
    { exfalso. unfold uenr_path in Hnp.
      rewrite (bool_decide_eq_true_2 (FsFdMirror.USYS_mknod
                                      = FsFdMirror.USYS_mknod) eq_refl)
        in Hnp. rewrite orb_true_r in Hnp. discriminate Hnp. }
    exact Hst.
  Qed.

  (* OWNING THE STRING IS WHAT MAKES THE ROW CONCRETE.  The contract's
     [ufs_step] reads the path off the image at argument 0 and keeps an
     unreadable-string escape into the -1 blanket; a caller that OWNS the
     string ([UexecRetFs.ustrq], whose reading is the [ustr_read] premise
     here) collapses both arms onto ITS [pl]. *)
  Lemma ufs_step_pin (n : Z) (tf : list (mword 64)) (Mi : gmap Z (bv 8))
      (r : mword 64) (u u' : umirror) (pl : list (bv 8)) :
    uenr_dom n = true ->
    ustr_read Mi (uint (ufs_arg tf 0)) = Some pl ->
    ufs_step n tf Mi r u u' ->
    ufs_step_at n pl tf r u u'.
  Proof.
    intros Hdom Hread Hst.
    destruct (uenr_path n) eqn:Hp.
    - unfold ufs_step in Hst. rewrite Hp in Hst.
      destruct Hst as [[-> ->] | (pl' & Hread' & Hst)].
      + exact (ufs_step_at_blanket n pl tf u Hdom).
      + rewrite Hread in Hread'. apply Some_inj in Hread'. subst pl'.
        exact Hst.
    - exact (ufs_step_np n tf Mi r u u' pl Hp Hst).
  Qed.

End StepPin.

Section UkRunSysFs.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.

  (* =================================================================== *)
  (* §2 THE ENRICHED BUNDLE'S FACTS AND THE ENRICHED CONTINUATION.        *)
  (* =================================================================== *)

  (* x0 is pinned inside the bundle -- [UkStep.uvb_x0] at [uvb_fs] *)
  Lemma uvb_fs_x0 (γm : gname) (h : CpuId) (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (fdv : list fdstate) :
    uvb_fs (CID := h) γm C pt Rfd Rut sz π fdv M m pc -∗
    ⌜m !!! Regidx (mword_of_int 0) = zero_reg⌝ ∗
    uvb_fs (CID := h) γm C pt Rfd Rut sz π fdv M m pc.
  Proof.
    rewrite /uvb_fs /uvb_fs_F.
    iIntros "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iDestruct (gpr_file_x0 m (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hg") as "[%Hx0 Hg]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut Hk";
      try (iPureIntro; exact Hsz).
  Qed.

  (* THE ENRICHED U-MODE CONTINUATION at a natural state -- [UexecRet.ukc]
     with the enriched bundle.  A leaf's continuation is this; the enriched
     slot IS this at the key's own state ([uslot_fs_ukc]). *)
  Definition ukc_fs (γm : gname) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (szv : Z) (fdv : list fdstate)
      (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
       (Rut : uptd -> iProp Σ),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) szv = π⌝ -∗
       uvb_fs (CID := h) γm C pt Rfd Rut szv π fdv M m pc -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma uslot_fs_ukc (γm : gname) (W : uvis) :
    uslot_fs γm W ⊣⊢
    ukc_fs γm (uvis_perm W) (uvis_M W) (uvis_sz W) (uvis_fd W)
      (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).
  Proof. exact (uslot_fs_unfold γm W). Qed.

  (* ...and the enriched slot at a BUMPED trap-out key: the continuation
     after the syscall returned (a0 := r, pc + 4) *)
  Lemma uslot_fs_bump_run (γm : gname) (m : regfile) (pc : mword 64)
      (M M' : gmap Z (bv 8)) (π π' : gmap (mword 27) uperm) (szv szv' : Z)
      (fdv fdv' : list fdstate) (r : mword 64) :
    m !!! Regidx (mword_of_int 0) = zero_reg ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uslot_fs γm (bump (uvis_of_run m pc M π szv fdv) r M' π' szv' fdv')
    ⊣⊢ ukc_fs γm π' M' szv' fdv' (<[Regidx (mword_of_int 10) := r]> m)
                (add_vec_int pc 4).
  Proof.
    intros Hx0 Hal. rewrite uslot_fs_ukc.
    rewrite (bump_run_gpr m pc M M' π π' szv szv' fdv fdv' r Hx0)
            (bump_run_pc m pc M M' π π' szv szv' fdv fdv' r Hal).
    reflexivity.
  Qed.

  (* =================================================================== *)
  (* §3 THE RE-CLOSE, at [urun_fs] -- [UkRun.urun_close(_upd)]'s twins.    *)
  (* =================================================================== *)
  Lemma urun_fs_close (γm γt γd γs γfd : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (fdv : list fdstate)
      (m : regfile) (pc : mword 64)
      (avail : nat) :
    uheap γt γd γs M pm -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    (* the descriptor authority, exactly as [UkRun.urun_close] takes it *)
    ufd_auth γfd fdv -∗
    (∀ h : CpuId,
       urun_fs γm γt γd γs γfd h m pc avail -∗ WP (Loop : expr riscv_lang)) -∗
    ukc_fs γm pm M sz fdv m pc.
  Proof.
    iIntros "Hheap Hstk Hufd Hcont".
    rewrite /ukc_fs. iIntros (h C pt Rfd Rut) "%Hlo %Hpm Hb".
    iApply ("Hcont" $! h). rewrite /urun_fs.
    iExists C, pt, Rfd, Rut, sz, M, pm, fdv.
    iFrame "Hheap Hstk Hufd Hb". iPureIntro. split; [ exact Hlo | exact Hpm ].
  Qed.

  Lemma urun_fs_close_upd (γm γt γd γs γfd : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (m : regfile) (rd : mword 5)
      (v : mword 64) (sz : Z) (fdv : list fdstate) (pc' : mword 64)
      (avail : nat) :
    unot_sp rd ->
    uheap γt γd γs M pm -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    ufd_auth γfd fdv -∗
    (∀ h : CpuId,
       urun_fs γm γt γd γs γfd h (<[Regidx rd := v]> m) pc' avail -∗
       WP (Loop : expr riscv_lang)) -∗
    ukc_fs γm pm M sz fdv (<[Regidx rd := v]> m) pc'.
  Proof.
    intros Hns. iIntros "Hheap Hstk Hufd Hcont".
    iApply (urun_fs_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd v m Hns). iExact "Hstk".
  Qed.

  (* =================================================================== *)
  (* §4 THE LEAF.                                                         *)
  (*                                                                      *)
  (* [UkRunSys.wp_uk_ecall_quiet]'s shape on [urun_fs], with the deposit:  *)
  (* the caller hands in its mirror half and the string its argument 0     *)
  (* names, and gets the half back STEPPED by the row at that very string  *)
  (* -- which is the only thing the plain quiet leaf cannot say.  The      *)
  (* machine step is the sealed premise [STEP] (the header explains why    *)
  (* it cannot be [UkStep.wp_uk_ecall]).                                   *)
  (* =================================================================== *)
  Lemma wp_uk_ecall_fs_of_step
      (STEP : forall (γm' : gname) (h' : CpuId) (C : ucfg) (pt : uptd)
                (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z)
                (M : gmap Z (bv 8)) (fdv' : list fdstate)
                (m' : regfile) (pc' : mword 64),
                loop_ok C pt ->
                perm_of (ud_um pt) sz = π ->
                uk_instr π M pc' false (ECALL tt) ->
                uvb_fs (CID := h') γm' C pt Rfd Rut sz π fdv' M m' pc' -∗
                uexec_ret_fs γm' uecall_scause
                  (uvis_of_run m' pc' M π sz fdv') -∗
                WP (Loop : expr riscv_lang))
      (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (n : Z) (u : umirror) (pl : list (bv 8)) (dq : dfrac) (avail : nat) :
    usys_num (tf_of m pc) = n ->
    uenr_dom n = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    ⊢ wp_uk_ecall_fs_body γm γt γd γs γfd h m pc n u pl dq avail.
  Proof.
    intros Hn Hdom Hal4.
    rewrite /wp_uk_ecall_fs_body.
    iIntros "#Hi Hrun Hmc Hstr Hcont".
    iDestruct "Hrun" as (C pt Rfd Rut sz M pm fdv)
      "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_fs_x0 with "Hb") as "[%Hx0 Hb]".
    (* THE PATH, PINNED: the caller's string is the one the row reads *)
    iDestruct (uheap_ustrq with "Hheap Hstr") as %Hread.
    assert (Hread0 : ustr_read M (uint (ufs_arg (tf_of m pc) 0)) = Some pl)
      by exact Hread.
    iApply (STEP γm h C pt Rfd Rut pm sz M fdv m pc Hlo Hpm Hui with "Hb").
    (* ---- the ENRICHED return, at the trap-out key ---- *)
    rewrite /uexec_ret_fs /uexec_ret_fs_F.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hc];
      [| exfalso; exact (Hc eq_refl) ].
    cbv zeta.
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv)) = n).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite Hnum.
    destruct (uenr_dom_rows n Hdom)
      as (Hexit & Hfork & Hexec & Hsbrk & Hwait & Hpipe & Hrd & Hfst).
    destruct (decide (n = USYS_exit)) as [He | _];
      [ exfalso; exact (Hexit He) |].
    destruct (decide (n = USYS_fork)) as [He | _];
      [ exfalso; exact (Hfork He) |].
    rewrite Hdom.
    (* THE DEPOSIT: the process takes the arm's RIGHT disjunct *)
    iRight. iExists u. iFrame "Hmc".
    iIntros (r M' pm' sz' fdv' u') "%Hok %Hfdok %Hpiperow %Hstep Hmc".
    (* the enriched rows are QUIET: nothing about the image moved *)
    destruct (usys_mem_ok_quiet n _ r _ _ _ _ _ _
                Hexec Hsbrk Hwait Hpipe Hrd Hfst Hok) as [-> [-> ->]].
    cbn [uvis_M uvis_perm uvis_sz uvis_of_run].
    (* THE ENRICHED ROWS INCLUDE open AND dup, so the table may have moved.
       The program is not tracking these descriptors, so the authority moves
       and no handle comes back ([UkRunSys.ufd_auth_move]); close is not in
       [uenr_dom], which is exactly the row that rule cannot serve. *)
    iApply uslot_fs_bupd.
    iMod (ufd_auth_move γfd n (tf_of m pc) r fdv fdv'
            (uenr_dom_ne_close n Hdom) Hfdok with "Hufd") as "Hufd".
    iModIntro.
    rewrite (uslot_fs_bump_run γm m pc M M pm pm sz sz fdv fdv' r Hx0 Hal4).
    iApply (urun_fs_close_upd γm γt γd γs γfd M pm m (mword_of_int 10) r sz fdv'
              (add_vec_int pc 4) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r u' with "[%] Hmc Hstr Hrun").
    (* ...and the tie, read at the caller's own string *)
    cbn [uvis_tf uvis_M uvis_of_run] in Hstep.
    exact (ufs_step_pin n (tf_of m pc) M r u u' pl Hdom Hread0 Hstep).
  Qed.

End UkRunSysFs.

(* ===================================================================== *)
(* THE REMAINING SEAL: the machine step, and NOTHING else.                *)
(*                                                                        *)
(* [UkStep.wp_uk_ecall] with [uvb -> uvb_fs] and                          *)
(* [uexec_ret -> uexec_ret_fs].  No fs vocabulary appears in it beyond     *)
(* those two names; its discharge is the X-generic engine the header's     *)
(* upstream ask describes (or, transitionally, that engine's copy at the   *)
(* enriched fixpoint).                                                     *)
(* ===================================================================== *)
Module Type FDROW_UKFS_STEP.
  Parameter wp_uk_ecall_fs_step :
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
End FDROW_UKFS_STEP.

(* ...and the engine seal, DISCHARGED from it: everything the pilot's leaf
   owes beyond the machine step is proven above. *)
Module FdRowUkfsEngineOfStep (S : FDROW_UKFS_STEP) <: FDROW_UKFS_ENGINE.
  Lemma wp_uk_ecall_fs :
    forall `{!riscvGS Σ} `{GEN : GenId} `{XI : CurCtx}
           `{!ghost_varG Σ Z} `{!ghost_varG Σ umirror} `{!ufdG Σ}
      (γm γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (n : Z) (u : umirror) (pl : list (bv 8)) (dq : dfrac) (avail : nat),
      usys_num (tf_of m pc) = n ->
      uenr_dom n = true ->
      is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
      ⊢ wp_uk_ecall_fs_body γm γt γd γs γfd h m pc n u pl dq avail.
  Proof.
    intros.
    apply (wp_uk_ecall_fs_of_step S.wp_uk_ecall_fs_step); assumption.
  Qed.
End FdRowUkfsEngineOfStep.
