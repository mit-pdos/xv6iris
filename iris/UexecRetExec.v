(* ===================================================================== *)
(* UexecRetExec.v -- THE ENRICHED TRAP CONTRACT (exec row): the            *)
(* user/kernel syscall arm with an exec HAND-OVER, as a PARALLEL FORM      *)
(* beside UexecRet.v.                                                      *)
(*                                                                         *)
(* Design of record: claude-notes/design/user-wp-slot.md (the slot and the *)
(* trap contract) and SpecSysExecAU.v's header (the bundle the kernel      *)
(* wants at an exec ecall).  The precedent for the PARALLEL-FIXPOINT shape *)
(* -- and for the receipts below -- is UexecRetFs.v.                       *)
(*                                                                         *)
(* THE ONE DIFFERENCE from [UexecRet.uexec_ret_F]: the returning-syscall   *)
(* arm splits off [USYS_exec], where the process must ALSO hand over       *)
(*                                                                         *)
(*     xbundle W  ∗  <today's generic returning arm, VERBATIM>             *)
(*                                                                         *)
(* [xbundle] is the payload family, a field of the ambient class           *)
(* [uexecXG] declared in this file, so this file's cone gains no fs        *)
(* import; the kernel-side instance (the AU bundle                         *)
(* [SpecSysExecAU.sys_exec_au_pre] at the trapping key's image, argv       *)
(* pointer and descriptor view) lives in UexecExecInst.v, beside the spec  *)
(* it names.                                                               *)
(*                                                                         *)
(* IT IS A PURE GIVE, and both halves of that matter:                      *)
(*   - on SUCCESS the kernel CONSUMES the bundle: exec's success arm       *)
(*     returns [uslot (exec_key U' sts na)] for the NEW process, which is  *)
(*     a different key, and THIS process never resumes.  So the generic    *)
(*     arm beside the bundle is simply never instantiated -- the           *)
(*     continuation is dropped, exactly as [USYS_exit]'s [emp] arm is      *)
(*     dropped.                                                            *)
(*   - on FAILURE exec returns -1 to this process and the generic arm      *)
(*     fires; [UsysMemOk]'s exec row pins that arm to                      *)
(*     [r = -1 /\ M' = M /\ π' = π /\ szv' = szv], so the process resumes  *)
(*     at its own key, exactly as today.  THE REFUNDED BUNDLE IS LOST TO   *)
(*     THE PROGRAM: [sys_exec_post_fail] hands the AU bundle back to the   *)
(*     KERNEL's frame, and this arm gives the process no channel to        *)
(*     receive it on, so a program cannot retry exec after a failure.      *)
(*     That is a deliberate limit of this increment (the refund would need *)
(*     the arm to read [xbundle] back under the ∀, i.e. the fd-row         *)
(*     pilot's DEPOSIT shape rather than a give); nothing here depends on  *)
(*     it, and the init -> sh chain never retries.                         *)
(*                                                                         *)
(* TRANSITIONAL BY DESIGN, exactly as UexecRetFs.v is: at adoption the one *)
(* arm moves into [UexecRet.uexec_ret_F] with [xbundle] behind the same    *)
(* ambient class, and this file's fixpoint collapses into the original.    *)
(*                                                                         *)
(* WHAT IS PROVEN HERE (the conservativity receipts), AND WHICH WAY THEY   *)
(* POINT.  UexecRetFs's enrichment OFFERS the process a disjunct, so its   *)
(* receipts run plain -> enriched ([uslot_uslot_fs]).  THIS enrichment     *)
(* DEMANDS a resource of the process, so every receipt runs the OTHER way: *)
(*   [uexec_ret_x_to]  -- the enriched return implies the plain one (the   *)
(*                        bundle is dropped at the exec arm);              *)
(*   [uslot_x_uslot]   -- every exec-safe process is plain-safe, by Löb    *)
(*                        through the ▷ in [ukont_x];                      *)
(*   [ukont_ukont_x] / [uvb_uvb_x] / [urun_urun_x] -- a PLAIN kernel       *)
(*                        promise (bundle, running predicate) meets the    *)
(*                        enriched one: being handed a stronger return is  *)
(*                        easier.                                          *)
(* [uslot W -∗ uslot_x W] IS NOT PROVABLE, and the header says so on       *)
(* purpose: lifting a plain program to this tier would have to conjure an  *)
(* [xbundle] at every future exec trap the program takes, and nothing in   *)
(* [uslot] carries one.  The honest arm-level statements are               *)
(* [uexec_ret_x_of_bundle] (the exec ecall, with the bundle supplied) and  *)
(* [uexec_ret_x_of] (every other trap, no bundle needed), each over the    *)
(* slot upgrader as an explicit premise -- the shape                       *)
(* [UexecRetFs.uexec_ret_fs_of] has, minus the [uslot_uslot_fs] that       *)
(* discharges it there.                                                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes WpGpr.
Require Import UserPtTree.
Require Import UserExec.
Require Import UexecWp.
Require Import UexecSlot.
Require Import UsysMemOk.
Require Import UmodeRegs.
Require Import UserPerm.
Local Open Scope Z_scope.
Import Defs.
(* ...UexecRet.v's block above, VERBATIM (durable-notes: trimmed imports
   have OOM'd the build); the enrichment's own imports below. *)
From iris.base_logic.lib Require Import ghost_var.
Require Import UexecRet.
Require Import UmodeText.     (* the plain contract this file encloses --
                                 REQUIRED DIRECTLY: [uslot]/[uvb] are
                                 [Typeclasses Opaque] and the seal does not
                                 travel through a re-export *)
Require Import WpMmodeLeafBase.   (* [csp_rs1] *)
Require Import UserHeap.     (* [uheap]/[ustack] *)
Require Import UkRun.        (* [urun] -- the plain running predicate *)
Require Import TsoCtx.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import UserFd.       (* [ufd_auth] *)

(* ===================================================================== *)
(* SS0 THE PAYLOAD FAMILY, as an ambient class.                            *)
(*                                                                         *)
(* What the program hands the kernel at its exec ecall, keyed on the       *)
(* TRAPPING KEY [W] -- the kernel reads the argv pointer, the image and    *)
(* the descriptor view off that key, so the family has to be indexed by it *)
(* rather than by the syscall number alone.  It is a CLASS and not a       *)
(* parameter for the reason UexecRet's cone is the reason: the concrete    *)
(* family ([SpecSysExecAU.sys_exec_au_pre]) lives above the whole fs       *)
(* tower, and threading it as an argument would drag that tower's binders  *)
(* through every U-mode form below.  UexecExecInst.v supplies the one      *)
(* instance.                                                               *)
(* ===================================================================== *)
Class uexecXG (Σ : gFunctors) := {
  xbundle : uvis -> iProp Σ
}.

Section UexecRetExec.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{XG : uexecXG Σ}.
  Context `{!ghost_varG Σ Z}.

  (* =================================================================== *)
  (* SS1 THE CONTRACT, as one guarded fixpoint -- UexecRet.v SS3 with the  *)
  (* ONE arm spliced into the returning-syscall case.                     *)
  (* =================================================================== *)

  (* (A) what user execution hands back, at the fixpoint variable [X].
     The difference from [UexecRet.uexec_ret_F], and there is exactly one:
     the returning-syscall arm splits [USYS_exec] off, and there the arm
     is [xbundle W ∗ <the generic arm verbatim>]. *)
  Definition uexec_ret_x_F (X : uvis -d> iPropO Σ) (sc : mword 64) (W : uvis)
      : iProp Σ :=
    (if decide (sc = uecall_scause) then
       let n := usys_num (uvis_tf W) in
       if decide (n = USYS_exit) then emp
       else if decide (n = USYS_fork) then
         ((∀ (r : mword 64) (fdv' : list fdstate),
             ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
             (* the parent's own table does not move -- see
                [UexecRet.uexec_ret_F]'s note on the same guard *)
             ⌜fdv' = uvis_fd W⌝ -∗
             X (bump W r (uvis_M W) (uvis_perm W) (uvis_sz W) fdv')) ∗
          (∀ fdv' : list fdstate,
             (* the child's table is the parent's -- see [UexecRet]'s note *)
             ⌜fdv' = uvis_fd W⌝ -∗
             X (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W) (uvis_sz W)
                  fdv')))
       else if decide (n = USYS_exec) then
         (* THE HAND-OVER (header).  The bundle goes BESIDE the generic
            arm, not inside it: on success the kernel consumes the bundle
            and the arm is dropped (the new process runs under the slot
            the kernel derived from the bundle, and this process never
            resumes); on failure the arm fires at [UsysMemOk]'s exec row,
            which pins [r = -1] and leaves the image, the map and the
            break where they were. *)
         (xbundle W ∗
          (∀ (r : mword 64) (M' : gmap Z (bv 8))
             (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate),
             ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W)
                          (uvis_sz W) M' π' szv'⌝ -∗
             ⌜usys_fd_ok n (uvis_tf W) r (uvis_fd W) fdv'⌝ -∗
             ⌜usys_pipe_ok n (uvis_tf W) r (uvis_M W) M' (uvis_fd W) fdv'⌝ -∗
             X (bump W r M' π' szv' fdv')))
       else (∀ (r : mword 64) (M' : gmap Z (bv 8))
               (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate),
               ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W)
                            (uvis_sz W) M' π' szv'⌝ -∗
               ⌜usys_fd_ok n (uvis_tf W) r (uvis_fd W) fdv'⌝ -∗
               (* ...AND PIPE'S JOIN, the one row neither of the two above can
                  state.  [usys_mem_ok] says pipe wrote eight bytes at a0 from
                  SOME function, [usys_fd_ok] says it opened two free slots, and
                  only this says the bytes NAME the slots -- which is the whole
                  of pipe() to the program that called it.  [UsysMemOk.v] SS2c. *)
               ⌜usys_pipe_ok n (uvis_tf W) r (uvis_M W) M' (uvis_fd W) fdv'⌝ -∗
               X (bump W r M' π' szv' fdv'))
     else X W)%I.

  (* (B) the kernel obligation, and (C) the bundle -- UexecRet.v verbatim
     at the enriched return *)
  Definition ukb_x_F (X : uvis -d> iPropO Σ) `{CID : CpuId}
      `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) : iProp Σ :=
    (∀ (W' : uvis) (sc stv : mword 64),
       ⌜uvis_perm W' = π⌝ -∗
       ⌜uvis_sz W' = sz⌝ -∗
       ⌜uvis_fd W' = fdv⌝ -∗
       trapped_machine C pt Rut sz sc stv W' ∗ Rfd (uvis_fd W') ∗
       uexec_ret_x_F X sc W' -∗
       WP (Loop : expr riscv_lang))%I.

  Definition ukont_x_F (X : uvis -d> iPropO Σ) `{CID : CpuId}
      `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) : iProp Σ :=
    (▷ ukb_x_F X C pt Rfd Rut sz π fdv)%I.

  Definition uvb_x_F (X : uvis -d> iPropO Σ) `{CID : CpuId}
      `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (uv_amb ∗ uv_regs ∗ ⌜usz_ok sz⌝ ∗ user_ptm_inv_x pt sz M ∗ Rfd fdv ∗
     user_cfg C ∗
     gpr_file m ∗ pc_is pc ∗ Rut pt ∗ ukont_x_F X C pt Rfd Rut sz π fdv)%I.

  Definition uslot_x_F (X : uvis -d> iPropO Σ) : uvis -d> iPropO Σ :=
    fun W =>
      (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd)
         (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
         (* A6.140: the residue-token accessor rides the ∀ as a Coq-level
            fact, exactly [UexecRet.uslot_F]'s row -- the loop engine
            borrows the running token out of [Rut pt] per step and
            restores it *)
         (HRut : forall pt' : uptd,
                 ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                              (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')),
         ⌜loop_ok C pt⌝ -∗
         ⌜perm_of (ud_um pt) (uvis_sz W) = uvis_perm W⌝ -∗
         uvb_x_F X (CID := h) (XI := xi) C pt Rfd Rut (uvis_sz W)
           (uvis_perm W) (uvis_fd W) (uvis_M W)
           (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         -∗
         WP (Loop : expr riscv_lang))%I.

  Local Instance uslot_x_F_contractive : Contractive uslot_x_F.
  Proof.
    rewrite /uslot_x_F /uvb_x_F /ukont_x_F /ukb_x_F /uexec_ret_x_F.
    solve_contractive.
  Qed.

  Definition uslot_x : uvis -> iProp Σ := fixpoint uslot_x_F.
  Definition uexec_ret_x : mword 64 -> uvis -> iProp Σ :=
    uexec_ret_x_F uslot_x.
  Definition ukb_x `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate)
      : iProp Σ := ukb_x_F uslot_x C pt Rfd Rut sz π fdv.
  Definition ukont_x `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg)
      (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate)
      : iProp Σ := ukont_x_F uslot_x C pt Rfd Rut sz π fdv.
  Definition uvb_x `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    uvb_x_F uslot_x C pt Rfd Rut sz π fdv M m pc.

  Lemma uslot_x_unfold (W : uvis) :
    uslot_x W ⊣⊢
    (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd)
       (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
       (HRut : forall pt' : uptd,
                 ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                              (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) (uvis_sz W) = uvis_perm W⌝ -∗
       uvb_x (CID := h) (XI := xi) C pt Rfd Rut (uvis_sz W) (uvis_perm W)
         (uvis_fd W) (uvis_M W)
         (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)) -∗
       WP (Loop : expr riscv_lang)).
  Proof. exact (fixpoint_unfold uslot_x_F W). Qed.

  (* the exec slot absorbs a basic update, exactly as [UexecRet.uslot_bupd]
     does -- what a leaf needs when its own ghost step runs before the key
     is handed back *)
  Lemma uslot_x_bupd (W : uvis) : (|==> uslot_x W) -∗ uslot_x W.
  Proof.
    rewrite !(uslot_x_unfold W).
    iIntros "H" (h xi C pt Rfd Rut HRut) "%Hl %Hp Hb".
    iMod "H". iApply ("H" $! h xi C pt Rfd Rut HRut with "[%] [%] Hb");
      [ exact Hl | exact Hp ].
  Qed.

  (* =================================================================== *)
  (* SS2 THE CONSERVATIVITY RECEIPTS.                                     *)
  (* =================================================================== *)

  (* the FORGETFUL direction, arm by arm: an enriched return builds a plain
     one -- the exec arm's bundle is dropped -- given a slot downgrader for
     the returned keys *)
  Lemma uexec_ret_x_down (sc : mword 64) (W : uvis) :
    □ (∀ W' : uvis, uslot_x W' -∗ uslot W') -∗
    uexec_ret_x sc W -∗
    uexec_ret sc W.
  Proof.
    rewrite /uexec_ret_x /uexec_ret /uexec_ret_F /uexec_ret_x_F.
    cbv zeta.
    iIntros "#Hdn Hret".
    destruct (decide (sc = uecall_scause)); [| by iApply "Hdn"].
    destruct (decide (usys_num (uvis_tf W) = USYS_exit)); [done |].
    destruct (decide (usys_num (uvis_tf W) = USYS_fork)).
    { iDestruct "Hret" as "[Hp Hc]".
      iSplitL "Hp".
      - iIntros (r fdv') "%Hr %Hfv".
        iApply "Hdn". iApply ("Hp" $! r fdv' with "[%] [%]");
          [ exact Hr | exact Hfv ].
      - iIntros (fdv') "%Hfvl". iApply "Hdn".
        iApply ("Hc" $! fdv' with "[%]"). exact Hfvl. }
    destruct (decide (usys_num (uvis_tf W) = USYS_exec)).
    { (* THE BUNDLE IS DROPPED HERE, and this is the only place it is *)
      iDestruct "Hret" as "[_ Hret]".
      iIntros (r M' π' szv' fdv') "%Hok %Hfdok %Hpiperow".
      iApply "Hdn".
      iApply ("Hret" $! r M' π' szv' fdv' with "[%] [%] [%]");
        [exact Hok | exact Hfdok | exact Hpiperow]. }
    iIntros (r M' π' szv' fdv') "%Hok %Hfdok %Hpiperow".
    iApply "Hdn".
    iApply ("Hret" $! r M' π' szv' fdv' with "[%] [%] [%]");
      [exact Hok | exact Hfdok | exact Hpiperow].
  Qed.

  (* THE BRIDGE: every exec-safe process is plain-safe.  This is the
     conservativity receipt -- the enriched tier proves no MORE programs
     safe -- and it is the direction the demand-shaped enrichment admits
     (header: the opposite direction is not provable). *)
  Lemma uslot_x_uslot (W : uvis) : uslot_x W -∗ uslot W.
  Proof.
    iLöb as "IH" forall (W).
    iIntros "Hs".
    rewrite uslot_unfold.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    rewrite /uvb /uvb_F.
    iDestruct "Hb" as
      "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iEval (rewrite uslot_x_unfold) in "Hs".
    iApply ("Hs" $! h xi C pt Rfd Rut HRut with "[%] [%] [-]");
      [exact Hlo | exact Hpm |].
    rewrite /uvb_x /uvb_x_F.
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut".
    iSplitR; [iPureIntro; exact Hsz |].
    (* the enriched kernel promise, from the plain one: postcompose the
       return with the forgetful map *)
    rewrite /ukont_x_F.
    iEval (rewrite /ukont_F) in "Hk".
    iNext.
    rewrite /ukb_F /ukb_x_F.
    iIntros (W' sc stv) "%Hp %Hs' %Hf' (Htm & Hfr & Hret)".
    iApply ("Hk" $! W' sc stv with "[%] [%] [%] [Htm Hfr Hret]");
      [exact Hp | exact Hs' | exact Hf' |].
    iFrame "Htm Hfr".
    iApply (uexec_ret_x_down with "IH Hret").
  Qed.

  Lemma uexec_ret_x_to (sc : mword 64) (W : uvis) :
    uexec_ret_x sc W -∗ uexec_ret sc W.
  Proof.
    iIntros "H". iApply (uexec_ret_x_down with "[] H").
    iIntros "!>" (W') "Hs". iApply uslot_x_uslot. iExact "Hs".
  Qed.

  (* ...and the kernel-side fallback: a PLAIN kernel promise meets the
     enriched one.  (The enrichment is a demand on the process, so the
     kernel side moves the easy way: being handed a stronger return.) *)
  Lemma ukont_ukont_x `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg)
      (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) :
    ukont C pt Rfd Rut sz π fdv -∗ ukont_x C pt Rfd Rut sz π fdv.
  Proof.
    iIntros "Hk". rewrite /ukont_x /ukont_x_F.
    iEval (rewrite /ukont /ukont_F) in "Hk".
    iNext. rewrite /ukb_x_F.
    iIntros (W' sc stv) "%Hp %Hs %Hf (Htm & Hfr & Hret)".
    iApply ("Hk" $! W' sc stv with "[%] [%] [%] [Htm Hfr Hret]");
      [exact Hp | exact Hs | exact Hf |].
    iFrame "Htm Hfr".
    iApply (uexec_ret_x_to with "Hret").
  Qed.

  Lemma uvb_uvb_x `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) :
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    uvb_x C pt Rfd Rut sz π fdv M m pc.
  Proof.
    iIntros "Hb". rewrite /uvb_x /uvb_x_F.
    iEval (rewrite /uvb /uvb_F) in "Hb".
    iDestruct "Hb" as
      "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut".
    iSplitR; [iPureIntro; exact Hsz |].
    iApply (ukont_ukont_x with "Hk").
  Qed.

  (* =================================================================== *)
  (* SS3 THE ENRICHED RUNNING PREDICATE.                                  *)
  (* =================================================================== *)

  (* [UkRun.urun] with [uvb] swapped for [uvb_x] -- and nothing else: the
     exec enrichment adds no ghost state of its own (the payload is the
     class field), so unlike [UexecRetFs.urun_fs] this carries no extra
     ledger. *)
  Definition urun_x (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) : iProp Σ :=
    (∃ (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd)
       (Rfd : list fdstate -> iProp Σ)
       (Rut : uptd -> iProp Σ) (sz : Z)
       (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (fdv : list fdstate),
       ⌜ loop_ok C pt ⌝ ∗ ⌜ perm_of (ud_um pt) sz = pm ⌝ ∗
       ⌜ forall pt' : uptd,
           ⊢ Rut pt' -∗ TsoCtx.own_context (CID := h) (cur_ctx (CurCtx := xi)) ∗
                        (TsoCtx.own_context (CID := h) (cur_ctx (CurCtx := xi))
                         -∗ Rut pt') ⌝ ∗
       uheap γt γd γs M pm ∗
       ustack γd (m !!! Regidx csp_rs1) avail ∗
       ufd_auth γfd fdv ∗
       uvb_x (CID := h) (XI := xi) C pt Rfd Rut sz pm fdv M m pc)%I.

  (* a plain running bundle IS an exec-enriched one: the loop hands out
     [urun] today and the exec-tier program can take it as is *)
  Lemma urun_urun_x (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    urun γt γd γs γfd h m pc avail -∗ urun_x γt γd γs γfd h m pc avail.
  Proof.
    iIntros "H".
    rewrite /urun.
    iDestruct "H" as (xi C pt Rfd Rut sz M pm fdv)
      "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    rewrite /urun_x. iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv.
    iSplitR; [iPureIntro; exact Hlo |].
    iSplitR; [iPureIntro; exact Hpm |].
    iSplitR; [iPureIntro; exact HRut |].
    iFrame "Hheap Hstk Hufd".
    iApply (uvb_uvb_x with "Hb").
  Qed.

  (* =================================================================== *)
  (* SS4 THE ARM-LEVEL INJECTIONS (what the program owes), and the        *)
  (* KERNEL-FACING READERS.                                               *)
  (* =================================================================== *)

  (* the plain return builds the enriched one AT EVERY TRAP, given the
     bundle for the exec arm and a slot upgrader for the returned keys.
     NOTE the upgrader is a PREMISE and is not discharged here: see the
     header -- [uslot W -∗ uslot_x W] does not hold, so this receipt is
     the honest arm-level statement and the program-side caller supplies
     both halves at the one key it is at. *)
  Lemma uexec_ret_x_of_bundle (sc : mword 64) (W : uvis) :
    □ (∀ W' : uvis, uslot W' -∗ uslot_x W') -∗
    xbundle W -∗
    uexec_ret sc W -∗
    uexec_ret_x sc W.
  Proof.
    rewrite /uexec_ret_x /uexec_ret /uexec_ret_F /uexec_ret_x_F.
    cbv zeta.
    iIntros "#Hup Hx Hret".
    destruct (decide (sc = uecall_scause)); [| by iApply "Hup"].
    destruct (decide (usys_num (uvis_tf W) = USYS_exit)); [done |].
    destruct (decide (usys_num (uvis_tf W) = USYS_fork)).
    { iDestruct "Hret" as "[Hp Hc]".
      iSplitL "Hp".
      - iIntros (r fdv') "%Hr %Hfv".
        iApply "Hup". iApply ("Hp" $! r fdv' with "[%] [%]");
          [ exact Hr | exact Hfv ].
      - iIntros (fdv') "%Hfvl". iApply "Hup".
        iApply ("Hc" $! fdv' with "[%]"). exact Hfvl. }
    destruct (decide (usys_num (uvis_tf W) = USYS_exec)).
    { iSplitL "Hx"; [iExact "Hx" |].
      iIntros (r M' π' szv' fdv') "%Hok %Hfdok %Hpiperow".
      iApply "Hup".
      iApply ("Hret" $! r M' π' szv' fdv' with "[%] [%] [%]");
        [exact Hok | exact Hfdok | exact Hpiperow]. }
    iIntros (r M' π' szv' fdv') "%Hok %Hfdok %Hpiperow".
    iApply "Hup".
    iApply ("Hret" $! r M' π' szv' fdv' with "[%] [%] [%]");
      [exact Hok | exact Hfdok | exact Hpiperow].
  Qed.

  (* ...and at every trap that is NOT an exec ecall, no bundle is needed *)
  Lemma uexec_ret_x_of (sc : mword 64) (W : uvis) :
    (sc = uecall_scause -> usys_num (uvis_tf W) <> USYS_exec) ->
    □ (∀ W' : uvis, uslot W' -∗ uslot_x W') -∗
    uexec_ret sc W -∗
    uexec_ret_x sc W.
  Proof.
    intros Hne.
    rewrite /uexec_ret_x /uexec_ret /uexec_ret_F /uexec_ret_x_F.
    cbv zeta.
    iIntros "#Hup Hret".
    destruct (decide (sc = uecall_scause)) as [Hec |]; [| by iApply "Hup"].
    destruct (decide (usys_num (uvis_tf W) = USYS_exit)); [done |].
    destruct (decide (usys_num (uvis_tf W) = USYS_fork)).
    { iDestruct "Hret" as "[Hp Hc]".
      iSplitL "Hp".
      - iIntros (r fdv') "%Hr %Hfv".
        iApply "Hup". iApply ("Hp" $! r fdv' with "[%] [%]");
          [ exact Hr | exact Hfv ].
      - iIntros (fdv') "%Hfvl". iApply "Hup".
        iApply ("Hc" $! fdv' with "[%]"). exact Hfvl. }
    destruct (decide (usys_num (uvis_tf W) = USYS_exec)) as [Hx |].
    { exfalso. exact (Hne Hec Hx). }
    iIntros (r M' π' szv' fdv') "%Hok %Hfdok %Hpiperow".
    iApply "Hup".
    iApply ("Hret" $! r M' π' szv' fdv' with "[%] [%] [%]");
      [exact Hok | exact Hfdok | exact Hpiperow].
  Qed.

  (* THE ROUND'S READER, in [UexecApply.uexec_ret_ecall]'s shape: at an
     ecall whose number is exec, the enriched return IS the bundle beside
     the generic (failure) arm.  This is what the dispatch route extracts
     the bundle with. *)
  Lemma uexec_ret_x_ecall_exec (sc : mword 64) (W : uvis) :
    sc = uecall_scause ->
    usys_num (uvis_tf W) = USYS_exec ->
    uexec_ret_x sc W ⊣⊢
    (xbundle W ∗
     (∀ (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm)
        (szv' : Z) (fdv' : list fdstate),
        ⌜usys_mem_ok (usys_num (uvis_tf W)) (uvis_tf W) r (uvis_M W)
                     (uvis_perm W) (uvis_sz W) M' π' szv'⌝ -∗
        ⌜usys_fd_ok (usys_num (uvis_tf W)) (uvis_tf W) r (uvis_fd W) fdv'⌝ -∗
        ⌜usys_pipe_ok (usys_num (uvis_tf W)) (uvis_tf W) r (uvis_M W) M'
                      (uvis_fd W) fdv'⌝ -∗
        uslot_x (bump W r M' π' szv' fdv'))).
  Proof.
    intros -> Hn. rewrite /uexec_ret_x /uexec_ret_x_F. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hc];
      [| contradiction].
    rewrite Hn.
    destruct (decide (USYS_exec = USYS_exit)) as [Hc | _];
      [ exfalso; discriminate Hc |].
    destruct (decide (USYS_exec = USYS_fork)) as [Hc | _];
      [ exfalso; discriminate Hc |].
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc]; [| contradiction].
    reflexivity.
  Qed.

  (* the transparent arm, verbatim from [UexecRet.uexec_ret_transparent] *)
  Lemma uexec_ret_x_transparent (sc : mword 64) (W : uvis) :
    sc <> uecall_scause ->
    uexec_ret_x sc W ⊣⊢ uslot_x W.
  Proof.
    intros Hne. rewrite /uexec_ret_x /uexec_ret_x_F.
    destruct (decide (sc = uecall_scause)); [ contradiction | reflexivity ].
  Qed.

End UexecRetExec.

(* the bundle wraps [gpr_file] and the slot wraps the bundle: sealed,
   exactly as UexecRet.v seals its own pair; consumers go through
   [uslot_x_unfold] / [rewrite /uvb_x /uvb_x_F], and a file manipulating
   either must [Require Import UexecRetExec] directly *)
Global Typeclasses Opaque uslot_x uvb_x.
