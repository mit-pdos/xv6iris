(* UexecExecInst.v -- THE KERNEL-SIDE INSTANCE of the per-syscall deposit
   class [UexecSG.uexecSG], and of the generic program's [UexecSG.uprogSG]
   beside it.

   UexecSG.v states the U-mode trap contract's returning arm over an
   ambient class whose family
   [sbundle : (uvis -d> iPropO Σ) -> Z -> uvis -> iProp Σ] says what the
   program hands over at an ecall of number [n], AT THE RECURSIVE
   OCCURRENCE: exec's bundle carries a slot wand, so the family is applied
   to the fixpoint variable and at the fixpoint it concludes at [uslot] --
   the slot the kernel returns for the new process.  The class is what
   keeps the whole U-mode fixpoint's cone clear of the fs tower.  THIS file
   is where the two meet.

   WHICH NUMBERS HAVE A BUNDLE.  Exactly one: [UsysMemOk.USYS_exec].  Every
   other number's [sbundle_at] is [emp] and every number's [spost_at] is
   [emp] -- exec's process never resumes on success, and the syscalls whose
   armed post is real are the next round's.

   THE DEPOSIT'S FAMILIES ([UexecSG.sfam]) are a RECORD with one field per
   contracted syscall, so that the arm can bind them once in front of both
   legs and the post comes back at the receipts the process chose.  At this
   instance the record is [xfam], whose one field is exec's -- and exec's
   post is [emp], so nothing reads it yet; the nine real syscalls' fields
   are the next round's.

   WHAT EXEC'S BUNDLE IS.  [SpecSysExecAU.sys_exec_au_pre] at the TRAPPING
   KEY's own data:
     - the image [uvis_M W]: the arguments are read off the image the
       process trapped at ([wp_sys_exec_sconf_body] takes the bundle at
       [us_M U], and the trap-out key's image IS that image -- the loop
       hands [uvis_M W] to the dispatcher);
     - the argv pointer [tf_w (uvis_tf W) (tf_arg_idx 1)]: sys_exec's
       argument 1, read off the key's trapframe.  ([wp_sys_exec_sconf_body]
       names it [v1] and pins it by [pv_tf (us_V U) !! tf_arg_idx 1 =
       Some v1]; [tf_w] is the total reader of the same word.)
     - the descriptor view [uvis_fd W] as [sts]: the table the NEW process
       starts with is the one the caller had, which is exactly the key's
       ([exec_slot_pre]'s [sts] rides straight into [exec_key U' sts na]).
   The ghost/logical parameters [P], [Pmiss], [Fo] and the slot piece's
   refund are EXISTENTIAL here: the U-mode contract cannot name the
   caller's era predicates, so the arm says only "some AU bundle at this
   key", and the dispatch route re-binds them when it consumes the bundle.

   THE KEY CONGRUENCE is [UexecSG.skey_eq]'s six rows: the bundle reads the
   image, argument word 1, the descriptor view and the working directory,
   and nothing else off its key.

   MONOTONICITY IN THE SLOT FAMILY is the one field whose proof is not a
   projection: the family occurs only as the CONCLUSION of the slot piece's
   wand, so the upgrader walks in under [sys_exec_slot_pre]'s ∀s and
   [PieceFam.pf_at]'s [∧]-refund.

   THE SUPPLY [ssupply] is [True] at this instance, and that is the honest
   reading: a generic process's exec bundle is FREE.
   [FsAbsInvFire.fsabs_exec_half] hands back the walk premise and open's
   commit at [True] receipts as a closed fact, and a generic slot family
   answers the slot wand at every key, so nothing has to be supplied.  The
   application's own predicate is what goes here once a syscall with a
   constraining contract is turned on.  That mint is also why this file sits
   ABOVE the fire tower rather than beside SpecSysExecAU.v: the supply law is
   a class field, and its exec case is that mint.

   [Γ] and [γfs] are NOT existential: the whole tree runs at the single
   ambient file system ([FsCfg.fsc_fs] with the derived view names
   [FsBytesGamma.fs_gamma_L fsc_fs]), exactly as [wp_sys_exec_sconf_body]
   pins them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import ProcGeom.       (* [tf_arg_idx]                        *)
Require Export SwtchCtx.
Require Import Xv6Cameras.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import UserFd.         (* [ufdG]                              *)
Require Import UexecSlot.      (* [uvis] / [tf_w]                     *)
Require Import UsysMemOk.      (* [USYS_exec] -- the one number with a bundle *)
Require Import UexecSG.        (* [uexecSG] / [uprogSG] -- the class   *)
Require Import UexecRet.       (* [uslot] -- the family the generic
                                  inhabitants mint at                 *)
Require Import SpecSysExecAU.  (* [sys_exec_au_pre]                   *)
Require Import SpecKexecAU.    (* [exec_slot_pre] -- the piece the
                                  monotonicity walks through          *)
Require Import FsAbsInvFire.   (* [fsabs_exec_half] -- the fs half of the
                                  bundle, free out of the invariant   *)
Require Import FirstTok.       (* [FirstTok.fsabs_env] -- THE SUPPLY   *)
Require Import PieceFam.       (* [pfam]: the one-shot piece's pair *)
Require Import FsAbsDefs.          (* LAST (FsAbs's own rule)             *)
Require Import FsBytesGamma.   (* [fs_gamma_L]                        *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Section UexecExecInst.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  (* NO AMBIENT [CurCtx], AND THAT IS A REQUIREMENT, not a convenience.  The
     instance is what [UexecRet.uslot] is indexed by, and [uslot] rides
     through the park ([ParkCap.park_token] reads it) and every other place
     two proofs at two hart contexts meet.  A context-indexed class makes
     those two slots DIFFERENT terms that print identically, and the unifier
     does not stop.  A process's deposit does not depend on the context of
     the kernel proof that consumes it, and the chain the exec bundle names
     ([SpecSysExecAU.sys_exec_au_pre] down to [SpecSysOpenAU]'s pieces) does
     not read one. *)
  Context `{GEN : GenId}.

  (* ================================================================== *)
  (* THE DEPOSIT'S FAMILIES, as one record.                               *)
  (*                                                                      *)
  (* One field per syscall whose contract takes caller-chosen families.    *)
  (* The arm binds the whole record ONCE in front of both legs, so what a  *)
  (* process gets back is a post at the very receipts and refunds it       *)
  (* deposited.  Exec's four are the only ones here -- its walk cursor and *)
  (* miss predicate, its observation pair, and the slot piece's refund --  *)
  (* because exec is the only number with a bundle at this round.          *)
  (*                                                                      *)
  (* NOT [Z]-INDEXED (UexecSG.v's header): a record makes [f] a plain      *)
  (* value with no dependency, which is what keeps the fixpoint's          *)
  (* contractivity proof and the trap route's transport free of [eq_rect]. *)
  (* ================================================================== *)
  Record xfam : Type := MkXfam {
    xf_P     : nat -> Z -> iProp Σ;
    xf_Pmiss : nat -> Z -> iProp Σ;
    xf_Fo    : pfam Σ (aview -> Z -> anode -> iProp Σ);
    xf_Rs    : iProp Σ;
  }.

  (* the point, for the arms that carry no deposit *)
  Definition xfam_pt : xfam :=
    MkXfam (fun _ _ => True%I) (fun _ _ => True%I)
           (pfam_triv (fun _ _ _ => True%I)) True%I.

  (* what the program hands over at its exec ecall, at the trapping key
     [W] and at ITS OWN families [f]; the bundle's slot wand concludes at
     [X], the recursive occurrence (see the header) *)
  Definition exec_sbundle (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      : iProp Σ :=
    (sys_exec_au_pre (MkPfam X (xf_Rs f)) (fs_gamma_L fsc_fs) fsc_fs
       (uvis_cwd W) (xf_P f) (xf_Pmiss f) (xf_Fo f)
       (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W))%I.

  Lemma exec_sbundle_ne (n : nat) :
    Proper (dist n ==> eq ==> eq ==> dist n) exec_sbundle.
  Proof.
    intros X Y HXY f ? <- W ? <-. rewrite /exec_sbundle.
    exact (sys_exec_au_pre_ne n X Y (xf_Rs f) (fs_gamma_L fsc_fs) fsc_fs
             (uvis_cwd W) (xf_P f) (xf_Pmiss f) (xf_Fo f)
             (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) HXY).
  Qed.

  Lemma exec_sbundle_cong (X : uvis -d> iPropO Σ) (f : xfam) (W W' : uvis) :
    uvis_M W = uvis_M W' ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = tf_w (uvis_tf W') (tf_arg_idx 1) ->
    uvis_fd W = uvis_fd W' ->
    uvis_cwd W = uvis_cwd W' ->
    exec_sbundle X f W ⊣⊢ exec_sbundle X f W'.
  Proof.
    intros HM Hav Hfd Hcw. rewrite /exec_sbundle HM Hav Hfd Hcw. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* THE CLASS INSTANCE.                                                     *)
  (*                                                                         *)
  (* [sbundle_at] is exec's bundle at 7 and [emp] at every other number:    *)
  (* ARM-a turns no other syscall's contract on, so no other number has a    *)
  (* deposit yet.  [spost_at] is [emp] everywhere -- exec's process never    *)
  (* resumes on success, and the numbers whose armed post is real are        *)
  (* ARM-b's.                                                                *)
  (* ===================================================================== *)
  Definition xv6_sbundle (X : uvis -d> iPropO Σ) (n : Z) (f : xfam) (W : uvis)
      : iProp Σ :=
    (if decide (n = USYS_exec) then exec_sbundle X f W else emp)%I.

  Definition xv6_spost (X : uvis -d> iPropO Σ) (n : Z) (f : xfam) (W : uvis)
      (r : mword 64) : iProp Σ := emp%I.

  Lemma xv6_sbundle_ne (k : nat) :
    Proper (dist k ==> eq ==> eq ==> eq ==> dist k) xv6_sbundle.
  Proof.
    intros X Y HXY n ? <- f ? <- W ? <-. rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _]; [ | reflexivity ].
    exact (exec_sbundle_ne k X Y HXY f f eq_refl W W eq_refl).
  Qed.

  Lemma xv6_spost_ne (k : nat) :
    Proper (dist k ==> eq ==> eq ==> eq ==> eq ==> dist k) xv6_spost.
  Proof. intros X Y _ n ? <- f ? <- W ? <- r ? <-. reflexivity. Qed.

  (* THE KEY CONGRUENCE, off [UexecSG.skey_eq]: exec's bundle reads the
     image, argument word 1 (argv), the descriptor view and the working
     directory, and [skey_eq] pins all four. *)
  Lemma xv6_sbundle_cong (X : uvis -d> iPropO Σ) (n : Z) (f : xfam)
      (W W' : uvis) :
    skey_eq W W' -> xv6_sbundle X n f W ⊣⊢ xv6_sbundle X n f W'.
  Proof.
    intros (HM & _ & Ha1 & _ & Hfd & Hcw). rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _]; [ | reflexivity ].
    exact (exec_sbundle_cong X f W W' HM Ha1 Hfd Hcw).
  Qed.

  Lemma xv6_spost_cong (X : uvis -d> iPropO Σ) (n : Z) (f : xfam)
      (W W' : uvis) (r : mword 64) :
    skey_eq W W' -> xv6_spost X n f W r ⊣⊢ xv6_spost X n f W' r.
  Proof. intros _. reflexivity. Qed.

  (* MONOTONICITY IN THE SLOT FAMILY.  The family occurs in exactly one
     place -- the CONCLUSION of the slot piece's wand ([exec_slot_pre]) --
     so the upgrader walks in under the piece's ∀s and its [∧]-refund. *)
  Lemma xv6_sbundle_mono (X Y : uvis -d> iPropO Σ) (n : Z) (f : xfam)
      (W : uvis) :
    ⊢ □ (∀ W' : uvis, X W' -∗ Y W') -∗
      xv6_sbundle X n f W -∗ xv6_sbundle Y n f W.
  Proof.
    iIntros "#Hup Hb". rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _]; [ | iExact "Hb" ].
    rewrite /exec_sbundle.
    rewrite /sys_exec_au_pre.
    iDestruct "Hb" as "(Hwalk & Hcommit & Hslot)".
    iFrame "Hwalk Hcommit".
    rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [ | iDestruct "Hslot" as "[_ $]" ].
    iDestruct "Hslot" as "[Hslot _]".
    rewrite /sys_exec_slot_pre.
    iIntros (na alen afun) "%Hsh".
    iDestruct ("Hslot" $! na alen afun with "[%]") as "Hslot"; [ exact Hsh | ].
    rewrite /exec_slot_pre.
    iIntros (av i ff nl W') "Ho %Hld %Him".
    iApply "Hup".
    iApply ("Hslot" $! av i ff nl W' with "Ho [%] [%]");
      [ exact Hld | exact Him ].
  Qed.

  (* THE SUPPLY.  Opaque in the class, and at THIS instance it is [True]:
     the only number with a bundle is exec, and exec's fs half comes out of
     [FsAbsInvFire.fsabs_exec_half], which is a closed fact -- it reads the
     abstract-state invariant's SHAPE and spends nothing, so a generic
     process's bundle costs the kernel nothing at all.  The application's
     own predicate is what goes here once a syscall with a constraining
     contract is turned on; until then there is nothing for a supplier to
     supply. *)
  Definition xv6_ssupply : iProp Σ := True%I.

  (* the half every ecall leaf uses: no other number has a bundle *)
  Lemma xv6_sbundle_of_supply_ne (X : uvis -d> iPropO Σ) (n : Z) (W : uvis) :
    n <> USYS_exec -> ⊢ □ xv6_ssupply ==∗ ∃ f : xfam, xv6_sbundle X n f W.
  Proof.
    intros Hne. iIntros "_ !>". iExists xfam_pt. rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [He | _];
      [ exfalso; exact (Hne He) | done ].
  Qed.

  (* ...and the half the generic inhabitants use: exec's bundle is the fs
     half out of the invariant beside the slot wand, and a generic family
     answers that wand at every key. *)
  Lemma xv6_sbundle_of_supply (X : uvis -d> iPropO Σ) (n : Z) (W : uvis) :
    ⊢ □ xv6_ssupply -∗ □ (∀ W' : uvis, X W') ==∗ ∃ f : xfam, xv6_sbundle X n f W.
  Proof.
    iIntros "_ #Hs !>". iExists xfam_pt. rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _]; [ | done ].
    rewrite /exec_sbundle /xfam_pt /=.
    (* read-kind only ([fsabs_exec_half]): the environment is carried, not
       spent *)
    iDestruct (fsabs_exec_half (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W))
      as "[#Hwalk #Hcommit]".
    rewrite /sys_exec_au_pre.
    iSplitR; [iExact "Hwalk" |].
    iSplitR; [iExact "Hcommit" |].
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [| done].
    rewrite /sys_exec_slot_pre. iIntros (na alen afun) "_".
    rewrite /exec_slot_pre. iIntros (av' i ff nl W') "_ _ _".
    iApply "Hs".
  Qed.

  Global Instance uexecSG_xv6 : uexecSG Σ :=
    {| sfam := xfam;
       sfam_pt := xfam_pt;
       sbundle_at := xv6_sbundle;
       spost_at := xv6_spost;
       sbundle_at_ne := xv6_sbundle_ne;
       spost_at_ne := xv6_spost_ne;
       sbundle_at_cong := xv6_sbundle_cong;
       spost_at_cong := xv6_spost_cong;
       sbundle_at_mono := xv6_sbundle_mono;
       ssupply := xv6_ssupply;
       sbundle_of_supply_ne := xv6_sbundle_of_supply_ne;
       sbundle_of_supply := xv6_sbundle_of_supply |}.

  (* ...AND THE GENERIC PROGRAM'S OWN DEPOSIT DATA ([UexecSG.uprogSG]): the
     supply itself, and every number admitted -- which is what makes the
     generic slot's minting law hold at every key ([sbundle_of_supply_ne] is
     the whole proof).  A verified program with a weaker supplier declares
     its own instance beside its constructor. *)
  Global Instance uprogSG_gen : uprogSG Σ :=
    {| Dsup := xv6_ssupply;
       psok := fun _ : Z => True |}.

  (* ...and the two at the class field, which is [exec_sbundle] at 7: what
     a consumer that speaks [UexecSG.sbundle_at] reads it back at.  The
     INTRO is at the families the caller chose (packed into the record);
     the ELIM is at the [∃] the family-free reader carries. *)
  Lemma sbundle_at_exec_intro (X : uvis -d> iPropO Σ) (W : uvis)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) :
    sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      P Pmiss Fo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) -∗
    sbundle_at X USYS_exec (MkXfam P Pmiss Fo Rs) W.
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite /exec_sbundle /=. iExact "H".
  Qed.

  Lemma sbundle_exec_intro (X : uvis -d> iPropO Σ) (W : uvis)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) :
    sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      P Pmiss Fo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) -∗
    sbundle X USYS_exec W.
  Proof.
    iIntros "H". rewrite /sbundle. iExists (MkXfam P Pmiss Fo Rs).
    iApply (sbundle_at_exec_intro X W P Pmiss Fo Rs with "H").
  Qed.

  Lemma sbundle_at_exec_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X USYS_exec f W -∗
    sys_exec_au_pre (MkPfam X (xf_Rs f)) (fs_gamma_L fsc_fs) fsc_fs
      (uvis_cwd W) (xf_P f) (xf_Pmiss f) (xf_Fo f)
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite /exec_sbundle. iExact "H".
  Qed.

  Lemma sbundle_exec_elim (X : uvis -d> iPropO Σ) (W : uvis) :
    sbundle X USYS_exec W -∗
    ∃ (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ),
      sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
        P Pmiss Fo
        (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W).
  Proof.
    iIntros "H". rewrite /sbundle. iDestruct "H" as (f) "H".
    iDestruct (sbundle_at_exec_elim X f W with "H") as "H".
    iExists (xf_P f), (xf_Pmiss f), (xf_Fo f), (xf_Rs f). iExact "H".
  Qed.

End UexecExecInst.
