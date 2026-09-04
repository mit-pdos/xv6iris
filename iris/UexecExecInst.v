(* UexecExecInst.v -- THE KERNEL-SIDE INSTANCE of the exec trap contract's
   payload family: [UexecRetExec.uexecXG] at [SpecSysExecAU]'s AU bundle.

   UexecRetExec.v states the enriched U-mode trap contract over an ambient
   class [uexecXG Σ] whose payload field
   [xbundle : (uvis -d> iPropO Σ) -> uvis -> iProp Σ] says what the
   program hands over at its exec ecall, AT THE RECURSIVE OCCURRENCE: the
   bundle's slot wand concludes at the fixpoint variable, so at the
   fixpoint it concludes at [uslot_x] -- the enriched slot the kernel
   returns for the new process.  The class is what keeps the whole
   U-mode fixpoint's cone clear of the fs tower.  THIS file is where
   the two meet, and it is deliberately a LEAF beside SpecSysExecAU.v (the
   spec it names) rather than anything the U-mode engine requires.

   WHAT THE BUNDLE IS.  [SpecSysExecAU.sys_exec_au_pre] at the TRAPPING
   KEY's own data:
     - the image [uvis_M W]: the arguments are read off the image the
       process trapped at ([wp_sys_exec_au_body] takes the bundle at
       [us_M U], and the trap-out key's image IS that image -- the loop
       hands [uvis_M W] to the dispatcher);
     - the argv pointer [tf_w (uvis_tf W) (tf_arg_idx 1)]: sys_exec's
       argument 1, read off the key's trapframe.  ([wp_sys_exec_au_body]
       names it [v1] and pins it by [pv_tf (us_V U) !! tf_arg_idx 1 =
       Some v1]; [tf_w] is the total reader of the same word, and the
       dispatch route (stage E2) is where the two are joined.)
     - the descriptor view [uvis_fd W] as [sts]: the table the NEW process
       starts with is the one the caller had, which is exactly the key's
       ([exec_slot_pre]'s [sts] rides straight into [exec_key U' sts na]).
   The three ghost/logical parameters [P], [Pmiss] and [Φo] are
   EXISTENTIAL here: the U-mode contract cannot name the caller's era
   predicates, so the arm says only "some AU bundle at this key", and the
   dispatch route re-binds them when it consumes the bundle.

   The class's two proof fields are paid here from SpecKexecAU's and
   SpecSysExecAU's own [_ne] lemmas (the slot predicate sits under wands
   and ∀/∃ only) and from the key congruence of the three projections.

   [Γ] and [γfs] are NOT existential: the whole tree runs at the single
   ambient file system ([FsCfg.fsc_fs] with the derived view names
   [FsBytesGamma.fs_gamma_L fsc_fs]), exactly as [wp_sys_exec_au_body]
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
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import FdSlots.
Require Import ProcGeom.       (* [tf_arg_idx]                        *)
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import Xv6Cameras.
Require Import BioDefs.
Require Import LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.
Require Import ByteBuf.
Require Import FsBlocks.
Require Import FsTree.
Require Import PathElems.
Require Import SpecKexec.
Require Import SpecSysExec.
Require Import ElfFile.
Require Import UmodeAbi.
Require Import UserFd.         (* [ufdG]                              *)
Require Import UexecSlot.      (* [uvis] / [tf_w]                     *)
Require Import UexecRet.       (* [uslot]                             *)
Require Import UexecRetExec.   (* [uexecXG] / [xbundle]               *)
Require Import SpecSysOpenAU.
Require Import SpecKexecAU.
Require Import SpecSysExecAU.  (* [sys_exec_au_pre]                   *)
Require Import FsAbsInv.
Require Import FsAbs.          (* LAST (FsAbs's own rule)             *)
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
  Context `{GEN : GenId} `{XI : CurCtx}.

  (* what the program hands over at its exec ecall, at the trapping key
     [W]; the bundle's slot wand concludes at [X], the recursive
     occurrence (header, and UexecRetExec.v's) *)
  Definition exec_xbundle (X : uvis -d> iPropO Σ) (W : uvis) : iProp Σ :=
    (∃ (P Pmiss : nat -> Z -> iProp Σ)
       (Φo : aview -> Z -> anode -> iProp Σ),
       sys_exec_au_pre X (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W) P Pmiss Φo
         (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W))%I.

  Lemma exec_xbundle_ne (n : nat) :
    Proper (dist n ==> eq ==> dist n) exec_xbundle.
  Proof.
    intros X Y HXY W ? <-. rewrite /exec_xbundle.
    apply bi.exist_ne; intros P. apply bi.exist_ne; intros Pmiss.
    apply bi.exist_ne; intros Φo.
    exact (sys_exec_au_pre_ne n X Y (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W) P Pmiss Φo
             (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) HXY).
  Qed.

  Lemma exec_xbundle_cong (X : uvis -d> iPropO Σ) (W W' : uvis) :
    uvis_M W = uvis_M W' ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = tf_w (uvis_tf W') (tf_arg_idx 1) ->
    uvis_fd W = uvis_fd W' ->
    uvis_cwd W = uvis_cwd W' ->
    exec_xbundle X W ⊣⊢ exec_xbundle X W'.
  Proof.
    intros HM Hav Hfd Hcw. rewrite /exec_xbundle HM Hav Hfd Hcw. reflexivity.
  Qed.

  Global Instance uexecXG_sysexec : uexecXG Σ :=
    {| xbundle := exec_xbundle;
       xbundle_ne := exec_xbundle_ne;
       xbundle_cong := exec_xbundle_cong |}.

  (* the intro: a caller holding a CONCRETE bundle -- its own era
     predicates, its own observation -- has the arm's payload *)
  Lemma xbundle_intro (X : uvis -d> iPropO Σ) (W : uvis)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) :
    sys_exec_au_pre X (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W) P Pmiss Φo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) -∗
    xbundle X W.
  Proof.
    iIntros "H". rewrite /xbundle /= /exec_xbundle.
    iExists P, Pmiss, Φo. iExact "H".
  Qed.

  (* ...and the elim, the shape the dispatch route (stage E2) reads the
     bundle back at *)
  Lemma xbundle_elim (X : uvis -d> iPropO Σ) (W : uvis) :
    xbundle X W -∗
    ∃ (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ),
      sys_exec_au_pre X (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W) P Pmiss Φo
        (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W).
  Proof. iIntros "H". rewrite /xbundle /= /exec_xbundle. iExact "H". Qed.

End UexecExecInst.
