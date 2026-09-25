(* ===================================================================== *)
(*  UShCatPay.v -- LANE EXEC-CAT, THE SUPPLY: sh's forked RIGHT child     *)
(*  runs /cat on the paid entry.                                          *)
(*                                                                       *)
(*  [UShEchoPay.v] is the mould: the U-tier exec rule                     *)
(*  ([ExecRun.udepw_at_refR_of_sup]) with sh's own supply plugged in --   *)
(*  the node read off the lent heap, the PIN as (W)'s supplier            *)
(*  ([ExecRun.exec_walk_of_pin] at [FsCatPin.era0_cat_pins], which        *)
(*  [AppPipeCons.pipe_cat_pins_acc] hands the pipeline claim), the        *)
(*  resolving arm as (E), the taint arm at the chosen payload, and the    *)
(*  refund -- the ledger fragment and the lend, WHOLE.                    *)
(*                                                                       *)
(*  THE ENTRY IS THE CALLER'S.  The supply ([sh_exec_sup_cat_of_entry],  *)
(*  section 7) takes cat's entry from its caller at every image the exec *)
(*  can produce; the pipeline hands over the tree route's                 *)
(*  ([UkPipeEntries.pe_cat_image_entry_qc_alloc]).  The earlier supply    *)
(*  that built the entry here out of cat's round ([cat_image_entry_1w]    *)
(*  over [UCatPipe.pcat_pay_at]) was deleted by the pipe sweep.           *)
(*                                                                       *)
(*  THE ARGUMENT READING IS NOT A RESTATEMENT OF THE WORD-LIST LAYER.     *)
(*  Every [line_ok] in [UShEcho]'s node layer ([echo_node_img],           *)
(*  [echo_args_det], [echo_uargv_shape]) is spent on facts the GENERAL    *)
(*  argument layer already has without it -- [ExecArgs.uargv_shape],      *)
(*  [uargv_img], [uargv_det] name no word list at all.  So the right      *)
(*  command's reading is short lemmas over [ExecArgs] (section 3) and no  *)
(*  word list appears in this file.  (A word-list reading at one word is  *)
(*  vacuous: [UkShCat.cat_line_premises_absurd] /                         *)
(*  [UkShCat.cat_line_head_absurd].)                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import RegFile.
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UexecSlot UexecRet.
Require Import UkRun UkRunLeaf.
Require Import UserHeap.
Require Import UserFd UserCwd.
Require Import ChildTok.
Require Import ByteBuf.
Require Import ElfFile ElfUser ElfLoadable.
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import PathElems ArgPath.
Require Import FsCfg.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import FsCatPin.
Require Import FileFsPure.
Require Import PinnedExec.
Require Import ExecEntry.
Require Import ExecArgs.
Require Import ExecRun.
Require Import SpecKexec SpecSysExec.
Require Import KexecDefs.
Require Import UexecExecInst.
Require Import UexecSG.
Require Import CtxIdDefs.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun UkShMain.
Require Import UkShDiag.
Require Import PipeDisc.
Require Import UserChildren.
Require User.ShSyms.
Require Import UShEcho.            (* [uargv_exec_of_cmd] / [uint_avi_moi] --
                                      the two general steps, which name no
                                      program and no word list *)
Require Import UkAbi.
Require Import UEchoKernel.   (* [uvis_argc] / [uvis_av] / [echo_arg] /
                                 [echo_args] -- the argument reading, which
                                 names no program *)
Require Import UkCat UkCatCat UkCatMain.
Require Import UShCat.             (* cat's image geometry, all of it
                                      [line_ok]-free except two lemmas this
                                      file replaces *)
Require Import UCodeCat.
Require Import UkShCat.            (* the (W) half this supply feeds *)
Require User.CatSyms.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  CAT'S PATH, AND THE PIN THAT RESOLVES IT                          *)
(*                                                                       *)
(*  [UShEcho]'s sections 1-2 at /cat.  argv[0] is the pipe line's right   *)
(*  word, whose three bytes are "cat"; the pin speaks of                  *)
(*  [FsCatPin.cat_path], a list of NAMES, and [PathElems.path_elems]      *)
(*  joins them.                                                          *)
(* ===================================================================== *)
Definition cat_pl : list (bv 8) := FsImgCheck.fname_cat.

Lemma cat_path_elems : path_elems cat_pl = FsCatPin.cat_path.
Proof using . vm_compute. reflexivity. Qed.

Lemma cat_pl_len : length cat_pl = 3%nat.
Proof using . reflexivity. Qed.

(* ...and the bytes ARE the command name the pipe line's right side
   spells ([UkShPipeLex.ushq_cat], through [UkShCat.cmd_cat]) -- which is
   what ties the pin to what sh actually passes to exec. *)
Lemma cat_pl_line (j : nat) :
  (j < 3)%nat -> cat_pl !!! j = UkShCat.cmd_cat !!! j.
Proof using .
  intro Hj.
  do 3 (destruct j as [| j]; [ vm_compute; reflexivity | ]). lia.
Qed.

Lemma cat_pl_shape : arg_path_shape cat_pl.
Proof using .
  split; [ vm_compute; reflexivity | ].
  intros j b Hj.
  destruct j as [| [| [| j]]]; cbn in Hj; try discriminate Hj;
    injection Hj as <-;
    (intro Hc; apply (f_equal bv_unsigned) in Hc;
     vm_compute in Hc; discriminate Hc).
Qed.

(* no byte of the command name is a NUL, which is what pins argv[0]'s
   LENGTH: a [bb_cstr] that stopped early would have to find one *)
Lemma cmd_cat_nonul (j : nat) :
  (j < 3)%nat -> UkShCat.cmd_cat !!! j <> (mword_of_int 0 : mword 8).
Proof using .
  intro Hj.
  do 3 (destruct j as [| j];
        [ intro Hc; apply (f_equal bv_unsigned) in Hc;
          vm_compute in Hc; discriminate Hc | ]). lia.
Qed.

Lemma sh_cat_pin_resolves :
  pin_resolves FsCatPin.era0_cat_pins FsImg.ROOTINO cat_pl
    [FsImg.ROOTINO; FsCatPin.CAT_INO] FsCatPin.CAT_INO
    ElfUser.cat_elf 1%nat.
Proof using .
  split_and!.
  - (* "cat" is RELATIVE, so the walk starts at the cwd -- the root *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (cat_pl !! 0%nat = Some PathElems.SLASH)); reflexivity.
  - rewrite cat_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite cat_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsCatPin.cat_bytes_elf. reflexivity.
Qed.

Section UShCatPay.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally): NO [Context {SG}] /
     [Context {PS}] here, exactly as in [UShEcho] and [UShEchoPay]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  (* ...EXCEPT [uprogSG], WHICH IS A SECTION VARIABLE (design SS4.3z item
     2, lane SH-PIPE-ROUND-11 finding (3)).  The entry this file's
     supply takes is the ENTERED PROGRAM's, and a verified
     program runs at its own deposit data ([UexecExecInst.uprogSG_free]),
     not at the ambient generic instance whose only [udep] producer is the
     taint.  Nothing is pinned here: the round instantiates at
     [uprogSG_free], the file era at its own, and every landed statement is
     byte-identical after [(PS := _)].  The DEPOSIT RULE this file applies
     ([ExecRun.udepw_at_refR_of_sup]) is [uprogSG]-FREE -- [UkRun.
     udepw_at_ref] names only [uslot] and [sbundle_pay_ref] -- so the
     conclusion [UkShCat.sh_exec_sup_cat_at] does not move either.
     [sh_cat_slot] below reads no instance at all and is unchanged. *)
  Context `{PS : UexecSG.uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  2.  THE INGREDIENTS -- [UShEcho.sh_echo_slot] at /cat               *)
  (* =================================================================== *)
  Definition sh_cat_slot (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FsCatPin.era0_cat_pins v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Global Instance sh_cat_slot_persistent T : Persistent (sh_cat_slot T).
  Proof using . rewrite /sh_cat_slot. apply _. Qed.

  (* ...AND THE ONE SEAM A PIPELINE ERA HAS TO MEET.  The claim's law is
     stated at the WHOLE of [FileFsPure.file_fs_pure] (that is what
     [AppPipeCons.pipe_fs_pure_acc] hands out, and [pipe_cat_pins_acc] is
     the same projection one level up), so this is the projection under
     the law's own box. *)
  Definition sh_cat_slot_of_fs_pure (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FileFsPure.file_fs_pure v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Lemma sh_cat_slot_of_fs_pure_holds (T : iProp Σ) :
    sh_cat_slot_of_fs_pure T -∗ sh_cat_slot T.
  Proof using .
    iIntros "(#Hinv & #Hcl & #Hgen)".
    rewrite /sh_cat_slot. iFrame "Hinv Hgen".
    iModIntro. iIntros (v) "Hp".
    iDestruct ("Hcl" $! v with "Hp") as "[$ [%Hpure | HT]]".
    - iLeft. iPureIntro. exact (FileFsPure.file_fs_pure_cat v Hpure).
    - iRight. iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  3.  THE RIGHT COMMAND'S READINGS, OVER [ExecArgs] AND NOTHING ELSE  *)
  (* =================================================================== *)

  (* THE SHAPE: one argument, three bytes, none of them a NUL, terminated
     by the cut's own zero.  [UShEcho.echo_uargv_shape] at one token --
     and with no [line_ok], because the two things that lemma spends it on
     (the word count and the line's length bound) are closed numbers
     here. *)
  Lemma cat_uargv_shape (a b : nat) (sv : Z) (gn : nat -> bv 8) :
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_shape (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)).
  Proof using .
    intros Hs0 Hbytes.
    pose proof (UkShCat.cat_argv_bytes_end a b gn Hbytes) as Hb3.
    destruct Hbytes as (_ & Hin & Hnul).
    rewrite UkShCat.cmd_cat_len in Hin.
    split.
    - rewrite UkShCat.cat_cmd_args_length. unfold MAXARG. lia.
    - intros i x Hi.
      assert (Hi0 : i = 0%nat).
      { pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
        rewrite UkShCat.cat_cmd_args_length in Hlt. lia. }
      subst i.
      rewrite (UkShCat.cat_cmd_args_lookup a b sv gn Hb3) in Hi.
      injection Hi as <-.
      cbn [UserHeap.ua_ptr UserHeap.ua_len UserHeap.ua_bytes].
      split_and!.
      + exact Hs0.
      + lia.
      + split.
        * intros j Hj. rewrite (Hin j Hj).
          exact (cmd_cat_nonul j Hj).
        * rewrite <- UShEcho.ubyte0_moi0. rewrite <- Hb3. exact Hnul.
  Qed.

  (* ...and the node IS a [uargv_exec], off the heap the deposit lends *)
  Lemma cat_uargv_exec_of_cmd (a b : nat) (gd : gname) (t sv : Z)
      (gn : nat -> bv 8) :
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    ush_cmd gd t (UkShCat.cat_cmd a b sv gn) -∗
    uargv_exec gd (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)).
  Proof using .
    intros Hs0 Hbytes. iIntros "#Hc".
    iApply (UShEcho.uargv_exec_of_cmd gd t
              (UkShMain.ush_args sv gn (UkShCat.cat_toks a b))
              (cat_uargv_shape a b sv gn Hs0 Hbytes)).
    rewrite /UkShCat.cat_cmd. iExact "Hc".
  Qed.

  (* THE PATH: argv[0]'s string IS "cat", terminated.
     [UShEcho.sh_echo_path_of_holds] at one token, read off the general
     layout rather than off a word-list summary. *)
  Lemma cat_path_of_holds (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) :
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    exec_path_of Mn (mword_of_int (sv + Z.of_nat a) : mword 64) cat_pl.
  Proof using .
    intros Hs0 Hbytes Himg.
    pose proof (UkShCat.cat_argv_bytes_end a b gn Hbytes) as Hb3.
    pose proof Hbytes as Hbb. destruct Hbb as (_ & Hin & Hnul).
    rewrite UkShCat.cmd_cat_len in Hin.
    destruct Himg as (_ & _ & Hhi & _ & _ & Hrow).
    pose proof (UkShCat.cat_cmd_args_lookup a b sv gn Hb3) as Hlk.
    pose proof (Hhi 0%nat _ Hlk) as Hz64.
    cbn [UserHeap.ua_ptr UserHeap.ua_len] in Hz64.
    pose proof (Hrow 0%nat _ Hlk) as Hbyte.
    cbn [UserHeap.ua_ptr UserHeap.ua_len UserHeap.ua_bytes] in Hbyte.
    split_and!.
    - exact cat_pl_shape.
    - intros j c Hj.
      assert (Hjl : (j < 3)%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
        rewrite cat_pl_len in Hlt. exact Hlt. }
      rewrite (UShEcho.uint_avi_moi (sv + Z.of_nat a) (Z.of_nat j)
                 ltac:(lia) ltac:(lia) ltac:(unfold Z64 in *; lia)).
      rewrite (Hbyte j ltac:(lia)).
      f_equal.
      rewrite <- (list_lookup_total_correct _ _ _ Hj).
      rewrite (cat_pl_line j Hjl). exact (Hin j Hjl).
    - rewrite cat_pl_len.
      rewrite (UShEcho.uint_avi_moi (sv + Z.of_nat a) (Z.of_nat 3%nat)
                 ltac:(lia) ltac:(lia) ltac:(unfold Z64 in *; lia)).
      rewrite (Hbyte 3%nat ltac:(lia)).
      f_equal. rewrite <- UShEcho.ubyte0_bv0. rewrite <- Hb3. exact Hnul.
  Qed.

  (* =================================================================== *)
  (*  7.  THE SUPPLY AT A CALLER'S ENTRY (lane REPOINT-PIPE; design       *)
  (*      program-specs SS3.4g)                                           *)
  (*                                                                     *)
  (*  The supply with the ENTRY abstracted (the pipe sweep deleted the    *)
  (*  form that built cat's entry itself out of a round): it takes it     *)
  (*  from the caller, at every image the                                 *)
  (*  exec can produce -- which is how the pipeline's round hands over    *)
  (*  the TREE-ROUTE entry ([UkPipeEntries.pe_cat_image_entry_qc_alloc])  *)
  (*  without this file naming the pipeline's instance.  What the         *)
  (*  supply reads off sh's node and ledger is exactly what that entry    *)
  (*  asks for: the node's two addresses under [2 ^ 38]                   *)
  (*  ([UkShCat.cat_cmd_addr], [UkShCat.cat_cmd_str]), the argv reading,  *)
  (*  the image, the table's length and the caller's rows [Fd0] at the    *)
  (*  table's standard slots.  The entry's [Pay] is the lend alone: the   *)
  (*  ledger fragment is spent at the exec (the new image has its own     *)
  (*  table), as at [UShEchoPipePay.sh_exec_sup_echo_pipe_of_entry].  No  *)
  (*  [udep]: only the deleted entry read it.                             *)
  (* =================================================================== *)
  Lemma sh_exec_sup_cat_of_entry
      (Fd0 : list fdstate -> Prop) (a b : nat)
      (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (Qc Cr : iProp Σ) :
    ⊢ □ (app_taint -∗ Qc) -∗
      □ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8)
           (sts : list fdstate) (cs : gset gname) (pidv : mword 32),
           ⌜0 < t < 2 ^ 38⌝ -∗ ⌜0 < s0 + Z.of_nat a < 2 ^ 38⌝ -∗
           ⌜UkShCat.cat_argv_bytes a b g⌝ -∗
           ⌜uargv_img M (t + 8)
              (UkShMain.ush_args s0 g (UkShCat.cat_toks a b))⌝ -∗
           ⌜length sts = NOFILE⌝ -∗ ⌜Fd0 (take NSTD sts)⌝ -∗
           UkRun.urun_nopipe sts -∗
           image_entry ElfUser.cat_elf M (mword_of_int (t + 8) : mword 64)
             sts FsImg.ROOTINO ProcDefs.secc_all cs pidv (fun _ : Z => Qc) Cr uslot) -∗
      sh_cat_slot T -∗
      UkShCat.sh_exec_sup_cat_at Fd0 a b (fun _ : Z => Qc) Cr.
  Proof using xv6G0 ghost_varG0 ghost_varG1 ufdG0 uartGhostG0.
    iIntros "#Hqt #Hent (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShCat.sh_exec_sup_cat_at.
    iIntros "!>" (N' m pc s0 t g ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd0 Hstd #Hcmd Hcr".
    (* ---- THE TAINT ARM: the generic slot at the chosen payload ---- *)
    iAssert (∀ sts, image_entry_taint T sts ProcDefs.secc_all (fun _ : Z => Qc) uslot)%I as "#Hgen'".
    { iIntros (sts). iApply image_entry_taint_intro. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! Qc W' with "HT Hmp Hqt"). }
    (* ---- ...AND THE REST IS THE U-TIER RULE. ---- *)
    iApply (udepw_at_refR_of_sup N' m pc
              (mword_of_int (s0 + Z.of_nat a)) (mword_of_int (t + 8))
              FsImg.ROOTINO T cat_pl ElfUser.cat_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I
              _ UShCat.cat_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    (* THE REFUND IS THE LEDGER AND THE LEND, WHOLE *)
    { iIntros "!> $". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iDestruct (cat_cmd_str a b (ukn_d N') t s0 g
                 (UkShCat.cat_argv_bytes_end a b g Hbytes) with "Hcmd")
      as "[%Hsa _]".
    iDestruct (cat_cmd_addr a b (ukn_d N') t s0 g with "Hcmd")
      as %[Hta _].
    iDestruct (cat_uargv_exec_of_cmd a b (ukn_d N') t s0 g
                 ltac:(lia) Hbytes with "Hcmd") as "#Hvec".
    iDestruct (uargv_img_of_uargv (ukn_t N') (ukn_d N') (ukn_s N') M pm sz
                 (t + 8) _ with "Hheap Hvec") as %Himg.
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro.
      exact (cat_path_of_holds a b M s0 t g ltac:(lia) Hbytes Himg). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsCatPin.era0_cat_pins T FsImg.ROOTINO
                cat_pl [FsImg.ROOTINO; FsCatPin.CAT_INO]
                FsCatPin.CAT_INO
                (MkAnode (AFile ElfUser.cat_elf) 1%nat) sh_cat_pin_resolves
                with "Hcl Hinv"). }
    iSplitR "Hstd Hcr".
    { rewrite Hpeq.
      iPoseProof ("Hent" $! M s0 t g fdv cs pidv
                    with "[%] [%] [%] [%] [%] [%] Hnp0") as "#He";
        [ exact Hta | exact Hsa | exact Hbytes | exact Himg | exact Hlen
        | rewrite Hl; exact Hfd0 | ].
      (* the ledger fragment is SPENT at the entry; the lend is the pay *)
      rewrite /image_entry.
      iIntros "!>" (na alen afun W')
        "%Hok %Hcw %Hlz %Hscw %Hch %Hpid %Hargs Hmp [_ Hc]".
      iApply ("He" $! na alen afun W'
               with "[%] [%] [%] [%] [%] [%] [%] Hmp Hc");
        [ exact Hok | exact Hcw | exact Hlz | exact Hscw | exact Hch | exact Hpid
        | exact Hargs ]. }
    iFrame "Hstd Hcr".
  Qed.

  (* ...AND THE CONSUMER TEST AT IT: the supply above feeds
     [UkShCat.wp_kshr_exec_cat_at_holds], and what comes out is a WP over
     sh's EXEC arm at the caller's entry *)
  Lemma wp_kshr_exec_cat_paid_of_entry (Fd0 : list fdstate -> Prop)
      (a b : nat) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (Qc Cr Cd : iProp Σ)
      (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
      (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat) :
    ukn_pay N = (fun _ : Z => Qc) ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    UkShCat.cat_argv_bytes a b g ->
    Fd0 ld ->
    UkSh.ush_fd2p ld ->
    ⊢ □ (app_taint -∗ Qc) -∗
      □ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8)
           (sts : list fdstate) (cs : gset gname) (pidv : mword 32),
           ⌜0 < t < 2 ^ 38⌝ -∗ ⌜0 < s0 + Z.of_nat a < 2 ^ 38⌝ -∗
           ⌜UkShCat.cat_argv_bytes a b g⌝ -∗
           ⌜uargv_img M (t + 8)
              (UkShMain.ush_args s0 g (UkShCat.cat_toks a b))⌝ -∗
           ⌜length sts = NOFILE⌝ -∗ ⌜Fd0 (take NSTD sts)⌝ -∗
           UkRun.urun_nopipe sts -∗
           image_entry ElfUser.cat_elf M (mword_of_int (t + 8) : mword 64)
             sts FsImg.ROOTINO ProcDefs.secc_all cs pidv (fun _ : Z => Qc) Cr uslot) -∗
      sh_cat_slot T -∗
      shk_code (ukn_t N) -∗
      UkShDiag.ush_execfail_law_at PipeDisc.alt_execR 16%nat Cr Cd -∗
      □ (Cd -∗ Qc) -∗
      ush_jtab (ukn_t N) -∗
      ush_cmd (ukn_d N) t (UkShCat.cat_cmd a b s0 g) -∗
      usz (ukn_s N) szv -∗
      UserFd.ustd (ukn_fd N) ld -∗
      UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
      UserChildren.uch_any (ukn_ch N) -∗
      Cr -∗
      urun N h m (mword_of_int ShSyms.runcmd)
        (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
      mWP (Loop : expr riscv_lang).
  Proof using xv6G0 ghost_varG0 ghost_varG1 ufdG0 uartGhostG0.
    intros Hpeq Ha0 Hbytes Hfd0 Hfd2.
    iIntros "#Hqt #Hent #Hslot #Hcode #Hxl #Hcd #Hjt #Htree
             Hsz Hstd Hcwd Hch Hcr Hrun".
    iPoseProof (sh_exec_sup_cat_of_entry Fd0 a b T Qc Cr
                  with "Hqt Hent Hslot") as "#Hsup".
    iApply (UkShCat.wp_kshr_exec_cat_at_holds Fd0 a b (fun _ : Z => Qc)
              Cr Cd N Hc h m t szv s0 g ld n
              Hpeq Ha0 Hbytes Hfd0 Hfd2
              with "Hcode Hsup Hxl [] Hjt Htree Hsz Hstd Hcwd Hch Hcr Hrun").
    iIntros "!> Hc". iApply ("Hcd" with "Hc").
  Qed.

End UShCatPay.
