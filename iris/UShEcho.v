(* ===================================================================== *)
(* UShEcho.v -- E4 SH-ECHO, THE APPLICATION HALF: sh's exec of /echo PAID *)
(* out of the echo application's claim, and what echo's own slot then     *)
(* promises about the four bytes it writes.                              *)
(*                                                                        *)
(* [UInitSh.v] is the mould one level up: init execs /sh on                *)
(* [FsShPin.era0_sh_pins] and answers exec's slot piece with               *)
(* [UShKernel.sh_slot_of_kexec].  This file is the same shape one level    *)
(* DOWN -- sh's forked child execs /echo on [FsEchoPin.era0_echo_pins] and *)
(* answers with echo's own entry -- and the two differences are worth      *)
(* naming:                                                                *)
(*                                                                        *)
(*  THE PATH IS NOT A CONSTANT.  init's "sh" is a literal in its rodata    *)
(*  ([UCodeInit.init_ro] at 0x9a8) and its argv a literal in its data, so  *)
(*  [UInitSh.init_args_det] is three [vm_compute]s over the dump.  sh's    *)
(*  "echo" is a run of the LINE BUFFER, cut by [nulterminate], and its     *)
(*  argv is a malloc'd node -- so the reading is off the NODE                *)
(*  ([UkShRun.ush_cmd], persistent) against the heap the deposit lends,     *)
(*  and the pure input is [UkShEcho.echo_argv_bytes] rather than a map      *)
(*  equation.                                                              *)
(*                                                                        *)
(*  ECHO'S ENTRY IS KEY-LEVEL, NOT EXEC-LEVEL.                             *)
(*  [UShKernel.sh_slot_of_kexec] exists; echo has no twin.                 *)
(*  [UEchoKernel.echo_uexec_slot] states its nine premises about the KEY    *)
(*  (that is what makes [UexecCond.echo_gate] decidable), and what the      *)
(*  exec channel offers is [SpecKexec.kexec_image_ok] -- so the bridge      *)
(*  [echo_slot_of_kexec] below is E4's own piece, and it is the one place   *)
(*  where [kexec_args_at] (the argument block kexec BUILT) has to produce   *)
(*  [UkAbi.uk_args_c] (the argument block echo READS).                      *)
(*                                                                        *)
(* PHASE 1.  Statements, in the vocabulary the landed lemmas speak; the    *)
(* closed facts about the image and the pin are PROVED.  Nothing is        *)
(* [Admitted], nothing is a placeholder premise.                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import RegFile.           (* [regfile] *)
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf.   (* [uv_avi_pos] *)
Require Import UserFd UserCwd UserChildren.
Require Import ChildTok.
Require Import ElfFile ElfUser ElfLoadable.
Require Import PathElems FsTree FsBlocks FsBytesGamma.
Require Import FsCfg.             (* [fsc_fs] -- the era's file-system names *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import WpMmodeLeafBase.   (* [csp_rs1] *)
Require Import UmodeArith UmodeAbi.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import PinnedObs PinnedExec.
Require Import FsEchoPin.
Require Import ByteBuf.           (* [bb_cstr] / [bb_nonul] *)
Require Import ArgPath.           (* [arg_path_shape] / [arg_path_of] *)
Require Import SpecKexec SpecSysExec SpecCopyin SpecCopyinstr.
Require Import UInitSh.           (* [img_word_of_bytes] / [uimg_word_det] *)
Require Import KexecDefs.
Require Import UkAbi.
Require Import UexecSG UexecExecInst UexecExecMint.
Require Import UCodeEcho.
Require Import UkEcho UEchoKernel.
Require Import UkSh UkShRun UkShEcho.
Require Import UConsLine EchoDisc.
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  1.  THE PATH sh PASSES, as a byte list                                *)
(*                                                                        *)
(*  argv[0] is the line's first token, whose four bytes are "echo"; the    *)
(*  pin speaks of [FsEchoPin.echo_path], a list of NAMES.  As at "sh",     *)
(*  [PathElems.path_elems] joins them and the join is the identity on the  *)
(*  bytes, so the byte list is spelled AS the name.                        *)
(* ===================================================================== *)
Definition echo_pl : list (bv 8) := FsImgCheck.fname_echo.

Lemma echo_path_elems : path_elems echo_pl = FsEchoPin.echo_path.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_pl_len : length echo_pl = 4%nat.
Proof. reflexivity. Qed.

(* ...and the bytes are the disciplined line's first token, which is what
   ties the pin to what sh actually passes ([UkShEcho.echo_argv_bytes] at
   [i = 0]). *)
Lemma echo_pl_line (j : nat) :
  (j < 4)%nat -> echo_pl !!! j = echo_line !!! j.
Proof.
  intro Hj.
  do 4 (destruct j as [| j]; [ vm_compute; reflexivity | ]). lia.
Qed.

(* ...and no byte of the line is a NUL, which is what pins each argument's
   LENGTH: a [bb_cstr] that stopped early would have to find one. *)
Lemma echo_line_nonul (j : nat) : (j < 17)%nat -> echo_line !!! j <> ubyte0.
Proof.
  intro Hj.
  do 17 (destruct j as [| j];
         [ intro Hc; apply (f_equal bv_unsigned) in Hc;
           vm_compute in Hc; discriminate Hc | ]).
  exfalso. lia.
Qed.

Lemma ubyte0_bv0 : ubyte0 = (bv_0 8 : bv 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ubyte0_moi0 : ubyte0 = (mword_of_int 0 : mword 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma echo_pl_shape : arg_path_shape echo_pl.
Proof.
  split; [ vm_compute; reflexivity | ].
  intros j b Hj.
  destruct j as [| [| [| [| j]]]]; cbn in Hj; try discriminate Hj;
    injection Hj as <-;
    (intro Hc; apply (f_equal bv_unsigned) in Hc;
     vm_compute in Hc; discriminate Hc).
Qed.

(* the ONE piece of address arithmetic every reading below needs: the
   machine's own index [uint (add_vec_int (mword_of_int a) d)] IS [a + d]
   when neither wraps, and nothing a program owns does ([UserHeap.uheap]
   puts every owned address under [2 ^ 38]). *)
Lemma uint_avi_moi (a d : Z) :
  0 <= a -> 0 <= d -> a + d < Z64 ->
  uint (add_vec_int (mword_of_int a : mword 64) d) = a + d.
Proof.
  intros Ha Hd Had.
  assert (Hb : bv_unsigned (mword_of_int a : mword 64) = a)
    by (rewrite <- uint_unsigned; apply uint_moi; unfold Z64 in *; lia).
  rewrite uint_unsigned.
  rewrite (uv_avi_pos (mword_of_int a : mword 64) d Hd
             ltac:(rewrite Hb; exact Had)).
  rewrite Hb. reflexivity.
Qed.

(* ===================================================================== *)
(*  2.  THE PIN RESOLVES, at the child's cwd                              *)
(* ===================================================================== *)
Lemma sh_echo_pin_resolves :
  pin_resolves FsEchoPin.era0_echo_pins FsImg.ROOTINO echo_pl
    [FsImg.ROOTINO; FsEchoPin.ECHO_INO] FsEchoPin.ECHO_INO
    ElfUser.echo_elf 1%nat.
Proof.
  split_and!.
  - (* "echo" is RELATIVE, so the walk starts at the cwd -- the root *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (echo_pl !! 0%nat = Some PathElems.SLASH)); reflexivity.
  - rewrite echo_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite echo_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsEchoPin.echo_bytes_elf. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  /echo IS A FILE xv6's exec LOADS                                  *)
(*                                                                        *)
(*  [ElfLoadable.v]'s two instances at the third image.  It belongs        *)
(*  BESIDE them; it is here in phase 1 only so that stating E4 costs no    *)
(*  rebuild of the cone above [ElfLoadable.v], and moving it is a phase-2  *)
(*  line.                                                                 *)
(* ===================================================================== *)
Lemma echo_elf_loadable : kexec_loadable ElfUser.echo_elf.
Proof.
  unfold kexec_loadable.
  split; [ exact ElfUser.echo_elf_wf | ].
  split; [ apply ehdr_phoff_of_b; vm_compute; reflexivity | ].
  split; [ apply phdrs_loadable_of_b; vm_compute; reflexivity
         | apply loads_ascending_of_b; vm_compute; reflexivity ].
Qed.

Lemma echo_anode_loadable (nl : nat) :
  anode_loadable (MkAnode (AFile ElfUser.echo_elf) nl).
Proof.
  exists ElfUser.echo_elf, nl.
  split; [ reflexivity | exact echo_elf_loadable ].
Qed.

(* ===================================================================== *)
(*  3a. THE IMAGE exec BUILDS FOR /echo, as two numbers                   *)
(*                                                                        *)
(*  echo's PT_LOADs are (0, 0xdcc, R-X) and (0x1000, 0x20, RW-), so the   *)
(*  loaded top is [pgroundup 0x1020 = 0x2000] and the new [p->sz] is that *)
(*  plus the guard and the stack page.  Everything the room condition     *)
(*  needs is closed arithmetic over these two.                            *)
(* ===================================================================== *)
Lemma echo_kexec_top : kexec_top ElfUser.echo_elf = 0x2000.
Proof. unfold kexec_top. rewrite ElfUser.echo_elf_end. reflexivity. Qed.

Lemma echo_kexec_sz : kexec_sz ElfUser.echo_elf = 0x4000.
Proof. unfold kexec_sz. rewrite echo_kexec_top. reflexivity. Qed.

(* THE ROOM echo's entry needs, at the arguments sh passes: twelve words
   below the entry sp, which lands at 0x3FB0 -- 0xFB0 above the stack
   page's base.  [UInitSh.init_sh_room] is the same closed computation for
   sh's frames at init's one argument. *)
Lemma echo_sp_final (alen : nat -> nat) :
  alen 0%nat = 4%nat -> alen 1%nat = 5%nat -> alen 2%nat = 5%nat ->
  kxc_sp_final 0x4000 alen 3%nat = 0x3FB0.
Proof.
  intros H0 H1 H2. unfold kxc_sp_final. cbn [kxc_sp].
  rewrite H0 H1 H2. vm_compute. reflexivity.
Qed.

Lemma echo_room (alen : nat -> nat) :
  alen 0%nat = 4%nat -> alen 1%nat = 5%nat -> alen 2%nat = 5%nat ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen 3%nat.
Proof.
  intros H0 H1 H2. rewrite echo_kexec_sz. rewrite (echo_sp_final alen H0 H1 H2).
  unfold PGSIZE. lia.
Qed.

Section UShEcho.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally): NO [Context {SG}] /
     [Context {PS}] here, exactly as in [UInitSh]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* [UserHeap.uheap_ubytes_img] at ANY dfrac.  The node's runs are all
     [DfracDiscarded] -- that is what makes the tree persistent and lets it
     cross sh's fork -- so the owned-run form cannot read them. *)
  Lemma uheap_ubytesq_img (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    uheap gt gd gs M pm sz -∗ ubytesq gd dq a n f -∗
    ⌜ forall k : nat, (k < n)%nat -> M !! (a + Z.of_nat k)%Z = Some (f k) ⌝.
  Proof.
    iIntros "Hheap Hbs".
    iInduction n as [ | k IH ] "IH" forall (f).
    { iPureIntro. intros j Hj. exfalso. lia. }
    rewrite /ubytesq seq_S big_sepL_app /=.
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    iDestruct ("IH" $! f with "Hheap Hlo") as %Hlo.
    iDestruct (uheap_ubyte with "Hheap Hhi") as %(HM & _ & _).
    iPureIntro. intros j Hj.
    destruct (decide (j = k)) as [-> | Hne];
      [ exact HM | exact (Hlo j ltac:(lia)) ].
  Qed.

  (* ...and the word form, in the spelling [SpecCopyin.uimg_word_at] and
     [UInitSh.img_word_of_bytes] take. *)
  Lemma uheap_uwordq_img (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a z : Z) :
    uheap gt gd gs M pm sz -∗
    uwordq gd dq a (mword_of_int z : mword 64) -∗
    ⌜ forall k : nat, (k < 8)%nat ->
        M !! (a + Z.of_nat k)%Z = bv_to_little_endian 8 8 z !! k ⌝.
  Proof.
    iIntros "Hheap Hw". rewrite /uwordq.
    iDestruct (uheap_ubytesq_img with "Hheap Hw") as %Hb.
    iPureIntro. exact (img_word_of_bytes M a z Hb).
  Qed.

  (* =================================================================== *)
  (*  4.  THE INGREDIENTS -- [UInitSh.init_sh_slot] at /echo              *)
  (*                                                                      *)
  (*  Three persistent pieces and no [Pay]: the file-system invariant, the *)
  (*  duplicating claim law at [FsEchoPin.era0_echo_pins], and the taint's *)
  (*  generic slot.  init's fourth conjunct is sh's entry payload          *)
  (*  ([UInitSh.sh_pay]); echo's entry takes NO application-supplied       *)
  (*  resource -- its argv comes off the key and its one deposit is        *)
  (*  [UkRun.udepw_law 16] (E5) -- so [PinnedExec]'s linear [Pay] is [emp] *)
  (*  at this instance and nothing crosses the exec but the key.           *)
  (* =================================================================== *)
  Definition sh_echo_slot (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FsEchoPin.era0_echo_pins v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗ R -∗ uslot W))%I.

  Global Instance sh_echo_slot_persistent T : Persistent (sh_echo_slot T).
  Proof. rewrite /sh_echo_slot. apply _. Qed.

  (* =================================================================== *)
  (*  5.  THE TWO READINGS OF SH'S OWN IMAGE                              *)
  (*                                                                      *)
  (*  [PinnedExec.pinned_exec_bundle]'s two pure inputs, at sh's key.      *)
  (*  Both are read off the NODE (persistent, [DfracDiscarded]) against    *)
  (*  the heap [UkRun.udepw_at] lends the supplier -- the loan is the      *)
  (*  whole reason [udepw_at] hands the authorities over and takes them    *)
  (*  back (UkRun.v, the note at [udepw_at]).                              *)
  (* =================================================================== *)

  (* THE NODE, AS A FACT ABOUT THE IMAGE.  Both readings below are PURE,
     and they have to be: they are consumed inside [PinnedExec]'s
     PERSISTENT constructor wand, which cannot hold the heap.  So the heap
     is read ONCE, here, into the pure summary [echo_node_img] -- exactly
     what [UInitSh] gets for free from [uimg_sub UCodeInit.init_argv_map M]
     at a CONSTANT image and has to be extracted for a malloc'd one. *)
  Definition echo_node_img (M : gmap Z (bv 8)) (s0 t : Z)
      (g : nat -> bv 8) : Prop :=
    0 < t < 2 ^ 38
    /\ (forall i : nat, (i < 3)%nat ->
          0 < s0 + Z.of_nat (UkShEcho.echo_off i) < 2 ^ 38)
    /\ (forall i : nat, (i < 3)%nat -> forall k : nat, (k < 8)%nat ->
          M !! (t + 8 + 8 * Z.of_nat i + Z.of_nat k)
          = bv_to_little_endian 8 8
              (s0 + Z.of_nat (UkShEcho.echo_off i)) !! k)
    /\ (forall k : nat, (k < 8)%nat ->
          M !! (t + 8 + 8 * Z.of_nat 3%nat + Z.of_nat k)
          = bv_to_little_endian 8 8 0 !! k)
    /\ (forall i : nat, (i < 3)%nat ->
          forall j : nat, (j < UkShEcho.echo_alen i)%nat ->
            M !! (s0 + Z.of_nat (UkShEcho.echo_off i) + Z.of_nat j)
            = Some (g (UkShEcho.echo_off i + j)%nat))
    /\ (forall i : nat, (i < 3)%nat ->
          M !! (s0 + Z.of_nat (UkShEcho.echo_off i)
                + Z.of_nat (UkShEcho.echo_alen i)) = Some ubyte0).

  (* ...and the ONE place the heap is touched: the deposit's loan
     ([UkRun.udepw_at] hands the supplier the two authorities and takes
     them back), read against the node's own persistent runs. *)
  Lemma echo_node_img_of_cmd (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8) :
    uheap gt gd gs M pm sz -∗ ush_cmd gd t (UkShEcho.echo_cmd s0 g) -∗
    ⌜ echo_node_img M s0 t g ⌝.
  Proof.
    iIntros "Hheap #Hc".
    iDestruct (UkShEcho.echo_cmd_addr with "Hc") as %[Htr _].
    iDestruct (UkShEcho.echo_cmd_word gd t s0 g 0%nat ltac:(lia) with "Hc")
      as "#Hw0".
    iDestruct (uheap_uwordq_img with "Hheap Hw0") as %Hb0.
    iDestruct (UkShEcho.echo_cmd_word gd t s0 g 1%nat ltac:(lia) with "Hc")
      as "#Hw1".
    iDestruct (uheap_uwordq_img with "Hheap Hw1") as %Hb1.
    iDestruct (UkShEcho.echo_cmd_word gd t s0 g 2%nat ltac:(lia) with "Hc")
      as "#Hw2".
    iDestruct (uheap_uwordq_img with "Hheap Hw2") as %Hb2.
    iDestruct (UkShEcho.echo_cmd_cap gd t s0 g with "Hc") as "#Hwc".
    iDestruct (uheap_uwordq_img with "Hheap Hwc") as %Hbc.
    iDestruct (UkShEcho.echo_cmd_str gd t s0 g 0%nat ltac:(lia) with "Hc")
      as "[%Hr0 #Hs0]".
    iDestruct (UkShEcho.echo_cmd_str gd t s0 g 1%nat ltac:(lia) with "Hc")
      as "[%Hr1 #Hs1]".
    iDestruct (UkShEcho.echo_cmd_str gd t s0 g 2%nat ltac:(lia) with "Hc")
      as "[%Hr2 #Hs2]".
    iDestruct "Hs0" as "(_ & _ & Hbs0 & Hnl0)".
    iDestruct "Hs1" as "(_ & _ & Hbs1 & Hnl1)".
    iDestruct "Hs2" as "(_ & _ & Hbs2 & Hnl2)".
    iDestruct (uheap_ubytesq_img with "Hheap Hbs0") as %Hg0.
    iDestruct (uheap_ubytesq_img with "Hheap Hbs1") as %Hg1.
    iDestruct (uheap_ubytesq_img with "Hheap Hbs2") as %Hg2.
    iDestruct (uheap_ubyte with "Hheap Hnl0") as %(Hz0 & _ & _).
    iDestruct (uheap_ubyte with "Hheap Hnl1") as %(Hz1 & _ & _).
    iDestruct (uheap_ubyte with "Hheap Hnl2") as %(Hz2 & _ & _).
    iPureIntro. split_and!.
    - lia.
    - lia.
    - intros i Hi; destruct i as [| [| [| i]]];
        [ exact Hr0 | exact Hr1 | exact Hr2 | exfalso; lia ].
    - intros i Hi; destruct i as [| [| [| i]]];
        [ exact Hb0 | exact Hb1 | exact Hb2 | exfalso; lia ].
    - exact Hbc.
    - intros i Hi; destruct i as [| [| [| i]]];
        [ exact Hg0 | exact Hg1 | exact Hg2 | exfalso; lia ].
    - intros i Hi; destruct i as [| [| [| i]]];
        [ exact Hz0 | exact Hz1 | exact Hz2 | exfalso; lia ].
  Qed.

  (* THE PATH: argv[0]'s string IS "echo", terminated. *)
  Definition sh_echo_path_of : Prop :=
    forall (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8),
      echo_node_img M s0 t g ->
      UkShEcho.echo_argv_bytes g ->
      exec_path_of M (mword_of_int s0 : mword 64) echo_pl.

  Lemma sh_echo_path_of_holds : sh_echo_path_of.
  Proof.
    intros M s0 t g (_ & Hri & _ & _ & Hgi & Hzi) Hbytes.
    pose proof (Hri 0%nat ltac:(lia)) as Hr.
    cbn [UkShEcho.echo_off] in Hr. rewrite Z.add_0_r in Hr.
    assert (Hn4 : M !! (s0 + 4) = Some (bv_0 8)).
    { rewrite <- ubyte0_bv0.
      replace (s0 + 4)
        with (s0 + Z.of_nat (UkShEcho.echo_off 0%nat)
              + Z.of_nat (UkShEcho.echo_alen 0%nat))
        by (cbn [UkShEcho.echo_off UkShEcho.echo_alen]; lia).
      exact (Hzi 0%nat ltac:(lia)). }
    split_and!.
    - exact echo_pl_shape.
    - intros j b Hj.
      assert (Hjl : (j < 4)%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
        rewrite echo_pl_len in Hlt. exact Hlt. }
      rewrite (uint_avi_moi s0 (Z.of_nat j) ltac:(lia) ltac:(lia)
                 ltac:(unfold Z64; lia)).
      replace (s0 + Z.of_nat j)
        with (s0 + Z.of_nat (UkShEcho.echo_off 0%nat) + Z.of_nat j)
        by (cbn [UkShEcho.echo_off]; lia).
      rewrite (Hgi 0%nat ltac:(lia) j
                 ltac:(cbn [UkShEcho.echo_alen]; lia)).
      f_equal.
      rewrite <- (list_lookup_total_correct _ _ _ Hj).
      rewrite (echo_pl_line j Hjl).
      exact (proj1 Hbytes 0%nat j ltac:(lia)
               ltac:(cbn [UkShEcho.echo_alen]; lia)).
    - rewrite echo_pl_len.
      rewrite (uint_avi_moi s0 (Z.of_nat 4%nat) ltac:(lia) ltac:(lia)
                 ltac:(unfold Z64; lia)).
      replace (s0 + Z.of_nat 4%nat) with (s0 + 4) by lia.
      exact Hn4.
  Qed.

  (* THE VECTOR: sh's arguments are DETERMINED by the node it built.
     [UInitSh.init_args_det] is this lemma at init's constant image; the
     conclusion is stronger here because echo's entry reads the BYTES and
     not only the count and the lengths. *)
  Definition echo_args_det : Prop :=
    forall (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8)
           (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
      echo_node_img M s0 t g ->
      UkShEcho.echo_argv_bytes g ->
      exec_args_of M (mword_of_int (t + 8) : mword 64) na alen afun ->
      na = 3%nat
      /\ (forall i : nat, (i < 3)%nat -> alen i = UkShEcho.echo_alen i)
      /\ (forall i j : nat, (i < 3)%nat -> (j < UkShEcho.echo_alen i)%nat ->
            afun i j = echo_line !!! (UkShEcho.echo_off i + j)%nat).

  Lemma echo_args_det_holds : echo_args_det.
  Proof.
    intros M s0 t g na alen afun
      (Htr & Hri & Hword & Hbc & Hgi & Hzi) Hbytes Hargs.
    destruct Hargs as (Hshape & avf & Hptr & Hnz & Hnul & Hstr).
    destruct Hshape as (_ & Hcstr & Hlen4k).
    (* ---- the key's argv address, unwrapped ---- *)
    assert (Ea : forall i : nat, (i <= 3)%nat ->
              uint (add_vec_int (mword_of_int (t + 8) : mword 64)
                      (8 * Z.of_nat i)) = t + 8 + 8 * Z.of_nat i)
      by (intros i Hi; apply uint_avi_moi; unfold Z64; lia).
    (* ---- THE COUNT ---- *)
    assert (Hna : na = 3%nat).
    { destruct (decide (na < 3)%nat) as [Hlt | Hge].
      - exfalso.
        pose proof (Hptr na (Nat.le_refl na)) as Hw.
        rewrite (Ea na ltac:(lia)) in Hw.
        pose proof (Hri na Hlt) as Hrr.
        pose proof (uimg_word_det M (t + 8 + 8 * Z.of_nat na) (avf na)
                      (s0 + Z.of_nat (UkShEcho.echo_off na))
                      ltac:(lia) Hw (Hword na Hlt)) as Hv.
        assert (Hcz : (mword_of_int (s0 + Z.of_nat (UkShEcho.echo_off na))
                       : mword 64) = mword_of_int 0)
          by (rewrite <- Hv; exact Hnul).
        apply (f_equal uint) in Hcz.
        rewrite (uint_moi (s0 + Z.of_nat (UkShEcho.echo_off na))
                   ltac:(unfold Z64; lia)) in Hcz.
        rewrite (uint_moi 0 ltac:(unfold Z64; lia)) in Hcz.
        lia.
      - destruct (decide (na = 3%nat)) as [He | Hne];
          [ exact He | exfalso ].
        pose proof (Hptr 3%nat ltac:(lia)) as Hw.
        rewrite (Ea 3%nat ltac:(lia)) in Hw.
        exact (Hnz 3%nat ltac:(lia)
                 (uimg_word_det M (t + 8 + 8 * Z.of_nat 3%nat) (avf 3%nat) 0
                    ltac:(lia) Hw Hbc)). }
    subst na.
    (* ---- THE THREE POINTERS ---- *)
    assert (Hpi : forall i : nat, (i < 3)%nat ->
              avf i = (mword_of_int (s0 + Z.of_nat (UkShEcho.echo_off i))
                       : mword 64)).
    { intros i Hi.
      pose proof (Hptr i ltac:(lia)) as Hw. rewrite (Ea i ltac:(lia)) in Hw.
      pose proof (Hri i Hi) as Hrr.
      exact (uimg_word_det M (t + 8 + 8 * Z.of_nat i) (avf i)
               (s0 + Z.of_nat (UkShEcho.echo_off i)) ltac:(lia) Hw
               (Hword i Hi)). }
    (* ---- WHAT THE COPY LOOP READ, at the node's own addresses ---- *)
    assert (Hsi : forall i : nat, (i < 3)%nat ->
              forall j : nat, (j <= alen i)%nat ->
                M !! (s0 + Z.of_nat (UkShEcho.echo_off i) + Z.of_nat j)
                = Some (afun i j)).
    { intros i Hi j Hj.
      pose proof (Hstr i ltac:(lia)) as Hs. rewrite (Hpi i Hi) in Hs.
      pose proof (Hs j Hj) as Hsj.
      pose proof (Hri i Hi) as Hrr.
      pose proof (Hlen4k i ltac:(lia)) as H4k.
      rewrite (uint_avi_moi (s0 + Z.of_nat (UkShEcho.echo_off i)) (Z.of_nat j)
                 ltac:(lia) ltac:(lia) ltac:(unfold Z64; lia)) in Hsj.
      exact Hsj. }
    (* ---- THE THREE LENGTHS ---- *)
    assert (Halen : forall i : nat, (i < 3)%nat ->
              alen i = UkShEcho.echo_alen i).
    { intros i Hi.
      destruct (Hcstr i ltac:(lia)) as [Hno Hnl].
      destruct (decide (alen i < UkShEcho.echo_alen i)%nat) as [Hlt | Hge].
      - exfalso.
        pose proof (Hsi i Hi (alen i) (Nat.le_refl _)) as Hm1.
        rewrite Hnl in Hm1.
        pose proof (Hgi i Hi (alen i) Hlt) as Hm2.
        rewrite Hm1 in Hm2. injection Hm2 as Hm2.
        pose proof (proj1 Hbytes i (alen i) Hi Hlt) as Hgl.
        assert (Hidx : (UkShEcho.echo_off i + alen i < 17)%nat)
          by (destruct i as [| [| i]];
              cbn [UkShEcho.echo_off UkShEcho.echo_alen] in *; lia).
        apply (echo_line_nonul _ Hidx).
        rewrite <- Hgl, <- Hm2. exact (eq_sym ubyte0_moi0).
      - destruct (decide (alen i = UkShEcho.echo_alen i)) as [He | Hne];
          [ exact He | exfalso ].
        pose proof (Hno (UkShEcho.echo_alen i) ltac:(lia)) as Hnn.
        pose proof (Hsi i Hi (UkShEcho.echo_alen i) ltac:(lia)) as Hm1.
        pose proof (Hzi i Hi) as Hm2.
        rewrite Hm1 in Hm2. injection Hm2 as Hm2.
        apply Hnn. rewrite Hm2. exact ubyte0_moi0. }
    (* ---- ...AND THE BYTES ---- *)
    split_and!; [ reflexivity | exact Halen | ].
    intros i j Hi Hj.
    pose proof (Hsi i Hi j ltac:(rewrite (Halen i Hi); lia)) as Hm1.
    pose proof (Hgi i Hi j Hj) as Hm2.
    rewrite Hm1 in Hm2. injection Hm2 as Hm2.
    rewrite Hm2. exact (proj1 Hbytes i j Hi Hj).
  Qed.


  (* =================================================================== *)
  (*  6.  ECHO'S ENTRY AT THE EXEC CHANNEL                                *)
  (*                                                                      *)
  (*  [UShKernel.sh_slot_of_kexec]'s twin, and the piece E4 owes that sh's *)
  (*  lane never needed: [UEchoKernel.echo_uexec_slot] asks for            *)
  (*  [UkAbi.uk_args_c] and the two presence rows about the argument area, *)
  (*  and what [SpecKexec.kexec_image_ok] gives is [kexec_args_at] -- the  *)
  (*  strings at [kxc_sp top alen (S i)], the NULs after them and the      *)
  (*  [na + 1]-word vector at [kxc_sp_final].  Turning the second into the *)
  (*  first is the whole content of this obligation; the rest             *)
  (*  (entry pc, the text inclusion, the X-and-not-W page, the frame's     *)
  (*  zeroed bytes, the fd length, the map stop) is [sh_slot_of_kexec]'s   *)
  (*  derivation verbatim.                                                *)
  (*                                                                      *)
  (*  THE ROOM PREMISE is echo's 96 bytes (twelve words below the entry    *)
  (*  sp) where sh's is [2 + (8 + (16 + (ush_Dbody + n0)))] words; the     *)
  (*  supplier closes it by closed arithmetic at [na = 3] and             *)
  (*  [alen = 4, 5, 5] ([UInitSh.init_sh_room] is the mould).              *)
  (*                                                                      *)
  (*  THE PAYLOAD IS TRIVIAL: the process that execs is the one sh FORKED  *)
  (*  ([UkFork.wp_uk_ecall_fork_any]'s child arm), so [Q := fun _ => True] *)
  (*  and [echo_uexec_slot]'s own pay row is the one it already has.       *)
  (* =================================================================== *)
  Definition echo_slot_of_kexec : Prop :=
    forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
           (sts : list fdstate) (W' : uvis),
      kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
      kexec_sz ElfUser.echo_elf - PGSIZE + 96
        <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
      length sts = NOFILE ->
      ⊢ udepw_law 16 -∗ udep -∗
        my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W'.

  (* =================================================================== *)
  (*  7.  THE ASSEMBLY: sh's pinned bundle pays its exec supply            *)
  (*                                                                      *)
  (*  [UInitSh.init_exec_sup_of_sh_slot] at /echo.  The taint arm is       *)
  (*  [UexecExecMint.uslot_mint_all] (the generic slot at a constant       *)
  (*  payload -- here the trivial one), the resolving arm is               *)
  (*  [echo_slot_of_kexec] above, and the bundle is                        *)
  (*  [PinnedExec.pinned_exec_bundle] at                                   *)
  (*  [Pin := FsEchoPin.era0_echo_pins], [cw := FsImg.ROOTINO],            *)
  (*  [pl := echo_pl], [hops := [ROOTINO; ECHO_INO]],                      *)
  (*  [f := ElfUser.echo_elf], [nl := 1], [Pay := emp],                    *)
  (*  [Q := fun _ => True].                                                *)
  (* =================================================================== *)
  Definition sh_exec_sup_of_echo_slot : Prop :=
    forall (T : iProp Σ) (HP : Persistent T) (HT : Timeless T),
      (* the ONE obligation still open at this seam: echo's entry at the
         exec channel ([echo_slot_of_kexec] above, section 6). *)
      echo_slot_of_kexec ->
      ⊢ udep -∗ udepw_law 16 -∗ sh_echo_slot T -∗
        UkShEcho.sh_exec_sup_echo.

  Lemma sh_exec_sup_of_echo_slot_holds : sh_exec_sup_of_echo_slot.
  Proof.
    intros T HP HT Hslot.
    iIntros "#Hdep #Hwr (#Hinv & #Hcl & #Hgen)".
    iModIntro. iIntros (N' m pc s0 t g) "%Hpeq %Ha0 %Ha1 %Hbytes #Hcmd".
    rewrite /udepw_at. iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    (* the node, read ONCE off the lent heap *)
    iAssert (⌜ echo_node_img M s0 t g ⌝)%I as %Himg.
    { iApply (echo_node_img_of_cmd with "Hheap Hcmd"). }
    (* ...and the table's length, off the lent authority *)
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iFrame "Hheap Hufd". iRight.
    (* ---- THE RESOLVING ARM: echo's own entry, at the pinned image ---- *)
    iAssert (□ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
                  (W' : uvis),
                  ⌜kexec_image_ok ElfUser.echo_elf na alen afun fdv W'⌝ -∗
                  ⌜exec_args_of M (mword_of_int (t + 8) : mword 64)
                     na alen afun⌝ -∗
                  my_pay (uvis_gen W') (fun _ : Z => True)%I -∗
                  (fun _ : Z => True)%I (-1) -∗ (emp : iProp Σ) -∗
                  uslot W'))%I as "#Hcon".
    { iModIntro. iIntros (na alen afun W') "%Hok %Hargs #Hmp _ _".
      destruct (echo_args_det_holds M s0 t g na alen afun Himg Hbytes Hargs)
        as (Hna & Halen & _).
      subst na.
      iApply (Hslot 3%nat alen afun fdv W' Hok
                (echo_room alen (Halen 0%nat ltac:(lia))
                   (Halen 1%nat ltac:(lia)) (Halen 2%nat ltac:(lia)))
                Hlen with "Hwr Hdep Hmp"). }
    (* ---- THE TAINT ARM: the generic slot at the trivial payload ---- *)
    iAssert (□ (∀ W' : uvis, T -∗
                  my_pay (uvis_gen W') (fun _ : Z => True)%I -∗
                  (fun _ : Z => True)%I (-1) -∗ uslot W'))%I as "#Hgen'".
    { iModIntro. iIntros (W') "#HT #Hmp _".
      iApply ("Hgen" $! (True%I : iProp Σ) W' with "HT Hmp []"). done. }
    (* ---- THE BUNDLE ---- *)
    iDestruct (pinned_exec_bundle fsc_fs uslot FsEchoPin.era0_echo_pins T
                 FsImg.ROOTINO echo_pl
                 [FsImg.ROOTINO; FsEchoPin.ECHO_INO] FsEchoPin.ECHO_INO
                 ElfUser.echo_elf 1%nat (emp : iProp Σ)
                 (fun _ : Z => True)%I
                 M (mword_of_int s0) (mword_of_int (t + 8)) fdv
                 sh_echo_pin_resolves echo_elf_loadable
                 (sh_echo_path_of_holds M s0 t g Himg Hbytes)
                 with "Hcl Hinv Hcon Hgen' []") as (P Pmiss Fo R) "Hb";
      [ done | ].
    assert (Ea0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv
                                  FsImg.ROOTINO gn cs pidv))
                    (tf_arg_idx 0) = (mword_of_int s0 : mword 64))
      by (etransitivity; [ exact (tf_of_arg0 m pc) | exact Ha0 ]).
    assert (Ea1 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv
                                  FsImg.ROOTINO gn cs pidv))
                    (tf_arg_idx 1) = (mword_of_int (t + 8) : mword 64))
      by (etransitivity; [ exact (tf_of_arg1 m pc) | exact Ha1 ]).
    iApply (sbundle_pay_exec_intro uslot
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv)
              (ukn_pay N') P Pmiss Fo R).
    { cbn [uvis_gen uvis_of_run]. iExact "Hmpay". }
    rewrite Hpeq Ea0 Ea1. iExact "Hb".
  Qed.

  (* =================================================================== *)
  (*  8.  S3 -- ECHO'S OUTPUT                                             *)
  (*                                                                      *)
  (*  echo's loop is                                                       *)
  (*    for (i = 1; i < argc; i++) {                                       *)
  (*      write(1, argv[i], strlen(argv[i]));                              *)
  (*      write(1, i + 1 < argc ? " " : "\n", 1);                          *)
  (*    }                                                                  *)
  (*  so at [argc = 3] it writes four buffers, in this order.              *)
  (* =================================================================== *)
  Definition echo_out : list (bv 8) :=
    sb "hello" ++ sb " " ++ sb "world" ++ nlb.

  (* ANTI-VACUITY: those are the bytes the target statement's expected
     stream carries for one cycle. *)
  Lemma echo_out_string : echo_out = sb "hello world" ++ nlb.
  Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

  Lemma echo_out_length : length echo_out = 12%nat.
  Proof. vm_compute. reflexivity. Qed.

  (* ---- E4's OWN PART: the argv echo reads off its key ARE the strings -- *)
  (* [UEchoKernel.echo_arg] is a FUNCTION of the key (the pointer is the
     eight image bytes of the slot read as a word, the length is what a
     scan finds, the bytes are the image's), so what has to be shown is
     that [kexec_args_at]'s block, built from the [(na, alen, afun)] that
     [echo_args_det] pinned, is read back as the same three strings. *)
  Definition echo_key_args : Prop :=
    forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
           (sts : list fdstate) (W' : uvis),
      kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
      na = 3%nat ->
      (forall i : nat, (i < 3)%nat -> alen i = UkShEcho.echo_alen i) ->
      (forall i j : nat, (i < 3)%nat -> (j < UkShEcho.echo_alen i)%nat ->
         afun i j = echo_line !!! (UkShEcho.echo_off i + j)%nat) ->
      Z.to_nat (uvis_argc W') = 3%nat
      /\ (forall i : nat, (i < 3)%nat ->
            ua_len (echo_arg (uvis_M W') (uvis_av W') i)
            = UkShEcho.echo_alen i
            /\ forall j : nat, (j < UkShEcho.echo_alen i)%nat ->
                 ua_bytes (echo_arg (uvis_M W') (uvis_av W') i) j
                 = echo_line !!! (UkShEcho.echo_off i + j)%nat).

  (* ---- the shape a list of [uarg]s has when it IS echo's three -------- *)
  Definition echo_argv_is (args : list uarg) : Prop :=
    length args = 3%nat
    /\ forall (i : nat) (x : uarg), args !! i = Some x ->
         ua_len x = UkShEcho.echo_alen i
         /\ forall j : nat, (j < UkShEcho.echo_alen i)%nat ->
              ua_bytes x j = echo_line !!! (UkShEcho.echo_off i + j)%nat.

  (* ---- ECHO'S POST OVER ITS TRANSCRIPT ------------------------------- *)
  (*                                                                       *)
  (*  [UkEcho.wp_kecho_write] goes through [UkRunSys]'s QUIET row today:   *)
  (*  it returns an unconstrained [ret] and says nothing about a byte.     *)
  (*  The leaf that KEEPS the receipt is TX-RECEIPT's                      *)
  (*  [wp_uk_ecall_write_recv] -- "my transcript grew by exactly the first *)
  (*  [r] bytes of my buffer" -- and it is NOT built here (it is E5's, on  *)
  (*  lane/tx-receipt).  So it is a NAMED HYPOTHESIS: [recv N] is that     *)
  (*  leaf and [tx N bs] the program-side transcript handle it moves.      *)
  (*                                                                       *)
  (*  WHAT E4 OWES against it is the two things this lane knows and E5     *)
  (*  does not: the argv bytes ARE "echo", "hello", "world"                *)
  (*  ([echo_key_args], from [echo_cmd] through the exec channel) and the  *)
  (*  LOOP'S ORDER -- so the transcript at echo's [exit] ecall is the      *)
  (*  entry's plus [echo_out], and nothing else.                           *)
  (* =================================================================== *)
  Definition echo_writes_out
      (recv : uk_names Σ -> iProp Σ)
      (tx : uk_names Σ -> list (bv 8) -> iProp Σ) : Prop :=
    forall (N : uk_names Σ) (h : CpuId) (m : regfile) (av : Z)
           (args : list uarg) (bs : list (bv 8)) (n : nat),
      m !!! Regidx a0_idx
        = (mword_of_int (Z.of_nat (length args)) : mword 64) ->
      m !!! Regidx a1_idx = (mword_of_int av : mword 64) ->
      echo_argv_is args ->
      ⊢ recv N -∗ udepw_law 16 -∗ echo_code (ukn_t N) -∗
        uargv (ukn_d N) av args -∗ tx N bs -∗
        urun N h m (mword_of_int EchoSyms.start) (2 + (8 + (2 + n))) -∗
        (∀ (h' : CpuId) (m' : regfile),
           tx N (bs ++ echo_out) -∗
           urun N h' m' (mword_of_int EchoSyms.exit) n -∗
           WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang).

End UShEcho.
