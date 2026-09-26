(* ===================================================================== *)
(* UInitSh.v -- init's OWN exec deposit: the PINNED bundle for /sh, and    *)
(* the reading of init's image that prices sh's frames.                   *)
(*                                                                        *)
(* [UkInit.init_exec_sup] is what init's proof carries in place of         *)
(* [UkRun.uxsup] -- the exec deposit at init's OWN two argument registers  *)
(* (a0 = 0x9b8, the string "sh" in its rodata; a1 = 0x1000, the argument   *)
(* vector in its .data) and at the ONE working directory it ever has       *)
(* ([FsImg.ROOTINO]).  This file is where that supply is PAID, out of the  *)
(* application's claim that /sh is the file [ElfUser.sh_elf]:              *)
(*                                                                        *)
(*   [init_sh_slot T Pay]  the four persistent ingredients -- the          *)
(*                         file-system invariant, the duplicating claim    *)
(*                         law at [FsShPin.era0_sh_pins], the taint's      *)
(*                         generic slot, and sh's entry payload [Pay].     *)
(*   [init_args_det]       INIT'S ARGUMENTS ARE DETERMINED BY ITS IMAGE.   *)
(*   [init_exec_sup_of_sh_slot]  the assembly.                             *)
(*                                                                        *)
(* WHY THE READING IS NEEDED.  [UShKernel.sh_slot_of_kexec] prices sh's    *)
(* frames against [kxc_sp_final], which is a function of the argument      *)
(* COUNT and LENGTHS -- and the exec channel offers those only as bound    *)
(* variables.  [SpecSysExec.exec_args_of] ties them to the caller's own    *)
(* image, and init's image is a constant: the word at 0x1000 is the        *)
(* pointer 0x9b8, the word at 0x1008 is NULL, and the string at 0x9b8 is   *)
(* "sh".  So [na = 1] and [alen 0 = 2], and the room premise is closed     *)
(* arithmetic ([kxc_sp_final 0x5000 alen 1 = 0x4FE0], and sh's frames need *)
(* 0x4000 + 8 * (106 + n0) below the top of its image).                    *)
(*                                                                        *)
(* WHY IT IS NOT IN THE u-TIER.  The last step is                          *)
(* [UexecExecInst.sbundle_exec_intro], which is proved at the KERNEL's     *)
(* instance of [UexecSG.uexecSG]; [UkInitMain.v] and [UInitKernel.v] are   *)
(* stated over the CLASS, with the instance a section variable.  Importing *)
(* the instance into either of them would put two [sbundle]s that print    *)
(* identically in scope, and would make [UexecSG.psok] resolve to          *)
(* [uprogSG_gen]'s trivial one -- every [psok] premise vacuously true.     *)
(* So the u-tier speaks [UkInit.init_exec_sup] and this file, above the    *)
(* instance, is what pays it.                                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import WpMmodeLeafBase.  (* [csp_rs1] *)
Require Import UmodeArith UmodeAbi.   (* [Z64]: EX-3's reading needs it; the sweep predates it *)
Require Import ProcGeom.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required:
   naming [xv6G] / [fileG] / [irefslotG] / [pavG] without their defining
   module in scope introduces a FRESH Type variable instead of the class,
   and the kernel's [uexecSG] instance is then invisible to resolution.
   [PinnedExec.v]'s header is the note. *)
Require Import Xv6G.            (* [xv6G] *)
Require Import FdSlots.         (* [fdslotG], [fdstate] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG], and its [appcfg] / [icfg] fields *)
Require Import UserFd.
Require Import UserHeap.
Require Import ChildTok.  (* [my_pay]: the exec wands' pay fact *)
Require Import UexecSlot UexecRet UexecSG.
Require Import UInitFd.  (* [ufd_head] / [ufd_head_row] -- init's own
                            descriptor head, and the row sh's entry reads
                            off it against the lent authority *)
Require Import UkRun.
Require Import UCodeInit UInitArgv UkInit.
Require Import LineWords.       (* [wl_nl]: the credential steps are stated
                                   at the line the read delivered *)
Require Import UkSh UShKernel.
Require Import UkShParse.       (* the two lexer tables' addresses and
                                   content functions, which sh's static
                                   state is made of *)
Require Import UkShLoop.        (* [ushl_dat] -- sh's opaque static state *)
Require Import ElfFile.         (* [elf_image] / [elf_zero_byte] *)
Require Import BlockWords.      (* [nth_byte_zero] *)
Require User.ShData User.ShInstrs.
Require Import PathElems.          (* [path_elems] *)
Require Import ElfUser.
Require Import ElfLoadable.        (* [sh_elf_loadable] *)
Require Import EchoFsPure.         (* [echo_fs_pure] -- the WHOLE pins law
                                      sh is handed (lane E4: its own exec of
                                      /echo needs [FsEchoPin.era0_echo_pins],
                                      which is one of its conjuncts).  A PURE
                                      [Prop], so naming it costs nothing; the
                                      era's console GHOSTS are deliberately
                                      NOT named here -- see the note at
                                      [init_sh_slot]. *)
Require Import EchoOut.            (* [echoOutG]: the class [AppEcho]'s claims
                                      and its ledger are stated at (lane
                                      ECHO-OUT part 5).  It CARRIES
                                      [mono_natG], so it is the taint's one
                                      instance here too. *)
Require Import PageGeom.           (* [PGSIZE] *)
Require Import KexecDefs.
Require Import SpecKexec.
Require Export UImgWordDefs.  (* [img_word_of_bytes], [uimg_word_det]
                                 -- split out of this file for [UShEcho].
                                 EXPORT: existing importers unchanged. *)
Require Import SpecSysExec.        (* [exec_args_of] / [exec_path_of] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsImgCheck.         (* [fname_sh] *)
Require Import FsShPin.            (* [era0_sh_pins] / [sh_path] / [SH_INO] *)
Require Import FsAbsDefs.          (* [aview] / [arun] / [AFile] *)
Require Import PinnedExec.
Require Import ExecRun.            (* [sbundle_pay_exec_intro_refR] and the
                                      U-tier exec rule this file's supply is
                                      an instance of *)
Require Import ExecEntry.       (* [image_entry] / [image_entry_taint]:
                                   obligation (E), named (lane EX-1) *)
Require Import ExecArgs.        (* [uargv_img] / [uargv_shape] / [uargv_det]:
                                   the argument reading at ANY layout
                                   (lane EX-3); /init's is this one at a
                                   CONSTANT layout *)
Require Import UexecExecInst.      (* [sbundle_exec_intro] -- THE INSTANCE *)
Require Import Xv6Cameras.         (* [uartGhostG] *)
Require Import UartNames.          (* [cons_names] *)
Require Import UserConsole.        (* [ucons_pay] / [upos] *)
Require Import CtxIdDefs.
Require User.InitData.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  THE SAME SEAL [UShKernel.v] NEEDS, and for the same reason (its       *)
(*  header at [Typeclasses Opaque] is the note).  [UkSh.ush_rest_l_at] is *)
(*  TRANSPARENT, so once this file states sh's tail obligation at a line  *)
(*  predicate that is a VARIABLE ([sh_pay_at] below), the [Persistent]    *)
(*  search walks the obligation's whole body instead of stopping at its   *)
(*  named instance ([UkSh.ush_rest_l_at_persistent]) and does not         *)
(*  return.  LOCAL, so no importer is affected; nothing here needs to see *)
(*  through the constant, and any future [iModIntro] at such a goal wants *)
(*  [rewrite /UkSh.ush_rest_l_at] first.                                  *)
(* ===================================================================== *)
#[local] Typeclasses Opaque UkSh.ush_rest_l_at.

(* ===================================================================== *)
(*  1.  THE PATH init PASSES, as a byte list                              *)
(*                                                                        *)
(*  [SpecSysExec.exec_path_of] reads the caller's string off its image as  *)
(*  a [list (bv 8)]; [FsShPin]'s pin speaks of [FsShPin.sh_path], a list   *)
(*  of NAMES.  The two are joined by [PathElems.path_elems], and at "sh"   *)
(*  the join is the identity on the bytes -- so the byte list is spelled   *)
(*  AS the name, and nothing is retyped.                                   *)
(* ===================================================================== *)
Definition init_sh_pl : list (bv 8) := FsImgCheck.fname_sh.

Lemma init_sh_path_elems : path_elems init_sh_pl = FsShPin.sh_path.
Proof. vm_compute. reflexivity. Qed.

Lemma init_sh_pl_len : length init_sh_pl = 2%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2.  THE PIN RESOLVES, at init's cwd                                    *)
(* ===================================================================== *)
Lemma init_sh_pin_resolves :
  pin_resolves FsShPin.era0_sh_pins FsImg.ROOTINO init_sh_pl
    [FsImg.ROOTINO; FsShPin.SH_INO] FsShPin.SH_INO ElfUser.sh_elf 1%nat.
Proof.
  split_and!.
  - (* the start: "sh" is RELATIVE, so the walk starts at the cwd -- which
       is the root anyway, so both arms of [um_start_of] agree *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (init_sh_pl !! 0%nat = Some PathElems.SLASH));
      reflexivity.
  - rewrite init_sh_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite init_sh_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsShPin.sh_bytes_elf. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  INIT'S IMAGE, READ                                                 *)
(*                                                                        *)
(*  Three closed facts about the dump, each one [vm_compute] and nothing   *)
(*  else: the two words of the argument vector, and the three bytes of     *)
(*  the path.  Everything downstream is arithmetic over them.              *)
(* ===================================================================== *)
Lemma init_argv_words_bool :
  forallb (fun k : nat =>
      bool_decide (
        UInitArgv.init_argv_map !! (0x1000 + Z.of_nat k)
          = Some (nth_byte (mword_of_int 0x9b8 : mword 64) k)
        /\ UInitArgv.init_argv_map !! (0x1008 + Z.of_nat k)
          = Some (nth_byte (mword_of_int 0 : mword 64) k)))
    (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_argv_words (k : nat) :
  (k < 8)%nat ->
  UInitArgv.init_argv_map !! (0x1000 + Z.of_nat k)
    = Some (nth_byte (mword_of_int 0x9b8 : mword 64) k)
  /\ UInitArgv.init_argv_map !! (0x1008 + Z.of_nat k)
    = Some (nth_byte (mword_of_int 0 : mword 64) k).
Proof.
  intro Hk.
  pose proof (proj1 (forallb_forall _ (seq 0 8)) init_argv_words_bool k
                ltac:(apply in_seq; lia)) as H.
  exact (bool_decide_eq_true_1 _ H).
Qed.

Lemma init_ro_sh_bool :
  bool_decide (
      UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9b8 : mword 64) (Z.of_nat 0%nat))
      = init_sh_pl !! 0%nat
   /\ UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9b8 : mword 64) (Z.of_nat 1%nat))
      = init_sh_pl !! 1%nat
   /\ UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9b8 : mword 64) (Z.of_nat 2%nat))
      = Some (bv_0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bv0_moi0 : (bv_0 8 : bv 8) = (mword_of_int 0 : mword 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [img_word_of_bytes] and [uimg_word_det] MOVED DOWN to
   [UImgWordDefs.v] (re-exported above): they are pure facts about a
   byte map, and [UShEcho] wants exactly those two out of this file. *)

(* ===================================================================== *)
(*  4.  INIT'S ARGUMENTS ARE DETERMINED BY ITS IMAGE                       *)
(*                                                                        *)
(*  Every reading of the argument vector at 0x1000 that [sys_exec] can     *)
(*  perform against an image containing init's .data and .rodata is the    *)
(*  same one: ONE argument, of length two.  That is what prices sh's       *)
(*  frames, and it is why the pinned route needs [exec_args_of] and not    *)
(*  merely [exec_args_shape].                                              *)
(*                                                                        *)
(*  AS RE-DERIVED (lane EX-3).  This used to be sixty lines of its own --  *)
(*  two pointer words unwrapped by [vm_compute], the count cornered        *)
(*  against the NULL cap, the length cornered against three rodata bytes.  *)
(*  It is now [ExecArgs.uargv_det] at /init's layout, and the layout is    *)
(*  the only thing this file still spells: ONE [UserHeap.uarg] at a        *)
(*  literal pointer, whose two premises are three [vm_compute]s.  The      *)
(*  statement is unchanged, and so is everything downstream.               *)
(* ===================================================================== *)

(* THE VECTOR, in the U tier's own spelling.  [ua_bytes] is a FUNCTION,
   so the terminator has to be a value of it and not merely a byte of the
   image -- [default ubyte0] past the end of the name is exactly that,
   and it is what [ByteBuf.bb_cstr] asks for. *)
Definition init_argv_args : list uarg :=
  [UArg 0x9b8 2%nat (fun j : nat => default ubyte0 (init_sh_pl !! j))].

Lemma init_argv_args_length : length init_argv_args = 1%nat.
Proof. reflexivity. Qed.

Lemma init_argv_args_lookup (i : nat) (x : uarg) :
  init_argv_args !! i = Some x ->
  i = 0%nat
  /\ x = UArg 0x9b8 2%nat (fun j : nat => default ubyte0 (init_sh_pl !! j)).
Proof.
  intro Hi. rewrite /init_argv_args in Hi.
  destruct i as [| i]; cbn in Hi; [ | discriminate Hi ].
  injection Hi as <-. split; reflexivity.
Qed.

Lemma init_argv_shape : uargv_shape init_argv_args.
Proof.
  split; [ rewrite init_argv_args_length; unfold MAXARG; lia | ].
  intros i x Hi.
  destruct (init_argv_args_lookup i x Hi) as [_ ->].
  cbn [ua_ptr ua_len ua_bytes].
  split_and!; [ lia | lia | split ].
  - intros j Hj.
    destruct j as [| [| j]]; [ | | exfalso; lia ];
      (intro Hc; apply (f_equal bv_unsigned) in Hc;
       vm_compute in Hc; discriminate Hc).
  - apply bv_eq. vm_compute. reflexivity.
Qed.

(* the three bytes of the name AND its terminator, in one [vm_compute] over
   the dump -- [init_ro_sh_bool] with the byte function above in place of
   the list lookups, so the reading needs no case split at the use site *)
Lemma init_ro_sh_bytes_bool :
  forallb (fun j : nat =>
      bool_decide (UCodeInit.init_ro !! (0x9b8 + Z.of_nat j)
                   = Some (default ubyte0 (init_sh_pl !! j))))
    (seq 0 3) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_argv_img (M : gmap Z (bv 8)) :
  uimg_sub UInitArgv.init_argv_map M ->
  uimg_sub UCodeInit.init_ro M ->
  uargv_img M 0x1000 init_argv_args.
Proof.
  intros Hav Hro.
  (* the two windows, in the contract's spelling *)
  assert (Hb0 : forall k : nat, (k < 8)%nat ->
            M !! (0x1000 + Z.of_nat k)
            = bv_to_little_endian 8 8 0x9b8 !! k).
  { apply img_word_of_bytes. intros k Hk.
    exact (Hav _ _ (proj1 (init_argv_words k Hk))). }
  assert (Hb1 : forall k : nat, (k < 8)%nat ->
            M !! (0x1008 + Z.of_nat k)
            = bv_to_little_endian 8 8 0 !! k).
  { apply img_word_of_bytes. intros k Hk.
    exact (Hav _ _ (proj2 (init_argv_words k Hk))). }
  pose proof (proj1 (forallb_forall _ (seq 0 3)) init_ro_sh_bytes_bool) as Hb3.
  rewrite /uargv_img init_argv_args_length. split_and!.
  - lia.
  - unfold Z64. lia.
  - intros i x Hi.
    destruct (init_argv_args_lookup i x Hi) as [_ ->].
    cbn [ua_ptr ua_len]. unfold Z64. lia.
  - intros i x Hi.
    destruct (init_argv_args_lookup i x Hi) as [-> ->].
    cbn [ua_ptr]. intros k Hk.
    replace (0x1000 + 8 * Z.of_nat 0%nat + Z.of_nat k)
      with (0x1000 + Z.of_nat k) by lia.
    exact (Hb0 k Hk).
  - intros k Hk.
    replace (0x1000 + 8 * Z.of_nat 1%nat + Z.of_nat k)
      with (0x1008 + Z.of_nat k) by lia.
    exact (Hb1 k Hk).
  - intros i x Hi.
    destruct (init_argv_args_lookup i x Hi) as [_ ->].
    cbn [ua_ptr ua_len ua_bytes]. intros j Hj.
    assert (Hin : In j (seq 0 3)) by (apply in_seq; lia).
    pose proof (bool_decide_eq_true_1 _ (Hb3 j Hin)) as Hrow.
    exact (Hro _ _ Hrow).
Qed.

Lemma init_args_det (M : gmap Z (bv 8)) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) :
  uimg_sub UInitArgv.init_argv_map M ->
  uimg_sub UCodeInit.init_ro M ->
  exec_args_of M (mword_of_int 0x1000 : mword 64) na alen afun ->
  na = 1%nat /\ alen 0%nat = 2%nat.
Proof.
  intros Hav Hro Hargs.
  destruct (uargv_det M 0x1000 init_argv_args na alen afun
              init_argv_shape (init_argv_img M Hav Hro) Hargs) as (Hn & Hl & _).
  assert (Hn1 : na = 1%nat) by (rewrite Hn init_argv_args_length; reflexivity).
  split; [ exact Hn1 | ].
  rewrite (Hl 0%nat ltac:(rewrite Hn1; lia)). reflexivity.
Qed.

(* ===================================================================== *)
(*  5.  THE INGREDIENTS                                                    *)
(* ===================================================================== *)
(* ===================================================================== *)
(*  4b.  THE BYTES SH'S STATIC STATE IS MADE OF (lane SH-STATE)           *)
(*                                                                        *)
(*  sh's writable PT_LOAD is (vaddr 0x2000, filesz 0x10, memsz 0x98).      *)
(*  The file half is the two lexer tables ([UkShParse.ushp_symbols] at     *)
(*  0x2000, [ushp_whitespace] at 0x2008) and comes off the DUMP; the rest  *)
(*  -- [freep] at 0x2010, sh's line buffer [UkSh.sh_buf] at 0x2020, the    *)
(*  allocator's [base] cell at 0x2088 -- is .bss and comes off             *)
(*  [ElfUser.sh_elf_zero_image].  Both halves are read through             *)
(*  [ElfUser.sh_elf_image_concrete], the NAMED image equation, so nothing  *)
(*  here reduces [sh_elf] (durable-notes, "Name the ELF-bytes equation").  *)
(* ===================================================================== *)

(* the two tables, in the [forallb]-over-[seq] shape [UkSh.ush_jrow_bytes_ok]
   uses: ONE [vm_compute] over the 2532-entry dump, not fourteen *)
Definition sh_tbl_ok : bool :=
  forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_symbols + Z.of_nat j)
                   = Some (ushp_sym_f j))) (seq 0 7)
  && forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_whitespace + Z.of_nat j)
                   = Some (ushp_ws_f j))) (seq 0 5)
  && bool_decide (ShData.sh_data !! (ushp_symbols + 7) = Some ubyte0)
  && bool_decide (ShData.sh_data !! (ushp_whitespace + 5) = Some ubyte0).

Lemma sh_tbl_ok_true : sh_tbl_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_tbl_parts :
  forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_symbols + Z.of_nat j)
                   = Some (ushp_sym_f j))) (seq 0 7) = true
  /\ forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_whitespace + Z.of_nat j)
                   = Some (ushp_ws_f j))) (seq 0 5) = true
  /\ bool_decide (ShData.sh_data !! (ushp_symbols + 7) = Some ubyte0) = true
  /\ bool_decide (ShData.sh_data !! (ushp_whitespace + 5) = Some ubyte0) = true.
Proof.
  pose proof sh_tbl_ok_true as H. unfold sh_tbl_ok in H.
  apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* the dumped .data window IS part of the image *)
Lemma sh_dat_img (a : Z) (b : bv 8) :
  ShData.sh_data !! a = Some b -> elf_image ElfUser.sh_elf !! a = Some b.
Proof.
  intro Hb. rewrite ElfUser.sh_elf_image_concrete.
  assert (Hn : ShInstrs.sh_bytes !! a = None).
  { destruct (ShInstrs.sh_bytes !! a) as [c |] eqn:E; [ exfalso | reflexivity ].
    pose proof (ShInstrs.sh_bytes_range a c E) as Hr.
    pose proof (ShData.sh_data_range a b Hb) as Hr2.
    unfold ShInstrs.sh_bytes_hi, ShInstrs.sh_bytes_lo,
           ShData.sh_data_lo, ShData.sh_data_hi in *. lia. }
  apply lookup_union_Some_l. rewrite lookup_union_r; [ exact Hb | exact Hn ].
Qed.

(* ...and the .bss window is zero *)
Lemma sh_bss_img (a : Z) :
  0x2010 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some ubyte0.
Proof.
  intro Ha. rewrite ElfUser.sh_elf_image_concrete.
  assert (Hn : (ShInstrs.sh_bytes ∪ ShData.sh_data) !! a = None).
  { destruct ((ShInstrs.sh_bytes ∪ ShData.sh_data) !! a) as [c |] eqn:E;
      [ exfalso | reflexivity ].
    apply lookup_union_Some_raw in E as [E | [_ E]].
    - pose proof (ShInstrs.sh_bytes_range a c E) as Hr.
      unfold ShInstrs.sh_bytes_hi, ShInstrs.sh_bytes_lo in Hr. lia.
    - pose proof (ShData.sh_data_range a c E) as Hr.
      unfold ShData.sh_data_lo, ShData.sh_data_hi in Hr. lia. }
  rewrite lookup_union_r; [ | exact Hn ].
  apply lookup_map_seqZ_Some. split.
  - unfold ElfUser.sh_bss_lo. lia.
  - apply lookup_replicate_2. unfold ElfUser.sh_bss_lo, ElfUser.sh_bss_size. lia.
Qed.

Lemma moi0_bv0_64 : (mword_of_int 0 : mword 64) = bv_0 64.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma nth_byte_zero64 (j : nat) :
  nth_byte (mword_of_int 0 : mword 64) j = ubyte0.
Proof.
  rewrite moi0_bv0_64 nth_byte_zero.
  unfold ubyte0. apply bv_eq. vm_compute. reflexivity.
Qed.

(* a WINDOW of a map, in and out.  [UserHeap.umap_split_at]'s twin at a
   half-open interval; RELOCATION ASK: it belongs beside that lemma, and
   is local here only because moving it rebuilds the tier
   ([UkShMain.v]'s SS1 note is the same case. *)
Lemma umap_win_lookup (D : gmap Z (bv 8)) (lo hi a : Z) (b : bv 8) :
  lo <= a < hi -> D !! a = Some b ->
  base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D !! a = Some b.
Proof.
  intros Ha Hb. apply map_lookup_filter_Some.
  split; [ exact Hb | cbn [fst]; exact Ha ].
Qed.

Lemma umap_win_lookup_out (D : gmap Z (bv 8)) (lo hi a : Z) (b : bv 8) :
  ~ (lo <= a < hi) -> D !! a = Some b ->
  base.filter (fun kv : Z * bv 8 => ~ (lo <= kv.1 < hi)) D !! a = Some b.
Proof.
  intros Ha Hb. apply map_lookup_filter_Some.
  split; [ exact Hb | cbn [fst]; exact Ha ].
Qed.

Section UInitSh.
  (* THE KERNEL'S INSTANCE IS AMBIENT: [UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally, and this file is where the
     u-tier's class-level statements meet them.  NO [Context {SG}] /
     [Context {PS}] here -- a local instance beside the global one is two
     [sbundle]s that print identically. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console ring's cameras: the POSITION init lends sh across the exec
     is stated over them ([UserConsole.upos]) *)
  Context `{!uartGhostG Σ}.
  (* the echo claims' class (lane ECHO-OUT part 5): [AppEcho.echo_taint] and
     everything built over it is stated at [EchoOut.echoOutG] now, not at a
     bare [mono_natG]. *)
  Context `{!echoOutG Σ}.

  (* ------------------------------------------------------------------- *)
  (* sh's ENTRY PAYLOAD, as init holds it.                                 *)
  (*                                                                       *)
  (* The two ∀-quantified persistent pieces [UShKernel.sh_slot_of_kexec]   *)
  (* takes beside the image fact: the wand that produces sh's opaque       *)
  (* static state [R] and its line buffer out of the writable data below   *)
  (* the frame, and the discharge of sh's own tail obligation              *)
  (* ([UkSh.ush_rest]).  Both are PARAMETERS of init's constructor -- the  *)
  (* application (AppEcho) instantiates them -- and both are persistent,   *)
  (* which they must be: init execs inside the fork child, inside an       *)
  (* [iLob] the parent re-enters, so nothing linear can be spent there.    *)
  (*                                                                       *)
  (* [n0] is the slack sh's entry is priced at.  Any [n0] under 402 fits   *)
  (* ([init_sh_room] below); the caller picks one.                         *)
  (* ------------------------------------------------------------------- *)
  (* ITS THREE CONJUNCTS, NAMED (lane E2).  Each is owed by a different
     lane, and the top theorem carries the two it does not own as named
     hypotheses -- so [sh_pay] itself is assembled from the parts rather
     than quoted twice ([sh_pay_of_parts]).  The tag's reading is E2's own
     and is proved from the theorem's [riscv_rx_tag = app_tag] equation. *)
  (* LANE SH-STATE RESTATED THIS.  Two things were wrong with the [∀]-over-
     every-key form: at an arbitrary key nothing pins [uvis_sz W'] to the
     break a turn of the loop carries, and nothing puts sh's writable
     window in the map -- so NO [Rsh] could satisfy it.  Both are the
     entry's own reading of its key, and they enter as
     [UShKernel.sh_pay_key] ([UShKernel.sh_pay_key_of_kexec] is the
     discharge, off [kexec_image_ok] and the room bound).
     ...AND THE CONCLUSION IS AN UPDATE: [UkShLoop.ushl_dat] holds the two
     lexer tables at [DfracDiscarded], and persisting a [DfracOwn 1] byte
     is a frame-preserving update.  The wand is spent inside a [WP]
     ([UShKernel.sh_uexec_slot]), which absorbs it. *)
  Definition sh_pay_state (Rsh : gname -> gname -> gname -> iProp Σ)
      (n0 : nat) : iProp Σ :=
    (□ (∀ (W' : uvis) (γt γd γs : gname),
          ⌜ UShKernel.sh_pay_key W' n0 ⌝ -∗
          usz γs (uvis_sz W') -∗
          ([∗ map] k ↦ b ∈ base.filter
                (fun kv : Z * bv 8 =>
                   kv.1 < uint (tf_resume_gpr0 (uvis_tf W')
                                !!! Regidx csp_rs1)
                          - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
                (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
             ubyte γd k b) -∗
          |==> ∃ f : nat -> bv 8, Rsh γt γd γs ∗ ubytes γd sh_buf sh_nbuf f))%I.

  (* [sh_pay_rest] IS GONE (lane R3).  It was the era-FREE form of the
     tail obligation -- a [forall T Wc Wb Pm] the top theorem assumed --
     and it is not provable in that shape: its one discharger
     ([UkShFork.ushf_rest_of_body]) needs the PAID CHILD's law, a killed
     child's credential and sh's own panic law, all of which are facts
     about the era's families and FALSE for some of them.  The obligation
     is discharged at the echo era's own families instead
     ([UShRest.sh_rest_holds]), which is what [sh_pay]'s second conjunct
     below asks for and what [UInitBoot.echo_Hinit_boot] now proves rather
     than assumes. *)

  (* =================================================================== *)
  (*  THE TEN LAWS THE CONSOLE'S SUPPLY ASKS OF THE CREDENTIAL             *)
  (* =================================================================== *)
  (*  Gathered VERBATIM from what [init_exec_sup_of_sh_slot] below used to *)
  (*  take one at a time.  Together with [UserConsole.cons_cred] they are  *)
  (*  the seam's whole interface to the application: a record and a proof  *)
  (*  where there were five predicates and ten [forall ... -> ⊢ ...]       *)
  (*  premises at every lemma of the chain.                                *)
  (*                                                                       *)
  (*  This file names no era, so they stay Coq-level -- their one          *)
  (*  discharge is [UInitBoot.echo_cc_holds], where the record's equations *)
  (*  are.  The application proves them ONCE.                              *)
  (* =================================================================== *)
  (*  THE TEN AT AN ARBITRARY DISCIPLINE (lane APP-FILE).  Only the FIRST
      conjunct reads the discipline -- sh's read leaf is
      [UkSh.ush_read_recv_leaf_at] at it -- and the other nine are
      era-free already.  [cons_cred_holds] below is this at echo's five,
      so its type and its meaning are the landed ones. *)
  Definition cons_cred_holds_at (cn : cons_names) (T : iProp Σ)
      (* THE INPUT'S DISCIPLINE AND THE FOUR READINGS OF IT
         [UShKernel.sh_slot_of_kexec] spends (lane LINK-GEN-5/6), verbatim
         at the shapes that lemma binds them at: the byte a snoc admits is
         not a carriage return, the partial line is short, the era's own
         line constructor, and the line the newline closes. *)
      (Dsc : list (bv 8) -> Prop)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b]) -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl]) ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (Cr : cons_cred Σ) : Prop :=
    (* the read leaf sh runs on, AT THE DISCIPLINE *)
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate),
       ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)) ->
       ⊢ UkSh.ush_read_recv_leaf_at (PS := uprogSG_free) N γp T
           (cc_mid Cr γp) Dsc cn l)
    (* the lease's three laws *)
    /\ (forall (γp : gname) (N : uk_names Σ) (i : nat),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)) ->
          ⊢ UkSh.ush_at N γp i -∗
            ∃ I : list (bv 8), ⌜length I = i⌝
              ∗ UkSh.ush_lease N γp T (cc_mid Cr γp) I)
    /\ (forall (γp : gname) (N : uk_names Σ) (I : list (bv 8)),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)) ->
          ⊢ T -∗ cc_mid Cr γp I -∗ UkSh.ush_at N γp (length I))
    /\ (forall (γp : gname) (N : uk_names Σ) (I : list (bv 8)),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)) ->
          ⊢ cc_mid Cr γp I -∗ cc_wb Cr I -∗ UkSh.ush_at N γp (length I))
    (* the loop's step on the era's write credential, AT THE LINE THE READ
       DELIVERED (project echo-any-line): the boundary is the era's input
       and the step is its extension by one body and its newline *)
    (* ...AS A FANCY UPDATE AT [top] (design SS4.3k) *)
    /\ (forall (γp : gname) (I l : list (bv 8)), wl_nl ∉ l ->
          ⊢ cc_mid Cr γp (I ++ l ++ [wl_nl]) -∗
            cc_wc Cr I 2%nat ={⊤}=∗
            cc_mid Cr γp (I ++ l ++ [wl_nl])
            ∗ cc_wc Cr (I ++ l ++ [wl_nl]) 3%nat)
    (* the three conversions of step 4 *)
    /\ (forall I : list (bv 8), ⊢ cc_wb Cr I -∗ cc_wc Cr I 0%nat)
    /\ (forall I : list (bv 8), ⊢ cc_wc Cr I 3%nat -∗ cc_wc Cr I 0%nat)
    /\ (forall (γp : gname) (I l : list (bv 8)), wl_nl ∉ l ->
          ⊢ cc_mid Cr γp (I ++ l ++ [wl_nl]) -∗
            cc_wb Cr I -∗
            cc_mid Cr γp (I ++ l ++ [wl_nl]) ∗ T)
    (* the cursor's boundary *)
    /\ (forall (γp : gname) (N : uk_names Σ) (l : list fdstate) (i : nat),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)) ->
          ⊢ upos γp i -∗ ucons_pay cn γp T (cc_rd Cr) (-1) -∗
            ((∃ I : list (bv 8), ⌜length I = i⌝
                ∗ UkSh.ush_wcp (cc_wc Cr) (cc_wb Cr) l I 0%nat) ∨ T) -∗
            UkSh.ush_posb N γp T (cc_wc Cr) (cc_wb Cr) (cc_mid Cr γp) l 0%nat)
    (* the lend's conversion at the shell's entry (lane M6b) *)
    /\ (forall n : nat,
          ⊢ cc_wp Cr n -∗
            ∃ I : list (bv 8), ⌜length I = n⌝ ∗ cc_wc Cr I 0%nat).

  (* ...AND THE ECHO INSTANCE, WHICH IS THE NAME THE SEAM STILL USES.  A
     definitional instance and not a lemma: [UInitBoot.echo_cc_holds]
     proves this very [Prop] and the two constructors below take it, so
     the ten laws stay ONE unfolding away from the conjunction. *)
  Definition cons_cred_holds (cn : cons_names) (T : iProp Σ)
      (Cr : cons_cred Σ) : Prop :=
    cons_cred_holds_at cn T EchoDisc.disc_input UkSh.ush_disc_snoc_ncr
      EchoDisc.disc_input_rest_short UkSh.ush_line_echo
      UkSh.ush_disc_line_echo Cr.

  (* [sh_pay] AT AN ARBITRARY LINE CONSTRUCTOR (lane APP-FILE).  Only the
     SECOND conjunct reads one: sh's tail obligation is
     [UkSh.ush_rest_l_at] at the era's own line predicate, and
     [UShKernel.sh_slot_of_kexec] takes that obligation at the SAME [Dl]
     its line reading is stated at -- so widening the entry's discipline
     widens this payload with it.  [sh_pay] below is this at echo's
     [UkSh.ush_line_echo], so the landed name and type do not move. *)
  Definition sh_pay_at (Dl : FileDisc.uline -> Prop)
      (T : iProp Σ) (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ)
      (n0 : nat) : iProp Σ :=
    (□ (∀ (W' : uvis) (γt γd γs : gname),
          ⌜ UShKernel.sh_pay_key W' n0 ⌝ -∗
          usz γs (uvis_sz W') -∗
          ([∗ map] k ↦ b ∈ base.filter
                (fun kv : Z * bv 8 =>
                   kv.1 < uint (tf_resume_gpr0 (uvis_tf W')
                                !!! Regidx csp_rs1)
                          - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
                (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
             ubyte γd k b) -∗
          |==> ∃ f : nat -> bv 8, Rsh γt γd γs ∗ ubytes γd sh_buf sh_nbuf f)
     (* ...AND THE TAIL AT EVERY POSITION GHOST: init mints a FRESH pair
        per child ([UserConsole.upos_alloc]), so what the application owes
        is sh's body at whichever name this round's pair got. *)
     ∗ (∀ (γp : gname) (N : uk_names Σ),
          ush_rest_l_at (PS := uprogSG_free) N γp T (cc_wc Cr) (cc_wb Cr)
            (cc_mid Cr γp) Dl (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))
     (* ...AND THE TAG'S READING (lane SH-LINE 2b, L4).  How a tagged input
        history is READ -- as the discipline or as the taint -- is a fact
        about the TOP theorem's [boot_fixedGS] equation [riscv_rx_tag =
        app_tag] and nothing below it, so it reaches sh as a premise, and
        this is the slot it rides in ([UConsLine.ush_exec_pay] is the
        shape).  E2 discharges it from that equation, beside init's claim
        law.  LAST, so every existing destructuring of this payload keeps
        working (durable-notes, "Shaping a change so the sweep is small"). *)
     ∗ UkSh.ush_tag_law T)%I.

  (* ...AND THE ECHO INSTANCE, the landed name: [UInitBoot] and every
     other importer is stated at this one and does not move. *)
  Definition sh_pay (T : iProp Σ) (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ)
      (n0 : nat) : iProp Σ :=
    sh_pay_at UkSh.ush_line_echo T Cr Rsh n0.

  (* THE MIDDLE PREMISE IS [sh_pay]'s SECOND CONJUNCT ITSELF (lane R3):
     the tail obligation at THIS era's taint and families, one per
     position ghost.  [UShRest.sh_rest_holds] is what supplies it. *)
  Lemma sh_pay_of_parts_at (Dl : FileDisc.uline -> Prop)
      (T : iProp Σ) `{!Persistent T}
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    sh_pay_state Rsh n0 -∗
    (∀ (γp : gname) (N : uk_names Σ),
       ush_rest_l_at (PS := uprogSG_free) N γp T (cc_wc Cr) (cc_wb Cr)
         (cc_mid Cr γp) Dl (Rsh (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_tag_law T -∗
    sh_pay_at Dl T Cr Rsh n0.
  Proof using .
    iIntros "#Hst #Hre #Htg". rewrite /sh_pay_at /sh_pay_state.
    iSplitR; [ iExact "Hst" | ]. iSplitR; [ iExact "Hre" | iExact "Htg" ].
  Qed.

  Lemma sh_pay_of_parts (T : iProp Σ) `{!Persistent T}
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    sh_pay_state Rsh n0 -∗
    (∀ (γp : gname) (N : uk_names Σ),
       ush_rest_l (PS := uprogSG_free) N γp T (cc_wc Cr) (cc_wb Cr) (cc_mid Cr γp)
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_tag_law T -∗
    sh_pay T Cr Rsh n0.
  Proof using .
    exact (sh_pay_of_parts_at UkSh.ush_line_echo T Cr Rsh n0).
  Qed.

  Global Instance sh_pay_at_persistent Dl T Cr Rsh n0 :
    Persistent (sh_pay_at Dl T Cr Rsh n0).
  Proof using . rewrite /sh_pay_at. apply _. Qed.

  Global Instance sh_pay_persistent T Cr Rsh n0 :
    Persistent (sh_pay T Cr Rsh n0).
  Proof using . rewrite /sh_pay. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* THE CARVE (lane SH-STATE): sh's static state and its line buffer,    *)
  (* out of the writable data the entry hands over.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma umap_window (g : gname) (D : gmap Z (bv 8)) (lo hi : Z) :
    ([∗ map] k ↦ b ∈ D, ubyte g k b) -∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D,
         ubyte g k b)
      ∗ ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => ~ (lo <= kv.1 < hi)) D,
           ubyte g k b).
  Proof using .
    iIntros "H".
    rewrite -(big_sepM_union (fun k b => ubyte g k b)
                (base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D)
                (base.filter (fun kv : Z * bv 8 => ~ (lo <= kv.1 < hi)) D)
                (map_disjoint_filter_complement _ D)).
    rewrite (map_filter_union_complement (fun kv : Z * bv 8 => lo <= kv.1 < hi) D).
    iExact "H".
  Qed.

  Lemma ubytes_of_window (g : gname) (D : gmap Z (bv 8)) (lo hi a : Z) (n : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> lo <= a + Z.of_nat j < hi) ->
    (forall j : nat, (j < n)%nat -> D !! (a + Z.of_nat j) = Some (f j)) ->
    ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D,
       ubyte g k b) -∗ ubytes g a n f.
  Proof using .
    intros Hr HD. iIntros "H".
    assert (Hlk : forall j : nat, (j < n)%nat ->
              base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D
                !! (a + Z.of_nat j) = Some (f j)).
    { intros j Hj. apply umap_win_lookup; [ exact (Hr j Hj) | exact (HD j Hj) ]. }
    iApply (ubytes_of_map g
              (base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D) a n f Hlk
              with "H").
  Qed.

  Lemma ustr_of_window (g : gname) (D : gmap Z (bv 8)) (lo hi a : Z) (len : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    (forall j : nat, (j <= len)%nat -> lo <= a + Z.of_nat j < hi) ->
    (forall j : nat, (j < len)%nat -> D !! (a + Z.of_nat j) = Some (f j)) ->
    D !! (a + Z.of_nat len) = Some ubyte0 ->
    ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D,
       ubyteq g DfracDiscarded k b) -∗ ustr g DfracDiscarded a len f.
  Proof using .
    intros Hne Hlen Hr HD Hnul. iIntros "#H".
    assert (Hlk : forall j : nat, (j < len)%nat ->
              base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D
                !! (a + Z.of_nat j) = Some (f j)).
    { intros j Hj. apply umap_win_lookup; [ apply Hr; lia | exact (HD j Hj) ]. }
    assert (Hlk0 : base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D
                     !! (a + Z.of_nat len) = Some ubyte0).
    { apply umap_win_lookup; [ apply Hr; lia | exact Hnul ]. }
    iApply (ustr_of_pmap g
              (base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D)
              a len f Hne Hlen Hlk Hlk0 with "H").
  Qed.

  (* THE [Rsh] SH'S STATE FIXES, at the CONSTANT break (lane SH-STATE).
     [UkShLoop.ushl_R] uncurried, at the size [UShKernel.sh_pay_key] pins;
     the three bounds [UkShFork.ushf_rest_of_body] asks of the break
     ([8344 <= sz], [pgroundup sz = sz], [usz_ok (sz + 65536)]) are CLOSED
     computations at [0x5000], which is why the existential form the
     design of record carried is not needed. *)
  Definition sh_Rsh : gname -> gname -> gname -> iProp Σ :=
    fun _ γd γs => (UkShLoop.ushl_dat γd ∗ usz γs (kexec_sz ElfUser.sh_elf))%I.

  Lemma sh_pay_state_holds : ⊢ sh_pay_state sh_Rsh 0%nat.
  Proof using .
    rewrite /sh_pay_state /sh_Rsh.
    destruct sh_tbl_parts as (Hsy & Hws & Hsy0 & Hws0).
    iModIntro. iIntros (W' γt γd γs) "%Hkey Hszf HD".
    destruct Hkey as [Hsz Hin]. rewrite <- Hsz.
    set (D0 := base.filter
          (fun kv : Z * bv 8 =>
             kv.1 < uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1)
                    - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + 0%nat)))))
          (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W'))) in *.
    assert (HD0 : forall (a : Z) (b : bv 8),
              0x2000 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D0 !! a = Some b).
    { intros a b Ha Hb. apply Hin;
        [ unfold ShData.shRodataEnd, ShData.shMemEnd; lia | exact Hb ]. }
    (* ---- window 1: the .data half, [0x2000, 0x2010) ---- *)
    iDestruct (umap_window γd D0 0x2000 0x2010 with "HD") as "[Wdat HD]".
    set (D1 := base.filter (fun kv : Z * bv 8 => ~ (0x2000 <= kv.1 < 0x2010)) D0)
      in *.
    assert (HD1 : forall (a : Z) (b : bv 8),
              0x2010 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D1 !! a = Some b).
    { intros a b Ha Hb. unfold D1. apply umap_win_lookup_out;
        [ lia | apply HD0; [ lia | exact Hb ] ]. }
    (* ---- window 2: [freep], [0x2010, 0x2018) ---- *)
    iDestruct (umap_window γd D1 0x2010 0x2018 with "HD") as "[Wfp HD]".
    set (D2 := base.filter (fun kv : Z * bv 8 => ~ (0x2010 <= kv.1 < 0x2018)) D1)
      in *.
    assert (HD2 : forall (a : Z) (b : bv 8),
              0x2018 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D2 !! a = Some b).
    { intros a b Ha Hb. unfold D2. apply umap_win_lookup_out;
        [ lia | apply HD1; [ lia | exact Hb ] ]. }
    (* ---- window 3: the line buffer, [0x2020, 0x2084) ---- *)
    iDestruct (umap_window γd D2 sh_buf (sh_buf + 100) with "HD") as "[Wbuf HD]".
    set (D3 := base.filter
                 (fun kv : Z * bv 8 => ~ (sh_buf <= kv.1 < sh_buf + 100)) D2) in *.
    assert (HD3 : forall (a : Z) (b : bv 8),
              0x2084 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D3 !! a = Some b).
    { intros a b Ha Hb. unfold D3. apply umap_win_lookup_out;
        [ unfold sh_buf; lia | apply HD2; [ lia | exact Hb ] ]. }
    (* ---- window 4: the allocator's [base] cell, [0x2088, 0x2098) ---- *)
    iDestruct (umap_window γd D3 8328 (8328 + 16) with "HD") as "[Wbs _]".
    (* ---- the lookups, run by run ---- *)
    assert (Hsymb : forall j : nat, (j < 7)%nat ->
              D0 !! (ushp_symbols + Z.of_nat j) = Some (ushp_sym_f j)).
    { intros j Hj.
      assert (Hin7 : In j (seq 0 7)) by (apply in_seq; lia).
      pose proof (proj1 (forallb_forall _ _) Hsy j Hin7) as Hb.
      apply HD0; [ unfold ushp_symbols; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hb). }
    assert (Hsymn : D0 !! (ushp_symbols + Z.of_nat 7) = Some ubyte0).
    { change (Z.of_nat 7) with 7. apply HD0; [ unfold ushp_symbols; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hsy0). }
    assert (Hwsb : forall j : nat, (j < 5)%nat ->
              D0 !! (ushp_whitespace + Z.of_nat j) = Some (ushp_ws_f j)).
    { intros j Hj.
      assert (Hin5 : In j (seq 0 5)) by (apply in_seq; lia).
      pose proof (proj1 (forallb_forall _ _) Hws j Hin5) as Hb.
      apply HD0; [ unfold ushp_whitespace; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hb). }
    assert (Hwsn : D0 !! (ushp_whitespace + Z.of_nat 5) = Some ubyte0).
    { change (Z.of_nat 5) with 5. apply HD0; [ unfold ushp_whitespace; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hws0). }
    assert (Hfpb : forall j : nat, (j < 8)%nat ->
              D1 !! (8208 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0 : mword 64) j)).
    { intros j Hj. rewrite nth_byte_zero64.
      apply HD1; [ lia | apply sh_bss_img; lia ]. }
    assert (Hbufb : forall j : nat, (j < sh_nbuf)%nat ->
              D2 !! (sh_buf + Z.of_nat j) = Some ubyte0).
    { intros j Hj. unfold sh_nbuf in Hj. apply HD2;
        [ unfold sh_buf; lia | apply sh_bss_img; unfold sh_buf; lia ]. }
    assert (Hbsb : forall j : nat, (j < 16)%nat ->
              D3 !! (8328 + Z.of_nat j) = Some ubyte0).
    { intros j Hj. apply HD3; [ lia | apply sh_bss_img; lia ]. }
    (* ---- the window-range side conditions, HOISTED (durable-notes:
           an inline [ltac:] runs against an evar) ---- *)
    assert (Rws : forall j : nat, (j <= 5)%nat ->
              0x2000 <= ushp_whitespace + Z.of_nat j < 0x2010)
      by (intros j Hj; unfold ushp_whitespace; lia).
    assert (Rsym : forall j : nat, (j <= 7)%nat ->
              0x2000 <= ushp_symbols + Z.of_nat j < 0x2010)
      by (intros j Hj; unfold ushp_symbols; lia).
    assert (Rfp : forall j : nat, (j < 8)%nat ->
              0x2010 <= 8208 + Z.of_nat j < 0x2018) by (intros j Hj; lia).
    assert (Rbs : forall j : nat, (j < 16)%nat ->
              8328 <= 8328 + Z.of_nat j < 8328 + 16) by (intros j Hj; lia).
    assert (Rbuf : forall j : nat, (j < sh_nbuf)%nat ->
              sh_buf <= sh_buf + Z.of_nat j < sh_buf + 100)
      by (intros j Hj; unfold sh_nbuf in Hj; lia).
    assert (L5 : Z.of_nat 5 < 2 ^ 31) by (vm_compute; reflexivity).
    assert (L7 : Z.of_nat 7 < 2 ^ 31) by (vm_compute; reflexivity).
    (* ---- persist the .data half and assemble ---- *)
    iMod (uarea_persist γd
            (base.filter (fun kv : Z * bv 8 => 0x2000 <= kv.1 < 0x2010) D0)
            with "Wdat") as "#Wdatq".
    iModIntro. iExists (fun _ : nat => ubyte0).
    iSplitR "Wbuf".
    - iSplitR "Hszf"; [ | iExact "Hszf" ].
      rewrite /UkShLoop.ushl_dat.
      iSplitR.
      { iApply (ustr_of_window γd D0 0x2000 0x2010 ushp_whitespace 5 ushp_ws_f
                  ushp_ws_f_nonul L5 Rws Hwsb Hwsn with "Wdatq"). }
      iSplitR.
      { iApply (ustr_of_window γd D0 0x2000 0x2010 ushp_symbols 7 ushp_sym_f
                  ushp_sym_f_nonul L7 Rsym Hsymb Hsymn with "Wdatq"). }
      iSplitL "Wfp".
      { iPoseProof (ubytes_of_window γd D1 0x2010 0x2018 8208 8
                      (nth_byte (mword_of_int 0 : mword 64))
                      Rfp Hfpb with "Wfp") as "H".
        rewrite /uword /uwordq /ubytes. iExact "H". }
      iExists (fun _ : nat => ubyte0).
      iApply (ubytes_of_window γd D3 8328 (8328 + 16) 8328 16
                (fun _ : nat => ubyte0) Rbs Hbsb with "Wbs").
    - iApply (ubytes_of_window γd D2 sh_buf (sh_buf + 100) sh_buf sh_nbuf
                (fun _ : nat => ubyte0) Rbuf Hbufb with "Wbuf").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* INIT'S PINNED EXEC SLOT, as one persistent premise.                   *)
  (*                                                                       *)
  (* [T] is the application's TAINT -- the disjunct its claim law admits    *)
  (* when the pins may have been broken -- and it is Persistent AND        *)
  (* Timeless because the claim sits under [AppInv.app_body]'s later and   *)
  (* each fire strips it ([PinnedExec]'s header).                          *)
  (* ------------------------------------------------------------------- *)
  (* THE TAINT ARM IS INDEXED BY THE PAY FACT, AT EVERY CONSTANT PAYLOAD:
     a tainted process runs arbitrary code on the generic family, which is
     indexed by the pay fact ([UexecExecMint.uslot_mint_pay]) -- and the
     payload of the process init execs sh into is the one init chose at the
     fork that made it, which is the console reader token
     ([UserConsole.ucons_pay]) and not the trivial one.  So the arm is
     ∀-bound over the resource [R] the payload names: the tainted slot
     HOLDS it, pays it at exit and at every kill check, and hands it on
     across an exec (GENERIC-PAY).  Under the [□] and not outside it,
     because the arm is persistent and is spent at whatever payload the
     ROUND chose -- the console token of that round's own position pair.
     [UexecExecMint.uslot_mint_all] is exactly this proposition. *)
  (* THE PINS LAW IS THE WHOLE ONE (lane E4).  sh does not only get its own
     row: its [exec] of the parsed command is a PINNED exec at
     [FsEchoPin.era0_echo_pins], and both that and [FsShPin.era0_sh_pins]
     are conjuncts of [EchoFsPure.echo_fs_pure], so what crosses is the one
     law and each consumer projects ([sh_pins_of_fs_pure] below is /sh's
     projection; E4's is /echo's). *)
  Definition init_sh_slot_core (T : iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W)
     ∗ Pay)%I.

  (* THE CONSOLE CREDENTIAL IS NOT HERE but a premise of the constructor
     ([init_exec_sup_of_sh_slot]'s third, lane SH-OPEN): which of sh's two
     pinned leaves it can make is decided by /INIT'S OWN mknod, mid-walk,
     and this record is fixed at /init's entry.

     AND THE ERA'S SIDE OF THAT PREMISE IS NOT HERE EITHER.  Stating the
     bridge from [UInitCons.init_cons_cred] to those two leaves IN THIS
     FILE makes its elaboration explode -- measured at 8.6 GB RSS in 20
     seconds, killed as [UInitSh.vo Error 143].  The leaves are [UkSh]'s,
     over ITS section's binder list, and this file's is a different one;
     the bridge therefore lives in [UInitBoot.v], whose context is the
     assembly's ([UInitBoot.ush_cons_in_of_Cns]). *)
  Definition init_sh_slot (T : iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    init_sh_slot_core T Pay.

  Global Instance init_sh_slot_core_persistent T Pay `{!Persistent Pay} :
    Persistent (init_sh_slot_core T Pay).
  Proof using . rewrite /init_sh_slot_core. apply _. Qed.

  Global Instance init_sh_slot_persistent T Pay `{!Persistent Pay} :
    Persistent (init_sh_slot T Pay).
  Proof using . rewrite /init_sh_slot /init_sh_slot_core. apply _. Qed.

  (* the projection /sh's own pinned exec wants *)
  Lemma sh_pins_of_fs_pure (T : iProp Σ) :
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T)) -∗
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜FsShPin.era0_sh_pins v⌝ ∨ T)).
  Proof using .
    iIntros "#Hl !>" (v) "Hp".
    iDestruct ("Hl" $! v with "Hp") as "[Hp [%Hf | HT]]";
      [ iFrame "Hp"; iLeft; iPureIntro; exact (proj1 (proj2 Hf))
      | iFrame "Hp"; iRight; iExact "HT" ].
  Qed.

  (* ...and /echo's, which is lane E4's seam: one [iApply] of this. *)
  Lemma echo_pins_of_fs_pure (T : iProp Σ) :
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T)) -∗
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜FsEchoPin.era0_echo_pins v⌝ ∨ T)).
  Proof using .
    iIntros "#Hl !>" (v) "Hp".
    iDestruct ("Hl" $! v with "Hp") as "[Hp [%Hf | HT]]";
      [ iFrame "Hp"; iLeft; iPureIntro; exact (proj2 (proj2 Hf))
      | iFrame "Hp"; iRight; iExact "HT" ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ROOM, as closed arithmetic.                                       *)
  (*                                                                       *)
  (* [kexec_sz sh_elf] is 0x5000 and the argument block is one two-byte    *)
  (* string plus a two-word pointer vector, so [kxc_sp_final] lands at     *)
  (* 0x4FE0 -- 0xFE0 above the stack page's base, which is what sh's       *)
  (* frames have to fit in.                                                *)
  (* ------------------------------------------------------------------- *)
  Lemma init_sh_sp_final (alen : nat -> nat) :
    alen 0%nat = 2%nat -> kxc_sp_final 0x5000 alen 1%nat = 0x4FE0.
  Proof using .
    intro Ha. unfold kxc_sp_final. cbn [kxc_sp]. rewrite Ha.
    vm_compute. reflexivity.
  Qed.

  Lemma init_sh_room (alen : nat -> nat) (n0 : nat) :
    alen 0%nat = 2%nat ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    kexec_sz ElfUser.sh_elf - PGSIZE
      + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= kxc_sp_final (kexec_sz ElfUser.sh_elf) alen 1%nat.
  Proof using .
    intros Ha Hn0. rewrite sh_kexec_sz. rewrite (init_sh_sp_final alen Ha).
    unfold PGSIZE. lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE PATH, read out of init's read-only image.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma init_sh_path_of (M : gmap Z (bv 8)) :
    uimg_sub UCodeInit.init_ro M ->
    exec_path_of M (mword_of_int 0x9b8 : mword 64) init_sh_pl.
  Proof using .
    intro Hro.
    pose proof (bool_decide_eq_true_1 _ init_ro_sh_bool) as (Hb0 & Hb1 & Hb2).
    split_and!.
    - split.
      + rewrite init_sh_pl_len. clear; lia.
      + intros j b Hj.
        destruct j as [| [| j]]; cbn in Hj; try discriminate Hj;
          injection Hj as <-; (intro Hc; apply (f_equal bv_unsigned) in Hc;
                               vm_compute in Hc; discriminate Hc).
    - intros j b Hj.
      destruct j as [| [| j]]; cbn in Hj; try discriminate Hj.
      + apply Hro. rewrite Hb0. exact Hj.
      + apply Hro. rewrite Hb1. exact Hj.
    - rewrite init_sh_pl_len. apply Hro. exact Hb2.
  Qed.

  (* THE HEAD'S ROWS 0 AND 2 AT ONCE (lane IO-LEAF, M4a(3)).
     [UInitFd.ufd_head_row] and [UInitFd.ufd_head_row12] each SPEND the
     head, and this constructor needs BOTH readings: row 0 is what sh's
     entry is told ([UkSh.ush_fd0]) and row 2 is what its prompt's payment
     asks for ([UShOut.ksh_w_of_link_prompt]).  So they are read off the
     one head together, at the same three arms.  (The two lemmas above
     stay: they are what every other consumer takes.) *)
  Lemma ufd_head_rows (T : iProp Σ) (st : fdstate) (γfd : gname)
      (fdv : list fdstate) :
    ufd_auth γfd fdv -∗ ufd_head T st γfd -∗
    ufd_auth γfd fdv ∗
    ((⌜take NSTD fdv !! 0%nat = Some st⌝ ∗ ⌜take NSTD fdv !! 2%nat = Some st⌝)
     ∨ ⌜take NSTD fdv !! 0%nat = Some FdClosed⌝ ∨ T).
  Proof using .
    rewrite /ufd_head /ufd_headL.
    iIntros "Ha [H | [H | [_ HT]]]".
    - iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iLeft. iSplit; iPureIntro;
        [ exact (ufd_l3_row0 st) | exact (ufd_l3_row2 st) ].
    - iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iRight. iLeft. iPureIntro. exact ufd_l0_row0.
    - iFrame "Ha". iRight. iRight. iExact "HT".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ASSEMBLY: init's pinned bundle pays its exec supply.              *)
  (* ------------------------------------------------------------------- *)
  (* The deposit introduction this used to carry
     ([sbundle_pay_exec_intro_refR]) is [ExecRun]'s now: it is the general
     step from an exec bundle to the deposit and is not /init's.  The
     assembly below ([init_exec_sup_of_sh_slot]) is an INSTANCE of the
     U-tier rule ([ExecRun.udepw_at_refR_ids_of_sup_ids], lane EX-4) and
     spells only /init's own readings. *)

  (* /init's all-closed ledger is the closed-arm shape at zero opens
     (step 4) *)
  Lemma ufd_l0_lcl : UkSh.ush_lcl UInitFd.ufd_l0 0%nat.
  Proof using .
    split; [ intros i Hi; lia | ].
    intros i [_ Hi]. unfold NSTD in Hi.
    destruct i as [| [| [| i]]];
      [ exact UInitFd.ufd_l0_row0 | vm_compute; reflexivity
      | exact UInitFd.ufd_l0_row2 | lia ].
  Qed.

  (* =================================================================== *)
  (*  SH'S ENTRY, AS THE NAMED OBLIGATION (E) (lane EX-1)                  *)
  (*                                                                      *)
  (*  [ExecEntry.image_entry] at /sh, with /init as the caller: exactly    *)
  (*  the [□]-constructor [PinnedExec.pinned_exec_bundle] takes, named.    *)
  (*  It was written inline inside [init_exec_sup_of_sh_slot] below, which *)
  (*  is where it stopped being visible as a THEOREM ABOUT SH; hoisted, it *)
  (*  is one of the two obligations an exec bundle consumes and it can be  *)
  (*  read without the deposit around it.                                  *)
  (*                                                                      *)
  (*  WHAT THE STATEMENT SAYS ABOUT THE SEAM.  Four of the parameters are  *)
  (*  the CALLER's readings and sh fixes three of them: the working        *)
  (*  directory is [FsImg.ROOTINO] (sh's pinned open of the console is a   *)
  (*  path, so the cwd is part of what it is told), the children set is    *)
  (*  empty and the pid is not <init>'s (sh's wait redeems one child       *)
  (*  against those two).  The fourth, the descriptor view [fdv], is       *)
  (*  /init's own table, and the one row sh reads off it is fd 0's.  The   *)
  (*  fifth and sixth -- the caller's image [M] and its argv pointer --    *)
  (*  are what [init_args_det] is about: sh's ROOM bound is an inequality  *)
  (*  about the vector, and /init's is the constant one its image holds.   *)
  (*                                                                      *)
  (*  THE CHAIN TO [UShKernel.sh_image_entry_at] IS NOT TAKEN HERE, and    *)
  (*  the reason is [Pay]: this lemma's payload is /init's quadruple       *)
  (*  (sh's persistent state, the position, the lease and the ledger row   *)
  (*  with its credential) while sh's own entry is stated at the triple    *)
  (*  its body consumes, and the step between them is the credential       *)
  (*  conversion below -- which reads /init's ledger and so belongs on     *)
  (*  this side.  Both lemmas are [sh_slot_of_kexec] at the named          *)
  (*  obligation; neither restates it.                                     *)
  (* =================================================================== *)
  (* =================================================================== *)
  (*  THE SAME ENTRY AT AN ARBITRARY INPUT DISCIPLINE (lane APP-FILE)     *)
  (*                                                                      *)
  (*  [UShKernel.sh_slot_of_kexec] is already parameterised on the        *)
  (*  discipline and on the four readings of it the walk spends; this      *)
  (*  entry only RELAYED echo's five.  The twin takes them, and            *)
  (*  [init_sh_image_entry] below is this at echo's -- so the landed type  *)
  (*  does not move and [UInitBoot] is unchanged.  The FILE application    *)
  (*  instantiates it at [FileDisc.disc_input_f] with                      *)
  (*  [FileReadInst.file_gets_holds]'s three and                           *)
  (*  [UkShRedirBody.ush_line_file] for [Dl].                              *)
  (*  The comments on every other binder are on the landed statement.     *)
  (* =================================================================== *)
  Lemma init_sh_image_entry_at
      (Dsc : list (bv 8) -> Prop)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b]) -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl]) ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (T : iProp Σ) `{!Persistent T}
      (cn : cons_names) (K : iProp Σ) `{!Persistent K}
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat)
      (γp : gname) (np : nat) (N : uk_names Σ) (l : list fdstate)
      (M : gmap Z (bv 8)) (fdv : list fdstate)
      (cs : gset gname) (pidv : mword 32) :
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    uimg_sub UInitArgv.init_argv_map M ->
    uimg_sub UCodeInit.init_ro M ->
    take NSTD fdv = l ->
    cs = ∅ ->
    bv_unsigned pidv <> 1 ->
    length fdv = NOFILE ->
    cons_cred_holds_at cn T Dsc Hdncr Hdshort Dl Hdline Cr ->
    UkRun.urun_nopipe fdv -∗
    udep (PS := uprogSG_free) -∗
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) (cc_wc Cr) -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T K) ∗ K)
     ∨ T) -∗
    UkSh.ush_fd0 T (take NSTD fdv) -∗
    (* the exec'ing table's rows are closed or the console, or the taint
       (seccomp S4) *)
    (⌜ush_view_ok fdv⌝ ∨ T) -∗
    (∀ sts secc, image_entry_taint T sts secc
       (ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr))) uslot) -∗
    image_entry ElfUser.sh_elf M (mword_of_int 0x1000 : mword 64) fdv
      FsImg.ROOTINO ProcDefs.secc_all cs pidv
      (ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)))
      (sh_pay_at Dl T Cr Rsh n0 ∗ upos γp np
         ∗ ucons_pay cn γp T (cc_rd Cr) (-1)
         ∗ (UserFd.ustd (ukn_fd N) l
            ∗ UkInit.init_lend_cred T
                (FdOpen true true (FdDevice ConsoleInv.CONSOLE))
                (cc_wp Cr) (cc_wbn Cr) l np))%I
      uslot.
  Proof using .
    intros Hpsok_free Hn0 Hsav Hsro Hl Hcs Hpid Hlen HCr.
    pose proof HCr as (Hrl & Hpm1 & Hpm3 & Hpmwb & Hwc
                       & Hwbwc & Hwbl & Hwbr & Hbd & Hpw).
    (* the credential's laws are stated over EVERY position ghost; this
       lemma runs at the one [γp] its caller minted for the round. *)
    specialize (Hrl γp). specialize (Hpm1 γp). specialize (Hpm3 γp).
    specialize (Hpmwb γp). specialize (Hwc γp).
    specialize (Hwbr γp). specialize (Hbd γp).
    iIntros "#Hnpw #Hdep #Hdp #Hplaw #Hcons #Hfd0 #Hvok #Hgen'".
    rewrite /image_entry. iModIntro.
    iIntros (na alen afun W')
      "%Hok %Hcwd0 %Hlzf %Hscf %Hchq %Hpiq %Hargs #Hmp
       [[#Hp1 [#Hp2 #Htag]] [Hps [Hls [Hstd' Hcred]]]]".
    assert (Hch0 : uvis_ch W' = ∅) by (rewrite Hchq; exact Hcs).
    assert (Hpid1 : bv_unsigned (uvis_pid W') <> 1)
      by (rewrite Hpiq; exact Hpid).
    (* ...AND THE CREDENTIAL, AT THE SAME LEDGER (step 3; M6b): /init
       lent it correlated with the row ([UkInit.init_lend_cred]), so it
       lands in the loop's slot on the arm the row names -- the
       both-console arm, through the lend's conversion [Hpw]; the closed
       arm (slot 2 of the all-closed ledger); or the affine one.  The old
       record's ledger fragment is dropped: the process that execs is
       replaced. *)
    iAssert ((∃ I : list (bv 8), ⌜length I = np⌝
                ∗ UkSh.ush_wcp (cc_wc Cr) (cc_wb Cr) (take NSTD fdv) I 0%nat)
             ∨ T)%I
      with "[Hcred]" as "Hwcp".
    { rewrite Hl /UkInit.init_lend_cred.
      iDestruct "Hcred" as "[[%Hl3 Hc] | [[%Hl0 Hb] | #HT]]".
      - iPoseProof (Hpw np) as "Hpw'".
        iDestruct ("Hpw'" with "Hc") as (I) "[%HI Hc]".
        iLeft. iExists I. iSplitR; [ by iPureIntro | ].
        rewrite /UkSh.ush_wcp. iLeft. iSplitR.
        + iPureIntro. rewrite Hl3. split_and!.
          * exists true. exact (ufd_l3_row0 _).
          * exists true. exact (ufd_l3_row1 _).
          * exists true. exact (ufd_l3_row2 _).
        + iExact "Hc".
      - (* the all-closed ledger, with none of the preamble's opens landed
           yet (step 4: [UkSh.ush_lcl] at 0) *)
        rewrite /cc_wbn. iDestruct "Hb" as (I) "[%HI Hb]".
        iLeft. iExists I. iSplitR; [ by iPureIntro | ].
        rewrite /UkSh.ush_wcp. iRight. iFrame "Hb". iPureIntro. rewrite Hl0.
        split; [ | lia ]. exists 0%nat. split; [ lia | exact ufd_l0_lcl ].
      - (* the taint: a tainted shell runs on the generic slot, and the
           entry law's right arm is where it goes (lane EXEC-SEAM, (C)) *)
        iRight. iExact "HT". }
    iClear "Hstd'".
    destruct (init_args_det M na alen afun Hsav Hsro Hargs) as [-> Halen].
    (* STAGED, AND WITH BOTH CLASS ARGUMENTS GIVEN.  [sh_slot_of_kexec]
       is polymorphic in the PAIR ([UShKernel.v] binds [{SG : uexecSG}]
       and [{PS : uprogSG}] as section variables), so leaving [SG] to
       [iApply] means solving it against the goal while [PS] is already
       fixed -- and that unification runs inside [UexecSG.sbundle]'s
       tower and does not return.  The [pose proof] elaborates the
       INSTANTIATED lemma with no goal in play; the [iApply] then has
       only the resource list to do. *)
    pose proof (UShKernel.sh_slot_of_kexec (SG := uexecSG_xv6)
                  (PS := uprogSG_free)
                  Rsh γp cn T K
                  (ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)))
                  (ucons_pay cn γp T (cc_rd Cr))
                  ((cc_mid Cr) γp) (cc_wc Cr) (cc_wb Cr)
                  (* THE DISCIPLINE AND ITS FOUR READINGS, RELAYED (lane
                     LINK-GEN-5/6, generalised for lane APP-FILE): the
                     leaf [Hrl] came in at the same [Dsc], because
                     [cons_cred_holds_at]'s first conjunct is
                     [UkSh.ush_read_recv_leaf_at] at it. *)
                  Dsc Hdncr Hdshort Dl Hdline
                  Hrl Hpm1 Hpm3
                  Hpmwb Hwc Hwbwc Hwbl Hwbr
                  1%nat alen afun fdv W' n0 np
                  Hbd
                  (ucons_pay_const cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr))) Hok Hcwd0
                  (init_sh_room alen n0 Halen Hn0) Hlen Hlzf Hscf Hch0 Hpid1)
      as Hsk.
    iDestruct (image_entry_taint_all_elim with "Hgen'") as "#Hgen0".
    iApply (Hsk with "[] Hnpw Hdep Hdp Htag Hplaw [] [] Hvok Hcons Hgen0 Hmp Hps
                      Hls Hwcp").
    - (* THE KEY'S OWN READING (lane SH-STATE): [sh_pay_state]'s wand
         takes [UShKernel.sh_pay_key], and the two facts it is derived
         from are the very ones handed to [sh_slot_of_kexec] above. *)
      iModIntro. iIntros (γt γd γs) "Hsz Hlo".
      iApply ("Hp1" $! W' γt γd γs with "[%] Hsz Hlo").
      exact (UShKernel.sh_pay_key_of_kexec 1%nat alen afun fdv W' n0 Hok
               (init_sh_room alen n0 Halen Hn0)).
    - iIntros (N0). iApply ("Hp2" $! γp N0).
    - iExact "Hfd0".
  Qed.

  Lemma init_sh_image_entry (T : iProp Σ) `{!Persistent T}
      (cn : cons_names) (K : iProp Σ) `{!Persistent K}
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat)
      (γp : gname) (np : nat) (N : uk_names Σ) (l : list fdstate)
      (M : gmap Z (bv 8)) (fdv : list fdstate)
      (cs : gset gname) (pidv : mword 32) :
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    (* the two readings of /init's own image the argument vector is
       determined by ([init_args_det]) *)
    uimg_sub UInitArgv.init_argv_map M ->
    uimg_sub UCodeInit.init_ro M ->
    (* /init's ledger, its children set and its pid, as the caller holds
       them *)
    take NSTD fdv = l ->
    cs = ∅ ->
    bv_unsigned pidv <> 1 ->
    length fdv = NOFILE ->
    (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set is
       dead data now ([UkRun.urun_parked_row]), so this entry may be taken
       at a key with a HELD descriptor (design/app-file.md SS3 fact 4). *)
    cons_cred_holds cn T Cr ->
    (* ...and whether /init's own table holds a pipe row (design/pipe.md,
       "The exit path"): sh's table IS this one
       ([SpecKexec.kexec_image_ok_fd]), sh's run carries the fact between
       traps, and sh's exit leaf mints the tear-down's bundle row off it. *)
    UkRun.urun_nopipe fdv -∗
    udep (PS := uprogSG_free) -∗
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) (cc_wc Cr) -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T K) ∗ K)
     ∨ T) -∗
    UkSh.ush_fd0 T (take NSTD fdv) -∗
    (* the exec'ing table's rows are closed or the console, or the taint
       (seccomp S4) *)
    (⌜ush_view_ok fdv⌝ ∨ T) -∗
    (∀ sts secc, image_entry_taint T sts secc
       (ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr))) uslot) -∗
    image_entry ElfUser.sh_elf M (mword_of_int 0x1000 : mword 64) fdv
      FsImg.ROOTINO ProcDefs.secc_all cs pidv
      (ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)))
      (sh_pay T Cr Rsh n0 ∗ upos γp np
         ∗ ucons_pay cn γp T (cc_rd Cr) (-1)
         ∗ (UserFd.ustd (ukn_fd N) l
            ∗ UkInit.init_lend_cred T
                (FdOpen true true (FdDevice ConsoleInv.CONSOLE))
                (cc_wp Cr) (cc_wbn Cr) l np))%I
      uslot.
  Proof using .
    exact (init_sh_image_entry_at EchoDisc.disc_input UkSh.ush_disc_snoc_ncr
             EchoDisc.disc_input_rest_short UkSh.ush_line_echo
             UkSh.ush_disc_line_echo
             T cn K Cr Rsh n0 γp np N l M fdv cs pidv).
  Qed.

  (* =================================================================== *)
  (*  THE SAME ASSEMBLY AT AN ARBITRARY INPUT DISCIPLINE (lane APP-FILE)  *)
  (*                                                                      *)
  (*  [init_sh_image_entry_at]'s five extra parameters, relayed, and the   *)
  (*  credential's ten laws at the same [Dsc]                              *)
  (*  ([cons_cred_holds_at]).  [init_exec_sup_of_sh_slot] below is this    *)
  (*  at echo's five, so [UInitBoot.init_cons_sup_of_sh_slot] does not     *)
  (*  move.  Every other binder is commented on the landed statement.     *)
  (* =================================================================== *)
  Lemma init_exec_sup_of_sh_slot_at
      (Dsc : list (bv 8) -> Prop)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b]) -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl]) ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cn : cons_names) (st : fdstate) (K : iProp Σ) `{!Persistent K}
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    cons_cred_holds_at cn T Dsc Hdncr Hdshort Dl Hdline Cr ->
    udep (PS := uprogSG_free) -∗
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) (cc_wc Cr) -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T K) ∗ K)
     ∨ T) -∗
    init_sh_slot T (sh_pay_at Dl T Cr Rsh n0) -∗
    UkInit.init_exec_sup_lend cn T st Cr.
  Proof using .
    intros Hpsok_free Hn0 Hst HCr.
    pose proof HCr as (Hrl & Hpm1 & Hpm3 & Hpmwb & Hwc
                       & Hwbwc & Hwbl & Hwbr & Hbd & Hpw).
    subst st.
    iIntros "#Hdep #Hdp #Hplaw #Hcons (#Hinv & #Hcl0 & #Hgen & #Hpay)".
    (* E4: what crosses is the WHOLE pins law and each consumer projects *)
    iDestruct (sh_pins_of_fs_pure T with "Hcl0") as "#Hcl".
    (* THE LEDGER IS TAKEN AND NOT READ: sh's entry says nothing about its
       standard streams, and the only descriptor fact this constructor
       needs is [length fdv = NOFILE], which comes off the LENT authority
       ([UserFd.ufd_auth_len]) rather than off the ledger. *)
    iModIntro. iIntros (γp np N m pc l)
      "%Hpeq %Ha0 %Ha1 #Hro #Hargv Hstd Hrow Hcred Hpos Hlease Hchf Hpidf".
    (* ...and the taint arm at the SAME payload: a tainted process runs on
       the generic family, which exists at any constant payload and HOLDS
       the resource it names ([UexecExecMint.uslot_mint_pay]).  The payload
       is literally the constant function at what the kill status names
       ([UserConsole.ucons_pay_eta]).  It names no key, so it is built
       before the deposit's own ∀ and not inside it. *)
    (* ...AND THE TAINT ARM IS HANDED NOTHING AT ALL NOW (lane SELF-KILL,
       P6b): the generic family's constant payload is carried
       PERSISTENTLY ([UexecExecMint.uslot_mint_all] at
       [□ (app_taint -∗ R)]), and the arm builds it out of the TAINT
       it is already holding ([UserConsole.ucons_pay_taint]) -- which is
       the whole reason a tainted process needs no lease. *)
    iAssert (∀ sts secc, image_entry_taint T sts secc
               (ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr))) uslot)%I as "#Hgen'".
    { iIntros (sts secc). iApply image_entry_taint_intro. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wbn Cr)) (-1)) W' with "HT [Hmp] []").
      - rewrite ucons_pay_eta. iExact "Hmp".
      - iModIntro. iIntros "_". iApply (ucons_pay_taint with "HT"). }
    (* THE UPDATE DOOR COSTS ECHO ONE TOKEN (lane TL-9): the node's
       conclusion is [|==> udepw_at_refR_ids ...] now
       ([UkInit.init_exec_sup_pos]), and echo spends nothing to open it --
       its credential is the taint, which is persistent. *)
    iModIntro.
    (* ---- AND THE WHOLE OF THE REST IS THE U-TIER RULE (lane EX-4).
       [ExecRun.udepw_at_refR_ids_of_sup_ids] is the general step from an
       exec bundle to the deposit the leaf consumes; what is left below is
       /init's own SUPPLY -- its readings of its own image and of the
       record's authorities, the PIN as (W)'s supplier, and sh's entry. ---- *)
    iApply (udepw_at_refR_ids_of_sup_ids N m pc
              (mword_of_int 0x9b8) (mword_of_int 0x1000)
              FsImg.ROOTINO T init_sh_pl ElfUser.sh_elf 1%nat
              (sh_pay_at Dl T Cr Rsh n0 ∗ upos γp np
                 ∗ ucons_pay cn γp T (cc_rd Cr) (-1)
                 ∗ (UserFd.ustd (ukn_fd N) l
                    ∗ UkInit.init_lend_cred T
                        (FdOpen true true (FdDevice ConsoleInv.CONSOLE))
                        (cc_wp Cr) (cc_wbn Cr) l np))%I
              _ sh_elf_loadable Ha0 Ha1
              with "[] [] [Hstd Hrow Hcred Hpos Hlease Hchf Hpidf]").
    (* ---- THE REFUND IS THE LEND ITSELF (lane KILL-PAY, K4(a), ruling R-A;
       lane M6b): what init's child put into this deposit is the bundle's
       [Pay] -- sh's entry payload, the position, the lease, the ledger and
       the credential -- and a FAILED exec hands the last four back at the
       shapes they went in at ([UkInit.init_lend_ref]), which is what pays
       the child's diagnostic through the link and then its own [exit(1)]
       ([UkInitMain.wp_kinit_main_die_de]).  The wand drops only [sh_pay],
       which is persistent anyway. ---- *)
    { iIntros "!> (_ & Hps & Hls & Hstd & Hcred)".
      rewrite /UkInit.init_lend_ref. iFrame "Hstd Hps Hls Hcred". }
    { rewrite Hpeq. iIntros (sts). iApply "Hgen'". }
    rewrite /uexec_sup_run_ids.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd Hids".
    (* the run's two table rows come in bundled (lane OFF-HAND-3, R1);
       what the entry below is stated at is still the pipe half. *)
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    (* ---- THE TWO IDENTITY READINGS (lane EXEC-SEAM), off the lent
       authorities against the child's own fragments: the key's children
       set is EMPTY and its pid is not <init>'s.  Both are pure, so the
       fragments are spent and the authorities go straight back. ---- *)
    iDestruct (urun_ids_ch with "Hids") as "[Hcha Hidsb]".
    iDestruct (UserChildren.uch_agree with "Hcha Hchf") as %Hcs.
    iDestruct ("Hidsb" $! cs with "Hcha") as "Hids".
    iDestruct "Hpidf" as (p) "[%Hp1 Hpidf]".
    iDestruct (urun_ids_pid with "Hids") as "[Hpida Hidsb]".
    iDestruct (UserChildren.upid_agree with "Hpida Hpidf") as %Hpv.
    iDestruct ("Hidsb" with "Hpida") as "Hids".
    iClear "Hchf Hpidf".
    (* ---- the two image readings, off the lent heap ---- *)
    iAssert (⌜uimg_sub UCodeInit.init_ro M⌝)%I as %Hsro.
    { iIntros (a b Hb).
      rewrite /init_rodata /utext_img.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hro") as "Hb".
      iDestruct (uheap_text with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    iAssert (⌜uimg_sub UInitArgv.init_argv_map M⌝)%I as %Hsav.
    { iIntros (a b Hb).
      rewrite /init_argv.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hargv") as "Hb".
      iDestruct (uheap_ubyte with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    (* ---- the descriptor list, off the lent authority ---- *)
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    (* ...AND THE ROW SH'S ENTRY IS TOLD, read off INIT'S OWN LEDGER
       against that same authority ([UserFd.ustd_agree]): the ledger is
       spent here -- the process that execs is replaced, and the new image
       gets its ledger from its own run -- and its row ([UInitFd.ufd_row])
       is what sh's entry is told about slot 0. *)
    iDestruct (ustd_agree (ukn_fd N) fdv l with "Hufd Hstd") as %Hl.
    iAssert (UkSh.ush_fd0 T (take NSTD fdv)) with "[Hrow]" as "#Hfd0".
    { rewrite Hl /UInitFd.ufd_row. iDestruct "Hrow" as "[%Hr1 | [%Hr2 | HT]]".
      - iLeft. iPureIntro. left. exists true. rewrite Hr1. exact (ufd_l3_row0 _).
      - iLeft. iPureIntro. right. rewrite Hr2. exact ufd_l0_row0.
      - iRight. iExact "HT". }
    (* THE CREDENTIAL AND THE LEDGER STAY AT THE LEND'S OWN SHAPE UNTIL THE
       EXEC HAS SUCCEEDED (lane M6b): they go into the deposit as they are,
       so that a FAILED exec refunds them as they are
       ([UkInit.init_lend_ref]) -- the shell's slot converts the credential
       where it is built ([Hcon] below), and the refund wand hands the four
       back without looking at them. *)
    iFrame "Hheap Hufd Hids".
    (* ---- (W)'s PURE INPUT: the path /init's a0 names, off its rodata ---- *)
    iSplitR "Hpos Hlease Hstd Hcred".
    { iPureIntro. exact (init_sh_path_of M Hsro). }
    (* ---- (W) ITSELF, AT THE PIN SUPPLIER: era-0's claim about /sh, read
       out of the application's invariant ([ExecRun.exec_walk_of_pin]) ---- *)
    iSplitR "Hpos Hlease Hstd Hcred".
    { iApply (exec_walk_of_pin FsShPin.era0_sh_pins T FsImg.ROOTINO
                init_sh_pl [FsImg.ROOTINO; FsShPin.SH_INO] FsShPin.SH_INO
                (MkAnode (AFile ElfUser.sh_elf) 1%nat) init_sh_pin_resolves
                with "Hcl Hinv"). }
    iSplitR "Hpos Hlease Hstd Hcred".
    (* ---- sh's constructor, at every key the image fact admits ---- *)
    (* THE PAYLOAD RIDES WITH THE PAY FACT ([SpecKexec.exec_slot_pre]): the
       kernel holds the exec'ing process's own payment across this call and
       hands it to whatever slot answers, so sh's entry gets its exit
       payload -- the console reader token -- from here and from nowhere
       else (EXEC-PAY, GENERIC-PAY). *)
    (* THE ALL-PARKED ROW IS THE RUN'S OWN NOW (lane OFF-HAND-4, S1/S2).
       It used to have to ride the kexec SLOT WANDS, because the only
       thing this tier could say about its table was [Hl : take NSTD fdv =
       l] -- the low three slots -- and the rest was unconstrained.  The
       record's HELD SET says it: [UkRun.urun_rows] carries [fdv_held_in
       (ukn_held N) fdv] at every trap, and at the empty set that IS
       all-parkedness ([Hpks] above).  The key sh resumes at inherits it
       through [SpecKexec.kexec_image_ok_parked]. *)
    (* THE LINEAR HALF OF [Pay] IS THE POSITION: [UInitSh.sh_pay] is
       persistent, so what actually crosses [PinnedExec]'s one linear slot
       is [UserConsole.upos] at the pair init minted for this round.  The
       exit payload is NOT there -- it arrives at the constructor wand from
       the kernel's own payment. *)
    (* [init_sh_image_entry] above: obligation (E) at /sh, with /init's own
       four readings as the parameters they are equations against.  It was
       written here inline. *)
    { rewrite Hpeq.
      iApply (init_sh_image_entry_at Dsc Hdncr Hdshort Dl Hdline
                T cn K Cr Rsh n0 γp np N l
                M fdv cs pidv Hpsok_free Hn0 Hsav Hsro Hl Hcs
                ltac:(rewrite Hpv; exact Hp1) Hlen HCr
                with "Hnp0 Hdep Hdp Hplaw Hcons Hfd0 Hgen'"). }
    (* ...AND THE LINEAR PAYLOAD, WHOLE: [PinnedExec]'s one [Pay] slot is
       sh's persistent state, the position init minted for this round, the
       lease, and the ledger with its credential. *)
    iFrame "Hpay Hpos Hlease Hstd Hcred".
  Qed.

  Lemma init_exec_sup_of_sh_slot (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cn : cons_names) (st : fdstate) (K : iProp Σ) `{!Persistent K}
      (* ...AND THE APPLICATION'S PER-POSITION CREDENTIAL (lane IO-LEAF,
         M5): [UserConsole.ucons_pay]'s [Rd], which rides sh's exit payload
         under the same existential as the cursor and so round-trips
         through /init's wait.  A parameter for [T]'s reason -- this file
         names no era. *)
      (* ...AS THE PAIR (step 3): the exit family is [UkInit.init_rd (cc_rd Cr) (cc_wb Cr)]
         -- the READ side of the lease, which is what the child is handed
         ([(cc_rd Cr)], the lend family), beside the banner-owed credential the
         child's shell assembles where it leaves. *)
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    (* the numbers sh admits -- THE FREE ONES (lane SUPPLY-SPLIT) *)
    (* AT THE FREE INSTANCE, NAMED AND NOT RESOLVED (lane SUPPLY-SPLIT's
       own intent, ruled for E2).  A VERIFIED program's slot never takes
       the taint: [UkRun.udep] at the ambient [UexecExecInst.uprogSG_gen]
       is [box Dsup] with [Dsup := xv6_ssupply := AppInv.app_sup], and for
       the echo era the supply and the taint are interderivable
       ([AppEcho.echo_sup_of_taint] / [echo_taint_of_sup]) -- so a shell
       slot built at [gen] would be a vacuous arm.  This file may not bind
       [uprogSG] as a section variable (see the header: [uprogSG_gen] is
       the one instance resolution may find, and a second makes every
       [udep] in the tree ambiguous), and the GENERIC slot's lemmas below
       stay at [gen] by design.  So the free instance is written on EVERY
       position that carries a deposit -- the premises, the conclusion,
       and the [sh_slot_of_kexec] application in the proof -- and nowhere
       else.  At that instance [psok] IS [free_num], so this premise is
       the identity. *)
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    (* WHAT INIT'S OWN OPEN INSTALLED ON SLOT 0.  sh's entry is told one
       row about its table -- fd 0 is the console, slot 0 is closed, or the
       taint ([UkSh.ush_fd0]) -- and those are exactly the three arms of
       init's head ([UInitFd.ufd_head]), which the exec supply now carries
       ([UkInit.init_exec_sup_pos]) and reads against the lent authority
       ([UInitFd.ufd_head_row]).  The only thing left for the caller to say
       is that the head's OWN state is the console one, which is what the
       pinned open's receipt gives it.
       AT BOTH BITS (lane IO-LEAF, M4a(3)): /init's open is [O_RDWR], and
       the WRITABLE one is what sh's prompt asks of fd 2
       ([UShOut.ksh_w_of_link_prompt]).  It was [exists wr, ...] while only
       fd 0's READABLE bit was read off it. *)
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    cons_cred_holds cn T Cr ->
    udep (PS := uprogSG_free) -∗
    (* ...AND THE THREE DEPOSITS SH OWES: read(5), open(15), write(16), the
       CLAIM numbers sh calls ([UkSh.sh_deps]).  They cross the exec with
       the slot, because the slot they build IS sh's. *)
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    (* ...AND THE PROMPT'S LAW AT EVERY LINE BOUNDARY (lane IO-LEAF,
       M6a(3)): persistent, so it crosses into every shell this [□] builds. *)
    UShKernel.sh_prompt_law (PS := uprogSG_free) (cc_wc Cr) -∗
    (* ...AND WHAT SH'S CONSOLE PREAMBLE IS TOLD (lane SH-OPEN, H3).  sh's
       open of "console" is PINNED, so which of the two pinned leaves it
       makes is decided here.  PERSISTENT, AND THAT IS FORCED: this
       constructor's body is under a [□] -- /init execs sh inside the
       restart loop's [iLob] -- so the only LINEAR resource that can cross
       into sh is the one /init hands per round ([UserConsole.upos], through
       [PinnedExec]'s single [Pay]).  An EXCLUSIVE absence credential
       ([AppEcho.cons_key]) therefore cannot reach sh at all; the
       credential is [AppEcho.cons_never] (the owner's ruling (A), E2's to
       mint) and [UShConsK] states the two leaves against it. *)
    (* AT THE FREE INSTANCE TOO, and this is where the seam actually bit:
       the leaves CARRY the deposit instance ([UkSh]'s leaf section binds
       [{SG}] and [{PS}] as section variables), so an unannotated premise
       here is at [uprogSG_gen] while the [sh_slot_of_kexec] application
       below wants [uprogSG_free] -- and the two records are NOT
       convertible ([Dsup := xv6_ssupply] vs [True], [psok := fun _ =>
       True] vs [xv6_free]), so [iApply] unfolds both into
       [UexecSG.sbundle]'s tower looking for a match that cannot exist.
       That FAILING unification is the wedge; naming the instance on both
       sides removes it. *)
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T K) ∗ K)
     ∨ T) -∗
    init_sh_slot T (sh_pay T Cr Rsh n0) -∗
    (* NO [(PS := uprogSG_free)] ANY MORE: the exec supply's conclusion is
       [UkRun.udepw_at_ref] (lane KILL-PAY, K4(a), ruling R-A), whose one
       disjunct is the bundle itself -- it names no [psok], so there is no
       [uprogSG] instance left to pin. *)
    (* ...AND WHAT IT LENDS BESIDE THE POSITION AND THE LEASE (lane
       IO-LEAF, step 3): the era's credential AT THE LEDGER the child
       inherits ([UkInit.init_lend_cred]) -- prompt-shaped on the
       both-console row, banner-owed on the closed one -- which sh's
       entry puts in its loop's own slot ([UkSh.ush_wcp]).  This is the
       ONE place the two ends meet. *)
    UkInit.init_exec_sup_lend cn T st Cr.
  Proof using .
    exact (init_exec_sup_of_sh_slot_at EchoDisc.disc_input UkSh.ush_disc_snoc_ncr
             EchoDisc.disc_input_rest_short UkSh.ush_line_echo
             UkSh.ush_disc_line_echo
             T cn st K Cr Rsh n0).
  Qed.

  (* =================================================================== *)
  (*  THE EXEC SUPPLY AS THE WALK TAKES IT (lane E2)                      *)
  (*                                                                      *)
  (*  /init's walk does not hold the console credential at its entry --   *)
  (*  which credential it is is decided by its own mknod, mid-walk -- so   *)
  (*  what the entry carries is [UkInit.init_cons_sup]: the supply as a    *)
  (*  WAND from the credential, beside the law that pays it under the      *)
  (*  taint.  Everything else the shell's slot needs is persistent and is  *)
  (*  fixed at the entry.                                                  *)
  (* =================================================================== *)
End UInitSh.
