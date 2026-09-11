(* ===================================================================== *)
(* UInitSh.v -- init's OWN exec deposit: the PINNED bundle for /sh, and    *)
(* the reading of init's image that prices sh's frames.                   *)
(*                                                                        *)
(* [UkInit.init_exec_sup] is what init's proof carries in place of         *)
(* [UkRun.uxsup] -- the exec deposit at init's OWN two argument registers  *)
(* (a0 = 0x9a8, the string "sh" in its rodata; a1 = 0x1000, the argument   *)
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
(* pointer 0x9a8, the word at 0x1008 is NULL, and the string at 0x9a8 is   *)
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
(* [uprogSG_gen]'s [fun _ => True] -- every [psok] premise vacuously true. *)
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
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required:
   naming [xv6G] / [fileG] / [irefslotG] / [pavG] without their defining
   module in scope introduces a FRESH Type variable instead of the class,
   and the kernel's [uexecSG] instance is then invisible to resolution.
   [PinnedExec.v]'s header is the note. *)
Require Import Xv6Cameras.      (* [bioslotG] *)
Require Import Xv6G.            (* [xv6G] *)
Require Import FdSlots.         (* [fdslotG], [fdstate] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG], and its [appcfg] / [icfg] fields *)
Require Import UserFd.
Require Import UserHeap.
Require Import ChildTok.  (* [my_pay]: the exec wands' pay fact *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun.
Require Import UCodeInit UkInit.
Require Import UkSh UShKernel.
Require Import PathElems.          (* [path_elems] *)
Require Import ElfUser.
Require Import ElfLoadable.        (* [sh_elf_loadable] *)
Require Import PageGeom.           (* [PGSIZE] *)
Require Import KexecDefs.
Require Import SpecKexec.
Require Import SpecCopyin.         (* [uimg_word_at] *)
Require Import SpecSysExec.        (* [exec_args_of] / [exec_path_of] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsImgCheck.         (* [fname_sh] *)
Require Import FsShPin.            (* [era0_sh_pins] / [sh_path] / [SH_INO] *)
Require Import FsAbsDefs.          (* [aview] / [arun] / [AFile] *)
Require Import PinnedExec.
Require Import UexecExecInst.      (* [sbundle_exec_intro] -- THE INSTANCE *)
Require Import TsoCtx.
Require User.InitData.
Import Defs.

Local Open Scope Z_scope.

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
        UCodeInit.init_argv_map !! (0x1000 + Z.of_nat k)
          = Some (nth_byte (mword_of_int 0x9a8 : mword 64) k)
        /\ UCodeInit.init_argv_map !! (0x1008 + Z.of_nat k)
          = Some (nth_byte (mword_of_int 0 : mword 64) k)))
    (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_argv_words (k : nat) :
  (k < 8)%nat ->
  UCodeInit.init_argv_map !! (0x1000 + Z.of_nat k)
    = Some (nth_byte (mword_of_int 0x9a8 : mword 64) k)
  /\ UCodeInit.init_argv_map !! (0x1008 + Z.of_nat k)
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
        !! uint (add_vec_int (mword_of_int 0x9a8 : mword 64) (Z.of_nat 0%nat))
      = init_sh_pl !! 0%nat
   /\ UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9a8 : mword 64) (Z.of_nat 1%nat))
      = init_sh_pl !! 1%nat
   /\ UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9a8 : mword 64) (Z.of_nat 2%nat))
      = Some (bv_0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bv0_moi0 : (bv_0 8 : bv 8) = (mword_of_int 0 : mword 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* an eight-byte window of the image, in the two spellings: the map's own
   [Some (nth_byte w k)] and the contract's [bv_to_little_endian] *)
Lemma img_word_of_bytes (M : gmap Z (bv 8)) (a z : Z) :
  (forall k : nat, (k < 8)%nat ->
     M !! (a + Z.of_nat k) = Some (nth_byte (mword_of_int z : mword 64) k)) ->
  forall k : nat, (k < 8)%nat ->
    M !! (a + Z.of_nat k) = bv_to_little_endian 8 8 z !! k.
Proof.
  intros H k Hk. rewrite (H k Hk). exact (eq_sym (bv_le_nth_byte z k Hk)).
Qed.

(* the two spellings of a word's bytes agree, so eight image bytes pin the
   word they encode *)
Lemma uimg_word_det (M : gmap Z (bv 8)) (a : Z) (w : mword 64) (z : Z) :
  0 <= z < 2 ^ 64 ->
  uimg_word_at M a w ->
  (forall k : nat, (k < 8)%nat ->
     M !! (a + Z.of_nat k) = bv_to_little_endian 8 8 z !! k) ->
  w = (mword_of_int z : mword 64).
Proof.
  intros Hz Hw Hz8.
  assert (Hlen : forall y : Z, length (bv_to_little_endian 8 8 y) = 8%nat)
    by (intro y; rewrite (length_bv_to_little_endian 8 8 y ltac:(lia));
        reflexivity).
  assert (Hl : bv_to_little_endian 8 8 (bv_unsigned w)
               = bv_to_little_endian 8 8 z).
  { apply list_eq. intro k.
    destruct (decide (k < 8)%nat) as [Hk | Hk].
    - rewrite <- (Hw k Hk). exact (Hz8 k Hk).
    - assert (Hnw : bv_to_little_endian 8 8 (bv_unsigned w) !! k = None)
        by (apply lookup_ge_None_2; rewrite Hlen; lia).
      assert (Hnz : bv_to_little_endian 8 8 z !! k = None)
        by (apply lookup_ge_None_2; rewrite Hlen; lia).
      rewrite Hnw Hnz. reflexivity. }
  assert (Hmod : bv_unsigned w `mod` 2 ^ 64 = z `mod` 2 ^ 64).
  { pose proof (little_endian_to_bv_to_little_endian 8 8 (bv_unsigned w)
                  ltac:(lia)) as H1.
    pose proof (little_endian_to_bv_to_little_endian 8 8 z ltac:(lia)) as H2.
    change (8 * Z.of_N 8) with 64 in H1.
    change (8 * Z.of_N 8) with 64 in H2.
    rewrite <- H1. rewrite <- H2. rewrite Hl. reflexivity. }
  pose proof (bv_unsigned_in_range _ w) as Hr.
  unfold bv_modulus in Hr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
  rewrite (Z.mod_small _ _ Hr) in Hmod.
  rewrite (Z.mod_small _ _ Hz) in Hmod.
  apply bv_eq. rewrite Hmod.
  exact (eq_sym (moi_small z ltac:(unfold Z64; lia))).
Qed.

(* ===================================================================== *)
(*  4.  INIT'S ARGUMENTS ARE DETERMINED BY ITS IMAGE                       *)
(*                                                                        *)
(*  Every reading of the argument vector at 0x1000 that [sys_exec] can     *)
(*  perform against an image containing init's .data and .rodata is the    *)
(*  same one: ONE argument, of length two.  That is what prices sh's       *)
(*  frames, and it is why the pinned route needs [exec_args_of] and not    *)
(*  merely [exec_args_shape].                                              *)
(* ===================================================================== *)
Lemma init_args_det (M : gmap Z (bv 8)) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) :
  uimg_sub UCodeInit.init_argv_map M ->
  uimg_sub UCodeInit.init_ro M ->
  exec_args_of M (mword_of_int 0x1000 : mword 64) na alen afun ->
  na = 1%nat /\ alen 0%nat = 2%nat.
Proof.
  intros Hav Hro (Hshape & avf & Hptr & Hnz & Hnul & Hstr).
  destruct Hshape as (_ & Hcstr & _).
  (* the two windows, in the contract's spelling *)
  assert (Hb0 : forall k : nat, (k < 8)%nat ->
            M !! (0x1000 + Z.of_nat k)
            = bv_to_little_endian 8 8 0x9a8 !! k).
  { apply img_word_of_bytes. intros k Hk.
    exact (Hav _ _ (proj1 (init_argv_words k Hk))). }
  assert (Hb1 : forall k : nat, (k < 8)%nat ->
            M !! (0x1008 + Z.of_nat k)
            = bv_to_little_endian 8 8 0 !! k).
  { apply img_word_of_bytes. intros k Hk.
    exact (Hav _ _ (proj2 (init_argv_words k Hk))). }
  (* ---- the two pointer words ---- *)
  assert (E0 : uint (add_vec_int (mword_of_int 0x1000 : mword 64)
                       (8 * Z.of_nat 0%nat)) = 0x1000)
    by (vm_compute; reflexivity).
  assert (E1 : uint (add_vec_int (mword_of_int 0x1000 : mword 64)
                       (8 * Z.of_nat 1%nat)) = 0x1008)
    by (vm_compute; reflexivity).
  assert (Hne : (mword_of_int 0x9a8 : mword 64) <> mword_of_int 0).
  { intro Hc. apply (f_equal bv_unsigned) in Hc.
    vm_compute in Hc. discriminate Hc. }
  assert (Hna1 : na = 1%nat).
  { destruct (decide (na = 0%nat)) as [-> | Hn0].
    - exfalso. pose proof (Hptr 0%nat (Nat.le_refl 0%nat)) as Hw.
      rewrite E0 in Hw.
      assert (Hz0 : 0 <= 0x9a8 < 2 ^ 64) by (clear; lia).
      rewrite (uimg_word_det M 0x1000 (avf 0%nat) 0x9a8 Hz0 Hw Hb0) in Hnul.
      exact (Hne Hnul).
    - destruct (decide (na = 1%nat)) as [-> | Hn1]; [ reflexivity | exfalso ].
      pose proof (Hptr 1%nat ltac:(lia)) as Hw. rewrite E1 in Hw.
      pose proof (Hnz 1%nat ltac:(lia)) as Hz.
      assert (Hz1 : 0 <= 0 < 2 ^ 64) by (clear; lia).
      exact (Hz (uimg_word_det M 0x1008 (avf 1%nat) 0 Hz1 Hw Hb1)). }
  subst na.
  (* ---- the string at 0x9a8 ---- *)
  split; [ reflexivity | ].
  pose proof (Hptr 0%nat ltac:(lia)) as Hw. rewrite E0 in Hw.
  assert (Hz0 : 0 <= 0x9a8 < 2 ^ 64) by (clear; lia).
  assert (Hp0 : avf 0%nat = (mword_of_int 0x9a8 : mword 64))
    by exact (uimg_word_det M 0x1000 (avf 0%nat) 0x9a8 Hz0 Hw Hb0).
  pose proof (Hstr 0%nat ltac:(lia)) as Hs. rewrite Hp0 in Hs.
  destruct (Hcstr 0%nat ltac:(lia)) as [Hno Hnl].
  pose proof (bool_decide_eq_true_1 _ init_ro_sh_bool) as (Hr0 & Hr1 & Hr2).
  destruct (decide (alen 0%nat = 2%nat)) as [Hok | Hbad]; [ exact Hok | ].
  exfalso.
  destruct (decide (alen 0%nat < 2)%nat) as [Hlt | Hge].
  - (* the string would end at 0x9a8 or 0x9a9, and neither byte is NUL *)
    pose proof (Hs (alen 0%nat) (Nat.le_refl _)) as Hj.
    destruct (decide (alen 0%nat = 0%nat)) as [Hz | Hz].
    + rewrite Hz in Hj. rewrite Hz in Hnl. rewrite (Hro _ _ Hr0) in Hj.
      injection Hj as Hj. rewrite <- Hj in Hnl.
      vm_compute in Hnl. discriminate Hnl.
    + assert (Ha : alen 0%nat = 1%nat) by lia.
      rewrite Ha in Hj. rewrite Ha in Hnl. rewrite (Hro _ _ Hr1) in Hj.
      injection Hj as Hj. rewrite <- Hj in Hnl.
      vm_compute in Hnl. discriminate Hnl.
  - (* ...and past 0x9aa the string would have to continue through a NUL *)
    pose proof (Hs 2%nat ltac:(lia)) as Hj.
    rewrite (Hro _ _ Hr2) in Hj. injection Hj as Hj.
    exact (Hno 2%nat ltac:(lia) (eq_trans (eq_sym Hj) bv0_moi0)).
Qed.

(* ===================================================================== *)
(*  5.  THE INGREDIENTS                                                    *)
(* ===================================================================== *)
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
  Definition sh_pay (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat)
    : iProp Σ :=
    (□ (∀ (W' : uvis) (γt γd γs : gname),
          usz γs (uvis_sz W') -∗
          ([∗ map] k ↦ b ∈ base.filter
                (fun kv : Z * bv 8 =>
                   kv.1 < uint (tf_resume_gpr0 (uvis_tf W')
                                !!! Regidx csp_rs1)
                          - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
                (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
             ubyte γd k b) -∗
          ∃ f : nat -> bv 8, Rsh γt γd γs ∗ ubytes γd sh_buf sh_nbuf f)
     ∗ (∀ N : uk_names Σ,
          ush_rest N (Rsh (ukn_t N) (ukn_d N) (ukn_s N))))%I.

  Global Instance sh_pay_persistent Rsh n0 : Persistent (sh_pay Rsh n0).
  Proof. rewrite /sh_pay. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* INIT'S PINNED EXEC SLOT, as one persistent premise.                   *)
  (*                                                                       *)
  (* [T] is the application's TAINT -- the disjunct its claim law admits    *)
  (* when the pins may have been broken -- and it is Persistent AND        *)
  (* Timeless because the claim sits under [AppInv.app_body]'s later and   *)
  (* each fire strips it ([PinnedExec]'s header).                          *)
  (* ------------------------------------------------------------------- *)
  (* THE TAINT ARM IS INDEXED BY THE PAY FACT, at the TRIVIAL payload: a
     tainted process runs on the generic family, which is itself indexed by
     it ([UexecExecMint.uslot_mint]), and the payload of the process init
     execs sh into is the one init chose at the fork that made it -- trivial
     at this lane (L7 is what makes it the console-input resource). *)
  Definition init_sh_slot (T : iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v ∗ (⌜FsShPin.era0_sh_pins v⌝ ∨ T))
     ∗ □ (∀ W : uvis, T -∗ my_pay (uvis_gen W) (fun _ => True)%I -∗ uslot W)
     ∗ Pay)%I.

  Global Instance init_sh_slot_persistent T Pay `{!Persistent Pay} :
    Persistent (init_sh_slot T Pay).
  Proof. rewrite /init_sh_slot. apply _. Qed.

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
  Proof.
    intro Ha. unfold kxc_sp_final. cbn [kxc_sp]. rewrite Ha.
    vm_compute. reflexivity.
  Qed.

  Lemma init_sh_room (alen : nat -> nat) (n0 : nat) :
    alen 0%nat = 2%nat ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    kexec_sz ElfUser.sh_elf - PGSIZE
      + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= kxc_sp_final (kexec_sz ElfUser.sh_elf) alen 1%nat.
  Proof.
    intros Ha Hn0. rewrite sh_kexec_sz. rewrite (init_sh_sp_final alen Ha).
    unfold PGSIZE. lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE PATH, read out of init's read-only image.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma init_sh_path_of (M : gmap Z (bv 8)) :
    uimg_sub UCodeInit.init_ro M ->
    exec_path_of M (mword_of_int 0x9a8 : mword 64) init_sh_pl.
  Proof.
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

  (* ------------------------------------------------------------------- *)
  (* THE ASSEMBLY: init's pinned bundle pays its exec supply.              *)
  (* ------------------------------------------------------------------- *)
  Lemma init_exec_sup_of_sh_slot (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    (forall k : Z, k <> USYS_exec -> psok k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    udep -∗
    init_sh_slot T (sh_pay Rsh n0) -∗
    UkInit.init_exec_sup.
  Proof.
    intros Hpsok Hn0.
    iIntros "#Hdep (#Hinv & #Hcl & #Hgen & #Hpay)".
    (* THE LEDGER IS TAKEN AND NOT READ: sh's entry says nothing about its
       standard streams, and the only descriptor fact this constructor
       needs is [length fdv = NOFILE], which comes off the LENT authority
       ([UserFd.ufd_auth_len]) rather than off the ledger. *)
    iModIntro. iIntros (N m pc) "%Hpeq %Ha0 %Ha1 #Hro #Hargv _".
    rewrite /udepw_at. iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    (* ---- the two image readings, off the lent heap ---- *)
    iAssert (⌜uimg_sub UCodeInit.init_ro M⌝)%I as %Hsro.
    { iIntros (a b Hb).
      rewrite /init_rodata /utext_img.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hro") as "Hb".
      iDestruct (uheap_text with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    iAssert (⌜uimg_sub UCodeInit.init_argv_map M⌝)%I as %Hsav.
    { iIntros (a b Hb).
      rewrite /init_argv.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hargv") as "Hb".
      iDestruct (uheap_ubyte with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    (* ---- the descriptor list, off the lent authority ---- *)
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iFrame "Hheap Hufd". iRight.
    (* ---- sh's constructor, at every key the image fact admits ---- *)
    iAssert (□ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
                  (W' : uvis),
                  ⌜kexec_image_ok ElfUser.sh_elf na alen afun fdv W'⌝ -∗
                  ⌜exec_args_of M (mword_of_int 0x1000 : mword 64)
                     na alen afun⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  sh_pay Rsh n0 -∗ uslot W'))%I as "#Hcon".
    { iModIntro. iIntros (na alen afun W') "%Hok %Hargs #Hmp [#Hp1 #Hp2]".
      destruct (init_args_det M na alen afun Hsav Hsro Hargs) as [-> Halen].
      iApply (sh_slot_of_kexec Hpsok Rsh 1%nat alen afun fdv W' n0 Hok
                (init_sh_room alen n0 Halen Hn0) Hlen with "[] Hdep Hp2 Hmp").
      iModIntro. iIntros (γt γd γs) "Hsz Hlo".
      iApply ("Hp1" $! W' γt γd γs with "Hsz Hlo"). }
    (* ---- the bundle ---- *)
    iDestruct (pinned_exec_bundle fsc_fs uslot FsShPin.era0_sh_pins T
                 FsImg.ROOTINO init_sh_pl [FsImg.ROOTINO; FsShPin.SH_INO]
                 FsShPin.SH_INO ElfUser.sh_elf 1%nat (sh_pay Rsh n0)
                 (fun _ => True)%I
                 M (mword_of_int 0x9a8) (mword_of_int 0x1000) fdv
                 init_sh_pin_resolves sh_elf_loadable
                 (init_sh_path_of M Hsro)
                 with "Hcl Hinv Hcon Hgen Hpay") as (P Pmiss Fo R) "Hb".
    assert (Ea0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv))
                    (tf_arg_idx 0) = (mword_of_int 0x9a8 : mword 64))
      by (etransitivity; [ exact (tf_of_arg0 m pc) | exact Ha0 ]).
    assert (Ea1 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv))
                    (tf_arg_idx 1) = (mword_of_int 0x1000 : mword 64))
      by (etransitivity; [ exact (tf_of_arg1 m pc) | exact Ha1 ]).
    iApply (sbundle_exec_intro uslot
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv) P Pmiss Fo R).
    { (* init's own payload is the trivial one -- userinit's choice, which
         the entry constructor wrote into the record *)
      cbn [uvis_gen uvis_of_run]. rewrite -Hpeq. iExact "Hmpay". }
    rewrite Ea0 Ea1. iExact "Hb".
  Qed.

End UInitSh.
