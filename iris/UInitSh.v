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
Require Import UInitFd.  (* [ufd_head] / [ufd_head_row] -- init's own
                            descriptor head, and the row sh's entry reads
                            off it against the lent authority *)
Require Import UkRun.
Require Import UCodeInit UkInit.
Require Import UkSh UShKernel.
Require Import PathElems.          (* [path_elems] *)
Require Import ElfUser.
Require Import ElfLoadable.        (* [sh_elf_loadable] *)
Require Import AppEcho.            (* [echo_fs_pure] -- the WHOLE pins law
                                      sh is handed (lane E4: its own exec of
                                      /echo needs [FsEchoPin.era0_echo_pins],
                                      which is one of its conjuncts) *)
Require Import FsConsPin.          (* [cons_absent] / [cons_present_at] *)
Require Import UInitCons.          (* [init_cons_cred] -- the console
                                      credential /init hands the shell *)
Require Import UShConsK.           (* sh's two console leaf discharges at
                                      echo's era (lane SH-OPEN) *)
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
Require Import Xv6Cameras.         (* [uartGhostG] *)
Require Import UartNames.          (* [cons_names] *)
Require Import UserConsole.        (* [ucons_pay] / [upos] *)
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
  (* the console ring's cameras: the POSITION init lends sh across the exec
     is stated over them ([UserConsole.upos]) *)
  Context `{!uartGhostG Σ}.

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
  Definition sh_pay (T : iProp Σ) (Rsh : gname -> gname -> gname -> iProp Σ)
      (n0 : nat) : iProp Σ :=
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
     (* ...AND THE TAIL AT EVERY POSITION GHOST: init mints a FRESH pair
        per child ([UserConsole.upos_alloc]), so what the application owes
        is sh's body at whichever name this round's pair got. *)
     ∗ (∀ (γp : gname) (N : uk_names Σ),
          ush_rest N γp (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))
     (* ...AND THE TAG'S READING (lane SH-LINE 2b, L4).  How a tagged input
        history is READ -- as the discipline or as the taint -- is a fact
        about the TOP theorem's [boot_fixedGS] equation [riscv_rx_tag =
        app_tag] and nothing below it, so it reaches sh as a premise, and
        this is the slot it rides in ([UConsLine.ush_exec_pay] is the
        shape).  E2 discharges it from that equation, beside init's claim
        law.  LAST, so every existing destructuring of this payload keeps
        working (durable-notes, "Shaping a change so the sweep is small"). *)
     ∗ UkSh.ush_tag_law T)%I.

  Global Instance sh_pay_persistent T Rsh n0 : Persistent (sh_pay T Rsh n0).
  Proof. rewrite /sh_pay. apply _. Qed.

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
     are conjuncts of [AppEcho.echo_fs_pure], so what crosses is the one
     law and each consumer projects ([sh_pins_of_fs_pure] below is /sh's
     projection; E4's is /echo's). *)
  Definition init_sh_slot_core (T : iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗ R -∗ uslot W)
     ∗ Pay)%I.

  (* THE CONSOLE CREDENTIAL IS NOT HERE but a premise of the constructor
     ([init_exec_sup_of_sh_slot]'s third, lane SH-OPEN): which of sh's two
     pinned leaves it can make is decided by /INIT'S OWN mknod, mid-walk,
     and this record is fixed at /init's entry. *)
  Definition init_sh_slot (T : iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    init_sh_slot_core T Pay.

  Global Instance init_sh_slot_core_persistent T Pay `{!Persistent Pay} :
    Persistent (init_sh_slot_core T Pay).
  Proof. rewrite /init_sh_slot_core. apply _. Qed.

  Global Instance init_sh_slot_persistent T Pay `{!Persistent Pay} :
    Persistent (init_sh_slot T Pay).
  Proof. rewrite /init_sh_slot /init_sh_slot_core. apply _. Qed.

  (* the projection /sh's own pinned exec wants *)
  Lemma sh_pins_of_fs_pure (T : iProp Σ) :
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T)) -∗
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜FsShPin.era0_sh_pins v⌝ ∨ T)).
  Proof.
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
  Proof.
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
      (cn : cons_names) (st : fdstate) (K : iProp Σ) `{!Persistent K}
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    (* the numbers sh admits -- THE FREE ONES (lane SUPPLY-SPLIT) *)
    (forall k : Z, free_num k -> psok k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    (* WHAT INIT'S OWN OPEN INSTALLED ON SLOT 0.  sh's entry is told one
       row about its table -- fd 0 is the console, slot 0 is closed, or the
       taint ([UkSh.ush_fd0]) -- and those are exactly the three arms of
       init's head ([UInitFd.ufd_head]), which the exec supply now carries
       ([UkInit.init_exec_sup_pos]) and reads against the lent authority
       ([UInitFd.ufd_head_row]).  The only thing left for the caller to say
       is that the head's OWN state is the console one, which is what the
       pinned open's receipt gives it. *)
    (exists wr : bool, st = FdOpen true wr (FdDevice ConsoleInv.CONSOLE)) ->
    udep -∗
    (* ...AND THE THREE DEPOSITS SH OWES: read(5), open(15), write(16), the
       CLAIM numbers sh calls ([UkSh.sh_deps]).  They cross the exec with
       the slot, because the slot they build IS sh's. *)
    UkSh.sh_deps -∗
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
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N T)
     ∨ (□ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N T K) ∗ K)
     ∨ T) -∗
    init_sh_slot T (sh_pay T Rsh n0) -∗
    UkInit.init_exec_sup_lend cn T st.
  Proof.
    intros Hpsok_free Hn0 Hst.
    iIntros "#Hdep #Hdp #Hcons (#Hinv & #Hcl0 & #Hgen & #Hpay)".
    (* E4: what crosses is the WHOLE pins law and each consumer projects *)
    iDestruct (sh_pins_of_fs_pure T with "Hcl0") as "#Hcl".
    (* THE LEDGER IS TAKEN AND NOT READ: sh's entry says nothing about its
       standard streams, and the only descriptor fact this constructor
       needs is [length fdv = NOFILE], which comes off the LENT authority
       ([UserFd.ufd_auth_len]) rather than off the ledger. *)
    iModIntro. iIntros (γp np N m pc) "%Hpeq %Ha0 %Ha1 #Hro #Hargv Hhd Hpos".
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
    (* ...AND THE ROW SH'S ENTRY IS TOLD, read off INIT'S OWN HEAD against
       that same authority ([UInitFd.ufd_head_row]).  The head is spent
       here: the process that execs is replaced, and the new image gets its
       ledger from its own run. *)
    iDestruct (ufd_head_row T st (ukn_fd N) fdv with "Hufd Hhd")
      as "[Hufd #Hrow]".
    iAssert (UkSh.ush_fd0 T (take NSTD fdv)) as "#Hfd0".
    { iDestruct "Hrow" as "[%Hr1 | [%Hr2 | HT]]".
      - destruct Hst as [wr ->]. iLeft. iPureIntro. left. exists wr. exact Hr1.
      - iLeft. iPureIntro. right. exact Hr2.
      - iRight. iExact "HT". }
    iFrame "Hheap Hufd". iRight.
    (* ---- sh's constructor, at every key the image fact admits ---- *)
    (* THE PAYLOAD RIDES WITH THE PAY FACT ([SpecKexec.exec_slot_pre]): the
       kernel holds the exec'ing process's own payment across this call and
       hands it to whatever slot answers, so sh's entry gets its exit
       payload -- the console reader token -- from here and from nowhere
       else (EXEC-PAY, GENERIC-PAY). *)
    (* ...and the taint arm at the SAME payload: a tainted process runs on
       the generic family, which exists at any constant payload and HOLDS
       the resource it names ([UexecExecMint.uslot_mint_pay]).  The payload
       is literally the constant function at what the kill status names
       ([UserConsole.ucons_pay_eta]). *)
    iAssert (□ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') (ucons_pay cn γp T) -∗
                  ucons_pay cn γp T (-1) -∗ uslot W'))%I as "#Hgen'".
    { iModIntro. iIntros (W') "#HT #Hmp HQ".
      iApply ("Hgen" $! (ucons_pay cn γp T (-1)) W' with "HT [Hmp] HQ").
      rewrite ucons_pay_eta. iExact "Hmp". }
    (* THE LINEAR HALF OF [Pay] IS THE POSITION: [UInitSh.sh_pay] is
       persistent, so what actually crosses [PinnedExec]'s one linear slot
       is [UserConsole.upos] at the pair init minted for this round.  The
       exit payload is NOT there -- it arrives at the constructor wand from
       the kernel's own payment. *)
    iAssert (□ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
                  (W' : uvis),
                  ⌜kexec_image_ok ElfUser.sh_elf na alen afun fdv W'⌝ -∗
                  (* THE TWO ROWS [SpecKexec.exec_slot_pre] carries, in
                     [PinnedExec.pex_slot]'s own order (beside
                     [kexec_image_ok], before the pay fact).  THE CWD ROW
                     is proved there from [SpecKexec.kexec_ok_exec_cwi]:
                     exec INHERITS the working directory, and /init's is
                     the root -- sh's console preamble needs it because a
                     pinned open is about a PATH ([UkRun.udepwf_at] fixes
                     the cwd).  THE LAZY ROW is [false] because exec's
                     image is EAGER (lane LAZY-FLAG's K4).  Both are read
                     off the wand here and restated nowhere. *)
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  ⌜exec_args_of M (mword_of_int 0x1000 : mword 64)
                     na alen afun⌝ -∗
                  my_pay (uvis_gen W') (ucons_pay cn γp T) -∗
                  ucons_pay cn γp T (-1) -∗
                  (sh_pay T Rsh n0 ∗ upos γp np) -∗ uslot W'))%I as "#Hcon".
    { iModIntro.
      iIntros (na alen afun W')
        "%Hok %Hcwd0 %Hlzf %Hargs #Hmp HQ [[#Hp1 [#Hp2 #Htag]] Hps]".
      destruct (init_args_det M na alen afun Hsav Hsro Hargs) as [-> Halen].
      iApply (sh_slot_of_kexec Hpsok_free Rsh γp T K (ucons_pay cn γp T)
                1%nat alen afun fdv W' n0 np
                (ucons_pay_const cn γp T) Hok Hcwd0
                (init_sh_room alen n0 Halen Hn0) Hlen Hlzf
                with "[] Hdep Hdp Htag [] [] Hcons Hgen' Hmp HQ Hps").
      - iModIntro. iIntros (γt γd γs) "Hsz Hlo".
        iApply ("Hp1" $! W' γt γd γs with "Hsz Hlo").
      - iIntros (N0). iApply ("Hp2" $! γp N0).
      - iExact "Hfd0". }
    iDestruct (pinned_exec_bundle fsc_fs uslot FsShPin.era0_sh_pins T
                 FsImg.ROOTINO init_sh_pl [FsImg.ROOTINO; FsShPin.SH_INO]
                 FsShPin.SH_INO ElfUser.sh_elf 1%nat
                 (sh_pay T Rsh n0 ∗ upos γp np)%I
                 (ucons_pay cn γp T)
                 M (mword_of_int 0x9a8) (mword_of_int 0x1000) fdv
                 init_sh_pin_resolves sh_elf_loadable
                 (init_sh_path_of M Hsro)
                 with "Hcl Hinv Hcon Hgen' [Hpos]") as (P Pmiss Fo R) "Hb".
    { iFrame "Hpay Hpos". }
    assert (Ea0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false))
                    (tf_arg_idx 0) = (mword_of_int 0x9a8 : mword 64))
      by (etransitivity; [ exact (tf_of_arg0 m pc) | exact Ha0 ]).
    assert (Ea1 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false))
                    (tf_arg_idx 1) = (mword_of_int 0x1000 : mword 64))
      by (etransitivity; [ exact (tf_of_arg1 m pc) | exact Ha1 ]).
    (* THE DEPOSIT IS WANTED AT THIS PROGRAM'S OWN PAYLOAD (app-echo.md,
       "SH-LINE RULING", R1, at exec): exec's bundle READS the payload --
       it is what the kernel hands the new image's slot -- so the bundle is
       introduced AT that payload rather than re-keyed afterwards.  init's
       own is the trivial one ([Hpeq], userinit's choice). *)
    iApply (sbundle_pay_exec_intro uslot
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              (ukn_pay N) P Pmiss Fo R).
    { cbn [uvis_gen uvis_of_run]. iExact "Hmpay". }
    rewrite Hpeq Ea0 Ea1. iExact "Hb".
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
  (* ...AND THE SEAM SH-OPEN CONSUMES.  [UShConsK] states sh's two console
     leaves against an abstract credential; these are its two discharges,
     chosen by the credential /init's own mknod left.  At the SEAL the
     credential is [AppEcho.cons_never] and sh's first open MISSES (its
     repair arm runs); at the FLAG it is [cons_made r i] and sh's first
     open is the pinned one; under the taint sh proves nothing. *)
  Lemma ush_cons_in_of_Cns (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    app_inv fsc_fs -∗ init_cons_cred (echo_taint γ) r -∗
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N (echo_taint γ))
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf N (echo_taint γ) (cons_never r))
        ∗ cons_never r)
     ∨ echo_taint γ).
  Proof.
    intros Heq. iIntros "#Hinv #Hc".
    rewrite /init_cons_cred.
    iDestruct "Hc" as "[#Hn | [[%i #Hm] | #HT]]".
    - iRight. iLeft. iSplitR; [ | iExact "Hn" ].
      iApply (sh_cons_absent_echo γ r (cons_never r)
                ltac:(apply _) ltac:(apply _) Heq with "[] Hinv").
      rewrite /sh_cons_never_law. rewrite Heq.
      cbn [app_pred app_run app_names].
      iApply (echo_cons_never_law γ r).
    - iLeft. iApply (sh_cons_console_echo γ r i Heq with "Hm Hinv").
    - iRight. iRight. iExact "HT".
  Qed.

  Lemma init_cons_sup_of_sh_slot (γ : echo_fixed) (r : echo_names)
      (cn : cons_names) (st : fdstate)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    (forall k : Z, free_num k -> psok k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    (exists wr : bool, st = FdOpen true wr (FdDevice ConsoleInv.CONSOLE)) ->
    udep -∗ UkSh.sh_deps -∗
    init_sh_slot (echo_taint γ) (sh_pay Rsh n0) -∗
    UkInit.init_cons_sup cn (echo_taint γ)
      (init_cons_cred (echo_taint γ) r) st.
  Proof.
    intros Heq Hpsok_free Hn0 Hst.
    iIntros "#Hdep #Hdp #Hcore". rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #Hcns".
      iDestruct "Hcore" as "#Hcore'".
      iApply (init_exec_sup_of_sh_slot (echo_taint γ) cn st (cons_never r)
                ltac:(apply _) Rsh n0 Hpsok_free Hn0 Hst
                with "Hdep Hdp [] Hcore'").
      iApply (ush_cons_in_of_Cns γ r Heq with "[] Hcns").
      iDestruct "Hcore'" as "(#Hinv & _)". iExact "Hinv".
    - iIntros "!> #HT".
      iApply (init_cons_cred_of_taint (echo_taint γ) r with "HT").
  Qed.

End UInitSh.
