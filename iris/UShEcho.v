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
(*  ([UCodeInit.init_ro] at 0x9b8) and its argv a literal in its data, so  *)
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
Require Import UserFd.
Require Import ChildTok.
Require Import ElfFile ElfUser ElfLoadable.
Require Import PathElems.
Require Import FsCfg.             (* [fsc_fs] -- the era's file-system names *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeArith UmodeAbi.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import PinnedExec.
Require Import ExecEntry.        (* [image_entry]: obligation (E), named
                                    (design/user-exec.md section 1) *)
Require Import ExecArgs.         (* [uargv_exec] / [uargv_img] / [uargv_det]
                                    and the two heap readings: the argument
                                    vector at ANY layout (lane EX-3) *)
Require Import FsEchoPin.
Require Import ArgPath.           (* [arg_path_shape] / [arg_path_of] *)
Require Import SpecKexec SpecSysExec SpecCopyin.
Require Import UImgWordDefs.  (* [img_word_of_bytes] / [uimg_word_det] *)
Require Import EchoFsPure.    (* [echo_fs_pure] -- reached through [UInitSh] before *)
Require Import UShKernel.         (* the entry geometry: [sh_page_perm],
                                     [udata_lo_is_Some], [kxc_sp_final_mod8],
                                     [csp_rs1_eq], [elf_segments_loads] *)
Require Import KexecBuilt.        (* [kxc_sp_mono] / [kxc_sp_gap] /
                                     [kxc_sp_final_gap] / [kexec_pg] *)
Require Import UserPtTree.        (* [pgroundup] *)
Require Import WpUmodeLoad.       (* [uM_word] / [uM_word_bytes] *)
Require Import KexecDefs.
Require Import UkAbi.
Require Import UCodeEcho.
Require Import UEchoKernel.
Require Import LineWords.       (* [wl_line]: the admissible line *)
Require Import UkShRun UkShEcho.
Require Import EchoDisc.
Require Import ExecWords.        (* [exec_ok]: [line_ok] without the command *)
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

(* a failing tactic in a whole-function WP looks like a hang: Rocq prints
   the entire goal, and a [urun]-altitude goal is enormous (durable-notes,
   "The dev loop"). *)
Set Printing Depth 40.

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

(* ...and the bytes are the COMMAND NAME, which is what ties the pin to
   what sh actually passes: word 0 of every admissible line is "echo"
   ([EchoDisc.line_ok_head]). *)
Lemma echo_pl_line (j : nat) :
  (j < 4)%nat -> echo_pl !!! j = cmd_echo !!! j.
Proof.
  intro Hj.
  do 4 (destruct j as [| j]; [ vm_compute; reflexivity | ]). lia.
Qed.

(* ...and no byte of an admissible line is a NUL, which is what pins each
   argument's LENGTH: a [bb_cstr] that stopped early would have to find
   one. *)
Lemma line_nonul_x (ws : list (list (bv 8))) (j : nat) :
  exec_ok ws -> (j < length (wl_line ws))%nat -> wl_line ws !!! j <> ubyte0.
Proof. intro Hok. exact (UkSh.ush_line_no_nul ws j (exec_ok_wf ws Hok)). Qed.

Lemma line_nonul (ws : list (list (bv 8))) (j : nat) :
  line_ok ws -> (j < length (wl_line ws))%nat -> wl_line ws !!! j <> ubyte0.
Proof.
  intro Hok__.
  exact (line_nonul_x ws j (line_ok_exec_ok _ Hok__)).
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
(*  echo's PT_LOADs are (0, 0xddc, R-X) and (0x1000, 0x20, RW-), so the   *)
(*  loaded top is [pgroundup 0x1020 = 0x2000] and the new [p->sz] is that *)
(*  plus the guard and the stack page.  Everything the room condition     *)
(*  needs is closed arithmetic over these two.                            *)
(* ===================================================================== *)
Lemma echo_kexec_top : kexec_top ElfUser.echo_elf = 0x2000.
Proof. unfold kexec_top. rewrite ElfUser.echo_elf_end. reflexivity. Qed.

Lemma echo_kexec_sz : kexec_sz ElfUser.echo_elf = 0x4000.
Proof. unfold kexec_sz. rewrite echo_kexec_top. reflexivity. Qed.

(* THE ROOM echo's entry needs: twelve words below the entry sp.  This
   used to be the ADDRESS -- [kxc_sp_final 0x4000 alen 3 = 0x3FB0] at
   lengths 4, 5 and 5 -- and an address is a fact about one argument
   vector.  What the entry actually needs is an INEQUALITY, and what buys
   it is a bound on how much stack the arguments took: their own bytes,
   their NULs, the vector's words and at most fifteen of alignment each
   ([KexecDefs.kxc_sp_final_ge]).

   THAT BOUND IS A SIDE CONDITION ON THE LINE, and the right one: a line
   long enough to crowd echo's frame off its own stack page is a line the
   claim must not be about.  [UInitSh.init_sh_room] is the same shape for
   sh's frames at init's one argument. *)
Definition echo_argv_fits (ws : list (list (bv 8))) (alen : nat -> nat)
  : Prop :=
  kxc_span alen (length ws)
    + (8 * (Z.of_nat (length ws) + 1) + 16)
  <= PGSIZE - 96.

Lemma echo_room (ws : list (list (bv 8))) (alen : nat -> nat) :
  echo_argv_fits ws alen ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen (length ws).
Proof.
  rewrite /echo_argv_fits. intro Hfit. rewrite echo_kexec_sz.
  pose proof (kxc_sp_final_ge 0x4000 alen (length ws)).
  unfold PGSIZE in *. lia.
Qed.

(* ...AND EVERY ADMISSIBLE LINE EARNS THE ROOM.  One argument costs its
   bytes, its NUL and at most fifteen bytes of alignment
   ([KexecDefs.kxc_span] adds [len i + 16] per word), a word of an
   admissible line is shorter than [EchoDisc.line_max] = 100 bytes, and
   [line_ok] allows fewer than ten words -- so the whole push is under
   1200 bytes of a 4096-byte stack page.  A line long enough to crowd
   echo's frame off that page is a line the claim must not be about, and
   [line_ok] is where it is excluded. *)
Lemma kxc_span_le_line (len : nat -> nat) (n : nat) :
  (forall i : nat, (i < n)%nat -> (len i < line_max)%nat) ->
  kxc_span len n <= 115 * Z.of_nat n.       (* 115 = (line_max - 1) + 16 *)
Proof.
  unfold line_max.
  induction n as [| n IH]; cbn [kxc_span]; intro Hb; [ lia | ].
  assert (Hb' : forall i : nat, (i < n)%nat -> (len i < 100)%nat)
    by (intros i Hi; apply Hb; lia).
  pose proof (IH Hb') as Hprev. pose proof (Hb n ltac:(lia)) as Hn. lia.
Qed.

Lemma echo_argv_fits_of_ok_x (ws : list (list (bv 8))) :
  exec_ok ws -> echo_argv_fits ws (UkShEcho.echo_alen ws).
Proof.
  intro Hok. rewrite /echo_argv_fits.
  assert (Hb : forall i : nat, (i < length ws)%nat ->
            (UkShEcho.echo_alen ws i < line_max)%nat).
  { intros i Hi.
    pose proof (UkShEcho.echo_off_lt_x ws i (UkShEcho.echo_alen ws i)
                  Hok Hi ltac:(lia)) as Hlt.
    pose proof (exec_ok_len ws Hok) as Hlm. lia. }
  pose proof (kxc_span_le_line (UkShEcho.echo_alen ws) (length ws) Hb) as Hsp.
  pose proof (exec_ok_lt10 ws Hok) as H10.
  unfold PGSIZE. lia.
Qed.

Lemma echo_argv_fits_of_ok (ws : list (list (bv 8))) :
  line_ok ws -> echo_argv_fits ws (UkShEcho.echo_alen ws).
Proof.
  intro Hok__.
  exact (echo_argv_fits_of_ok_x ws (line_ok_exec_ok _ Hok__)).
Qed.

(* ===================================================================== *)
(*  3b. THE TWO PT_LOADs, AND THE ENTRY                                   *)
(*                                                                        *)
(*  [UShKernel.sh_loads] at echo: (0x0, 0xddc, R-X) and (0x1000, 0x20,    *)
(*  RW-).  Only the FIRST is read below -- echo's entry asks for page 0   *)
(*  to be X-and-not-W and for nothing else about the loaded image.        *)
(* ===================================================================== *)
Lemma echo_loads :
  exists p0 p1 : elf_phdr,
    elf_loads ElfUser.echo_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0xddc /\ ep_flags p0 = 5
    /\ ep_vaddr p1 = 0x1000 /\ ep_memsz p1 = 0x20 /\ ep_flags p1 = 6.
Proof.
  pose proof (UShKernel.elf_segments_loads ElfUser.echo_elf _
                ElfUser.echo_elf_segments) as H.
  revert H. generalize (elf_loads ElfUser.echo_elf) as l. intros l H.
  destruct l as [| p0 [| p1 [| p2 l]]]; cbn [fmap list_fmap] in H;
    try discriminate H.
  injection H as Hv0 Hfs0 Hms0 Hfl0 Hv1 Hfs1 Hms1 Hfl1.
  exists p0, p1. split_and!; [ reflexivity | assumption.. ].
Qed.

(* the entry, as the resume pc reads it: [EchoData.echoEntry] is 0x7c and
   2-aligned, so [ret_pc] is the identity on it, and it IS
   [EchoSyms.start] ([UShKernel.sh_start_pc] is the mould). *)
Lemma echo_start_pc :
  ret_pc (mword_of_int EchoData.echoEntry : mword 64)
  = mword_of_int EchoSyms.start.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  3c. THE CANONICAL STRING LENGTH, OUT OF A TERMINATOR ALONE             *)
(*                                                                        *)
(*  [UkAbi.uk_args_c] is stated at [uk_slens] -- a SCAN -- and             *)
(*  [uk_slen_ucstr] runs it only where a [ucstr] is already in hand.  What *)
(*  [SpecKexec.kexec_args_at] gives is weaker: a NUL at [alen i] and bytes *)
(*  below it, with NOTHING said about whether those bytes are themselves   *)
(*  NUL (exec copies whatever the caller's pointer names).  So the         *)
(*  canonical length has to be produced from the TERMINATOR alone, and     *)
(*  that is this induction.  It is what makes [uk_args_c] provable of the  *)
(*  image exec builds for ARBITRARY arguments, which is what echo's        *)
(*  bridge is quantified over.                                            *)
(* ===================================================================== *)
Lemma uscan_nul (M : gmap Z (bv 8)) (n : nat) :
  forall (fu : nat) (a : Z),
    (n < fu)%nat ->
    (forall j : nat, (j < n)%nat -> is_Some (M !! (a + Z.of_nat j))) ->
    M !! (a + Z.of_nat n) = Some ubyte0 ->
    (uscan M a fu <= n)%nat /\ ucstr M a (Z.of_nat (uscan M a fu)).
Proof.
  induction n as [| n IH ]; intros fu a Hlt Hex Hnul.
  - destruct fu as [| fu ]; [ exfalso; lia | ].
    rewrite Z.add_0_r in Hnul. cbn [uscan]. rewrite Hnul.
    rewrite (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl).
    split; [ lia | ].
    constructor; [ lia | intros j Hj; exfalso; lia | ].
    rewrite Z.add_0_r. exact Hnul.
  - destruct fu as [| fu ]; [ exfalso; lia | ].
    destruct (Hex 0%nat ltac:(lia)) as [b Hb].
    rewrite Z.add_0_r in Hb. cbn [uscan]. rewrite Hb.
    destruct (decide (b = ubyte0)) as [Hz | Hnz].
    + rewrite (bool_decide_eq_true_2 (b = ubyte0) Hz).
      split; [ lia | ].
      constructor; [ lia | intros j Hj; exfalso; lia | ].
      rewrite Z.add_0_r. rewrite Hb. rewrite Hz. reflexivity.
    + rewrite (bool_decide_eq_false_2 (b = ubyte0) Hnz).
      destruct (IH fu (a + 1)%Z ltac:(lia)
                  ltac:(intros j Hj;
                        destruct (Hex (S j) ltac:(lia)) as [c Hc];
                        exists c;
                        replace (a + 1 + Z.of_nat j)%Z
                          with (a + Z.of_nat (S j))%Z by lia;
                        exact Hc)
                  ltac:(replace (a + 1 + Z.of_nat n)%Z
                          with (a + Z.of_nat (S n))%Z by lia;
                        exact Hnul))
        as [Hle Hs].
      split; [ lia | ].
      constructor.
      * lia.
      * intros j Hj.
        destruct (decide (j = 0)) as [-> | Hj0].
        { rewrite Z.add_0_r. exists b. exact (conj Hb Hnz). }
        { destruct (ucs_body _ _ _ Hs (j - 1) ltac:(lia)) as (c & Hc & Hc0).
          exists c. replace (a + j)%Z with (a + 1 + (j - 1))%Z by lia.
          exact (conj Hc Hc0). }
      * pose proof (ucs_nul _ _ _ Hs) as Hn.
        replace (a + Z.of_nat (S (uscan M (a + 1) fu)))%Z
          with (a + 1 + Z.of_nat (uscan M (a + 1) fu))%Z by lia.
        exact Hn.
Qed.

(* ...at [uk_slen]'s own fuel, which the ABI's length bound clears *)
Lemma uk_slen_nul (M : gmap Z (bv 8)) (a : Z) (n : nat) :
  Z.of_nat n < 2 ^ 31 ->
  (forall j : nat, (j < n)%nat -> is_Some (M !! (a + Z.of_nat j))) ->
  M !! (a + Z.of_nat n) = Some ubyte0 ->
  uk_slen M a <= Z.of_nat n /\ ucstr M a (uk_slen M a).
Proof.
  intros Hn Hex Hnul.
  unfold uk_slen, uk_slen_fuel.
  destruct (uscan_nul M n (Z.to_nat (2 ^ 31)) a ltac:(lia) Hex Hnul)
    as [Hle Hs].
  split; [ lia | exact Hs ].
Qed.

(* a word's eight little-endian bytes are all there *)
Lemma bv_le8_is_Some (z : Z) (k : nat) :
  (k < 8)%nat -> exists b : bv 8, bv_to_little_endian 8 8 z !! k = Some b.
Proof.
  intro Hk.
  assert (Hlen : length (bv_to_little_endian 8 8 z) = 8%nat)
    by (rewrite (length_bv_to_little_endian 8 8 z ltac:(lia)); reflexivity).
  destruct (bv_to_little_endian 8 8 z !! k) as [b |] eqn:Ek.
  - exists b. reflexivity.
  - exfalso. apply lookup_ge_None_1 in Ek. rewrite Hlen in Ek. lia.
Qed.

Lemma kexec_vec_bytes (top : Z) (alen : nat -> nat) (na : nat)
    (M : gmap Z (bv 8)) :
  (forall i k, (i <= na)%nat -> (k < 8)%nat ->
     M !! (kxc_sp_final top alen na + 8 * Z.of_nat i + Z.of_nat k)
     = bv_to_little_endian 8 8 (kexec_ustack top alen na i) !! k) ->
  forall j : Z, 0 <= j < 8 * (Z.of_nat na + 1) ->
    exists b : bv 8, M !! (kxc_sp_final top alen na + j) = Some b.
Proof.
  intros Hvec j Hj.
  pose proof (Z.div_pos j 8 ltac:(lia) ltac:(lia)) as Hq0.
  pose proof (Z.mod_pos_bound j 8 ltac:(lia)) as Hr.
  assert (Hq : (Z.to_nat (j / 8) <= na)%nat).
  { assert (Hd : j / 8 < Z.of_nat na + 1)
      by (apply Z.div_lt_upper_bound; lia).
    lia. }
  destruct (bv_le8_is_Some (kexec_ustack top alen na (Z.to_nat (j / 8)))
              (Z.to_nat (j mod 8)) ltac:(lia)) as [b Hb].
  exists b.
  replace (kxc_sp_final top alen na + j)
    with (kxc_sp_final top alen na
          + 8 * Z.of_nat (Z.to_nat (j / 8))
          + Z.of_nat (Z.to_nat (j mod 8))) by lia.
  rewrite (Hvec (Z.to_nat (j / 8)) (Z.to_nat (j mod 8)) Hq ltac:(lia)).
  exact Hb.
Qed.

(* ...and eight image bytes PIN the pointer the ABI reads off that slot:
   [UkAbi.uk_argv_p] is [uM_word] read back as a [Z], and [UInitSh.
   uimg_word_det] is what says two spellings of a word's bytes agree. *)
Lemma uk_argv_p_of_bytes (M : gmap Z (bv 8)) (av i z : Z) :
  0 <= z < Z64 ->
  (forall k : nat, (k < 8)%nat ->
     M !! (av + 8 * i + Z.of_nat k) = bv_to_little_endian 8 8 z !! k) ->
  uk_argv_p M av i = z.
Proof.
  intros Hz Hb.
  assert (Hex : forall k : nat, (k < Z.to_nat 8)%nat ->
            exists b : bv 8, M !! (av + 8 * i + Z.of_nat k) = Some b).
  { intros k Hk. destruct (bv_le8_is_Some z k ltac:(lia)) as [b Hbk].
    exists b. rewrite (Hb k ltac:(lia)). exact Hbk. }
  pose proof (uM_word_bytes M (av + 8 * i) 8 ltac:(lia) Hex) as Hw.
  assert (Hww : (mword_of_int (bv_unsigned (uM_word M (av + 8 * i) 8))
                 : mword 64)
                = uM_word M (av + 8 * i) 8)
    by (rewrite <- uint_unsigned; apply moi_of_uint).
  assert (Hiw : uimg_word_at M (av + 8 * i) (uM_word M (av + 8 * i) 8)).
  { intros k Hk.
    rewrite (bv_le_nth_byte (bv_unsigned (uM_word M (av + 8 * i) 8)) k Hk).
    rewrite Hww. exact (Hw k ltac:(lia)). }
  pose proof (uimg_word_det M (av + 8 * i) (uM_word M (av + 8 * i) 8) z
                ltac:(unfold Z64 in Hz; lia) Hiw Hb) as He.
  unfold uk_argv_p, uk_argv_w. rewrite He.
  exact (uint_moi z Hz).
Qed.


(* ===================================================================== *)
(*  3d. THE ELEVEN ROWS ECHO'S ENTRY READS OFF THE KEY                    *)
(*                                                                        *)
(*  [UShKernel.sh_slot_of_kexec]'s derivation at echo, and PURE -- no      *)
(*  resource crosses this lemma, which is what keeps the Iris proof below  *)
(*  a three-liner (and its [Qed] inside the kernel's stack).  The two rows *)
(*  sh's own bridge never needed are the last but one and [uk_args_c]:     *)
(*  [SpecKexec.kexec_args_at] (the block exec BUILT) turned into           *)
(*  [UkAbi.uk_args_c] (the block echo READS).                             *)
(* ===================================================================== *)
(* ---- THE PUSH GEOMETRY, as twelve closed readings of the key.  Split
   off from the rows below for one reason: a single [Qed] over both
   overflows the kernel's stack. *)
Lemma echo_kexec_geom (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
  uvis_sz W' = 0x4000
  /\ 0x3060 <= kxc_sp_final 0x4000 alen na
  /\ kxc_sp_final 0x4000 alen na + 8 * (Z.of_nat na + 1) <= 0x4000
  /\ uint (uvis_sp W') = kxc_sp_final 0x4000 alen na
  /\ uvis_av W' = kxc_sp_final 0x4000 alen na
  /\ uvis_argc W' = Z.of_nat na
  /\ (forall i : nat, (i <= na)%nat ->
        uk_argv_p (uvis_M W') (kxc_sp_final 0x4000 alen na) (Z.of_nat i)
        = kexec_ustack 0x4000 alen na i)
  /\ (forall i : nat, (i < na)%nat ->
        kxc_sp_final 0x4000 alen na < kxc_sp 0x4000 alen (S i)
        /\ kxc_sp 0x4000 alen (S i) + Z.of_nat (alen i) < 0x4000)
  /\ (forall i : nat, (i < na)%nat -> forall j : nat, (j <= alen i)%nat ->
        exists b : bv 8,
          uvis_M W' !! (kxc_sp 0x4000 alen (S i) + Z.of_nat j) = Some b)
  /\ (forall i : nat, (i < na)%nat ->
        uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i)) <= Z.of_nat (alen i)
        /\ ucstr (uvis_M W') (kxc_sp 0x4000 alen (S i))
             (uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i))))
  /\ (forall j : Z, 0 <= j < 8 * (Z.of_nat na + 1) ->
        exists b : bv 8,
          uvis_M W' !! (kxc_sp_final 0x4000 alen na + j) = Some b)
  /\ (forall a : Z, 0x3000 <= a < kxc_sp_final 0x4000 alen na ->
        uvis_M W' !! a = Some (bv_0 8)).
Proof.
  intros Hok Hroom.
  (* the two readers of the key that need no geometry; the ENTRY is the
     page half's ([echo_kexec_pages]) and does not come back here. *)
  pose proof echo_kexec_sz as Hsz.
  rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hspw & Ha1w & Ha0w & Himg
                   & (Hstr & Hnul & Hvec) & (_ & Hzero) & _ & _ & _ & _).
  unfold PGSIZE in Hzero.
  (* ---- THE STACK PAGE'S GEOMETRY, in three numbers ---- *)
  (* [kxc_sp] at zero pushes IS the top; naming the equation keeps [cbn]
     away from the [S i] side, which it would unfold into the recurrence. *)
  assert (Hsp00 : kxc_sp 0x4000 alen 0%nat = 0x4000) by reflexivity.
  pose proof (kxc_sp_final_gap 0x4000 alen na) as Hgap.
  pose proof (kxc_sp_mono 0x4000 alen 0 na (Nat.le_0_l na)) as Hmono.
  rewrite Hsp00 in Hmono.
  assert (Hlo : 0x3060 <= kxc_sp_final 0x4000 alen na) by lia.
  assert (Hhi : kxc_sp_final 0x4000 alen na + 8 * (Z.of_nat na + 1)
                <= 0x4000) by lia.
  assert (Hna : 0 <= Z.of_nat na < 2 ^ 31) by lia.
  (* ---- the three registers echo's entry reads off the trapframe ---- *)
  assert (Hsp' : uint (uvis_sp W') = kxc_sp_final 0x4000 alen na).
  { unfold uvis_sp. rewrite UShKernel.csp_rs1_eq. unfold tf_resume_gpr0.
    rewrite tf_resume_gpr_sp. change tf_sp_idx with kxc_tf_sp_idx.
    rewrite Hspw. apply uint_moi. unfold Z64. lia. }
  assert (Hav : uvis_av W' = kxc_sp_final 0x4000 alen na).
  { unfold uvis_av. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a1.
    rewrite Ha1w. apply uint_moi. unfold Z64. lia. }
  assert (Hargc : uvis_argc W' = Z.of_nat na).
  { unfold uvis_argc. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a0.
    rewrite Ha0w. apply uint_moi. unfold Z64. lia. }
  (* ---- THE VECTOR: each slot's eight bytes pin its pointer ---- *)
  assert (Hptr : forall i : nat, (i <= na)%nat ->
            uk_argv_p (uvis_M W') (kxc_sp_final 0x4000 alen na) (Z.of_nat i)
            = kexec_ustack 0x4000 alen na i).
  { intros i Hi.
    apply uk_argv_p_of_bytes; [ | intros k Hk; exact (Hvec i k Hi Hk) ].
    unfold kexec_ustack.
    destruct (decide (i < na)%nat) as [Hlt | Hge]; [ | unfold Z64; lia ].
    pose proof (kxc_sp_mono 0x4000 alen 0 (S i) ltac:(lia)) as H1.
    rewrite Hsp00 in H1.
    pose proof (kxc_sp_mono 0x4000 alen (S i) na ltac:(lia)) as H2.
    unfold Z64. lia. }
  (* ---- THE STRINGS: where they sit, and that they end ---- *)
  assert (Hsi : forall i : nat, (i < na)%nat ->
            kxc_sp_final 0x4000 alen na < kxc_sp 0x4000 alen (S i)
            /\ kxc_sp 0x4000 alen (S i) + Z.of_nat (alen i) < 0x4000).
  { intros i Hi.
    pose proof (kxc_sp_gap 0x4000 alen i) as Hg.
    pose proof (kxc_sp_mono 0x4000 alen 0 i (Nat.le_0_l i)) as H0.
    rewrite Hsp00 in H0.
    pose proof (kxc_sp_mono 0x4000 alen (S i) na ltac:(lia)) as H2.
    lia. }
  assert (Hsb : forall i : nat, (i < na)%nat ->
            forall j : nat, (j <= alen i)%nat ->
              exists b : bv 8,
                uvis_M W' !! (kxc_sp 0x4000 alen (S i) + Z.of_nat j)
                = Some b).
  { intros i Hi j Hj.
    destruct (decide (j < alen i)%nat) as [Hlt | Hge].
    - exists (afun i j). exact (Hstr i j Hi Hlt).
    - assert (Hje : j = alen i) by lia. subst j.
      exists (bv_0 8). exact (Hnul i Hi). }
  assert (Hslen : forall i : nat, (i < na)%nat ->
            uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i))
              <= Z.of_nat (alen i)
            /\ ucstr (uvis_M W') (kxc_sp 0x4000 alen (S i))
                 (uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i)))).
  { intros i Hi. destruct (Hsi i Hi) as [Hlo1 Hhi1].
    apply uk_slen_nul.
    - lia.
    - intros j Hj. exists (afun i j). exact (Hstr i j Hi Hj).
    - rewrite ubyte0_bv0. exact (Hnul i Hi). }
  (* ---- every byte of the vector is in the image ---- *)
  assert (Hvb : forall j : Z, 0 <= j < 8 * (Z.of_nat na + 1) ->
            exists b : bv 8,
              uvis_M W' !! (kxc_sp_final 0x4000 alen na + j) = Some b).
  { exact (kexec_vec_bytes 0x4000 alen na (uvis_M W') Hvec). }
  assert (Hbelow : forall a : Z,
            0x3000 <= a < kxc_sp_final 0x4000 alen na ->
            uvis_M W' !! a = Some (bv_0 8)).
  { intros a Ha. apply Hzero; [ lia | ].
    intros [ (i & Hi & Hlo1 & _) | (Hlo1 & _) ]; [ | lia ].
    pose proof (kxc_sp_mono 0x4000 alen (S i) na ltac:(lia)) as Hm. lia. }
  exact (conj Hszv (conj Hlo (conj Hhi (conj Hsp' (conj Hav (conj Hargc
           (conj Hptr (conj Hsi (conj Hsb (conj Hslen
             (conj Hvb Hbelow))))))))))).
Qed.

(* ---- THE PAGE/TEXT HALF, split off so the kernel checks it on its own.
   Everything that touches the ELF -- the two PT_LOADs, the image
   inclusion, the entry -- is here and NOTHING else is
   (durable-notes: a [Qed] over both halves at once overflows the
   kernel's stack). *)
Lemma echo_kexec_pages (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  tf_resume_pc (uvis_tf W') = (mword_of_int EchoSyms.start : mword 64)
  /\ echo_text_sub (uvis_M W')
  /\ (forall a : Z, 0 <= a < 4096 ->
        ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 ->
        uk_rpage (uvis_perm W') (mword_of_int a : mword 64)).
Proof.
  intros Hok.
  (* ---- the three readers of the key that need no geometry ---- *)
  pose proof (kexec_image_ok_below _ _ _ _ _ _ Hok) as Hstop.
  pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok ElfUser.echo_elf_entry)
    as Hpcw.
  pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
  destruct echo_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & _ & _ & _).
  pose proof echo_kexec_sz as Hsz. pose proof echo_kexec_top as Htop.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hspw & Ha1w & Ha0w & Himg
                   & (Hstr & Hnul & Hvec) & (_ & Hzero) & Hperm & _ & _ & _).
  destruct Hperm as (Hpg & _ & Hstpg).
  rewrite Htop in Hstpg. change (0x2000 + PGSIZE) with 0x3000 in Hstpg.
  unfold PGSIZE in Hzero.
  (* ---- the stack page is RW, at every byte of it ---- *)
  assert (Hstkperm : forall a : Z, 0x3000 <= a < 0x4000 ->
            uperm_at (uvis_perm W') (mword_of_int a : mword 64)
            = Some uperm_rw).
  { intros a Ha.
    apply (UShKernel.sh_page_perm (uvis_perm W') 0x3000 a uperm_rw Hstpg);
      [ reflexivity | lia | lia | lia ]. }
  assert (Hwr : forall a : Z, 0x3000 <= a < 0x4000 ->
            uw_addr (uvis_perm W') a)
    by (intros a Ha; exists uperm_rw; exact (conj (Hstkperm a Ha) eq_refl)).
  assert (Hrp : forall a : Z, 0x3000 <= a < 0x4000 ->
            uk_rpage (uvis_perm W') (mword_of_int a : mword 64))
    by (intros a Ha; exists uperm_rw; exact (conj (Hstkperm a Ha) eq_refl)).
  (* ---- page 0 is echo's text: X and not W ---- *)
  assert (Hpg0 : uvis_perm W' !! kexec_pg 0 = Some (kexec_seg_perm p0)).
  { apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    rewrite kexec_sz_after_nil. rewrite Hv0 Hm0.
    split_and!; [ vm_compute; reflexivity
                | vm_compute; discriminate | vm_compute; reflexivity ]. }
  assert (Hperm0 : kexec_seg_perm p0 = MkUperm true false)
    by (unfold kexec_seg_perm; rewrite Hf0; reflexivity).
  assert (Hx : forall a : Z, 0 <= a < 4096 ->
            ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a).
  { intros a Ha.
    assert (Hat : uperm_at (uvis_perm W') (mword_of_int a : mword 64)
                  = Some (MkUperm true false)).
    { rewrite <- Hperm0.
      apply (UShKernel.sh_page_perm (uvis_perm W') 0 a
               (kexec_seg_perm p0) Hpg0); [ reflexivity | lia | lia | lia ]. }
    split.
    - exists (MkUperm true false). exact (conj Hat eq_refl).
    - intros (q & Hq & Hw). rewrite Hat in Hq. injection Hq as <-.
      discriminate Hw. }
  (* ---- the entry pc and the text inclusion ---- *)
  assert (Hpc : tf_resume_pc (uvis_tf W')
                = (mword_of_int EchoSyms.start : mword 64))
    by (rewrite Hpcw; exact echo_start_pc).
  assert (Hsub : echo_text_sub (uvis_M W')).
  { rewrite ElfUser.echo_elf_image in Himg.
    exact (UShKernel.uimg_sub_union_l _ _ _
             (UShKernel.uimg_sub_union_l _ _ _ Himg)). }
  exact (conj Hpc (conj Hsub (conj Hx (conj Hwr Hrp)))).
Qed.

(* ---- THE ARGUMENT-BLOCK HALF.  No ELF: the two page rows come in as
   premises ([echo_kexec_pages] above), and what is left is the push
   geometry [exec] computed and the readings of it echo's entry makes. *)
Lemma echo_kexec_argsc (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  uk_args_c (uvis_perm W') (uvis_M W') (uvis_av W') (uvis_argc W')
    (uint (uvis_sp W')).
Proof.
  intros Hok Hroom Hwr Hrp.
  destruct (echo_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  assert (Hargsrow : uk_args_c (uvis_perm W') (uvis_M W')
                       (uvis_av W') (uvis_argc W') (uint (uvis_sp W'))).
  { rewrite Hav Hargc Hsp'. constructor.
    - rewrite Z.rem_mod_nonneg; [ | lia | lia ].
      exact (UShKernel.kxc_sp_final_mod8 0x4000 alen na).
    - lia.
    - lia.
    - constructor; [ lia | lia | lia | | ].
      + intros j Hj. apply Hrp. lia.
      + intros j Hj. apply Hvb. lia.
    - intros i Hi.
      destruct (Z_of_nat_complete i ltac:(lia)) as [n0 ->].
      assert (Hn0 : (n0 < na)%nat) by lia.
      unfold uk_slens. rewrite (Hptr n0 ltac:(lia)).
      unfold kexec_ustack.
      destruct (decide (n0 < na)%nat) as [Hlt | Hge]; [ | exfalso; lia ].
      destruct (Hsi n0 Hn0) as [Hlo1 Hhi1].
      destruct (Hslen n0 Hn0) as [Hle1 Hcs1].
      pose proof (ucs_len _ _ _ Hcs1) as Hge0.
      split_and!; [ lia | lia | lia | exact Hcs1 | ].
      constructor; [ lia | lia | lia | | ].
      + intros j Hj. apply Hrp. lia.
      + intros j Hj.
        replace (kxc_sp 0x4000 alen (S n0) + j)
          with (kxc_sp 0x4000 alen (S n0) + Z.of_nat (Z.to_nat j)) by lia.
        apply (Hsb n0 Hn0). lia. }
  (* =============== THE TWO PRESENCE ROWS =============== *)
  exact Hargsrow.
Qed.

Lemma echo_kexec_avd (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uvis_av W' + Z.of_nat j)%Z)).
Proof.
  intros Hok Hroom Hwr.
  destruct (echo_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. rewrite Hargc in Hj. rewrite Hav. rewrite Hszv.
  destruct (Hvb (Z.of_nat j) ltac:(lia)) as [b Hb].
  apply (UShKernel.udata_lo_is_Some _ _ _ _ b Hb);
    [ apply Hwr; lia | lia ].
Qed.

Lemma echo_kexec_avs (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
     (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                    + Z.of_nat j)%Z)).
Proof.
  intros Hok Hroom Hwr.
  destruct (echo_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  (* THE TWO READINGS, EACH ONCE AND IN THE ROW'S OWN VOCABULARY.  A
     [rewrite ... in Hj] would carry the [Z.to_nat] of the opaque scan
     through the rest of the walk, and a [Qed] over that does not fit the
     kernel's stack; so the pointer and the scanned length are converted
     up front and the row's own hypotheses are never rewritten. *)
  assert (Hpi : forall i : nat, (i < na)%nat ->
            uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
            = kxc_sp 0x4000 alen (S i)).
  { intros i Hi. rewrite Hav. rewrite (Hptr i ltac:(lia)).
    unfold kexec_ustack.
    destruct (decide (i < na)%nat) as [Hlt | Hge];
      [ reflexivity | exfalso; lia ]. }
  assert (Hle2 : forall i : nat, (i < na)%nat ->
            (Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i))
             <= alen i)%nat).
  { intros i Hi. unfold uk_slens. rewrite (Hpi i Hi).
    destruct (Hslen i Hi) as [Hle1 Hcs1].
    pose proof (ucs_len _ _ _ Hcs1) as Hge0. lia. }
  intros i j Hi Hj.
  assert (Hin : (i < na)%nat) by lia.
  pose proof (Hle2 i Hin) as Hle3.
  destruct (Hsi i Hin) as [Hlo1 Hhi1].
  rewrite (Hpi i Hin). rewrite Hszv.
  destruct (Hsb i Hin j ltac:(lia)) as [b Hb].
  apply (UShKernel.udata_lo_is_Some _ _ _ _ b Hb);
    [ apply Hwr; lia | lia ].
Qed.

Lemma echo_kexec_avrows (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uvis_av W' + Z.of_nat j)%Z))
  /\ (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
        (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                       + Z.of_nat j)%Z)).
Proof.
  intros Hok Hroom Hwr Hrp.
  exact (conj (echo_kexec_avd na alen afun sts W' Hok Hroom Hwr)
              (echo_kexec_avs na alen afun sts W' Hok Hroom Hwr)).
Qed.

Lemma echo_kexec_stkrow (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  (forall j : nat, (j < 8 * 12)%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uint (uvis_sp W') - 8 * Z.of_nat 12 + Z.of_nat j)%Z)).
Proof.
  intros Hok Hroom Hwr Hrp.
  destruct (echo_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  assert (Hstkrow : forall j : nat, (j < 8 * 12)%nat ->
            is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                       !! (uint (uvis_sp W') - 8 * Z.of_nat 12
                           + Z.of_nat j)%Z)).
  { intros j Hj. rewrite Hsp'. rewrite Hszv.
    apply (UShKernel.udata_lo_is_Some _ _ _ _ (bv_0 8));
      [ apply Hbelow; lia | apply Hwr; lia | lia ]. }
  exact Hstkrow.
Qed.

Lemma echo_kexec_entry_rows (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
  kexec_sz ElfUser.echo_elf - PGSIZE + 96
    <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
  length sts = NOFILE ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  96 <= uint (uvis_sp W')
  /\ uint (uvis_sp W') mod 8 = 0
  /\ (forall j : nat, (j < 8 * 12)%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uint (uvis_sp W') - 8 * Z.of_nat 12 + Z.of_nat j)%Z))
  /\ uk_args_c (uvis_perm W') (uvis_M W') (uvis_av W') (uvis_argc W')
       (uint (uvis_sp W'))
  /\ (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uvis_av W' + Z.of_nat j)%Z))
  /\ (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
        (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                       + Z.of_nat j)%Z))
  /\ length (uvis_fd W') = NOFILE
  /\ (forall (p : mword 27) (q : UserPerm.uperm), uvis_perm W' !! p = Some q ->
        bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W')).
Proof.
  intros Hok Hroom Hfdl Hwr Hrp.
  pose proof (kexec_image_ok_below _ _ _ _ _ _ Hok) as Hstop.
  pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
  destruct (echo_kexec_geom na alen afun sts W' Hok Hroom)
    as (_ & Hlo & _ & Hsp' & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (echo_kexec_argsc na alen afun sts W' Hok Hroom Hwr Hrp)
    as Hargsrow.
  destruct (echo_kexec_avrows na alen afun sts W' Hok Hroom Hwr Hrp)
    as [Havd Havs].
  pose proof (echo_kexec_stkrow na alen afun sts W' Hok Hroom Hwr Hrp)
    as Hstkrow.
  assert (Hroom96 : 96 <= uint (uvis_sp W')) by (rewrite Hsp'; lia).
  assert (Hal8 : uint (uvis_sp W') mod 8 = 0)
    by (rewrite Hsp'; exact (UShKernel.kxc_sp_final_mod8 0x4000 alen na)).
  rewrite <- Hfd in Hfdl.
  exact (conj Hroom96 (conj Hal8 (conj Hstkrow (conj Hargsrow
           (conj Havd (conj Havs (conj Hfdl Hstop))))))).
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

  (* [uheap_ubytesq_img] and [uheap_uwordq_img] -- [UserHeap.uheap_ubytes_img]
     at ANY dfrac, which is what a node whose runs are all [DfracDiscarded]
     needs -- MOVED to [ExecArgs.v] (lane EX-3): they are how the general
     argument reading reads a heap, and nothing about them is echo's. *)

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
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Global Instance sh_echo_slot_persistent T : Persistent (sh_echo_slot T).
  Proof using . rewrite /sh_echo_slot. apply _. Qed.

  (* ...AND E2'S SEAM, AS ONE APPLICATION (the coordinator's ruling (c)).
     [UInitSh.init_sh_slot] will hand sh ONE claim law, at the whole of
     [EchoFsPure.echo_fs_pure] rather than at each pin separately -- /init's,
     /sh's and /echo's three conjuncts -- and both [FsShPin.era0_sh_pins]
     and [FsEchoPin.era0_echo_pins] project out of it.  So what E2 owes
     this lane is this, and turning it into [sh_echo_slot] is a projection
     under the law's own [□]. *)
  Definition sh_echo_slot_of_fs_pure (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜EchoFsPure.echo_fs_pure v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Lemma sh_echo_slot_of_fs_pure_holds (T : iProp Σ) :
    sh_echo_slot_of_fs_pure T -∗ sh_echo_slot T.
  Proof using .
    iIntros "(#Hinv & #Hcl & #Hgen)".
    rewrite /sh_echo_slot. iFrame "Hinv Hgen".
    iModIntro. iIntros (v) "Hp".
    iDestruct ("Hcl" $! v with "Hp") as "[$ [%Hpure | HT]]".
    - iLeft. iPureIntro. exact (proj2 (proj2 Hpure)).
    - iRight. iExact "HT".
  Qed.

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
     what [UInitSh] gets for free from [uimg_sub UInitArgv.init_argv_map M]
     at a CONSTANT image and has to be extracted for a malloc'd one. *)
  Definition echo_node_img (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) : Prop :=
    0 < t < 2 ^ 38
    /\ (forall i : nat, (i < length ws)%nat ->
          0 < s0 + Z.of_nat (UkShEcho.echo_off ws i) < 2 ^ 38)
    /\ (forall i : nat, (i < length ws)%nat -> forall k : nat, (k < 8)%nat ->
          M !! (t + 8 + 8 * Z.of_nat i + Z.of_nat k)
          = bv_to_little_endian 8 8
              (s0 + Z.of_nat (UkShEcho.echo_off ws i)) !! k)
    /\ (forall k : nat, (k < 8)%nat ->
          M !! (t + 8 + 8 * Z.of_nat (length ws) + Z.of_nat k)
          = bv_to_little_endian 8 8 0 !! k)
    /\ (forall i : nat, (i < length ws)%nat ->
          forall j : nat, (j < UkShEcho.echo_alen ws i)%nat ->
            M !! (s0 + Z.of_nat (UkShEcho.echo_off ws i) + Z.of_nat j)
            = Some (g (UkShEcho.echo_off ws i + j)%nat))
    /\ (forall i : nat, (i < length ws)%nat ->
          M !! (s0 + Z.of_nat (UkShEcho.echo_off ws i)
                + Z.of_nat (UkShEcho.echo_alen ws i)) = Some ubyte0).

  (* ONE ARGUMENT'S FOUR ROWS, at an ARBITRARY index.  [uheap]'s readings
     are pure, so the heap survives all four of them -- which is what lets
     the count be inducted on rather than unrolled. *)
  Definition echo_node_row (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) (i : nat) : Prop :=
    0 < s0 + Z.of_nat (UkShEcho.echo_off ws i) < 2 ^ 38
    /\ (forall k : nat, (k < 8)%nat ->
          M !! (t + 8 + 8 * Z.of_nat i + Z.of_nat k)
          = bv_to_little_endian 8 8
              (s0 + Z.of_nat (UkShEcho.echo_off ws i)) !! k)
    /\ (forall j : nat, (j < UkShEcho.echo_alen ws i)%nat ->
          M !! (s0 + Z.of_nat (UkShEcho.echo_off ws i) + Z.of_nat j)
          = Some (g (UkShEcho.echo_off ws i + j)%nat))
    /\ M !! (s0 + Z.of_nat (UkShEcho.echo_off ws i)
             + Z.of_nat (UkShEcho.echo_alen ws i)) = Some ubyte0.

  Lemma echo_node_row_of_cmd_x (ws : list (list (bv 8))) (gt gd gs : gname)
      (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8) (i : nat) :
    exec_ok ws ->
    (i < length ws)%nat ->
    uheap gt gd gs M pm sz -∗ ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    ⌜ echo_node_row ws M s0 t g i ⌝.
  Proof using .
    intros Hok Hi. iIntros "Hheap #Hc".
    iDestruct (UkShEcho.echo_cmd_word_x ws gd t s0 g i Hok Hi with "Hc") as "#Hw".
    iDestruct (uheap_uwordq_img with "Hheap Hw") as %Hb.
    iDestruct (UkShEcho.echo_cmd_str_x ws gd t s0 g i Hok Hi with "Hc")
      as "[%Hr #Hs]".
    iDestruct "Hs" as "(_ & _ & Hbs & Hnl)".
    iDestruct (uheap_ubytesq_img with "Hheap Hbs") as %Hg.
    iDestruct (uheap_ubyte with "Hheap Hnl") as %(Hz & _ & _).
    iPureIntro. rewrite /echo_node_row.
    split_and!; [ lia | lia | exact Hb | exact Hg | exact Hz ].
  Qed.

  Lemma echo_node_row_of_cmd (ws : list (list (bv 8))) (gt gd gs : gname)
      (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8) (i : nat) :
    line_ok ws ->
    (i < length ws)%nat ->
    uheap gt gd gs M pm sz -∗ ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    ⌜ echo_node_row ws M s0 t g i ⌝.
  Proof using .
    intro Hok__.
    exact (echo_node_row_of_cmd_x ws gt gd gs M pm sz s0 t g i (line_ok_exec_ok _ Hok__)).
  Qed.

  (* ...AND EVERY ARGUMENT, by induction on the count.  This was twelve
     [iDestruct]s at indices 0, 1 and 2. *)
  Lemma echo_node_rows_of_cmd_x (ws : list (list (bv 8))) (gt gd gs : gname)
      (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8) (n : nat) :
    exec_ok ws ->
    (n <= length ws)%nat ->
    uheap gt gd gs M pm sz -∗ ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    ⌜ forall i : nat, (i < n)%nat -> echo_node_row ws M s0 t g i ⌝.
  Proof using .
    intro Hok.
    induction n as [| n IH]; intro Hn; iIntros "Hheap #Hc".
    - iPureIntro. intros i Hi. exfalso. lia.
    - iDestruct (IH ltac:(lia) with "Hheap Hc") as %Hprev.
      iDestruct (echo_node_row_of_cmd_x ws gt gd gs M pm sz s0 t g n Hok
                   ltac:(lia) with "Hheap Hc") as %Hnew.
      iPureIntro. intros i Hi.
      destruct (decide (i < n)%nat) as [Hlt | Hge]; [ exact (Hprev i Hlt) | ].
      assert (Hin : i = n) by lia. by subst i.
  Qed.

  Lemma echo_node_rows_of_cmd (ws : list (list (bv 8))) (gt gd gs : gname)
      (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8) (n : nat) :
    line_ok ws ->
    (n <= length ws)%nat ->
    uheap gt gd gs M pm sz -∗ ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    ⌜ forall i : nat, (i < n)%nat -> echo_node_row ws M s0 t g i ⌝.
  Proof using .
    intro Hok__.
    exact (echo_node_rows_of_cmd_x ws gt gd gs M pm sz s0 t g n (line_ok_exec_ok _ Hok__)).
  Qed.

  (* ...and the ONE place the heap is touched: the deposit's loan
     ([UkRun.udepw_at] hands the supplier the two authorities and takes
     them back), read against the node's own persistent runs. *)
  Lemma echo_node_img_of_cmd_x (ws : list (list (bv 8))) (gt gd gs : gname)
      (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8) :
    exec_ok ws ->
    uheap gt gd gs M pm sz -∗ ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    ⌜ echo_node_img ws M s0 t g ⌝.
  Proof.
    intro Hok. iIntros "Hheap #Hc".
    iDestruct (UkShEcho.echo_cmd_addr ws with "Hc") as %[Htr _].
    iDestruct (UkShEcho.echo_cmd_cap ws gd t s0 g with "Hc") as "#Hwc".
    iDestruct (uheap_uwordq_img with "Hheap Hwc") as %Hbc.
    iDestruct (echo_node_rows_of_cmd_x ws gt gd gs M pm sz s0 t g
                 (length ws) Hok ltac:(lia) with "Hheap Hc") as %Hall.
    iPureIntro. rewrite /echo_node_img. split_and!.
    - lia.
    - lia.
    - intros i Hi. exact (proj1 (Hall i Hi)).
    - intros i Hi. exact (proj1 (proj2 (Hall i Hi))).
    - exact Hbc.
    - intros i Hi. exact (proj1 (proj2 (proj2 (Hall i Hi)))).
    - intros i Hi. exact (proj2 (proj2 (proj2 (Hall i Hi)))).
  Qed.

  Lemma echo_node_img_of_cmd (ws : list (list (bv 8))) (gt gd gs : gname)
      (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8) :
    line_ok ws ->
    uheap gt gd gs M pm sz -∗ ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    ⌜ echo_node_img ws M s0 t g ⌝.
  Proof.
    intro Hok__.
    exact (echo_node_img_of_cmd_x ws gt gd gs M pm sz s0 t g (line_ok_exec_ok _ Hok__)).
  Qed.

  (* THE PATH: argv[0]'s string IS "echo", terminated. *)
  (* THE EXEC'S PATH IS THE LINE'S FIRST WORD, at any exec'able word list
     (PROGRAM-STREAM stretch 12).  [sh_echo_path_of] below is this at
     [ws !!! 0 = cmd_echo]; a consumer at another command ([cat f]) reads
     its own path here. *)
  Definition sh_exec_path_of_x (ws : list (list (bv 8))) : Prop :=
    exec_ok ws ->
    forall (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8),
      echo_node_img ws M s0 t g ->
      UkShEcho.echo_argv_bytes ws g ->
      exec_path_of M (mword_of_int s0 : mword 64) (ws !!! 0%nat).

  Lemma sh_exec_path_of_x_holds (ws : list (list (bv 8))) :
    sh_exec_path_of_x ws.
  Proof using .
    intros Hok M s0 t g (_ & Hri & _ & _ & Hgi & Hzi) Hbytes.
    pose proof (exec_ok_pos ws Hok) as Hpos.
    pose proof (Hri 0%nat Hpos) as Hr.
    rewrite UkShEcho.echo_off_0 in Hr. rewrite Z.add_0_r in Hr.
    pose proof (UkShEcho.echo_off_0 ws) as Hoff0.
    set (cmd := ws !!! 0%nat).
    assert (Hal : UkShEcho.echo_alen ws 0%nat = length cmd) by reflexivity.
    pose proof (UkShEcho.echo_off_lt_x ws 0%nat (UkShEcho.echo_alen ws 0%nat)
                  Hok Hpos ltac:(lia)) as Hlt.
    pose proof (exec_ok_len ws Hok) as Hlm. unfold line_max in Hlm.
    rewrite Hoff0 Hal Nat.add_0_l in Hlt.
    assert (Hn : M !! (s0 + Z.of_nat (length cmd)) = Some (bv_0 8)).
    { rewrite <- ubyte0_bv0.
      replace (s0 + Z.of_nat (length cmd))
        with (s0 + Z.of_nat (UkShEcho.echo_off ws 0%nat)
              + Z.of_nat (UkShEcho.echo_alen ws 0%nat))
        by (rewrite Hoff0 Hal; lia).
      exact (Hzi 0%nat Hpos). }
    split_and!.
    - split; [ lia | ].
      intros j b Hj.
      pose proof (Forall_lookup_1 _ _ _ _ (exec_ok_wf ws Hok)
                    (exec_ok_at ws 0%nat Hok Hpos)) as [_ Hwa].
      pose proof (Forall_lookup_1 _ _ _ _ Hwa Hj) as Hb.
      intros ->. revert Hb. rewrite /wl_alnum. vm_compute.
      intros [H | [H | H]]; destruct H as [H1 H2];
        first [ by apply H1 | by apply H2 ].
    - intros j b Hj.
      assert (Hjl : (j < length cmd)%nat) by exact (lookup_lt_Some _ _ _ Hj).
      rewrite (uint_avi_moi s0 (Z.of_nat j) ltac:(lia) ltac:(lia)
                 ltac:(unfold Z64; lia)).
      replace (s0 + Z.of_nat j)
        with (s0 + Z.of_nat (UkShEcho.echo_off ws 0%nat) + Z.of_nat j)
        by (rewrite Hoff0; lia).
      rewrite (Hgi 0%nat Hpos j ltac:(rewrite Hal; exact Hjl)).
      f_equal.
      rewrite <- (list_lookup_total_correct _ _ _ Hj).
      rewrite (proj1 Hbytes 0%nat j Hpos ltac:(rewrite Hal; exact Hjl)).
      rewrite Hoff0 Nat.add_0_l.
      exact (UkShEcho.echo_line_word0 ws j Hok Hjl).
    - rewrite (uint_avi_moi s0 (Z.of_nat (length cmd)) ltac:(lia) ltac:(lia)
                 ltac:(unfold Z64; lia)).
      exact Hn.
  Qed.

  Definition sh_echo_path_of (ws : list (list (bv 8))) : Prop :=
    line_ok ws ->
    forall (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8),
      echo_node_img ws M s0 t g ->
      UkShEcho.echo_argv_bytes ws g ->
      exec_path_of M (mword_of_int s0 : mword 64) echo_pl.

  Lemma sh_echo_path_of_holds (ws : list (list (bv 8))) :
    sh_echo_path_of ws.
  Proof using .
    intros Hok M s0 t g (_ & Hri & _ & _ & Hgi & Hzi) Hbytes.
    pose proof (Hri 0%nat ltac:(exact (line_ok_pos ws Hok))) as Hr.
    rewrite UkShEcho.echo_off_0 in Hr. rewrite Z.add_0_r in Hr.
    pose proof (line_ok_pos ws Hok) as Hpos.
    pose proof (UkShEcho.echo_off_0 ws) as Hoff0.
    pose proof (UkShEcho.echo_alen_0 ws Hok) as Halen0.
    assert (Hn4 : M !! (s0 + 4) = Some (bv_0 8)).
    { rewrite <- ubyte0_bv0.
      replace (s0 + 4)
        with (s0 + Z.of_nat (UkShEcho.echo_off ws 0%nat)
              + Z.of_nat (UkShEcho.echo_alen ws 0%nat))
        by (rewrite Hoff0 Halen0; lia).
      exact (Hzi 0%nat Hpos). }
    split_and!.
    - exact echo_pl_shape.
    - intros j b Hj.
      assert (Hjl : (j < 4)%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
        rewrite echo_pl_len in Hlt. exact Hlt. }
      rewrite (uint_avi_moi s0 (Z.of_nat j) ltac:(lia) ltac:(lia)
                 ltac:(unfold Z64; lia)).
      replace (s0 + Z.of_nat j)
        with (s0 + Z.of_nat (UkShEcho.echo_off ws 0%nat) + Z.of_nat j)
        by (rewrite Hoff0; lia).
      rewrite (Hgi 0%nat Hpos j ltac:(rewrite Halen0; lia)).
      f_equal.
      rewrite <- (list_lookup_total_correct _ _ _ Hj).
      rewrite (echo_pl_line j Hjl).
      rewrite (proj1 Hbytes 0%nat j Hpos ltac:(rewrite Halen0; lia)).
      rewrite Hoff0 Nat.add_0_l.
      exact (UkShEcho.echo_line_cmd_byte ws j Hok Hjl).
    - rewrite echo_pl_len.
      rewrite (uint_avi_moi s0 (Z.of_nat 4%nat) ltac:(lia) ltac:(lia)
                 ltac:(unfold Z64; lia)).
      replace (s0 + Z.of_nat 4%nat) with (s0 + 4) by lia.
      exact Hn4.
  Qed.

  (* =================================================================== *)
  (*  5b.  THE NODE IS A GENERAL ARGUMENT VECTOR (lane EX-3)              *)
  (*                                                                      *)
  (*  [ExecArgs] states the argument reading at an arbitrary layout -- a   *)
  (*  [list UserHeap.uarg] at an address -- and sh's node already IS one:  *)
  (*  [UkShRun.ush_cmd_exec] hands out [UserHeap.uargv] together with the  *)
  (*  NULL cap word, which is [ExecArgs.uargv_exec] once the vector's pure *)
  (*  SHAPE is known.  So what this file still spells is only its own two  *)
  (*  facts -- the shape (a fact about the LINE sh parsed) and the layout  *)
  (*  ([echo_node_img], re-indexed) -- and the reading is general.         *)
  (* =================================================================== *)

  (* THE GENERAL STEP, at ANY exec node: [ush_cmd_exec] and the shape, and
     it names neither /echo nor its word list.  This is what a second
     program sh learns to run would take. *)
  Lemma uargv_exec_of_cmd (gd : gname) (t : Z) (args : list uarg) :
    uargv_shape args ->
    ush_cmd gd t (UExec args) -∗ uargv_exec gd (t + 8) args.
  Proof using .
    intro Hsh. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(#Hv & #Hn & _)".
    rewrite /uargv_exec /ush_ptr.
    iSplitR; [ by iPureIntro | ]. iFrame "Hv Hn".
  Qed.

  (* THE SHAPE, at /echo's word list: fewer words than MAXARG, each string
     inside the line (hence far under a page) and its terminator the cut's
     ([UkShEcho.echo_argv_bytes]'s second conjunct).  The one thing the
     line cannot say is that no pointer is NULL, and that is the node's own
     base address. *)
  Lemma echo_uargv_shape_x (ws : list (list (bv 8))) (s0 : Z) (g : nat -> bv 8) :
    exec_ok ws -> 0 < s0 -> UkShEcho.echo_argv_bytes ws g ->
    uargv_shape (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws)).
  Proof.
    intros Hok Hs0 Hbytes.
    pose proof (exec_ok_len ws Hok) as Hlm. unfold line_max in Hlm.
    split.
    - rewrite UkShEcho.echo_cmd_args_length.
      pose proof (exec_ok_lt10 ws Hok). unfold MAXARG. lia.
    - intros i x Hi.
      assert (Hi' : (i < length ws)%nat).
      { pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
        rewrite UkShEcho.echo_cmd_args_length in Hlt. exact Hlt. }
      assert (Hx : x = UArg (s0 + Z.of_nat (UkShEcho.echo_off ws i))
                        (UkShEcho.echo_alen ws i)
                        (fun j : nat => g (UkShEcho.echo_off ws i + j)%nat)).
      { rewrite (UkShEcho.echo_cmd_args_lookup_x ws s0 g i Hok Hi') in Hi.
        injection Hi as Hi. exact (eq_sym Hi). }
      rewrite Hx. cbn [UserHeap.ua_ptr UserHeap.ua_len UserHeap.ua_bytes].
      refine (conj _ (conj _ (conj _ _))).
      + pose proof (Nat2Z.is_nonneg (UkShEcho.echo_off ws i)). lia.
      + pose proof (UkShEcho.echo_off_lt_x ws i (UkShEcho.echo_alen ws i) Hok Hi'
                      ltac:(lia)) as Hb. lia.
      + intros j Hj.
        rewrite (proj1 Hbytes i j Hi' Hj).
        rewrite <- ubyte0_moi0.
        exact (line_nonul_x ws (UkShEcho.echo_off ws i + j)%nat Hok
                 (UkShEcho.echo_off_lt_x ws i j Hok Hi' ltac:(lia))).
      + rewrite (proj2 Hbytes i Hi'). exact ubyte0_moi0.
  Qed.

  Lemma echo_uargv_shape (ws : list (list (bv 8))) (s0 : Z) (g : nat -> bv 8) :
    line_ok ws -> 0 < s0 -> UkShEcho.echo_argv_bytes ws g ->
    uargv_shape (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws)).
  Proof.
    intro Hok__.
    exact (echo_uargv_shape_x ws s0 g (line_ok_exec_ok _ Hok__)).
  Qed.

  (* ...and the node's own base is positive, which is what [echo_cmd_str]
     says at argument 0 ([UkShEcho.echo_off_0]). *)
  Lemma echo_node_img_s0_pos_x (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) :
    exec_ok ws -> echo_node_img ws M s0 t g -> 0 < s0.
  Proof.
    intros Hok (_ & Hri & _ & _ & _ & _).
    pose proof (Hri 0%nat (exec_ok_pos ws Hok)) as Hr.
    rewrite (UkShEcho.echo_off_0 ws) in Hr. cbn in Hr. lia.
  Qed.

  Lemma echo_node_img_s0_pos (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) :
    line_ok ws -> echo_node_img ws M s0 t g -> 0 < s0.
  Proof.
    intro Hok__.
    exact (echo_node_img_s0_pos_x ws M s0 t g (line_ok_exec_ok _ Hok__)).
  Qed.

  (* THE LAYOUT.  [echo_node_img] stays this file's own summary -- the PATH
     reading consumes it too, and its [2 ^ 38] bounds are STRONGER than the
     general layout's [< 2 ^ 64] -- so the bridge is a re-indexing:
     argument [i]'s four rows are the [i]th element's.  The terminator row
     is the one place the line's own cut is needed, because the general
     layout asks for the string's bytes at [j <= len] in ONE clause (which
     is [SpecCopyinstr.copyinstr_got]'s spelling) and the node's summary
     keeps the NUL apart. *)
  Lemma echo_uargv_img_x (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) :
    exec_ok ws ->
    echo_node_img ws M s0 t g -> UkShEcho.echo_argv_bytes ws g ->
    uargv_img M (t + 8) (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws)).
  Proof using .
    intros Hok Himg Hbytes.
    pose proof (exec_ok_len ws Hok) as Hlm. unfold line_max in Hlm.
    pose proof Himg as (Htr & Hri & Hword & Hbc & Hgi & Hzi).
    change (2 ^ 38) with 274877906944 in Htr.
    assert (Hlen : length (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws))
                   = length ws)
      by exact (UkShEcho.echo_cmd_args_length ws s0 g).
    assert (Hel : forall (i : nat) (x : uarg),
              UkShMain.ush_args s0 g (UkShEcho.echo_toks ws) !! i = Some x ->
              (i < length ws)%nat
              /\ x = UArg (s0 + Z.of_nat (UkShEcho.echo_off ws i))
                       (UkShEcho.echo_alen ws i)
                       (fun j : nat => g (UkShEcho.echo_off ws i + j)%nat)).
    { intros i x Hi.
      assert (Hi' : (i < length ws)%nat).
      { pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
        rewrite Hlen in Hlt. exact Hlt. }
      rewrite (UkShEcho.echo_cmd_args_lookup_x ws s0 g i Hok Hi') in Hi.
      injection Hi as Hi. split; [ exact Hi' | exact (eq_sym Hi) ]. }
    pose proof (exec_ok_lt10 ws Hok) as Hws.
    rewrite /uargv_img Hlen. split_and!.
    - lia.
    - unfold Z64. lia.
    - intros i x Hi. destruct (Hel i x Hi) as [Hi' ->].
      cbn [UserHeap.ua_ptr UserHeap.ua_len].
      pose proof (Hri i Hi') as Hr. change (2 ^ 38) with 274877906944 in Hr.
      pose proof (UkShEcho.echo_off_lt_x ws i (UkShEcho.echo_alen ws i) Hok Hi'
                    ltac:(lia)) as Hb. unfold Z64. lia.
    - intros i x Hi. destruct (Hel i x Hi) as [Hi' ->].
      cbn [UserHeap.ua_ptr]. intros k Hk. exact (Hword i Hi' k Hk).
    - exact Hbc.
    - intros i x Hi. destruct (Hel i x Hi) as [Hi' ->].
      cbn [UserHeap.ua_ptr UserHeap.ua_len UserHeap.ua_bytes]. intros j Hj.
      destruct (decide (j = UkShEcho.echo_alen ws i)) as [-> | Hne].
      + rewrite (Hzi i Hi'). f_equal. exact (eq_sym (proj2 Hbytes i Hi')).
      + exact (Hgi i Hi' j ltac:(lia)).
  Qed.

  Lemma echo_uargv_img (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) :
    line_ok ws ->
    echo_node_img ws M s0 t g -> UkShEcho.echo_argv_bytes ws g ->
    uargv_img M (t + 8) (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws)).
  Proof using .
    intro Hok__.
    exact (echo_uargv_img_x ws M s0 t g (line_ok_exec_ok _ Hok__)).
  Qed.

  (* ...AND THE NODE IS A [uargv_exec] OUTRIGHT, off the heap the deposit
     lends.  This is the route a program with a malloc'd vector takes when
     it has no pure summary of its own to keep: one lemma instead of an
     induction over the word count. *)
  Lemma echo_uargv_exec_of_cmd_x (ws : list (list (bv 8))) (gd : gname)
      (t s0 : Z) (g : nat -> bv 8) :
    exec_ok ws -> 0 < s0 -> UkShEcho.echo_argv_bytes ws g ->
    ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    uargv_exec gd (t + 8) (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws)).
  Proof.
    intros Hok Hs0 Hbytes. iIntros "#Hc".
    iApply (uargv_exec_of_cmd gd t (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws))
              (echo_uargv_shape_x ws s0 g Hok Hs0 Hbytes)).
    rewrite /UkShEcho.echo_cmd. iExact "Hc".
  Qed.

  Lemma echo_uargv_exec_of_cmd (ws : list (list (bv 8))) (gd : gname)
      (t s0 : Z) (g : nat -> bv 8) :
    line_ok ws -> 0 < s0 -> UkShEcho.echo_argv_bytes ws g ->
    ush_cmd gd t (UkShEcho.echo_cmd ws s0 g) -∗
    uargv_exec gd (t + 8) (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws)).
  Proof.
    intro Hok__.
    exact (echo_uargv_exec_of_cmd_x ws gd t s0 g (line_ok_exec_ok _ Hok__)).
  Qed.

  (* THE VECTOR: sh's arguments are DETERMINED by the node it built.
     [UInitSh.init_args_det] is this lemma at init's constant image; the
     conclusion is stronger here because echo's entry reads the BYTES and
     not only the count and the lengths.

     AS RE-DERIVED (lane EX-3): both are now [ExecArgs.uargv_det] at their
     own layout, and what was ninety lines of cornering the count against
     the NULL cap and each length against its terminator is the general
     agreement lemma ([ExecArgs.exec_args_of_agree]). *)
  (* AT ANY EXEC'ABLE WORD LIST ([ExecWords.exec_ok]): nothing below reads
     the command's name. *)
  Definition echo_args_det_x (ws : list (list (bv 8))) : Prop :=
    exec_ok ws ->
    forall (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8)
           (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
      echo_node_img ws M s0 t g ->
      UkShEcho.echo_argv_bytes ws g ->
      exec_args_of M (mword_of_int (t + 8) : mword 64) na alen afun ->
      na = length ws
      /\ (forall i : nat, (i < length ws)%nat ->
            alen i = UkShEcho.echo_alen ws i)
      /\ (forall i j : nat, (i < length ws)%nat ->
            (j < UkShEcho.echo_alen ws i)%nat ->
            afun i j = wl_line ws !!! (UkShEcho.echo_off ws i + j)%nat).

  Lemma echo_args_det_x_holds (ws : list (list (bv 8))) : echo_args_det_x ws.
  Proof.
    intros Hok M s0 t g na alen afun Himg Hbytes Hargs.
    (* the [i]th element of the node's vector, named once *)
    assert (Hnth : forall i : nat, (i < length ws)%nat ->
              ua_nth (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws)) i
              = UArg (s0 + Z.of_nat (UkShEcho.echo_off ws i))
                  (UkShEcho.echo_alen ws i)
                  (fun j : nat => g (UkShEcho.echo_off ws i + j)%nat))
      by (intros i Hi;
          exact (ua_nth_lookup _ i _
                   (UkShEcho.echo_cmd_args_lookup_x ws s0 g i Hok Hi))).
    destruct (uargv_det M (t + 8) (UkShMain.ush_args s0 g (UkShEcho.echo_toks ws))
                na alen afun
                (echo_uargv_shape_x ws s0 g Hok
                   (echo_node_img_s0_pos_x ws M s0 t g Hok Himg) Hbytes)
                (echo_uargv_img_x ws M s0 t g Hok Himg Hbytes) Hargs)
      as (Hn & Hl & Hb).
    assert (Hna : na = length ws)
      by (rewrite Hn; exact (UkShEcho.echo_cmd_args_length ws s0 g)).
    split_and!.
    - exact Hna.
    - intros i Hi. rewrite (Hl i ltac:(rewrite Hna; lia)).
      rewrite /ua_alen (Hnth i Hi). reflexivity.
    - intros i j Hi Hj.
      rewrite (Hb i j ltac:(rewrite Hna; lia)
                 ltac:(rewrite (Hl i ltac:(rewrite Hna; lia));
                       rewrite /ua_alen (Hnth i Hi); cbn [UserHeap.ua_len]; lia)).
      rewrite /ua_afun (Hnth i Hi). cbn [UserHeap.ua_bytes].
      exact (proj1 Hbytes i j Hi Hj).
  Qed.

  Definition echo_args_det (ws : list (list (bv 8))) : Prop :=
    line_ok ws ->
    forall (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8)
           (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
      echo_node_img ws M s0 t g ->
      UkShEcho.echo_argv_bytes ws g ->
      exec_args_of M (mword_of_int (t + 8) : mword 64) na alen afun ->
      na = length ws
      /\ (forall i : nat, (i < length ws)%nat ->
            alen i = UkShEcho.echo_alen ws i)
      /\ (forall i j : nat, (i < length ws)%nat ->
            (j < UkShEcho.echo_alen ws i)%nat ->
            afun i j = wl_line ws !!! (UkShEcho.echo_off ws i + j)%nat).

  Lemma echo_args_det_holds (ws : list (list (bv 8))) : echo_args_det ws.
  Proof.
    intro Hok. exact (echo_args_det_x_holds ws (line_ok_exec_ok ws Hok)).
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
      (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set
         is dead data now ([UkRun.urun_parked_row]), so this entry may be
         taken at a key with a HELD descriptor (design/app-file.md SS3
         fact 4). *)
      (* ...and the key's LAZY BIT (lane LAZY-FLAG, L6), passed straight
         through to [UEchoKernel.echo_uexec_slot].  [kexec_image_ok] does
         not name it yet, so it is a premise here exactly as it is on
         [UShKernel.sh_slot_of_kexec]; the caller reads it off
         [SpecKexec.exec_slot_pre]'s wand ([PinnedExec.pex_slot]'s row). *)
      uvis_lazy W' = false ->
      ⊢ udepw_law 16 -∗
        (* ...and whether the exec'ing process's table held a pipe row
           (design/pipe.md, "The exit path"): echo's run carries it and its
           exit leaf mints the tear-down's bundle row off it.  echo's table
           IS the exec'ing process's ([SpecKexec.kexec_image_ok_fd]). *)
        UkRun.urun_nopipe sts -∗ udep -∗
        my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W'.

  Lemma echo_slot_of_kexec_holds : echo_slot_of_kexec.
  Proof.
    intros na alen afun sts W' Hok Hroom Hfdl Hlzf.
    destruct (echo_kexec_pages na alen afun sts W' Hok)
      as (Hpc & Hsub & Hx & Hwr & Hrp).
    destruct (echo_kexec_entry_rows na alen afun sts W' Hok Hroom Hfdl Hwr Hrp)
      as (Hroom96 & Hal8 & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    iIntros "#Hwr #Hnpw #Hdep #Hmp".
    (* echo's table IS the exec'ing process's, so the fact crosses by the
       image row's own equation ([SpecKexec.kexec_image_ok_fd]) *)
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite (kexec_image_ok_fd _ na alen afun sts W' Hok); iExact "Hnpw" | ].
    iApply (echo_uexec_slot W' Hpc Hsub Hx Hroom96 Hal8 Hstkrow Hargsrow
              Havd Havs Hfdlen Hstop Hlzf
              with "Hwr Hnpw' Hdep Hmp").
  Qed.

  (* ---- THE ROOM BOUND, OFF THE ARGUMENT READING (lane EX-1) ---------- *)
  (*                                                                       *)
  (*  echo's entry needs twelve words below the block the caller pushed,   *)
  (*  which is an inequality about [alen] and [na] -- FALSE for a big      *)
  (*  enough argument vector, and therefore not something echo's entry can *)
  (*  be stated without.  What discharges it is the CALLER's reading of    *)
  (*  its own argv ([echo_args_det]) together with the LINE's own bound    *)
  (*  ([echo_argv_fits_of_ok]): an admissible line has fewer than ten      *)
  (*  words and is shorter than [line_max] bytes.  Stated as a lemma of    *)
  (*  its own because the entry below and [UShEchoPay]'s paid one both     *)
  (*  need it.                                                             *)
  Lemma echo_room_of_det_x (ws : list (list (bv 8))) (na : nat)
      (alen : nat -> nat) :
    exec_ok ws ->
    na = length ws ->
    (forall i : nat, (i < length ws)%nat ->
       alen i = UkShEcho.echo_alen ws i) ->
    kexec_sz ElfUser.echo_elf - PGSIZE + 96
      <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na.
  Proof using .
    intros Hok Hna Halen.
    rewrite Hna. apply (echo_room ws).
    (* the push's span reads the SAME lengths at every index the vector
       has, so the line's own bound transports to [alen] *)
    rewrite /echo_argv_fits.
    assert (Hsp : kxc_span alen (length ws)
                  = kxc_span (UkShEcho.echo_alen ws) (length ws)).
    { assert (Hgen : forall n : nat, (n <= length ws)%nat ->
                kxc_span alen n = kxc_span (UkShEcho.echo_alen ws) n).
      { induction n as [| n IH]; intro Hn; cbn [kxc_span]; [ reflexivity | ].
        rewrite (IH ltac:(lia)) (Halen n ltac:(lia)). reflexivity. }
      exact (Hgen (length ws) ltac:(lia)). }
    rewrite Hsp. exact (echo_argv_fits_of_ok_x ws Hok).
  Qed.

  Lemma echo_room_of_det (ws : list (list (bv 8))) (na : nat)
      (alen : nat -> nat) :
    line_ok ws ->
    na = length ws ->
    (forall i : nat, (i < length ws)%nat ->
       alen i = UkShEcho.echo_alen ws i) ->
    kexec_sz ElfUser.echo_elf - PGSIZE + 96
      <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na.
  Proof using .
    intro Hok__.
    exact (echo_room_of_det_x ws na alen (line_ok_exec_ok _ Hok__)).
  Qed.

  (* ---- ...AND ECHO'S ENTRY AS THE NAMED OBLIGATION (E) --------------- *)
  (*                                                                       *)
  (*  [ExecEntry.image_entry] at /echo: section 6's bridge, moved onto the *)
  (*  shape an exec bundle takes it at ([ExecBundle.exec_bundle_of]'s      *)
  (*  third premise).  Three things are worth reading off the statement:   *)
  (*                                                                       *)
  (*  - [cw], [cs] and [pidv] are FREE.  echo reads no identity row, so    *)
  (*    its entry holds at whatever the caller's are -- which is what      *)
  (*    "the rows are the caller's knowledge, not the program's" means.    *)
  (*    sh's entry ([UShKernel.sh_image_entry_at]) fixes all three.        *)
  (*                                                                       *)
  (*  - [Pay] is [emp]: this is the UNPAID entry, the anti-vacuity witness *)
  (*    of echo's own constructor.  The PAID one -- the era's turn bundle  *)
  (*    as [Pay] -- is [UShEchoPay.echo_slot_of_kexec_at], and the caller  *)
  (*    that assembles it is [UShEchoPay.sh_exec_sup_echo_wq_holds].       *)
  (*                                                                       *)
  (*  - the ARGUMENT READING is consumed here, through                     *)
  (*    [ExecEntry.image_entry_of_at]: the entry is owed at every shape    *)
  (*    the kernel might build, and what makes that payable is that the    *)
  (*    caller's own image DETERMINES the shape ([echo_args_det]).         *)
  Lemma echo_image_entry (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32) :
    line_ok ws ->
    echo_node_img ws M s0 t g ->
    UkShEcho.echo_argv_bytes ws g ->
    length sts = NOFILE ->
    (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set
       is dead data now ([UkRun.urun_parked_row]), so this entry may be
       taken at a key with a HELD descriptor (design/app-file.md SS3
       fact 4). *)
    udepw_law 16 -∗
    (* ...and the exec'ing process's table, pipe-free (design/pipe.md,
       "The exit path") *)
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv (fun _ : Z => True)%I emp uslot.
  Proof.
    intros Hok Himg Hbytes Hfdl. iIntros "#Hwr #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (echo_args_det_holds ws Hok M s0 t g na alen afun Himg Hbytes
                Hargs) as (Hna & Halen & _).
    rewrite /image_entry_at. iIntros "!>" (W') "%Hokk _ %Hlzf _ _ Hmp _".
    iApply (echo_slot_of_kexec_holds na alen afun sts W' Hokk
              (echo_room_of_det ws na alen Hok Hna Halen) Hfdl
              Hlzf with "Hwr Hnpw Hdep Hmp").
  Qed.

  (* =================================================================== *)
  (*  7.  THE ASSEMBLY -- MOVED (lane IO-LEAF, step 4).                    *)
  (*                                                                      *)
  (*  [sh_exec_sup_of_echo_slot] / [_holds] / [_closed] -- sh's pinned    *)
  (*  bundle paying its exec supply at the TRIVIAL payload and the FREE   *)
  (*  write law -- are gone: the shell's forked child runs /echo on the   *)
  (*  PAID entry now ([UEchoOut.echo_uexec_slot_at]), at the payload sh's *)
  (*  fork chose, and that assembly needs the era's links, which sit above *)
  (*  this file.  It is [UShEchoPay.sh_exec_sup_echo_wq_holds].  The       *)
  (*  generic entry at the exec channel ([echo_slot_of_kexec], section 6)  *)
  (*  stays as the anti-vacuity witness of echo's own constructor.        *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  8.  S3 -- ECHO'S OUTPUT                                             *)
  (*                                                                      *)
  (*  echo's loop is                                                       *)
  (*    for (i = 1; i < argc; i++) {                                       *)
  (*      write(1, argv[i], strlen(argv[i]));                              *)
  (*      write(1, i + 1 < argc ? " " : "\n", 1);                          *)
  (*    }                                                                  *)
  (*  so at [argc] arguments it writes [2 * (argc - 1)] buffers, in this   *)
  (*  order.                                                               *)
  (* =================================================================== *)
  (* ...and those bytes are [wl_line (drop 1 ws)] -- the line minus its
     command name.  There is no second spelling of them here: the loop's
     output IS the join, and [LineWords] is where the join is named. *)

  (* ---- E4's OWN PART: the argv echo reads off its key ARE the strings -- *)
  (* [UEchoKernel.echo_arg] is a FUNCTION of the key (the pointer is the
     eight image bytes of the slot read as a word, the length is what a
     scan finds, the bytes are the image's), so what has to be shown is
     that [kexec_args_at]'s block, built from the [(na, alen, afun)] that
     [echo_args_det] pinned, is read back as the same strings. *)
  (* THE KEY'S READING OF ITS ARGUMENT VECTOR IS THE STRINGS exec PUSHED.
     [UEchoKernel.echo_arg] is a FUNCTION of the key -- the pointer is the
     eight image bytes of the slot read as a word, the length is what a
     scan finds, the bytes are the image's -- and this says that function
     agrees with the [(na, alen, afun)] the exec channel carried.

     NOT AT THREE ARGUMENTS OF FOUR AND FIVE BYTES.  It used to compute
     [kxc_sp_final 0x4000 alen 3 = 0x3FB0] and the three string addresses
     as closed numbers, which is a proof about one argument vector.  The
     addresses come off [KexecDefs]' push geometry now: the block lies
     between the stack page's base and its top because the C tested the
     pointer after every push ([kxc_stack_ok]), and that is the whole of
     what puts them in machine range.

     THE ONE SIDE CONDITION is that no pushed byte is a NUL -- which is
     what pins each string's LENGTH, because a scan that stopped early
     would have to find one.  The ELF is still echo's: [kexec_sz] decides
     the stack page, and nothing else here is about the program. *)
  Definition echo_key_args : Prop :=
    forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
           (sts : list fdstate) (W' : uvis),
      kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
      (forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
         afun i j <> ubyte0) ->
      Z.to_nat (uvis_argc W') = na
      /\ (forall i : nat, (i < na)%nat ->
            ua_len (echo_arg (uvis_M W') (uvis_av W') i) = alen i
            /\ forall j : nat, (j < alen i)%nat ->
                 ua_bytes (echo_arg (uvis_M W') (uvis_av W') i) j
                 = afun i j).

  Lemma echo_key_args_holds : echo_key_args.
  Proof using .
    intros na alen afun sts W' Hok Hno.
    pose proof echo_kexec_sz as Hsz.
    unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
    destruct Hok as (_ & _ & _ & Ha1w & Ha0w & _
                     & (Hstr & Hnul & Hvec) & (Hfit & _) & _ & _ & _ & _).
    unfold PGSIZE in Hfit.
    (* ---- THE BLOCK IS INSIDE THE STACK PAGE ---- *)
    pose proof (kxc_argc_bound 0x4000 (0x4000 - 4096) alen na Hfit) as Hnab.
    assert (Hsprange : forall i : nat, (i < na)%nat ->
              0x4000 - 4096 <= kxc_sp 0x4000 alen (S i) <= 0x4000)
      by (intros i Hi;
          exact (kxc_sp_range 0x4000 (0x4000 - 4096) alen na (S i)
                   Hfit ltac:(lia) ltac:(lia))).
    pose proof (kxc_sp_final_range 0x4000 (0x4000 - 4096) alen na Hfit)
      as Hfinal.
    (* ---- the key's own a0/a1 ---- *)
    assert (Hav : uvis_av W' = kxc_sp_final 0x4000 alen na).
    { unfold uvis_av. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a1.
      rewrite Ha1w. apply uint_moi. unfold Z64. lia. }
    assert (Hargc : uvis_argc W' = Z.of_nat na).
    { unfold uvis_argc. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a0.
      rewrite Ha0w. apply uint_moi. unfold Z64. lia. }
    (* ---- the pointers the vector spells ---- *)
    assert (Hptr : forall i : nat, (i < na)%nat ->
              uk_argv_p (uvis_M W') (kxc_sp_final 0x4000 alen na) (Z.of_nat i)
              = kxc_sp 0x4000 alen (S i)).
    { intros i Hi. apply uk_argv_p_of_bytes.
      - pose proof (Hsprange i Hi). unfold Z64. lia.
      - intros k Hk.
        pose proof (Hvec i k ltac:(lia) Hk) as Hb.
        unfold kexec_ustack in Hb.
        destruct (decide (i < na)%nat) as [Hlt | Hge]; [ | exfalso; lia ].
        exact Hb. }
    (* ---- each string is NUL-terminated exactly where exec put the NUL ---- *)
    assert (Hcs : forall i : nat, (i < na)%nat ->
              ucstr (uvis_M W') (kxc_sp 0x4000 alen (S i))
                (Z.of_nat (alen i))).
    { intros i Hi. constructor.
      - lia.
      - intros j Hj. exists (afun i (Z.to_nat j)). split.
        + replace (kxc_sp 0x4000 alen (S i) + j)
            with (kxc_sp 0x4000 alen (S i) + Z.of_nat (Z.to_nat j)) by lia.
          apply Hstr; lia.
        + apply Hno; lia.
      - rewrite ubyte0_bv0. exact (Hnul i Hi). }
    assert (Hlen : forall i : nat, (i < na)%nat ->
              uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i))
              = Z.of_nat (alen i)).
    { intros i Hi. apply uk_slen_ucstr; [ | exact (Hcs i Hi) ].
      pose proof (kxc_len_bound 0x4000 (0x4000 - 4096) alen na i Hfit Hi).
      change (2 ^ 31) with 2147483648. lia. }
    (* ---- and that is the key's own reading ---- *)
    split; [ rewrite Hargc; lia | ].
    intros i Hi. unfold echo_arg. cbn [ua_len ua_bytes].
    rewrite Hav. unfold uk_slens. rewrite (Hptr i Hi). rewrite (Hlen i Hi).
    split; [ lia | ].
    intros j Hj. rewrite (Hstr i j Hi Hj). reflexivity.
  Qed.

  (* ---- the shape a list of [uarg]s has when it IS the line's words ---- *)
  Definition echo_argv_is (ws : list (list (bv 8))) (args : list uarg)
    : Prop :=
    length args = length ws
    /\ forall (i : nat) (x : uarg), args !! i = Some x ->
         ua_len x = UkShEcho.echo_alen ws i
         /\ forall j : nat, (j < UkShEcho.echo_alen ws i)%nat ->
              ua_bytes x j = wl_line ws !!! (UkShEcho.echo_off ws i + j)%nat.

  (* ---- ECHO'S POST OVER ITS TRANSCRIPT ------------------------------- *)
  (*                                                                       *)
  (*  [UkEcho.wp_kecho_write] goes through [UkRunSys]'s QUIET row today:   *)
  (*  it returns an unconstrained [ret] and says nothing about a byte.     *)
  (*  The leaf that KEEPS the receipt is TX-RECEIPT's                      *)
  (*  [wp_uk_ecall_write_recv] -- “my transcript grew by exactly the first *)
  (*  [r] bytes of my buffer” -- and it is NOT built here (it is E5's, on  *)
  (*  lane/tx-receipt).  So it is a NAMED HYPOTHESIS: [recv N] is that     *)
  (*  leaf and [tx N bs] the program-side transcript handle it moves.      *)
  (*                                                                       *)
  (*  WHAT E4 OWES against it is the two things this lane knows and E5     *)
  (*  does not: the argv bytes ARE the words of the line sh parsed         *)
  (*  ([echo_key_args], from [echo_cmd] through the exec channel) and the  *)
  (*  LOOP'S ORDER -- so the transcript at echo's [exit] ecall is the      *)
  (*  entry's plus [wl_line (drop 1 ws)], the line minus its command name, *)
  (*  and nothing else.                                                    *)
  (* =================================================================== *)
  Definition echo_writes_out (ws : list (list (bv 8)))
      (recv : uk_names Σ -> iProp Σ)
      (tx : uk_names Σ -> list (bv 8) -> iProp Σ) : Prop :=
    forall (N : uk_names Σ) (h : CpuId) (m : regfile) (av : Z)
           (args : list uarg) (bs : list (bv 8)) (n : nat),
      m !!! Regidx a0_idx
        = (mword_of_int (Z.of_nat (length args)) : mword 64) ->
      m !!! Regidx a1_idx = (mword_of_int av : mword 64) ->
      echo_argv_is ws args ->
      ⊢ recv N -∗ udepw_law 16 -∗ echo_code (ukn_t N) -∗
        uargv (ukn_d N) av args -∗ tx N bs -∗
        urun N h m (mword_of_int EchoSyms.start) (2 + (8 + (2 + n))) -∗
        (∀ (h' : CpuId) (m' : regfile),
           tx N (bs ++ wl_line (drop 1 ws)) -∗
           urun N h' m' (mword_of_int EchoSyms.exit) n -∗
           mWP (Loop : expr riscv_lang)) -∗
        mWP (Loop : expr riscv_lang).

End UShEcho.
