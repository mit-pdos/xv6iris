(* ===================================================================== *)
(* UShGeom.v -- THE EXEC GEOMETRY, ONCE (user-once C1;                    *)
(* design/user-once.md SS4, [image_geom E frame]).                        *)
(*                                                                        *)
(* [UShEcho.v] turns [SpecKexec.kexec_image_ok] at [ElfUser.echo_elf]     *)
(* into the rows [UEchoKernel.echo_uexec_slot] reads off the key, and     *)
(* [UShCat.v] is "the same derivation at [ElfUser.cat_elf]" with, as its  *)
(* own header says, four differences -- of which ONE is about the push:   *)
(* the entry's FRAME (echo twelve words, cat forty-two).  Everything else *)
(* in the two chains is about the stack page exec built, and the stack    *)
(* page is decided by [kexec_sz], which is 0x4000 for both images.        *)
(*                                                                        *)
(* So the chain is stated here ONCE, over an image [E] with               *)
(* [kexec_sz E = 0x4000] and a frame [frame] in words:                    *)
(*                                                                        *)
(*   (1) the push helpers ([uscan_nul], [uk_slen_nul], [bv_le8_is_Some],  *)
(*       [kexec_vec_bytes], [uk_argv_p_of_bytes], [kxc_span_le_line]),    *)
(*       moved down from UShEcho SS3c verbatim (that file re-exports       *)
(*       them under their landed names);                                  *)
(*   (2) the room: [img_argv_fits frame] (the push leaves [8 * frame]     *)
(*       bytes of the stack page), [img_room], and that every admissible *)
(*       line earns it at any frame up to 370 words                       *)
(*       ([img_argv_fits_of_ok]: a line has fewer than ten words each     *)
(*       under [line_max] bytes, so the push is under 1131 bytes);        *)
(*   (3) THE PUSH GEOMETRY [img_kexec_geom] -- the twelve closed readings  *)
(*       of the key -- and the rows off it ([img_kexec_argsc], [_avd],     *)
(*       [_avs], [_avrows], [_stkrow], [img_kexec_entry_rows]);            *)
(*   (4) THE PAGE HALF, in its image-generic part: the stack page RW, page *)
(*       0 X-and-not-W off the FIRST PT_LOAD's shape (a premise, read off *)
(*       the literal per image), the image inclusion and the entry pc     *)
(*       ([img_kexec_pages]); page 1 W off the SECOND PT_LOAD             *)
(*       ([img_kexec_page1_w], cat's .bss page).  What stays per image is *)
(*       the text/data INCLUSIONS (a union shape of the literal) and the  *)
(*       zero window;                                                     *)
(*   (5) the room off the argument reading ([img_room_of_det]) and the    *)
(*       key's own reading of its vector ([img_key_args]).                 *)
(*                                                                        *)
(* echo is this at [(ElfUser.echo_elf, 12)], cat at [(ElfUser.cat_elf,    *)
(* 42)]; both files' statements are unchanged and their proofs are the    *)
(* instances.  PURE: no resource crosses this file.                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.   (* ssreflect's [rewrite], as UShEcho has it *)
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.       (* [fdstate] *)
Require Import ElfFile ElfUser ElfLoadable.
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeArith UmodeAbi.
Require Import SpecKexec SpecCopyin.   (* [uimg_word_at] *)
Require Import UImgWordDefs.      (* [img_word_of_bytes] / [uimg_word_det] *)
Require Import UShKernel.
Require Import KexecBuilt.
Require Import UserPtTree.        (* [pgroundup] *)
Require Import WpUmodeLoad.       (* [uM_word] / [uM_word_bytes] *)
Require Import KexecDefs.
Require Import UkAbi.
Require Import UEchoKernel.       (* [echo_arg]: the argument reading, which names no program *)
Require Import LineWords.
Require Import UkShEcho.          (* [echo_alen]: the caller's own argument lengths *)
Require Import EchoDisc.
Require Import ExecWords.         (* [exec_ok]: [line_ok] without the command *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  1.  THE PUSH HELPERS (UShEcho SS3c, moved)                             *)
(* ===================================================================== *)
Lemma ubyte0_bv0 : ubyte0 = (bv_0 8 : bv 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ubyte0_moi0 : ubyte0 = (mword_of_int 0 : mword 8).
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
    (* [uM_word M a 8 : mword (8 * 8)], so the byte lemma's [bv_unsigned]
       elaborates at width [8 * 8] where the goal's is at [64]: convertible,
       which [exact] sees and a [rewrite] pattern does not. *)
    pose proof (bv_le_nth_byte (bv_unsigned (uM_word M (av + 8 * i) 8)) k Hk)
      as Hle.
    rewrite Hww in Hle.
    exact (eq_trans (Hw k ltac:(lia)) (eq_sym Hle)). }
  pose proof (uimg_word_det M (av + 8 * i) (uM_word M (av + 8 * i) 8) z
                ltac:(unfold Z64 in Hz; lia) Hiw Hb) as He.
  unfold uk_argv_p, uk_argv_w. rewrite He.
  exact (uint_moi z Hz).
Qed.


(* ===================================================================== *)
(*  2.  THE ROOM                                                          *)
(*                                                                        *)
(*  The entry needs [frame] words below the block the caller pushed.      *)
(*  What buys it is a bound on how much stack the arguments took: their   *)
(*  own bytes, their NULs, the vector's words and at most fifteen of      *)
(*  alignment each ([KexecDefs.kxc_sp_final_ge]).  THAT BOUND IS A SIDE   *)
(*  CONDITION ON THE LINE, and the right one: a line long enough to crowd *)
(*  the frame off its own stack page is a line the claim must not be     *)
(*  about.                                                                *)
(* ===================================================================== *)
Definition img_argv_fits (frame : nat) (ws : list (list (bv 8)))
    (alen : nat -> nat) : Prop :=
  kxc_span alen (length ws)
    + (8 * (Z.of_nat (length ws) + 1) + 16)
  <= PGSIZE - 8 * Z.of_nat frame.

Lemma img_room (E : elf_bytes) (frame : nat) (ws : list (list (bv 8)))
    (alen : nat -> nat) :
  kexec_sz E = 0x4000 ->
  img_argv_fits frame ws alen ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen (length ws).
Proof.
  intros HE. rewrite /img_argv_fits. intro Hfit. rewrite HE.
  pose proof (kxc_sp_final_ge 0x4000 alen (length ws)).
  unfold PGSIZE in *. lia.
Qed.

(* ...AND EVERY ADMISSIBLE LINE EARNS THE ROOM, at any frame up to 370
   words.  One argument costs its bytes, its NUL and at most fifteen
   bytes of alignment ([KexecDefs.kxc_span] adds [len i + 16] per word),
   a word of an admissible line is shorter than [EchoDisc.line_max] = 100
   bytes, and [line_ok] allows fewer than ten words -- so the whole push
   is under 1131 bytes of a 4096-byte stack page, and 8 * 370 = 2960 more
   still fit. *)
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

Lemma img_argv_fits_of_ok_x (frame : nat) (ws : list (list (bv 8))) :
  (frame <= 370)%nat ->
  exec_ok ws -> img_argv_fits frame ws (UkShEcho.echo_alen ws).
Proof.
  intros Hfr Hok. rewrite /img_argv_fits.
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

Lemma img_argv_fits_of_ok (frame : nat) (ws : list (list (bv 8))) :
  (frame <= 370)%nat ->
  line_ok ws -> img_argv_fits frame ws (UkShEcho.echo_alen ws).
Proof.
  intros Hfr Hok__.
  exact (img_argv_fits_of_ok_x frame ws Hfr (line_ok_exec_ok _ Hok__)).
Qed.

(* ===================================================================== *)
(*  3.  THE PUSH GEOMETRY, as twelve closed readings of the key.          *)
(*                                                                        *)
(*  PURE -- no resource crosses this lemma, which is what keeps the Iris  *)
(*  proofs above a three-liner (and their [Qed] inside the kernel's       *)
(*  stack).  Split off from the rows below for one reason: a single [Qed] *)
(*  over both overflows the kernel's stack.                               *)
(* ===================================================================== *)
Lemma img_kexec_geom (E : elf_bytes) (frame : nat) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_sz E = 0x4000 ->
  kexec_image_ok E na alen afun sts W' ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na ->
  uvis_sz W' = 0x4000
  /\ 0x3000 + 8 * Z.of_nat frame <= kxc_sp_final 0x4000 alen na
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
  intros Hsz Hok Hroom.
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
  assert (Hlo : 0x3000 + 8 * Z.of_nat frame <= kxc_sp_final 0x4000 alen na) by lia.
  assert (Hhi : kxc_sp_final 0x4000 alen na + 8 * (Z.of_nat na + 1)
                <= 0x4000) by lia.
  assert (Hna : 0 <= Z.of_nat na < 2 ^ 31) by lia.
  (* ---- the three registers the entry reads off the trapframe ---- *)
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

(* ===================================================================== *)
(*  4.  THE PAGE HALF, image-generic: the stack page RW at every byte,     *)
(*      page 0 X-and-not-W off the FIRST PT_LOAD's shape, the image       *)
(*      inclusion and the entry pc.  Everything that touches the ELF is   *)
(*      here and NOTHING else is (a [Qed] over both halves overflows the  *)
(*      kernel's stack).  The load's shape is a PREMISE: it is read off   *)
(*      the literal per image ([UShEcho.echo_loads], [UShCat.cat_loads]). *)
(* ===================================================================== *)
Lemma img_kexec_pages (E : elf_bytes) (e : Z) (p0 : elf_phdr) (rest : list elf_phdr)
    (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_top E = 0x2000 ->
  elf_entry E = Some e ->
  elf_loads E = p0 :: rest ->
  ep_vaddr p0 = 0 -> 0 < ep_memsz p0 <= 4096 -> ep_flags p0 = 5 ->
  kexec_image_ok E na alen afun sts W' ->
  tf_resume_pc (uvis_tf W') = ret_pc (mword_of_int e : mword 64)
  /\ uimg_sub (elf_image E) (uvis_M W')
  /\ (forall a : Z, 0 <= a < 4096 ->
        ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 ->
        uk_rpage (uvis_perm W') (mword_of_int a : mword 64)).
Proof.
  intros Htop Hent Hld Hv0 Hm0 Hf0 Hok.
  pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok Hent) as Hpc.
  assert (Hsz : kexec_sz E = 0x4000) by (unfold kexec_sz; rewrite Htop; reflexivity).
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hspw & Ha1w & Ha0w & Himg
                   & (Hstr & Hnul & Hvec) & (_ & Hzero) & Hperm & _ & _ & _).
  destruct Hperm as (Hpg & _ & Hstpg).
  rewrite Htop in Hstpg. change (0x2000 + PGSIZE) with 0x3000 in Hstpg.
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
  (* ---- page 0 is the text: X and not W ---- *)
  assert (Hpg0 : uvis_perm W' !! kexec_pg 0 = Some (kexec_seg_perm p0)).
  { apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    rewrite kexec_sz_after_nil. rewrite Hv0.
    split_and!; [ reflexivity
                | change (UserPtTree.pgroundup 0) with 0; lia
                | lia ]. }
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
  exact (conj Hpc (conj Himg (conj Hx (conj Hwr Hrp)))).
Qed.

(* ...and page 1 is WRITABLE when the SECOND PT_LOAD is RW- at 0x1000
   (cat's .bss page; echo has no writable data at all). *)
Lemma img_kexec_page1_w (E : elf_bytes) (p0 p1 : elf_phdr) (rest : list elf_phdr)
    (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_top E = 0x2000 ->
  elf_loads E = p0 :: p1 :: rest ->
  ep_vaddr p0 = 0 -> 0 <= ep_memsz p0 <= 4096 ->
  ep_vaddr p1 = 0x1000 -> 0 < ep_memsz p1 <= 4096 -> ep_flags p1 = 6 ->
  kexec_image_ok E na alen afun sts W' ->
  forall a : Z, 0x1000 <= a < 0x2000 -> uw_addr (uvis_perm W') a.
Proof.
  intros Htop Hld Hv0 Hm0 Hv1 Hm1 Hf1 Hok.
  assert (Hsz : kexec_sz E = 0x4000) by (unfold kexec_sz; rewrite Htop; reflexivity).
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & Hperm & _ & _ & _).
  destruct Hperm as (Hpg & _ & _).
  assert (Hpg1 : uvis_perm W' !! kexec_pg 0x1000 = Some (kexec_seg_perm p1)).
  { apply (Hpg 1%nat p1); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    change ([p0]) with (@nil elf_phdr ++ [p0]).
    rewrite (kexec_sz_after_snoc_le [] p0
               ltac:(rewrite kexec_sz_after_nil Hv0; lia)).
    rewrite Hv0 Hv1.
    split_and!; [ reflexivity
                | unfold UserPtTree.pgroundup; lia
                | lia ]. }
  assert (Hperm1 : kexec_seg_perm p1 = MkUperm false true)
    by (unfold kexec_seg_perm; rewrite Hf1; reflexivity).
  intros a Ha. exists (MkUperm false true). split; [ | reflexivity ].
  rewrite <- Hperm1.
  apply (UShKernel.sh_page_perm (uvis_perm W') 0x1000 a
           (kexec_seg_perm p1) Hpg1); [ reflexivity | lia | lia | lia ].
Qed.

(* ===================================================================== *)
(*  5.  THE ROWS OFF THE GEOMETRY.  No ELF: the two page rows come in as  *)
(*      premises ([img_kexec_pages]), and what is left is the push        *)
(*      geometry [exec] computed and the readings of it the entry makes.  *)
(* ===================================================================== *)
Lemma img_kexec_argsc (E : elf_bytes) (frame : nat) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_sz E = 0x4000 ->
  kexec_image_ok E na alen afun sts W' ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  uk_args_c (uvis_perm W') (uvis_M W') (uvis_av W') (uvis_argc W')
    (uint (uvis_sp W')).
Proof.
  intros Hsz Hok Hroom Hwr Hrp.
  destruct (img_kexec_geom E frame na alen afun sts W' Hsz Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  rewrite Hav Hargc Hsp'. constructor.
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
      apply (Hsb n0 Hn0). lia.
Qed.

Lemma img_kexec_avd (E : elf_bytes) (frame : nat) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_sz E = 0x4000 ->
  kexec_image_ok E na alen afun sts W' ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uvis_av W' + Z.of_nat j)%Z)).
Proof.
  intros Hsz Hok Hroom Hwr.
  destruct (img_kexec_geom E frame na alen afun sts W' Hsz Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. rewrite Hargc in Hj. rewrite Hav. rewrite Hszv.
  destruct (Hvb (Z.of_nat j) ltac:(lia)) as [b Hb].
  apply (UShKernel.udata_lo_is_Some _ _ _ _ b Hb);
    [ apply Hwr; lia | lia ].
Qed.

Lemma img_kexec_avs (E : elf_bytes) (frame : nat) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_sz E = 0x4000 ->
  kexec_image_ok E na alen afun sts W' ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
     (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                    + Z.of_nat j)%Z)).
Proof.
  intros Hsz Hok Hroom Hwr.
  destruct (img_kexec_geom E frame na alen afun sts W' Hsz Hok Hroom)
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

Lemma img_kexec_avrows (E : elf_bytes) (frame : nat) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_sz E = 0x4000 ->
  kexec_image_ok E na alen afun sts W' ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na ->
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
  intros Hsz Hok Hroom Hwr Hrp.
  exact (conj (img_kexec_avd E frame na alen afun sts W' Hsz Hok Hroom Hwr)
              (img_kexec_avs E frame na alen afun sts W' Hsz Hok Hroom Hwr)).
Qed.

(* the frame's own bytes: [8 * frame] zeroed, writable bytes below the
   entry sp, inside the key's writable data *)
Lemma img_kexec_stkrow (E : elf_bytes) (frame : nat) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_sz E = 0x4000 ->
  kexec_image_ok E na alen afun sts W' ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * frame)%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uint (uvis_sp W') - 8 * Z.of_nat frame + Z.of_nat j)%Z)).
Proof.
  intros Hsz Hok Hroom Hwr.
  destruct (img_kexec_geom E frame na alen afun sts W' Hsz Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. rewrite Hsp'. rewrite Hszv.
  apply (UShKernel.udata_lo_is_Some _ _ _ _ (bv_0 8));
    [ apply Hbelow; lia | apply Hwr; lia | lia ].
Qed.

Lemma img_kexec_entry_rows (E : elf_bytes) (frame : nat) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_sz E = 0x4000 ->
  kexec_image_ok E na alen afun sts W' ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na ->
  length sts = NOFILE ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  8 * Z.of_nat frame <= uint (uvis_sp W')
  /\ uint (uvis_sp W') mod 8 = 0
  /\ uvis_sz W' = 0x4000
  /\ (forall j : nat, (j < 8 * frame)%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uint (uvis_sp W') - 8 * Z.of_nat frame + Z.of_nat j)%Z))
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
  intros Hsz Hok Hroom Hfdl Hwr Hrp.
  pose proof (kexec_image_ok_below _ _ _ _ _ _ Hok) as Hstop.
  pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
  destruct (img_kexec_geom E frame na alen afun sts W' Hsz Hok Hroom)
    as (Hszv & Hlo & _ & Hsp' & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (img_kexec_argsc E frame na alen afun sts W' Hsz Hok Hroom Hwr Hrp)
    as Hargsrow.
  destruct (img_kexec_avrows E frame na alen afun sts W' Hsz Hok Hroom Hwr Hrp)
    as [Havd Havs].
  pose proof (img_kexec_stkrow E frame na alen afun sts W' Hsz Hok Hroom Hwr)
    as Hstkrow.
  assert (Hroomf : 8 * Z.of_nat frame <= uint (uvis_sp W')) by (rewrite Hsp'; lia).
  assert (Hal8 : uint (uvis_sp W') mod 8 = 0)
    by (rewrite Hsp'; exact (UShKernel.kxc_sp_final_mod8 0x4000 alen na)).
  rewrite <- Hfd in Hfdl.
  exact (conj Hroomf (conj Hal8 (conj Hszv (conj Hstkrow (conj Hargsrow
           (conj Havd (conj Havs (conj Hfdl Hstop)))))))).
Qed.

(* ===================================================================== *)
(*  6.  THE ROOM OFF THE ARGUMENT READING (lane EX-1).                    *)
(*                                                                        *)
(*  The entry needs [frame] words below the block the caller pushed,      *)
(*  which is an inequality about [alen] and [na] -- FALSE for a big       *)
(*  enough argument vector.  What discharges it is the CALLER's reading  *)
(*  of its own argv ([UShEcho.echo_args_det]) together with the LINE's    *)
(*  own bound: an admissible line has fewer than ten words and is shorter *)
(*  than [line_max] bytes.                                                *)
(* ===================================================================== *)
Lemma img_room_of_det_x (E : elf_bytes) (frame : nat) (ws : list (list (bv 8)))
    (na : nat) (alen : nat -> nat) :
  kexec_sz E = 0x4000 ->
  (frame <= 370)%nat ->
  exec_ok ws ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na.
Proof.
  intros Hsz Hfr Hok Hna Halen.
  rewrite Hna. apply (img_room E frame ws alen Hsz).
  rewrite /img_argv_fits.
  assert (Hsp : kxc_span alen (length ws)
                = kxc_span (UkShEcho.echo_alen ws) (length ws)).
  { assert (Hgen : forall n : nat, (n <= length ws)%nat ->
              kxc_span alen n = kxc_span (UkShEcho.echo_alen ws) n).
    { induction n as [| n IH]; intro Hn; cbn [kxc_span]; [ reflexivity | ].
      rewrite (IH ltac:(lia)) (Halen n ltac:(lia)). reflexivity. }
    exact (Hgen (length ws) ltac:(lia)). }
  rewrite Hsp. exact (img_argv_fits_of_ok_x frame ws Hfr Hok).
Qed.

Lemma img_room_of_det (E : elf_bytes) (frame : nat) (ws : list (list (bv 8)))
    (na : nat) (alen : nat -> nat) :
  kexec_sz E = 0x4000 ->
  (frame <= 370)%nat ->
  line_ok ws ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  kexec_sz E - PGSIZE + 8 * Z.of_nat frame
    <= kxc_sp_final (kexec_sz E) alen na.
Proof.
  intros Hsz Hfr Hok__.
  exact (img_room_of_det_x E frame ws na alen Hsz Hfr (line_ok_exec_ok _ Hok__)).
Qed.

(* ===================================================================== *)
(*  7.  THE KEY'S OWN READING OF ITS ARGUMENT VECTOR IS THE STRINGS exec  *)
(*      PUSHED.  [UEchoKernel.echo_arg] is a FUNCTION of the key -- the   *)
(*      pointer is the eight image bytes of the slot read as a word, the  *)
(*      length is what a scan finds, the bytes are the image's -- and     *)
(*      this says that function agrees with the [(na, alen, afun)] the    *)
(*      exec channel carried.  The addresses come off [KexecDefs]' push   *)
(*      geometry: the block lies between the stack page's base and its   *)
(*      top because the C tested the pointer after every push            *)
(*      ([kxc_stack_ok]).  THE ONE SIDE CONDITION is that no pushed byte  *)
(*      is a NUL -- which is what pins each string's LENGTH.  The ELF     *)
(*      enters only through [kexec_sz].                                   *)
(* ===================================================================== *)
Definition img_key_args (E : elf_bytes) : Prop :=
  forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (sts : list fdstate) (W' : uvis),
    kexec_image_ok E na alen afun sts W' ->
    (forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
       afun i j <> ubyte0) ->
    Z.to_nat (uvis_argc W') = na
    /\ (forall i : nat, (i < na)%nat ->
          ua_len (echo_arg (uvis_M W') (uvis_av W') i) = alen i
          /\ forall j : nat, (j < alen i)%nat ->
               ua_bytes (echo_arg (uvis_M W') (uvis_av W') i) j
               = afun i j).

Lemma img_key_args_holds (E : elf_bytes) :
  kexec_sz E = 0x4000 -> img_key_args E.
Proof.
  intros Hsz na alen afun sts W' Hok Hno.
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
