(* ===================================================================== *)
(* ExecArgs.v -- THE CALLER'S ARGUMENT VECTOR AND PATH, AT ANY LAYOUT.    *)
(*                                                                       *)
(* design/user-exec.md section 4's EX-3.  [SpecSysExec.exec_args_of M av  *)
(* na alen afun] is the reading sys_exec performs of the CALLER's own     *)
(* image: the [na + 1] pointer words at [av + 8i], the strings they name, *)
(* and the shape kexec accepts.  Until now every program that execs       *)
(* re-derived that reading from its own layout -- /init from two catalog  *)
(* inclusions at literal addresses ([UInitSh.init_args_det]), /sh from a  *)
(* malloc'd node by induction on the word count ([UShEcho.echo_args_det]) *)
(* -- and the two proofs look nothing alike although they say the same    *)
(* thing.  This file says it once.                                       *)
(*                                                                       *)
(* THE SHAPE THE TWO SHARE is exactly [UserHeap.uarg]: a pointer, a       *)
(* length and a byte function per argument.  The vector is a [list uarg], *)
(* and [SpecSysExec]'s function spelling [(na, alen, afun)] is that list  *)
(* read at its indices ([ua_alen] / [ua_afun]).  Nothing is invented: the *)
(* U tier already owns argv this way ([UserHeap.uargv], which /cat's and  *)
(* /echo's own mains walk, and which sh's command node hands out at       *)
(* [UkShRun.ush_cmd_exec]); what was missing is the bridge from it to the *)
(* kernel's reading.                                                     *)
(*                                                                       *)
(* FOUR LAYERS, and each is used by a different caller:                   *)
(*                                                                       *)
(*  1. THE PURE LAYOUT [uargv_img M av args] -- the image holds this      *)
(*     vector at this address -- with [uargv_shape args], the decidable   *)
(*     facts about the vector itself (below MAXARG, non-null pointers,    *)
(*     NUL-terminated strings under a page).  [exec_args_of_uargv_img]    *)
(*     turns the pair into the kernel's reading.  A program with a        *)
(*     CONSTANT image (/init) supplies both by [vm_compute] and stops     *)
(*     here.                                                             *)
(*                                                                       *)
(*  2. THE AGREEMENT [exec_args_of_agree]: two readings of ONE image at   *)
(*     ONE address agree, on the count, the lengths and the bytes each    *)
(*     length admits.  This is the lemma section 1's second ruling named  *)
(*     as EX-3's "bigger prize", and it is what makes the layout layer    *)
(*     enough: a program does not have to show that the vector the kernel *)
(*     quantified over IS its own, only that ITS OWN is a reading.        *)
(*     [uargv_det] is (1) and (2) composed, and it is what both program   *)
(*     instances now are.                                                *)
(*                                                                       *)
(*  3. THE RESOURCE [uargv_exec]: [UserHeap.uargv] together with the NULL *)
(*     cap word and the shape -- i.e. sh's own [ush_cmd_exec] output.     *)
(*     [uargv_img_of_uargv] reads the layout off the heap the exec        *)
(*     deposit lends ([UkRun.udepw_at]), and it is PURE, so the heap      *)
(*     survives it.  A program whose vector is malloc'd (/sh) enters      *)
(*     here.  The path is the same story one argument over and needs no   *)
(*     new resource at all: a path IS a [UserHeap.ustr] whose byte        *)
(*     function is the list ([upath]), because [ustr]'s own no-interior-  *)
(*     NUL clause and length bound ARE [ArgPath.arg_path_shape].          *)
(*                                                                       *)
(*  4. THE LIFT [image_entry_of_at_reading]: with (2) in hand, a program  *)
(*     that proved its entry at ONE argument shape has it at every shape  *)
(*     the caller's image admits -- [ExecEntry.image_entry_of_at]'s       *)
(*     premise discharged from a single reading rather than at every      *)
(*     vector.  The step needs [kexec_image_ok] to be EXTENSIONAL in      *)
(*     [alen] below the count and in [afun] below each length, which it   *)
(*     is ([kexec_image_ok_ext]) -- every occurrence is under one of      *)
(*     those two binders, [kxc_sp]'s recursion included.                  *)
(*                                                                       *)
(* WHY THE RANGE BOUNDS ARE ALMOST FREE (a finding).  Section 4 priced    *)
(* the lemma with "the two range bounds EX-4 named" -- echo's             *)
(* [0 < t < 2 ^ 38] and [0 < s0 + off i < 2 ^ 38].  Only the POSITIVITY   *)
(* of a pointer is really owed: it is what refutes the reading in which   *)
(* argv[i] is itself the NULL terminator, and no heap fact implies it.    *)
(* Every one of the UPPER bounds, by contrast, comes straight off         *)
(* [UserHeap.uheap]'s own canonicity clause (every mapped user address is *)
(* below MAXVA), so on the resource route the caller supplies none of     *)
(* them, and the pure layout asks only for the [< 2 ^ 64] that keeps the  *)
(* machine's own [add_vec_int] indexing from wrapping.                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto RiscvExtras.
Require Import UmodeArith.      (* [Z64], [uint_moi], [moi_small]        *)
Require Import UmodeAbi.        (* [ubyte0], [uimg_sub]                  *)
Require Import ByteBuf.         (* [bb_cstr] / [bb_nonul]                *)
Require Import SpecCopyin.      (* [uimg_word_at]                        *)
Require Import UImgWordDefs.    (* [img_word_of_bytes], [uimg_word_det]  *)
Require Import KexecDefs.       (* [MAXARG], [kxc_sp], [kxc_sp_final],
                                   [kxc_stack_ok]                        *)
Require Import ElfFile.         (* [elf_bytes]                           *)
Require Import FdSlots.         (* [fdstate]                             *)
Require Import UexecSlot.       (* [uvis]                                *)
Require Import SpecKexec.       (* [kexec_image_ok] and its pieces       *)
Require Import SpecSysExec.     (* [exec_args_of] / [exec_path_of]       *)
Require Import ExecEntry.       (* [image_entry] / [image_entry_at]      *)
Require Import ChildTok.        (* [ctokG]: the lift's only ghost class  *)
Require Import UserFd.          (* [ufdG]                                *)
Require Import UserPerm.        (* [uperm]: the heap's permission view    *)
Require Import UserHeap.        (* [uarg], [uargv], [ustr], [uheap]      *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  TWO SPELLINGS OF ONE VECTOR                                       *)
(* ===================================================================== *)

(* [SpecSysExec]'s reading is stated at FUNCTIONS [(alen, afun)] because
   that is what the kernel's copy loop hands back; the U tier owns a
   vector as a LIST of [uarg]s because that is what a program indexes.
   These three turn the list into the functions, and nothing below ever
   converts the other way. *)
Definition ua_none : uarg := UArg 0 0%nat (fun _ => ubyte0).

Definition ua_nth (args : list uarg) (i : nat) : uarg :=
  default ua_none (args !! i).

Definition ua_alen (args : list uarg) (i : nat) : nat := ua_len (ua_nth args i).
Definition ua_afun (args : list uarg) (i j : nat) : bv 8 :=
  ua_bytes (ua_nth args i) j.

Lemma ua_nth_lookup (args : list uarg) (i : nat) (x : uarg) :
  args !! i = Some x -> ua_nth args i = x.
Proof. intro H. rewrite /ua_nth H. reflexivity. Qed.

Lemma ua_lookup_lt (args : list uarg) (i : nat) :
  (i < length args)%nat -> args !! i = Some (ua_nth args i).
Proof.
  intro Hi. destruct (lookup_lt_is_Some_2 args i Hi) as [x Hx].
  rewrite (ua_nth_lookup args i x Hx). exact Hx.
Qed.

(* ===================================================================== *)
(*  1.  THE PURE LAYOUT                                                   *)
(* ===================================================================== *)

(* WHAT THE VECTOR IS, decidably: fewer arguments than the kernel accepts,
   no NULL pointer among them (that is the terminator's job and nothing
   else's), each string NUL-terminated ([bb_cstr]) and shorter than a
   page.  These are [SpecSysExec.exec_args_shape] plus the one fact no
   heap can supply. *)
Definition uargv_shape (args : list uarg) : Prop :=
  (length args < MAXARG)%nat
  /\ (forall (i : nat) (x : uarg), args !! i = Some x ->
        0 < ua_ptr x
        /\ Z.of_nat (ua_len x) < 4096
        /\ bb_cstr (ua_bytes x) (ua_len x)).

(* WHERE THE VECTOR IS, in the image: argument [i]'s pointer word at
   [av + 8i], the NULL cap at [av + 8 * length args], and each string's
   bytes AND its terminator at [ua_ptr] ([j <= ua_len], one clause, the
   spelling [SpecCopyinstr.copyinstr_got] takes).  The two [< Z64] rows
   are what keeps the machine's own [add_vec_int] indexing from wrapping;
   see the header on why nothing tighter is asked. *)
Definition uargv_img (M : gmap Z (bv 8)) (av : Z) (args : list uarg) : Prop :=
  0 <= av
  /\ av + 8 * Z.of_nat (length args) + 8 <= Z64
  /\ (forall (i : nat) (x : uarg), args !! i = Some x ->
        ua_ptr x + Z.of_nat (ua_len x) < Z64)
  /\ (forall (i : nat) (x : uarg), args !! i = Some x ->
        forall k : nat, (k < 8)%nat ->
          M !! (av + 8 * Z.of_nat i + Z.of_nat k)
          = bv_to_little_endian 8 8 (ua_ptr x) !! k)
  /\ (forall k : nat, (k < 8)%nat ->
        M !! (av + 8 * Z.of_nat (length args) + Z.of_nat k)
        = bv_to_little_endian 8 8 0 !! k)
  /\ (forall (i : nat) (x : uarg), args !! i = Some x ->
        forall j : nat, (j <= ua_len x)%nat ->
          M !! (ua_ptr x + Z.of_nat j) = Some (ua_bytes x j)).

(* ---- the address arithmetic, once ------------------------------------ *)
(* [UkRunLeaf.uv_avi_pos] is this fact about a word; it is re-proved here
   rather than imported because that file is the whole leaf tier and this
   one is three definitions.  Both are [UmodeAbi.uv_avi_neg]'s body with
   the sign flipped. *)
Lemma ua_avi_pos (a : mword 64) (d : Z) :
  0 <= d -> bv_unsigned a + d < Z64 ->
  bv_unsigned (add_vec_int a d) = bv_unsigned a + d.
Proof.
  intros Hd Hlt. unfold add_vec_int.
  rewrite add_vec64_unsigned moi64_unsigned.
  unfold bv_wrap.
  assert (E64 : bv_modulus 64 = 18446744073709551616)
    by (vm_compute; reflexivity).
  rewrite E64. rewrite Zplus_mod_idemp_r. apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ a) as Hr. rewrite E64 in Hr.
  unfold Z64 in Hlt. lia.
Qed.

Lemma ua_uint_avi_moi (a d : Z) :
  0 <= a -> 0 <= d -> a + d < Z64 ->
  uint (add_vec_int (mword_of_int a : mword 64) d) = a + d.
Proof.
  intros Ha Hd Had.
  assert (Hb : bv_unsigned (mword_of_int a : mword 64) = a)
    by (apply moi_small; unfold Z64 in *; lia).
  rewrite uint_unsigned.
  rewrite (ua_avi_pos (mword_of_int a : mword 64) d Hd
             ltac:(rewrite Hb; exact Had)).
  rewrite Hb. reflexivity.
Qed.

Lemma ua_ubyte0_moi0 : ubyte0 = (mword_of_int 0 : mword 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ua_ubyte0_bv0 : ubyte0 = (bv_0 8 : bv 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- THE READING ----------------------------------------------------- *)

(* THE VECTOR A CALLER LAID OUT IS A VECTOR sys_exec READS.  Every
   conjunct of [exec_args_of] is one row of the layout, at the machine's
   own index; the [avf] witness is the pointer list capped by the NULL,
   which is what the layout's last word says the image holds. *)
Lemma exec_args_of_uargv_img (M : gmap Z (bv 8)) (av : Z) (args : list uarg) :
  uargv_shape args -> uargv_img M av args ->
  exec_args_of M (mword_of_int av : mword 64)
    (length args) (ua_alen args) (ua_afun args).
Proof.
  intros (Hmax & Hsh) (Hav0 & Havhi & Hphi & Hword & Hcap & Hstr).
  (* every index below the count has its element *)
  assert (Hel : forall i : nat, (i < length args)%nat ->
            args !! i = Some (ua_nth args i))
    by (intros i Hi; exact (ua_lookup_lt args i Hi)).
  (* the pointer words' addresses do not wrap *)
  assert (Ea : forall i : nat, (i <= length args)%nat ->
            uint (add_vec_int (mword_of_int av : mword 64) (8 * Z.of_nat i))
            = av + 8 * Z.of_nat i).
  { intros i Hi. apply ua_uint_avi_moi; [ exact Hav0 | lia | ].
    unfold Z64 in *. lia. }
  (* ...and neither does any string's *)
  assert (Ep : forall (i j : nat), (i < length args)%nat ->
            (j <= ua_alen args i)%nat ->
            uint (add_vec_int (mword_of_int (ua_ptr (ua_nth args i)) : mword 64)
                    (Z.of_nat j))
            = ua_ptr (ua_nth args i) + Z.of_nat j).
  { intros i j Hi Hj.
    destruct (Hsh i _ (Hel i Hi)) as (Hpos & _ & _).
    pose proof (Hphi i _ (Hel i Hi)) as Hhi.
    apply ua_uint_avi_moi; [ lia | lia | rewrite /ua_alen in Hj; lia ]. }
  split.
  { (* ---- THE SHAPE ---- *)
    split_and!.
    - exact Hmax.
    - intros i Hi. rewrite /ua_afun /ua_alen.
      exact (proj2 (proj2 (Hsh i _ (Hel i Hi)))).
    - intros i Hi. rewrite /ua_alen.
      exact (proj1 (proj2 (Hsh i _ (Hel i Hi)))). }
  (* ---- THE POINTERS ---- *)
  exists (fun i : nat =>
            (mword_of_int (if decide (i < length args)%nat
                           then ua_ptr (ua_nth args i) else 0) : mword 64)).
  split_and!.
  - intros i Hi. rewrite (Ea i Hi).
    destruct (decide (i < length args)%nat) as [Hlt | Hge].
    + destruct (Hsh i _ (Hel i Hlt)) as (Hpos & _ & _).
      pose proof (Hphi i _ (Hel i Hlt)) as Hhi.
      intros k Hk.
      rewrite (moi_small (ua_ptr (ua_nth args i)) ltac:(unfold Z64 in *; lia)).
      exact (Hword i _ (Hel i Hlt) k Hk).
    + assert (Hi2 : i = length args) by lia. subst i.
      intros k Hk.
      rewrite (moi_small 0 ltac:(unfold Z64; lia)).
      exact (Hcap k Hk).
  - intros i Hi.
    destruct (decide (i < length args)%nat) as [_ | Hge]; [ | exfalso; lia ].
    destruct (Hsh i _ (Hel i Hi)) as (Hpos & _ & _).
    pose proof (Hphi i _ (Hel i Hi)) as Hhi.
    intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite (moi_small (ua_ptr (ua_nth args i)) ltac:(unfold Z64 in *; lia)) in Hc.
    rewrite (moi_small 0 ltac:(unfold Z64; lia)) in Hc. lia.
  - destruct (decide (length args < length args)%nat) as [Hc | _];
      [ exfalso; lia | reflexivity ].
  - intros i Hi j Hj.
    destruct (decide (i < length args)%nat) as [_ | Hge]; [ | exfalso; lia ].
    rewrite (Ep i j Hi Hj).
    rewrite /ua_afun.
    exact (Hstr i _ (Hel i Hi) j ltac:(rewrite /ua_alen in Hj; lia)).
Qed.

(* ===================================================================== *)
(*  2.  THE AGREEMENT                                                     *)
(* ===================================================================== *)

(* eight image bytes pin the word they encode, in the form that needs no
   candidate value: [UImgWordDefs.uimg_word_det] at the second word's own
   unsigned reading *)
Lemma uimg_word_agree (M : gmap Z (bv 8)) (a : Z) (w1 w2 : mword 64) :
  uimg_word_at M a w1 -> uimg_word_at M a w2 -> w1 = w2.
Proof.
  intros H1 H2.
  pose proof (bv_unsigned_in_range _ w2) as Hr.
  assert (E64 : bv_modulus 64 = 18446744073709551616)
    by (vm_compute; reflexivity).
  rewrite E64 in Hr.
  rewrite (uimg_word_det M a w1 (bv_unsigned w2)
             ltac:(change (2 ^ 64) with 18446744073709551616; lia) H1 H2).
  apply bv_eq. rewrite moi64_unsigned. unfold bv_wrap. rewrite E64.
  apply Z.mod_small. lia.
Qed.

(* TWO READINGS OF ONE IMAGE AT ONE ADDRESS AGREE.  This is what makes the
   entry's [∀ na alen afun] harmless: the kernel quantifies the vector it
   built, the caller knows the vector it laid out, and there is only one.
   The conclusion is stated on the INDICES THAT MATTER -- the count, the
   lengths below it, and each string's bytes up to and including its
   terminator -- because nothing else is determined and nothing else is
   read ([kexec_image_ok] touches no more; see [kexec_image_ok_ext]). *)
Lemma exec_args_of_agree (M : gmap Z (bv 8)) (av : mword 64)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
    (na' : nat) (alen' : nat -> nat) (afun' : nat -> nat -> bv 8) :
  exec_args_of M av na alen afun ->
  exec_args_of M av na' alen' afun' ->
  na = na'
  /\ (forall i : nat, (i < na)%nat -> alen i = alen' i)
  /\ (forall i j : nat, (i < na)%nat -> (j <= alen i)%nat ->
        afun i j = afun' i j).
Proof.
  intros (Hs & avf & Hptr & Hnz & Hnul & Hstr)
         (Hs' & avf' & Hptr' & Hnz' & Hnul' & Hstr').
  destruct Hs as (_ & Hcstr & _). destruct Hs' as (_ & Hcstr' & _).
  (* the two pointer vectors agree wherever both are defined *)
  assert (Hag : forall i : nat, (i <= na)%nat -> (i <= na')%nat ->
            avf i = avf' i)
    by (intros i Hi Hi'; exact (uimg_word_agree M _ _ _ (Hptr i Hi) (Hptr' i Hi'))).
  (* ---- THE COUNT: the shorter vector's terminator is the longer one's
     non-null pointer ---- *)
  assert (Hcut : forall (n1 n2 : nat) (f1 f2 : nat -> mword 64),
             (forall i, (i <= n1)%nat -> (i <= n2)%nat -> f1 i = f2 i) ->
             f1 n1 = (mword_of_int 0 : mword 64) ->
             (forall i, (i < n2)%nat -> f2 i <> (mword_of_int 0 : mword 64)) ->
             (n2 <= n1)%nat).
  { intros n1 n2 f1 f2 Hagr Hz Hnn.
    destruct (decide (n2 <= n1)%nat) as [Hle | Hgt]; [ exact Hle | exfalso ].
    apply (Hnn n1 ltac:(lia)). rewrite <- (Hagr n1 ltac:(lia) ltac:(lia)).
    exact Hz. }
  assert (Hna : na = na').
  { pose proof (Hcut na na' avf avf' Hag Hnul Hnz') as H1.
    pose proof (Hcut na' na avf' avf
                  ltac:(intros i Hi Hi'; exact (eq_sym (Hag i Hi' Hi)))
                  Hnul' Hnz) as H2.
    lia. }
  subst na'.
  split; [ reflexivity | ].
  (* ---- THE LENGTHS: the shorter string's terminator is an interior byte
     of the longer one ---- *)
  assert (Hlen : forall i : nat, (i < na)%nat -> alen i = alen' i).
  { intros i Hi.
    pose proof (Hag i ltac:(lia) ltac:(lia)) as Hai.
    pose proof (Hstr i Hi) as Hg. pose proof (Hstr' i Hi) as Hg'.
    rewrite <- Hai in Hg'.
    destruct (Hcstr i Hi) as [Hno Hnl].
    destruct (Hcstr' i Hi) as [Hno' Hnl'].
    assert (Hcut2 : forall (k1 k2 : nat) (g1 g2 : nat -> bv 8),
               (forall j, (j <= k1)%nat ->
                  M !! uint (add_vec_int (avf i) (Z.of_nat j)) = Some (g1 j)) ->
               (forall j, (j <= k2)%nat ->
                  M !! uint (add_vec_int (avf i) (Z.of_nat j)) = Some (g2 j)) ->
               g1 k1 = (mword_of_int 0 : mword 8) ->
               bb_nonul g2 k2 -> (k2 <= k1)%nat).
    { intros k1 k2 g1 g2 Hd1 Hd2 Hz2 Hnn.
      destruct (decide (k2 <= k1)%nat) as [Hle | Hgt]; [ exact Hle | exfalso ].
      pose proof (Hd1 k1 ltac:(lia)) as Ha1.
      pose proof (Hd2 k1 ltac:(lia)) as Ha2.
      rewrite Ha1 in Ha2. injection Ha2 as Ha2.
      exact (Hnn k1 ltac:(lia) (eq_trans (eq_sym Ha2) Hz2)). }
    pose proof (Hcut2 (alen i) (alen' i) (afun i) (afun' i) Hg Hg' Hnl Hno') as L1.
    pose proof (Hcut2 (alen' i) (alen i) (afun' i) (afun i) Hg' Hg Hnl' Hno) as L2.
    lia. }
  split; [ exact Hlen | ].
  (* ---- ...AND THE BYTES ---- *)
  intros i j Hi Hj.
  pose proof (Hag i ltac:(lia) ltac:(lia)) as Hai.
  pose proof (Hstr i Hi j Hj) as Hb.
  pose proof (Hstr' i Hi j ltac:(rewrite <- (Hlen i Hi); lia)) as Hb'.
  rewrite <- Hai in Hb'. rewrite Hb in Hb'. injection Hb' as Hb'.
  exact Hb'.
Qed.

(* (1) AND (2) COMPOSED: the layout DETERMINES every reading of it.  Both
   program instances are this lemma and a projection. *)
Lemma uargv_det (M : gmap Z (bv 8)) (av : Z) (args : list uarg)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
  uargv_shape args -> uargv_img M av args ->
  exec_args_of M (mword_of_int av : mword 64) na alen afun ->
  na = length args
  /\ (forall i : nat, (i < na)%nat -> alen i = ua_alen args i)
  /\ (forall i j : nat, (i < na)%nat -> (j <= alen i)%nat ->
        afun i j = ua_afun args i j).
Proof.
  intros Hsh Himg Hargs.
  exact (exec_args_of_agree M (mword_of_int av : mword 64) na alen afun
           (length args) (ua_alen args) (ua_afun args) Hargs
           (exec_args_of_uargv_img M av args Hsh Himg)).
Qed.

(* ===================================================================== *)
(*  3.  THE RESOURCE                                                      *)
(* ===================================================================== *)

Section ExecArgsHeap.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{!ghost_varG Σ Z}.

  (* ------------------------------------------------------------------ *)
  (*  3a.  READING A RUN OFF THE HEAP                                     *)
  (* ------------------------------------------------------------------ *)

  (* [UserHeap.uheap_ubytes_img] at ANY dfrac.  An argv node's runs are
     all [DfracDiscarded] -- that is what makes sh's command tree
     persistent and lets it cross a fork -- so the owned-run form cannot
     read them.  (Was [UShEcho]'s; it belongs where [uargv] is read.) *)
  Lemma uheap_ubytesq_img (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    uheap gt gd gs M pm sz -∗ ubytesq gd dq a n f -∗
    ⌜ forall k : nat, (k < n)%nat -> M !! (a + Z.of_nat k)%Z = Some (f k) ⌝.
  Proof using .
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

  (* ...AND ITS RANGE.  [uheap]'s canonicity clause is what makes every
     upper bound of section 1 free (the header): an owned address is
     below MAXVA, so no run a program holds can wrap. *)
  Lemma uheap_ubytesq_range (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    uheap gt gd gs M pm sz -∗ ubytesq gd dq a n f -∗
    ⌜ forall k : nat, (k < n)%nat -> 0 <= a + Z.of_nat k < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hheap Hbs".
    iInduction n as [ | k IH ] "IH" forall (f).
    { iPureIntro. intros j Hj. exfalso. lia. }
    rewrite /ubytesq seq_S big_sepL_app /=.
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    iDestruct ("IH" $! f with "Hheap Hlo") as %Hlo.
    iDestruct (uheap_ubyte with "Hheap Hhi") as %(_ & _ & HR).
    iPureIntro. intros j Hj.
    destruct (decide (j = k)) as [-> | Hne];
      [ exact HR | exact (Hlo j ltac:(lia)) ].
  Qed.

  (* ...and the word form, in the spelling [SpecCopyin.uimg_word_at] and
     [UImgWordDefs.img_word_of_bytes] take. *)
  Lemma uheap_uwordq_img (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a z : Z) :
    uheap gt gd gs M pm sz -∗
    uwordq gd dq a (mword_of_int z : mword 64) -∗
    ⌜ forall k : nat, (k < 8)%nat ->
        M !! (a + Z.of_nat k)%Z = bv_to_little_endian 8 8 z !! k ⌝.
  Proof using .
    iIntros "Hheap Hw". rewrite /uwordq.
    iDestruct (uheap_ubytesq_img with "Hheap Hw") as %Hb.
    iPureIntro. exact (img_word_of_bytes M a z Hb).
  Qed.

  Lemma uheap_uwordq_range (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (w : mword 64) :
    uheap gt gd gs M pm sz -∗ uwordq gd dq a w -∗
    ⌜ 0 <= a /\ a + 8 <= 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hheap Hw". rewrite /uwordq.
    iDestruct (uheap_ubytesq_range with "Hheap Hw") as %Hr.
    iPureIntro.
    pose proof (Hr 0%nat ltac:(lia)) as H0.
    pose proof (Hr 7%nat ltac:(lia)) as H7.
    cbn in H0, H7. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3b.  THE ARGUMENT VECTOR AS A RESOURCE                              *)
  (* ------------------------------------------------------------------ *)

  (* [UserHeap.uargv] IS the vector -- the pointer array paired with the
     string each element names -- and it is already what sh's command node
     hands out ([UkShRun.ush_cmd_exec]) and what /cat's and /echo's mains
     walk.  Two things it does not carry, because a program that only
     WALKS argv does not need them and a program that PASSES it to exec
     does: the NULL cap word past the last element (argv[argc] = 0, which
     is what pins the count), and [uargv_shape] (which pins each string's
     terminator INSIDE the byte function, where [bb_cstr] wants it, rather
     than only in the image). *)
  Definition uargv_exec (γd : gname) (av : Z) (args : list uarg) : iProp Σ :=
    (⌜ uargv_shape args ⌝ ∗
     uargv γd av args ∗
     uwordq γd DfracDiscarded (av + 8 * Z.of_nat (length args))
       (mword_of_int 0))%I.

  Global Instance uargv_exec_persistent γd av args :
    Persistent (uargv_exec γd av args).
  Proof using . rewrite /uargv_exec. apply _. Qed.

  (* THE LAYOUT, READ OFF THE HEAP THE DEPOSIT LENDS.  PURE, and it has to
     be: the reading is consumed inside a persistent constructor that
     cannot hold the heap ([UkRun.udepw_at]'s loan is why the authorities
     travel at all).  Every range row comes from [uheap]'s canonicity, so
     the caller supplies none. *)
  Lemma uargv_img_of_uargv (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz av : Z) (args : list uarg) :
    uheap gt gd gs M pm sz -∗ uargv_exec gd av args -∗
    ⌜ uargv_img M av args ⌝.
  Proof using .
    iIntros "Hheap (%Hsh & #Hargv & #Hcap)".
    destruct Hsh as (Hmax & Hsh).
    iDestruct (uheap_uwordq_img with "Hheap Hcap") as %Hcapb.
    iDestruct (uheap_uwordq_range with "Hheap Hcap") as %[Hc0 Hc8].
    (* the BASE is in range too, and that reading is where the vector's
       own shape shows: the cap word sits at [av + 8 * length args], so at
       an empty vector it IS the base, and otherwise argument 0's own word
       is. *)
    iAssert (⌜ 0 <= av ⌝)%I as %Hav0.
    { destruct args as [| x0 args'].
      - iPureIntro. cbn in Hc0. lia.
      - iDestruct (uargv_acc gd av (x0 :: args') 0%nat x0 eq_refl with "Hargv")
          as "[[#Hw0 _] _]".
        iDestruct (uheap_uwordq_range with "Hheap Hw0") as %[H0 _].
        iPureIntro. lia. }
    (* the per-element rows, one index at a time: everything in sight is
       persistent, so the heap is read once per row and survives *)
    iAssert (⌜ forall (i : nat) (x : uarg), args !! i = Some x ->
               ua_ptr x + Z.of_nat (ua_len x) < Z64
               /\ (forall k : nat, (k < 8)%nat ->
                     M !! (av + 8 * Z.of_nat i + Z.of_nat k)%Z
                     = bv_to_little_endian 8 8 (ua_ptr x) !! k)
               /\ (forall j : nat, (j <= ua_len x)%nat ->
                     M !! (ua_ptr x + Z.of_nat j)%Z = Some (ua_bytes x j)) ⌝)%I
      as %Hrow.
    { iIntros (i x Hi).
      iDestruct (uargv_acc gd av args i x Hi with "Hargv") as "[[#Hw #Hs] _]".
      iDestruct (uheap_uwordq_img with "Hheap Hw") as %Hwb.
      rewrite /ustr. iDestruct "Hs" as "(_ & _ & #Hbs & #Hnul)".
      iDestruct (uheap_ubytesq_img with "Hheap Hbs") as %Hbv.
      iDestruct (uheap_ubyte with "Hheap Hnul") as %(Hnv & _ & Hnr).
      iPureIntro.
      change (2 ^ 38) with 274877906944 in Hnr.
      split_and!.
      - unfold Z64. lia.
      - exact Hwb.
      - intros j Hj.
        destruct (decide (j = ua_len x)) as [-> | Hne].
        + rewrite Hnv. f_equal.
          rewrite ua_ubyte0_moi0.
          exact (eq_sym (proj2 (proj2 (proj2 (Hsh i x Hi))))).
        + exact (Hbv j ltac:(lia)). }
    iPureIntro. rewrite /uargv_img.
    change (2 ^ 38) with 274877906944 in Hc0, Hc8.
    split_and!.
    - exact Hav0.
    - unfold Z64. lia.
    - intros i x Hi. exact (proj1 (Hrow i x Hi)).
    - intros i x Hi. exact (proj1 (proj2 (Hrow i x Hi))).
    - exact Hcapb.
    - intros i x Hi. exact (proj2 (proj2 (Hrow i x Hi))).
  Qed.

  (* THE READING, end to end: what a program that OWNS its argument vector
     hands the entry. *)
  Lemma exec_args_of_uargv (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz av : Z) (args : list uarg) :
    uheap gt gd gs M pm sz -∗ uargv_exec gd av args -∗
    ⌜ exec_args_of M (mword_of_int av : mword 64)
        (length args) (ua_alen args) (ua_afun args) ⌝.
  Proof using .
    iIntros "Hheap #Hv".
    iDestruct (uargv_img_of_uargv with "Hheap Hv") as %Himg.
    iDestruct "Hv" as "(%Hsh & _ & _)".
    iPureIntro. exact (exec_args_of_uargv_img M av args Hsh Himg).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3c.  THE PATH, THE SAME STORY ONE ARGUMENT OVER                     *)
  (* ------------------------------------------------------------------ *)

  (* AND IT NEEDS NO NEW RESOURCE.  [UserHeap.ustr]'s two pure clauses --
     no interior NUL, length representable -- ARE [ArgPath.arg_path_shape],
     and its two runs are the bytes and the terminator [arg_path_of] asks
     the image for.  So a path a program owns IS a [ustr] whose byte
     function is the list. *)
  Definition upath (γd : gname) (dq : dfrac) (pa : Z)
      (pl : list (bv 8)) : iProp Σ :=
    ustr γd dq pa (length pl) (fun j : nat => pl !!! j).

  Lemma exec_path_of_upath (gt gd gs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz pa : Z) (dq : dfrac)
      (pl : list (bv 8)) :
    uheap gt gd gs M pm sz -∗ upath gd dq pa pl -∗
    ⌜ exec_path_of M (mword_of_int pa : mword 64) pl ⌝.
  Proof using .
    iIntros "Hheap Hs". rewrite /upath /ustr.
    iDestruct "Hs" as "(%Hno & %Hlen & Hbs & Hnul)".
    iDestruct (uheap_ubytesq_img with "Hheap Hbs") as %Hbv.
    iDestruct (uheap_ubytesq_range with "Hheap Hbs") as %Hbr.
    iDestruct (uheap_ubyte with "Hheap Hnul") as %(Hnv & _ & Hnr).
    iPureIntro.
    change (2 ^ 38) with 274877906944 in Hnr.
    assert (Hpa0 : 0 <= pa).
    { destruct (decide (0 < length pl)%nat) as [Hne | Hz].
      - pose proof (Hbr 0%nat Hne) as H0. lia.
      - assert (Hl0 : length pl = 0%nat) by lia.
        rewrite Hl0 in Hnr. cbn in Hnr. lia. }
    assert (Ej : forall j : nat, (j <= length pl)%nat ->
              uint (add_vec_int (mword_of_int pa : mword 64) (Z.of_nat j)) = pa + Z.of_nat j)
      by (intros j Hj; apply ua_uint_avi_moi; [ lia | lia | unfold Z64; lia ]).
    split_and!.
    - split; [ exact Hlen | ].
      intros j b Hj.
      rewrite <- (list_lookup_total_correct _ _ _ Hj).
      rewrite <- ua_ubyte0_moi0.
      exact (Hno j (lookup_lt_Some _ _ _ Hj)).
    - intros j b Hj.
      rewrite (Ej j ltac:(pose proof (lookup_lt_Some _ _ _ Hj); lia)).
      rewrite (Hbv j (lookup_lt_Some _ _ _ Hj)).
      f_equal. exact (list_lookup_total_correct _ _ _ Hj).
    - rewrite (Ej (length pl) ltac:(lia)). rewrite Hnv.
      f_equal. exact ua_ubyte0_bv0.
  Qed.

End ExecArgsHeap.

(* ===================================================================== *)
(*  4.  THE LIFT: ONE READING DISCHARGES THE ENTRY AT EVERY SHAPE         *)
(* ===================================================================== *)

(* [kxc_sp top len i] reads [len] only BELOW [i], so two length functions
   that agree below the count give the same stack geometry. *)
Lemma kxc_sp_ext (top : Z) (len len' : nat -> nat) (n i : nat) :
  (forall k : nat, (k < n)%nat -> len k = len' k) -> (i <= n)%nat ->
  kxc_sp top len i = kxc_sp top len' i.
Proof.
  intro Hext. revert i. induction i as [| i IH]; intro Hi; [ reflexivity | ].
  cbn [kxc_sp]. rewrite (IH ltac:(lia)). rewrite (Hext i ltac:(lia)).
  reflexivity.
Qed.

Lemma kxc_sp_final_ext (top : Z) (len len' : nat -> nat) (n : nat) :
  (forall k : nat, (k < n)%nat -> len k = len' k) ->
  kxc_sp_final top len n = kxc_sp_final top len' n.
Proof.
  intro Hext. rewrite /kxc_sp_final (kxc_sp_ext top len len' n n Hext ltac:(lia)).
  reflexivity.
Qed.

Lemma kexec_ustack_ext (top : Z) (len len' : nat -> nat) (n i : nat) :
  (forall k : nat, (k < n)%nat -> len k = len' k) ->
  kexec_ustack top len n i = kexec_ustack top len' n i.
Proof.
  intro Hext. rewrite /kexec_ustack.
  destruct (decide (i < n)%nat) as [Hlt | Hge]; [ | reflexivity ].
  exact (kxc_sp_ext top len len' n (S i) Hext ltac:(lia)).
Qed.

Lemma kexec_arg_addr_ext (top : Z) (len len' : nat -> nat) (n : nat) (a : Z) :
  (forall k : nat, (k < n)%nat -> len k = len' k) ->
  kexec_arg_addr top len n a -> kexec_arg_addr top len' n a.
Proof.
  intro Hext. rewrite /kexec_arg_addr.
  rewrite (kxc_sp_final_ext top len len' n Hext).
  intros [[i [Hi Hrow]] | Hvec]; [ left | right; exact Hvec ].
  exists i. split; [ exact Hi | ].
  rewrite <- (kxc_sp_ext top len len' n (S i) Hext ltac:(lia)).
  rewrite <- (Hext i Hi). exact Hrow.
Qed.

(* WHAT THE KERNEL BUILT DEPENDS ON [alen] ONLY BELOW THE COUNT AND ON
   [afun] ONLY BELOW EACH LENGTH.  Every occurrence is under one of those
   two binders -- the geometry through [kxc_sp]'s recursion, the argument
   bytes through [kexec_args_at]'s two quantifiers -- so the reading's
   agreement (section 2) is exactly enough to move an entry between
   argument shapes.  This is EX-3's second prize, and it is what section 1
   named as the only way to lift [M] and [av] out of [image_entry]. *)
Lemma kexec_image_ok_ext (f : elf_bytes) (na : nat)
    (alen alen' : nat -> nat) (afun afun' : nat -> nat -> bv 8)
    (sts : list fdstate) (W' : uvis) :
  (forall i : nat, (i < na)%nat -> alen i = alen' i) ->
  (forall i j : nat, (i < na)%nat -> (j < alen i)%nat -> afun i j = afun' i j) ->
  kexec_image_ok f na alen afun sts W' ->
  kexec_image_ok f na alen' afun' sts W'.
Proof.
  intros Hlen Hfun.
  assert (Esp : forall i : nat, (i <= na)%nat ->
            kxc_sp (kexec_sz f) alen i = kxc_sp (kexec_sz f) alen' i)
    by (intros i Hi; exact (kxc_sp_ext (kexec_sz f) alen alen' na i Hlen Hi)).
  assert (Efin : kxc_sp_final (kexec_sz f) alen na
                 = kxc_sp_final (kexec_sz f) alen' na)
    by exact (kxc_sp_final_ext (kexec_sz f) alen alen' na Hlen).
  intros (He & Hsz & Hsp & Ha1 & Ha0 & Himg & Hargs & Hstk & Hperm & Hbelow
          & Hfd & Htf).
  rewrite /kexec_image_ok. cbv zeta.
  split_and!.
  - exact He.
  - exact Hsz.
  - rewrite <- Efin. exact Hsp.
  - rewrite <- Efin. exact Ha1.
  - exact Ha0.
  - exact Himg.
  - (* the argument block *)
    destruct Hargs as (Hb & Hn & Hv).
    split_and!.
    + intros i j Hi Hj.
      rewrite <- (Esp (S i) ltac:(lia)).
      rewrite <- (Hfun i j Hi ltac:(rewrite (Hlen i Hi); lia)).
      exact (Hb i j Hi ltac:(rewrite (Hlen i Hi); lia)).
    + intros i Hi.
      rewrite <- (Esp (S i) ltac:(lia)).
      rewrite <- (Hlen i Hi). exact (Hn i Hi).
    + intros i k Hi Hk.
      rewrite <- Efin.
      rewrite <- (kexec_ustack_ext (kexec_sz f) alen alen' na i Hlen).
      exact (Hv i k Hi Hk).
  - (* the stack page *)
    destruct Hstk as [Hok Hz]. split.
    + destruct Hok as [Hrow Hfin]. split.
      * intros i H1 H2. rewrite <- (Esp i H2). exact (Hrow i H1 H2).
      * rewrite <- Efin. exact Hfin.
    + intros a Ha Hna. apply Hz; [ exact Ha | ].
      intro Hc. apply Hna.
      exact (kexec_arg_addr_ext (kexec_sz f) alen alen' na a Hlen Hc).
  - exact Hperm.
  - exact Hbelow.
  - exact Hfd.
  - exact Htf.
Qed.

Section ExecArgsLift.
  Context `{!ctokG Σ}.

  (* THE PAYOFF.  [ExecEntry.image_entry_of_at] asks a program for its
     entry at EVERY argument shape the caller's image admits; with the
     agreement lemma there is only one such shape, so ONE reading is the
     whole premise.  A program proves [image_entry_at] from its code proof
     at the vector it laid out, reads that vector back off its own runs,
     and is done -- which is what section 1's second ruling (the argv
     reading is a premise the entry may consume) costs once general. *)
  Lemma image_entry_of_at_reading (f : elf_bytes) (M : gmap Z (bv 8))
      (av : mword 64) (sts : list fdstate) (cw : Z) (secc : mword 64) (cs : gset gname)
      (pidv : mword 32) (Q : Z -> iProp Σ) (Pay : iProp Σ)
      (X : uvis -d> iPropO Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
    exec_args_of M av na alen afun ->
    image_entry_at f na alen afun sts cw secc cs pidv Q Pay X -∗
    image_entry f M av sts cw secc cs pidv Q Pay X.
  Proof using .
    intros Hargs. iIntros "#H". rewrite /image_entry.
    iIntros "!>" (na' alen' afun' W')
      "%Hok %Hcw %Hlz %Hscw %Hch %Hpid %Hargs' Hp HPay".
    destruct (exec_args_of_agree M av na alen afun na' alen' afun'
                Hargs Hargs') as (Hn & Hl & Hb).
    subst na'.
    rewrite /image_entry_at.
    iApply ("H" $! W' with "[%] [%] [%] [%] [%] [%] Hp HPay");
      [ | exact Hcw | exact Hlz | exact Hscw | exact Hch | exact Hpid ].
    refine (kexec_image_ok_ext f na alen' alen afun' afun sts W'
              _ _ Hok).
    - intros i Hi. exact (eq_sym (Hl i Hi)).
    - intros i j Hi Hj.
      exact (eq_sym (Hb i j Hi ltac:(rewrite (Hl i Hi); lia))).
  Qed.

End ExecArgsLift.
