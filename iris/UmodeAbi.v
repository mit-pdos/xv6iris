(* UmodeAbi.v -- program-GENERIC user-space ABI vocabulary for the verified
   user-execution tier (claude-notes/projects/user-verified.md): the RISC-V
   ABI register indices contracts speak about, image inclusion, the call
   stack a gcc prologue carves its frames out of, readable byte windows,
   C strings, and the argc/argv area [exec()] hands a process.  Nothing
   here is about any particular program -- per-program facts live in
   UCode<Prog>.v / USpec<Prog>.v.

   Everything in this file is PURE (a [Prop] about the image [M] and the
   fixed user table [pt]); the Iris side is UmodeMem.v's [umem], which this
   file sits on for [uM_bytes] / [uva_canon] / [uva_fetch_leaf]. *)
From Stdlib Require Import ZArith Bool Lia Znumtheory.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import RegFile.
Require Import RiscvExtras.
Require Import UserBits.
Require Import UserPtTree.
Require Import UmodeMem UmodeFetch UmodeArith.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 ABI register indices.  (a7_idx, the syscall-number register, lives   *)
(* in UmodeCap.v because [uv_sys_wp] itself dispatches on it.)             *)
(* ===================================================================== *)

Definition ra_idx : mword 5 := mword_of_int 1.
Definition sp_idx : mword 5 := mword_of_int 2.
Definition a0_idx : mword 5 := mword_of_int 10.
Definition a1_idx : mword 5 := mword_of_int 11.
Definition a2_idx : mword 5 := mword_of_int 12.

(* ===================================================================== *)
(* §2 Image inclusion: program bytes [img] (a dumped [<prog>_bytes] /      *)
(* [<prog>_data]) present verbatim in a process image [M].                 *)
(* ===================================================================== *)

Definition uimg_sub (img M : gmap Z (bv 8)) : Prop :=
  forall (a : Z) (b : bv 8), img !! a = Some b -> M !! a = Some b.

Lemma uimg_sub_lookup (img M : gmap Z (bv 8)) (a : Z) (b : bv 8) :
  uimg_sub img M -> img !! a = Some b -> M !! a = Some b.
Proof. intros Hs Hl. exact (Hs a b Hl). Qed.

(* ===================================================================== *)
(* §3 THE CALL STACK.                                                      *)
(*                                                                         *)
(* [uv_stack pt M sp0 n] -- [n] bytes of usable stack BELOW [sp0]: present *)
(* in the image, on ONE mapped page the user may both load from and store  *)
(* to, 16-aligned at the top and 16-aligned in size.  Contents are         *)
(* deliberately unconstrained ([is_Some], not a value): a frame is         *)
(* scratch.                                                                *)
(*                                                                         *)
(* This is the verified tier's [StackOwn.stack_own] -- a BUDGET, not a     *)
(* frame.  A function's contract asks for its own frame PLUS everything    *)
(* its callees need, and [uv_stack_split] hands the callee its slice at    *)
(* the post-prologue sp.  There is no interrupt headroom to reserve: user  *)
(* traps run on the KERNEL stack, so unlike the kernel's [sie_cap] there   *)
(* is no carve and no [avail] accounting.                                  *)
(* ===================================================================== *)

Record uv_stack (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64) (n : Z)
    : Prop := UvStack {
  us_al    : Z.rem (uint sp0) 16 = 0;
  us_n0    : 0 <= n;
  us_n16   : Z.rem n 16 = 0;
  us_page  : Z.rem (uint sp0 - n) 4096 + n <= 4096;   (* the whole budget is
                                                         on one page *)
  us_lo    : 4096 <= uint sp0 - n;                    (* ... which is not page 0 *)
  us_canon : uint sp0 <= 2 ^ 38;                      (* Sv39-canonical, no wrap *)
  us_leaf  : 0 < n ->
             exists w : mword 64,
               ud_um pt !! svpn_of (add_vec_int sp0 (- n)) = Some w /\
               uleaf_ok (Store Data) w /\ uleaf_ok (Load Data) w;
  us_bytes : forall j : Z, 0 <= j < n ->
               exists b : bv 8, M !! (uint sp0 - n + j) = Some b
}.

(* a dom-preserving image update keeps every stack budget (contents are
   unconstrained, so only the KEYS matter) *)
Lemma uv_stack_dom (pt : uptd) (M M' : gmap Z (bv 8)) (sp0 : mword 64) (n : Z) :
  (forall a : Z, is_Some (M !! a) -> is_Some (M' !! a)) ->
  uv_stack pt M sp0 n -> uv_stack pt M' sp0 n.
Proof.
  intros Hdom [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  constructor; try assumption.
  intros j Hj. destruct (Hb j Hj) as [b HMb].
  destruct (Hdom (uint sp0 - n + j) (mk_is_Some _ _ HMb)) as [b' Hb'].
  eauto.
Qed.

(* ===================================================================== *)
(* §4 Readable byte windows and C strings.                                 *)
(*                                                                         *)
(* [uv_rd pt M a n] -- the [n] bytes from [a] are present in the image and *)
(* on pages the user may LOAD from.  The mapping is quantified PER BYTE    *)
(* rather than stated as one leaf, so a window may cross a page; an        *)
(* individual (naturally aligned) access never does, which is what the     *)
(* load leaf's own in-page premise needs.                                  *)
(* ===================================================================== *)

Record uv_rd (pt : uptd) (M : gmap Z (bv 8)) (a n : Z) : Prop := UvRd {
  urd_lo    : 0 <= a;
  urd_n0    : 0 <= n;
  urd_hi    : a + n <= 2 ^ 38;
  urd_leaf  : forall j : Z, 0 <= j < n ->
                exists w : mword 64,
                  ud_um pt !! svpn_of (mword_of_int (a + j) : mword 64) = Some w /\
                  uleaf_ok (Load Data) w;
  urd_bytes : forall j : Z, 0 <= j < n -> exists b : bv 8, M !! (a + j) = Some b
}.

(* a sub-window is readable *)
Lemma uv_rd_sub (pt : uptd) (M : gmap Z (bv 8)) (a n a' n' : Z) :
  uv_rd pt M a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  uv_rd pt M a' n'.
Proof.
  intros [Hlo Hn0 Hhi Hleaf Hb] Ha Hn' Hhi'.
  constructor; try lia.
  - intros j Hj. replace (a' + j) with (a + (a' - a + j)) by lia.
    apply Hleaf. lia.
  - intros j Hj. replace (a' + j) with (a + (a' - a + j)) by lia.
    apply Hb. lia.
Qed.

(* a dom-preserving image update keeps readability *)
Lemma uv_rd_dom (pt : uptd) (M M' : gmap Z (bv 8)) (a n : Z) :
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
  uv_rd pt M a n -> uv_rd pt M' a n.
Proof.
  intros Hdom [Hlo Hn0 Hhi Hleaf Hb]. constructor; try assumption.
  intros j Hj. destruct (Hb j Hj) as [b HMb].
  destruct (Hdom (a + j) (mk_is_Some _ _ HMb)) as [b' Hb']. eauto.
Qed.

(* the NUL byte, as the image spells one *)
Definition ubyte0 : bv 8 := Z_to_bv 8 0.

(* a NUL-terminated C string of length [len] at [a]: [len] non-NUL bytes
   followed by a NUL.  Says nothing about mapping -- pair it with
   [uv_rd pt M a (len+1)]. *)
Record ucstr (M : gmap Z (bv 8)) (a len : Z) : Prop := UCstr {
  ucs_len : 0 <= len;
  ucs_body : forall j : Z, 0 <= j < len ->
               exists b : bv 8, M !! (a + j) = Some b /\ b <> ubyte0;
  ucs_nul : M !! (a + len) = Some ubyte0
}.

(* an image update that leaves every byte at or above [lo] alone keeps a
   string that lives there (the shape every stack store below the argument
   area has) *)
Lemma ucstr_above (M M' : gmap Z (bv 8)) (a len lo : Z) :
  (forall k : Z, lo <= k -> M' !! k = M !! k) ->
  lo <= a -> ucstr M a len -> ucstr M' a len.
Proof.
  intros Heq Hlo [Hl Hb Hn]. constructor; [ exact Hl | | ].
  - intros j Hj. rewrite (Heq (a + j) ltac:(lia)). exact (Hb j Hj).
  - rewrite (Heq (a + len) ltac:(lia)). exact Hn.
Qed.

Lemma uv_rd_above (pt : uptd) (M M' : gmap Z (bv 8)) (a n lo : Z) :
  (forall k : Z, lo <= k -> M' !! k = M !! k) ->
  lo <= a -> uv_rd pt M a n -> uv_rd pt M' a n.
Proof.
  intros Heq Hlo [Hlo' Hn0 Hhi Hleaf Hb]. constructor; try assumption.
  intros j Hj. rewrite (Heq (a + j) ltac:(lia)). exact (Hb j Hj).
Qed.

(* ===================================================================== *)
(* §5 The argument area.                                                   *)
(*                                                                         *)
(* What [exec()] leaves for a process: [argc] in a0, and in a1 the address *)
(* of an [argc]-entry array of pointers, each pointing at a NUL-terminated *)
(* string.  Entry 0 is the program name, which is described like the rest. *)
(*                                                                         *)
(* Everything -- the array and every string -- is at or above [lo].  That  *)
(* single bound is what makes the whole area disjoint from the frames a    *)
(* program carves BELOW its entry sp, so a prologue's stores cannot        *)
(* invalidate it ([uargs_above]).  In the image [exec()] builds, [lo] is   *)
(* the entry sp.                                                           *)
(* ===================================================================== *)

Record uargs (pt : uptd) (M : gmap Z (bv 8)) (av argc lo : Z) : Prop := UArgs {
  ua_al   : Z.rem av 8 = 0;
  ua_lo   : lo <= av;
  ua_argc : 0 <= argc < 2 ^ 31;
  ua_rd   : uv_rd pt M av (8 * argc);
  ua_ptr  : forall i : Z, 0 <= i < argc ->
              exists p len : Z,
                uM_bytes M (av + 8 * i) 8 (mword_of_int p : mword 64) /\
                0 <= p /\ lo <= p /\ 0 <= len < 2 ^ 31 /\
                ucstr M p len /\ uv_rd pt M p (len + 1)
}.

Lemma uargs_above (pt : uptd) (M M' : gmap Z (bv 8)) (av argc lo : Z) :
  (forall k : Z, lo <= k -> M' !! k = M !! k) ->
  uargs pt M av argc lo -> uargs pt M' av argc lo.
Proof.
  intros Heq [Hal Hlo Hargc Hrd Hptr].
  constructor; try assumption.
  - exact (uv_rd_above pt M M' av (8 * argc) lo Heq Hlo Hrd).
  - intros i Hi. destruct (Hptr i Hi) as (p & len & Hp & Hp0 & Hplo & Hlen & Hs & Hr).
    exists p, len. split_and!.
    + intros j Hj. rewrite (Heq (av + 8 * i + Z.of_nat j) ltac:(lia)).
      exact (Hp j Hj).
    + exact Hp0.
    + exact Hplo.
    + lia.
    + lia.
    + exact (ucstr_above M M' p len lo Heq Hplo Hs).
    + exact (uv_rd_above pt M M' p (len + 1) lo Heq Hplo Hr).
Qed.

(* ===================================================================== *)
(* §6 THE STACK'S ARITHMETIC: splitting a budget, and one 8-byte slot.     *)
(*                                                                         *)
(* Every side condition a stack access needs is pure Z arithmetic on       *)
(* [uint sp0], and is derived here once rather than at each call site.     *)
(* ===================================================================== *)

(* a 16-aligned page offset leaves at least 4080-r room *)
Lemma uz_mod4096_of_mod16 (V r : Z) :
  0 <= V -> 0 <= r < 16 -> V mod 16 = r -> V mod 4096 <= 4080 + r.
Proof.
  intros HV Hr Hm.
  assert (Hd : (16 | 4096)) by (exists 256; reflexivity).
  pose proof (Znumtheory.Zmod_div_mod 16 4096 V ltac:(lia) ltac:(lia) Hd) as Hq.
  pose proof (Z.mod_pos_bound V 4096 ltac:(lia)) as Hb.
  pose proof (Z.div_mod (V mod 4096) 16 ltac:(lia)) as Hdm.
  rewrite <- Hq in Hdm. rewrite Hm in Hdm. lia.
Qed.

Lemma uz_canon_small (V : Z) :
  0 <= V < 274877906944 ->
  V = (((V mod 549755813888 + 274877906944) mod 549755813888) - 274877906944)
        mod 18446744073709551616.
Proof.
  intro HV.
  rewrite (Z.mod_small V 549755813888 ltac:(lia)).
  rewrite (Z.mod_small (V + 274877906944) 549755813888 ltac:(lia)).
  replace (V + 274877906944 - 274877906944) with V by lia.
  rewrite (Z.mod_small V 18446744073709551616 ltac:(lia)). reflexivity.
Qed.

Lemma uva_canon_small (a : mword 64) :
  bv_unsigned a < 274877906944 -> uva_canon a.
Proof.
  intro Hlt.
  pose proof (proj1 (bv_unsigned_in_range _ a)) as Hlo.
  apply uva_canon_unsigned.
  unfold bv_swrap, bv_wrap.
  assert (E39 : bv_modulus 39 = 549755813888) by (vm_compute; reflexivity).
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Eh39 : bv_half_modulus 39 = 274877906944) by (vm_compute; reflexivity).
  rewrite E39 E64 Eh39.
  exact (uz_canon_small (bv_unsigned a) (conj Hlo Hlt)).
Qed.

(* a NEGATIVE 64-bit displacement, as unsigned arithmetic *)
Lemma uv_avi_neg (a : mword 64) (d : Z) :
  0 <= d -> d <= bv_unsigned a ->
  bv_unsigned (add_vec_int a (- d)) = bv_unsigned a - d.
Proof.
  intros Hd Hle.
  unfold add_vec_int.
  rewrite add_vec64_unsigned moi64_unsigned.
  unfold bv_wrap.
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite E64.
  rewrite Zplus_mod_idemp_r.
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ a) as Hr. rewrite E64 in Hr. lia.
Qed.

Lemma uv_stack_uint_lo (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64) (n : Z) :
  uv_stack pt M sp0 n -> bv_unsigned (add_vec_int sp0 (- n)) = bv_unsigned sp0 - n.
Proof.
  intros [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  rewrite uint_unsigned in Hlo.
  exact (uv_avi_neg sp0 n Hn0 ltac:(lia)).
Qed.

(* ---- splitting a budget: the caller keeps [n1], the callee gets [n2] --
   [n] is taken as its OWN parameter with [n1 + n2 = n] as a premise, so a
   contract stating a literal budget (32, 80, 96) applies this directly and
   [lia] absorbs the arithmetic; demanding the budget be SPELLED [n1 + n2]
   costs every call site a contentless [replace]. *)
Lemma uv_stack_split (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64) (n n1 n2 : Z) :
  n1 + n2 = n ->
  0 <= n1 -> Z.rem n1 16 = 0 -> 0 <= n2 ->
  uv_stack pt M sp0 n ->
  uv_stack pt M sp0 n1 /\ uv_stack pt M (add_vec_int sp0 (- n1)) n2.
Proof.
  intros Hn Hn1 Hn1r Hn2 HS. subst n.
  pose proof HS as [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  rewrite !uint_unsigned in Hal, Hpg, Hlo, Hc, Hb.
  pose proof (proj1 (bv_unsigned_in_range _ sp0)) as Hsp0.
  rewrite Z.rem_mod_nonneg in Hal; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hn16; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hn1r; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hpg; [ | lia | lia ].
  assert (Hn2r : n2 mod 16 = 0).
  { replace n2 with ((n1 + n2) - n1) by lia.
    rewrite Zminus_mod Hn16 Hn1r. reflexivity. }
  assert (Hu1 : bv_unsigned (add_vec_int sp0 (- n1)) = bv_unsigned sp0 - n1)
    by (apply uv_avi_neg; lia).
  assert (Hu12 : bv_unsigned (add_vec_int sp0 (- (n1 + n2)))
                 = bv_unsigned sp0 - (n1 + n2))
    by (apply uv_avi_neg; lia).
  (* the two ways of naming the bottom of each half *)
  assert (Etop : add_vec_int (add_vec_int sp0 (- (n1 + n2))) n2
                 = add_vec_int sp0 (- n1)).
  { apply bv_eq.
    rewrite (uint_add_vec_int_small (add_vec_int sp0 (- (n1 + n2))) n2
               ltac:(lia) ltac:(rewrite Hu12; lia)).
    rewrite Hu12 Hu1. lia. }
  assert (Ebot : add_vec_int (add_vec_int sp0 (- n1)) (- n2)
                 = add_vec_int sp0 (- (n1 + n2))).
  { apply bv_eq.
    rewrite (uv_avi_neg (add_vec_int sp0 (- n1)) n2 ltac:(lia)
               ltac:(rewrite Hu1; lia)).
    rewrite Hu1 Hu12. lia. }
  (* the page bound at each half *)
  assert (Hmod : forall k : Z, 0 <= k -> k <= n1 + n2 ->
                   (bv_unsigned sp0 - k) mod 4096 + k <= 4096).
  { intros k Hk0 Hkn.
    pose proof (Z.mod_pos_bound (bv_unsigned sp0 - (n1 + n2)) 4096 ltac:(lia)) as Hb1.
    destruct (Z.eq_dec k 0) as [Hk | Hk].
    { subst k. pose proof (Z.mod_pos_bound (bv_unsigned sp0 - 0) 4096 ltac:(lia)). lia. }
    assert (He : bv_unsigned sp0 - k
                 = (bv_unsigned sp0 - (n1 + n2)) + ((n1 + n2) - k)) by lia.
    rewrite He.
    assert (Hsm : ((bv_unsigned sp0 - (n1 + n2)) + ((n1 + n2) - k)) mod 4096
                  = (bv_unsigned sp0 - (n1 + n2)) mod 4096 + ((n1 + n2) - k)).
    { rewrite <- Zplus_mod_idemp_l. apply Z.mod_small. lia. }
    rewrite Hsm. lia. }
  split.
  - constructor; rewrite ?uint_unsigned;
      try (rewrite Z.rem_mod_nonneg; [ | lia | lia ]); try lia.
    + exact (Hmod n1 ltac:(lia) ltac:(lia)).
    + intros Hpos.
      destruct (Hleaf ltac:(lia)) as (w & Hw & Hst & Hld).
      exists w. split_and!; try assumption.
      rewrite <- Hw. f_equal.
      rewrite <- Etop.
      apply (usvpn_window (add_vec_int sp0 (- (n1 + n2))) n2 ltac:(lia)).
      rewrite Hu12.
      pose proof (Z.mod_pos_bound (bv_unsigned sp0 - (n1 + n2)) 4096 ltac:(lia)). lia.
    + intros j Hj. replace (bv_unsigned sp0 - n1 + j)
        with (bv_unsigned sp0 - (n1 + n2) + (n2 + j)) by lia.
      apply Hb. lia.
  - constructor; rewrite ?uint_unsigned ?Hu1;
      try (rewrite Z.rem_mod_nonneg; [ | lia | lia ]); try lia.
    + rewrite Zminus_mod Hal Hn1r. reflexivity.
    + replace (bv_unsigned sp0 - n1 - n2) with (bv_unsigned sp0 - (n1 + n2)) by lia.
      pose proof (Hmod (n1 + n2) ltac:(lia) ltac:(lia)). lia.
    + intros Hpos.
      destruct (Hleaf ltac:(lia)) as (w & Hw & Hst & Hld).
      exists w. split_and!; try assumption.
      rewrite Ebot. exact Hw.
    + intros j Hj. replace (bv_unsigned sp0 - n1 - n2 + j)
        with (bv_unsigned sp0 - (n1 + n2) + j) by lia.
      apply Hb. lia.
Qed.

(* ---- ONE 8-byte slot: every side condition a load/store leaf needs ---- *)
Lemma uv_stack_slot (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64) (n d : Z) :
  uv_stack pt M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
  let tgt := add_vec_int (add_vec_int sp0 (- n)) d in
  uint tgt = uint sp0 - n + d /\
  (exists w : mword 64,
     ud_um pt !! svpn_of tgt = Some w /\
     uleaf_ok (Store Data) w /\ uleaf_ok (Load Data) w) /\
  uva_canon tgt /\
  Z.rem (uint tgt) 4096 <= 4088 /\
  is_aligned_vaddr (Virtaddr tgt) 8 = true /\
  (forall j : nat, (j < 8)%nat ->
     exists b : bv 8, M !! (uint tgt + Z.of_nat j) = Some b).
Proof.
  intros HS Hd0 Hdn Hd8 tgt.
  pose proof HS as [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  rewrite !uint_unsigned in Hal, Hpg, Hlo, Hc, Hb.
  pose proof (bv_unsigned_in_range _ sp0) as Hrng.
  assert (Em64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Em64 in Hrng.
  rewrite Z.rem_mod_nonneg in Hd8; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hpg; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hal; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hn16; [ | lia | lia ].
  assert (Hlow : bv_unsigned (add_vec_int sp0 (- n)) = bv_unsigned sp0 - n)
    by (apply uv_avi_neg; lia).
  assert (Htu : bv_unsigned tgt = bv_unsigned sp0 - n + d).
  { unfold tgt.
    rewrite (uint_add_vec_int_small (add_vec_int sp0 (- n)) d ltac:(lia)
               ltac:(rewrite Hlow; lia)).
    rewrite Hlow. reflexivity. }
  assert (Hpgd : (bv_unsigned sp0 - n) mod 4096 + d < 4096).
  { pose proof (Z.mod_pos_bound (bv_unsigned sp0 - n) 4096 ltac:(lia)). lia. }
  split_and!.
  - rewrite !uint_unsigned. exact Htu.
  - destruct (Hleaf ltac:(lia)) as (w & Hw & Hst & Hld). exists w.
    assert (Hv : svpn_of tgt = svpn_of (add_vec_int sp0 (- n))).
    { unfold tgt. apply (usvpn_window (add_vec_int sp0 (- n)) d ltac:(lia)).
      rewrite Hlow. exact Hpgd. }
    rewrite Hv. split_and!; assumption.
  - apply uva_canon_small. rewrite Htu. lia.
  - rewrite uint_unsigned Htu.
    rewrite Z.rem_mod_nonneg; [ | lia | lia ].
    assert (He : (bv_unsigned sp0 - n + d) mod 4096
                 = (bv_unsigned sp0 - n) mod 4096 + d).
    { rewrite <- Zplus_mod_idemp_l. apply Z.mod_small.
      pose proof (Z.mod_pos_bound (bv_unsigned sp0 - n) 4096 ltac:(lia)). lia. }
    rewrite He. lia.
  - unfold is_aligned_vaddr. apply Z.eqb_eq.
    cbn [bits_of_virtaddr]. rewrite uint_unsigned Htu.
    rewrite Z.rem_mod_nonneg; [ | lia | lia ].
    assert (Hsp8 : bv_unsigned sp0 mod 8 = 0).
    { assert (Hdv : (8 | 16)) by (exists 2; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 8 16 (bv_unsigned sp0) ltac:(lia) ltac:(lia) Hdv).
      rewrite Hal. reflexivity. }
    assert (Hn8 : n mod 8 = 0).
    { assert (Hdv : (8 | 16)) by (exists 2; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 8 16 n ltac:(lia) ltac:(lia) Hdv).
      rewrite Hn16. reflexivity. }
    rewrite Zplus_mod Zminus_mod Hsp8 Hn8 Hd8. reflexivity.
  - intros j Hj. rewrite uint_unsigned Htu.
    replace (bv_unsigned sp0 - n + d + Z.of_nat j)
      with (bv_unsigned sp0 - n + (d + Z.of_nat j)) by lia.
    apply Hb. lia.
Qed.

(* ===================================================================== *)
(* §7 WHAT A CALL LEAVES BEHIND.                                          *)
(*                                                                        *)
(* [uM_only M M' a n] -- [M'] is [M] with only the bytes in [a, a+n)       *)
(* possibly changed, and no key lost.  This is the whole postcondition a   *)
(* verified function needs to state about the IMAGE: a function writes     *)
(* nothing but the frames it carves below its entry sp, so [a, a+n) is the *)
(* contiguous stack range it and its callees own.  It composes             *)
(* ([uM_only_trans]), widens ([uM_only_widen]), and transports every       *)
(* other image predicate across itself in one step.                       *)
(* ===================================================================== *)

Definition uM_only (M M' : gmap Z (bv 8)) (a n : Z) : Prop :=
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) /\
  (forall k : Z, k < a \/ a + n <= k -> M' !! k = M !! k).

Lemma uM_only_refl (M : gmap Z (bv 8)) (a n : Z) : uM_only M M a n.
Proof. split; [ intros k H; exact H | intros k _; reflexivity ]. Qed.

Lemma uM_only_trans (M1 M2 M3 : gmap Z (bv 8)) (a n : Z) :
  uM_only M1 M2 a n -> uM_only M2 M3 a n -> uM_only M1 M3 a n.
Proof.
  intros [D1 E1] [D2 E2]. split.
  - intros k H. exact (D2 k (D1 k H)).
  - intros k Hk. rewrite (E2 k Hk). exact (E1 k Hk).
Qed.

Lemma uM_only_widen (M M' : gmap Z (bv 8)) (a n a' n' : Z) :
  uM_only M M' a n -> a' <= a -> a + n <= a' + n' -> uM_only M M' a' n'.
Proof.
  intros [D E] Hlo Hhi. split; [ exact D | ].
  intros k Hk. apply E. lia.
Qed.

(* ---- the transports ------------------------------------------------- *)

Lemma uM_only_stack (pt : uptd) (M M' : gmap Z (bv 8)) (sp0 : mword 64)
    (k a n : Z) :
  uM_only M M' a n -> uv_stack pt M sp0 k -> uv_stack pt M' sp0 k.
Proof. intros [D _] HS. exact (uv_stack_dom pt M M' sp0 k D HS). Qed.

Lemma uM_only_rd (pt : uptd) (M M' : gmap Z (bv 8)) (b m a n : Z) :
  uM_only M M' a n -> (a + n <= b \/ b + m <= a) -> uv_rd pt M b m ->
  uv_rd pt M' b m.
Proof.
  intros [_ E] Hdisj [Hlo Hn0 Hhi Hleaf Hb]. constructor; try assumption.
  intros j Hj. rewrite (E (b + j) ltac:(lia)). exact (Hb j Hj).
Qed.

Lemma uM_only_cstr (M M' : gmap Z (bv 8)) (b len a n : Z) :
  uM_only M M' a n -> (a + n <= b \/ b + len + 1 <= a) -> ucstr M b len ->
  ucstr M' b len.
Proof.
  intros [_ E] Hdisj [Hl Hbody Hnul]. constructor; [ exact Hl | | ].
  - intros j Hj. rewrite (E (b + j) ltac:(lia)). exact (Hbody j Hj).
  - rewrite (E (b + len) ltac:(lia)). exact Hnul.
Qed.

Lemma uM_only_uargs (pt : uptd) (M M' : gmap Z (bv 8)) (av argc lo a n : Z) :
  uM_only M M' a n -> a + n <= lo -> uargs pt M av argc lo ->
  uargs pt M' av argc lo.
Proof.
  intros [_ E] Hbelow HA.
  exact (uargs_above pt M M' av argc lo
           (fun k Hk => E k ltac:(lia)) HA).
Qed.

(* an image inclusion whose keys all sit BELOW the disturbed range -- the
   program TEXT, against any stack write *)
Lemma uM_only_img (img M M' : gmap Z (bv 8)) (a n : Z) :
  (forall (k : Z) (b : bv 8), img !! k = Some b -> k < a) ->
  uM_only M M' a n -> uimg_sub img M -> uimg_sub img M'.
Proof.
  intros Hkeys [_ E] Hsub k b Hk.
  rewrite (E k (or_introl (Hkeys k b Hk))). exact (Hsub k b Hk).
Qed.

(* ===================================================================== *)
(* §8 The callee-saved register set of the RISC-V calling convention.      *)
(*                                                                        *)
(* sp (x2), gp (x3), tp (x4), s0/s1 (x8/x9), s2..s11 (x18..x27).  A        *)
(* returning function's contract states [ucallee_saved m m'] rather than   *)
(* an insert tower, so a caller reads back exactly the registers the ABI   *)
(* promises and nothing about the ones it clobbered.                      *)
(* ===================================================================== *)

Definition ucallee_saved_idx (r : mword 5) : bool :=
  let z := uint r in
  Z.eqb z 2 || Z.eqb z 3 || Z.eqb z 4 || Z.eqb z 8 || Z.eqb z 9 ||
  ((18 <=? z) && (z <=? 27)).

Definition ucallee_saved (m m' : regfile) : Prop :=
  forall r : mword 5, ucallee_saved_idx r = true -> m' !!! Regidx r = m !!! Regidx r.

Lemma ucallee_saved_refl (m : regfile) : ucallee_saved m m.
Proof. intros r _; reflexivity. Qed.

Lemma ucallee_saved_trans (m1 m2 m3 : regfile) :
  ucallee_saved m1 m2 -> ucallee_saved m2 m3 -> ucallee_saved m1 m3.
Proof. intros H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

(* The area's lower bound may always be RELAXED.  This is the order a
   caller's transports have to run in: a prologue's stores sit BELOW the
   entry sp, so carry [uargs] across them at the OLD bound (where
   [uM_only_uargs]'s [a + n <= lo] holds exactly), and only then hand the
   callee the area at ITS lower entry sp. *)
Lemma uargs_lo_le (pt : uptd) (M : gmap Z (bv 8)) (av argc lo lo' : Z) :
  lo' <= lo -> uargs pt M av argc lo -> uargs pt M av argc lo'.
Proof.
  intros Hle [Hal Hlo Hargc Hrd Hptr].
  constructor; try assumption; [ lia | ].
  intros i Hi. destruct (Hptr i Hi) as (p & len & Hp & Hp0 & Hplo & Hlen & Hs & Hr).
  exists p, len. split_and!; try assumption; lia.
Qed.

(* ===================================================================== *)
(* §9 THE NORMALIZED READINGS.                                            *)
(*                                                                        *)
(* A verified program's proof carries every live register as              *)
(* [mword_of_int z] (UmodeArith.v).  The records above are stated over the *)
(* model's own address spellings ([add_vec_int sp0 (- n)]), so this        *)
(* section is the bridge: each lemma is the SAME fact read at a normalized *)
(* address, proved once here rather than transposed at every call site.    *)
(* ===================================================================== *)

(* the mod-8 twin of [uz_mod4096_of_mod16]: an 8-aligned address leaves a
   whole 8-byte access on its page *)
Lemma uz_mod4096_of_mod8 (V : Z) :
  0 <= V -> V mod 8 = 0 -> V mod 4096 <= 4088.
Proof.
  intros HV Hm.
  assert (Hd : (8 | 4096)) by (exists 512; reflexivity).
  pose proof (Znumtheory.Zmod_div_mod 8 4096 V ltac:(lia) ltac:(lia) Hd) as Hq.
  pose proof (Z.mod_pos_bound V 4096 ltac:(lia)) as Hb.
  pose proof (Z.div_mod (V mod 4096) 8 ltac:(lia)) as Hdm.
  rewrite <- Hq in Hdm. rewrite Hm in Hdm. lia.
Qed.

Lemma uva_canon_moi (z : Z) :
  0 <= z < 2 ^ 38 -> uva_canon (mword_of_int z : mword 64).
Proof.
  intro Hz. change (2 ^ 38) with 274877906944 in Hz.
  apply uva_canon_small.
  rewrite (moi_small z ltac:(unfold Z64; lia)). lia.
Qed.

(* THE bridge: the two spellings of a stack slot's address are one word *)
Lemma uv_stack_slot_addr (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64)
    (n d : Z) :
  uv_stack pt M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
  add_vec_int (add_vec_int sp0 (- n)) d
  = (mword_of_int (uint sp0 - n + d) : mword 64).
Proof.
  intros HS Hd0 Hdn Hd8.
  destruct (uv_stack_slot pt M sp0 n d HS Hd0 Hdn Hd8) as (Hu & _).
  rewrite <- Hu. symmetry. apply moi_of_uint.
Qed.

(* [uv_stack_slot] read at the normalized address.  BOTH readings are kept
   deliberately: a proof that carries sp in the model's own spelling (the
   [sync] proofs) wants the raw one, and a proof that normalizes every
   register through UmodeArith.v (everything since) wants this one.  They
   are one adapter apart, which is much cheaper than transposing six
   conclusions at every store and reload. *)
Lemma uv_stack_slot_moi (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64)
    (n d : Z) (tgt : mword 64) :
  uv_stack pt M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
  tgt = (mword_of_int (uint sp0 - n + d) : mword 64) ->
  uint tgt = uint sp0 - n + d /\
  (exists w : mword 64,
     ud_um pt !! svpn_of tgt = Some w /\
     uleaf_ok (Store Data) w /\ uleaf_ok (Load Data) w) /\
  uva_canon tgt /\
  Z.rem (uint tgt) 4096 <= 4088 /\
  is_aligned_vaddr (Virtaddr tgt) 8 = true /\
  (forall j : nat, (j < 8)%nat ->
     exists b : bv 8, M !! (uint tgt + Z.of_nat j) = Some b).
Proof.
  intros HS Hd0 Hdn Hd8 Htgt.
  rewrite Htgt. rewrite <- (uv_stack_slot_addr pt M sp0 n d HS Hd0 Hdn Hd8).
  exact (uv_stack_slot pt M sp0 n d HS Hd0 Hdn Hd8).
Qed.

(* ... and of the bottom of a budget (the post-prologue sp) *)
Lemma uv_stack_sp_moi (pt : uptd) (M : gmap Z (bv 8)) (sp0 : mword 64) (n : Z) :
  uv_stack pt M sp0 n ->
  add_vec_int sp0 (- n) = (mword_of_int (uint sp0 - n) : mword 64).
Proof.
  intro HS. rewrite uint_unsigned.
  rewrite <- (uv_stack_uint_lo pt M sp0 n HS).
  symmetry. apply moi_of_unsigned.
Qed.

(* [urd_leaf] at an ABSOLUTE address -- the reading a load's call site
   wants, [urd_leaf]'s own being indexed by an offset *)
Lemma uv_rd_leaf_at (pt : uptd) (M : gmap Z (bv 8)) (b n k : Z) :
  uv_rd pt M b n -> 0 <= k - b < n ->
  exists w : mword 64,
    ud_um pt !! svpn_of (mword_of_int k : mword 64) = Some w /\
    uleaf_ok (Load Data) w.
Proof.
  intros HR Hk.
  destruct (urd_leaf _ _ _ _ HR (k - b) Hk) as (w & Hw & Hok).
  replace (b + (k - b)) with k in Hw by lia.
  exists w. exact (conj Hw Hok).
Qed.

(* every side condition an 8-byte ACCESS needs at an 8-aligned canonical
   address that is NOT on the stack -- the argument area's counterpart of
   [uv_stack_slot] (a pointer dereference; echo's [ld s2,0(s1)]) *)
Lemma uv_slot8_facts (a : Z) (va : mword 64) :
  0 <= a -> a mod 8 = 0 -> a + 8 <= 2 ^ 38 ->
  va = (mword_of_int a : mword 64) ->
  uint va = a /\
  uva_canon va /\
  Z.rem (uint va) 4096 <= 4088 /\
  is_aligned_vaddr (Virtaddr va) 8 = true.
Proof.
  intros Ha0 Ha8 Hahi Hva.
  change (2 ^ 38) with 274877906944 in Hahi.
  assert (Hu : uint va = a)
    by (rewrite Hva; apply uint_moi; unfold Z64; lia).
  split_and!.
  - exact Hu.
  - apply uva_canon_small. rewrite <- uint_unsigned. rewrite Hu. lia.
  - rewrite Hu. rewrite Z.rem_mod_nonneg; [ | lia | lia ].
    exact (uz_mod4096_of_mod8 a Ha0 Ha8).
  - unfold is_aligned_vaddr. apply Z.eqb_eq. cbn [bits_of_virtaddr].
    rewrite Hu. rewrite Z.rem_mod_nonneg; [ | lia | lia ]. exact Ha8.
Qed.

(* [ucallee_saved]'s INTRODUCTION rule: writing a caller-saved register
   preserves the callee-saved set.  Without it, a loop body's register
   invariants have to be walked back through the whole insert tower one
   [upd_ne] at a time. *)
Lemma ucs_caller (m : regfile) (r : mword 5) (v : mword 64) :
  ucallee_saved_idx r = false -> ucallee_saved m (<[Regidx r := v]> m).
Proof.
  intros Hr r' Hr'. apply upd_ne. intro He.
  assert (Hrr : r' = r) by (injection He; trivial).
  rewrite Hrr in Hr'. rewrite Hr in Hr'. discriminate.
Qed.

(* ===================================================================== *)
(* §10 WRITABLE windows, and the exec argument vector.                    *)
(*                                                                        *)
(* [uv_wr] is [uv_rd]'s store-side twin -- what a syscall that WRITES a    *)
(* caller-supplied buffer (read, pipe, wait) needs about it.              *)
(*                                                                        *)
(* [ustr_at] / [uargv_at] / [uexec_args] describe a C string and an        *)
(* argv vector by their CONTENTS, not just their shape: that is what lets  *)
(* a syscall arm say WHICH program is being exec'd with WHICH arguments,   *)
(* and hence what lets a verified process's theorem say what it DOES       *)
(* rather than only that it steps.  ([ucstr] above says a string is        *)
(* NUL-terminated of some length; [ustr_at] pins the bytes.)              *)
(* ===================================================================== *)

Record uv_wr (pt : uptd) (M : gmap Z (bv 8)) (a n : Z) : Prop := UvWr {
  uwr_lo    : 0 <= a;
  uwr_n0    : 0 <= n;
  uwr_hi    : a + n <= 2 ^ 38;
  uwr_leaf  : forall j : Z, 0 <= j < n ->
                exists w : mword 64,
                  ud_um pt !! svpn_of (mword_of_int (a + j) : mword 64) = Some w /\
                  uleaf_ok (Store Data) w;
  uwr_bytes : forall j : Z, 0 <= j < n -> exists b : bv 8, M !! (a + j) = Some b
}.

Lemma uv_wr_sub (pt : uptd) (M : gmap Z (bv 8)) (a n a' n' : Z) :
  uv_wr pt M a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> uv_wr pt M a' n'.
Proof.
  intros [Hlo Hn0 Hhi Hleaf Hb] Ha Hn' Hhi'.
  constructor; try lia.
  - intros j Hj. replace (a' + j) with (a + (a' - a + j)) by lia. apply Hleaf. lia.
  - intros j Hj. replace (a' + j) with (a + (a' - a + j)) by lia. apply Hb. lia.
Qed.

Lemma uv_wr_dom (pt : uptd) (M M' : gmap Z (bv 8)) (a n : Z) :
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
  uv_wr pt M a n -> uv_wr pt M' a n.
Proof.
  intros Hdom [Hlo Hn0 Hhi Hleaf Hb]. constructor; try assumption.
  intros j Hj. destruct (Hb j Hj) as [b HMb].
  destruct (Hdom (a + j) (mk_is_Some _ _ HMb)) as [b' Hb']. eauto.
Qed.

(* a NUL-terminated string at [a] whose bytes are exactly [bs] *)
Definition ustr_at (M : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) : Prop :=
  (forall (j : nat) (b : bv 8), bs !! j = Some b -> M !! (a + Z.of_nat j) = Some b) /\
  M !! (a + Z.of_nat (length bs)) = Some ubyte0.

(* a NULL-terminated array of pointers at [pv], the i-th pointing at the
   NUL-terminated string [args !!! i] -- exec's second argument *)
Definition uargv_at (M : gmap Z (bv 8)) (pv : Z)
    (args : list (list (bv 8))) : Prop :=
  (forall (i : nat) (bs : list (bv 8)), args !! i = Some bs ->
     exists p : Z,
       uM_bytes M (pv + 8 * Z.of_nat i) 8 (mword_of_int p : mword 64) /\
       ustr_at M p bs) /\
  uM_bytes M (pv + 8 * Z.of_nat (length args)) 8 (mword_of_int 0 : mword 64).

(* THE observable content of an [exec]: which program, with which
   arguments.  A protocol's exec arm demands this of the process, so a
   process's theorem states what it execs. *)
Definition uexec_args (M : gmap Z (bv 8)) (pa pv : Z)
    (path : list (bv 8)) (args : list (list (bv 8))) : Prop :=
  ustr_at M pa path /\ uargv_at M pv args.
