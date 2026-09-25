(* ===================================================================== *)
(* UkGrepLib.v -- grep's two ulib callees on the separation-logic heap,   *)
(* and the heap and arithmetic lemmas grep's matcher walks share.         *)
(* (design: claude-notes/design/grep.md, section 3)                        *)
(*                                                                        *)
(*   - [ustr_cons_split] / [ustr_cons_join]: a string at its first byte.  *)
(*     The matcher recurses at [re+1], [re+2] and [text+1], so every      *)
(*     recursive call hands the callee the string's SUFFIX and takes it   *)
(*     back.  The join needs the two facts the split forgets (the first   *)
(*     byte is not the NUL, the length is representable); the caller      *)
(*     reads them off the whole string before splitting it.               *)
(*   - [wp_kgrep_strchr]: [strchr(p, c)] over an owned run whose last     *)
(*     byte is the first one that is [c] or the NUL.                      *)
(*   - [wp_kgrep_memmove]: [memmove(dst, src, n)] at [dst <= src], both   *)
(*     loops: [dst < src] copies forward, [dst = src] takes the backward  *)
(*     loop and rewrites every byte with itself.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UserBits UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunBr.
Require Import UCodeGrep.
Require Import CtxIdDefs.
Require User.GrepSyms User.GrepInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Set Printing Depth 40.

(* ===================================================================== *)
(* §1 PURE: lists, bytes, words.                                          *)
(* ===================================================================== *)

(* the list a [ustr] names, at its first byte *)
Lemma map_seq_S {A : Type} (f : nat -> A) (n : nat) :
  map f (seq 0 (S n)) = f 0%nat :: map (fun j => f (S j)) (seq 0 n).
Proof.
  simpl. f_equal. rewrite <- seq_shift. rewrite map_map. reflexivity.
Qed.

(* a byte function with one entry replaced -- what a store leaves behind *)
Definition fset (f : nat -> bv 8) (i : nat) (b : bv 8) : nat -> bv 8 :=
  fun j => if Nat.eqb j i then b else f j.

(* the first byte of a string of length [len]: its NUL when it is empty *)
Definition ustr_hd (len : nat) (f : nat -> bv 8) : bv 8 :=
  match len with 0%nat => ubyte0 | S _ => f 0%nat end.

Lemma ubyte0_unsigned : bv_unsigned ubyte0 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma byte_range (b : bv 8) : 0 <= bv_unsigned b < 256.
Proof.
  destruct (bv_unsigned_in_range _ b) as [H0 H1].
  assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E in H1. lia.
Qed.

(* a byte is the NUL exactly when its value is 0 *)
Lemma byte_eqb0 (b : bv 8) : (bv_unsigned b =? 0) = bool_decide (b = ubyte0).
Proof.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [Hz | Hz].
  - symmetry. apply bool_decide_eq_true. apply bv_eq. rewrite Hz. vm_compute. reflexivity.
  - symmetry. apply bool_decide_eq_false. intro He. apply Hz. rewrite He. vm_compute. reflexivity.
Qed.

(* two bytes are equal exactly when their values are *)
Lemma byte_eqb (a b : bv 8) : (bv_unsigned a =? bv_unsigned b) = bool_decide (a = b).
Proof.
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Hz | Hz].
  - symmetry. apply bool_decide_eq_true. apply bv_eq. exact Hz.
  - symmetry. apply bool_decide_eq_false. intro He. apply Hz. rewrite He. reflexivity.
Qed.

(* ...and against a literal byte [Z_to_bv 8 k] *)
Lemma byte_eqb_lit (a : bv 8) (k : Z) :
  0 <= k < 256 -> (bv_unsigned a =? k) = bool_decide (a = Z_to_bv 8 k).
Proof.
  intros Hk.
  assert (Ek : bv_unsigned (Z_to_bv 8 k) = k).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap.
    assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite E. apply Z.mod_small. exact Hk. }
  rewrite <- (byte_eqb a (Z_to_bv 8 k)). rewrite Ek. reflexivity.
Qed.

Lemma ustr_hd_eqb0 (len : nat) (f : nat -> bv 8) :
  (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
  (bv_unsigned (ustr_hd len f) =? 0) = Nat.eqb len 0.
Proof.
  intros Hne. destruct len as [| len'].
  - cbn [ustr_hd]. rewrite ubyte0_unsigned. reflexivity.
  - cbn [ustr_hd Nat.eqb]. rewrite byte_eqb0.
    apply bool_decide_eq_false. apply Hne. lia.
Qed.

(* the byte-valued register a load leaves: [mword_of_int] of the byte *)
Lemma moi_byte_eq (a b : bv 8) :
  eq_vec (mword_of_int (bv_unsigned a) : mword 64) (mword_of_int (bv_unsigned b))
  = bool_decide (a = b).
Proof.
  pose proof (byte_range a). pose proof (byte_range b).
  rewrite (moi_eq_vec (bv_unsigned a) (bv_unsigned b)
             ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
  apply byte_eqb.
Qed.

Lemma moi_byte_eqz (b : bv 8) :
  eq_vec (mword_of_int (bv_unsigned b) : mword 64) zero_reg = bool_decide (b = ubyte0).
Proof.
  pose proof (byte_range b).
  rewrite (moi_eq_zero (bv_unsigned b) ltac:(unfold Z64; lia)). apply byte_eqb0.
Qed.

Lemma moi_byte_neqz (b : bv 8) :
  neq_vec (mword_of_int (bv_unsigned b) : mword 64) zero_reg
  = negb (bool_decide (b = ubyte0)).
Proof. unfold neq_vec. rewrite moi_byte_eqz. reflexivity. Qed.

(* [addi rd,rs,-k ; beqz rd] on a byte: the byte is [k] *)
Lemma moi_sub_eqz (x k : Z) :
  0 <= x < 256 -> 0 <= k < 256 ->
  eq_vec (mword_of_int (x - k) : mword 64) zero_reg = (x =? k).
Proof.
  intros Hx Hk. rewrite zero_reg_moi.
  rewrite (moi_mod (x - k) ((x - k) mod Z64) ltac:(rewrite Z.mod_mod; unfold Z64; lia)).
  rewrite (moi_eq_vec ((x - k) mod Z64) 0
             ltac:(apply Z.mod_pos_bound; unfold Z64; lia) ltac:(unfold Z64; lia)).
  destruct (Z.eqb_spec x k) as [-> | Hne].
  - rewrite Z.sub_diag. reflexivity.
  - apply Z.eqb_neq. intro H0. apply Hne.
    apply Z.mod_divide in H0; [ | unfold Z64; lia ].
    destruct H0 as [q Hq]. unfold Z64 in Hq. nia.
Qed.

(* [seqz rd,rs] = [sltiu rd,rs,1], at a value that is a small difference *)
Lemma moi_seqz_sub (x k : Z) :
  0 <= x < 256 -> 0 <= k < 256 ->
  (zero_extend' 64 (bool_to_bit (zopz0zI_u (mword_of_int (x - k) : mword 64)
                                   (sign_extend' 64 (mword_of_int 1 : mword 12))))
   : mword 64)
  = mword_of_int (if x =? k then 1 else 0).
Proof.
  intros Hx Hk.
  assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64) = mword_of_int 1)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite E1.
  rewrite (moi_mod (x - k) ((x - k) mod Z64) ltac:(rewrite Z.mod_mod; unfold Z64; lia)).
  rewrite (moi_lt_u ((x - k) mod Z64) 1
             ltac:(apply Z.mod_pos_bound; unfold Z64; lia) ltac:(unfold Z64; lia)).
  assert (Hb : ((x - k) mod Z64 <? 1) = (x =? k)).
  { destruct (Z.eqb_spec x k) as [-> | Hne].
    - rewrite Z.sub_diag. reflexivity.
    - apply Z.ltb_ge.
      assert (Hm : 0 <= (x - k) mod Z64) by (apply Z.mod_pos_bound; unfold Z64; lia).
      assert (Hnz : (x - k) mod Z64 <> 0).
      { intro H0. apply Hne.
        apply Z.mod_divide in H0; [ | unfold Z64; lia ].
        destruct H0 as [q Hq]. unfold Z64 in Hq. nia. }
      lia. }
  rewrite Hb. destruct (x =? k); apply bv_eq; vm_compute; reflexivity.
Qed.

(* ...at a plain value: [seqz] of a byte *)
Lemma moi_seqz (x : Z) :
  0 <= x < 256 ->
  (zero_extend' 64 (bool_to_bit (zopz0zI_u (mword_of_int x : mword 64)
                                   (sign_extend' 64 (mword_of_int 1 : mword 12))))
   : mword 64)
  = mword_of_int (if x =? 0 then 1 else 0).
Proof.
  intros Hx. pose proof (moi_seqz_sub x 0 Hx ltac:(lia)) as H.
  rewrite Z.sub_0_r in H. exact H.
Qed.

(* a 0/1 word is nonzero exactly when it is 1 *)
Lemma moi_b01_neqz (b : bool) :
  neq_vec (mword_of_int (if b then 1 else 0) : mword 64) zero_reg = b.
Proof. destruct b; vm_compute; reflexivity. Qed.

Lemma moi_b01_eqz (b : bool) :
  eq_vec (mword_of_int (if b then 1 else 0) : mword 64) zero_reg = negb b.
Proof. destruct b; vm_compute; reflexivity. Qed.

(* the 64-bit complement, [xori rd,rs,-1] *)
Lemma xor_vec64_unsigned (x y : mword 64) :
  bv_unsigned (xor_vec x y) = Z.lxor (bv_unsigned x) (bv_unsigned y).
Proof.
  cbv [xor_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word to_word get_word].
  unfold MachineWord.MachineWord.xor. apply bv_xor_unsigned.
Qed.

Lemma moi_not (x : Z) :
  0 <= x < Z64 ->
  xor_vec (mword_of_int x : mword 64) (sign_extend' 64 (mword_of_int 4095 : mword 12))
  = mword_of_int (- x - 1).
Proof.
  intros Hx.
  assert (Em1 : (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                = mword_of_int (-1)) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Em1. apply bv_eq.
  rewrite xor_vec64_unsigned !moi_unsigned.
  assert (EZ : Z64 = 2 ^ 64) by (vm_compute; reflexivity).
  rewrite EZ.
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases k 64) as [Hlt | Hge].
  - rewrite !(Z.mod_pow2_bits_low _ 64 k Hlt).
    rewrite Z.bits_m1; [ | lia ].
    replace (- x - 1) with (Z.lnot x) by (unfold Z.lnot; lia).
    rewrite (Z.lnot_spec x k Hk). destruct (Z.testbit x k); reflexivity.
  - rewrite !(Z.mod_pow2_bits_high _ 64 k ltac:(lia)). reflexivity.
Qed.

(* the zero-extend idiom [slli rd,rd,32 ; srli rd,rd,32] on a small count *)
Lemma moi_zext32 (z : Z) :
  0 <= z < Z31 ->
  shift_bits_right
    (shift_bits_left (mword_of_int z : mword 64)
       (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int z.
Proof.
  intro Hz.
  rewrite (moi_shl z 32 ltac:(lia)).
  rewrite (moi_shr (z * 2 ^ 32) 32 ltac:(lia)
             ltac:(change (2 ^ 32) with 4294967296; unfold Z31, Z64 in *; lia)).
  f_equal. apply Z.div_mul. vm_compute. discriminate.
Qed.

(* a byte loaded by [lbu] *)
Lemma zext8_byte (b : bv 8) :
  (zero_extend' 64 (b : mword 8) : mword 64) = mword_of_int (bv_unsigned b).
Proof. exact (zext8_moi b). Qed.

(* the byte a [sb] stores out of a register an [lbu] filled *)
Lemma nth_byte_zext8 (b : bv 8) :
  nth_byte (zero_extend' 64 (b : mword 8) : mword 64) 0 = b.
Proof.
  rewrite zext8_moi. apply bv_eq.
  rewrite nth_byte_unsigned.
  rewrite (moi_small (bv_unsigned b) ltac:(pose proof (byte_range b); unfold Z64; lia)).
  change (Z.of_N (8 * N.of_nat 0)) with 0. rewrite Z.shiftr_0_r.
  apply Z.mod_small. pose proof (byte_range b). change (2 ^ 8) with 256. lia.
Qed.

(* a 32-bit literal's value *)
Lemma moi32_small (z : Z) :
  0 <= z < Z32 -> bv_unsigned (mword_of_int z : mword 32) = z.
Proof.
  intros Hz. unfold mword_of_int, Values.to_word, get_word. cbn.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zmod32. apply Z.mod_small. exact Hz.
Qed.

(* [int n] as the ABI passes it: sign-extended, which at a nonnegative
   count is the count itself *)
Lemma sext32_count (z : Z) :
  0 <= z < Z31 ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intros Hz.
  rewrite (sext32_small (mword_of_int z : mword 32)
             ltac:(rewrite moi32_small; unfold Z31, Z32 in *; lia)).
  rewrite moi32_small; [ reflexivity | unfold Z31, Z32 in *; lia ].
Qed.

(* unsigned [>=] is reflexive *)
Lemma geu_refl (x : mword 64) : zopz0zKzJ_u x x = true.
Proof. unfold zopz0zKzJ_u. apply Z.geb_le. lia. Qed.

(* [blez rs] = [bge x0,rs] on a nonnegative count *)
Lemma blez_count (z : Z) :
  0 <= z < Z63 ->
  uv_btaken BGE zero_reg (mword_of_int z : mword 64) = (z =? 0).
Proof.
  intros Hz. cbn [uv_btaken]. rewrite zero_reg_moi.
  rewrite (moi_ge_s 0 z ltac:(unfold Z63; lia) Hz).
  destruct (Z.eqb_spec z 0) as [-> | Hne]; [ reflexivity | ].
  rewrite Z.geb_leb. apply Z.leb_gt. lia.
Qed.

(* WHAT memmove LEAVES, as one function.  [mm_post d i f]: the first [i]
   bytes of the window hold the source's ([f] at [d] further up), every
   other byte is where it was.  At [i = len] it is the post; the forward
   loop's invariant is the same function at the bytes copied so far. *)
Definition mm_post (d len : nat) (f : nat -> bv 8) : nat -> bv 8 :=
  fun j => if Nat.ltb j len then f (d + j)%nat else f j.

Lemma mm_post_0 (d : nat) (f : nat -> bv 8) (j : nat) : mm_post d 0 f j = f j.
Proof. reflexivity. Qed.

Lemma mm_post_d0 (len : nat) (f : nat -> bv 8) (j : nat) : mm_post 0 len f j = f j.
Proof. unfold mm_post. destruct (Nat.ltb j len); reflexivity. Qed.

(* one more byte copied *)
Lemma mm_post_step (d i : nat) (f : nat -> bv 8) (j : nat) :
  (0 < d)%nat ->
  fset (mm_post d i f) i (mm_post d i f (d + i)%nat) j = mm_post d (S i) f j.
Proof.
  intros Hd. unfold fset, mm_post.
  destruct (Nat.eqb_spec j i) as [-> | Hne].
  - rewrite (proj2 (Nat.ltb_ge (d + i) i) ltac:(lia)).
    rewrite (proj2 (Nat.ltb_lt i (S i)) ltac:(lia)). reflexivity.
  - destruct (Nat.ltb_spec j i) as [Hlt | Hge];
      destruct (Nat.ltb_spec j (S i)) as [Hlt' | Hge']; try reflexivity; lia.
Qed.

(* a byte rewritten with itself *)
Lemma fset_same (f : nat -> bv 8) (i j : nat) : fset f i (f i) j = f j.
Proof. unfold fset. destruct (Nat.eqb_spec j i) as [-> | _]; reflexivity. Qed.

(* ===================================================================== *)
(* §2 REGISTER BOOKKEEPING.                                               *)
(*                                                                        *)
(* [rkeep W m m']: every register outside the list [W] is where it was.   *)
(* A walk threads ONE such fact from a function's entry register file to  *)
(* its current one, widening [W] by each register an instruction writes;  *)
(* at the return it discharges [ucallee_saved] from it plus one equation  *)
(* per callee-saved member of [W] (the ones the epilogue restored).       *)
(* Membership is a boolean over the index's value, so for a literal       *)
(* register every side condition is one [vm_compute].                     *)
(* ===================================================================== *)
Definition rin (W : list Z) (r : mword 5) : bool := existsb (Z.eqb (uint r)) W.

Definition rkeep (W : list Z) (m m' : regfile) : Prop :=
  forall r : mword 5, rin W r = false -> m' !!! Regidx r = m !!! Regidx r.

Lemma rkeep_refl (W : list Z) (m : regfile) : rkeep W m m.
Proof. intros r _. reflexivity. Qed.

Lemma regidx_inj (r q : mword 5) : Regidx r = Regidx q -> r = q.
Proof. intros H. injection H. trivial. Qed.

(* writing a register of [W] keeps the fact *)
Lemma rkeep_upd (W : list Z) (m m' : regfile) (q : mword 5) (v : mword 64) :
  rin W q = true -> rkeep W m m' -> rkeep W m (<[Regidx q := v]> m').
Proof.
  intros Hq Hk r Hr. rewrite upd_ne.
  - exact (Hk r Hr).
  - intro He. apply regidx_inj in He. subst r. rewrite Hq in Hr. discriminate.
Qed.

(* a callee's [ucallee_saved] carries it, provided [W] holds every
   caller-saved register *)
Lemma rkeep_call (W : list Z) (m m1 m2 : regfile) :
  (forall r : mword 5, ucallee_saved_idx r = false -> rin W r = true) ->
  rkeep W m m1 -> ucallee_saved m1 m2 -> rkeep W m m2.
Proof.
  intros HW H1 H2 r Hr.
  destruct (ucallee_saved_idx r) eqn:Ecs.
  - rewrite (H2 r Ecs). exact (H1 r Hr).
  - rewrite (HW r Ecs) in Hr. discriminate.
Qed.

Lemma rkeep_weaken (W W' : list Z) (m m' : regfile) :
  (forall r : mword 5, rin W r = true -> rin W' r = true) ->
  rkeep W m m' -> rkeep W' m m'.
Proof.
  intros HW Hk r Hr. apply Hk.
  destruct (rin W r) eqn:E; [ | reflexivity ].
  rewrite (HW r E) in Hr. discriminate.
Qed.

Lemma rkeep_trans (W : list Z) (m1 m2 m3 : regfile) :
  rkeep W m1 m2 -> rkeep W m2 m3 -> rkeep W m1 m3.
Proof. intros H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

(* ...and at the return: the callee-saved members of [W] are restored *)
Lemma rkeep_ucs (W : list Z) (m m' : regfile) :
  rkeep W m m' ->
  (forall r : mword 5, ucallee_saved_idx r = true -> rin W r = true ->
     m' !!! Regidx r = m !!! Regidx r) ->
  ucallee_saved m m'.
Proof.
  intros Hk Hw r Hr. destruct (rin W r) eqn:E.
  - exact (Hw r Hr E).
  - exact (Hk r E).
Qed.

(* the value of a 5-bit index is below 32, so a register is one of the 32 *)
Lemma mword5_cases (r : mword 5) :
  exists k : Z, 0 <= k < 32 /\ r = mword_of_int k.
Proof.
  exists (bv_unsigned r). split.
  - destruct (bv_unsigned_in_range _ r) as [H0 H1].
    split; [ exact H0 | ].
    eapply Z.lt_le_trans; [ exact H1 | vm_compute; discriminate ].
  - apply bv_eq.
    unfold mword_of_int, Values.to_word, get_word. cbn.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. symmetry.
    apply Z.mod_small. exact (bv_unsigned_in_range _ r).
Qed.

(* widening a write set, decided over the 32 indices *)
Lemma rkeep_weaken_dec (W W' : list Z) (m m' : regfile) :
  forallb (fun k => implb (rin W (mword_of_int k)) (rin W' (mword_of_int k)))
          (map Z.of_nat (seq 0 32)) = true ->
  rkeep W m m' -> rkeep W' m m'.
Proof.
  intros Hdec. apply rkeep_weaken. intros r Hr.
  destruct (mword5_cases r) as [k [Hk32 ->]].
  rewrite forallb_forall in Hdec.
  assert (Hin : In k (map Z.of_nat (seq 0 32))).
  { apply in_map_iff. exists (Z.to_nat k). split; [ lia | ].
    apply in_seq. lia. }
  specialize (Hdec k Hin). rewrite Hr in Hdec. exact Hdec.
Qed.

(* THE RETURN, decided: every callee-saved register the walk wrote (a
   member of [W]) is one of [Wcs], and each of those is back.  The first
   premise is a closed boolean over the 32 indices, one [vm_compute]. *)
Lemma rkeep_ucs_dec (W Wcs : list Z) (m m' : regfile) :
  forallb (fun k => implb (ucallee_saved_idx (mword_of_int k) && rin W (mword_of_int k))
                          (existsb (Z.eqb k) Wcs))
          (map Z.of_nat (seq 0 32)) = true ->
  rkeep W m m' ->
  (forall k : Z, In k Wcs ->
     m' !!! Regidx (mword_of_int k) = m !!! Regidx (mword_of_int k)) ->
  ucallee_saved m m'.
Proof.
  intros Hdec Hk Hw r Hr. destruct (rin W r) eqn:E; [ | exact (Hk r E) ].
  destruct (mword5_cases r) as [k [Hk32 ->]].
  rewrite forallb_forall in Hdec.
  assert (Hin : In k (map Z.of_nat (seq 0 32))).
  { apply in_map_iff. exists (Z.to_nat k). split; [ lia | ].
    apply in_seq. lia. }
  specialize (Hdec k Hin). rewrite Hr E in Hdec. cbn in Hdec.
  apply existsb_exists in Hdec as [z [Hz Hze]]. apply Z.eqb_eq in Hze. subst z.
  exact (Hw k Hz).
Qed.

(* ===================================================================== *)
(* §3 THE HEAP LEMMAS: a string at its first byte, a run byte by byte.     *)
(* ===================================================================== *)
Section UkGrepHeap.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{!ghost_varG Σ Z}.

  (* two runs whose byte functions agree below the length are one run *)
  Lemma ubytesq_ext (γd : gname) (dq : dfrac) (a : Z) (n : nat) (f g : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> f j = g j) ->
    ubytesq γd dq a n f ⊣⊢ ubytesq γd dq a n g.
  Proof using .
    intros Hfg. rewrite /ubytesq. apply big_opL_proper.
    intros k j Hj. apply lookup_seq in Hj as [-> Hlt].
    rewrite (Hfg (0 + k)%nat Hlt). reflexivity.
  Qed.

  (* one byte of a run, out and back unchanged *)
  Lemma ubytesq_byte (γd : gname) (dq : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) (i : nat) :
    (i < n)%nat ->
    ubytesq γd dq a n f -∗
      ubyteq γd dq (a + Z.of_nat i) (f i) ∗
      (ubyteq γd dq (a + Z.of_nat i) (f i) -∗ ubytesq γd dq a n f).
  Proof using .
    intros Hi. iIntros "Hbs". rewrite /ubytesq.
    iDestruct (big_sepL_lookup_acc _ _ i i with "Hbs") as "[Hb Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hi ] | ].
    iFrame "Hb". iIntros "Hb". iApply ("Hcl" with "Hb").
  Qed.

  (* ...and back holding ANY byte: what a store does to one byte of a run *)
  Lemma ubytes_byte_upd (γd : gname) (a : Z) (n : nat) (f : nat -> bv 8) (i : nat) :
    (i < n)%nat ->
    ubytes γd a n f -∗
      ubyte γd (a + Z.of_nat i) (f i) ∗
      (∀ b : bv 8, ubyte γd (a + Z.of_nat i) b -∗ ubytes γd a n (fset f i b)).
  Proof using .
    intros Hi. iIntros "Hbs". rewrite /ubytes /ubytesq.
    iDestruct (big_sepL_lookup_acc_impl i i with "Hbs") as "[Hb Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hi ] | ].
    iFrame "Hb". iIntros (b) "Hb".
    iApply ("Hcl" with "[] [Hb]").
    - iModIntro. iIntros (k y Hy Hne) "H".
      apply lookup_seq in Hy as [-> _].
      rewrite /fset. rewrite (proj2 (Nat.eqb_neq (0 + k) i) ltac:(lia)). iExact "H".
    - rewrite /fset Nat.eqb_refl. iExact "Hb".
  Qed.

  (* THE SUFFIX SPLIT: a string of length [S len] is its first byte and
     the string of length [len] one address up *)
  Lemma ustr_cons_split (γd : gname) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    ustr γd dq a (S len) f -∗
      ubyteq γd dq a (f 0%nat) ∗ ustr γd dq (a + 1) len (fun j => f (S j)).
  Proof using .
    iIntros "(%Hne & %Hlen & Hbs & Hnul)". rewrite /ubytesq.
    change (seq 0 (S len)) with (0%nat :: seq 1 len).
    rewrite big_sepL_cons.
    iDestruct "Hbs" as "[H0 Hbs]".
    replace (a + Z.of_nat 0) with a by lia. iFrame "H0".
    rewrite /ustr /ubytesq.
    iSplit; [ iPureIntro; intros j Hj; apply Hne; lia | ].
    iSplit; [ iPureIntro; lia | ].
    replace (a + 1 + Z.of_nat len) with (a + Z.of_nat (S len)) by lia.
    iFrame "Hnul".
    rewrite <- (seq_shift len 0). rewrite big_sepL_fmap.
    iApply (big_sepL_mono with "Hbs"). intros k j _.
    replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia.
    auto.
  Qed.

  (* ...and the join, which needs back the two facts the split forgot *)
  Lemma ustr_cons_join (γd : gname) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    f 0%nat <> ubyte0 -> Z.of_nat (S len) < 2 ^ 31 ->
    ubyteq γd dq a (f 0%nat) -∗ ustr γd dq (a + 1) len (fun j => f (S j)) -∗
    ustr γd dq a (S len) f.
  Proof using .
    intros H0 Hlen. iIntros "Hb (%Hne & _ & Hbs & Hnul)".
    rewrite /ustr /ubytesq.
    iSplit.
    { iPureIntro. intros [| j] Hj; [ exact H0 | apply Hne; lia ]. }
    iSplit; [ iPureIntro; exact Hlen | ].
    replace (a + Z.of_nat (S len)) with (a + 1 + Z.of_nat len) by lia.
    iFrame "Hnul".
    change (seq 0 (S len)) with (0%nat :: seq 1 len).
    rewrite big_sepL_cons.
    replace (a + Z.of_nat 0) with a by lia. iFrame "Hb".
    rewrite <- (seq_shift len 0). rewrite big_sepL_fmap.
    iApply (big_sepL_mono with "Hbs"). intros k j _.
    replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia.
    auto.
  Qed.

  (* the first byte of a string, whatever its length: the NUL of the empty
     one, [f 0] otherwise *)
  Lemma ustr_hd_acc (γd : gname) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    ustr γd dq a len f -∗
      ubyteq γd dq a (ustr_hd len f) ∗
      (ubyteq γd dq a (ustr_hd len f) -∗ ustr γd dq a len f).
  Proof using .
    iIntros "Hs". destruct len as [| len'].
    - iDestruct (ustr_nul with "Hs") as "[Hb Hcl]".
      replace (a + Z.of_nat 0) with a by lia. iFrame.
    - iDestruct (ustr_byte γd dq a (S len') f 0%nat ltac:(lia) with "Hs")
        as "[Hb Hcl]".
      replace (a + Z.of_nat 0) with a by lia. iFrame.
  Qed.
End UkGrepHeap.

(* the caller-saved registers, as [rin] reads them: x0, ra, t0-t2, a0-a7,
   t3-t6.  A walk's write set is the callee-saved registers it spills
   followed by these. *)
Definition Wcaller : list Z := [0; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Lemma rin_app_caller (S : list Z) (r : mword 5) :
  ucallee_saved_idx r = false -> rin (S ++ Wcaller) r = true.
Proof.
  intros Hr. unfold rin. rewrite existsb_app. apply orb_true_iff. right.
  destruct (mword5_cases r) as [k [Hk ->]].
  assert (Hdec : forallb (fun k => implb (negb (ucallee_saved_idx (mword_of_int k)))
                                    (existsb (Z.eqb (uint (mword_of_int k : mword 5))) Wcaller))
                   (map Z.of_nat (seq 0 32)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hdec.
  assert (Hin : In k (map Z.of_nat (seq 0 32))).
  { apply in_map_iff. exists (Z.to_nat k). split; [ lia | ]. apply in_seq. lia. }
  specialize (Hdec k Hin). rewrite Hr in Hdec. exact Hdec.
Qed.

(* ===================================================================== *)
(* §4 THE WALKS.                                                          *)
(* ===================================================================== *)

(* [add_vec_int] of a literal pc by a literal displacement, as a literal *)
Ltac pcn :=
  repeat match goal with
  | |- context [ add_vec_int (mword_of_int ?a) ?d ] =>
      lazymatch a with Zpos _ => idtac | Z0 => idtac end;
      lazymatch d with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
      let z := eval vm_compute in (a + d)%Z in
      let E := fresh "Epc" in
      assert (E : add_vec_int (mword_of_int a : mword 64) d = mword_of_int z)
        by (apply bv_eq; vm_compute; reflexivity);
      rewrite E; clear E
  end.

(* a lookup in an insert tower, peeled to its base *)
Ltac rgl :=
  repeat first
    [ rewrite upd_eq
    | rewrite upd_ne; [ | vm_compute; discriminate ] ];
  cbv [regval_into_reg].

(* an [rkeep] across an insert tower *)
Ltac rk :=
  repeat first
    [ assumption
    | apply rkeep_refl
    | apply rkeep_upd; [ vm_compute; reflexivity | ] ].

Section UkGrepLib.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* NO DEPOSIT, NO [psok], NO PAYLOAD CLASS: strchr and memmove make no
     syscall and never exit, so nothing here touches [UkRun.udep] or the
     exit payload. *)

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* ADDRESS BOUNDS OFF THE RESOURCE (as [UkEcho.urun_ustr_bnd]).         *)
  (* ------------------------------------------------------------------- *)
  Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun N h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(_ & _ & _ & _ & Hh & _ & _ & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Lemma urun_ustr_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    urun N h m pc avail -∗ ustr γd dq a len f -∗
    ⌜ 0 <= a /\ a + Z.of_nat len < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hs".
    iDestruct (ustr_nul with "Hs") as "[Hnul Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun Hnul") as %Hhi.
    iDestruct ("Hcl" with "Hnul") as "Hs".
    destruct len as [| len' ].
    - iPureIntro. lia.
    - iDestruct (ustr_byte γd dq a (S len') f 0%nat ltac:(lia) with "Hs")
        as "[Hb0 _]".
      iDestruct (urun_ubyte_bnd with "Hrun Hb0") as %Hlo.
      iPureIntro. lia.
  Qed.

  (* a nonempty run's two ends bound it *)
  Lemma urun_ubytesq_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    (0 < len)%nat ->
    urun N h m pc avail -∗ ubytesq γd dq a len f -∗
    ⌜ 0 <= a /\ a + Z.of_nat len <= 2 ^ 38 ⌝.
  Proof using .
    intros Hlen. iIntros "Hrun Hs".
    iDestruct (ubytesq_byte γd dq a len f 0%nat Hlen with "Hs") as "[Hb0 Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun Hb0") as %Hlo.
    iDestruct ("Hcl" with "Hb0") as "Hs".
    iDestruct (ubytesq_byte γd dq a len f (len - 1)%nat ltac:(lia) with "Hs")
      as "[Hb1 _]".
    iDestruct (urun_ubyte_bnd with "Hrun Hb1") as %Hhi.
    iPureIntro. lia.
  Qed.

  (* ...and as an implication, for a run that may be empty *)
  Lemma urun_ubytesq_bnd' (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    urun N h m pc avail -∗ ubytesq γd dq a len f -∗
    ⌜ (0 < len)%nat -> 0 <= a /\ a + Z.of_nat len <= 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hs". destruct (Nat.eq_dec len 0) as [H0 | Hpos].
    - iPureIntro. intros Hp. lia.
    - iDestruct (urun_ubytesq_bnd with "Hrun Hs") as %Hb; [ lia | ].
      iPureIntro. intros _. exact Hb.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE TWO-WORD FRAME, generic in its four pcs (gcc emits it in strchr, *)
  (* memmove and matchhere):                                             *)
  (*   c.addi sp,sp,-16 ; c.sdsp ra,8(sp) ; c.sdsp s0,0(sp) ;             *)
  (*   c.addi4spn s0,sp,16                                               *)
  (* The frame's two words are handed out holding ra and s0; the post    *)
  (* says sp moved down by the frame and nothing but sp and s0 moved.    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kgrep_pro2 (h : CpuId) (m : regfile) (p0 p1 p2 p3 p4 : mword 64) (n : nat) :
    p1 = add_vec_int p0 2 -> p2 = add_vec_int p1 2 ->
    p3 = add_vec_int p2 2 -> p4 = add_vec_int p3 2 ->
    uinstr_is γt p0 true (C_ADDI (mword_of_int 48 : mword 6, Regidx (mword_of_int 2))) -∗
    uinstr_is γt p1 true (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))) -∗
    uinstr_is γt p2 true (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))) -∗
    uinstr_is γt p3 true (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)) -∗
    urun N h m p0 (2 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 16 <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1 = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)) ⌝ -∗
       ⌜ rkeep [2; 8] m m' ⌝ -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 8) (m !!! Regidx ra_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 16) (m !!! Regidx s0_idx) -∗
       urun N h' m' p4 n -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros E1 E2 E3 E4. iIntros "#I0 #I1 #I2 #I3 Hrun Hcont".
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 16 <= uint sp0) by lia.
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- c.addi sp,sp,-16 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn N h m p0 (mword_of_int 48 : mword 6) 2 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "I0 Hrun").
    rewrite Hsp -E1.
    iIntros "Hst" (h1) "Hrun".
    iDestruct (ustack_2_open with "Hst") as "(_ & [%v8 Hw8] & [%v0 Hw0])".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    (* ---- c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 p1
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 n
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "I1 Hw8 Hrun").
    iIntros "Hw8". rewrite -E2. iIntros (h2) "Hrun".
    (* ---- c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp N h2 m1 p2
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 n
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "I2 Hw0 Hrun").
    iIntros "Hw0". rewrite -E3 Hra1 Hs01. iIntros (h3) "Hrun".
    (* ---- c.addi4spn s0,sp,16 ---- *)
    iApply (wp_uk_caddi4spn N h3 m1 p3
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "I3 Hrun").
    rewrite -E4. iIntros (h4) "Hrun".
    iApply ("Hcont" $! h4 _ with "[] [] [] [] Hw8 Hw0 Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro. rgl. exact Hsp1.
    - iPureIntro. rewrite /m1. rk.
  Qed.

  (* ...and its epilogue, [c.ldsp ra,8(sp) ; c.ldsp s0,0(sp) ;
     c.addi sp,sp,16 ; c.jr ra]: the two words come back, [avail] rises by
     the frame, and only sp, s0 and ra moved *)
  Lemma wp_kgrep_epi2 (h : CpuId) (m : regfile) (sp0 vra vs0 : mword 64)
      (p0 p1 p2 p3 : mword 64) (n : nat) :
    p1 = add_vec_int p0 2 -> p2 = add_vec_int p1 2 -> p3 = add_vec_int p2 2 ->
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)) ->
    uint sp0 mod 8 = 0 ->
    16 <= uint sp0 ->
    uinstr_is γt p0 true (C_LDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))) -∗
    uinstr_is γt p1 true (C_LDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))) -∗
    uinstr_is γt p2 true (C_ADDI (mword_of_int 16 : mword 6, Regidx (mword_of_int 2))) -∗
    uinstr_is γt p3 true (C_JR (Regidx (mword_of_int 1))) -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    urun N h m p0 n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ rkeep [1; 2; 8] m m' ⌝ -∗
       urun N h' m' (ret_pc vra) (2 + n) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros E1 E2 E3 Hsp Hal8 Hlo. iIntros "#I0 #I1 #I2 #I3 Hwra Hws0 Hrun Hcont".
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- c.ldsp ra,8(sp) ---- *)
    iApply (wp_uk_cldsp N h m p0
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "I0 Hwra Hrun").
    iIntros "Hwra". rewrite -E1. iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx := regval_into_reg vra]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg vra)
               ltac:(vm_compute; discriminate)). }
    (* ---- c.ldsp s0,0(sp) ---- *)
    iApply (wp_uk_cldsp N h1 m1 p1
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "I1 Hws0 Hrun").
    iIntros "Hws0". rewrite -E2. iIntros (h2) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg vs0]> m1).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite <- Hsp1.
      exact (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg vs0)
               ltac:(vm_compute; discriminate)). }
    (* ---- c.addi sp,sp,16 -- THE POP ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd2 : 0 <= 8 * Z.of_nat 2) by lia.
    assert (Hlt2 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   + 8 * Z.of_nat 2 < Z64)
      by (rewrite Hbsp1; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    (8 * Z.of_nat 2) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                 (8 * Z.of_nat 2) Hd2 Hlt2).
      rewrite Hbsp1. lia. }
    iApply (wp_uk_caddi_sp_up N h2 m2 p2
              (mword_of_int 16 : mword 6) 2 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "I2 [Hwra Hws0] Hrun").
    { rewrite Hsp2 Hup ustack_2.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hwra"; [ iExists vra; iFrame | iExists vs0; iFrame ]. }
    rewrite Hsp2 Hup -E3.
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx csp_rs1 := regval_into_reg sp0]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = vra) by (rewrite /m3 /m2 /m1; rgl; reflexivity).
    (* ---- c.jr ra ---- *)
    iApply (wp_uk_cjr N h3 m3 p3
              ra_idx (ret_pc vra) (2 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra3; reflexivity)
              with "I3 Hrun").
    iIntros (h4) "Hrun".
    iApply ("Hcont" $! h4 m3 with "[] [] [] Hrun").
    - iPureIntro. rewrite /m3 /m2 /m1. rgl. reflexivity.
    - iPureIntro. rewrite /m3 /m2 /m1. rgl. reflexivity.
    - iPureIntro. rewrite /m3 /m2 /m1. rk.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* strchr's SCAN, 0x326..0x332:                                       *)
  (*   beq a1,a5,0x334 ; c.addi a0,a0,1 ; lbu a5,0(a0) ; c.bnez a5,0x326 *)
  (*   c.li a0,0                                                         *)
  (* a0 points AT byte [j] and a5 holds it; [i] bytes are left.  The     *)
  (* scan leaves at 0x334 either at the byte equal to [c] (a0 = p + k)   *)
  (* or after loading the NUL (a0 = 0) -- and the run's premises say     *)
  (* that byte is [k] either way.                                        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_strchr_loop (dq : dfrac) (p : Z) (c : bv 8) (k : nat)
      (g : nat -> bv 8) :
    c <> ubyte0 ->
    (forall j : nat, (j < k)%nat -> g j <> c /\ g j <> ubyte0) ->
    g k = c \/ g k = ubyte0 ->
    0 <= p -> p + Z.of_nat k < 2 ^ 38 ->
    forall (i j : nat) (h : CpuId) (mc : regfile) (n : nat),
    (j + i = k)%nat ->
    g j <> ubyte0 ->
    mc !!! Regidx a0_idx = mword_of_int (p + Z.of_nat j) ->
    mc !!! Regidx a1_idx = mword_of_int (bv_unsigned c) ->
    mc !!! Regidx a5_idx = mword_of_int (bv_unsigned (g j)) ->
    grep_code γt -∗
    ubytesq γd dq p (S k) g -∗
    urun N h mc (mword_of_int 0x326) n -∗
    (ubytesq γd dq p (S k) g -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ mc' !!! Regidx a0_idx
           = mword_of_int (if bool_decide (g k = c) then p + Z.of_nat k else 0)%Z ⌝ -∗
         ⌜ rkeep [10; 15] mc mc' ⌝ -∗
         urun N h' mc' (mword_of_int 0x334) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hc0 Hpre Hk Hp0 Hp38 i.
    change (2 ^ 38) with 274877906944 in Hp38.
    induction i as [| i IH ];
      intros j h mc n Hji Hgj Ha0 Ha1 Ha5;
      iIntros "#Hcode Hbs Hrun Hcont".
    - (* j = k: byte [k] is not the NUL, so it is [c] and the branch is taken *)
      assert (Hjk : j = k) by lia. subst j.
      assert (Hgk : g k = c) by (destruct Hk as [Hk | Hk]; [ exact Hk | contradiction ]).
      iApply (wp_uk_btype N h mc (mword_of_int 0x326)
                (mword_of_int 14 : mword 13) a5_idx a1_idx BEQ true
                (mword_of_int 0x334) n
                ltac:(cbn [uv_btaken]; rewrite Ha1 Ha5 moi_byte_eq;
                      symmetry; apply bool_decide_eq_true; symmetry; exact Hgk)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_326 with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "Hbs [] [] Hrun").
      + iPureIntro. rewrite (bool_decide_eq_true_2 _ Hgk). exact Ha0.
      + iPureIntro. apply rkeep_refl.
    - (* j < k: byte [j] is neither [c] nor the NUL *)
      assert (Hjk : (j < k)%nat) by lia.
      destruct (Hpre j Hjk) as [Hgjc _].
      iApply (wp_uk_btype N h mc (mword_of_int 0x326)
                (mword_of_int 14 : mword 13) a5_idx a1_idx BEQ false
                (mword_of_int 0x334) n
                ltac:(cbn [uv_btaken]; rewrite Ha1 Ha5 moi_byte_eq;
                      symmetry; apply bool_decide_eq_false; intro He; apply Hgjc;
                      symmetry; exact He)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros He; discriminate He)
                with "[] Hrun").
      { iApply (uis_grep_326 with "Hcode"). }
      iIntros (h1) "Hrun". pcn.
      (* ---- 0x32a  c.addi a0,a0,1 ---- *)
      iApply (wp_uk_caddi N h1 mc (mword_of_int 0x32a)
                (mword_of_int 1 : mword 6) a0_idx (mword_of_int (p + Z.of_nat (S j))) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0;
                      replace (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                        with (mword_of_int 1 : mword 64)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite moi_add; f_equal; lia)
                with "[] Hrun").
      { iApply (uis_grep_32a with "Hcode"). }
      iIntros (h2) "Hrun". pcn.
      set (m1 := <[Regidx a0_idx := regval_into_reg (mword_of_int (p + Z.of_nat (S j)) : mword 64)]> mc).
      (* ---- 0x32c  lbu a5,0(a0) ---- *)
      iDestruct (ubytesq_byte γd dq p (S k) g (S j) ltac:(lia) with "Hbs") as "[Hb Hcl]".
      assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0)
        by (vm_compute; reflexivity).
      assert (Hu1 : uint (mword_of_int (p + Z.of_nat (S j)) : mword 64) = p + Z.of_nat (S j))
        by (apply uint_moi; unfold Z64; lia).
      iApply (wp_uk_lbu N h2 m1 (mword_of_int 0x32c)
                (mword_of_int 0 : mword 12) a0_idx a5_idx dq (p + Z.of_nat (S j)) (g (S j)) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite /m1; rgl; rewrite Eoff0 Hu1; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_grep_32c with "Hcode"). }
      iIntros "Hb" (h3) "Hrun". pcn.
      iDestruct ("Hcl" with "Hb") as "Hbs".
      set (m2 := <[Regidx a5_idx := regval_into_reg (zero_extend' 64 (g (S j) : mword 8) : mword 64)]> m1).
      assert (Ha52 : m2 !!! Regidx a5_idx = mword_of_int (bv_unsigned (g (S j)))).
      { rewrite /m2; rgl. apply zext8_byte. }
      (* ---- 0x330  c.bnez a5,0x326 ---- *)
      iApply (wp_uk_cbnez N h3 m2 (mword_of_int 0x330)
                (mword_of_int 251 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                (negb (bool_decide (g (S j) = ubyte0))) (mword_of_int 0x326) n
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha52 moi_byte_neqz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_330 with "Hcode"). }
      iIntros (h4) "Hrun".
      destruct (decide (g (S j) = ubyte0)) as [Hz | Hnz].
      + (* the NUL: it is byte [k], and a0 := 0 *)
        rewrite (bool_decide_eq_true_2 _ Hz). cbn [negb]. pcn.
        assert (HSk : S j = k).
        { destruct (Nat.lt_ge_cases (S j) k) as [Hlt | Hge]; [ | lia ].
          exfalso. exact (proj2 (Hpre (S j) Hlt) Hz). }
        (* ---- 0x332  c.li a0,0 ---- *)
        iApply (wp_uk_cli N h4 m2 (mword_of_int 0x332)
                  (mword_of_int 0 : mword 6) a0_idx n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate) with "[] Hrun").
        { iApply (uis_grep_332 with "Hcode"). }
        iIntros (h5) "Hrun". pcn.
        iApply ("Hcont" with "Hbs [] [] Hrun").
        * iPureIntro. rgl.
          assert (Hgkc : g k <> c) by (rewrite <- HSk; rewrite Hz; intro He; apply Hc0; symmetry; exact He).
          rewrite (bool_decide_eq_false_2 _ Hgkc). apply bv_eq; vm_compute; reflexivity.
        * iPureIntro. rewrite /m2 /m1. rk.
      + (* a body byte: round again at [j+1] *)
        rewrite (bool_decide_eq_false_2 _ Hnz). cbn [negb].
        iApply (IH (S j) h4 m2 n ltac:(lia) Hnz
                  ltac:(rewrite /m2 /m1; rgl; reflexivity)
                  ltac:(rewrite /m2 /m1; rgl; exact Ha1)
                  Ha52
                  with "Hcode Hbs Hrun").
        iIntros "Hbs" (h5 mc5) "%Ha05 %Hk5 Hrun".
        iApply ("Hcont" with "Hbs [] [] Hrun").
        * iPureIntro. exact Ha05.
        * iPureIntro. eapply rkeep_trans; [ | exact Hk5 ]. rewrite /m2 /m1. rk.
  Qed.

  (* ===================================================================== *)
  (* strchr(p, c) -- the whole function.                                    *)
  (*                                                                        *)
  (* The run [p .. p+k] is owned (at any fraction), its bytes below [k]     *)
  (* are neither [c] nor the NUL, and byte [k] is one of the two.  The      *)
  (* answer is [p + k] when byte [k] is [c], else 0.  [c] is not the NUL    *)
  (* (grep asks for the newline): at [c = 0] the two premises on byte [k]   *)
  (* would not distinguish the arms.                                        *)
  (* ===================================================================== *)
  Lemma wp_kgrep_strchr (h : CpuId) (m : regfile) (dq : dfrac) (p : Z) (c : bv 8)
      (k : nat) (g : nat -> bv 8) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int p ->
    m !!! Regidx a1_idx = mword_of_int (bv_unsigned c) ->
    c <> ubyte0 ->
    (forall j : nat, (j < k)%nat -> g j <> c /\ g j <> ubyte0) ->
    g k = c \/ g k = ubyte0 ->
    grep_code γt -∗
    ubytesq γd dq p (S k) g -∗
    urun N h m (mword_of_int GrepSyms.strchr) (2 + n) -∗
    (ubytesq γd dq p (S k) g -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
           = mword_of_int (if bool_decide (g k = c) then p + Z.of_nat k else 0)%Z ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + n) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hc0 Hpre Hk. iIntros "#Hcode Hbs Hrun Hcont".
    iDestruct (urun_ubytesq_bnd with "Hrun Hbs") as %[Hp0 Hp38]; [ lia | ].
    change (2 ^ 38) with 274877906944 in Hp38.
    rewrite /GrepSyms.strchr.
    iApply (wp_kgrep_pro2 h m (mword_of_int 0x318) (mword_of_int 0x31a)
              (mword_of_int 0x31c) (mword_of_int 0x31e) (mword_of_int 0x320) n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [] [] [] Hrun").
    { iApply (uis_grep_318 with "Hcode"). }
    { iApply (uis_grep_31a with "Hcode"). }
    { iApply (uis_grep_31c with "Hcode"). }
    { iApply (uis_grep_31e with "Hcode"). }
    iIntros (h1 m1) "%Hal8 %Hlo %Hsp1 %Hk1 Hwra Hws0 Hrun".
    assert (Ha01 : m1 !!! Regidx a0_idx = mword_of_int p)
      by (rewrite (Hk1 a0_idx ltac:(vm_compute; reflexivity)); exact Ha0).
    assert (Ha11 : m1 !!! Regidx a1_idx = mword_of_int (bv_unsigned c))
      by (rewrite (Hk1 a1_idx ltac:(vm_compute; reflexivity)); exact Ha1).
    (* ---- 0x320  lbu a5,0(a0) ---- *)
    iDestruct (ubytesq_byte γd dq p (S k) g 0%nat ltac:(lia) with "Hbs") as "[Hb Hcl]".
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0)
      by (vm_compute; reflexivity).
    assert (Hu0 : uint (mword_of_int p : mword 64) = p) by (apply uint_moi; unfold Z64; lia).
    iApply (wp_uk_lbu N h1 m1 (mword_of_int 0x320)
              (mword_of_int 0 : mword 12) a0_idx a5_idx dq (p + Z.of_nat 0) (g 0%nat) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha01 Eoff0 Hu0; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_grep_320 with "Hcode"). }
    iIntros "Hb" (h2) "Hrun". pcn.
    iDestruct ("Hcl" with "Hb") as "Hbs".
    set (m2 := <[Regidx a5_idx := regval_into_reg (zero_extend' 64 (g 0%nat : mword 8) : mword 64)]> m1).
    assert (Ha52 : m2 !!! Regidx a5_idx = mword_of_int (bv_unsigned (g 0%nat))).
    { rewrite /m2; rgl. apply zext8_byte. }
    (* ---- 0x324  c.beqz a5,0x33c ---- *)
    iApply (wp_uk_cbeqz N h2 m2 (mword_of_int 0x324)
              (mword_of_int 12 : mword 8) (mword_of_int 7 : mword 3) a5_idx
              (bool_decide (g 0%nat = ubyte0)) (mword_of_int 0x33c) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha52 moi_byte_eqz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_324 with "Hcode"). }
    iIntros (h3) "Hrun".
    (* the rest of the walk, from the exit of the scan at 0x334 *)
    iAssert (∀ (h' : CpuId) (mc : regfile),
               ubytesq γd dq p (S k) g -∗
               ⌜ mc !!! Regidx a0_idx
                 = mword_of_int (if bool_decide (g k = c) then p + Z.of_nat k else 0)%Z ⌝ -∗
               ⌜ rkeep ([2; 8] ++ Wcaller) m mc ⌝ -∗
               ⌜ mc !!! Regidx csp_rs1
                 = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)) ⌝ -∗
               urun N h' mc (mword_of_int 0x334) n -∗
               mWP (Loop : expr riscv_lang))%I
      with "[Hwra Hws0 Hcont]" as "Htail".
    { iIntros (h' mc) "Hbs %Ha0c %Hkc %Hspc Hrun".
      iApply (wp_kgrep_epi2 h' mc (m !!! Regidx csp_rs1) (m !!! Regidx ra_idx)
                (m !!! Regidx s0_idx) (mword_of_int 0x334) (mword_of_int 0x336)
                (mword_of_int 0x338) (mword_of_int 0x33a) n
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                Hspc Hal8 Hlo
                with "[] [] [] [] Hwra Hws0 Hrun").
      { iApply (uis_grep_334 with "Hcode"). }
      { iApply (uis_grep_336 with "Hcode"). }
      { iApply (uis_grep_338 with "Hcode"). }
      { iApply (uis_grep_33a with "Hcode"). }
      iIntros (h'' m') "%Hsp' %Hs0' %Hk' Hrun".
      iApply ("Hcont" with "Hbs [] [] Hrun").
      - iPureIntro.
        assert (Hkm : rkeep ([2; 8] ++ Wcaller) m m').
        { eapply rkeep_trans; [ exact Hkc | ].
          refine (rkeep_weaken_dec _ _ _ _ _ Hk'); vm_compute; reflexivity. }
        apply (rkeep_ucs_dec ([2; 8] ++ Wcaller) [2; 8] m m'
                 ltac:(vm_compute; reflexivity) Hkm).
        intros z [<- | [<- | []]].
        + exact Hsp'.
        + exact Hs0'.
      - iPureIntro. rewrite (Hk' a0_idx ltac:(vm_compute; reflexivity)). exact Ha0c. }
    assert (Hk2 : rkeep ([2; 8] ++ Wcaller) m m2).
    { rewrite /m2. apply rkeep_upd; [ vm_compute; reflexivity | ].
      refine (rkeep_weaken_dec _ _ _ _ _ Hk1); vm_compute; reflexivity. }
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)))
      by (rewrite /m2; rgl; exact Hsp1).
    destruct (decide (g 0%nat = ubyte0)) as [Hz | Hnz].
    - (* the empty scan: byte 0 is the NUL, so [k = 0] and a0 := 0 *)
      rewrite (bool_decide_eq_true_2 _ Hz).
      assert (Hk0 : k = 0%nat).
      { destruct k as [| k']; [ reflexivity | ].
        exfalso. exact (proj2 (Hpre 0%nat ltac:(lia)) Hz). }
      subst k.
      (* ---- 0x33c  c.li a0,0 ---- *)
      iApply (wp_uk_cli N h3 m2 (mword_of_int 0x33c)
                (mword_of_int 0 : mword 6) a0_idx n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_grep_33c with "Hcode"). }
      iIntros (h4) "Hrun". pcn.
      set (m3 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> m2).
      (* ---- 0x33e  c.j 0x334 ---- *)
      iApply (wp_uk_cj N h4 m3 (mword_of_int 0x33e)
                (mword_of_int 2043 : mword 11) (mword_of_int 0x334) n
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_33e with "Hcode"). }
      iIntros (h5) "Hrun".
      iApply ("Htail" $! h5 m3 with "Hbs [] [] [] Hrun").
      + iPureIntro. rgl.
        assert (Hgkc : g 0%nat <> c) by (rewrite Hz; intro He; apply Hc0; symmetry; exact He).
        rewrite (bool_decide_eq_false_2 _ Hgkc). apply bv_eq; vm_compute; reflexivity.
      + iPureIntro. rewrite /m3. rk.
      + iPureIntro. rewrite /m3. rgl. exact Hsp2.
    - (* the scan, from byte 0 *)
      rewrite (bool_decide_eq_false_2 _ Hnz). pcn.
      iApply (wp_kgrep_strchr_loop dq p c k g Hc0 Hpre Hk Hp0 ltac:(lia)
                k 0%nat h3 m2 n ltac:(lia) Hnz
                ltac:(rewrite /m2; rgl; rewrite Ha01; f_equal; lia)
                ltac:(rewrite /m2; rgl; exact Ha11)
                Ha52
                with "Hcode Hbs Hrun").
      iIntros "Hbs" (h4 mc) "%Ha0c %Hkc Hrun".
      iApply ("Htail" $! h4 mc with "Hbs [] [] [] Hrun").
      + iPureIntro. exact Ha0c.
      + iPureIntro. eapply rkeep_trans; [ exact Hk2 | ].
        refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity.
      + iPureIntro. rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp2.
  Qed.

  Lemma ubytes_ext_w (a : Z) (n : nat) (f g : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> f j = g j) ->
    ubytes γd a n f -∗ ubytes γd a n g.
  Proof using .
    intros Hfg. rewrite /ubytes (ubytesq_ext γd (DfracOwn 1) a n f g Hfg).
    iIntros "H". iExact "H".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* memmove's FORWARD loop, 0x458..0x464 (dst < src):                   *)
  (*   c.addi a1,a1,1 ; c.addi a4,a4,1 ; lbu a3,-1(a1) ; sb a3,-1(a4) ;  *)
  (*   bne a5,a4,0x458                                                   *)
  (* [i] bytes are copied; a1 and a4 point at the next source and        *)
  (* destination bytes, a5 at the destination's end.  The read at        *)
  (* [d + i] is never a byte already written, because [d > 0].           *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_mm_fwd (dst : Z) (d len : nat) (f : nat -> bv 8) :
    (0 < d)%nat -> 0 <= dst -> dst + Z.of_nat (d + len) <= 2 ^ 38 ->
    forall (k i : nat) (h : CpuId) (mc : regfile) (n : nat),
    (i + S k = len)%nat ->
    mc !!! Regidx a1_idx = mword_of_int (dst + Z.of_nat d + Z.of_nat i) ->
    mc !!! Regidx a4_idx = mword_of_int (dst + Z.of_nat i) ->
    mc !!! Regidx a5_idx = mword_of_int (dst + Z.of_nat len) ->
    grep_code γt -∗
    ubytes γd dst (d + len) (mm_post d i f) -∗
    urun N h mc (mword_of_int 0x458) n -∗
    (ubytes γd dst (d + len) (mm_post d len f) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ rkeep [11; 13; 14] mc mc' ⌝ -∗
         urun N h' mc' (mword_of_int 0x468) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hd Hdst Hhi k.
    change (2 ^ 38) with 274877906944 in Hhi.
    induction k as [| k IH ];
      intros i h mc n Hik Ha1 Ha4 Ha5;
      iIntros "#Hcode Hw Hrun Hcont".
    all: assert (Em1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                       = mword_of_int 1) by (apply bv_eq; vm_compute; reflexivity).
    all: assert (Eoff : uoff_i12 (mword_of_int 4095 : mword 12) = -1)
           by (vm_compute; reflexivity).
    all: assert (Hu1 : uint (mword_of_int (dst + Z.of_nat d + Z.of_nat i + 1) : mword 64)
                       = dst + Z.of_nat d + Z.of_nat i + 1)
           by (apply uint_moi; unfold Z64; lia).
    all: assert (Hu4 : uint (mword_of_int (dst + Z.of_nat i + 1) : mword 64)
                       = dst + Z.of_nat i + 1)
           by (apply uint_moi; unfold Z64; lia).
    (* the body, shared by both arms *)
    all: iApply (wp_uk_caddi N h mc (mword_of_int 0x458)
                (mword_of_int 1 : mword 6) a1_idx
                (mword_of_int (dst + Z.of_nat d + Z.of_nat i + 1)) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1 Em1 moi_add; reflexivity)
                with "[] Hrun"); [ iApply (uis_grep_458 with "Hcode") | ].
    all: iIntros (h1) "Hrun"; pcn.
    all: set (m1 := <[Regidx a1_idx := regval_into_reg
                         (mword_of_int (dst + Z.of_nat d + Z.of_nat i + 1) : mword 64)]> mc).
    all: iApply (wp_uk_caddi N h1 m1 (mword_of_int 0x45a)
                (mword_of_int 1 : mword 6) a4_idx
                (mword_of_int (dst + Z.of_nat i + 1)) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /m1; rgl; rewrite Ha4 Em1 moi_add; reflexivity)
                with "[] Hrun"); [ iApply (uis_grep_45a with "Hcode") | ].
    all: iIntros (h2) "Hrun"; pcn.
    all: set (m2 := <[Regidx a4_idx := regval_into_reg
                         (mword_of_int (dst + Z.of_nat i + 1) : mword 64)]> m1).
    (* ---- 0x45c  lbu a3,-1(a1): byte [d + i], not yet written ---- *)
    all: iDestruct (ubytesq_byte γd (DfracOwn 1) dst (d + len) (mm_post d i f) (d + i)%nat
                   ltac:(lia) with "Hw") as "[Hb Hcl]".
    all: iApply (wp_uk_lbu N h2 m2 (mword_of_int 0x45c)
                (mword_of_int 4095 : mword 12) a1_idx a3_idx (DfracOwn 1)
                (dst + Z.of_nat (d + i)) (mm_post d i f (d + i)%nat) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite /m2 /m1; rgl; rewrite Hu1 Eoff; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun"); [ iApply (uis_grep_45c with "Hcode") | ].
    all: iIntros "Hb" (h3) "Hrun"; pcn.
    all: iDestruct ("Hcl" with "Hb") as "Hw".
    all: set (m3 := <[Regidx a3_idx := regval_into_reg
                         (zero_extend' 64 (mm_post d i f (d + i)%nat : mword 8) : mword 64)]> m2).
    (* ---- 0x460  sb a3,-1(a4): byte [i] ---- *)
    all: iDestruct (ubytes_byte_upd γd dst (d + len) (mm_post d i f) i ltac:(lia) with "Hw")
      as "[Hb Hcl]".
    all: iApply (wp_uk_sb N h3 m3 (mword_of_int 0x460)
                (mword_of_int 4095 : mword 12) a4_idx a3_idx
                (dst + Z.of_nat i) (mm_post d i f i) n
                ltac:(rewrite /m3 /m2 /m1; rgl; rewrite Hu4 Eoff; lia)
                with "[] Hb Hrun"); [ iApply (uis_grep_460 with "Hcode") | ].
    all: iIntros "Hb" (h4) "Hrun"; pcn.
    all: assert (Eb : nth_byte (m3 !!! Regidx a3_idx) 0 = mm_post d i f (d + i)%nat)
           by (rewrite /m3; rgl; apply nth_byte_zext8).
    all: iEval (rewrite Eb) in "Hb".
    all: iDestruct ("Hcl" with "Hb") as "Hw".
    all: iDestruct (ubytes_ext_w dst (d + len) _ (mm_post d (S i) f)
                      (fun j _ => mm_post_step d i f j Hd) with "Hw") as "Hw".
    (* ---- 0x464  bne a5,a4,0x458 ---- *)
    all: assert (Hbne : uv_btaken BNE (m3 !!! Regidx a5_idx) (m3 !!! Regidx a4_idx)
                        = negb (Nat.eqb (S i) len))
      by (cbn [uv_btaken]; rewrite /m3 /m2 /m1; rgl; rewrite Ha5;
          rewrite (moi_neq_vec (dst + Z.of_nat len) (dst + Z.of_nat i + 1)
                     ltac:(unfold Z64; lia) ltac:(unfold Z64; lia));
          f_equal; destruct (Nat.eqb_spec (S i) len) as [He | Hne];
          [ apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ]).
    - (* the last byte: fall through to 0x468 *)
      rewrite (proj2 (Nat.eqb_eq (S i) len) ltac:(lia)) in Hbne.
      iApply (wp_uk_btype N h4 m3 (mword_of_int 0x464)
                (mword_of_int 8180 : mword 13) a4_idx a5_idx BNE false
                (mword_of_int 0x458) n
                ltac:(rewrite Hbne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros He; discriminate He)
                with "[] Hrun"); [ iApply (uis_grep_464 with "Hcode") | ].
      iIntros (h5) "Hrun". pcn.
      assert (HSi : S i = len) by lia. rewrite HSi.
      iApply ("Hcont" with "Hw [] Hrun").
      iPureIntro. rewrite /m3 /m2 /m1. rk.
    - (* round again *)
      rewrite (proj2 (Nat.eqb_neq (S i) len) ltac:(lia)) in Hbne.
      iApply (wp_uk_btype N h4 m3 (mword_of_int 0x464)
                (mword_of_int 8180 : mword 13) a4_idx a5_idx BNE true
                (mword_of_int 0x458) n
                ltac:(rewrite Hbne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun"); [ iApply (uis_grep_464 with "Hcode") | ].
      iIntros (h5) "Hrun".
      iApply (IH (S i) h5 m3 n ltac:(lia)
                ltac:(rewrite /m3 /m2 /m1; rgl; f_equal; lia)
                ltac:(rewrite /m3 /m2; rgl; f_equal; lia)
                ltac:(rewrite /m3 /m2 /m1; rgl; exact Ha5)
                with "Hcode Hw Hrun").
      iIntros "Hw" (h6 mc6) "%Hk6 Hrun".
      iApply ("Hcont" with "Hw [] Hrun").
      iPureIntro. eapply rkeep_trans; [ | exact Hk6 ]. rewrite /m3 /m2 /m1. rk.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* memmove's BACKWARD loop, 0x488..0x494 (taken at dst = src):         *)
  (*   c.addi a1,a1,-1 ; c.addi a4,a4,-1 ; lbu a3,0(a1) ; sb a3,0(a4) ;  *)
  (*   bne a4,a5,0x488                                                   *)
  (* At [dst = src] both pointers name the same byte, so each turn        *)
  (* rewrites a byte with itself and the window comes back unchanged.    *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_mm_bwd (dst : Z) (len : nat) (f : nat -> bv 8) :
    0 <= dst -> dst + Z.of_nat len <= 2 ^ 38 ->
    forall (j : nat) (h : CpuId) (mc : regfile) (n : nat),
    (j <= len)%nat ->
    mc !!! Regidx a1_idx = mword_of_int (dst + Z.of_nat (S j)) ->
    mc !!! Regidx a4_idx = mword_of_int (dst + Z.of_nat (S j)) ->
    mc !!! Regidx a5_idx = mword_of_int dst ->
    (S j <= len)%nat ->
    grep_code γt -∗
    ubytes γd dst len f -∗
    urun N h mc (mword_of_int 0x488) n -∗
    (ubytes γd dst len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ rkeep [11; 13; 14] mc mc' ⌝ -∗
         urun N h' mc' (mword_of_int 0x498) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hdst Hhi j.
    change (2 ^ 38) with 274877906944 in Hhi.
    induction j as [j IH] using lt_wf_ind;
      intros h mc n Hjl Ha1 Ha4 Ha5 HSj;
      iIntros "#Hcode Hw Hrun Hcont".
    all: assert (Em1 : (sign_extend' 64 (mword_of_int 63 : mword 6) : mword 64)
                       = mword_of_int (-1)) by (apply bv_eq; vm_compute; reflexivity).
    all: assert (Eoff : uoff_i12 (mword_of_int 0 : mword 12) = 0)
           by (vm_compute; reflexivity).
    all: assert (Hu : uint (mword_of_int (dst + Z.of_nat j) : mword 64) = dst + Z.of_nat j)
           by (apply uint_moi; unfold Z64; lia).
    all: iApply (wp_uk_caddi N h mc (mword_of_int 0x488)
                (mword_of_int 63 : mword 6) a1_idx (mword_of_int (dst + Z.of_nat j)) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1 Em1 moi_add; f_equal; lia)
                with "[] Hrun"); [ iApply (uis_grep_488 with "Hcode") | ].
    all: iIntros (h1) "Hrun"; pcn.
    all: set (m1 := <[Regidx a1_idx := regval_into_reg
                         (mword_of_int (dst + Z.of_nat j) : mword 64)]> mc).
    all: iApply (wp_uk_caddi N h1 m1 (mword_of_int 0x48a)
                (mword_of_int 63 : mword 6) a4_idx (mword_of_int (dst + Z.of_nat j)) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /m1; rgl; rewrite Ha4 Em1 moi_add; f_equal; lia)
                with "[] Hrun"); [ iApply (uis_grep_48a with "Hcode") | ].
    all: iIntros (h2) "Hrun"; pcn.
    all: set (m2 := <[Regidx a4_idx := regval_into_reg
                         (mword_of_int (dst + Z.of_nat j) : mword 64)]> m1).
    (* ---- 0x48c  lbu a3,0(a1) ---- *)
    all: iDestruct (ubytesq_byte γd (DfracOwn 1) dst len f j ltac:(lia) with "Hw")
           as "[Hb Hcl]".
    all: iApply (wp_uk_lbu N h2 m2 (mword_of_int 0x48c)
                (mword_of_int 0 : mword 12) a1_idx a3_idx (DfracOwn 1)
                (dst + Z.of_nat j) (f j) n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite /m2 /m1; rgl; rewrite Hu Eoff; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun"); [ iApply (uis_grep_48c with "Hcode") | ].
    all: iIntros "Hb" (h3) "Hrun"; pcn.
    all: iDestruct ("Hcl" with "Hb") as "Hw".
    all: set (m3 := <[Regidx a3_idx := regval_into_reg
                         (zero_extend' 64 (f j : mword 8) : mword 64)]> m2).
    (* ---- 0x490  sb a3,0(a4): the same byte, back ---- *)
    all: iDestruct (ubytes_byte_upd γd dst len f j ltac:(lia) with "Hw") as "[Hb Hcl]".
    all: iApply (wp_uk_sb N h3 m3 (mword_of_int 0x490)
                (mword_of_int 0 : mword 12) a4_idx a3_idx
                (dst + Z.of_nat j) (f j) n
                ltac:(rewrite /m3 /m2; rgl; rewrite Hu Eoff; lia)
                with "[] Hb Hrun"); [ iApply (uis_grep_490 with "Hcode") | ].
    all: iIntros "Hb" (h4) "Hrun"; pcn.
    all: assert (Eb : nth_byte (m3 !!! Regidx a3_idx) 0 = f j)
           by (rewrite /m3; rgl; apply nth_byte_zext8).
    all: iEval (rewrite Eb) in "Hb".
    all: iDestruct ("Hcl" with "Hb") as "Hw".
    all: iDestruct (ubytes_ext_w dst len _ f (fun i _ => fset_same f j i) with "Hw") as "Hw".
    (* ---- 0x494  bne a4,a5,0x488 ---- *)
    all: assert (Hbne : uv_btaken BNE (m3 !!! Regidx a4_idx) (m3 !!! Regidx a5_idx)
                        = negb (Nat.eqb j 0))
      by (cbn [uv_btaken]; rewrite /m3 /m2 /m1; rgl; rewrite Ha5;
          rewrite (moi_neq_vec (dst + Z.of_nat j) dst
                     ltac:(unfold Z64; lia) ltac:(unfold Z64; lia));
          f_equal; destruct (Nat.eqb_spec j 0) as [He | Hne];
          [ apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ]).
    destruct j as [| j'].
    - (* the first byte: fall through to 0x498 *)
      cbn [Nat.eqb negb] in Hbne.
      iApply (wp_uk_btype N h4 m3 (mword_of_int 0x494)
                (mword_of_int 8180 : mword 13) a5_idx a4_idx BNE false
                (mword_of_int 0x488) n
                ltac:(rewrite Hbne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros He; discriminate He)
                with "[] Hrun"); [ iApply (uis_grep_494 with "Hcode") | ].
      iIntros (h5) "Hrun". pcn.
      iApply ("Hcont" with "Hw [] Hrun").
      iPureIntro. rewrite /m3 /m2 /m1. rk.
    - (* round again, one byte lower *)
      cbn [Nat.eqb negb] in Hbne.
      iApply (wp_uk_btype N h4 m3 (mword_of_int 0x494)
                (mword_of_int 8180 : mword 13) a5_idx a4_idx BNE true
                (mword_of_int 0x488) n
                ltac:(rewrite Hbne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun"); [ iApply (uis_grep_494 with "Hcode") | ].
      iIntros (h5) "Hrun".
      iApply (IH j' ltac:(lia) h5 m3 n ltac:(lia)
                ltac:(rewrite /m3 /m2 /m1; rgl; f_equal; lia)
                ltac:(rewrite /m3 /m2; rgl; f_equal; lia)
                ltac:(rewrite /m3 /m2 /m1; rgl; exact Ha5)
                ltac:(lia)
                with "Hcode Hw Hrun").
      iIntros "Hw" (h6 mc6) "%Hk6 Hrun".
      iApply ("Hcont" with "Hw [] Hrun").
      iPureIntro. eapply rkeep_trans; [ | exact Hk6 ]. rewrite /m3 /m2 /m1. rk.
  Qed.

  (* ===================================================================== *)
  (* memmove(dst, src, n) at [dst <= src] -- the whole function.            *)
  (*                                                                        *)
  (* The window [dst, src + n) is owned exclusively; afterwards its first   *)
  (* [n] bytes hold the source's and the rest is unchanged ([mm_post]).     *)
  (* [n] is a C [int], so its register is the ABI's sign-extended word.     *)
  (* [dst < src] runs the forward loop; [dst = src] runs the backward loop, *)
  (* which rewrites each byte with itself.                                 *)
  (* ===================================================================== *)
  Lemma wp_kgrep_memmove (h : CpuId) (m : regfile) (dst src : Z) (len : nat)
      (f : nat -> bv 8) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int dst ->
    m !!! Regidx a1_idx = mword_of_int src ->
    m !!! Regidx a2_idx = sign_extend' 64 (mword_of_int (Z.of_nat len) : mword 32) ->
    dst <= src ->
    Z.of_nat len < 2 ^ 31 ->
    grep_code γt -∗
    ubytes γd dst (Z.to_nat (src - dst) + len) f -∗
    urun N h m (mword_of_int GrepSyms.memmove) (2 + n) -∗
    (ubytes γd dst (Z.to_nat (src - dst) + len) (mm_post (Z.to_nat (src - dst)) len f) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + n) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Hds Hlen. iIntros "#Hcode Hw Hrun Hcont".
    remember (Z.to_nat (src - dst)) as d eqn:Hd.
    assert (Hsrc : src = dst + Z.of_nat d) by lia.
    clear Hd. subst src.
    change (2 ^ 31) with 2147483648 in Hlen.
    assert (Ha2' : m !!! Regidx a2_idx = mword_of_int (Z.of_nat len))
      by (rewrite Ha2; apply sext32_count; unfold Z31; lia).
    iDestruct (urun_ubytesq_bnd' with "Hrun Hw") as %Hbnd.
    rewrite /GrepSyms.memmove.
    iApply (wp_kgrep_pro2 h m (mword_of_int 0x43e) (mword_of_int 0x440)
              (mword_of_int 0x442) (mword_of_int 0x444) (mword_of_int 0x446) n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [] [] [] Hrun").
    { iApply (uis_grep_43e with "Hcode"). }
    { iApply (uis_grep_440 with "Hcode"). }
    { iApply (uis_grep_442 with "Hcode"). }
    { iApply (uis_grep_444 with "Hcode"). }
    iIntros (h1 m1) "%Hal8 %Hlo %Hsp1 %Hk1 Hwra Hws0 Hrun".
    assert (Ha01 : m1 !!! Regidx a0_idx = mword_of_int dst)
      by (rewrite (Hk1 a0_idx ltac:(vm_compute; reflexivity)); exact Ha0).
    assert (Ha11 : m1 !!! Regidx a1_idx = mword_of_int (dst + Z.of_nat d))
      by (rewrite (Hk1 a1_idx ltac:(vm_compute; reflexivity)); exact Ha1).
    assert (Ha21 : m1 !!! Regidx a2_idx = mword_of_int (Z.of_nat len))
      by (rewrite (Hk1 a2_idx ltac:(vm_compute; reflexivity)); exact Ha2').
    assert (Hk1' : rkeep ([2; 8] ++ Wcaller) m m1)
      by (refine (rkeep_weaken_dec _ _ _ _ _ Hk1); vm_compute; reflexivity).
    (* THE EPILOGUE, from 0x468, shared by every arm *)
    iAssert (∀ (h' : CpuId) (mc : regfile),
               ubytes γd dst (d + len) (mm_post d len f) -∗
               ⌜ rkeep ([2; 8] ++ Wcaller) m mc ⌝ -∗
               ⌜ mc !!! Regidx csp_rs1
                 = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)) ⌝ -∗
               urun N h' mc (mword_of_int 0x468) n -∗
               mWP (Loop : expr riscv_lang))%I
      with "[Hwra Hws0 Hcont]" as "Htail".
    { iIntros (h' mc) "Hw %Hkc %Hspc Hrun".
      iApply (wp_kgrep_epi2 h' mc (m !!! Regidx csp_rs1) (m !!! Regidx ra_idx)
                (m !!! Regidx s0_idx) (mword_of_int 0x468) (mword_of_int 0x46a)
                (mword_of_int 0x46c) (mword_of_int 0x46e) n
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                Hspc Hal8 Hlo
                with "[] [] [] [] Hwra Hws0 Hrun").
      { iApply (uis_grep_468 with "Hcode"). }
      { iApply (uis_grep_46a with "Hcode"). }
      { iApply (uis_grep_46c with "Hcode"). }
      { iApply (uis_grep_46e with "Hcode"). }
      iIntros (h'' m') "%Hsp' %Hs0' %Hk' Hrun".
      iApply ("Hcont" with "Hw [] Hrun").
      iPureIntro.
      assert (Hkm : rkeep ([2; 8] ++ Wcaller) m m').
      { eapply rkeep_trans; [ exact Hkc | ].
        refine (rkeep_weaken_dec _ _ _ _ _ Hk'); vm_compute; reflexivity. }
      apply (rkeep_ucs_dec ([2; 8] ++ Wcaller) [2; 8] m m'
               ltac:(vm_compute; reflexivity) Hkm).
      intros z [<- | [<- | []]].
      + exact Hsp'.
      + exact Hs0'. }
    (* ---- 0x446  bgeu a0,a1,0x470 -- taken exactly at dst = src ---- *)
    assert (Hbgeu : uv_btaken BGEU (m1 !!! Regidx a0_idx) (m1 !!! Regidx a1_idx)
                    = Nat.eqb d 0).
    { cbn [uv_btaken]. rewrite Ha01 Ha11. destruct d as [| d'].
      - rewrite Z.add_0_r. apply geu_refl.
      - destruct (Hbnd ltac:(lia)) as [Hd0 Hd38].
        change (2 ^ 38) with 274877906944 in Hd38.
        rewrite (moi_ge_u dst (dst + Z.of_nat (S d'))
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        cbn [Nat.eqb]. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype N h1 m1 (mword_of_int 0x446)
              (mword_of_int 42 : mword 13) a1_idx a0_idx BGEU (Nat.eqb d 0)
              (mword_of_int 0x470) n
              ltac:(rewrite Hbgeu; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_446 with "Hcode"). }
    iIntros (h2) "Hrun".
    assert (Hsp1' : m1 !!! Regidx csp_rs1
                    = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)))
      by exact Hsp1.
    assert (Hblez : forall mx : regfile, mx !!! Regidx a2_idx = mword_of_int (Z.of_nat len) ->
                      uv_btaken BGE zero_reg (mx !!! Regidx a2_idx) = Nat.eqb len 0).
    { intros mx Hmx. rewrite Hmx (blez_count (Z.of_nat len) ltac:(unfold Z63; lia)).
      destruct (Nat.eqb_spec len 0) as [-> | Hne]; [ reflexivity | apply Z.eqb_neq; lia ]. }
    destruct (Nat.eq_dec d 0) as [Hd0 | Hdpos].
    - (* ================= dst = src: the backward arm ================= *)
      subst d. cbn [Nat.eqb]. cbn [Nat.add].
      (* ---- 0x470  blez a2,0x468 ---- *)
      iApply (wp_uk_btype0l N h2 m1 (mword_of_int 0x470)
                (mword_of_int 8184 : mword 13) a2_idx BGE (Nat.eqb len 0)
                (mword_of_int 0x468) n
                ltac:(rewrite (Hblez m1 Ha21); reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_470 with "Hcode"). }
      iIntros (h3) "Hrun".
      destruct (Nat.eq_dec len 0) as [Hl0 | Hlpos].
      + (* nothing to move *)
        subst len. cbn [Nat.eqb].
        iApply ("Htail" $! h3 m1 with "[Hw] [] [] Hrun").
        * iApply (ubytes_ext_w with "Hw"). intros j _. symmetry. apply mm_post_0.
        * iPureIntro. exact Hk1'.
        * iPureIntro. exact Hsp1'.
      + rewrite (proj2 (Nat.eqb_neq len 0) Hlpos). pcn.
        destruct (Hbnd ltac:(lia)) as [Hd0 Hd38].
        change (2 ^ 38) with 274877906944 in Hd38. cbn [Nat.add] in Hd38.
        (* ---- 0x474  add a4,a0,a2 ---- *)
        iApply (wp_uk_add N h3 m1 (mword_of_int 0x474)
                  a0_idx a2_idx a4_idx (mword_of_int (dst + Z.of_nat len)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha01 Ha21 moi_add; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_474 with "Hcode"). }
        iIntros (h4) "Hrun". pcn.
        set (m2 := <[Regidx a4_idx := regval_into_reg
                        (mword_of_int (dst + Z.of_nat len) : mword 64)]> m1).
        (* ---- 0x478  c.add a1,a1,a2 ---- *)
        iApply (wp_uk_cadd N h4 m2 (mword_of_int 0x478)
                  a1_idx a2_idx (mword_of_int (dst + Z.of_nat len)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m2; rgl; rewrite Ha11 Ha21 moi_add; f_equal; lia)
                  with "[] Hrun").
        { iApply (uis_grep_478 with "Hcode"). }
        iIntros (h5) "Hrun". pcn.
        set (m3 := <[Regidx a1_idx := regval_into_reg
                        (mword_of_int (dst + Z.of_nat len) : mword 64)]> m2).
        (* ---- 0x47a  addiw a5,a2,-1 ---- *)
        iApply (wp_uk_addiw N h5 m3 (mword_of_int 0x47a)
                  (mword_of_int 4095 : mword 12) a2_idx a5_idx
                  (mword_of_int (Z.of_nat len - 1)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m3 /m2; rgl; rewrite Ha21;
                        replace (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                          with (mword_of_int (-1) : mword 64)
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite (moi_addw (Z.of_nat len) (-1) ltac:(unfold Z31; lia));
                        f_equal; lia)
                  with "[] Hrun").
        { iApply (uis_grep_47a with "Hcode"). }
        iIntros (h6) "Hrun". pcn.
        set (m4 := <[Regidx a5_idx := regval_into_reg
                        (mword_of_int (Z.of_nat len - 1) : mword 64)]> m3).
        (* ---- 0x47e  c.slli a5,a5,32 ; 0x480  c.srli a5,a5,32 ---- *)
        iApply (wp_uk_cslli N h6 m4 (mword_of_int 0x47e)
                  (mword_of_int 32 : mword 6) a5_idx
                  (shift_bits_left (mword_of_int (Z.of_nat len - 1) : mword 64)
                     (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m4; rgl; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_47e with "Hcode"). }
        iIntros (h7) "Hrun". pcn.
        set (m5 := <[Regidx a5_idx := regval_into_reg
                        (shift_bits_left (mword_of_int (Z.of_nat len - 1) : mword 64)
                           (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> m4).
        iApply (wp_uk_csrli N h7 m5 (mword_of_int 0x480)
                  (mword_of_int 32 : mword 6) (mword_of_int 7 : mword 3) a5_idx
                  (mword_of_int (Z.of_nat len - 1)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m5; rgl; symmetry; apply moi_zext32; unfold Z31; lia)
                  with "[] Hrun").
        { iApply (uis_grep_480 with "Hcode"). }
        iIntros (h8) "Hrun". pcn.
        set (m6 := <[Regidx a5_idx := regval_into_reg
                        (mword_of_int (Z.of_nat len - 1) : mword 64)]> m5).
        (* ---- 0x482  not a5,a5 ---- *)
        iApply (wp_uk_xori N h8 m6 (mword_of_int 0x482)
                  (mword_of_int 4095 : mword 12) a5_idx a5_idx
                  (mword_of_int (- (Z.of_nat len - 1) - 1)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m6; rgl; symmetry; apply moi_not; unfold Z64; lia)
                  with "[] Hrun").
        { iApply (uis_grep_482 with "Hcode"). }
        iIntros (h9) "Hrun". pcn.
        set (m7 := <[Regidx a5_idx := regval_into_reg
                        (mword_of_int (- (Z.of_nat len - 1) - 1) : mword 64)]> m6).
        (* ---- 0x486  c.add a5,a5,a4 -- a5 := dst, the loop's end ---- *)
        iApply (wp_uk_cadd N h9 m7 (mword_of_int 0x486)
                  a5_idx a4_idx (mword_of_int dst) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m7 /m6 /m5 /m4 /m3 /m2; rgl; rewrite moi_add; f_equal; lia)
                  with "[] Hrun").
        { iApply (uis_grep_486 with "Hcode"). }
        iIntros (h10) "Hrun". pcn.
        set (m8 := <[Regidx a5_idx := regval_into_reg (mword_of_int dst : mword 64)]> m7).
        iApply (wp_kgrep_mm_bwd dst len f Hd0 ltac:(lia) (len - 1)%nat h10 m8 n
                  ltac:(lia)
                  ltac:(rewrite /m8 /m7 /m6 /m5 /m4 /m3; rgl; f_equal; lia)
                  ltac:(rewrite /m8 /m7 /m6 /m5 /m4 /m3 /m2; rgl; f_equal; lia)
                  ltac:(rewrite /m8; rgl; reflexivity)
                  ltac:(lia)
                  with "Hcode Hw Hrun").
        iIntros "Hw" (h11 mc) "%Hkc Hrun".
        (* ---- 0x498  c.j 0x468 ---- *)
        iApply (wp_uk_cj N h11 mc (mword_of_int 0x498)
                  (mword_of_int 2024 : mword 11) (mword_of_int 0x468) n
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_498 with "Hcode"). }
        iIntros (h12) "Hrun".
        iApply ("Htail" $! h12 mc with "[Hw] [] [] Hrun").
        * iApply (ubytes_ext_w with "Hw"). intros j _. symmetry. apply mm_post_d0.
        * iPureIntro. eapply rkeep_trans; [ | refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity ].
          rewrite /m8 /m7 /m6 /m5 /m4 /m3 /m2. rk.
        * iPureIntro. rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite /m8 /m7 /m6 /m5 /m4 /m3 /m2. rgl. exact Hsp1'.
    - (* ================= dst < src: the forward arm ================= *)
      rewrite (proj2 (Nat.eqb_neq d 0) Hdpos). pcn.
      (* ---- 0x44a  blez a2,0x468 ---- *)
      iApply (wp_uk_btype0l N h2 m1 (mword_of_int 0x44a)
                (mword_of_int 30 : mword 13) a2_idx BGE (Nat.eqb len 0)
                (mword_of_int 0x468) n
                ltac:(rewrite (Hblez m1 Ha21); reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_44a with "Hcode"). }
      iIntros (h3) "Hrun".
      destruct (Nat.eq_dec len 0) as [Hl0 | Hlpos].
      + (* nothing to move *)
        subst len. cbn [Nat.eqb].
        iApply ("Htail" $! h3 m1 with "[Hw] [] [] Hrun").
        * iApply (ubytes_ext_w with "Hw"). intros j _. symmetry. apply mm_post_0.
        * iPureIntro. exact Hk1'.
        * iPureIntro. exact Hsp1'.
      + rewrite (proj2 (Nat.eqb_neq len 0) Hlpos). pcn.
        destruct (Hbnd ltac:(lia)) as [Hd0 Hd38].
        change (2 ^ 38) with 274877906944 in Hd38.
        (* ---- 0x44e  c.slli a2,a2,32 ; 0x450  c.srli a2,a2,32 ---- *)
        iApply (wp_uk_cslli N h3 m1 (mword_of_int 0x44e)
                  (mword_of_int 32 : mword 6) a2_idx
                  (shift_bits_left (mword_of_int (Z.of_nat len) : mword 64)
                     (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha21; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_44e with "Hcode"). }
        iIntros (h4) "Hrun". pcn.
        set (m2 := <[Regidx a2_idx := regval_into_reg
                        (shift_bits_left (mword_of_int (Z.of_nat len) : mword 64)
                           (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> m1).
        iApply (wp_uk_csrli N h4 m2 (mword_of_int 0x450)
                  (mword_of_int 32 : mword 6) (mword_of_int 4 : mword 3) a2_idx
                  (mword_of_int (Z.of_nat len)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m2; rgl; symmetry; apply moi_zext32; unfold Z31; lia)
                  with "[] Hrun").
        { iApply (uis_grep_450 with "Hcode"). }
        iIntros (h5) "Hrun". pcn.
        set (m3 := <[Regidx a2_idx := regval_into_reg
                        (mword_of_int (Z.of_nat len) : mword 64)]> m2).
        (* ---- 0x452  add a5,a0,a2 ---- *)
        iApply (wp_uk_add N h5 m3 (mword_of_int 0x452)
                  a0_idx a2_idx a5_idx (mword_of_int (dst + Z.of_nat len)) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m3 /m2; rgl; rewrite Ha01 moi_add; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_452 with "Hcode"). }
        iIntros (h6) "Hrun". pcn.
        set (m4 := <[Regidx a5_idx := regval_into_reg
                        (mword_of_int (dst + Z.of_nat len) : mword 64)]> m3).
        (* ---- 0x456  c.mv a4,a0 ---- *)
        iApply (wp_uk_cmv N h6 m4 (mword_of_int 0x456)
                  a4_idx a0_idx (mword_of_int dst) n
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /m4 /m3 /m2; rgl; rewrite Ha01 moi_add_zero_l; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_456 with "Hcode"). }
        iIntros (h7) "Hrun". pcn.
        set (m5 := <[Regidx a4_idx := regval_into_reg (mword_of_int dst : mword 64)]> m4).
        iDestruct (ubytes_ext_w dst (d + len) f (mm_post d 0 f)
                     (fun j _ => eq_sym (mm_post_0 d f j)) with "Hw") as "Hw".
        iApply (wp_kgrep_mm_fwd dst d len f ltac:(lia) Hd0 Hd38 (len - 1)%nat 0%nat h7 m5 n
                  ltac:(lia)
                  ltac:(rewrite /m5 /m4 /m3 /m2; rgl; rewrite Ha11; f_equal; lia)
                  ltac:(rewrite /m5; rgl; f_equal; lia)
                  ltac:(rewrite /m5 /m4; rgl; reflexivity)
                  with "Hcode Hw Hrun").
        iIntros "Hw" (h8 mc) "%Hkc Hrun".
        iApply ("Htail" $! h8 mc with "Hw [] [] Hrun").
        * iPureIntro. eapply rkeep_trans; [ | refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity ].
          rewrite /m5 /m4 /m3 /m2. rk.
        * iPureIntro. rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite /m5 /m4 /m3 /m2. rgl. exact Hsp1'.
  Qed.
End UkGrepLib.
