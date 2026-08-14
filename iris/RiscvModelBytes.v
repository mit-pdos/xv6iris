(* ====================================================================== *)
(* RiscvModelBytes.v                                                       *)
(*                                                                         *)
(* Pure byte / bitvector arithmetic helpers underpinning the functional    *)
(* interpreter [exec] of RiscvModelExec.v.                                 *)
(*                                                                         *)
(* This file deliberately does NOT import any [iris.*] module.  That keeps  *)
(* the vanilla Coq [rewrite LEM by TAC] (and comma-chained [rewrite a, b])  *)
(* tactics available here -- importing [iris.program_logic.language]        *)
(* activates ssreflect's [rewrite], whose syntax is incompatible.           *)
(*                                                                         *)
(* [pa_add]/[nth_byte] are re-defined here with the *same bodies* as in     *)
(* RiscvModelLang.v, so they are definitionally equal (convertible) and     *)
(* RiscvModelExec.v can relate these lemmas to [run] by [unfold]/[change].  *)
(* ====================================================================== *)

From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import list_monad.

(* The tree-wide [set_solver] override.  It lives here, rather than in each  *)
(* file that uses [set_solver], because this file is a transitive dependency *)
(* of 1071 of the tree's 1090 proof files -- so a NEW proof gets the fast    *)
(* tactic without having to know it exists.  It adds no dependency this file *)
(* did not already have ([stdpp.gmap] above already pulls in [stdpp.sets]);  *)
(* the two set_solver-using files this does not reach (BitmapEnc.v and       *)
(* CrashProto.v) import FastSetSolver.v directly.  See FastSetSolver.v.      *)
(*                                                                          *)
(* EXPORT, NOT IMPORT, AND THAT IS LOAD-BEARING TWICE OVER: it is what makes *)
(* the override reach this file's importers at all, and it is what keeps the *)
(* nightly dead-import sweep (.github/workflows/dead-imports.yml) from       *)
(* deleting it.  By that sweep's definition this IS a dead import -- the     *)
(* tree compiles without it, only slower -- and the sweep pushes to main on  *)
(* its own; [Require Export] lines are skipped by default, which is the      *)
(* protection being relied on here.                                          *)
Require Export FastSetSolver.

Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.

Local Open Scope Z_scope.

(* Byte address [a + j] and byte [j] of a value -- SAME bodies as          *)
(* RiscvModelLang.pa_add / RiscvModelLang.nth_byte (kept convertible).      *)
Definition pa_add (a : Arch.pa) (j : nat) : Arch.pa := add_vec_int a (Z.of_nat j).
Definition nth_byte {m : N} (w : bv m) (j : nat) : bv 8 :=
  bv_extract (8 * N.of_nat j) 8 w.

(* ---------------------------------------------------------------------- *)
(* 0. Byte / bitvector facts.                                              *)
(* ---------------------------------------------------------------------- *)

(* unsigned value of the j-th byte of a word *)
Lemma nth_byte_unsigned {m : N} (w : bv m) (j : nat) :
  bv_unsigned (nth_byte w j) = (bv_unsigned w ≫ Z.of_N (8 * N.of_nat j)) `mod` 2 ^ 8.
Proof.
  unfold nth_byte. rewrite bv_extract_unsigned. unfold bv_wrap, bv_modulus.
  reflexivity.
Qed.

(* A word is determined by all its bytes (the key determinism enabler). *)
Lemma bv_eq_of_bytes {n : N} (w1 w2 : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N -> nth_byte w1 j = nth_byte w2 j) ->
  w1 = w2.
Proof.
  intros H. apply bv_eq. apply Z.bits_inj_iff. intros i.
  destruct (decide (0 <= i)) as [Hi|Hi].
  2:{ rewrite !Z.testbit_neg_r by lia. reflexivity. }
  pose proof (bv_unsigned_in_range _ w1) as [Hl1 Hh1].
  pose proof (bv_unsigned_in_range _ w2) as [Hl2 Hh2].
  unfold bv_modulus in Hh1, Hh2.
  destruct (decide (i < Z.of_N (8 * n))) as [Hlt|Hge].
  - (* in range: j := i/8 *)
    set (j := Z.to_nat (i / 8)).
    assert (Hd8 : 0 < 8) by lia.
    pose proof (Z.mod_pos_bound i 8 Hd8) as Hmb.
    assert (Hdp : 0 <= i / 8) by (apply Z.div_pos; lia).
    assert (Hjn : (N.of_nat j < n)%N).
    { subst j. apply N2Z.inj_lt.
      rewrite N2Z.inj_mul in Hlt.
      rewrite nat_N_Z, Z2Nat.id by exact Hdp.
      apply Z.div_lt_upper_bound; lia. }
    assert (Hr : Z.of_N (8 * N.of_nat j) = 8 * (i / 8)).
    { subst j. rewrite N2Z.inj_mul, nat_N_Z, Z2Nat.id by exact Hdp. lia. }
    specialize (H j Hjn). apply (f_equal bv_unsigned) in H.
    rewrite !nth_byte_unsigned, Hr in H.
    (* testbit w i = testbit ((w >> 8*(i/8)) mod 2^8) (i mod 8) *)
    assert (Hbit : forall w : bv (8 * n),
              Z.testbit (bv_unsigned w) i
              = Z.testbit ((bv_unsigned w ≫ (8 * (i / 8))) `mod` 2 ^ 8) (i `mod` 8)).
    { intros w. rewrite Z.mod_pow2_bits_low by lia.
      rewrite Z.shiftr_spec by lia. f_equal.
      pose proof (Z.div_mod i 8 ltac:(lia)). lia. }
    rewrite (Hbit w1), (Hbit w2), H. reflexivity.
  - (* out of range: both bits false (numbers are < 2^(8n)) *)
    assert (Hhigh : forall w : bv (8 * n),
              0 <= bv_unsigned w -> bv_unsigned w < 2 ^ Z.of_N (8 * n) ->
              Z.testbit (bv_unsigned w) i = false).
    { intros w Hw0 Hw. rewrite <- (Z.mod_small (bv_unsigned w) (2 ^ Z.of_N (8 * n))) by lia.
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
    rewrite (Hhigh w1 Hl1 Hh1), (Hhigh w2 Hl2 Hh2). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* little-endian assembly of a byte list (own fold; controllable spec).    *)
(* ---------------------------------------------------------------------- *)

Fixpoint assemble_bytes (bs : list (bv 8)) : Z :=
  match bs with
  | [] => 0
  | b :: bs' => bv_unsigned b + 2 ^ 8 * assemble_bytes bs'
  end.

Lemma assemble_bytes_bound bs :
  0 <= assemble_bytes bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs' IH]; simpl.
  - simpl. lia.
  - pose proof (bv_unsigned_in_range 8 b) as [Hl Hh]. unfold bv_modulus in Hh. simpl in Hh.
    rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat (length bs'))) with (8 + 8 * Z.of_nat (length bs')) by lia.
    rewrite Z.pow_add_r by lia. simpl (2^8). nia.
Qed.

Lemma assemble_bytes_byte bs (j : nat) :
  (j < length bs)%nat ->
  (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j).
Proof.
  revert j. induction bs as [|b bs' IH]; intros j Hj; simpl in Hj; [lia|].
  destruct j as [|j']; simpl assemble_bytes.
  - rewrite Nat.mul_0_r. simpl (Z.of_nat 0). rewrite Z.shiftr_0_r.
    pose proof (bv_unsigned_in_range 8 b) as [Hl Hh]. unfold bv_modulus in Hh. simpl in Hh.
    rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small by lia.
    reflexivity.
  - change ((b :: bs') !!! S j') with (bs' !!! j').
    replace (8 * S j')%nat with (8 + 8 * j')%nat by lia.
    rewrite Nat2Z.inj_add. rewrite <- Z.shiftr_shiftr by lia.
    assert (Hsh : (bv_unsigned b + 2 ^ 8 * assemble_bytes bs') ≫ Z.of_nat 8 = assemble_bytes bs').
    { pose proof (bv_unsigned_in_range 8 b) as [Hl Hh]. unfold bv_modulus in Hh. simpl in Hh.
      rewrite Z.shiftr_div_pow2 by lia. simpl (Z.of_nat 8).
      rewrite Z.mul_comm, Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b)) by lia. lia. }
    rewrite Hsh. apply IH. lia.
Qed.

(* ...and the converse of [bv_eq_of_bytes]: a word of ANY width at least as
   wide as the byte list reproduces those bytes.  This is how an EXISTENTIAL
   byte window is turned back into a word -- a fetched instruction word
   (UserFetchPt), a struct field carved out of a fresh page (PageFields), the
   two halves of a stack slot (InstrBytes' [word_of_words]).  The width-4 and
   width-8 instances are one line each off it; do not re-derive them. *)
Lemma nth_byte_assemble_len (m : N) (bs : list (bv 8)) (j : nat) :
  (8 * Z.of_nat (length bs) <= Z.of_N m) ->
  (j < length bs)%nat ->
  nth_byte (Z_to_bv m (assemble_bytes bs) : bv m) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi].
  assert (Hws : bv_wrap m (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus. split; [lia|].
    eapply Z.lt_le_trans; [exact Hhi|].
    apply Z.pow_le_mono_r; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
    by (apply assemble_bytes_byte; lia).
  rewrite <- Hab.
  f_equal. f_equal. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* read_bytes: gather n little-endian bytes from memory (None if missing). *)
(* ---------------------------------------------------------------------- *)

Definition read_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
  : option (bv (8 * n)) :=
  match mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n)) with
  | Some bs => Some (Z_to_bv (8 * n) (assemble_bytes bs))
  | None => None
  end.

Lemma read_bytes_spec mm pa n w :
  read_bytes mm pa n = Some w ->
  forall j : nat, (N.of_nat j < n)%N -> mm !! pa_add pa j = Some (nth_byte w j).
Proof.
  unfold read_bytes.
  destruct (mapM (fun j : nat => mm !! pa_add pa j) (seq 0 (N.to_nat n))) as [bs|] eqn:Hm;
    [|discriminate].
  intros [= <-] j Hj.
  apply mapM_Some_1 in Hm.
  pose proof (Forall2_length _ _ _ Hm) as Hlen. rewrite length_seq in Hlen.
  assert (Hjlt : (j < length bs)%nat) by (rewrite <- Hlen; lia).
  (* memory lookup = the j-th gathered byte *)
  assert (Hseq : seq 0 (N.to_nat n) !! j = Some j).
  { rewrite lookup_seq_lt by (rewrite <- Hlen in Hjlt; lia). f_equal. }
  destruct (Forall2_lookup_l _ _ _ j j Hm Hseq) as (b & Hbs & Hmm).
  rewrite Hmm. f_equal.
  (* nth_byte of the assembled word = the gathered byte *)
  assert (Hbb : bs !!! j = b) by (apply list_lookup_total_correct; exact Hbs).
  apply bv_eq. rewrite nth_byte_unsigned.
  (* keep going via unsigned *)
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  (* outer wrap (8*n) is identity on assemble_bytes (it is in range) *)
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite <- Hlen in Hhi.
  rewrite (Z.mod_small (assemble_bytes bs)); [| split; [lia| rewrite N2Z.inj_mul; lia ] ].
  pose proof (assemble_bytes_byte bs j Hjlt) as Hbyte.
  rewrite Nat2Z.inj_mul in Hbyte. change (Z.of_nat 8) with 8 in Hbyte.
  replace (Z.of_N (8 * N.of_nat j)) with (8 * Z.of_nat j) by (rewrite N2Z.inj_mul; lia).
  rewrite Hbyte, Hbb. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* write_bytes: the dual of read_bytes -- store the [n] little-endian      *)
(* bytes of [v] at [pa..pa+n).  Used by the MemWrite case of the           *)
(* interpreters so that multi-byte stores (e.g. [sd], width 8) are         *)
(* faithful (the previous handler wrote only byte 0).                       *)
(* ---------------------------------------------------------------------- *)
Definition write_bytes {w : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) (v : bv w)
  : gmap Arch.pa (bv 8) :=
  foldr (fun j acc => <[ pa_add pa j := nth_byte v j ]> acc) mm (seq 0 (N.to_nat n)).
