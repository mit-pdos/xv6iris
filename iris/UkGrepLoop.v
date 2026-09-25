(* ===================================================================== *)
(* UkGrepLoop.v -- grep(pattern, fd): the READ/SCAN/WRITE LOOP, walked    *)
(* against grep's interaction tree [GrepTree.grep_go].                    *)
(* (design: claude-notes/design/grep.md, section 3)                        *)
(*                                                                        *)
(*   0xf8   prologue: a 14-word frame, s0..s11 and ra spilled;            *)
(*          s8 = pattern, s9 = fd, s3 = skip, s6 = m, s10 = 1023,         *)
(*          s7 = buf, s5 = '\n', s11 = 1                                  *)
(*   0x16e  n = read(fd, buf + m, 1023 - m) ; blez n -> 0x1b2             *)
(*   0x180  m += n ; buf[m] = 0 ; p = buf                                  *)
(*   0x136  q = strchr(p, '\n') ; beqz q -> 0x16a                         *)
(*   0x142  *q = 0 ; skip -> 0x130 ; match(pattern, p) = 0 -> 0x130      *)
(*   0x154  *q = '\n' ; write(1, p, q + 1 - p)                            *)
(*   0x130  p = q + 1 ; skip = 0 ; back to 0x136                          *)
(*   0x16a  m > 0 (always) ; m -= p - buf ; memmove(buf, p, m) ;          *)
(*   0x1a8  m != 1023 -> 0x16e ; else skip = 1, m = 0, -> 0x16e          *)
(*   0x1b2  epilogue                                                      *)
(*                                                                        *)
(* THE INVARIANTS.  At the loop head (0x16e) the tree still owed is       *)
(* [grep_go pat fd skip [] left rest], the first [|left|] bytes of [buf]  *)
(* spell [left], [|left| < 1023], and s3/s6 hold [skip]/[|left|].  Inside *)
(* the scan (0x136) with [p = buf + i], the tree owed is [grep_k] (the    *)
(* read's continuation) at the SCAN OF THE REST OF THE BUFFER FROM [p]:   *)
(* one strchr/match step is one step of [scan] ([grep_k_step_*]).  The    *)
(* read's window is [buf + |left| .. buf + 1023); the last byte of [buf]  *)
(* is never read into, and the [buf[m] = 0] store lands at most on it.    *)
(*                                                                        *)
(* The reads and writes go to the tree's holes ([UkTree.rd_obl] /         *)
(* [wr_obl]) at the stubs, as [UkCatTree.kcat_round_tree] does.  The      *)
(* outer loop is unbounded and closes by Loeb at the [bne] at 0x1a8        *)
(* ([wp_uk_btype_later]); the scan is bounded by the buffer and closes by *)
(* induction on what is left of it.                                      *)
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
Require Import UserHeap UkStep UkRun UkRunLeaf UkRunMem UkRunBr UkRunSys.
Require Import VcGen.        (* [trunc32_mword_of_int] *)
Require Import UCodeGrep.
Require Import UkGrepLib UkGrepMatch.
Require Import LineWords ProgTree GrepTree.
Require Import CtxIdDefs.
Require User.GrepSyms User.GrepInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkTree.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(* §1 PURE: the scan, one line at a time.                                 *)
(* ===================================================================== *)

(* a byte strchr passes over: neither the newline nor the NUL *)
Definition gplain (b : bv 8) : Prop := b <> wl_nl /\ b <> c_nul.

Lemma bdec_false (a b : bv 8) : a <> b -> bdec a b = false.
Proof. intros H. unfold bdec. by apply bool_decide_eq_false. Qed.

Lemma bdec_true (a : bv 8) : bdec a a = true.
Proof. unfold bdec. by apply bool_decide_eq_true. Qed.

Lemma nul_ne_nl : c_nul <> wl_nl.
Proof. intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.

(* a run of plain bytes is carried into the line begun *)
Lemma scan_plain_app (pat : bytes) (sk : bool) (cur l r : bytes) :
  Forall gplain l -> scan pat sk cur (l ++ r) = scan pat sk (cur ++ l) r.
Proof.
  revert cur. induction l as [| b l IH]; intros cur Hl.
  - by rewrite app_nil_r.
  - inversion Hl as [| ? ? [Hn Hz] Hl']; subst.
    cbn [app scan]. rewrite (bdec_false _ _ Hn) (bdec_false _ _ Hz).
    rewrite (IH (cur ++ [b]) Hl'). by rewrite <- app_assoc.
Qed.

Lemma scan_line_nl (pat : bytes) (sk : bool) (line r : bytes) :
  Forall gplain line ->
  scan pat sk [] (line ++ wl_nl :: r)
  = ((if sk then [] else if match_re pat line then [line ++ [wl_nl]] else [])
       ++ (scan pat false [] r).1.1,
     (scan pat false [] r).1.2, (scan pat false [] r).2).
Proof.
  intros Hl. rewrite (scan_plain_app _ _ _ _ _ Hl). cbn [app scan].
  rewrite bdec_true. reflexivity.
Qed.

Lemma scan_line_stop (pat : bytes) (sk : bool) (line r : bytes) :
  Forall gplain line ->
  (r = [] \/ exists r', r = c_nul :: r') ->
  scan pat sk [] (line ++ r) = ([], line ++ r, sk).
Proof.
  intros Hl Hr. rewrite (scan_plain_app _ _ _ _ _ Hl). cbn [app].
  destruct Hr as [-> | [r' ->]].
  - by rewrite app_nil_r.
  - cbn [scan]. rewrite (bdec_false _ _ nul_ne_nl) bdec_true. reflexivity.
Qed.

(* the read's continuation and the rest of a round, as one function of
   the scan's result *)
Definition grep_k (pat : bytes) (fd : Z) (rest : proc)
    (sc : list bytes * bytes * bool) : proc :=
  if decide (grep_bufsz - 1 <= length sc.1.2)%nat
  then grep_go pat fd true sc.1.1 [] rest
  else grep_go pat fd sc.2 sc.1.1 sc.1.2 rest.

Definition grep_rk (pat : bytes) (fd : Z) (skip : bool) (left : bytes)
    (rest : proc) (a : rd_ans) : proc :=
  match a with
  | RdBytes (b :: bs) => grep_k pat fd rest (scan pat skip [] (left ++ b :: bs))
  | _ => rest
  end.

Lemma grep_go_read (pat : bytes) (fd : Z) (skip : bool) (left : bytes) (rest : proc) :
  grep_go pat fd skip [] left rest
  = Vis (ERead fd (grep_room left)) (grep_rk pat fd skip left rest).
Proof. rewrite grep_go_unfold. reflexivity. Qed.

Lemma grep_rk_bytes (pat : bytes) (fd : Z) (skip : bool) (left : bytes)
    (rest : proc) (l : bytes) :
  l <> [] ->
  grep_rk pat fd skip left rest (RdBytes l) = grep_k pat fd rest (scan pat skip [] (left ++ l)).
Proof. destruct l; [ done | reflexivity ]. Qed.

Lemma grep_k_cons (pat : bytes) (fd : Z) (rest : proc) (o : bytes) (os : list bytes)
    (l : bytes) (s : bool) :
  grep_k pat fd rest (o :: os, l, s)
  = Vis (EWrite 1 o) (fun _ => grep_k pat fd rest (os, l, s)).
Proof.
  unfold grep_k. cbn [fst snd].
  destruct (decide _); rewrite grep_go_unfold; reflexivity.
Qed.

Lemma grep_k_short (pat : bytes) (fd : Z) (rest : proc) (l : bytes) (s : bool) :
  (length l < 1023)%nat ->
  grep_k pat fd rest ([], l, s) = grep_go pat fd s [] l rest.
Proof.
  intros Hl. unfold grep_k. cbn [fst snd].
  destruct (decide _) as [Hd | _]; [ | reflexivity ].
  exfalso. unfold grep_bufsz in Hd. lia.
Qed.

Lemma grep_k_full (pat : bytes) (fd : Z) (rest : proc) (l : bytes) (s : bool) :
  length l = 1023%nat ->
  grep_k pat fd rest ([], l, s) = grep_go pat fd true [] [] rest.
Proof.
  intros Hl. unfold grep_k. cbn [fst snd].
  destruct (decide _) as [_ | Hd]; [ reflexivity | ].
  exfalso. unfold grep_bufsz in Hd. lia.
Qed.

(* ONE STEP OF THE SCAN, in the three arms the code takes at a newline *)
Lemma grep_k_step_skip (pat : bytes) (fd : Z) (rest : proc) (line r : bytes) :
  Forall gplain line ->
  grep_k pat fd rest (scan pat true [] (line ++ wl_nl :: r))
  = grep_k pat fd rest (scan pat false [] r).
Proof.
  intros Hl. rewrite (scan_line_nl _ _ _ _ Hl). cbn [app].
  by destruct (scan pat false [] r) as [[o l] s].
Qed.

Lemma grep_k_step_nomatch (pat : bytes) (fd : Z) (rest : proc) (line r : bytes) :
  Forall gplain line -> match_re pat line = false ->
  grep_k pat fd rest (scan pat false [] (line ++ wl_nl :: r))
  = grep_k pat fd rest (scan pat false [] r).
Proof.
  intros Hl Hm. rewrite (scan_line_nl _ _ _ _ Hl) Hm. cbn [app].
  by destruct (scan pat false [] r) as [[o l] s].
Qed.

Lemma grep_k_step_match (pat : bytes) (fd : Z) (rest : proc) (line r : bytes) :
  Forall gplain line -> match_re pat line = true ->
  grep_k pat fd rest (scan pat false [] (line ++ wl_nl :: r))
  = Vis (EWrite 1 (line ++ [wl_nl])) (fun _ => grep_k pat fd rest (scan pat false [] r)).
Proof.
  intros Hl Hm. rewrite (scan_line_nl _ _ _ _ Hl) Hm. cbn [app].
  rewrite grep_k_cons.
  by destruct (scan pat false [] r) as [[o l] s].
Qed.

(* ...and at the stop: the terminating NUL, or a NUL of the input *)
Lemma grep_k_step_stop (pat : bytes) (fd : Z) (rest : proc) (sk : bool) (line r : bytes) :
  Forall gplain line ->
  (r = [] \/ exists r', r = c_nul :: r') ->
  grep_k pat fd rest (scan pat sk [] (line ++ r)) = grep_k pat fd rest ([], line ++ r, sk).
Proof. intros Hl Hr. by rewrite (scan_line_stop _ _ _ _ Hl Hr). Qed.

(* ===================================================================== *)
(* §2 PURE: byte functions as lists.                                      *)
(* ===================================================================== *)

Lemma map_seq_shift {A : Type} (f : nat -> A) (s n : nat) :
  map f (seq s n) = map (fun j => f (s + j)%nat) (seq 0 n).
Proof.
  revert f s. induction n as [| n IH]; intros f s; [ reflexivity | ].
  cbn [List.seq List.map]. rewrite Nat.add_0_r. f_equal.
  rewrite (IH f (S s)) (IH (fun j => f (s + j)%nat) 1%nat).
  apply map_ext. intros j. f_equal. lia.
Qed.

Lemma map_seq_ext {A : Type} (f g : nat -> A) (n : nat) :
  (forall j : nat, (j < n)%nat -> f j = g j) -> map f (seq 0 n) = map g (seq 0 n).
Proof.
  intros H. apply map_ext_in. intros j Hj. apply in_seq in Hj. apply H. lia.
Qed.

Lemma map_seq_add {A : Type} (f : nat -> A) (a b : nat) :
  map f (seq 0 (a + b)) = map f (seq 0 a) ++ map (fun j => f (a + j)%nat) (seq 0 b).
Proof. rewrite seq_app map_app. f_equal. apply map_seq_shift. Qed.

Lemma map_seq_cut {A : Type} (f : nat -> A) (a b : nat) :
  map f (seq 0 (a + S b))
  = map f (seq 0 a) ++ f a :: map (fun j => f (a + 1 + j)%nat) (seq 0 b).
Proof.
  rewrite map_seq_add. f_equal. cbn [List.seq List.map]. rewrite Nat.add_0_r. f_equal.
  rewrite map_seq_shift. apply map_ext. intros j. f_equal. lia.
Qed.

Lemma forall_map_seq (P : bv 8 -> Prop) (f : nat -> bv 8) (k : nat) :
  (forall j : nat, (j < k)%nat -> P (f j)) -> Forall P (map f (seq 0 k)).
Proof.
  intros H. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as [j [<- Hj]]. apply in_seq in Hj. apply H. lia.
Qed.

(* THE STOP strchr finds: from [i], the first newline or NUL, which exists
   because the buffer is NUL-terminated at [mv] *)
Lemma first_stop (F : nat -> bv 8) (mv : nat) :
  F mv = c_nul ->
  forall (d i : nat), (i + d = mv)%nat ->
  exists k, (i + k <= mv)%nat /\
    (forall j : nat, (j < k)%nat -> gplain (F (i + j)%nat)) /\
    (F (i + k)%nat = wl_nl \/ F (i + k)%nat = c_nul).
Proof.
  intros Hm d. induction d as [| d IH]; intros i Hid.
  - exists 0%nat. split; [ lia | ]. split; [ intros; lia | ].
    right. rewrite Nat.add_0_r. replace i with mv by lia. exact Hm.
  - destruct (decide (F i = wl_nl)) as [Hn | Hn].
    { exists 0%nat. split; [ lia | ]. split; [ intros; lia | ]. left. by rewrite Nat.add_0_r. }
    destruct (decide (F i = c_nul)) as [Hz | Hz].
    { exists 0%nat. split; [ lia | ]. split; [ intros; lia | ]. right. by rewrite Nat.add_0_r. }
    destruct (IH (S i) ltac:(lia)) as (k & Hk & Hpl & Hst).
    exists (S k). split; [ lia | ]. split.
    + intros [| j] Hj.
      * rewrite Nat.add_0_r. split; assumption.
      * replace (i + S j)%nat with (S i + j)%nat by lia. apply Hpl. lia.
    + replace (i + S k)%nat with (S i + k)%nat by lia. exact Hst.
Qed.

(* the buffer after a read into the window [L, L + w) *)
Definition fread (F g : nat -> bv 8) (L w : nat) : nat -> bv 8 :=
  fun j => if Nat.ltb j L then F j else if Nat.ltb j (L + w) then g (j - L)%nat else F j.

(* ===================================================================== *)
(* §3 PURE: the arithmetic of grep's words.                               *)
(* ===================================================================== *)

Lemma add_vec32_unsigned' (x y : mword 32) :
  bv_unsigned (add_vec x y) = bv_wrap 32 (bv_unsigned x + bv_unsigned y).
Proof. exact (add_vec_unsigned x y). Qed.

(* addw at a result that fits: rd := x + y exactly *)
Lemma moi_addw_rr (x y : Z) :
  0 <= x + y < Z31 ->
  (sign_extend' 64
     (add_vec (subrange_vec_dec (mword_of_int x : mword 64) 31 0 : mword 32)
              (subrange_vec_dec (mword_of_int y : mword 64) 31 0 : mword 32))
   : mword 64)
  = mword_of_int (x + y).
Proof.
  intro H.
  assert (Hlow' : bv_unsigned
                    (add_vec (subrange_vec_dec (mword_of_int x : mword 64) 31 0 : mword 32)
                             (subrange_vec_dec (mword_of_int y : mword 64) 31 0 : mword 32))
                  = x + y).
  { rewrite add_vec32_unsigned' !low32_moi.
    unfold bv_wrap. rewrite Zmod32.
    rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r.
    apply Z.mod_small. unfold Z31, Z32 in *; lia. }
  rewrite (sext32_small
             (add_vec (subrange_vec_dec (mword_of_int x : mword 64) 31 0 : mword 32)
                      (subrange_vec_dec (mword_of_int y : mword 64) 31 0 : mword 32))
             ltac:(rewrite Hlow'; unfold Z31 in *; lia)).
  rewrite Hlow'. reflexivity.
Qed.

Lemma moi_of_sint' (r : mword 64) : (mword_of_int (bv_signed r) : mword 64) = r.
Proof.
  apply bv_eq. rewrite moi64_unsigned.
  change (bv_signed r) with (bv_swrap 64 (bv_unsigned r)).
  unfold bv_swrap, bv_wrap.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned r + bv_half_modulus 64 - bv_half_modulus 64)
    with (bv_unsigned r) by lia.
  apply Z.mod_small. exact (bv_unsigned_in_range 64 r).
Qed.

(* a small count read back as the C [int] the kernel reads *)
Lemma cint_moi_small' (z : Z) :
  0 <= z < 2 ^ 31 -> bv_signed (trunc32 (mword_of_int z : mword 64)) = z.
Proof.
  intros Hz. rewrite trunc32_mword_of_int.
  assert (Hbw : bv_wrap 32 z = z) by (apply bvw32_small; lia).
  unfold bv_signed. rewrite moi32_unsigned Hbw.
  apply bv_swrap_small.
  assert (Hh32 : bv_half_modulus 32 = 2147483648%Z) by (vm_compute; reflexivity).
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite Hh32. lia.
Qed.

Lemma nth_byte_zero0 : nth_byte (zero_reg : mword 64) 0 = ubyte0.
Proof. vm_compute. reflexivity. Qed.

Lemma nth_byte_moi10 : nth_byte (mword_of_int 10 : mword 64) 0 = wl_nl.
Proof. vm_compute. reflexivity. Qed.

Lemma wl_nl_unsigned : bv_unsigned wl_nl = 10.
Proof. vm_compute. reflexivity. Qed.

Definition b01 (b : bool) : Z := if b then 1 else 0.

(* THE STACK A CALL OF grep NEEDS: its 14-word frame, then match's (the
   deepest callee; strchr and memmove need 2 words, the stubs none) *)
Definition grep_words (pat : list (bv 8)) : nat :=
  (14 + (4 + mh_words (match pat with
                       | c :: r => if GrepTree.bdec c GrepTree.c_caret then r else c :: r
                       | [] => []
                       end)))%nat.

Definition grep_body (pat : list (bv 8)) : list (bv 8) :=
  match pat with
  | c :: r => if GrepTree.bdec c GrepTree.c_caret then r else c :: r
  | [] => []
  end.

(* ===================================================================== *)
(* §4 PURE: the buffer's contents, as the scan reads them.                *)
(* ===================================================================== *)

Lemma fread_lo (F g : nat -> bv 8) (L w j : nat) : (j < L)%nat -> fread F g L w j = F j.
Proof. intros Hj. unfold fread. destruct (Nat.ltb_spec j L); [ reflexivity | lia ]. Qed.

Lemma fread_mid (F g : nat -> bv 8) (L w j : nat) :
  (j < w)%nat -> fread F g L w (L + j) = g j.
Proof.
  intros Hj. unfold fread.
  destruct (Nat.ltb_spec (L + j) L); [ lia | ].
  destruct (Nat.ltb_spec (L + j) (L + w)); [ | lia ].
  f_equal. lia.
Qed.

Lemma fread_hi (F g : nat -> bv 8) (L w j : nat) :
  fread F g L w (L + w + j) = F (L + w + j)%nat.
Proof.
  unfold fread.
  destruct (Nat.ltb_spec (L + w + j) L); [ lia | ].
  destruct (Nat.ltb_spec (L + w + j) (L + w)); [ lia | reflexivity ].
Qed.

(* what the scan sees after the read and the [buf[m] = 0] store *)
Lemma head_bytes (F g : nat -> bv 8) (L w nb : nat) (left : bytes) (b : bv 8) :
  map F (seq 0 L) = left -> (nb <= w)%nat ->
  map (fun j => fset (fread F g L w) (L + nb) b (0 + j)%nat) (seq 0 (L + nb - 0))
  = left ++ map g (seq 0 nb).
Proof.
  intros Hl Hnb. replace (L + nb - 0)%nat with (L + nb)%nat by lia.
  rewrite map_seq_add. f_equal.
  - rewrite <- Hl. apply map_seq_ext. intros j Hj. cbn [Nat.add].
    unfold fset. rewrite (proj2 (Nat.eqb_neq j (L + nb)) ltac:(lia)).
    apply fread_lo. exact Hj.
  - apply map_seq_ext. intros j Hj. cbn [Nat.add].
    unfold fset. rewrite (proj2 (Nat.eqb_neq (L + j) (L + nb)) ltac:(lia)).
    apply fread_mid. lia.
Qed.

Lemma rd_ans_of_pos (ret : mword 64) (g : nat -> bv 8) (nb : nat) :
  bv_signed ret = Z.of_nat nb -> rd_ans_of ret g = RdBytes (map g (seq 0 nb)).
Proof.
  intros H. unfold rd_ans_of. destruct (decide (bv_signed ret < 0)); [ lia | ].
  rewrite H Nat2Z.id. reflexivity.
Qed.

Lemma grep_rk_nonpos (pat : bytes) (fd : Z) (skip : bool) (left : bytes) (rest : proc)
    (ret : mword 64) (g : nat -> bv 8) :
  bv_signed ret <= 0 -> grep_rk pat fd skip left rest (rd_ans_of ret g) = rest.
Proof.
  intros H. unfold rd_ans_of. destruct (decide (bv_signed ret < 0)); [ reflexivity | ].
  replace (Z.to_nat (bv_signed ret)) with 0%nat by lia. reflexivity.
Qed.

(* the rest of the buffer from [i], cut at the stop [k] *)
Lemma S_split (F : nat -> bv 8) (i k mv : nat) :
  (i + k < mv)%nat ->
  map (fun j => F (i + j)%nat) (seq 0 (mv - i))
  = map (fun j => F (i + j)%nat) (seq 0 k)
      ++ F (i + k)%nat :: map (fun j => F (i + k + 1 + j)%nat) (seq 0 (mv - (i + k + 1))).
Proof.
  intros H. replace (mv - i)%nat with (k + S (mv - (i + k + 1)))%nat by lia.
  rewrite map_seq_cut. f_equal. f_equal. apply map_ext. intros j. f_equal. lia.
Qed.

Lemma line_plain (F : nat -> bv 8) (i k : nat) :
  (forall j : nat, (j < k)%nat -> gplain (F (i + j)%nat)) ->
  Forall gplain (map (fun j => F (i + j)%nat) (seq 0 k)).
Proof. intros H. apply (forall_map_seq gplain (fun j => F (i + j)%nat) k H). Qed.

Section scan_S.
  Context (pat : bytes) (fd : Z) (rest : proc) (F : nat -> bv 8) (i k mv : nat).
  Hypothesis Hpl : forall j : nat, (j < k)%nat -> gplain (F (i + j)%nat).
  Local Notation S := (map (fun j => F (i + j)%nat) (seq 0 (mv - i))).
  Local Notation S' := (map (fun j => F (i + k + 1 + j)%nat) (seq 0 (mv - (i + k + 1)))).
  Local Notation line := (map (fun j => F (i + j)%nat) (seq 0 k)).

  Lemma grep_k_stop_S (sk : bool) :
    (i + k <= mv)%nat -> F (i + k)%nat = c_nul ->
    grep_k pat fd rest (scan pat sk [] S) = grep_k pat fd rest ([], S, sk).
  Proof using Hpl.
    intros Hk Hz. destruct (Nat.eq_dec (i + k) mv) as [He | Hne].
    - replace (mv - i)%nat with k by lia.
      rewrite -(app_nil_r (map _ (seq 0 k))).
      apply grep_k_step_stop; [ apply line_plain; exact Hpl | by left ].
    - rewrite (S_split F i k mv ltac:(lia)) Hz.
      apply grep_k_step_stop; [ apply line_plain; exact Hpl | right; by eexists ].
  Qed.

  Lemma grep_k_skip_S :
    (i + k < mv)%nat -> F (i + k)%nat = wl_nl ->
    grep_k pat fd rest (scan pat true [] S) = grep_k pat fd rest (scan pat false [] S').
  Proof using Hpl.
    intros Hk Hn. rewrite (S_split F i k mv Hk) Hn.
    apply grep_k_step_skip. apply line_plain; exact Hpl.
  Qed.

  Lemma grep_k_nomatch_S :
    (i + k < mv)%nat -> F (i + k)%nat = wl_nl -> match_re pat line = false ->
    grep_k pat fd rest (scan pat false [] S) = grep_k pat fd rest (scan pat false [] S').
  Proof using Hpl.
    intros Hk Hn Hm. rewrite (S_split F i k mv Hk) Hn.
    apply grep_k_step_nomatch; [ apply line_plain; exact Hpl | exact Hm ].
  Qed.

  Lemma grep_k_match_S :
    (i + k < mv)%nat -> F (i + k)%nat = wl_nl -> match_re pat line = true ->
    grep_k pat fd rest (scan pat false [] S)
    = Vis (EWrite 1 (line ++ [wl_nl])) (fun _ => grep_k pat fd rest (scan pat false [] S')).
  Proof using Hpl.
    intros Hk Hn Hm. rewrite (S_split F i k mv Hk) Hn.
    apply grep_k_step_match; [ apply line_plain; exact Hpl | exact Hm ].
  Qed.
End scan_S.

(* a store at the stop leaves the rest of the buffer alone *)
Lemma S'_fset (F : nat -> bv 8) (x n : nat) (b : bv 8) :
  map (fun j => fset F x b (x + 1 + j)%nat) (seq 0 n)
  = map (fun j => F (x + 1 + j)%nat) (seq 0 n).
Proof.
  apply map_seq_ext. intros j _. unfold fset.
  rewrite (proj2 (Nat.eqb_neq (x + 1 + j) x) ltac:(lia)). reflexivity.
Qed.

(* the line and its newline, as the write hole reads them *)
Lemma bytes_of_line (F : nat -> bv 8) (i k : nat) :
  F (i + k)%nat = wl_nl ->
  bytes_of (map (fun j => F (i + j)%nat) (seq 0 k) ++ [wl_nl]) (fun j => F (i + j)%nat).
Proof.
  intros Hn j Hj.
  assert (E : map (fun j => F (i + j)%nat) (seq 0 k) ++ [wl_nl]
              = map (fun j => F (i + j)%nat) (seq 0 (S k))).
  { rewrite seq_S map_app /=. rewrite Hn. reflexivity. }
  rewrite E. rewrite E length_map length_seq in Hj.
  exact (map_seq_lookup (fun j => F (i + j)%nat) (S k) j Hj).
Qed.

Lemma length_line (F : nat -> bv 8) (i k : nat) :
  length (map (fun j => F (i + j)%nat) (seq 0 k) ++ [wl_nl]) = S k.
Proof. rewrite length_app length_map length_seq /=. lia. Qed.

(* every callee-saved register listed is back: the return, decided *)
Lemma ucallee_saved_of_list (m0 m' : regfile) :
  (forall k : Z, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
     m' !!! Regidx (mword_of_int k) = m0 !!! Regidx (mword_of_int k)) ->
  ucallee_saved m0 m'.
Proof.
  intros H r Hr. destruct (mword5_cases r) as [k [Hk ->]]. apply H.
  assert (Hdec : forallb (fun k => implb (ucallee_saved_idx (mword_of_int k))
                                   (existsb (Z.eqb k) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]))
                   (map Z.of_nat (seq 0 32)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hdec.
  assert (Hin : In k (map Z.of_nat (seq 0 32))).
  { apply in_map_iff. exists (Z.to_nat k). split; [ lia | ]. apply in_seq. lia. }
  specialize (Hdec k Hin). rewrite Hr in Hdec.
  change (implb true ?b) with b in Hdec.
  apply existsb_exists in Hdec as [z [Hz Hze]]. apply Z.eqb_eq in Hze. subst z. exact Hz.
Qed.

Section UkGrepLoop.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation x3_idx := (mword_of_int 3 : mword 5).
  Local Notation x4_idx := (mword_of_int 4 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).
  Local Notation gbuf := GrepSyms.buf.

  (* grep's instance: its code and its five stubs *)
  Definition grep_prog : uprog Σ :=
    MkUprog Σ (grep_code γt) GrepSyms.write GrepSyms.read GrepSyms.open
      GrepSyms.close GrepSyms.exit.

  Local Notation tp := (tree_pay N grep_prog).

  (* ------------------------------------------------------------------- *)
  (* x0 as a VALUE: the [sb zero] stores read it (as [UkSh.urun_x0])     *)
  (* ------------------------------------------------------------------- *)
  Local Lemma urun_x0 (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat) :
    urun N h m pc avail -∗
    ⌜ m !!! Regidx x0_idx = zero_reg ⌝ ∗ urun N h m pc avail.
  Proof using .
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv, cw, gn, cs, pidv.
    iFrame "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hb".
    iPureIntro. split_and!; [ exact Hlo | exact Hpm | exact Hlzf | exact HRut ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE BUFFER, in three runs and back                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma ubytes_open3 (a : Z) (x y z : nat) (F : nat -> bv 8) :
    ubytes γd a (x + y + z) F -∗
    ubytes γd a x F ∗ ubytes γd (a + Z.of_nat x) y (fun j => F (x + j)%nat) ∗
    ubytes γd (a + Z.of_nat x + Z.of_nat y) z (fun j => F (x + y + j)%nat).
  Proof using .
    iIntros "H". rewrite -Nat.add_assoc.
    iDestruct (ubytes_app with "H") as "[$ H]".
    iDestruct (ubytes_app with "H") as "[$ H]".
    iApply (ubytes_ext_w with "H"). intros j _. f_equal. lia.
  Qed.

  Lemma ubytes_close3 (a : Z) (x y z : nat) (F f1 f2 f3 : nat -> bv 8) :
    (forall j, (j < x)%nat -> F j = f1 j) ->
    (forall j, (j < y)%nat -> F (x + j)%nat = f2 j) ->
    (forall j, (j < z)%nat -> F (x + y + j)%nat = f3 j) ->
    ubytes γd a x f1 -∗ ubytes γd (a + Z.of_nat x) y f2 -∗
    ubytes γd (a + Z.of_nat x + Z.of_nat y) z f3 -∗
    ubytes γd a (x + y + z) F.
  Proof using .
    intros H1 H2 H3. iIntros "A B C". rewrite -Nat.add_assoc.
    iApply ubytes_app. iSplitL "A".
    { iApply (ubytes_ext_w with "A"). intros j Hj. symmetry. by apply H1. }
    iApply ubytes_app. iSplitL "B".
    { iApply (ubytes_ext_w with "B"). intros j Hj. symmetry. by apply H2. }
    iApply (ubytes_ext_w with "C"). intros j Hj. rewrite -H3; [ | done ]. f_equal. lia.
  Qed.

  Lemma ubytes_close3' (a : Z) (x y z n : nat) (F f1 f2 f3 : nat -> bv 8) :
    (x + y + z = n)%nat ->
    (forall j, (j < x)%nat -> F j = f1 j) ->
    (forall j, (j < y)%nat -> F (x + j)%nat = f2 j) ->
    (forall j, (j < z)%nat -> F (x + y + j)%nat = f3 j) ->
    ubytes γd a x f1 -∗ ubytes γd (a + Z.of_nat x) y f2 -∗
    ubytes γd (a + Z.of_nat x + Z.of_nat y) z f3 -∗
    ubytes γd a n F.
  Proof using .
    intros <- H1 H2 H3. iIntros "A B C".
    iApply (ubytes_close3 with "A B C"); assumption.
  Qed.

  (* a run and the byte after it *)
  Lemma ubytes_snoc_open (a : Z) (k : nat) (f : nat -> bv 8) :
    ubytes γd a (S k) f -∗ ubytes γd a k f ∗ ubyte γd (a + Z.of_nat k) (f k).
  Proof using .
    iIntros "H". rewrite -Nat.add_1_r.
    iDestruct (ubytes_app with "H") as "[$ H]".
    rewrite /ubytes /ubytesq /=. rewrite Nat.add_0_r Z.add_0_r.
    iDestruct "H" as "[$ _]".
  Qed.

  Lemma ubytes_snoc_close (a : Z) (k : nat) (f : nat -> bv 8) (b : bv 8) :
    f k = b ->
    ubytes γd a k f -∗ ubyte γd (a + Z.of_nat k) b -∗ ubytes γd a (S k) f.
  Proof using .
    intros Hb. iIntros "H Hb". rewrite -Nat.add_1_r.
    iApply ubytes_app. iFrame "H".
    rewrite /ubytes /ubytesq /=. rewrite Nat.add_0_r Z.add_0_r Hb. iFrame.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE FRAME: fourteen words, thirteen of them spills                   *)
  (* ------------------------------------------------------------------- *)
  Lemma ustack_14_open (sp : mword 64) :
    ustack γd sp 14 -∗
      ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 40) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 48) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 56) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 64) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 72) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 80) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 88) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 96) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 104) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 112) w).
  Proof using .
    rewrite /ustack /ustack_body /=.
    assert (E0 : uint sp - 8 * (Z.of_nat 0 + 1) = uint sp - 8) by lia.
    assert (E1 : uint sp - 8 * (Z.of_nat 1 + 1) = uint sp - 16) by lia.
    assert (E2 : uint sp - 8 * (Z.of_nat 2 + 1) = uint sp - 24) by lia.
    assert (E3 : uint sp - 8 * (Z.of_nat 3 + 1) = uint sp - 32) by lia.
    assert (E4 : uint sp - 8 * (Z.of_nat 4 + 1) = uint sp - 40) by lia.
    assert (E5 : uint sp - 8 * (Z.of_nat 5 + 1) = uint sp - 48) by lia.
    assert (E6 : uint sp - 8 * (Z.of_nat 6 + 1) = uint sp - 56) by lia.
    assert (E7 : uint sp - 8 * (Z.of_nat 7 + 1) = uint sp - 64) by lia.
    assert (E8 : uint sp - 8 * (Z.of_nat 8 + 1) = uint sp - 72) by lia.
    assert (E9 : uint sp - 8 * (Z.of_nat 9 + 1) = uint sp - 80) by lia.
    assert (E10 : uint sp - 8 * (Z.of_nat 10 + 1) = uint sp - 88) by lia.
    assert (E11 : uint sp - 8 * (Z.of_nat 11 + 1) = uint sp - 96) by lia.
    assert (E12 : uint sp - 8 * (Z.of_nat 12 + 1) = uint sp - 104) by lia.
    assert (E13 : uint sp - 8 * (Z.of_nat 13 + 1) = uint sp - 112) by lia.
    rewrite E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 right_id.
    iIntros "H". iExact "H".
  Qed.

  Lemma ustack_14_close (sp : mword 64) :
    uint sp mod 8 = 0 ->
    (∃ w : mword 64, uword γd (uint sp - 8) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 16) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 24) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 32) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 40) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 64) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 72) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 80) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 96) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 104) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 112) w) -∗
    ustack γd sp 14.
  Proof using .
    intros Hal. iIntros "H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13".
    rewrite /ustack /ustack_body /=.
    assert (E0 : uint sp - 8 * (Z.of_nat 0 + 1) = uint sp - 8) by lia.
    assert (E1 : uint sp - 8 * (Z.of_nat 1 + 1) = uint sp - 16) by lia.
    assert (E2 : uint sp - 8 * (Z.of_nat 2 + 1) = uint sp - 24) by lia.
    assert (E3 : uint sp - 8 * (Z.of_nat 3 + 1) = uint sp - 32) by lia.
    assert (E4 : uint sp - 8 * (Z.of_nat 4 + 1) = uint sp - 40) by lia.
    assert (E5 : uint sp - 8 * (Z.of_nat 5 + 1) = uint sp - 48) by lia.
    assert (E6 : uint sp - 8 * (Z.of_nat 6 + 1) = uint sp - 56) by lia.
    assert (E7 : uint sp - 8 * (Z.of_nat 7 + 1) = uint sp - 64) by lia.
    assert (E8 : uint sp - 8 * (Z.of_nat 8 + 1) = uint sp - 72) by lia.
    assert (E9 : uint sp - 8 * (Z.of_nat 9 + 1) = uint sp - 80) by lia.
    assert (E10 : uint sp - 8 * (Z.of_nat 10 + 1) = uint sp - 88) by lia.
    assert (E11 : uint sp - 8 * (Z.of_nat 11 + 1) = uint sp - 96) by lia.
    assert (E12 : uint sp - 8 * (Z.of_nat 12 + 1) = uint sp - 104) by lia.
    assert (E13 : uint sp - 8 * (Z.of_nat 13 + 1) = uint sp - 112) by lia.
    rewrite E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 right_id.
    iSplit; [ iPureIntro; exact Hal | ].
    iSplitL "H0"; [iExact "H0"|]. iSplitL "H1"; [iExact "H1"|].
    iSplitL "H2"; [iExact "H2"|]. iSplitL "H3"; [iExact "H3"|].
    iSplitL "H4"; [iExact "H4"|]. iSplitL "H5"; [iExact "H5"|].
    iSplitL "H6"; [iExact "H6"|]. iSplitL "H7"; [iExact "H7"|].
    iSplitL "H8"; [iExact "H8"|]. iSplitL "H9"; [iExact "H9"|].
    iSplitL "H10"; [iExact "H10"|]. iSplitL "H11"; [iExact "H11"|].
    iSplitL "H12"; [iExact "H12"|]. iExact "H13".
  Qed.

  (* the thirteen spills and the one free word, as the loop leaves them *)
  Definition gframe (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) ∗
     uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) ∗
     uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) ∗
     uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) ∗
     uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) ∗
     uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) ∗
     uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) ∗
     uword γd (uint sp0 - 64) (m0 !!! Regidx s6_idx) ∗
     uword γd (uint sp0 - 72) (m0 !!! Regidx s7_idx) ∗
     uword γd (uint sp0 - 80) (m0 !!! Regidx s8_idx) ∗
     uword γd (uint sp0 - 88) (m0 !!! Regidx s9_idx) ∗
     uword γd (uint sp0 - 96) (m0 !!! Regidx s10_idx) ∗
     uword γd (uint sp0 - 104) (m0 !!! Regidx s11_idx) ∗
     (∃ w : mword 64, uword γd (uint sp0 - 112) w))%I.

  (* ------------------------------------------------------------------- *)
  (* THE REGISTERS THE LOOP PINS: sp, gp, tp (never written), and the    *)
  (* six callee-saved constants the prologue loads                        *)
  (* ------------------------------------------------------------------- *)
  Definition gl_regs (m0 : regfile) (sp0 : mword 64) (ar : Z) (fdv : mword 64)
      (m : regfile) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 14)) /\
    m !!! Regidx x3_idx = m0 !!! Regidx x3_idx /\
    m !!! Regidx x4_idx = m0 !!! Regidx x4_idx /\
    m !!! Regidx s5_idx = mword_of_int 10 /\
    m !!! Regidx s7_idx = mword_of_int gbuf /\
    m !!! Regidx s8_idx = mword_of_int ar /\
    m !!! Regidx s9_idx = fdv /\
    m !!! Regidx s10_idx = mword_of_int 1023 /\
    m !!! Regidx s11_idx = mword_of_int 1.

  Lemma gl_regs_keep (W : list Z) (m0 : regfile) (sp0 : mword 64) (ar : Z)
      (fdv : mword 64) (m m' : regfile) :
    rin W csp_rs1 = false -> rin W x3_idx = false -> rin W x4_idx = false ->
    rin W s5_idx = false -> rin W s7_idx = false -> rin W s8_idx = false ->
    rin W s9_idx = false -> rin W s10_idx = false -> rin W s11_idx = false ->
    rkeep W m m' -> gl_regs m0 sp0 ar fdv m -> gl_regs m0 sp0 ar fdv m'.
  Proof using .
    intros H1 H2 H3 H4 H5 H6 H7 H8 H9 Hk (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    rewrite /gl_regs (Hk _ H1) (Hk _ H2) (Hk _ H3) (Hk _ H4) (Hk _ H5) (Hk _ H6)
      (Hk _ H7) (Hk _ H8) (Hk _ H9).
    auto 10.
  Qed.

  Lemma gl_regs_call (m0 : regfile) (sp0 : mword 64) (ar : Z) (fdv : mword 64)
      (m m' : regfile) :
    ucallee_saved m m' -> gl_regs m0 sp0 ar fdv m -> gl_regs m0 sp0 ar fdv m'.
  Proof using .
    intros Hcs (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    rewrite /gl_regs (Hcs csp_rs1 ltac:(vm_compute; reflexivity))
      (Hcs x3_idx ltac:(vm_compute; reflexivity))
      (Hcs x4_idx ltac:(vm_compute; reflexivity))
      (Hcs s5_idx ltac:(vm_compute; reflexivity))
      (Hcs s7_idx ltac:(vm_compute; reflexivity))
      (Hcs s8_idx ltac:(vm_compute; reflexivity))
      (Hcs s9_idx ltac:(vm_compute; reflexivity))
      (Hcs s10_idx ltac:(vm_compute; reflexivity))
      (Hcs s11_idx ltac:(vm_compute; reflexivity)).
    auto 10.
  Qed.

  (* ===================================================================== *)
  (* THE PROLOGUE, 0xf8..0x12e: the frame, the thirteen spills, and the   *)
  (* six constants the loop keeps in callee-saved registers.              *)
  (* ===================================================================== *)
  Lemma wp_kgl_pro (h : CpuId) (m : regfile) (ar : Z) (fdv : mword 64) (n2 : nat) :
    m !!! Regidx a0_idx = mword_of_int ar ->
    m !!! Regidx a1_idx = fdv ->
    grep_code γt -∗
    urun N h m (mword_of_int GrepSyms.grep) (14 + (4 + n2)) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 112 <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ gl_regs m (m !!! Regidx csp_rs1) ar fdv m' ⌝ -∗
       ⌜ m' !!! Regidx s3_idx = mword_of_int (b01 false) ⌝ -∗
       ⌜ m' !!! Regidx s6_idx = mword_of_int (Z.of_nat 0) ⌝ -∗
       gframe (m !!! Regidx csp_rs1) m -∗
       urun N h' m' (mword_of_int 0x16e) (4 + n2) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1. iIntros "#Hcode Hrun Hcont".
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 112 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 14)))
                   = bv_unsigned sp0 - 112).
    { replace (- (8 * Z.of_nat 14)) with (-112) by lia.
      exact (uv_avi_neg sp0 112 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp112 : uint (add_vec_int sp0 (- (8 * Z.of_nat 14))) = uint sp0 - 112)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho104 : uoff_sdsp (mword_of_int 13 : mword 6) = 104) by (vm_compute; reflexivity).
    assert (Ho96 : uoff_sdsp (mword_of_int 12 : mword 6) = 96) by (vm_compute; reflexivity).
    assert (Ho88 : uoff_sdsp (mword_of_int 11 : mword 6) = 88) by (vm_compute; reflexivity).
    assert (Ho80 : uoff_sdsp (mword_of_int 10 : mword 6) = 80) by (vm_compute; reflexivity).
    assert (Ho72 : uoff_sdsp (mword_of_int 9 : mword 6) = 72) by (vm_compute; reflexivity).
    assert (Ho64 : uoff_sdsp (mword_of_int 8 : mword 6) = 64) by (vm_compute; reflexivity).
    assert (Ho56 : uoff_sdsp (mword_of_int 7 : mword 6) = 56) by (vm_compute; reflexivity).
    assert (Ho48 : uoff_sdsp (mword_of_int 6 : mword 6) = 48) by (vm_compute; reflexivity).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40) by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32) by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24) by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16) by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8) by (vm_compute; reflexivity).
    rewrite /GrepSyms.grep.
    (* ---- 0xf8  c.addi16sp sp,sp,-112 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0xf8) (mword_of_int 57 : mword 6) 14 (4 + n2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_f8 with "Hcode"). }
    rewrite Hsp. iIntros "Hst" (h1) "Hrun". pcn.
    iDestruct (ustack_14_open with "Hst")
      as "(_ & [%w1 Hw1] & [%w2 Hw2] & [%w3 Hw3] & [%w4 Hw4] & [%w5 Hw5] & [%w6 Hw6]
             & [%w7 Hw7] & [%w8 Hw8] & [%w9 Hw9] & [%w10 Hw10] & [%w11 Hw11]
             & [%w12 Hw12] & [%w13 Hw13] & Hw14)".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 14)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 14)))
      by (rewrite /m1; rgl; reflexivity).
    (* ---- 0xfa..0x112  the thirteen spills ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0xfa) (mword_of_int 13 : mword 6) ra_idx
              (uint sp0 - 8) w1 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho104; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_grep_fa with "Hcode"). }
    iIntros "Hw1" (h2) "Hrun". pcn.
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0xfc) (mword_of_int 12 : mword 6) s0_idx
              (uint sp0 - 16) w2 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho96; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_grep_fc with "Hcode"). }
    iIntros "Hw2" (h3) "Hrun". pcn.
    iApply (wp_uk_csdsp N h3 m1 (mword_of_int 0xfe) (mword_of_int 11 : mword 6) s1_idx
              (uint sp0 - 24) w3 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho88; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_grep_fe with "Hcode"). }
    iIntros "Hw3" (h4) "Hrun". pcn.
    iApply (wp_uk_csdsp N h4 m1 (mword_of_int 0x100) (mword_of_int 10 : mword 6) s2_idx
              (uint sp0 - 32) w4 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho80; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_grep_100 with "Hcode"). }
    iIntros "Hw4" (h5) "Hrun". pcn.
    iApply (wp_uk_csdsp N h5 m1 (mword_of_int 0x102) (mword_of_int 9 : mword 6) s3_idx
              (uint sp0 - 40) w5 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho72; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_grep_102 with "Hcode"). }
    iIntros "Hw5" (h6) "Hrun". pcn.
    iApply (wp_uk_csdsp N h6 m1 (mword_of_int 0x104) (mword_of_int 8 : mword 6) s4_idx
              (uint sp0 - 48) w6 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho64; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_grep_104 with "Hcode"). }
    iIntros "Hw6" (h7) "Hrun". pcn.
    iApply (wp_uk_csdsp N h7 m1 (mword_of_int 0x106) (mword_of_int 7 : mword 6) s5_idx
              (uint sp0 - 56) w7 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho56; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_grep_106 with "Hcode"). }
    iIntros "Hw7" (h8) "Hrun". pcn.
    iApply (wp_uk_csdsp N h8 m1 (mword_of_int 0x108) (mword_of_int 6 : mword 6) s6_idx
              (uint sp0 - 64) w8 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho48; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_grep_108 with "Hcode"). }
    iIntros "Hw8" (h9) "Hrun". pcn.
    iApply (wp_uk_csdsp N h9 m1 (mword_of_int 0x10a) (mword_of_int 5 : mword 6) s7_idx
              (uint sp0 - 72) w9 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho40; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw9 Hrun").
    { iApply (uis_grep_10a with "Hcode"). }
    iIntros "Hw9" (h10) "Hrun". pcn.
    iApply (wp_uk_csdsp N h10 m1 (mword_of_int 0x10c) (mword_of_int 4 : mword 6) s8_idx
              (uint sp0 - 80) w10 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho32; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw10 Hrun").
    { iApply (uis_grep_10c with "Hcode"). }
    iIntros "Hw10" (h11) "Hrun". pcn.
    iApply (wp_uk_csdsp N h11 m1 (mword_of_int 0x10e) (mword_of_int 3 : mword 6) s9_idx
              (uint sp0 - 88) w11 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho24; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw11 Hrun").
    { iApply (uis_grep_10e with "Hcode"). }
    iIntros "Hw11" (h12) "Hrun". pcn.
    iApply (wp_uk_csdsp N h12 m1 (mword_of_int 0x110) (mword_of_int 2 : mword 6) s10_idx
              (uint sp0 - 96) w12 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho16; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw12 Hrun").
    { iApply (uis_grep_110 with "Hcode"). }
    iIntros "Hw12" (h13) "Hrun". pcn.
    iApply (wp_uk_csdsp N h13 m1 (mword_of_int 0x112) (mword_of_int 1 : mword 6) s11_idx
              (uint sp0 - 104) w13 (4 + n2)
              ltac:(rewrite Hsp1 Hsp112 Ho8; lia) ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw13 Hrun").
    { iApply (uis_grep_112 with "Hcode"). }
    iIntros "Hw13" (h14) "Hrun". pcn.
    assert (Er1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er2 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er3 : m1 !!! Regidx s1_idx = m !!! Regidx s1_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er4 : m1 !!! Regidx s2_idx = m !!! Regidx s2_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er5 : m1 !!! Regidx s3_idx = m !!! Regidx s3_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er6 : m1 !!! Regidx s4_idx = m !!! Regidx s4_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er7 : m1 !!! Regidx s5_idx = m !!! Regidx s5_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er8 : m1 !!! Regidx s6_idx = m !!! Regidx s6_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er9 : m1 !!! Regidx s7_idx = m !!! Regidx s7_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er10 : m1 !!! Regidx s8_idx = m !!! Regidx s8_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er11 : m1 !!! Regidx s9_idx = m !!! Regidx s9_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er12 : m1 !!! Regidx s10_idx = m !!! Regidx s10_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Er13 : m1 !!! Regidx s11_idx = m !!! Regidx s11_idx) by (rewrite /m1; rgl; reflexivity).
    rewrite Er1 Er2 Er3 Er4 Er5 Er6 Er7 Er8 Er9 Er10 Er11 Er12 Er13.
    (* ---- 0x114  c.addi4spn s0,sp,112 ---- *)
    iApply (wp_uk_caddi4spn N h14 m1 (mword_of_int 0x114)
              (mword_of_int 0 : mword 3) (mword_of_int 28 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8)))) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_114 with "Hcode"). }
    iIntros (h15) "Hrun". pcn.
    set (m2 := <[Regidx s0_idx := regval_into_reg
                   (add_vec (m1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))))]> m1).
    (* ---- 0x116  c.mv s8,a0 ; 0x118  c.mv s9,a1 ---- *)
    iApply (wp_uk_cmv N h15 m2 (mword_of_int 0x116) s8_idx a0_idx (mword_of_int ar) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m2 /m1; rgl; rewrite Ha0 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_116 with "Hcode"). }
    iIntros (h16) "Hrun". pcn.
    set (m3 := <[Regidx s8_idx := regval_into_reg (mword_of_int ar : mword 64)]> m2).
    iApply (wp_uk_cmv N h16 m3 (mword_of_int 0x118) s9_idx a1_idx fdv (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m3 /m2 /m1; rgl; rewrite Ha1; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_grep_118 with "Hcode"). }
    iIntros (h17) "Hrun". pcn.
    set (m4 := <[Regidx s9_idx := regval_into_reg fdv]> m3).
    (* ---- 0x11a  c.li s3,0 ; 0x11c  c.li s6,0 ---- *)
    iApply (wp_uk_cli N h17 m4 (mword_of_int 0x11a) (mword_of_int 0 : mword 6) s3_idx (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_grep_11a with "Hcode"). }
    iIntros (h18) "Hrun". pcn.
    set (m5 := <[Regidx s3_idx := regval_into_reg
                   (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> m4).
    iApply (wp_uk_cli N h18 m5 (mword_of_int 0x11c) (mword_of_int 0 : mword 6) s6_idx (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_grep_11c with "Hcode"). }
    iIntros (h19) "Hrun". pcn.
    set (m6 := <[Regidx s6_idx := regval_into_reg
                   (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> m5).
    (* ---- 0x11e  li s10,1023 ---- *)
    iApply (wp_uk_li N h19 m6 (mword_of_int 0x11e) (mword_of_int 1023 : mword 12) s10_idx
              (mword_of_int 1023) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_11e with "Hcode"). }
    iIntros (h20) "Hrun". pcn.
    set (m7 := <[Regidx s10_idx := regval_into_reg (mword_of_int 1023 : mword 64)]> m6).
    (* ---- 0x122  auipc s7,0x2 ; 0x126  addi s7,s7,-274 -- s7 = buf ---- *)
    iApply (wp_uk_auipc N h20 m7 (mword_of_int 0x122) (mword_of_int 2 : mword 20) s7_idx
              (mword_of_int 0x2122) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_122 with "Hcode"). }
    iIntros (h21) "Hrun". pcn.
    set (m8 := <[Regidx s7_idx := regval_into_reg (mword_of_int 0x2122 : mword 64)]> m7).
    iApply (wp_uk_addi N h21 m8 (mword_of_int 0x126) (mword_of_int 3822 : mword 12)
              s7_idx s7_idx (mword_of_int gbuf) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m8; rgl; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_126 with "Hcode"). }
    iIntros (h22) "Hrun". pcn.
    set (m9 := <[Regidx s7_idx := regval_into_reg (mword_of_int gbuf : mword 64)]> m8).
    (* ---- 0x12a  c.li s5,10 ; 0x12c  c.li s11,1 ---- *)
    iApply (wp_uk_cli N h22 m9 (mword_of_int 0x12a) (mword_of_int 10 : mword 6) s5_idx (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_grep_12a with "Hcode"). }
    iIntros (h23) "Hrun". pcn.
    set (m10 := <[Regidx s5_idx := regval_into_reg
                   (sign_extend' 64 (mword_of_int 10 : mword 6) : mword 64)]> m9).
    iApply (wp_uk_cli N h23 m10 (mword_of_int 0x12c) (mword_of_int 1 : mword 6) s11_idx (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_grep_12c with "Hcode"). }
    iIntros (h24) "Hrun". pcn.
    set (m11 := <[Regidx s11_idx := regval_into_reg
                   (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)]> m10).
    (* ---- 0x12e  c.j 0x16e ---- *)
    iApply (wp_uk_cj N h24 m11 (mword_of_int 0x12e) (mword_of_int 32 : mword 11)
              (mword_of_int 0x16e) (4 + n2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_12e with "Hcode"). }
    iIntros (h25) "Hrun".
    iApply ("Hcont" $! h25 m11 with "[] [] [] [] [] [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14] Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro.
      rewrite /gl_regs /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1.
      rgl. split_and!; first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
    - iPureIntro. rewrite /m11 /m10 /m9 /m8 /m7 /m6 /m5. rgl.
      apply bv_eq; vm_compute; reflexivity.
    - iPureIntro. rewrite /m11 /m10 /m9 /m8 /m7 /m6. rgl.
      apply bv_eq; vm_compute; reflexivity.
    - rewrite /gframe. iFrame.
  Qed.

  (* ===================================================================== *)
  (* THE EPILOGUE, 0x1b2..0x1ce: the thirteen reloads, the pop, the return. *)
  (* ===================================================================== *)
  Lemma wp_kgl_epi (h : CpuId) (m m0 : regfile) (sp0 : mword 64) (ar : Z)
      (fdv : mword 64) (n2 : nat) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 -> 112 <= uint sp0 ->
    gl_regs m0 sp0 ar fdv m ->
    grep_code γt -∗ gframe sp0 m0 -∗
    urun N h m (mword_of_int 0x1b2) (4 + n2) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m0 m' ⌝ -∗
       urun N h' m' (ret_pc (m0 !!! Regidx ra_idx)) (14 + (4 + n2)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hsp0 Hal8 Hlo Hgl.
    iIntros "#Hcode (Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14) Hrun Hcont".
    destruct Hgl as (Hsp & Hx3 & Hx4 & _).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 14)))
                   = bv_unsigned sp0 - 112).
    { replace (- (8 * Z.of_nat 14)) with (-112) by lia.
      exact (uv_avi_neg sp0 112 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp112 : uint (add_vec_int sp0 (- (8 * Z.of_nat 14))) = uint sp0 - 112)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho104 : uoff_sdsp (mword_of_int 13 : mword 6) = 104) by (vm_compute; reflexivity).
    assert (Ho96 : uoff_sdsp (mword_of_int 12 : mword 6) = 96) by (vm_compute; reflexivity).
    assert (Ho88 : uoff_sdsp (mword_of_int 11 : mword 6) = 88) by (vm_compute; reflexivity).
    assert (Ho80 : uoff_sdsp (mword_of_int 10 : mword 6) = 80) by (vm_compute; reflexivity).
    assert (Ho72 : uoff_sdsp (mword_of_int 9 : mword 6) = 72) by (vm_compute; reflexivity).
    assert (Ho64 : uoff_sdsp (mword_of_int 8 : mword 6) = 64) by (vm_compute; reflexivity).
    assert (Ho56 : uoff_sdsp (mword_of_int 7 : mword 6) = 56) by (vm_compute; reflexivity).
    assert (Ho48 : uoff_sdsp (mword_of_int 6 : mword 6) = 48) by (vm_compute; reflexivity).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40) by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32) by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24) by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16) by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8) by (vm_compute; reflexivity).
    (* ---- 0x1b2..0x1ca  the thirteen reloads ---- *)
    iApply (wp_uk_cldsp N h m (mword_of_int 0x1b2) (mword_of_int 13 : mword 6) ra_idx
              (uint sp0 - 8) (m0 !!! Regidx ra_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp112 Ho104; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_grep_1b2 with "Hcode"). }
    iIntros "Hw1" (h1) "Hrun". pcn.
    set (e1 := <[Regidx ra_idx := regval_into_reg (m0 !!! Regidx ra_idx)]> m).
    iApply (wp_uk_cldsp N h1 e1 (mword_of_int 0x1b4) (mword_of_int 12 : mword 6) s0_idx
              (uint sp0 - 16) (m0 !!! Regidx s0_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e1; rgl; rewrite Hsp Hsp112 Ho96; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_grep_1b4 with "Hcode"). }
    iIntros "Hw2" (h2) "Hrun". pcn.
    set (e2 := <[Regidx s0_idx := regval_into_reg (m0 !!! Regidx s0_idx)]> e1).
    iApply (wp_uk_cldsp N h2 e2 (mword_of_int 0x1b6) (mword_of_int 11 : mword 6) s1_idx
              (uint sp0 - 24) (m0 !!! Regidx s1_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e2 /e1; rgl; rewrite Hsp Hsp112 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_grep_1b6 with "Hcode"). }
    iIntros "Hw3" (h3) "Hrun". pcn.
    set (e3 := <[Regidx s1_idx := regval_into_reg (m0 !!! Regidx s1_idx)]> e2).
    iApply (wp_uk_cldsp N h3 e3 (mword_of_int 0x1b8) (mword_of_int 10 : mword 6) s2_idx
              (uint sp0 - 32) (m0 !!! Regidx s2_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_grep_1b8 with "Hcode"). }
    iIntros "Hw4" (h4) "Hrun". pcn.
    set (e4 := <[Regidx s2_idx := regval_into_reg (m0 !!! Regidx s2_idx)]> e3).
    iApply (wp_uk_cldsp N h4 e4 (mword_of_int 0x1ba) (mword_of_int 9 : mword 6) s3_idx
              (uint sp0 - 40) (m0 !!! Regidx s3_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_grep_1ba with "Hcode"). }
    iIntros "Hw5" (h5) "Hrun". pcn.
    set (e5 := <[Regidx s3_idx := regval_into_reg (m0 !!! Regidx s3_idx)]> e4).
    iApply (wp_uk_cldsp N h5 e5 (mword_of_int 0x1bc) (mword_of_int 8 : mword 6) s4_idx
              (uint sp0 - 48) (m0 !!! Regidx s4_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho64; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_grep_1bc with "Hcode"). }
    iIntros "Hw6" (h6) "Hrun". pcn.
    set (e6 := <[Regidx s4_idx := regval_into_reg (m0 !!! Regidx s4_idx)]> e5).
    iApply (wp_uk_cldsp N h6 e6 (mword_of_int 0x1be) (mword_of_int 7 : mword 6) s5_idx
              (uint sp0 - 56) (m0 !!! Regidx s5_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e6 /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_grep_1be with "Hcode"). }
    iIntros "Hw7" (h7) "Hrun". pcn.
    set (e7 := <[Regidx s5_idx := regval_into_reg (m0 !!! Regidx s5_idx)]> e6).
    iApply (wp_uk_cldsp N h7 e7 (mword_of_int 0x1c0) (mword_of_int 6 : mword 6) s6_idx
              (uint sp0 - 64) (m0 !!! Regidx s6_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_grep_1c0 with "Hcode"). }
    iIntros "Hw8" (h8) "Hrun". pcn.
    set (e8 := <[Regidx s6_idx := regval_into_reg (m0 !!! Regidx s6_idx)]> e7).
    iApply (wp_uk_cldsp N h8 e8 (mword_of_int 0x1c2) (mword_of_int 5 : mword 6) s7_idx
              (uint sp0 - 72) (m0 !!! Regidx s7_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw9 Hrun").
    { iApply (uis_grep_1c2 with "Hcode"). }
    iIntros "Hw9" (h9) "Hrun". pcn.
    set (e9 := <[Regidx s7_idx := regval_into_reg (m0 !!! Regidx s7_idx)]> e8).
    iApply (wp_uk_cldsp N h9 e9 (mword_of_int 0x1c4) (mword_of_int 4 : mword 6) s8_idx
              (uint sp0 - 80) (m0 !!! Regidx s8_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw10 Hrun").
    { iApply (uis_grep_1c4 with "Hcode"). }
    iIntros "Hw10" (h10) "Hrun". pcn.
    set (e10 := <[Regidx s8_idx := regval_into_reg (m0 !!! Regidx s8_idx)]> e9).
    iApply (wp_uk_cldsp N h10 e10 (mword_of_int 0x1c6) (mword_of_int 3 : mword 6) s9_idx
              (uint sp0 - 88) (m0 !!! Regidx s9_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw11 Hrun").
    { iApply (uis_grep_1c6 with "Hcode"). }
    iIntros "Hw11" (h11) "Hrun". pcn.
    set (e11 := <[Regidx s9_idx := regval_into_reg (m0 !!! Regidx s9_idx)]> e10).
    iApply (wp_uk_cldsp N h11 e11 (mword_of_int 0x1c8) (mword_of_int 2 : mword 6) s10_idx
              (uint sp0 - 96) (m0 !!! Regidx s10_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw12 Hrun").
    { iApply (uis_grep_1c8 with "Hcode"). }
    iIntros "Hw12" (h12) "Hrun". pcn.
    set (e12 := <[Regidx s10_idx := regval_into_reg (m0 !!! Regidx s10_idx)]> e11).
    iApply (wp_uk_cldsp N h12 e12 (mword_of_int 0x1ca) (mword_of_int 1 : mword 6) s11_idx
              (uint sp0 - 104) (m0 !!! Regidx s11_idx) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /e12 /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; rewrite Hsp Hsp112 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw13 Hrun").
    { iApply (uis_grep_1ca with "Hcode"). }
    iIntros "Hw13" (h13) "Hrun". pcn.
    set (e13 := <[Regidx s11_idx := regval_into_reg (m0 !!! Regidx s11_idx)]> e12).
    assert (Hsp13 : e13 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 14)))
      by (rewrite /e13 /e12 /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; exact Hsp).
    (* ---- 0x1cc  c.addi16sp sp,sp,112 -- THE POP ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd14 : 0 <= 8 * Z.of_nat 14) by lia.
    assert (Hlt14 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 14))) + 8 * Z.of_nat 14 < Z64)
      by (rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 14))) (8 * Z.of_nat 14) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 14))) (8 * Z.of_nat 14) Hd14 Hlt14).
      rewrite Hbsp. lia. }
    iApply (wp_uk_caddi16sp_up N h13 e13 (mword_of_int 0x1cc) (mword_of_int 7 : mword 6) 14 (4 + n2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14] Hrun").
    { iApply (uis_grep_1cc with "Hcode"). }
    { rewrite Hsp13 Hup.
      iApply (ustack_14_close with "[Hw1] [Hw2] [Hw3] [Hw4] [Hw5] [Hw6] [Hw7] [Hw8] [Hw9] [Hw10] [Hw11] [Hw12] [Hw13] [Hw14]");
        [ exact Hal8 | .. ]; try iExact "Hw14"; iExists _; iFrame. }
    rewrite Hsp13 Hup. iIntros (h14) "Hrun". pcn.
    set (e14 := <[Regidx csp_rs1 := regval_into_reg sp0]> e13).
    (* ---- 0x1ce  c.jr ra ---- *)
    iApply (wp_uk_cjr N h14 e14 (mword_of_int 0x1ce) ra_idx (ret_pc (m0 !!! Regidx ra_idx))
              (14 + (4 + n2))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /e14 /e13 /e12 /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_1ce with "Hcode"). }
    iIntros (h15) "Hrun".
    iApply ("Hcont" with "[] Hrun").
    iPureIntro. apply ucallee_saved_of_list. intros k Hk.
    destruct Hk as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]]]]]]];
      try change (Regidx (mword_of_int 2)) with (Regidx csp_rs1);
      rewrite /e14 /e13 /e12 /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1; rgl;
      first [ reflexivity | exact Hx3 | exact Hx4 | symmetry; exact Hsp0 ].
  Qed.

  (* the buffer back together after a byte of the stop's run was stored *)
  Lemma buf_close_set (i k : nat) (F : nat -> bv 8) (b : bv 8) :
    (i + S k <= 1024)%nat ->
    ubytes γd gbuf i F -∗
    ubytes γd (gbuf + Z.of_nat i) k (fun j => F (i + j)%nat) -∗
    ubyte γd (gbuf + Z.of_nat i + Z.of_nat k) b -∗
    ubytes γd (gbuf + Z.of_nat i + Z.of_nat (S k)) (1024 - i - S k)
      (fun j => F (i + S k + j)%nat) -∗
    ubytes γd gbuf 1024 (fset F (i + k) b).
  Proof using .
    intros Hle. iIntros "HA HM Hb HR".
    iDestruct (ubytes_snoc_close (gbuf + Z.of_nat i) k
                 (fun j => fset F (i + k) b (i + j)%nat) b with "[HM] Hb") as "HM".
    { unfold fset. rewrite Nat.eqb_refl. reflexivity. }
    { iApply (ubytes_ext_w with "HM"). intros j Hj. unfold fset.
      rewrite (proj2 (Nat.eqb_neq (i + j) (i + k)) ltac:(lia)). reflexivity. }
    iApply (ubytes_close3' gbuf i (S k) (1024 - i - S k) 1024 _ F _ _ ltac:(lia) with "HA HM HR").
    - intros j Hj. unfold fset. rewrite (proj2 (Nat.eqb_neq j (i + k)) ltac:(lia)). reflexivity.
    - intros j Hj. reflexivity.
    - intros j Hj. unfold fset. rewrite (proj2 (Nat.eqb_neq (i + S k + j) (i + k)) ltac:(lia)).
      reflexivity.
  Qed.

  Lemma buf_close_same (i y : nat) (F : nat -> bv 8) :
    (i + y <= 1024)%nat ->
    ubytes γd gbuf i F -∗
    ubytes γd (gbuf + Z.of_nat i) y (fun j => F (i + j)%nat) -∗
    ubytes γd (gbuf + Z.of_nat i + Z.of_nat y) (1024 - i - y) (fun j => F (i + y + j)%nat) -∗
    ubytes γd gbuf 1024 F.
  Proof using .
    intros Hle. iIntros "HA HM HR".
    iApply (ubytes_close3' gbuf i y (1024 - i - y) 1024 F F _ _ ltac:(lia) with "HA HM HR");
      intros; reflexivity.
  Qed.

  Lemma buf_open (i y : nat) (F : nat -> bv 8) :
    (i + y <= 1024)%nat ->
    ubytes γd gbuf 1024 F -∗
    ubytes γd gbuf i F ∗
    ubytes γd (gbuf + Z.of_nat i) y (fun j => F (i + j)%nat) ∗
    ubytes γd (gbuf + Z.of_nat i + Z.of_nat y) (1024 - i - y) (fun j => F (i + y + j)%nat).
  Proof using .
    intros Hle. iIntros "H".
    iApply ubytes_open3.
    by replace (i + y + (1024 - i - y))%nat with 1024%nat by lia.
  Qed.

  (* ===================================================================== *)
  (* THE LOOP HEAD, 0x16e..0x190: the read into the room left, its answer *)
  (* tested, [m] advanced, [buf[m] = 0], [p = buf].                        *)
  (* ===================================================================== *)
  Lemma wp_kgl_head (h : CpuId) (m m0 : regfile) (sp0 fdv : mword 64) (ar fd : Z)
      (pat : bytes) (skip : bool) (left : bytes) (F : nat -> bv 8) (rest : proc)
      (n2 : nat) :
    gl_regs m0 sp0 ar fdv m ->
    bv_signed (trunc32 fdv) = fd ->
    m !!! Regidx s3_idx = mword_of_int (b01 skip) ->
    m !!! Regidx s6_idx = mword_of_int (Z.of_nat (length left)) ->
    (length left < 1023)%nat ->
    map F (seq 0 (length left)) = left ->
    grep_code γt -∗
    ubytes γd gbuf 1024 F -∗
    tp (grep_go pat fd skip [] left rest) -∗
    urun N h m (mword_of_int 0x16e) (4 + n2) -∗
    ((∀ (h' : CpuId) (m' : regfile) (F' : nat -> bv 8),
        ⌜ gl_regs m0 sp0 ar fdv m' ⌝ -∗
        ubytes γd gbuf 1024 F' -∗ tp rest -∗
        urun N h' m' (mword_of_int 0x1b2) (4 + n2) -∗ mWP (Loop : expr riscv_lang)) ∧
     (∀ (h' : CpuId) (m' : regfile) (F' : nat -> bv 8) (mv : nat),
        ⌜ gl_regs m0 sp0 ar fdv m' ⌝ -∗
        ⌜ m' !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat 0) ⌝ -∗
        ⌜ m' !!! Regidx s3_idx = mword_of_int (b01 skip) ⌝ -∗
        ⌜ m' !!! Regidx s4_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ⌜ m' !!! Regidx s6_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ⌜ (0 < mv <= 1023)%nat ⌝ -∗ ⌜ F' mv = ubyte0 ⌝ -∗
        ubytes γd gbuf 1024 F' -∗
        tp (grep_k pat fd rest
              (scan pat skip [] (map (fun j => F' (0 + j)%nat) (seq 0 (mv - 0))))) -∗
        urun N h' m' (mword_of_int 0x136) (4 + n2) -∗ mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hgl Hfd Hs3 Hs6 HL Hleft. iIntros "#Hcode Hbuf Ht Hrun Hk".
    pose proof Hgl as (Hsp & _ & _ & Hs5 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
    assert (Hbufv : gbuf = 8208) by reflexivity.
    assert (Hroom : grep_room left = (1023 - length left)%nat)
      by (rewrite /grep_room /grep_bufsz; lia).
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0) by (vm_compute; reflexivity).
    (* ---- 0x16e  subw a2,s10,s6 -- the room ---- *)
    iApply (wp_uk_subw N h m (mword_of_int 0x16e) s10_idx s6_idx a2_idx
              (mword_of_int (1023 - Z.of_nat (length left))) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs10 Hs6; symmetry; apply moi_subw; unfold Z31; lia)
              with "[] Hrun").
    { iApply (uis_grep_16e with "Hcode"). }
    iIntros (h1) "Hrun". pcn.
    set (m1 := <[Regidx a2_idx := regval_into_reg
                   (mword_of_int (1023 - Z.of_nat (length left)) : mword 64)]> m).
    (* ---- 0x172  add a1,s7,s6 -- buf + m ---- *)
    iApply (wp_uk_add N h1 m1 (mword_of_int 0x172) s7_idx s6_idx a1_idx
              (mword_of_int (gbuf + Z.of_nat (length left))) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m1; rgl; rewrite Hs7 Hs6 moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_172 with "Hcode"). }
    iIntros (h2) "Hrun". pcn.
    set (m2 := <[Regidx a1_idx := regval_into_reg
                   (mword_of_int (gbuf + Z.of_nat (length left)) : mword 64)]> m1).
    (* ---- 0x176  c.mv a0,s9 -- the descriptor ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0x176) a0_idx s9_idx fdv (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m2 /m1; rgl; rewrite Hs9; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_grep_176 with "Hcode"). }
    iIntros (h3) "Hrun". pcn.
    set (m3 := <[Regidx a0_idx := regval_into_reg fdv]> m2).
    (* ---- 0x178  jal read ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x178) (mword_of_int 956 : mword 21) ra_idx
              (mword_of_int GrepSyms.read) (mword_of_int 0x17c) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.read; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.read; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_178 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x17c : mword 64)]> m3).
    (* ---- read(fd, buf + m, 1023 - m): THE TREE'S READ HOLE ---- *)
    iEval (rewrite grep_go_read tree_pay_vis; cbn [ev_obl]) in "Ht".
    iDestruct (buf_open (length left) (grep_room left) F ltac:(lia) with "Hbuf")
      as "(HA & HW & HT)".
    iApply ("Ht" $! h4 m4 (4 + n2)%nat (gbuf + Z.of_nat (length left))
              (fun j => F (length left + j)%nat)
              with "[%] [%] [%] Hcode HW Hrun").
    { rewrite /m4 /m3; rgl. exact Hfd. }
    { rewrite /m4 /m3 /m2; rgl. reflexivity. }
    { rewrite /m4 /m3 /m2 /m1; rgl. rewrite cint_moi_small'.
      - rewrite Hroom. lia.
      - change (2 ^ 31) with 2147483648. lia. }
    iIntros (h5 ret g') "%Hok HK HW Hrun".
    assert (Eret : ret_pc (m4 !!! Regidx ra_idx) = (mword_of_int 0x17c : mword 64))
      by (rewrite /m4; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (m5 := stub_ret m4 5 ret).
    assert (Ha05 : m5 !!! Regidx a0_idx = ret) by (rewrite /m5 /stub_ret; rgl; reflexivity).
    assert (Hk5 : rkeep ([18; 20; 22] ++ Wcaller) m m5)
      by (rewrite /m5 /stub_ret /m4 /m3 /m2 /m1; rk).
    (* the buffer, the read's window at what it answered *)
    set (F2 := fread F g' (length left) (grep_room left)).
    iAssert (ubytes γd gbuf 1024 F2) with "[HA HW HT]" as "Hbuf".
    { iApply (buf_close_same (length left) (grep_room left) F2 ltac:(lia)
                with "[HA] [HW] [HT]").
      - iApply (ubytes_ext_w with "HA"). intros j Hj. symmetry. by apply fread_lo.
      - iApply (ubytes_ext_w with "HW"). intros j Hj. symmetry. by apply fread_mid.
      - iApply (ubytes_ext_w with "HT"). intros j Hj. symmetry. apply fread_hi. }
    (* ---- 0x17c  blez a0,0x1b2 -- n <= 0 leaves the loop ---- *)
    assert (Hsz : sint (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
    assert (Hbge : uv_btaken BGE zero_reg (m5 !!! Regidx a0_idx) = Z.geb 0 (bv_signed ret)).
    { rewrite Ha05. cbn [uv_btaken]. unfold zopz0zKzJ_s. rewrite Hsz. reflexivity. }
    destruct (Z.geb 0 (bv_signed ret)) eqn:Hble.
    - (* n <= 0: the loop ends, and so does grep's share of the tree *)
      iApply (wp_uk_btype0l N h5 m5 (mword_of_int 0x17c) (mword_of_int 54 : mword 13) a0_idx
                BGE true (mword_of_int 0x1b2) (4 + n2)
                (eq_sym Hbge) ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity) with "[] Hrun").
      { iApply (uis_grep_17c with "Hcode"). }
      iIntros (h6) "Hrun".
      assert (Hr : grep_rk pat fd skip left rest (rd_ans_of ret g') = rest).
      { apply grep_rk_nonpos. rewrite Z.geb_leb in Hble. apply Z.leb_le in Hble. lia. }
      iEval (cbv beta; rewrite Hr) in "HK".
      iDestruct "Hk" as "[Hx _]".
      iApply ("Hx" $! h6 m5 F2 with "[%] Hbuf HK Hrun").
      apply (gl_regs_keep ([18; 20; 22] ++ Wcaller) m0 sp0 ar fdv m m5);
        [ vm_compute; reflexivity .. | assumption | assumption ].
    - (* n > 0 *)
      iApply (wp_uk_btype0l N h5 m5 (mword_of_int 0x17c) (mword_of_int 54 : mword 13) a0_idx
                BGE false (mword_of_int 0x1b2) (4 + n2)
                (eq_sym Hbge) ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity) with "[] Hrun").
      { iApply (uis_grep_17c with "Hcode"). }
      iIntros (h6) "Hrun". pcn.
      assert (Hpos : 0 < bv_signed ret)
        by (rewrite Z.geb_leb in Hble; apply Z.leb_gt in Hble; lia).
      destruct Hok as [Hm1 | [_ Hle]]; [ lia | ].
      rewrite Hroom in Hle.
      remember (Z.to_nat (bv_signed ret)) as nb eqn:Enb.
      assert (Hnb : bv_signed ret = Z.of_nat nb) by lia.
      assert (Hretv : ret = mword_of_int (Z.of_nat nb))
        by (rewrite -Hnb; symmetry; apply moi_of_sint').
      (* ---- 0x180  addw s4,s6,a0 -- m += n ---- *)
      iApply (wp_uk_addw N h6 m5 (mword_of_int 0x180) s6_idx a0_idx s4_idx
                (mword_of_int (Z.of_nat (length left) + Z.of_nat nb)) (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha05 /m5 /stub_ret /m4 /m3 /m2 /m1; rgl; rewrite Hs6 Hretv;
                      symmetry; apply moi_addw_rr; unfold Z31; lia)
                with "[] Hrun").
      { iApply (uis_grep_180 with "Hcode"). }
      iIntros (h7) "Hrun". pcn.
      set (m6 := <[Regidx s4_idx := regval_into_reg
                     (mword_of_int (Z.of_nat (length left) + Z.of_nat nb) : mword 64)]> m5).
      (* ---- 0x184  c.mv s6,s4 ---- *)
      iApply (wp_uk_cmv N h7 m6 (mword_of_int 0x184) s6_idx s4_idx
                (mword_of_int (Z.of_nat (length left) + Z.of_nat nb)) (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /m6; rgl; rewrite moi_add_zero_l; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_184 with "Hcode"). }
      iIntros (h8) "Hrun". pcn.
      set (m7 := <[Regidx s6_idx := regval_into_reg
                     (mword_of_int (Z.of_nat (length left) + Z.of_nat nb) : mword 64)]> m6).
      (* ---- 0x186  add a5,s7,s4 -- &buf[m] ---- *)
      iApply (wp_uk_add N h8 m7 (mword_of_int 0x186) s7_idx s4_idx a5_idx
                (mword_of_int (gbuf + (Z.of_nat (length left) + Z.of_nat nb))) (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /m7 /m6; rgl;
                      rewrite Hs7 moi_add;
                      reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_186 with "Hcode"). }
      iIntros (h9) "Hrun". pcn.
      set (m8 := <[Regidx a5_idx := regval_into_reg
                     (mword_of_int (gbuf + (Z.of_nat (length left) + Z.of_nat nb)) : mword 64)]> m7).
      (* ---- 0x18a  sb zero,0(a5) -- buf[m] = 0 ---- *)
      iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
      iDestruct (ubytes_byte_upd γd gbuf 1024 F2 (length left + nb)%nat ltac:(lia) with "Hbuf")
        as "[Hb Hcl]".
      iApply (wp_uk_sb N h9 m8 (mword_of_int 0x18a) (mword_of_int 0 : mword 12) a5_idx x0_idx
                (gbuf + Z.of_nat (length left + nb)%nat) (F2 (length left + nb)%nat) (4 + n2)
                ltac:(rewrite /m8; rgl; rewrite uint_moi; [ rewrite Eoff0; lia | unfold Z64; lia ])
                with "[] Hb Hrun").
      { iApply (uis_grep_18a with "Hcode"). }
      iIntros "Hb" (h10) "Hrun". pcn.
      iEval (rewrite Hx0 nth_byte_zero0) in "Hb".
      iDestruct ("Hcl" with "Hb") as "Hbuf".
      (* ---- 0x18e  c.mv s2,s7 -- p = buf ---- *)
      iApply (wp_uk_cmv N h10 m8 (mword_of_int 0x18e) s2_idx s7_idx
                (mword_of_int (gbuf + Z.of_nat 0)) (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /m8 /m7 /m6; rgl;
                      rewrite Hs7 moi_add_zero_l;
                      f_equal; lia)
                with "[] Hrun").
      { iApply (uis_grep_18e with "Hcode"). }
      iIntros (h11) "Hrun". pcn.
      set (m9 := <[Regidx s2_idx := regval_into_reg (mword_of_int (gbuf + Z.of_nat 0) : mword 64)]> m8).
      (* ---- 0x190  c.j 0x136 ---- *)
      iApply (wp_uk_cj N h11 m9 (mword_of_int 0x190) (mword_of_int 2003 : mword 11)
                (mword_of_int 0x136) (4 + n2)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_190 with "Hcode"). }
      iIntros (h12) "Hrun".
      assert (Hk9 : rkeep ([18; 20; 22] ++ Wcaller) m m9).
      { eapply rkeep_trans; [ exact Hk5 | ]. rewrite /m9 /m8 /m7 /m6; rk. }
      iDestruct "Hk" as "[_ Hi]".
      iApply ("Hi" $! h12 m9 (fset F2 (length left + nb) ubyte0) (length left + nb)%nat
                with "[%] [%] [%] [%] [%] [%] [%] Hbuf [HK] Hrun").
      + apply (gl_regs_keep ([18; 20; 22] ++ Wcaller) m0 sp0 ar fdv m m9);
          [ vm_compute; reflexivity .. | assumption | assumption ].
      + rewrite /m9; rgl. reflexivity.
      + rewrite (Hk9 s3_idx ltac:(vm_compute; reflexivity)). exact Hs3.
      + rewrite /m9 /m8 /m7 /m6; rgl. f_equal. lia.
      + rewrite /m9 /m8 /m7; rgl. f_equal. lia.
      + lia.
      + unfold fset. rewrite Nat.eqb_refl. reflexivity.
      + iEval (cbv beta; rewrite (rd_ans_of_pos ret g' nb Hnb)) in "HK".
        rewrite (grep_rk_bytes pat fd skip left rest (map g' (seq 0 nb))).
        2:{ destruct nb as [| nb']; [ lia | ]. simpl. discriminate. }
        rewrite (head_bytes F g' (length left) (grep_room left) nb left ubyte0 Hleft
                   ltac:(rewrite Hroom; lia)).
        iExact "HK".
  Qed.

  (* ===================================================================== *)
  (* ONE TURN OF THE SCAN, 0x136..0x168 and 0x130: strchr to the next     *)
  (* newline or NUL; at a NUL the scan is over (0x16a); at a newline the   *)
  (* line is NUL-terminated, matched unless skipping, written if it        *)
  (* matched, and [p] moves past it.                                      *)
  (* ===================================================================== *)
  Lemma wp_kgl_step (h : CpuId) (m m0 : regfile) (sp0 fdv : mword 64) (ar fd : Z)
      (dqr : dfrac) (lr : nat) (fr : nat -> bv 8)
      (sk : bool) (i mv : nat) (F : nat -> bv 8) (rest : proc) (n2 : nat) :
    gl_regs m0 sp0 ar fdv m ->
    m !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i) ->
    m !!! Regidx s3_idx = mword_of_int (b01 sk) ->
    m !!! Regidx s4_idx = mword_of_int (Z.of_nat mv) ->
    m !!! Regidx s6_idx = mword_of_int (Z.of_nat mv) ->
    (i <= mv <= 1023)%nat -> F mv = ubyte0 ->
    (mh_words (grep_body (map fr (seq 0 lr))) <= n2)%nat ->
    grep_code γt -∗ ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 F -∗
    tp (grep_k (map fr (seq 0 lr)) fd rest
          (scan (map fr (seq 0 lr)) sk [] (map (fun j => F (i + j)%nat) (seq 0 (mv - i))))) -∗
    urun N h m (mword_of_int 0x136) (4 + n2) -∗
    ((∀ (h' : CpuId) (m' : regfile),
        ⌜ gl_regs m0 sp0 ar fdv m' ⌝ -∗
        ⌜ m' !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i) ⌝ -∗
        ⌜ m' !!! Regidx s3_idx = mword_of_int (b01 sk) ⌝ -∗
        ⌜ m' !!! Regidx s4_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ⌜ m' !!! Regidx s6_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 F -∗
        tp (grep_k (map fr (seq 0 lr)) fd rest
              ([], map (fun j => F (i + j)%nat) (seq 0 (mv - i)), sk)) -∗
        urun N h' m' (mword_of_int 0x16a) (4 + n2) -∗ mWP (Loop : expr riscv_lang)) ∧
     (∀ (h' : CpuId) (m' : regfile) (F' : nat -> bv 8) (i' : nat),
        ⌜ (i < i' <= mv)%nat ⌝ -∗
        ⌜ gl_regs m0 sp0 ar fdv m' ⌝ -∗
        ⌜ m' !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i') ⌝ -∗
        ⌜ m' !!! Regidx s3_idx = mword_of_int (b01 false) ⌝ -∗
        ⌜ m' !!! Regidx s4_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ⌜ m' !!! Regidx s6_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ⌜ F' mv = ubyte0 ⌝ -∗
        ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 F' -∗
        tp (grep_k (map fr (seq 0 lr)) fd rest
              (scan (map fr (seq 0 lr)) false [] (map (fun j => F' (i' + j)%nat) (seq 0 (mv - i'))))) -∗
        urun N h' m' (mword_of_int 0x136) (4 + n2) -∗ mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hgl Hs2 Hs3 Hs4 Hs6 Him HFm Hn. iIntros "#Hcode Hre Hbuf Ht Hrun Hk".
    pose proof Hgl as (Hsp & _ & _ & Hs5 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
    assert (Hbufv : gbuf = 8208) by reflexivity.
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0) by (vm_compute; reflexivity).
    destruct (first_stop F mv HFm (mv - i) i ltac:(lia)) as (k & Hik & Hpl & Hst).
    (* ---- 0x136  c.mv a1,s5 ; 0x138  c.mv a0,s2 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x136) a1_idx s5_idx
              (mword_of_int (bv_unsigned wl_nl)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5 wl_nl_unsigned moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_136 with "Hcode"). }
    iIntros (h1) "Hrun". pcn.
    set (m1 := <[Regidx a1_idx := regval_into_reg (mword_of_int (bv_unsigned wl_nl) : mword 64)]> m).
    iApply (wp_uk_cmv N h1 m1 (mword_of_int 0x138) a0_idx s2_idx
              (mword_of_int (gbuf + Z.of_nat i)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m1; rgl; rewrite Hs2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_138 with "Hcode"). }
    iIntros (h2) "Hrun". pcn.
    set (m2 := <[Regidx a0_idx := regval_into_reg (mword_of_int (gbuf + Z.of_nat i) : mword 64)]> m1).
    (* ---- 0x13a  jal strchr ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0x13a) (mword_of_int 478 : mword 21) ra_idx
              (mword_of_int GrepSyms.strchr) (mword_of_int 0x13e) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.strchr; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.strchr; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_13a with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x13e : mword 64)]> m2).
    iDestruct (buf_open i (S k) F ltac:(lia) with "Hbuf") as "(HA & HM & HR)".
    iApply (wp_kgrep_strchr N h3 m3 (DfracOwn 1) (gbuf + Z.of_nat i) wl_nl k
              (fun j => F (i + j)%nat) (2 + n2)
              ltac:(rewrite /m3; rgl; reflexivity)
              ltac:(rewrite /m3 /m2; rgl; reflexivity)
              ltac:(intros He; apply (f_equal bv_unsigned) in He; vm_compute in He; discriminate)
              ltac:(intros j Hj; exact (Hpl j Hj))
              Hst
              with "Hcode HM Hrun").
    iIntros "HM" (h4 m4) "%Hcs4 %Ha04 Hrun".
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = (mword_of_int 0x13e : mword 64))
      by (rewrite /m3; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    assert (Hk4 : rkeep ([9] ++ Wcaller) m m4).
    { eapply (rkeep_call ([9] ++ Wcaller) m m3 m4); [ | | exact Hcs4 ].
      - intros r Hr. apply rin_app_caller. exact Hr.
      - rewrite /m3 /m2 /m1; rk. }
    (* ---- 0x13e  c.mv s1,a0 -- q ---- *)
    iApply (wp_uk_cmv N h4 m4 (mword_of_int 0x13e) s1_idx a0_idx
              (mword_of_int (if bool_decide (F (i + k)%nat = wl_nl)
                             then gbuf + Z.of_nat i + Z.of_nat k else 0)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha04 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_13e with "Hcode"). }
    iIntros (h5) "Hrun". pcn.
    set (m5 := <[Regidx s1_idx := regval_into_reg
                   (mword_of_int (if bool_decide (F (i + k)%nat = wl_nl)
                                  then gbuf + Z.of_nat i + Z.of_nat k else 0) : mword 64)]> m4).
    assert (Hk5 : rkeep ([9] ++ Wcaller) m m5) by (rewrite /m5; rk).
    assert (Hgl5 : gl_regs m0 sp0 ar fdv m5)
      by (apply (gl_regs_keep ([9] ++ Wcaller) m0 sp0 ar fdv m m5);
          [ vm_compute; reflexivity .. | assumption | assumption ]).
    assert (Hs2_5 : m5 !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i))
      by (rewrite (Hk5 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_5 : m5 !!! Regidx s3_idx = mword_of_int (b01 sk))
      by (rewrite (Hk5 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (Hs4_5 : m5 !!! Regidx s4_idx = mword_of_int (Z.of_nat mv))
      by (rewrite (Hk5 s4_idx ltac:(vm_compute; reflexivity)); exact Hs4).
    assert (Hs6_5 : m5 !!! Regidx s6_idx = mword_of_int (Z.of_nat mv))
      by (rewrite (Hk5 s6_idx ltac:(vm_compute; reflexivity)); exact Hs6).
    (* ---- 0x140  c.beqz a0,0x16a ---- *)
    destruct (decide (F (i + k)%nat = wl_nl)) as [Hnl | Hnnl].
    2:{ (* THE NUL: strchr found no newline, and the scan is over *)
      assert (Hz : F (i + k)%nat = c_nul) by (destruct Hst as [H | H]; [ contradiction | exact H ]).
      rewrite (bool_decide_eq_false_2 _ Hnnl) in Ha04.
      iApply (wp_uk_cbeqz N h5 m5 (mword_of_int 0x140)
                (mword_of_int 21 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x16a) (4 + n2)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite /m5; rgl; rewrite Ha04; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_140 with "Hcode"). }
      iIntros (h6) "Hrun".
      iDestruct (buf_close_same i (S k) F ltac:(lia) with "HA HM HR") as "Hbuf".
      iDestruct "Hk" as "[Hend _]".
      iApply ("Hend" $! h6 m5 with "[%] [%] [%] [%] [%] Hre Hbuf [Ht] Hrun");
        [ exact Hgl5 | exact Hs2_5 | exact Hs3_5 | exact Hs4_5 | exact Hs6_5 | ].
      rewrite (grep_k_stop_S (map fr (seq 0 lr)) fd rest F i k mv Hpl sk Hik Hz).
      iExact "Ht". }
    (* THE NEWLINE, at [q = p + k] *)
    rewrite (bool_decide_eq_true_2 _ Hnl) in Ha04 Hk5 Hgl5 Hs2_5 Hs3_5 Hs4_5 Hs6_5 |- *.
    assert (Hlt : (i + k < mv)%nat).
    { destruct (Nat.eq_dec (i + k) mv) as [He | Hne]; [ | lia ].
      exfalso. rewrite He HFm in Hnl. apply nul_ne_nl. exact Hnl. }
    assert (Hs1_5 : m5 !!! Regidx s1_idx = mword_of_int (gbuf + Z.of_nat i + Z.of_nat k))
      by (rewrite /m5; rgl; rewrite (bool_decide_eq_true_2 _ Hnl); reflexivity).
    assert (Hz0 : eq_vec (mword_of_int (gbuf + Z.of_nat i + Z.of_nat k) : mword 64) zero_reg = false)
      by (rewrite moi_eq_zero; [ apply Z.eqb_neq; lia | unfold Z64; lia ]).
    iApply (wp_uk_cbeqz N h5 m5 (mword_of_int 0x140)
              (mword_of_int 21 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x16a) (4 + n2)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite /m5; rgl; rewrite Ha04 Hz0; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros He; discriminate He)
              with "[] Hrun").
    { iApply (uis_grep_140 with "Hcode"). }
    iIntros (h6) "Hrun". pcn.
    iDestruct (ubytes_snoc_open with "HM") as "[HM Hb]".
    (* ---- 0x142  sb zero,0(s1) -- *q = 0 ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    iApply (wp_uk_sb N h6 m5 (mword_of_int 0x142) (mword_of_int 0 : mword 12) s1_idx x0_idx
              (gbuf + Z.of_nat i + Z.of_nat k) (F (i + k)%nat) (4 + n2)
              ltac:(rewrite Hs1_5 uint_moi; [ rewrite Eoff0; lia | unfold Z64; lia ])
              with "[] Hb Hrun").
    { iApply (uis_grep_142 with "Hcode"). }
    iIntros "Hb" (h7) "Hrun". pcn.
    iEval (rewrite Hx0 nth_byte_zero0) in "Hb".
    (* THE BACK EDGE's TAIL, 0x130: p = q + 1, skip = 0 *)
    iAssert (∀ (h' : CpuId) (mc : regfile) (Fc : nat -> bv 8),
       ⌜ rkeep ([9] ++ Wcaller) m mc ⌝ -∗
       ⌜ mc !!! Regidx s1_idx = mword_of_int (gbuf + Z.of_nat i + Z.of_nat k) ⌝ -∗
       ⌜ Fc mv = ubyte0 ⌝ -∗
       ⌜ forall j : nat, (i + k < j)%nat -> Fc j = F j ⌝ -∗
       ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 Fc -∗
       tp (grep_k (map fr (seq 0 lr)) fd rest
             (scan (map fr (seq 0 lr)) false []
                (map (fun j => F (i + k + 1 + j)%nat) (seq 0 (mv - (i + k + 1)))))) -∗
       urun N h' mc (mword_of_int 0x130) (4 + n2) -∗ mWP (Loop : expr riscv_lang))%I
      with "[Hk]" as "Htail".
    { iIntros (h' mc Fc) "%Hkc %Hs1c %HFc %HFF Hre Hbuf Ht Hrun".
      iApply (wp_uk_addi N h' mc (mword_of_int 0x130) (mword_of_int 1 : mword 12)
                s1_idx s2_idx (mword_of_int (gbuf + Z.of_nat i + Z.of_nat k + 1)) (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1c;
                      replace (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                        with (mword_of_int 1 : mword 64) by (apply bv_eq; vm_compute; reflexivity);
                      rewrite moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_130 with "Hcode"). }
      iIntros (h8) "Hrun". pcn.
      set (mc1 := <[Regidx s2_idx := regval_into_reg
                      (mword_of_int (gbuf + Z.of_nat i + Z.of_nat k + 1) : mword 64)]> mc).
      iApply (wp_uk_cli N h8 mc1 (mword_of_int 0x134) (mword_of_int 0 : mword 6) s3_idx (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_grep_134 with "Hcode"). }
      iIntros (h9) "Hrun". pcn.
      set (mc2 := <[Regidx s3_idx := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> mc1).
      assert (Hkc2 : rkeep ([9; 18; 19] ++ Wcaller) m mc2).
      { eapply rkeep_trans.
        - refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity.
        - rewrite /mc2 /mc1; rk. }
      iDestruct "Hk" as "[_ Hloop]".
      iApply ("Hloop" $! h9 mc2 Fc (i + k + 1)%nat
                with "[%] [%] [%] [%] [%] [%] [%] Hre Hbuf [Ht] Hrun").
      - lia.
      - apply (gl_regs_keep ([9; 18; 19] ++ Wcaller) m0 sp0 ar fdv m mc2);
          [ vm_compute; reflexivity .. | assumption | assumption ].
      - rewrite /mc2 /mc1; rgl. f_equal. lia.
      - rewrite /mc2; rgl. apply bv_eq; vm_compute; reflexivity.
      - rewrite (Hkc2 s4_idx ltac:(vm_compute; reflexivity)). exact Hs4.
      - rewrite (Hkc2 s6_idx ltac:(vm_compute; reflexivity)). exact Hs6.
      - exact HFc.
      - rewrite (map_seq_ext (fun j => Fc (i + k + 1 + j)%nat) (fun j => F (i + k + 1 + j)%nat));
          [ iExact "Ht" | intros j _; apply HFF; lia ]. }
    (* ---- 0x146  bnez s3,0x130 -- skipping? ---- *)
    iApply (wp_uk_btype0 N h7 m5 (mword_of_int 0x146) (mword_of_int 8170 : mword 13) s3_idx
              BNE sk (mword_of_int 0x130) (4 + n2)
              ltac:(cbn [uv_btaken]; rewrite Hs3_5 /b01; symmetry; apply moi_b01_neqz)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_146 with "Hcode"). }
    iIntros (h8) "Hrun".
    destruct sk.
    { (* skipping the tail of an over-long line: no match, no write *)
      iDestruct (buf_close_set i k F ubyte0 ltac:(lia) with "HA HM Hb HR") as "Hbuf".
      iApply ("Htail" $! h8 m5 (fset F (i + k) ubyte0) with "[%] [%] [%] [%] Hre Hbuf [Ht] Hrun").
      - exact Hk5.
      - exact Hs1_5.
      - unfold fset. rewrite (proj2 (Nat.eqb_neq mv (i + k)) ltac:(lia)). exact HFm.
      - intros j Hj. unfold fset. rewrite (proj2 (Nat.eqb_neq j (i + k)) ltac:(lia)). reflexivity.
      - rewrite (grep_k_skip_S (map fr (seq 0 lr)) fd rest F i k mv Hpl Hlt Hnl).
        iExact "Ht". }
    pcn.
    (* ---- 0x14a  c.mv a1,s2 ; 0x14c  c.mv a0,s8 ; 0x14e  jal match ---- *)
    iApply (wp_uk_cmv N h8 m5 (mword_of_int 0x14a) a1_idx s2_idx
              (mword_of_int (gbuf + Z.of_nat i)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_5 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_14a with "Hcode"). }
    iIntros (h9) "Hrun". pcn.
    set (m6 := <[Regidx a1_idx := regval_into_reg (mword_of_int (gbuf + Z.of_nat i) : mword 64)]> m5).
    iApply (wp_uk_cmv N h9 m6 (mword_of_int 0x14c) a0_idx s8_idx
              (mword_of_int ar) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m6; rgl; try rewrite (Hk4 s8_idx ltac:(vm_compute; reflexivity)); rewrite Hs8;
                    rewrite moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_14c with "Hcode"). }
    iIntros (h10) "Hrun". pcn.
    set (m7 := <[Regidx a0_idx := regval_into_reg (mword_of_int ar : mword 64)]> m6).
    iApply (wp_uk_jal N h10 m7 (mword_of_int 0x14e) (mword_of_int 2096996 : mword 21) ra_idx
              (mword_of_int GrepSyms.match_) (mword_of_int 0x152) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.match_; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.match_; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_14e with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x152 : mword 64)]> m7).
    (* the line, NUL-terminated by the store: a string *)
    iAssert (ustr γd (DfracOwn 1) (gbuf + Z.of_nat i) k (fun j => F (i + j)%nat))%I
      with "[HM Hb]" as "Htx".
    { rewrite /ustr. iSplit.
      { iPureIntro. intros j Hj. exact (proj2 (Hpl j Hj)). }
      iSplit; [ iPureIntro; change (2 ^ 31) with 2147483648; lia | ].
      iSplitL "HM"; [ iExact "HM" | iExact "Hb" ]. }
    iApply (wp_kgrep_match N h11 m8 dqr (DfracOwn 1) ar (gbuf + Z.of_nat i) lr k fr
              (fun j => F (i + j)%nat) (4 + n2)
              ltac:(rewrite /m8; rgl; reflexivity)
              ltac:(rewrite /m8 /m7; rgl; reflexivity)
              ltac:(unfold grep_body in Hn; lia)
              with "Hcode Hre Htx Hrun").
    iIntros "Hre Htx" (h12 m9) "%Hcs9 %Ha09 Hrun".
    assert (Eret9 : ret_pc (m8 !!! Regidx ra_idx) = (mword_of_int 0x152 : mword 64))
      by (rewrite /m8; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret9.
    iDestruct "Htx" as "(_ & _ & HM & Hb)".
    assert (Hk9 : rkeep ([9] ++ Wcaller) m m9).
    { eapply (rkeep_call ([9] ++ Wcaller) m m8 m9); [ | | exact Hcs9 ].
      - intros r Hr. apply rin_app_caller. exact Hr.
      - eapply rkeep_trans; [ exact Hk5 | ]. rewrite /m8 /m7 /m6; rk. }
    assert (Hs1_9 : m9 !!! Regidx s1_idx = mword_of_int (gbuf + Z.of_nat i + Z.of_nat k)).
    { rewrite (Hcs9 s1_idx ltac:(vm_compute; reflexivity)) /m8 /m7 /m6; rgl. exact Hs1_5. }
    (* ---- 0x152  c.beqz a0,0x130 -- no match ---- *)
    destruct (match_re (map fr (seq 0 lr)) (map (fun j => F (i + j)%nat) (seq 0 k))) eqn:Hm.
    2:{ iApply (wp_uk_cbeqz N h12 m9 (mword_of_int 0x152)
                  (mword_of_int 239 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                  true (mword_of_int 0x130) (4 + n2)
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha09; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_152 with "Hcode"). }
        iIntros (h13) "Hrun".
        iDestruct (buf_close_set i k F ubyte0 ltac:(lia) with "HA HM Hb HR") as "Hbuf".
        iApply ("Htail" $! h13 m9 (fset F (i + k) ubyte0) with "[%] [%] [%] [%] Hre Hbuf [Ht] Hrun").
        - exact Hk9.
        - exact Hs1_9.
        - unfold fset. rewrite (proj2 (Nat.eqb_neq mv (i + k)) ltac:(lia)). exact HFm.
        - intros j Hj. unfold fset. rewrite (proj2 (Nat.eqb_neq j (i + k)) ltac:(lia)). reflexivity.
        - rewrite (grep_k_nomatch_S (map fr (seq 0 lr)) fd rest F i k mv Hpl Hlt Hnl Hm).
          iExact "Ht". }
    iApply (wp_uk_cbeqz N h12 m9 (mword_of_int 0x152)
              (mword_of_int 239 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x130) (4 + n2)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha09; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros He; discriminate He)
              with "[] Hrun").
    { iApply (uis_grep_152 with "Hcode"). }
    iIntros (h13) "Hrun". pcn.
    (* ---- 0x154  sb s5,0(s1) -- *q = '\n' ---- *)
    assert (Hgl9 : gl_regs m0 sp0 ar fdv m9)
      by (apply (gl_regs_keep ([9] ++ Wcaller) m0 sp0 ar fdv m m9);
          [ vm_compute; reflexivity .. | assumption | assumption ]).
    pose proof Hgl9 as (_ & _ & _ & Hs5_9 & _ & _ & _ & _ & Hs11_9).
    iApply (wp_uk_sb N h13 m9 (mword_of_int 0x154) (mword_of_int 0 : mword 12) s1_idx s5_idx
              (gbuf + Z.of_nat i + Z.of_nat k) ubyte0 (4 + n2)
              ltac:(rewrite Hs1_9 uint_moi; [ rewrite Eoff0; lia | unfold Z64; lia ])
              with "[] Hb Hrun").
    { iApply (uis_grep_154 with "Hcode"). }
    iIntros "Hb" (h14) "Hrun". pcn.
    iEval (rewrite Hs5_9 nth_byte_moi10 -Hnl) in "Hb".
    (* ---- 0x158  addi a2,s1,1 ; 0x15c  subw a2,a2,s2 -- q + 1 - p ---- *)
    iApply (wp_uk_addi N h14 m9 (mword_of_int 0x158) (mword_of_int 1 : mword 12)
              s1_idx a2_idx (mword_of_int (gbuf + Z.of_nat i + Z.of_nat k + 1)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9;
                    replace (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                      with (mword_of_int 1 : mword 64) by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_158 with "Hcode"). }
    iIntros (h15) "Hrun". pcn.
    set (m10 := <[Regidx a2_idx := regval_into_reg
                    (mword_of_int (gbuf + Z.of_nat i + Z.of_nat k + 1) : mword 64)]> m9).
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i))
      by (rewrite (Hk9 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    iApply (wp_uk_subw N h15 m10 (mword_of_int 0x15c) a2_idx s2_idx a2_idx
              (mword_of_int (Z.of_nat (S k))) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m10; rgl; rewrite Hs2_9 moi_subw; [ f_equal; lia | unfold Z31; lia ])
              with "[] Hrun").
    { iApply (uis_grep_15c with "Hcode"). }
    iIntros (h16) "Hrun". pcn.
    set (m11 := <[Regidx a2_idx := regval_into_reg (mword_of_int (Z.of_nat (S k)) : mword 64)]> m10).
    (* ---- 0x160  c.mv a1,s2 ; 0x162  c.mv a0,s11 ; 0x164  jal write ---- *)
    iApply (wp_uk_cmv N h16 m11 (mword_of_int 0x160) a1_idx s2_idx
              (mword_of_int (gbuf + Z.of_nat i)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m11 /m10; rgl; rewrite Hs2_9 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_160 with "Hcode"). }
    iIntros (h17) "Hrun". pcn.
    set (m12 := <[Regidx a1_idx := regval_into_reg (mword_of_int (gbuf + Z.of_nat i) : mword 64)]> m11).
    iApply (wp_uk_cmv N h17 m12 (mword_of_int 0x162) a0_idx s11_idx
              (mword_of_int 1) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m12 /m11 /m10; rgl; rewrite Hs11_9 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_162 with "Hcode"). }
    iIntros (h18) "Hrun". pcn.
    set (m13 := <[Regidx a0_idx := regval_into_reg (mword_of_int 1 : mword 64)]> m12).
    iApply (wp_uk_jal N h18 m13 (mword_of_int 0x164) (mword_of_int 984 : mword 21) ra_idx
              (mword_of_int GrepSyms.write) (mword_of_int 0x168) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.write; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.write; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_164 with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m14 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x168 : mword 64)]> m13).
    (* ---- write(1, p, q + 1 - p): THE TREE'S WRITE HOLE ---- *)
    iEval (rewrite (grep_k_match_S (map fr (seq 0 lr)) fd rest F i k mv Hpl Hlt Hnl Hm)
             tree_pay_vis; cbn [ev_obl]) in "Ht".
    iDestruct (ubytes_snoc_close (gbuf + Z.of_nat i) k (fun j => F (i + j)%nat) (F (i + k)%nat)
                 eq_refl with "HM Hb") as "HM".
    iApply ("Ht" $! h19 m14 (4 + n2)%nat (gbuf + Z.of_nat i) false (DfracOwn 1)
              (fun j => F (i + j)%nat)
              with "[%] [%] [%] [%] Hcode [HM] Hrun").
    { exact (bytes_of_line F i k Hnl). }
    { rewrite /m14 /m13; rgl. apply cint_moi_small'. change (2 ^ 31) with 2147483648. lia. }
    { rewrite /m14 /m13 /m12; rgl. reflexivity. }
    { rewrite /m14 /m13 /m12 /m11; rgl. rewrite length_line. reflexivity. }
    { rewrite length_line /usrc_at. iExact "HM". }
    iIntros (h20 wret) "HK Hs Hrun". iEval (cbv beta) in "HK".
    iEval (rewrite length_line /usrc_at) in "Hs".
    assert (Eret14 : ret_pc (m14 !!! Regidx ra_idx) = (mword_of_int 0x168 : mword 64))
      by (rewrite /m14; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret14.
    iDestruct (buf_close_same i (S k) F ltac:(lia) with "HA Hs HR") as "Hbuf".
    (* ---- 0x168  c.j 0x130 ---- *)
    iApply (wp_uk_cj N h20 (stub_ret m14 16 wret) (mword_of_int 0x168) (mword_of_int 2020 : mword 11)
              (mword_of_int 0x130) (4 + n2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_168 with "Hcode"). }
    iIntros (h21) "Hrun".
    iApply ("Htail" $! h21 (stub_ret m14 16 wret) F with "[%] [%] [%] [%] Hre Hbuf [HK] Hrun").
    - eapply rkeep_trans; [ exact Hk9 | ].
      rewrite /stub_ret /m14 /m13 /m12 /m11 /m10; rk.
    - rewrite /stub_ret /m14 /m13 /m12 /m11 /m10; rgl. exact Hs1_9.
    - exact HFm.
    - done.
    - iExact "HK".
  Qed.

  (* ===================================================================== *)
  (* THE SCAN, to the NUL strchr stops at: bounded by the buffer, so by    *)
  (* induction on what is left of it.                                     *)
  (* ===================================================================== *)
  Lemma wp_kgl_scan (m0 : regfile) (sp0 fdv : mword 64) (ar fd : Z) (dqr : dfrac)
      (lr : nat) (fr : nat -> bv 8) (mv : nat) (rest : proc) (n2 : nat) (d : nat) :
    (mv <= 1023)%nat ->
    (mh_words (grep_body (map fr (seq 0 lr))) <= n2)%nat ->
    grep_code γt -∗
    ∀ (i : nat) (h : CpuId) (m : regfile) (F : nat -> bv 8) (sk : bool),
    ⌜ (mv - i = d)%nat ⌝ -∗ ⌜ (i <= mv)%nat ⌝ -∗
    ⌜ gl_regs m0 sp0 ar fdv m ⌝ -∗
    ⌜ m !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i) ⌝ -∗
    ⌜ m !!! Regidx s3_idx = mword_of_int (b01 sk) ⌝ -∗
    ⌜ m !!! Regidx s4_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
    ⌜ m !!! Regidx s6_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
    ⌜ F mv = ubyte0 ⌝ -∗
    ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 F -∗
    tp (grep_k (map fr (seq 0 lr)) fd rest
          (scan (map fr (seq 0 lr)) sk [] (map (fun j => F (i + j)%nat) (seq 0 (mv - i))))) -∗
    urun N h m (mword_of_int 0x136) (4 + n2) -∗
    (∀ (h' : CpuId) (m' : regfile) (F' : nat -> bv 8) (i' : nat) (sk' : bool),
        ⌜ (i' <= mv)%nat ⌝ -∗
        ⌜ gl_regs m0 sp0 ar fdv m' ⌝ -∗
        ⌜ m' !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i') ⌝ -∗
        ⌜ m' !!! Regidx s3_idx = mword_of_int (b01 sk') ⌝ -∗
        ⌜ m' !!! Regidx s4_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ⌜ m' !!! Regidx s6_idx = mword_of_int (Z.of_nat mv) ⌝ -∗
        ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 F' -∗
        tp (grep_k (map fr (seq 0 lr)) fd rest
              ([], map (fun j => F' (i' + j)%nat) (seq 0 (mv - i')), sk')) -∗
        urun N h' m' (mword_of_int 0x16a) (4 + n2) -∗ mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hmv Hn. induction d as [d IH] using lt_wf_ind.
    iIntros "#Hcode" (i h m F sk) "%Hd %Him %Hgl %Hs2 %Hs3 %Hs4 %Hs6 %HFm Hre Hbuf Ht Hrun Hend".
    iApply (wp_kgl_step h m m0 sp0 fdv ar fd dqr lr fr sk i mv F rest n2
              Hgl Hs2 Hs3 Hs4 Hs6 ltac:(lia) HFm Hn
              with "Hcode Hre Hbuf Ht Hrun").
    iSplit.
    - iIntros (h' m') "%Hgl' %Hs2' %Hs3' %Hs4' %Hs6' Hre Hbuf Ht Hrun".
      iApply ("Hend" $! h' m' F i sk with "[%] [%] [%] [%] [%] [%] Hre Hbuf Ht Hrun"); done.
    - iIntros (h' m' F' i') "%Hii %Hgl' %Hs2' %Hs3' %Hs4' %Hs6' %HFm' Hre Hbuf Ht Hrun".
      iApply (IH (mv - i')%nat ltac:(lia) with "Hcode [%] [%] [%] [%] [%] [%] [%] [%] Hre Hbuf Ht Hrun Hend");
        first [ reflexivity | lia | done ].
  Qed.

  (* ===================================================================== *)
  (* AFTER THE SCAN, 0x16a..0x1b0: the leftover moved to the front, and    *)
  (* the reset of a full buffer.  The back edge is the [bne] at 0x1a8,    *)
  (* which hands out the step's later.                                    *)
  (* ===================================================================== *)
  Lemma wp_kgl_post (h : CpuId) (m m0 : regfile) (sp0 fdv : mword 64) (ar fd : Z)
      (pat : bytes) (sk : bool) (i mv : nat) (F : nat -> bv 8) (rest : proc) (n2 : nat) :
    gl_regs m0 sp0 ar fdv m ->
    m !!! Regidx s2_idx = mword_of_int (gbuf + Z.of_nat i) ->
    m !!! Regidx s3_idx = mword_of_int (b01 sk) ->
    m !!! Regidx s4_idx = mword_of_int (Z.of_nat mv) ->
    m !!! Regidx s6_idx = mword_of_int (Z.of_nat mv) ->
    (i <= mv <= 1023)%nat -> (0 < mv)%nat ->
    grep_code γt -∗ ubytes γd gbuf 1024 F -∗
    tp (grep_k pat fd rest ([], map (fun j => F (i + j)%nat) (seq 0 (mv - i)), sk)) -∗
    urun N h m (mword_of_int 0x16a) (4 + n2) -∗
    ▷ (∀ (h' : CpuId) (m' : regfile) (F' : nat -> bv 8) (skip' : bool) (left' : bytes),
         ⌜ gl_regs m0 sp0 ar fdv m' ⌝ -∗
         ⌜ m' !!! Regidx s3_idx = mword_of_int (b01 skip') ⌝ -∗
         ⌜ m' !!! Regidx s6_idx = mword_of_int (Z.of_nat (length left')) ⌝ -∗
         ⌜ (length left' < 1023)%nat ⌝ -∗
         ⌜ map F' (seq 0 (length left')) = left' ⌝ -∗
         ubytes γd gbuf 1024 F' -∗
         tp (grep_go pat fd skip' [] left' rest) -∗
         urun N h' m' (mword_of_int 0x16e) (4 + n2) -∗ mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hgl Hs2 Hs3 Hs4 Hs6 Him Hmv. iIntros "#Hcode Hbuf Ht Hrun Hloop".
    pose proof Hgl as (Hsp & _ & _ & Hs5 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
    assert (Hbufv : gbuf = 8208) by reflexivity.
    (* ---- 0x16a  bgtz s6,0x192 -- m > 0, always ---- *)
    iApply (wp_uk_btype0l N h m (mword_of_int 0x16a) (mword_of_int 40 : mword 13) s6_idx
              BLT true (mword_of_int 0x192) (4 + n2)
              ltac:(cbn [uv_btaken]; rewrite Hs6 zero_reg_moi;
                    rewrite (moi_lt_s 0 (Z.of_nat mv) ltac:(unfold Z63; lia) ltac:(unfold Z63; lia));
                    symmetry; apply Z.ltb_lt; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity) with "[] Hrun").
    { iApply (uis_grep_16a with "Hcode"). }
    iIntros (h1) "Hrun".
    (* ---- 0x192  sub a5,s2,s7 -- p - buf ---- *)
    iApply (wp_uk_sub N h1 m (mword_of_int 0x192) s2_idx s7_idx a5_idx
              (mword_of_int (Z.of_nat i)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2 Hs7 moi_sub; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_grep_192 with "Hcode"). }
    iIntros (h2) "Hrun". pcn.
    set (m1 := <[Regidx a5_idx := regval_into_reg (mword_of_int (Z.of_nat i) : mword 64)]> m).
    (* ---- 0x196  subw a2,s4,a5 -- m -= p - buf ---- *)
    iApply (wp_uk_subw N h2 m1 (mword_of_int 0x196) s4_idx a5_idx a2_idx
              (mword_of_int (Z.of_nat (mv - i))) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m1; rgl; rewrite Hs4 moi_subw; [ f_equal; lia | unfold Z31; lia ])
              with "[] Hrun").
    { iApply (uis_grep_196 with "Hcode"). }
    iIntros (h3) "Hrun". pcn.
    set (m2 := <[Regidx a2_idx := regval_into_reg (mword_of_int (Z.of_nat (mv - i)) : mword 64)]> m1).
    (* ---- 0x19a  c.mv s6,a2 ; 0x19c  c.mv a1,s2 ; 0x19e  c.mv a0,s7 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x19a) s6_idx a2_idx
              (mword_of_int (Z.of_nat (mv - i))) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m2; rgl; rewrite moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_19a with "Hcode"). }
    iIntros (h4) "Hrun". pcn.
    set (m3 := <[Regidx s6_idx := regval_into_reg (mword_of_int (Z.of_nat (mv - i)) : mword 64)]> m2).
    iApply (wp_uk_cmv N h4 m3 (mword_of_int 0x19c) a1_idx s2_idx
              (mword_of_int (gbuf + Z.of_nat i)) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m3 /m2 /m1; rgl; rewrite Hs2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_19c with "Hcode"). }
    iIntros (h5) "Hrun". pcn.
    set (m4 := <[Regidx a1_idx := regval_into_reg (mword_of_int (gbuf + Z.of_nat i) : mword 64)]> m3).
    iApply (wp_uk_cmv N h5 m4 (mword_of_int 0x19e) a0_idx s7_idx
              (mword_of_int gbuf) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m4 /m3 /m2 /m1; rgl; rewrite Hs7 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_19e with "Hcode"). }
    iIntros (h6) "Hrun". pcn.
    set (m5 := <[Regidx a0_idx := regval_into_reg (mword_of_int gbuf : mword 64)]> m4).
    (* ---- 0x1a0  jal memmove ---- *)
    iApply (wp_uk_jal N h6 m5 (mword_of_int 0x1a0) (mword_of_int 670 : mword 21) ra_idx
              (mword_of_int GrepSyms.memmove) (mword_of_int 0x1a4) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.memmove; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.memmove; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_1a0 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m6 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x1a4 : mword 64)]> m5).
    iDestruct (buf_open mv 0 F ltac:(lia) with "Hbuf") as "(HW & H0 & HR)".
    assert (Ed : Z.to_nat (gbuf + Z.of_nat i - gbuf) = i) by lia.
    assert (Ha2 : m6 !!! Regidx a2_idx
                  = sign_extend' 64 (mword_of_int (Z.of_nat (mv - i)) : mword 32)).
    { rewrite /m6 /m5 /m4 /m3 /m2; rgl. rewrite sext32_count; [ reflexivity | unfold Z31; lia ]. }
    iApply (wp_kgrep_memmove N h7 m6 gbuf (gbuf + Z.of_nat i) (mv - i) F (2 + n2)
              ltac:(rewrite /m6 /m5; rgl; reflexivity)
              ltac:(rewrite /m6 /m5 /m4; rgl; reflexivity)
              Ha2 ltac:(lia) ltac:(change (2 ^ 31) with 2147483648; lia)
              with "Hcode [HW] Hrun").
    { rewrite Ed. replace (i + (mv - i))%nat with mv by lia. iExact "HW". }
    rewrite Ed. replace (i + (mv - i))%nat with mv by lia.
    iIntros "HW" (h8 m7) "%Hcs7 Hrun".
    assert (Eret : ret_pc (m6 !!! Regidx ra_idx) = (mword_of_int 0x1a4 : mword 64))
      by (rewrite /m6; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (F' := mm_post i (mv - i) F).
    iDestruct (buf_close_same mv 0 F' ltac:(lia) with "[HW] [H0] [HR]") as "Hbuf".
    { iExact "HW". }
    { rewrite /ubytes /ubytesq /=. done. }
    { iApply (ubytes_ext_w with "HR"). intros j Hj. rewrite /F' /mm_post.
      destruct (Nat.ltb_spec (mv + 0 + j) (mv - i)); [ lia | reflexivity ]. }
    assert (Hk7 : rkeep ([22] ++ Wcaller) m m7).
    { eapply (rkeep_call ([22] ++ Wcaller) m m6 m7); [ | | exact Hcs7 ].
      - intros r Hr. apply rin_app_caller. exact Hr.
      - rewrite /m6 /m5 /m4 /m3 /m2 /m1; rk. }
    assert (Hs6_7 : m7 !!! Regidx s6_idx = mword_of_int (Z.of_nat (mv - i))).
    { rewrite (Hcs7 s6_idx ltac:(vm_compute; reflexivity)) /m6 /m5 /m4; rgl. reflexivity. }
    (* ---- 0x1a4  li a5,1023 ---- *)
    iApply (wp_uk_li N h8 m7 (mword_of_int 0x1a4) (mword_of_int 1023 : mword 12) a5_idx
              (mword_of_int 1023) (4 + n2)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_1a4 with "Hcode"). }
    iIntros (h9) "Hrun". pcn.
    set (m8 := <[Regidx a5_idx := regval_into_reg (mword_of_int 1023 : mword 64)]> m7).
    assert (Hk8 : rkeep ([22] ++ Wcaller) m m8) by (rewrite /m8; rk).
    assert (Hgl8 : gl_regs m0 sp0 ar fdv m8)
      by (apply (gl_regs_keep ([22] ++ Wcaller) m0 sp0 ar fdv m m8);
          [ vm_compute; reflexivity .. | assumption | assumption ]).
    (* the leftover, now at the front *)
    assert (Hleft : map F' (seq 0 (mv - i)) = map (fun j => F (i + j)%nat) (seq 0 (mv - i))).
    { apply map_seq_ext. intros j Hj. rewrite /F' /mm_post.
      destruct (Nat.ltb_spec j (mv - i)); [ f_equal; lia | lia ]. }
    (* ---- 0x1a8  bne s6,a5,0x16e -- THE BACK EDGE ---- *)
    iApply (wp_uk_btype_later N h9 m8 (mword_of_int 0x1a8) (mword_of_int 8134 : mword 13)
              a5_idx s6_idx BNE (negb (Z.of_nat (mv - i) =? 1023)) (mword_of_int 0x16e) (4 + n2)
              ltac:(cbn [uv_btaken]; rewrite /m8; rgl; rewrite Hs6_7;
                    rewrite (moi_neq_vec (Z.of_nat (mv - i)) 1023 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia)); reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_1a8 with "Hcode"). }
    iNext. iIntros (h10) "Hrun".
    destruct (Z.eqb_spec (Z.of_nat (mv - i)) 1023) as [Hfull | Hshort]; cbn [negb].
    - (* m == 1023: the line is too long; skip = 1, m = 0 *)
      pcn.
      iApply (wp_uk_cmv N h10 m8 (mword_of_int 0x1ac) s3_idx s11_idx
                (mword_of_int (b01 true)) (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hgl8))))))));
                      rewrite moi_add_zero_l; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_1ac with "Hcode"). }
      iIntros (h11) "Hrun". pcn.
      set (m9 := <[Regidx s3_idx := regval_into_reg (mword_of_int (b01 true) : mword 64)]> m8).
      iApply (wp_uk_cli N h11 m9 (mword_of_int 0x1ae) (mword_of_int 0 : mword 6) s6_idx (4 + n2)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_grep_1ae with "Hcode"). }
      iIntros (h12) "Hrun". pcn.
      set (m10 := <[Regidx s6_idx := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> m9).
      iApply (wp_uk_cj N h12 m10 (mword_of_int 0x1b0) (mword_of_int 2015 : mword 11)
                (mword_of_int 0x16e) (4 + n2)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_1b0 with "Hcode"). }
      iIntros (h13) "Hrun".
      iApply ("Hloop" $! h13 m10 F' true [] with "[%] [%] [%] [%] [%] Hbuf [Ht] Hrun").
      + apply (gl_regs_keep [19; 22] m0 sp0 ar fdv m8 m10);
          [ vm_compute; reflexivity .. | rewrite /m10 /m9; rk | exact Hgl8 ].
      + rewrite /m10 /m9; rgl. reflexivity.
      + rewrite /m10; rgl. apply bv_eq; vm_compute; reflexivity.
      + simpl. lia.
      + reflexivity.
      + rewrite grep_k_full; [ iExact "Ht" | rewrite length_map length_seq; lia ].
    - (* m < 1023: the leftover is carried to the next read *)
      iApply ("Hloop" $! h10 m8 F' sk (map (fun j => F (i + j)%nat) (seq 0 (mv - i)))
                with "[%] [%] [%] [%] [%] Hbuf [Ht] Hrun").
      + exact Hgl8.
      + rewrite (Hk8 s3_idx ltac:(vm_compute; reflexivity)). exact Hs3.
      + rewrite length_map length_seq /m8; rgl. exact Hs6_7.
      + rewrite length_map length_seq. lia.
      + rewrite length_map length_seq. exact Hleft.
      + rewrite grep_k_short; [ iExact "Ht" | rewrite length_map length_seq; lia ].
  Qed.

  (* ===================================================================== *)
  (* THE LOOP, from its head: by Loeb, paid at the back edge's later.      *)
  (* ===================================================================== *)
  Lemma wp_kgl_loop (m0 : regfile) (sp0 fdv : mword 64) (ar fd : Z) (dqr : dfrac)
      (lr : nat) (fr : nat -> bv 8) (rest : proc) (n2 : nat) :
    bv_signed (trunc32 fdv) = fd ->
    (mh_words (grep_body (map fr (seq 0 lr))) <= n2)%nat ->
    grep_code γt -∗
    ∀ (h : CpuId) (m : regfile) (F : nat -> bv 8) (skip : bool) (left : bytes),
      ⌜ gl_regs m0 sp0 ar fdv m ⌝ -∗
      ⌜ m !!! Regidx s3_idx = mword_of_int (b01 skip) ⌝ -∗
      ⌜ m !!! Regidx s6_idx = mword_of_int (Z.of_nat (length left)) ⌝ -∗
      ⌜ (length left < 1023)%nat ⌝ -∗
      ⌜ map F (seq 0 (length left)) = left ⌝ -∗
      ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 F -∗
      tp (grep_go (map fr (seq 0 lr)) fd skip [] left rest) -∗
      (∀ (h' : CpuId) (m' : regfile) (F' : nat -> bv 8),
         ⌜ gl_regs m0 sp0 ar fdv m' ⌝ -∗
         ustr γd dqr ar lr fr -∗ ubytes γd gbuf 1024 F' -∗ tp rest -∗
         urun N h' m' (mword_of_int 0x1b2) (4 + n2) -∗ mWP (Loop : expr riscv_lang)) -∗
      urun N h m (mword_of_int 0x16e) (4 + n2) -∗
      mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hfd Hn. iIntros "#Hcode". iLöb as "IH".
    iIntros (h m F skip left) "%Hgl %Hs3 %Hs6 %HL %Hleft Hre Hbuf Ht Hx Hrun".
    iApply (wp_kgl_head h m m0 sp0 fdv ar fd _ skip left F rest n2
              Hgl Hfd Hs3 Hs6 HL Hleft with "Hcode Hbuf Ht Hrun").
    iSplit.
    - iIntros (h' m' F') "%Hgl' Hbuf Ht Hrun".
      iApply ("Hx" with "[%] Hre Hbuf Ht Hrun"). exact Hgl'.
    - iIntros (h' m' F' mv) "%Hgl' %Hs2' %Hs3' %Hs4' %Hs6' %Hmv %HFm Hbuf Ht Hrun".
      iPoseProof (wp_kgl_scan m0 sp0 fdv ar fd dqr lr fr mv rest n2 (mv - 0) ltac:(lia) Hn
                    with "Hcode") as "Hscan".
      iApply ("Hscan" $! 0%nat h' m' F' skip
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hre Hbuf Ht Hrun");
        [ reflexivity | lia | exact Hgl' | exact Hs2' | exact Hs3' | exact Hs4' | exact Hs6'
        | exact HFm | ].
      iIntros (h2 m2 F2 i2 sk2) "%Hi2 %Hgl2 %Hs22 %Hs32 %Hs42 %Hs62 Hre Hbuf Ht Hrun".
      iApply (wp_kgl_post h2 m2 m0 sp0 fdv ar fd _ sk2 i2 mv F2 rest n2
                Hgl2 Hs22 Hs32 Hs42 Hs62 ltac:(lia) ltac:(lia) with "Hcode Hbuf Ht Hrun").
      iNext. iIntros (h3 m3 F3 skip3 left3) "%Hgl3 %Hs33 %Hs63 %HL3 %Hleft3 Hbuf Ht Hrun".
      iApply ("IH" $! h3 m3 F3 skip3 left3 with "[%] [%] [%] [%] [%] Hre Hbuf Ht Hx Hrun");
        done.
  Qed.

  (* ===================================================================== *)
  (* grep(pattern, fd), WHOLE: from the call to the return, paying the     *)
  (* tree [grep_go pat fd false [] [] rest] and leaving [rest] to pay.     *)
  (* The pattern at any fraction, handed back.                             *)
  (* ===================================================================== *)
  Lemma wp_kgrep_grep_gen (h : CpuId) (m : regfile) (dqr : dfrac) (ar : Z) (lr : nat)
      (fr : nat -> bv 8) (fdv : mword 64) (fd : Z) (g : nat -> bv 8) (rest : proc) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int ar -> m !!! Regidx a1_idx = fdv ->
    bv_signed (trunc32 fdv) = fd ->
    (grep_words (map fr (seq 0 lr)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr ar lr fr -∗
    ubytes γd GrepSyms.buf 1024 g -∗
    tp (grep_go (map fr (seq 0 lr)) fd false [] [] rest) -∗
    urun N h m (mword_of_int GrepSyms.grep) n -∗
    (∀ (h' : CpuId) (m' : regfile) (g' : nat -> bv 8),
       ⌜ucallee_saved m m'⌝ -∗ ustr γd dqr ar lr fr -∗
       ubytes γd GrepSyms.buf 1024 g' -∗ tp rest -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) n -∗ mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hfd Hn. iIntros "#Hcode Hre Hbuf Ht Hrun Hcont".
    remember (n - 18)%nat as n2 eqn:En2.
    assert (En : n = (14 + (4 + n2))%nat) by (unfold grep_words in Hn; lia).
    assert (Hn2 : (mh_words (grep_body (map fr (seq 0 lr))) <= n2)%nat)
      by (unfold grep_words in Hn; unfold grep_body; lia).
    rewrite En.
    iApply (wp_kgl_pro h m ar fdv n2 Ha0 Ha1 with "Hcode Hrun").
    iIntros (h1 m1) "%Hal8 %Hlo %Hgl %Hs3 %Hs6 Hfr Hrun".
    iPoseProof (wp_kgl_loop m (m !!! Regidx csp_rs1) fdv ar fd dqr lr fr rest n2 Hfd Hn2
                  with "Hcode") as "Hloop".
    iApply ("Hloop" $! h1 m1 g false [] with "[%] [%] [%] [%] [%] Hre Hbuf Ht [Hfr Hcont] Hrun").
    - exact Hgl.
    - exact Hs3.
    - exact Hs6.
    - simpl. lia.
    - reflexivity.
    - iIntros (h' m' F') "%Hgl' Hre Hbuf Ht Hrun".
      iApply (wp_kgl_epi h' m' m (m !!! Regidx csp_rs1) ar fdv n2 eq_refl Hal8 Hlo Hgl'
                with "Hcode Hfr Hrun").
      iIntros (h'' m'') "%Hcs Hrun".
      iApply ("Hcont" with "[%] Hre Hbuf Ht Hrun"). exact Hcs.
  Qed.

  (* ...AND THE STATEMENT OF RECORD: the pattern an argv string (main's) *)
  Lemma wp_kgrep_grep (h : CpuId) (m : regfile) (ar : Z) (lr : nat) (fr : nat -> bv 8)
      (fdv : mword 64) (fd : Z) (g : nat -> bv 8) (rest : proc) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int ar -> m !!! Regidx a1_idx = fdv ->
    bv_signed (trunc32 fdv) = fd ->
    (grep_words (map fr (seq 0 lr)) <= n)%nat ->
    grep_code γt -∗
    ustr γd DfracDiscarded ar lr fr -∗
    ubytes γd GrepSyms.buf 1024 g -∗
    tp (grep_go (map fr (seq 0 lr)) fd false [] [] rest) -∗
    urun N h m (mword_of_int GrepSyms.grep) n -∗
    (∀ (h' : CpuId) (m' : regfile) (g' : nat -> bv 8),
       ⌜ucallee_saved m m'⌝ -∗ ubytes γd GrepSyms.buf 1024 g' -∗ tp rest -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) n -∗ mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hfd Hn. iIntros "#Hcode Hre Hbuf Ht Hrun Hcont".
    iApply (wp_kgrep_grep_gen h m DfracDiscarded ar lr fr fdv fd g rest n Ha0 Ha1 Hfd Hn
              with "Hcode Hre Hbuf Ht Hrun").
    iIntros (h' m' g') "%Hcs _ Hbuf Ht Hrun".
    iApply ("Hcont" with "[%] Hbuf Ht Hrun"). exact Hcs.
  Qed.

End UkGrepLoop.
