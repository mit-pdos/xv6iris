(* UProofShLex.v -- the VERIFIED-EXECUTION proofs of `sh''s LEXER:
   [peek] @0x448 and [gettoken] @0x310
   (claude-notes/projects/user-sh.md).

   Both are 64-byte-frame functions whose body is a [strchr]-guarded
   whitespace scan, so this file carries several pieces of shared
   machinery before either:

     - the 64-byte frames are built out of UmodeFrame.v's size-generic
       [wp_uv_frame_store] / [wp_uv_frame_load], one line per slot:
       [wp_uv_prologue16] / [wp_uv_epilogue16] cannot serve, because the
       frame is 64 bytes AND the spill SET differs between the two
       functions (peek saves ra,s0..s5; gettoken saves ra,s0..s6).

     - §2 the pure arithmetic of [USpecSh.sh_skipws] / [sh_toklen], one
       step at a time, in the shape the scan loops consume them.

     - §3 THE WHITESPACE-SKIP LOOP, which occurs THREE times in the two
       functions (peek @0x46a, gettoken @0x336 and @0x398) with an
       identical 24-byte layout, and again inside [parseredirs].  It is
       proved ONCE ([wp_sh_wsloop] for the body, [wp_sh_wsskip] for the
       entry test plus the body), parameterised by the entry address, the
       [jal] displacement, the eight [uinstr] facts and the register that
       holds [es] at the entry test.  [gettoken] needs it verbatim at
       0x336 and 0x398.

     - §3 also carries [spill7_facts] and §5 [spill8_facts] -- a whole
       spill tower read back in ONE lemma (each slot's value, the
       untouched complement, and key preservation) -- with [wp_sh_epi7]
       for the seven-slot reload, which [gettoken]'s eight-slot epilogue
       reuses and then adds its own [c.ldsp s6,0(sp)].

     - §5 also splits [gettoken]'s three JOIN POINTS into their own
       lemmas, because gcc's control flow reconverges at each: 0x3b0
       ([*ps = s] and the epilogue), 0x390 (the second whitespace scan on
       top of it), 0x38c ([*eq = s] on top of THAT) and 0x388 ([if (eq)]
       on top of THAT).  The word scan at 0x400 tells its two exits apart
       by [atend], which is invariant along the loop because
       [i + sh_toklen (drop i bs)] is.

   Neither function is entered on the SYMBOL arms of gettoken's switch:
   [sh_no_symbols] excludes them, and §5's [sym_excl] is what turns that
   premise into the seven byte-value disequalities gcc's comparison chain
   needs.  The one place the code's arithmetic is not a plain 64-bit add
   is [addiw a5,a5,-40; zext.b a5], whose value goes NEGATIVE; §2's
   [sext32_low32] and [moi_and255] are that step. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeArith UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeSh USpecSh USpecShParse.
Require Import UProofShLib.
Require User.ShSyms User.ShInstrs User.ShData.
Require Import UmodeAbi.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.


(* ===================================================================== *)
(* §2 THE PURE LEXICAL MODEL.                                             *)
(*                                                                        *)
(* [sh_skipws] and [sh_toklen] are [list_find] indices; the scan loops     *)
(* consume the buffer HEAD-FIRST, so what a loop step needs is how each    *)
(* reacts to a head byte.  Everything here is closed [Prop] arithmetic --  *)
(* no [pt], no image, no protocol.                                        *)
(* ===================================================================== *)

Local Lemma bv8_ne0 (b : bv 8) : bv_unsigned b <> 0 -> b <> ubyte0.
Proof.
  intros H He. apply H. rewrite He. vm_compute. reflexivity.
Qed.

Local Lemma bv8_is0 (b : bv 8) : bv_unsigned b = 0 <-> b = ubyte0.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H. vm_compute. reflexivity.
  - intro H. subst b. vm_compute. reflexivity.
Qed.

Local Lemma bv8_rng (b : bv 8) : 0 <= bv_unsigned b < Z64.
Proof.
  pose proof (bv_unsigned_in_range 8 b) as Hr.
  assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E in Hr. unfold Z64. lia.
Qed.

Local Lemma not_in_win (ws : list (Z * Z)) (a n k : Z) :
  (a, n) ∈ ws -> ~ uM_in_windows ws k -> k < a \/ a + n <= k.
Proof.
  intros Hin Hnot.
  destruct (Z.lt_ge_cases k a) as [ Hlt | Hge ]; [ left; lia | ].
  destruct (Z.lt_ge_cases k (a + n)) as [ Hlt2 | Hge2 ]; [ | right; lia ].
  exfalso. apply Hnot. exists (a, n). split; [ exact Hin | simpl; lia ].
Qed.

(* ---- [sh_skipws], one head byte at a time --------------------------- *)

Lemma sh_skipws_nil : sh_skipws [] = 0%nat.
Proof. reflexivity. Qed.

Lemma sh_skipws_cons_ws (b : bv 8) (bs : list (bv 8)) :
  sh_is_ws b = true -> sh_skipws (b :: bs) = S (sh_skipws bs).
Proof.
  intro Hb. unfold sh_skipws. cbn [list_find length].
  destruct (decide (sh_is_ws b = false)) as [Hf | _];
    [ rewrite Hb in Hf; discriminate | ].
  destruct (list_find (fun x => sh_is_ws x = false) bs) as [ [k x] | ];
    reflexivity.
Qed.

Lemma sh_skipws_cons_nws (b : bv 8) (bs : list (bv 8)) :
  sh_is_ws b = false -> sh_skipws (b :: bs) = 0%nat.
Proof.
  intro Hb. unfold sh_skipws. cbn [list_find].
  destruct (decide (sh_is_ws b = false)) as [_ | Hf];
    [ reflexivity | exfalso; exact (Hf Hb) ].
Qed.

Lemma sh_skipws_le (bs : list (bv 8)) : (sh_skipws bs <= length bs)%nat.
Proof.
  unfold sh_skipws.
  destruct (list_find (fun x => sh_is_ws x = false) bs) as [ [k x] | ] eqn:E;
    [ | lia ].
  apply list_find_Some in E as (Hk & _ & _).
  pose proof (lookup_lt_Some bs k x Hk). lia.
Qed.

(* ---- [sh_toklen], the same ------------------------------------------ *)

Lemma sh_toklen_nil : sh_toklen [] = 0%nat.
Proof. reflexivity. Qed.

Lemma sh_toklen_cons_in (b : bv 8) (bs : list (bv 8)) :
  sh_is_ws b || sh_is_sym b = false ->
  sh_toklen (b :: bs) = S (sh_toklen bs).
Proof.
  intro Hb. unfold sh_toklen. cbn [list_find]. case_decide as Ht.
  - exfalso. rewrite Hb in Ht. exact Ht.
  - cbn [length].
    destruct (list_find (fun x => sh_is_ws x || sh_is_sym x) bs) as [ [k x] | ];
      reflexivity.
Qed.

Lemma sh_toklen_cons_stop (b : bv 8) (bs : list (bv 8)) :
  sh_is_ws b || sh_is_sym b = true -> sh_toklen (b :: bs) = 0%nat.
Proof.
  intro Hb. unfold sh_toklen. cbn [list_find]. case_decide as Ht.
  - reflexivity.
  - exfalso. apply Ht. rewrite Hb. exact I.
Qed.

Lemma sh_toklen_le (bs : list (bv 8)) : (sh_toklen bs <= length bs)%nat.
Proof.
  unfold sh_toklen.
  destruct (list_find (fun x => sh_is_ws x || sh_is_sym x) bs) as [ [k x] | ] eqn:E;
    [ | lia ].
  apply list_find_Some in E as (Hk & _ & _).
  pose proof (lookup_lt_Some bs k x Hk). lia.
Qed.

(* ---- what [strchr] returns on the two static tables ------------------ *)

Lemma ustr_find_not_elem (bs : list (bv 8)) (c : bv 8) :
  c ∉ bs -> ustr_find bs c = None.
Proof.
  intro Hc. unfold ustr_find.
  assert (E : list_find (fun x => x = c) bs = None).
  { apply list_find_None. apply Forall_forall. intros x Hx He.
    apply Hc. rewrite <- He. exact (proj2 (elem_of_list_In bs x) Hx). }
  rewrite E. reflexivity.
Qed.

Lemma ustr_find_elem (bs : list (bv 8)) (c : bv 8) :
  c ∈ bs -> exists i : nat, ustr_find bs c = Some i /\ (i < length bs)%nat.
Proof.
  intro Hc. unfold ustr_find.
  destruct (list_find_elem_of (fun x => x = c) bs c Hc eq_refl) as ([k x] & E).
  pose proof E as E'. apply list_find_Some in E' as (Hk & _ & _).
  exists k. rewrite E. cbn [fmap option_fmap option_map fst].
  split; [ reflexivity | exact (lookup_lt_Some bs k x Hk) ].
Qed.

(* the two static tables have no NUL among their bytes -- [strchr]'s [Hnz] *)
Lemma sh_ws_nz : forall (j : nat) (b : bv 8), sh_ws_bytes !! j = Some b -> b <> ubyte0.
Proof.
  intros j b Hj. apply bv8_ne0.
  destruct j as [|[|[|[|[|j]]]]]; cbn in Hj; try discriminate;
    injection Hj as Hj; subst b; vm_compute; discriminate.
Qed.

Lemma sh_sym_nz : forall (j : nat) (b : bv 8), sh_sym_bytes !! j = Some b -> b <> ubyte0.
Proof.
  intros j b Hj. apply bv8_ne0.
  destruct j as [|[|[|[|[|[|[|j]]]]]]]; cbn in Hj; try discriminate;
    injection Hj as Hj; subst b; vm_compute; discriminate.
Qed.

Lemma sh_ws_len : length sh_ws_bytes = 5%nat.
Proof. reflexivity. Qed.

Lemma sh_sym_len : length sh_sym_bytes = 7%nat.
Proof. reflexivity. Qed.

(* what [strchr(whitespace, b)] RETURNS, as a [Z], read off [sh_is_ws] *)
Lemma sh_ws_chr_nws (b : bv 8) :
  sh_is_ws b = false -> ustr_find sh_ws_bytes b = None.
Proof.
  unfold sh_is_ws. intro Hb. apply bool_decide_eq_false in Hb.
  exact (ustr_find_not_elem sh_ws_bytes b Hb).
Qed.

Lemma sh_ws_chr_ws (b : bv 8) :
  sh_is_ws b = true ->
  exists i : nat, ustr_find sh_ws_bytes b = Some i /\ (i < 5)%nat.
Proof.
  unfold sh_is_ws. intro Hb. apply bool_decide_eq_true in Hb.
  destruct (ustr_find_elem sh_ws_bytes b Hb) as (i & Hi & Hlt).
  exists i. rewrite sh_ws_len in Hlt. exact (conj Hi Hlt).
Qed.

Lemma sh_sym_chr_nsym (b : bv 8) :
  sh_is_sym b = false -> ustr_find sh_sym_bytes b = None.
Proof.
  unfold sh_is_sym. intro Hb. apply bool_decide_eq_false in Hb.
  exact (ustr_find_not_elem sh_sym_bytes b Hb).
Qed.

Lemma sh_sym_chr_sym (b : bv 8) :
  sh_is_sym b = true ->
  exists i : nat, ustr_find sh_sym_bytes b = Some i /\ (i < 7)%nat.
Proof.
  unfold sh_is_sym. intro Hb. apply bool_decide_eq_true in Hb.
  destruct (ustr_find_elem sh_sym_bytes b Hb) as (i & Hi & Hlt).
  exists i. rewrite sh_sym_len in Hlt. exact (conj Hi Hlt).
Qed.

(* the byte a whitespace skip stops on is not whitespace -- what puts
   [gettoken]'s switch in its default arm *)
Lemma sh_skipws_stop (bs : list (bv 8)) (b : bv 8) :
  bs !! sh_skipws bs = Some b -> sh_is_ws b = false.
Proof.
  unfold sh_skipws.
  destruct (list_find (fun x => sh_is_ws x = false) bs) as [ [i x] | ] eqn:E.
  - intro Hl. apply list_find_Some in E as (Hi & HP & _).
    rewrite Hi in Hl. injection Hl as Hl. rewrite <- Hl. exact HP.
  - intro Hl. exfalso. pose proof (lookup_lt_Some bs _ b Hl). lia.
Qed.

Lemma bv8_val_eq (b : bv 8) (z : Z) :
  0 <= z < 256 -> bv_unsigned b = z -> b = Z_to_bv 8 z.
Proof.
  intros Hz He. apply bv_eq. rewrite He.
  symmetry. apply Z_to_bv_small.
  assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity). rewrite E. lia.
Qed.

(* "[b] is not the symbol byte [z]" -- the seven readings gcc's switch
   needs, all discharged from [sh_is_sym b = false] by computation *)
Lemma sym_excl (b : bv 8) (z : Z) :
  sh_is_sym b = false -> 0 <= z < 256 -> sh_is_sym (Z_to_bv 8 z) = true ->
  bv_unsigned b <> z.
Proof.
  intros Hf Hz Ht He. rewrite (bv8_val_eq b z Hz He) in Hf.
  rewrite Ht in Hf. discriminate.
Qed.

(* ---- the two bit-level facts gcc's switch prologue needs --------------
   [addiw a5,a5,-40] on a byte-sized value goes NEGATIVE, so
   UmodeArith's [moi_addw] (which wants a result in [0, 2^31)) does not
   apply; what holds instead is that a 32-bit truncate-then-sign-extend is
   the IDENTITY on any value that already fits a signed 32-bit word.  And
   [zext.b] is [andi rd,rs,255], i.e. a [Z.land] with [Z.ones 8]. --------- *)

Lemma sext32_low32 (z : Z) :
  - Z31 <= z < Z31 ->
  (sign_extend' 64 (subrange_vec_dec (mword_of_int z : mword 64) 31 0 : mword 32)
   : mword 64) = mword_of_int z.
Proof.
  intro Hz.
  apply bv_eq.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  unfold bv_signed, bv_swrap, bv_wrap.
  assert (Eh32 : bv_half_modulus 32 = Z31) by (vm_compute; reflexivity).
  rewrite Zmod32 Eh32 Zmod64 moi_unsigned low32_moi.
  assert (Hm2 : (z mod Z32 + Z31) mod Z32 = z + Z31).
  { symmetry. destruct (Z_lt_le_dec z 0) as [Hn | Hp].
    - assert (Hm : z mod Z32 = z + Z32)
        by (symmetry; apply (Zmod_unique z Z32 (-1) (z + Z32));
            unfold Z31, Z32 in *; lia).
      rewrite Hm.
      apply (Zmod_unique (z + Z32 + Z31) Z32 1 (z + Z31));
        unfold Z31, Z32 in *; lia.
    - assert (Hm : z mod Z32 = z)
        by (apply Z.mod_small; unfold Z31, Z32 in *; lia).
      rewrite Hm.
      apply (Zmod_unique (z + Z31) Z32 0 (z + Z31));
        unfold Z31, Z32 in *; lia. }
  rewrite Hm2. replace (z + Z31 - Z31) with z by lia. reflexivity.
Qed.

Lemma moi_and255 (z : Z) :
  and_vec (mword_of_int z : mword 64) (mword_of_int 255) = mword_of_int (z mod 256).
Proof.
  apply bv_eq. rewrite and_vec64_unsigned !moi_unsigned.
  assert (H255 : (255 : Z) mod Z64 = 255) by (unfold Z64; reflexivity).
  rewrite H255.
  replace (255 : Z) with (Z.ones 8) by (vm_compute; reflexivity).
  rewrite (Z.land_ones (z mod Z64) 8 ltac:(lia)).
  change (2 ^ 8) with 256.
  assert (Hd : (256 | Z64)) by (exists 72057594037927936; unfold Z64; reflexivity).
  rewrite <- (Znumtheory.Zmod_div_mod 256 Z64 z ltac:(lia)
                ltac:(unfold Z64; lia) Hd).
  rewrite (Z.mod_small (z mod 256) Z64
             ltac:(pose proof (Z.mod_pos_bound z 256 ltac:(lia)); unfold Z64; lia)).
  reflexivity.
Qed.

(* ===================================================================== *)
(* §3 THE WHITESPACE-SKIP LOOP.                                           *)
(* ===================================================================== *)

Section UProofShLex.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ---- the .data/.bss page, and the two tables on it ------------------ *)

  Local Lemma data_leaf (a : Z) :
    sh_layout pt hbase hlen -> SH_DATA_PG <= a < SH_DATA_PG + 4096 ->
    exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
      uleaf_ok (Load Data) w /\ uleaf_ok (Store Data) w.
  Proof.
    intros Hlay Ha. unfold SH_DATA_PG in Ha.
    destruct (shl_data _ _ _ Hlay) as (w & Hw & Hld & Hst).
    unfold SH_DATA_PG in Hw.
    assert (Hq : a / 4096 = 2)
      by (symmetry; apply (Zdiv_unique a 4096 2 (a - 8192)); lia).
    exists w. rewrite (sh_svpn_page a ltac:(lia)).
    rewrite Hq. replace (4096 * 2) with 8192 by lia.
    split_and!; assumption.
  Qed.

  Local Lemma data_rd (M : gmap Z (bv 8)) (a n : Z) :
    sh_layout pt hbase hlen ->
    SH_DATA_PG <= a -> 0 <= n -> a + n <= SH_DATA_PG + 4096 ->
    (forall j : Z, 0 <= j < n -> exists b : bv 8, M !! (a + j) = Some b) ->
    uv_rd pt M a n.
  Proof.
    intros Hlay Ha Hn Hhi Hb.
    unfold SH_DATA_PG in Ha. unfold SH_DATA_PG in Hhi.
    assert (Hhi2 : a + n <= 12288) by lia.
    constructor.
    - lia.
    - lia.
    - change (2 ^ 38) with 274877906944. lia.
    - intros j Hj.
      destruct (data_leaf (a + j) Hlay ltac:(unfold SH_DATA_PG; lia))
        as (w & Hw & Hld & _).
      exists w. exact (conj Hw Hld).
    - exact Hb.
  Qed.

  Local Lemma ustr_at_bytes (M : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) :
    ustr_at M a bs ->
    forall j : Z, 0 <= j < Z.of_nat (length bs) + 1 ->
      exists b : bv 8, M !! (a + j) = Some b.
  Proof.
    intros (Hb & Hn) j Hj.
    destruct (decide (j = Z.of_nat (length bs))) as [He | Hne].
    - exists ubyte0. rewrite He. exact Hn.
    - destruct (lookup_lt_is_Some_2 bs (Z.to_nat j) ltac:(lia)) as (b & Hbj).
      exists b. replace (a + j) with (a + Z.of_nat (Z.to_nat j)) by lia.
      exact (Hb (Z.to_nat j) b Hbj).
  Qed.

  Local Lemma ws_table_rd (M : gmap Z (bv 8)) :
    sh_layout pt hbase hlen -> sh_tables_ok M ->
    uv_rd pt M SH_WHITESPACE (Z.of_nat (length sh_ws_bytes) + 1).
  Proof.
    intros Hlay (Hws & _). rewrite sh_ws_len.
    apply (data_rd M SH_WHITESPACE 6 Hlay);
      [ unfold SH_WHITESPACE, SH_DATA_PG; lia | lia
      | unfold SH_WHITESPACE, SH_DATA_PG; lia | ].
    intros j Hj. exact (ustr_at_bytes M SH_WHITESPACE sh_ws_bytes Hws j
                          ltac:(rewrite sh_ws_len; lia)).
  Qed.

  Local Lemma sym_table_rd (M : gmap Z (bv 8)) :
    sh_layout pt hbase hlen -> sh_tables_ok M ->
    uv_rd pt M SH_SYMBOLS (Z.of_nat (length sh_sym_bytes) + 1).
  Proof.
    intros Hlay (_ & Hsy). rewrite sh_sym_len.
    apply (data_rd M SH_SYMBOLS 8 Hlay);
      [ unfold SH_SYMBOLS, SH_DATA_PG; lia | lia
      | unfold SH_SYMBOLS, SH_DATA_PG; lia | ].
    intros j Hj. exact (ustr_at_bytes M SH_SYMBOLS sh_sym_bytes Hsy j
                          ltac:(rewrite sh_sym_len; lia)).
  Qed.

  (* ---- THE LOOP'S IMAGE INVARIANT ------------------------------------- *)
  (* Everything the lexer reads -- the program image, the two tables and    *)
  (* the command buffer -- sits BELOW the frame, so one bound transports    *)
  (* all of it across a callee's frame writes.                             *)

  Local Definition lex_ok (M : gmap Z (bv 8)) (sp0 : mword 64) (s0 : Z)
      (bs : list (bv 8)) : Prop :=
    sh_img_sub M /\ sh_tables_ok M /\ sh_buf_ok M s0 bs /\
    uv_rd pt M s0 (Z.of_nat (length bs) + 1) /\ uv_stack pt M sp0 80.

  Local Lemma lex_ok_below (M M' : gmap Z (bv 8)) (sp0 : mword 64) (s0 : Z)
      (bs : list (bv 8)) (a n : Z) :
    uM_only M M' a n ->
    12288 <= a -> s0 + Z.of_nat (length bs) + 1 <= a ->
    lex_ok M sp0 s0 bs -> lex_ok M' sp0 s0 bs.
  Proof.
    intros Honly Ha Hbuf (Himg & Htab & Hbuf0 & Hrd & Hst).
    pose proof Honly as (Hdom & Heq).
    assert (Hlo : forall k : Z, k < a -> M' !! k = M !! k)
      by (intros k Hk; apply Heq; left; exact Hk).
    split_and!.
    - split.
      + intros k b Hk. rewrite (Hlo k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
        exact (sh_img_text M Himg k b Hk).
      + intros k b Hk. rewrite (Hlo k ltac:(pose proof (sh_data_key_lt k b Hk); lia)).
        exact (sh_img_data M Himg k b Hk).
    - destruct Htab as ((Hw1 & Hw2) & (Hs1 & Hs2)). split; split.
      + intros j b Hj.
        pose proof (lookup_lt_Some sh_ws_bytes j b Hj) as Hjl.
        rewrite sh_ws_len in Hjl.
        rewrite (Hlo (SH_WHITESPACE + Z.of_nat j)
                   ltac:(unfold SH_WHITESPACE, SH_DATA_PG; lia)).
        exact (Hw1 j b Hj).
      + rewrite sh_ws_len.
        rewrite (Hlo (SH_WHITESPACE + Z.of_nat 5%nat)
                   ltac:(unfold SH_WHITESPACE, SH_DATA_PG; lia)).
        rewrite sh_ws_len in Hw2. exact Hw2.
      + intros j b Hj.
        pose proof (lookup_lt_Some sh_sym_bytes j b Hj) as Hjl.
        rewrite sh_sym_len in Hjl.
        rewrite (Hlo (SH_SYMBOLS + Z.of_nat j)
                   ltac:(unfold SH_SYMBOLS, SH_DATA_PG; lia)).
        exact (Hs1 j b Hj).
      + rewrite sh_sym_len.
        rewrite (Hlo (SH_SYMBOLS + Z.of_nat 7%nat)
                   ltac:(unfold SH_SYMBOLS, SH_DATA_PG; lia)).
        rewrite sh_sym_len in Hs2. exact Hs2.
    - destruct Hbuf0 as ((Hb1 & Hb2) & Hnz). split; [ split | exact Hnz ].
      + intros j b Hj. pose proof (lookup_lt_Some bs j b Hj) as Hjl.
        rewrite (Hlo (s0 + Z.of_nat j) ltac:(lia)). exact (Hb1 j b Hj).
      + rewrite (Hlo (s0 + Z.of_nat (length bs)) ltac:(lia)). exact Hb2.
    - constructor; try (destruct Hrd; assumption).
      intros j Hj. destruct (urd_bytes _ _ _ _ Hrd j Hj) as (b & Hb).
      exists b. rewrite (Hlo (s0 + j) ltac:(lia)). exact Hb.
    - exact (uv_stack_dom pt M M' sp0 80 Hdom Hst).
  Qed.

  (* the callee's frame, one level down: [sp0 - 64] as an [mword] *)
  Local Lemma spA_facts (M : gmap Z (bv 8)) (sp0 : mword 64) :
    uv_stack pt M sp0 80 ->
    uv_stack pt M (mword_of_int (uint sp0 - 64) : mword 64) 16 /\
    uint (mword_of_int (uint sp0 - 64) : mword 64) = uint sp0 - 64.
  Proof.
    intro Hst.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hhi.
    change (2 ^ 38) with 274877906944 in Hhi.
    destruct (uv_stack_split pt M sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hst1 & Hst2).
    rewrite (uv_stack_sp_moi pt M sp0 64 Hst1) in Hst2.
    split; [ exact Hst2 | apply uint_moi; unfold Z64; lia ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE WHITESPACE-SKIP LOOP, once for all three occurrences.            *)
  (*                                                                     *)
  (*   base+0   bgeu   s1,<es>,base+24   -- the ENTRY test (not here)     *)
  (*   base+4   lbu    a1,0(s1)          <- the loop HEAD                 *)
  (*   base+8   c.mv   a0,s3                                             *)
  (*   base+10  jal    ra,strchr                                         *)
  (*   base+14  c.beqz a0,base+24        -- not whitespace: out          *)
  (*   base+16  c.addi s1,s1,1                                          *)
  (*   base+18  bne    s2,s1,base+4      -- the BACK EDGE                *)
  (*   base+22  c.mv   s1,s2             -- s1 == s2 already             *)
  (*   base+24                           <- the exit                     *)
  (*                                                                     *)
  (* peek @0x46a, gettoken @0x336 and @0x398 are byte-identical here up   *)
  (* to the [jal] displacement, so [base] and [jimm] are the only         *)
  (* per-site parameters besides the eight [uinstr] facts.  Ordinary Rocq *)
  (* induction on the STRICT nat measure [length bs - i]; the branch leaf *)
  (* is later-free, so a bounded loop pays no [>].                       *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_wsloop (nn : nat) :
    forall (CIDp : CpuId) (base : Z) (jimm : mword 21)
      (M : gmap Z (bv 8)) (mE : regfile) (sp0 : mword 64)
      (s0 : Z) (bs : list (bv 8)) (i : nat) (bi : bv 8),
      (length bs - i < nn)%nat ->
      sh_layout pt hbase hlen ->
      lex_ok M sp0 s0 bs ->
      sh_frame_ok hbase hlen sp0 80 ->
      0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
      (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
         uinstr pt Mx (mword_of_int (base + 4)) false
           (LOAD (mword_of_int 0 : mword 12, Regidx s1_idx, Regidx a1_idx, true, 1))) ->
      (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
         uinstr pt Mx (mword_of_int (base + 8)) true
           (C_MV (Regidx a0_idx, Regidx s3_idx))) ->
      (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
         uinstr pt Mx (mword_of_int (base + 10)) false
           (JAL (jimm, Regidx ra_idx))) ->
      (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
         uinstr pt Mx (mword_of_int (base + 14)) true
           (C_BEQZ (mword_of_int 5 : mword 8, Cregidx (mword_of_int 2)))) ->
      (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
         uinstr pt Mx (mword_of_int (base + 16)) true
           (C_ADDI (mword_of_int 1 : mword 6, Regidx s1_idx))) ->
      (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
         uinstr pt Mx (mword_of_int (base + 18)) false
           (BTYPE (mword_of_int 8178 : mword 13, Regidx s1_idx, Regidx s2_idx, BNE))) ->
      (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
         uinstr pt Mx (mword_of_int (base + 22)) true
           (C_MV (Regidx s1_idx, Regidx s2_idx))) ->
      add_vec_int (mword_of_int (base + 4) : mword 64) 4 = mword_of_int (base + 8) ->
      add_vec_int (mword_of_int (base + 8) : mword 64) 2 = mword_of_int (base + 10) ->
      (mword_of_int ShSyms.strchr : mword 64)
        = add_vec (mword_of_int (base + 10)) (sign_extend' 64 jimm) ->
      (mword_of_int (base + 14) : mword 64)
        = add_vec_int (mword_of_int (base + 10) : mword 64) 4 ->
      (mword_of_int (base + 24) : mword 64)
        = add_vec (mword_of_int (base + 14))
            (sign_extend' 64 (sign_extend' 13
               (concat_vec (mword_of_int 5 : mword 8) ('b"0")))) ->
      add_vec_int (mword_of_int (base + 14) : mword 64) 2 = mword_of_int (base + 16) ->
      add_vec_int (mword_of_int (base + 16) : mword 64) 2 = mword_of_int (base + 18) ->
      (mword_of_int (base + 4) : mword 64)
        = add_vec (mword_of_int (base + 18))
            (sign_extend' 64 (mword_of_int 8178 : mword 13)) ->
      add_vec_int (mword_of_int (base + 18) : mword 64) 4 = mword_of_int (base + 22) ->
      add_vec_int (mword_of_int (base + 22) : mword 64) 2 = mword_of_int (base + 24) ->
      is_aligned_vaddr (Virtaddr (mword_of_int (base + 14) : mword 64)) 2 = true ->
      eq_vec (access_vec_dec (mword_of_int ShSyms.strchr : mword 64) 0) ('b"0") = true ->
      eq_vec (access_vec_dec (mword_of_int (base + 24) : mword 64) 0) ('b"0") = true ->
      eq_vec (access_vec_dec (mword_of_int (base + 4) : mword 64) 0) ('b"0") = true ->
      (i < length bs)%nat -> bs !! i = Some bi ->
      mE !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat i) : mword 64) ->
      mE !!! Regidx s2_idx
        = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
      mE !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64) ->
      mE !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh M mE -∗
      pc_is (CID := CIDp) (mword_of_int (base + 4)) -∗
      (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
         ⌜m' !!! Regidx s1_idx
            = (mword_of_int (s0 + Z.of_nat (i + sh_skipws (drop i bs)))
               : mword 64)⌝ -∗
         ⌜forall r : mword 5, ucallee_saved_idx r = true ->
            Regidx r <> Regidx s1_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         ⌜uM_only M M' (uint sp0 - 80) 16⌝ -∗
         uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
         pc_is (CID := CID) (mword_of_int (base + 24)) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction nn as [ | nn IH ];
      intros CIDp base jimm M mE sp0 s0 bs i bi Hmeas Hlay Hok Hfr Hs0 Hbufhi
             Hu4 Hu8 Hu10 Hu14 Hu16 Hu18 Hu22
             E4 E8 Etgt Elink Ebz E14 E16 Eback E18 E22
             Hal14 Halchr Hal24 Hal4
             Hi Hbi Hs1 Hs2 Hs3 Hsp.
    { exfalso. lia. }
    unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    destruct (spA_facts M sp0 Hst) as (HstA & HuA).
    pose proof Hbuf as Hbuf0.
    destruct Hbuf as ((Hbody & Hnul) & Hnzb).
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    assert (Hilen : (Z.of_nat i < Z.of_nat (length bs))%Z) by lia.
    assert (Hdrop : drop i bs = bi :: drop (S i) bs) by (apply drop_S; exact Hbi).
    iIntros "Hcg Hpc Hcont".
    (* ---- base+4  lbu a1,0(s1) ---- *)
    assert (Hva : (mword_of_int (s0 + Z.of_nat i) : mword 64)
                  = add_vec (mE !!! Regidx s1_idx)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hs1.
      assert (Hc0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc0 moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M s0 (Z.of_nat (length bs) + 1)
                (s0 + Z.of_nat i) Hrd ltac:(lia)) as (wl & Hll & Hokl).
    assert (Huva : uint (mword_of_int (s0 + Z.of_nat i) : mword 64)
                   = s0 + Z.of_nat i) by (apply uint_moi; unfold Z64; lia).
    assert (Hbyte : M !! (uint (mword_of_int (s0 + Z.of_nat i) : mword 64))
                    = Some bi) by (rewrite Huva; exact (Hbody i bi Hbi)).
    assert (Hcanon : uva_canon (mword_of_int (s0 + Z.of_nat i) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hwv : (mword_of_int (bv_unsigned bi) : mword 64)
                  = zero_extend' 64 (bi : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uv_lbu C pt Psh M mE (mword_of_int (base + 4))
              (mword_of_int 0 : mword 12) s1_idx a1_idx
              wl (mword_of_int (s0 + Z.of_nat i))
              (mword_of_int (bv_unsigned bi)) bi
              (Hu4 M Htext) ltac:(vm_compute; discriminate) Hva Hll Hokl
              Hcanon Hbyte Hwv with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (bv_unsigned bi) : mword 64)]> mE).
    iEval (rewrite E4) in "Hpc".
    (* ---- base+8  c.mv a0,s3 ---- *)
    assert (Hs3_1 : m1 !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64))
      by exact (eq_trans (upd_ne mE (Regidx a1_idx) (Regidx s3_idx) _
                            ltac:(vm_compute; discriminate)) Hs3).
    assert (Hwa0 : (mword_of_int SH_WHITESPACE : mword 64)
                   = add_vec zero_reg (m1 !!! Regidx s3_idx))
      by (rewrite Hs3_1; symmetry; apply moi_add_zero_l).
    iApply (wp_uv_cmv C pt Psh M m1 (mword_of_int (base + 8))
              a0_idx s3_idx (mword_of_int SH_WHITESPACE)
              (Hu8 M Htext) ltac:(vm_compute; discriminate) Hwa0
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int SH_WHITESPACE : mword 64)]> m1).
    iEval (rewrite E8) in "Hpc".
    (* ---- base+10  jal ra,strchr ---- *)
    iApply (wp_uv_jal C pt Psh M m2 (mword_of_int (base + 10))
              jimm ra_idx (mword_of_int ShSyms.strchr) (mword_of_int (base + 14))
              (Hu10 M Htext) ltac:(vm_compute; discriminate) Etgt Elink Halchr
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int (base + 14) : mword 64)]> m2).
    (* the registers the callee is handed, and the ones it leaves alone *)
    assert (Hpres3 : forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx a0_idx ->
              Regidx r <> Regidx a1_idx -> m3 !!! Regidx r = mE !!! Regidx r).
    { intros r H1 H2 H3.
      exact (eq_trans (upd_ne m2 (Regidx ra_idx) (Regidx r) _ H1)
               (eq_trans (upd_ne m1 (Regidx a0_idx) (Regidx r) _ H2)
                  (upd_ne mE (Regidx a1_idx) (Regidx r) _ H3))). }
    assert (Hsp3 : m3 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hpres3 sp_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = (mword_of_int SH_WHITESPACE : mword 64))
      by exact (eq_trans (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate))
                 (upd_eq m1 (Regidx a0_idx) _)).
    assert (Ha1_3 : m3 !!! Regidx a1_idx
                    = (mword_of_int (bv_unsigned bi) : mword 64))
      by exact (eq_trans (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                            ltac:(vm_compute; discriminate))
                 (eq_trans (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
                              ltac:(vm_compute; discriminate))
                    (upd_eq mE (Regidx a1_idx) _))).
    assert (Hra3 : m3 !!! Regidx ra_idx = (mword_of_int (base + 14) : mword 64))
      by exact (upd_eq m2 (Regidx ra_idx) _).
    assert (HfrA : sh_frame_ok hbase hlen
                     (mword_of_int (uint sp0 - 64) : mword 64) 16)
      by (unfold sh_frame_ok; rewrite HuA; lia).
    assert (HaboveA :
              uint (mword_of_int (uint sp0 - 64) : mword 64) <= SH_WHITESPACE \/
              SH_WHITESPACE + Z.of_nat (length sh_ws_bytes) + 1
                <= uint (mword_of_int (uint sp0 - 64) : mword 64) - 16).
    { right. rewrite HuA sh_ws_len. unfold SH_WHITESPACE, SH_DATA_PG. lia. }
    assert (Hret2A : is_aligned_vaddr (Virtaddr (m3 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra3; exact Hal14).
    iApply (wp_sh_strchr C pt gin gbrk hbase hlen Q CID3 M m3
              (mword_of_int (uint sp0 - 64)) SH_WHITESPACE sh_ws_bytes bi
              Hlay Htext Hsp3 HstA Ha0_3 Ha1_3 sh_ws_nz (proj1 Htab)
              (ws_table_rd M Hlay Htab) HaboveA HfrA Hret2A
              with "Hcg Hpc [Hcont]").
    iIntros (CID4 m4 M4) "%Hcs4 %Ha0_4 %Honly4 Hcg Hpc".
    iEval (rewrite Hra3) in "Hpc".
    rewrite HuA in Honly4.
    assert (Honly : uM_only M M4 (uint sp0 - 80) 16).
    { destruct Honly4 as (D & E). split; [ exact D | ].
      intros k Hk. apply E. lia. }
    assert (Hok4 : lex_ok M4 sp0 s0 bs)
      by exact (lex_ok_below M M4 sp0 s0 bs (uint sp0 - 80) 16 Honly
                  ltac:(lia) ltac:(lia) Hok0).
    pose proof Hok4 as Hok4'.
    destruct Hok4' as (Himg4 & Htab4 & Hbuf4 & Hrd4 & Hst4).
    pose proof (sh_img_text M4 Himg4) as Htext4.
    (* the registers strchr promises back *)
    assert (Hs1_4 : m4 !!! Regidx s1_idx
                    = (mword_of_int (s0 + Z.of_nat i) : mword 64)).
    { rewrite (Hcs4 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hpres3 s1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hs1. }
    assert (Hs2_4 : m4 !!! Regidx s2_idx
                    = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (Hcs4 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hpres3 s2_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hs2. }
    assert (Hs3_4 : m4 !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64)).
    { rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hpres3 s3_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hs3. }
    assert (Hsp4 : m4 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (Hcs4 sp_idx ltac:(vm_compute; reflexivity)). exact Hsp3. }
    assert (Hpres4 : forall r : mword 5, ucallee_saved_idx r = true ->
              m4 !!! Regidx r = mE !!! Regidx r).
    { intros r Hr. rewrite (Hcs4 r Hr).
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      exact (Hpres3 r Nra Na0 Na1). }
    (* ---- base+14  c.beqz a0,base+24 ---- *)
    destruct (bool_dec (sh_is_ws bi) true) as [Hws | Hnws].
    - (* WHITESPACE: strchr found it, so the branch falls through ---- *)
      destruct (sh_ws_chr_ws bi Hws) as (kk & Hkk & Hkklt).
      rewrite Hkk in Ha0_4.
      assert (Htk : false = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (moi_eq_zero (SH_WHITESPACE + Z.of_nat kk)
                         ltac:(unfold SH_WHITESPACE, SH_DATA_PG, Z64; lia)).
        symmetry. apply Z.eqb_neq.
        unfold SH_WHITESPACE, SH_DATA_PG. lia. }
      iApply (wp_uv_cbeqz C pt Psh M4 m4 (mword_of_int (base + 14))
                (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int (base + 24))
                (Hu14 M4 Htext4) ltac:(vm_compute; reflexivity) Htk Ebz
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      assert (E14' : (if false then (mword_of_int (base + 24) : mword 64)
                      else add_vec_int (mword_of_int (base + 14) : mword 64) 2)
                     = mword_of_int (base + 16)) by exact E14.
      iEval (rewrite E14') in "Hpc".
      (* ---- base+16  c.addi s1,s1,1 ---- *)
      assert (Hadd : (mword_of_int (s0 + Z.of_nat i + 1) : mword 64)
                     = add_vec (m4 !!! Regidx s1_idx)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 1 : mword 6)))).
      { rewrite Hs1_4.
        assert (Hc1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                       : mword 64) = mword_of_int 1)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc1 moi_add. f_equal; lia. }
      iApply (wp_uv_caddi C pt Psh M4 m4 (mword_of_int (base + 16))
                (mword_of_int 1 : mword 6) s1_idx
                (mword_of_int (s0 + Z.of_nat i + 1))
                (Hu16 M4 Htext4) ltac:(vm_compute; discriminate) Hadd
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      set (m5 := <[Regidx s1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat i + 1) : mword 64)]> m4).
      iEval (rewrite E16) in "Hpc".
      assert (Hs1_5 : m5 !!! Regidx s1_idx
                      = (mword_of_int (s0 + Z.of_nat i + 1) : mword 64))
        by exact (upd_eq m4 (Regidx s1_idx) _).
      assert (Hpres5 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                m5 !!! Regidx r = m4 !!! Regidx r)
        by (intros r Hr; exact (upd_ne m4 (Regidx s1_idx) (Regidx r) _ Hr)).
      assert (Hs2_5 : m5 !!! Regidx s2_idx
                      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
        by (rewrite (Hpres5 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_4).
      assert (Hs3_5 : m5 !!! Regidx s3_idx
                      = (mword_of_int SH_WHITESPACE : mword 64))
        by (rewrite (Hpres5 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_4).
      assert (Hsp5 : m5 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64))
        by (rewrite (Hpres5 sp_idx ltac:(vm_compute; discriminate)); exact Hsp4).
      (* ---- base+18  bne s2,s1,base+4 ---- *)
      destruct (decide (S i = length bs)%nat) as [Hend | Hne].
      + (* the buffer is exhausted: fall through to the [c.mv] ---- *)
        assert (Htk2 : false = uv_btaken BNE (m5 !!! Regidx s2_idx)
                                 (m5 !!! Regidx s1_idx)).
        { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5.
          rewrite (moi_neq_vec (s0 + Z.of_nat (length bs)) (s0 + Z.of_nat i + 1)
                     ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
          symmetry. apply negb_false_iff. apply Z.eqb_eq. lia. }
        iApply (wp_uv_btype C pt Psh M4 m5 (mword_of_int (base + 18))
                  (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE
                  false (mword_of_int (base + 4))
                  (Hu18 M4 Htext4) Htk2 Eback
                  ltac:(intro Hc'; discriminate Hc')
                  with "Hcg Hpc").
        iIntros (CID7) "Hcg Hpc".
        assert (E18' : (if false then (mword_of_int (base + 4) : mword 64)
                        else add_vec_int (mword_of_int (base + 18) : mword 64) 4)
                       = mword_of_int (base + 22)) by exact E18.
        iEval (rewrite E18') in "Hpc".
        (* ---- base+22  c.mv s1,s2 ---- *)
        assert (Hmv : (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                      = add_vec zero_reg (m5 !!! Regidx s2_idx))
          by (rewrite Hs2_5; symmetry; apply moi_add_zero_l).
        iApply (wp_uv_cmv C pt Psh M4 m5 (mword_of_int (base + 22))
                  s1_idx s2_idx (mword_of_int (s0 + Z.of_nat (length bs)))
                  (Hu22 M4 Htext4) ltac:(vm_compute; discriminate) Hmv
                  with "Hcg Hpc").
        iIntros (CID8) "Hcg Hpc".
        set (m6 := <[Regidx s1_idx
                     := regval_into_reg
                          (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)]> m5).
        iEval (rewrite E22) in "Hpc".
        iApply ("Hcont" $! CID8 m6 M4 with "[] [] [] Hcg Hpc").
        * iPureIntro.
          assert (Hsk : sh_skipws (drop i bs) = 1%nat).
          { rewrite Hdrop (sh_skipws_cons_ws bi (drop (S i) bs) Hws).
            assert (Hd : drop (S i) bs = []) by (apply drop_ge; lia).
            rewrite Hd sh_skipws_nil. reflexivity. }
          rewrite Hsk.
          replace (s0 + Z.of_nat (i + 1)) with (s0 + Z.of_nat (length bs)) by lia.
          exact (upd_eq m5 (Regidx s1_idx) _).
        * iPureIntro. intros r Hr Hne1.
          rewrite (upd_ne m5 (Regidx s1_idx) (Regidx r) _ Hne1).
          rewrite (Hpres5 r Hne1). exact (Hpres4 r Hr).
        * iPureIntro. exact Honly.
      + (* another byte: take the back edge with i := S i ---- *)
        assert (Hlt : (S i < length bs)%nat) by lia.
        assert (Htk2 : true = uv_btaken BNE (m5 !!! Regidx s2_idx)
                                (m5 !!! Regidx s1_idx)).
        { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5.
          rewrite (moi_neq_vec (s0 + Z.of_nat (length bs)) (s0 + Z.of_nat i + 1)
                     ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
          symmetry. apply negb_true_iff. apply Z.eqb_neq. lia. }
        iApply (wp_uv_btype C pt Psh M4 m5 (mword_of_int (base + 18))
                  (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE
                  true (mword_of_int (base + 4))
                  (Hu18 M4 Htext4) Htk2 Eback
                  ltac:(intros _; exact Hal4)
                  with "Hcg Hpc").
        iIntros (CID7) "Hcg Hpc".
        destruct (lookup_lt_is_Some_2 bs (S i) Hlt) as (bn & Hbn).
        assert (Hs1_5' : m5 !!! Regidx s1_idx
                         = (mword_of_int (s0 + Z.of_nat (S i)) : mword 64))
          by (rewrite Hs1_5; f_equal; lia).
        iApply (IH CID7 base jimm M4 m5 sp0 s0 bs (S i) bn
                  ltac:(lia) Hlay Hok4 ltac:(unfold sh_frame_ok; lia) Hs0 Hbufhi
                  Hu4 Hu8 Hu10 Hu14 Hu16 Hu18 Hu22
                  E4 E8 Etgt Elink Ebz E14 E16 Eback E18 E22
                  Hal14 Halchr Hal24 Hal4
                  Hlt Hbn Hs1_5' Hs2_5 Hs3_5 Hsp5
                  with "Hcg Hpc").
        iIntros (CID9 m' M') "%Hv' %Hp' %Ho' Hcg Hpc".
        iApply ("Hcont" $! CID9 m' M' with "[] [] [] Hcg Hpc").
        * iPureIntro. rewrite Hv'.
          rewrite Hdrop (sh_skipws_cons_ws bi (drop (S i) bs) Hws).
          f_equal; lia.
        * iPureIntro. intros r Hr Hne1.
          rewrite (Hp' r Hr Hne1). rewrite (Hpres5 r Hne1). exact (Hpres4 r Hr).
        * iPureIntro. exact (uM_only_trans M M4 M' (uint sp0 - 80) 16 Honly Ho').
    - (* NOT WHITESPACE: strchr returned 0, the branch is taken ---- *)
      assert (Hnws' : sh_is_ws bi = false)
        by (destruct (sh_is_ws bi); [ exfalso; exact (Hnws eq_refl) | reflexivity ]).
      rewrite (sh_ws_chr_nws bi Hnws') in Ha0_4.
      assert (Htk : true = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uv_cbeqz C pt Psh M4 m4 (mword_of_int (base + 14))
                (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int (base + 24))
                (Hu14 M4 Htext4) ltac:(vm_compute; reflexivity) Htk Ebz
                ltac:(intros _; exact Hal24)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      iApply ("Hcont" $! CID5 m4 M4 with "[] [] [] Hcg Hpc").
      + iPureIntro. rewrite Hs1_4.
        rewrite Hdrop (sh_skipws_cons_nws bi (drop (S i) bs) Hnws').
        f_equal; lia.
      + iPureIntro. intros r Hr _. exact (Hpres4 r Hr).
      + iPureIntro. exact Honly.
  Qed.

  (* ---- the ENTRY TEST plus the loop: the whole `while (s < es &&        *)
  (*      strchr(whitespace,*s)) s++', at any of its three sites.          *)
  Local Lemma wp_sh_wsskip (CIDp : CpuId) (base : Z) (jimm : mword 21)
      (esr : mword 5) (M : gmap Z (bv 8)) (mE : regfile) (sp0 : mword 64)
      (s0 : Z) (bs : list (bv 8)) (off : nat) :
    sh_layout pt hbase hlen ->
    lex_ok M sp0 s0 bs ->
    sh_frame_ok hbase hlen sp0 80 ->
    0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
    (off <= length bs)%nat ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int base) false
         (BTYPE (mword_of_int 24 : mword 13, Regidx esr, Regidx s1_idx, BGEU))) ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int (base + 4)) false
         (LOAD (mword_of_int 0 : mword 12, Regidx s1_idx, Regidx a1_idx, true, 1))) ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int (base + 8)) true
         (C_MV (Regidx a0_idx, Regidx s3_idx))) ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int (base + 10)) false
         (JAL (jimm, Regidx ra_idx))) ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int (base + 14)) true
         (C_BEQZ (mword_of_int 5 : mword 8, Cregidx (mword_of_int 2)))) ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int (base + 16)) true
         (C_ADDI (mword_of_int 1 : mword 6, Regidx s1_idx))) ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int (base + 18)) false
         (BTYPE (mword_of_int 8178 : mword 13, Regidx s1_idx, Regidx s2_idx, BNE))) ->
    (forall Mx : gmap Z (bv 8), sh_text_sub Mx ->
       uinstr pt Mx (mword_of_int (base + 22)) true
         (C_MV (Regidx s1_idx, Regidx s2_idx))) ->
    (mword_of_int (base + 24) : mword 64)
      = add_vec (mword_of_int base) (sign_extend' 64 (mword_of_int 24 : mword 13)) ->
    add_vec_int (mword_of_int base : mword 64) 4 = mword_of_int (base + 4) ->
    add_vec_int (mword_of_int (base + 4) : mword 64) 4 = mword_of_int (base + 8) ->
    add_vec_int (mword_of_int (base + 8) : mword 64) 2 = mword_of_int (base + 10) ->
    (mword_of_int ShSyms.strchr : mword 64)
      = add_vec (mword_of_int (base + 10)) (sign_extend' 64 jimm) ->
    (mword_of_int (base + 14) : mword 64)
      = add_vec_int (mword_of_int (base + 10) : mword 64) 4 ->
    (mword_of_int (base + 24) : mword 64)
      = add_vec (mword_of_int (base + 14))
          (sign_extend' 64 (sign_extend' 13
             (concat_vec (mword_of_int 5 : mword 8) ('b"0")))) ->
    add_vec_int (mword_of_int (base + 14) : mword 64) 2 = mword_of_int (base + 16) ->
    add_vec_int (mword_of_int (base + 16) : mword 64) 2 = mword_of_int (base + 18) ->
    (mword_of_int (base + 4) : mword 64)
      = add_vec (mword_of_int (base + 18))
          (sign_extend' 64 (mword_of_int 8178 : mword 13)) ->
    add_vec_int (mword_of_int (base + 18) : mword 64) 4 = mword_of_int (base + 22) ->
    add_vec_int (mword_of_int (base + 22) : mword 64) 2 = mword_of_int (base + 24) ->
    is_aligned_vaddr (Virtaddr (mword_of_int (base + 14) : mword 64)) 2 = true ->
    eq_vec (access_vec_dec (mword_of_int ShSyms.strchr : mword 64) 0) ('b"0") = true ->
    eq_vec (access_vec_dec (mword_of_int (base + 24) : mword 64) 0) ('b"0") = true ->
    eq_vec (access_vec_dec (mword_of_int (base + 4) : mword 64) 0) ('b"0") = true ->
    mE !!! Regidx esr = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    mE !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat off) : mword 64) ->
    mE !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    mE !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64) ->
    mE !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mE -∗
    pc_is (CID := CIDp) (mword_of_int base) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜m' !!! Regidx s1_idx
          = (mword_of_int (s0 + Z.of_nat (off + sh_skipws (drop off bs)))
             : mword 64)⌝ -∗
       ⌜forall r : mword 5, ucallee_saved_idx r = true ->
          Regidx r <> Regidx s1_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
       ⌜uM_only M M' (uint sp0 - 80) 16⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (mword_of_int (base + 24)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hok Hfr Hs0 Hbufhi Hoff Hu0 Hu4 Hu8 Hu10 Hu14 Hu16 Hu18 Hu22
           Etest E0 E4 E8 Etgt Elink Ebz E14 E16 Eback E18 E22
           Hal14 Halchr Hal24 Hal4 Hes Hs1 Hs2 Hs3 Hsp.
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    iIntros "Hcg Hpc Hcont".
    destruct (decide (off = length bs)%nat) as [Hend | Hne].
    - (* s == es already: the entry test is taken, nothing runs ---- *)
      assert (Htk : true = uv_btaken BGEU (mE !!! Regidx s1_idx)
                             (mE !!! Regidx esr)).
      { cbn [uv_btaken]. rewrite Hs1 Hes.
        rewrite (moi_ge_u (s0 + Z.of_nat off) (s0 + Z.of_nat (length bs))
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        symmetry. apply Z.geb_le. lia. }
      iApply (wp_uv_btype C pt Psh M mE (mword_of_int base)
                (mword_of_int 24 : mword 13) esr s1_idx BGEU
                true (mword_of_int (base + 24))
                (Hu0 M Htext) Htk Etest ltac:(intros _; exact Hal24)
                with "Hcg Hpc").
      iIntros (CID1) "Hcg Hpc".
      iApply ("Hcont" $! CID1 mE M with "[] [] [] Hcg Hpc").
      + iPureIntro. rewrite Hs1.
        assert (Hd : drop off bs = []) by (apply drop_ge; lia).
        rewrite Hd sh_skipws_nil. f_equal; lia.
      + iPureIntro. intros r _ _. reflexivity.
      + iPureIntro. exact (uM_only_refl M (uint sp0 - 80) 16).
    - (* there IS a byte: fall through into the loop ---- *)
      assert (Hlt : (off < length bs)%nat) by lia.
      assert (Htk : false = uv_btaken BGEU (mE !!! Regidx s1_idx)
                              (mE !!! Regidx esr)).
      { cbn [uv_btaken]. rewrite Hs1 Hes.
        rewrite (moi_ge_u (s0 + Z.of_nat off) (s0 + Z.of_nat (length bs))
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
      iApply (wp_uv_btype C pt Psh M mE (mword_of_int base)
                (mword_of_int 24 : mword 13) esr s1_idx BGEU
                false (mword_of_int (base + 24))
                (Hu0 M Htext) Htk Etest ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID1) "Hcg Hpc".
      assert (E0' : (if false then (mword_of_int (base + 24) : mword 64)
                     else add_vec_int (mword_of_int base : mword 64) 4)
                    = mword_of_int (base + 4)) by exact E0.
      iEval (rewrite E0') in "Hpc".
      destruct (lookup_lt_is_Some_2 bs off Hlt) as (b0 & Hb0).
      iApply (wp_sh_wsloop (S (length bs)) CID1 base jimm M mE sp0 s0 bs off b0
                ltac:(lia) Hlay Hok0 Hfr Hs0 Hbufhi
                Hu4 Hu8 Hu10 Hu14 Hu16 Hu18 Hu22
                E4 E8 Etgt Elink Ebz E14 E16 Eback E18 E22
                Hal14 Halchr Hal24 Hal4 Hlt Hb0 Hs1 Hs2 Hs3 Hsp
                with "Hcg Hpc Hcont").
  Qed.

  (* ---- local image plumbing for the 64-byte frames -------------------- *)

  Local Lemma um_st8_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
    (k < a \/ a + 8 <= k) -> uM_store8 M a v !! k = M !! k.
  Proof. intro H. apply uM_store8_lookup_ne. intros j Hj. lia. Qed.

  Local Lemma img_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
    sh_img_sub M -> 12288 <= a -> sh_img_sub (uM_store8 M a v).
  Proof.
    intros (Ht & Hd) Ha. split.
    - intros k b Hk.
      rewrite (um_st8_ne M a v k
                 ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Ht k b Hk).
    - intros k b Hk.
      rewrite (um_st8_ne M a v k
                 ltac:(pose proof (sh_data_key_lt k b Hk); lia)).
      exact (Hd k b Hk).
  Qed.

  Local Lemma uM_bytes_eq8 (M M' : gmap Z (bv 8)) (a : Z) (v : mword 64) :
    (forall k : Z, a <= k < a + 8 -> M' !! k = M !! k) ->
    uM_bytes M a 8 v -> uM_bytes M' a 8 v.
  Proof.
    intros Heq Hb j Hj. rewrite (Heq (a + Z.of_nat j) ltac:(lia)). exact (Hb j Hj).
  Qed.

  Local Lemma uM_bytes_val (Mx : gmap Z (bv 8)) (a : Z) (w1 w2 : mword 64) :
    w1 = w2 -> uM_bytes Mx a 8 w1 -> uM_bytes Mx a 8 w2.
  Proof. intros He H. rewrite <- He. exact H. Qed.

  Local Lemma uM_word_of_bytes (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
    uM_bytes M a 8 v -> uM_word M a 8 = v.
  Proof.
    intro Hb. apply (uM_bytes_inj M a); [ | exact Hb ].
    exact (uM_word_bytes M a 8 ltac:(lia) (uM_bytes_exists M a 8 v Hb)).
  Qed.

  (* ---- THE SEVEN-SLOT RELOAD, shared by peek's and gettoken's           *)
  (*      epilogues (gettoken's eighth slot and both [c.addi16sp]/[c.jr]    *)
  (*      tails are one step each at the call site).                       *)
  Local Lemma wp_sh_epi7 (CIDp : CpuId) (epi : Z)
      (M : gmap Z (bv 8)) (mF : regfile) (sp0 : mword 64)
      (ra0 s00 s10 s20 s30 s40 s50 : mword 64) :
    uv_stack pt M sp0 64 ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    uM_bytes M (uint sp0 - 8) 8 ra0 ->
    uM_bytes M (uint sp0 - 16) 8 s00 ->
    uM_bytes M (uint sp0 - 24) 8 s10 ->
    uM_bytes M (uint sp0 - 32) 8 s20 ->
    uM_bytes M (uint sp0 - 40) 8 s30 ->
    uM_bytes M (uint sp0 - 48) 8 s40 ->
    uM_bytes M (uint sp0 - 56) 8 s50 ->
    uinstr pt M (mword_of_int epi) true
      (C_LDSP (mword_of_int 7 : mword 6, Regidx ra_idx)) ->
    uinstr pt M (mword_of_int (epi + 2)) true
      (C_LDSP (mword_of_int 6 : mword 6, Regidx s0_idx)) ->
    uinstr pt M (mword_of_int (epi + 4)) true
      (C_LDSP (mword_of_int 5 : mword 6, Regidx s1_idx)) ->
    uinstr pt M (mword_of_int (epi + 6)) true
      (C_LDSP (mword_of_int 4 : mword 6, Regidx s2_idx)) ->
    uinstr pt M (mword_of_int (epi + 8)) true
      (C_LDSP (mword_of_int 3 : mword 6, Regidx s3_idx)) ->
    uinstr pt M (mword_of_int (epi + 10)) true
      (C_LDSP (mword_of_int 2 : mword 6, Regidx s4_idx)) ->
    uinstr pt M (mword_of_int (epi + 12)) true
      (C_LDSP (mword_of_int 1 : mword 6, Regidx s5_idx)) ->
    add_vec_int (mword_of_int epi : mword 64) 2 = mword_of_int (epi + 2) ->
    add_vec_int (mword_of_int (epi + 2) : mword 64) 2 = mword_of_int (epi + 4) ->
    add_vec_int (mword_of_int (epi + 4) : mword 64) 2 = mword_of_int (epi + 6) ->
    add_vec_int (mword_of_int (epi + 6) : mword 64) 2 = mword_of_int (epi + 8) ->
    add_vec_int (mword_of_int (epi + 8) : mword 64) 2 = mword_of_int (epi + 10) ->
    add_vec_int (mword_of_int (epi + 10) : mword 64) 2 = mword_of_int (epi + 12) ->
    add_vec_int (mword_of_int (epi + 12) : mword 64) 2 = mword_of_int (epi + 14) ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int epi) -∗
    (∀ (CID : CpuId) (m' : regfile),
       ⌜m' !!! Regidx ra_idx = ra0⌝ -∗
       ⌜m' !!! Regidx s0_idx = s00⌝ -∗
       ⌜m' !!! Regidx s1_idx = s10⌝ -∗
       ⌜m' !!! Regidx s2_idx = s20⌝ -∗
       ⌜m' !!! Regidx s3_idx = s30⌝ -∗
       ⌜m' !!! Regidx s4_idx = s40⌝ -∗
       ⌜m' !!! Regidx s5_idx = s50⌝ -∗
       ⌜forall r : mword 5,
          Regidx r <> Regidx ra_idx -> Regidx r <> Regidx s0_idx ->
          Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
          Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
          Regidx r <> Regidx s5_idx -> m' !!! Regidx r = mF !!! Regidx r⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M m' -∗
       pc_is (CID := CID) (mword_of_int (epi + 14)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hst Hsp Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
           Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 E0 E2 E4 E6 E8 E10 E12.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    iIntros "Hcg Hpc Hcont".
    (* ---- epi+0  c.ldsp ra_idx ---- *)
    assert (Hw1 : uM_word M (uint sp0 - 64 + 56) 8 = ra0).
    { replace (uint sp0 - 64 + 56) with (uint sp0 - 8) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 8) ra0 Hb1). }
    iApply (wp_uv_frame_load C pt CIDp Psh M mF sp0 (mword_of_int epi)
              (mword_of_int 7 : mword 6) ra_idx 64 56 ra0
              Hi0 ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw1)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    iEval (rewrite E0) in "Hpc".
    set (mR1 := <[Regidx ra_idx := regval_into_reg ra0]> mF).
    assert (Hsp1 : mR1 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (eq_trans (upd_ne mF (Regidx ra_idx) (Regidx sp_idx) _
                            ltac:(vm_compute; discriminate)) Hsp).
    (* ---- epi+2  c.ldsp s0_idx ---- *)
    assert (Hw2 : uM_word M (uint sp0 - 64 + 48) 8 = s00).
    { replace (uint sp0 - 64 + 48) with (uint sp0 - 16) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 16) s00 Hb2). }
    iApply (wp_uv_frame_load C pt CID1 Psh M mR1 sp0 (mword_of_int (epi + 2))
              (mword_of_int 6 : mword 6) s0_idx 64 48 s00
              Hi2 ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw2)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite E2) in "Hpc".
    set (mR2 := <[Regidx s0_idx := regval_into_reg s00]> mR1).
    assert (Hsp2 : mR2 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (eq_trans (upd_ne mR1 (Regidx s0_idx) (Regidx sp_idx) _
                            ltac:(vm_compute; discriminate)) Hsp1).
    (* ---- epi+4  c.ldsp s1_idx ---- *)
    assert (Hw3 : uM_word M (uint sp0 - 64 + 40) 8 = s10).
    { replace (uint sp0 - 64 + 40) with (uint sp0 - 24) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 24) s10 Hb3). }
    iApply (wp_uv_frame_load C pt CID2 Psh M mR2 sp0 (mword_of_int (epi + 4))
              (mword_of_int 5 : mword 6) s1_idx 64 40 s10
              Hi4 ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp2
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw3)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite E4) in "Hpc".
    set (mR3 := <[Regidx s1_idx := regval_into_reg s10]> mR2).
    assert (Hsp3 : mR3 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (eq_trans (upd_ne mR2 (Regidx s1_idx) (Regidx sp_idx) _
                            ltac:(vm_compute; discriminate)) Hsp2).
    (* ---- epi+6  c.ldsp s2_idx ---- *)
    assert (Hw4 : uM_word M (uint sp0 - 64 + 32) 8 = s20).
    { replace (uint sp0 - 64 + 32) with (uint sp0 - 32) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 32) s20 Hb4). }
    iApply (wp_uv_frame_load C pt CID3 Psh M mR3 sp0 (mword_of_int (epi + 6))
              (mword_of_int 4 : mword 6) s2_idx 64 32 s20
              Hi6 ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw4)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iEval (rewrite E6) in "Hpc".
    set (mR4 := <[Regidx s2_idx := regval_into_reg s20]> mR3).
    assert (Hsp4 : mR4 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx sp_idx) _
                            ltac:(vm_compute; discriminate)) Hsp3).
    (* ---- epi+8  c.ldsp s3_idx ---- *)
    assert (Hw5 : uM_word M (uint sp0 - 64 + 24) 8 = s30).
    { replace (uint sp0 - 64 + 24) with (uint sp0 - 40) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 40) s30 Hb5). }
    iApply (wp_uv_frame_load C pt CID4 Psh M mR4 sp0 (mword_of_int (epi + 8))
              (mword_of_int 3 : mword 6) s3_idx 64 24 s30
              Hi8 ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp4
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw5)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    iEval (rewrite E8) in "Hpc".
    set (mR5 := <[Regidx s3_idx := regval_into_reg s30]> mR4).
    assert (Hsp5 : mR5 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx sp_idx) _
                            ltac:(vm_compute; discriminate)) Hsp4).
    (* ---- epi+10  c.ldsp s4_idx ---- *)
    assert (Hw6 : uM_word M (uint sp0 - 64 + 16) 8 = s40).
    { replace (uint sp0 - 64 + 16) with (uint sp0 - 48) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 48) s40 Hb6). }
    iApply (wp_uv_frame_load C pt CID5 Psh M mR5 sp0 (mword_of_int (epi + 10))
              (mword_of_int 2 : mword 6) s4_idx 64 16 s40
              Hi10 ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp5
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw6)
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    iEval (rewrite E10) in "Hpc".
    set (mR6 := <[Regidx s4_idx := regval_into_reg s40]> mR5).
    assert (Hsp6 : mR6 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx sp_idx) _
                            ltac:(vm_compute; discriminate)) Hsp5).
    (* ---- epi+12  c.ldsp s5_idx ---- *)
    assert (Hw7 : uM_word M (uint sp0 - 64 + 8) 8 = s50).
    { replace (uint sp0 - 64 + 8) with (uint sp0 - 56) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 56) s50 Hb7). }
    iApply (wp_uv_frame_load C pt CID6 Psh M mR6 sp0 (mword_of_int (epi + 12))
              (mword_of_int 1 : mword 6) s5_idx 64 8 s50
              Hi12 ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp6
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw7)
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    iEval (rewrite E12) in "Hpc".
    set (mR7 := <[Regidx s5_idx := regval_into_reg s50]> mR6).
    iApply ("Hcont" $! CID7 mR7 with "[] [] [] [] [] [] [] [] Hcg Hpc").
    - iPureIntro. exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR2 (Regidx s1_idx) (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR1 (Regidx s0_idx) (Regidx ra_idx) _ ltac:(vm_compute; discriminate)) (upd_eq mF (Regidx ra_idx) _))))))).
    - iPureIntro. exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s0_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s0_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx s0_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx s0_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR2 (Regidx s1_idx) (Regidx s0_idx) _ ltac:(vm_compute; discriminate)) (upd_eq mR1 (Regidx s0_idx) _)))))).
    - iPureIntro. exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s1_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s1_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx s1_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx s1_idx) _ ltac:(vm_compute; discriminate)) (upd_eq mR2 (Regidx s1_idx) _))))).
    - iPureIntro. exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s2_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s2_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx s2_idx) _ ltac:(vm_compute; discriminate)) (upd_eq mR3 (Regidx s2_idx) _)))).
    - iPureIntro. exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s3_idx) _ ltac:(vm_compute; discriminate)) (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s3_idx) _ ltac:(vm_compute; discriminate)) (upd_eq mR4 (Regidx s3_idx) _))).
    - iPureIntro. exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s4_idx) _ ltac:(vm_compute; discriminate)) (upd_eq mR5 (Regidx s4_idx) _)).
    - iPureIntro. exact (upd_eq mR6 (Regidx s5_idx) _).
    - iPureIntro. intros r N1 N2 N3 N4 N5 N6 N7.
      exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx r) _ N7)
               (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx r) _ N6)
                  (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx r) _ N5)
                     (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx r) _ N4)
                        (eq_trans (upd_ne mR2 (Regidx s1_idx) (Regidx r) _ N3)
                           (eq_trans (upd_ne mR1 (Regidx s0_idx) (Regidx r) _ N2)
                              (upd_ne mF (Regidx ra_idx) (Regidx r) _ N1))))))).
  Qed.

  Local Lemma stack_store8 (M : gmap Z (bv 8)) (sp0 : mword 64) (n a : Z)
      (v : mword 64) :
    uv_stack pt M sp0 n -> uv_stack pt (uM_store8 M a v) sp0 n.
  Proof.
    intro H. apply (uv_stack_dom pt M _ sp0 n); [ | exact H ].
    intros k Hk. exact (uM_store8_is_Some M a v k Hk).
  Qed.

  (* ---- THE SEVEN-SLOT SPILL, read back.  One lemma covers the whole      *)
  (*      tower: each slot's value, the untouched complement, and the       *)
  (*      key-preservation the image predicates transport across.          *)
  Local Lemma spill7_facts (M M7 : gmap Z (bv 8)) (bot : Z)
      (v0 v1 v2 v3 v4 v5 v6 : mword 64) :
    M7 = uM_store8 (uM_store8 (uM_store8 (uM_store8 (uM_store8
                (uM_store8 (uM_store8 M (bot + 56) v0)
                   (bot + 48) v1) (bot + 40) v2) (bot + 32) v3)
                   (bot + 24) v4) (bot + 16) v5) (bot + 8) v6 ->
    uM_bytes M7 (bot + 56) 8 v0 /\ uM_bytes M7 (bot + 48) 8 v1 /\
    uM_bytes M7 (bot + 40) 8 v2 /\ uM_bytes M7 (bot + 32) 8 v3 /\
    uM_bytes M7 (bot + 24) 8 v4 /\ uM_bytes M7 (bot + 16) 8 v5 /\
    uM_bytes M7 (bot + 8) 8 v6 /\
    (forall k : Z, k < bot + 8 \/ bot + 64 <= k -> M7 !! k = M !! k) /\
    (forall k : Z, is_Some (M !! k) -> is_Some (M7 !! k)).
  Proof.
    intro HM7. subst M7. split_and!.
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 8) v6 (bot + 56 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 16) v5 (bot + 56 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 24) v4 (bot + 56 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 32) v3 (bot + 56 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 40) v2 (bot + 56 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 48) v1 (bot + 56 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M (bot + 56) v0 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 8) v6 (bot + 48 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 16) v5 (bot + 48 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 24) v4 (bot + 48 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 32) v3 (bot + 48 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 40) v2 (bot + 48 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes _ (bot + 48) v1 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 8) v6 (bot + 40 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 16) v5 (bot + 40 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 24) v4 (bot + 40 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 32) v3 (bot + 40 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes _ (bot + 40) v2 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 8) v6 (bot + 32 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 16) v5 (bot + 32 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 24) v4 (bot + 32 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes _ (bot + 32) v3 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 8) v6 (bot + 24 + Z.of_nat j) ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 16) v5 (bot + 24 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes _ (bot + 24) v4 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 8) v6 (bot + 16 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes _ (bot + 16) v5 j Hj).
    - intros j Hj.
      exact (uM_store8_bytes _ (bot + 8) v6 j Hj).
    - intros k Hk.
      rewrite (um_st8_ne _ (bot + 8) v6 k ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 16) v5 k ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 24) v4 k ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 32) v3 k ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 40) v2 k ltac:(lia)).
      rewrite (um_st8_ne _ (bot + 48) v1 k ltac:(lia)).
      exact (um_st8_ne M (bot + 56) v0 k ltac:(lia)).
    - intros k Hk.
      repeat apply uM_store8_is_Some. exact Hk.
  Qed.

  (* ---- peek's EXIT: the seven reloads, [c.addi16sp sp,+64], [c.jr ra]. *)
  Local Lemma wp_sh_peek_exit (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64) (ret : Z) :
    sh_text_layout pt -> sh_text_sub M ->
    uv_stack pt M sp0 64 ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx a0_idx = (mword_of_int ret : mword 64) ->
    uM_bytes M (uint sp0 - 8) 8 (m !!! Regidx ra_idx) ->
    uM_bytes M (uint sp0 - 16) 8 (m !!! Regidx s0_idx) ->
    uM_bytes M (uint sp0 - 24) 8 (m !!! Regidx s1_idx) ->
    uM_bytes M (uint sp0 - 32) 8 (m !!! Regidx s2_idx) ->
    uM_bytes M (uint sp0 - 40) 8 (m !!! Regidx s3_idx) ->
    uM_bytes M (uint sp0 - 48) 8 (m !!! Regidx s4_idx) ->
    uM_bytes M (uint sp0 - 56) 8 (m !!! Regidx s5_idx) ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
       Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
       Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
       Regidx r <> Regidx s5_idx -> mF !!! Regidx r = m !!! Regidx r) ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x48e) -∗
    (∀ (CID : CpuId) (m' : regfile),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int ret : mword 64)⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hltext Htext Hst Hret2 Hspm HspF Ha0F Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hpres.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_sh_epi7 CIDp 0x48e M mF sp0
              (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s1_idx)
              (m !!! Regidx s2_idx) (m !!! Regidx s3_idx) (m !!! Regidx s4_idx)
              (m !!! Regidx s5_idx)
              Hst HspF Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
              (ui_sh_48e pt M Hltext Htext) (ui_sh_490 pt M Hltext Htext)
              (ui_sh_492 pt M Hltext Htext) (ui_sh_494 pt M Hltext Htext)
              (ui_sh_496 pt M Hltext Htext) (ui_sh_498 pt M Hltext Htext)
              (ui_sh_49a pt M Hltext Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros (CID1 mR) "%Hra %Hs0 %Hs1 %Hs2 %Hs3 %Hs4 %Hs5 %HpR Hcg Hpc".
    (* ---- 0x49c  c.addi16sp sp,sp,64 ---- *)
    assert (HspR : mR !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { assert (Hx : mR !!! Regidx sp_idx = mF !!! Regidx sp_idx)
        by (apply HpR; vm_compute; discriminate).
      rewrite Hx. exact HspF. }
    assert (Hwsp : sp0 = add_vec (mR !!! Regidx csp_rs1)
                          (sign_extend' 64
                             (caddi16sp_imm (mword_of_int 4 : mword 6)))).
    { rewrite HspR.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 64 + 64) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh M mR (mword_of_int 0x49c)
              (mword_of_int 4 : mword 6) sp0
              (ui_sh_49c pt M Hltext Htext) Hwsp with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mS := <[Regidx csp_rs1 := regval_into_reg sp0]> mR).
    assert (E49c : add_vec_int (mword_of_int 0x49c : mword 64) 2
                   = mword_of_int 0x49e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E49c) in "Hpc".
    (* ---- 0x49e  c.jr ra ---- *)
    assert (HraS : mS !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne mR (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)). exact Hra. }
    assert (Htgt : (m !!! Regidx ra_idx) = ret_pc (mS !!! Regidx ra_idx)).
    { rewrite HraS. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh M mS (mword_of_int 0x49e)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_49e pt M Hltext Htext)
              ltac:(vm_compute; discriminate) Htgt with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 mS with "[] [] Hcg Hpc").
    - iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
      { rewrite Esp. rewrite (upd_eq mR (Regidx csp_rs1) _). symmetry. exact Hspm. }
      rewrite (upd_ne mR (Regidx csp_rs1) (Regidx r) _ Nsp).
      destruct (decide (Regidx r = Regidx s0_idx)) as [E0 | N0].
      { rewrite E0. exact Hs0. }
      destruct (decide (Regidx r = Regidx s1_idx)) as [E1 | N1].
      { rewrite E1. exact Hs1. }
      destruct (decide (Regidx r = Regidx s2_idx)) as [E2 | N2].
      { rewrite E2. exact Hs2. }
      destruct (decide (Regidx r = Regidx s3_idx)) as [E3 | N3].
      { rewrite E3. exact Hs3. }
      destruct (decide (Regidx r = Regidx s4_idx)) as [E4 | N4].
      { rewrite E4. exact Hs4. }
      destruct (decide (Regidx r = Regidx s5_idx)) as [E5 | N5].
      { rewrite E5. exact Hs5. }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HpR r Nra N0 N1 N2 N3 N4 N5).
      exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5).
    - iPureIntro.
      rewrite (upd_ne mR (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpR a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact Ha0F.
  Qed.

  (* ===================================================================== *)
  (* §4 peek @0x448.                                                        *)
  (*                                                                        *)
  (*   int peek(char **ps, char *es, char *toks) {                          *)
  (*     char *s = *ps;                                                     *)
  (*     while (s < es && strchr(whitespace, *s)) s++;                      *)
  (*     *ps = s;                                                           *)
  (*     return *s && strchr(toks, *s);                                     *)
  (*   }                                                                    *)
  (*                                                                        *)
  (*   448..458  the 64-byte prologue (ra, s0..s5 spilled)                  *)
  (*   45a..466  s4 := ps, s2 := es, s5 := toks, s1 := *ps, s3 := whitespace *)
  (*   46a..480  the whitespace scan ([wp_sh_wsskip])                       *)
  (*   482       *ps = s                                                    *)
  (*   486..48c  ret := 0; branch to 4a0 when *s is not NUL               *)
  (*   48e..49e  the epilogue                                               *)
  (*   4a0..4aa  ret := (strchr(toks, *s) != 0), then back to the epilogue  *)
  (* ===================================================================== *)

  Lemma wp_sh_peek (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr s0 : Z) (bs : list (bv 8)) (off : nat)
      (toks : Z) (tbs : list (bv 8)) :
    wp_sh_peek_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 psaddr s0 bs off toks tbs.
  Proof.
    intros Hpre Hsp Hst Hps Hes Htoks Hcellp Hoff Htnn Htbs Htnz Htrd Htbelow
           Hret2.
    destruct Hpre as (Hlay & Himg & Htab & Hbuf & Hnosym & Hrd & Hwr & Hs0lo &
                      Hs0hi & Hfr & Hbufhi).
    (* [sh_parse_pre]'s 8th conjunct is now [8208 <= s0] (the buffer is above
       the loaded image); the block lemmas below only need it positive. *)
    assert (Hs0p : 0 < s0) by lia.
    destruct Hcellp as (Hcell & Hpsrd & Hcellw & Hpsal & Hpshi & Hpshi2).
    unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & Hspeek & _ & _ & _ & _ & Hsstrchr & _).
    assert (Hst80 : uv_stack pt M sp0 80) by exact Hst.
    pose proof (us_lo _ _ _ _ Hst80) as Hlo.
    pose proof (us_canon _ _ _ _ Hst80) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi.
    change (2 ^ 38) with 274877906944 in Hpshi2.
    destruct (uv_stack_split pt M sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst80) as (Hst64 & _).
    assert (Hokm : lex_ok M sp0 s0 bs)
      by (split_and!; assumption).
    (* the scan's stopping index *)
    set (kk := sh_skipws (drop off bs)).
    assert (Hkk : (off + kk <= length bs)%nat).
    { unfold kk. pose proof (sh_skipws_le (drop off bs)) as H.
      rewrite length_drop in H. lia. }
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hspeek) in "Hpc".
    (* ---- 0x448  c.addi16sp sp,sp,-64 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 64) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))
                    : mword 64) = mword_of_int (-64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x448)
              (mword_of_int 60 : mword 6) (mword_of_int (uint sp0 - 64))
              (ui_sh_448 pt M Hltext (sh_img_text M Himg)) Hwsp with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mA := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64)]> m).
    assert (E448 : add_vec_int (mword_of_int 0x448 : mword 64) 2
                   = mword_of_int 0x44a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E448) in "Hpc".
    assert (HspA : mA !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (HpresA : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              mA !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0x44a  c.sdsp ra_idx ---- *)
    iApply (wp_uv_frame_store C pt CID1 Psh M mA sp0 (mword_of_int 0x44a)
              (mword_of_int 7 : mword 6) ra_idx 64 56
              (ui_sh_44a pt M Hltext (sh_img_text M Himg))
              Hst64 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x44a : mword 64) 2
                      = mword_of_int 0x44c)) in "Hpc".
    set (P1 := uM_store8 M (uint sp0 - 64 + 56) (mA !!! Regidx ra_idx)).
    assert (Himg1 : sh_img_sub P1)
      by (unfold P1; apply img_store8; [ exact Himg | lia ]).
    assert (Hstk1 : uv_stack pt P1 sp0 64)
      by (unfold P1; apply stack_store8; exact Hst64).
    (* ---- 0x44c  c.sdsp s0_idx ---- *)
    iApply (wp_uv_frame_store C pt CID2 Psh P1 mA sp0 (mword_of_int 0x44c)
              (mword_of_int 6 : mword 6) s0_idx 64 48
              (ui_sh_44c pt P1 Hltext (sh_img_text P1 Himg1))
              Hstk1 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x44c : mword 64) 2
                      = mword_of_int 0x44e)) in "Hpc".
    set (P2 := uM_store8 P1 (uint sp0 - 64 + 48) (mA !!! Regidx s0_idx)).
    assert (Himg2 : sh_img_sub P2)
      by (unfold P2; apply img_store8; [ exact Himg1 | lia ]).
    assert (Hstk2 : uv_stack pt P2 sp0 64)
      by (unfold P2; apply stack_store8; exact Hstk1).
    (* ---- 0x44e  c.sdsp s1_idx ---- *)
    iApply (wp_uv_frame_store C pt CID3 Psh P2 mA sp0 (mword_of_int 0x44e)
              (mword_of_int 5 : mword 6) s1_idx 64 40
              (ui_sh_44e pt P2 Hltext (sh_img_text P2 Himg2))
              Hstk2 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x44e : mword 64) 2
                      = mword_of_int 0x450)) in "Hpc".
    set (P3 := uM_store8 P2 (uint sp0 - 64 + 40) (mA !!! Regidx s1_idx)).
    assert (Himg3 : sh_img_sub P3)
      by (unfold P3; apply img_store8; [ exact Himg2 | lia ]).
    assert (Hstk3 : uv_stack pt P3 sp0 64)
      by (unfold P3; apply stack_store8; exact Hstk2).
    (* ---- 0x450  c.sdsp s2_idx ---- *)
    iApply (wp_uv_frame_store C pt CID4 Psh P3 mA sp0 (mword_of_int 0x450)
              (mword_of_int 4 : mword 6) s2_idx 64 32
              (ui_sh_450 pt P3 Hltext (sh_img_text P3 Himg3))
              Hstk3 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x450 : mword 64) 2
                      = mword_of_int 0x452)) in "Hpc".
    set (P4 := uM_store8 P3 (uint sp0 - 64 + 32) (mA !!! Regidx s2_idx)).
    assert (Himg4 : sh_img_sub P4)
      by (unfold P4; apply img_store8; [ exact Himg3 | lia ]).
    assert (Hstk4 : uv_stack pt P4 sp0 64)
      by (unfold P4; apply stack_store8; exact Hstk3).
    (* ---- 0x452  c.sdsp s3_idx ---- *)
    iApply (wp_uv_frame_store C pt CID5 Psh P4 mA sp0 (mword_of_int 0x452)
              (mword_of_int 3 : mword 6) s3_idx 64 24
              (ui_sh_452 pt P4 Hltext (sh_img_text P4 Himg4))
              Hstk4 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x452 : mword 64) 2
                      = mword_of_int 0x454)) in "Hpc".
    set (P5 := uM_store8 P4 (uint sp0 - 64 + 24) (mA !!! Regidx s3_idx)).
    assert (Himg5 : sh_img_sub P5)
      by (unfold P5; apply img_store8; [ exact Himg4 | lia ]).
    assert (Hstk5 : uv_stack pt P5 sp0 64)
      by (unfold P5; apply stack_store8; exact Hstk4).
    (* ---- 0x454  c.sdsp s4_idx ---- *)
    iApply (wp_uv_frame_store C pt CID6 Psh P5 mA sp0 (mword_of_int 0x454)
              (mword_of_int 2 : mword 6) s4_idx 64 16
              (ui_sh_454 pt P5 Hltext (sh_img_text P5 Himg5))
              Hstk5 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x454 : mword 64) 2
                      = mword_of_int 0x456)) in "Hpc".
    set (P6 := uM_store8 P5 (uint sp0 - 64 + 16) (mA !!! Regidx s4_idx)).
    assert (Himg6 : sh_img_sub P6)
      by (unfold P6; apply img_store8; [ exact Himg5 | lia ]).
    assert (Hstk6 : uv_stack pt P6 sp0 64)
      by (unfold P6; apply stack_store8; exact Hstk5).
    (* ---- 0x456  c.sdsp s5_idx ---- *)
    iApply (wp_uv_frame_store C pt CID7 Psh P6 mA sp0 (mword_of_int 0x456)
              (mword_of_int 1 : mword 6) s5_idx 64 8
              (ui_sh_456 pt P6 Hltext (sh_img_text P6 Himg6))
              Hstk6 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x456 : mword 64) 2
                      = mword_of_int 0x458)) in "Hpc".
    set (P7 := uM_store8 P6 (uint sp0 - 64 + 8) (mA !!! Regidx s5_idx)).
    assert (Himg7 : sh_img_sub P7)
      by (unfold P7; apply img_store8; [ exact Himg6 | lia ]).
    assert (Hstk7 : uv_stack pt P7 sp0 64)
      by (unfold P7; apply stack_store8; exact Hstk6).
    (* ---- the frame, read back ---- *)
    destruct (spill7_facts M P7 (uint sp0 - 64)
                (mA !!! Regidx ra_idx) (mA !!! Regidx s0_idx)
                (mA !!! Regidx s1_idx) (mA !!! Regidx s2_idx)
                (mA !!! Regidx s3_idx) (mA !!! Regidx s4_idx)
                (mA !!! Regidx s5_idx) eq_refl)
      as (Hf0 & Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hfout & Hfdom).
    assert (Hg0 : uM_bytes P7 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { apply (uM_bytes_val P7 (uint sp0 - 8) (mA !!! Regidx ra_idx));
        [ exact (HpresA ra_idx ltac:(vm_compute; discriminate)) | ].
      intros j Hj.
      replace (uint sp0 - 8 + Z.of_nat j)
        with (uint sp0 - 64 + 56 + Z.of_nat j) by lia.
      exact (Hf0 j Hj). }
    assert (Hg1 : uM_bytes P7 (uint sp0 - 16) 8 (m !!! Regidx s0_idx)).
    { apply (uM_bytes_val P7 (uint sp0 - 16) (mA !!! Regidx s0_idx));
        [ exact (HpresA s0_idx ltac:(vm_compute; discriminate)) | ].
      intros j Hj.
      replace (uint sp0 - 16 + Z.of_nat j)
        with (uint sp0 - 64 + 48 + Z.of_nat j) by lia.
      exact (Hf1 j Hj). }
    assert (Hg2 : uM_bytes P7 (uint sp0 - 24) 8 (m !!! Regidx s1_idx)).
    { apply (uM_bytes_val P7 (uint sp0 - 24) (mA !!! Regidx s1_idx));
        [ exact (HpresA s1_idx ltac:(vm_compute; discriminate)) | ].
      intros j Hj.
      replace (uint sp0 - 24 + Z.of_nat j)
        with (uint sp0 - 64 + 40 + Z.of_nat j) by lia.
      exact (Hf2 j Hj). }
    assert (Hg3 : uM_bytes P7 (uint sp0 - 32) 8 (m !!! Regidx s2_idx)).
    { apply (uM_bytes_val P7 (uint sp0 - 32) (mA !!! Regidx s2_idx));
        [ exact (HpresA s2_idx ltac:(vm_compute; discriminate)) | ].
      intros j Hj.
      replace (uint sp0 - 32 + Z.of_nat j)
        with (uint sp0 - 64 + 32 + Z.of_nat j) by lia.
      exact (Hf3 j Hj). }
    assert (Hg4 : uM_bytes P7 (uint sp0 - 40) 8 (m !!! Regidx s3_idx)).
    { apply (uM_bytes_val P7 (uint sp0 - 40) (mA !!! Regidx s3_idx));
        [ exact (HpresA s3_idx ltac:(vm_compute; discriminate)) | ].
      intros j Hj.
      replace (uint sp0 - 40 + Z.of_nat j)
        with (uint sp0 - 64 + 24 + Z.of_nat j) by lia.
      exact (Hf4 j Hj). }
    assert (Hg5 : uM_bytes P7 (uint sp0 - 48) 8 (m !!! Regidx s4_idx)).
    { apply (uM_bytes_val P7 (uint sp0 - 48) (mA !!! Regidx s4_idx));
        [ exact (HpresA s4_idx ltac:(vm_compute; discriminate)) | ].
      intros j Hj.
      replace (uint sp0 - 48 + Z.of_nat j)
        with (uint sp0 - 64 + 16 + Z.of_nat j) by lia.
      exact (Hf5 j Hj). }
    assert (Hg6 : uM_bytes P7 (uint sp0 - 56) 8 (m !!! Regidx s5_idx)).
    { apply (uM_bytes_val P7 (uint sp0 - 56) (mA !!! Regidx s5_idx));
        [ exact (HpresA s5_idx ltac:(vm_compute; discriminate)) | ].
      intros j Hj.
      replace (uint sp0 - 56 + Z.of_nat j)
        with (uint sp0 - 64 + 8 + Z.of_nat j) by lia.
      exact (Hf6 j Hj). }
    assert (Honly7 : uM_only M P7 (uint sp0 - 56) 56).
    { split; [ exact Hfdom | ]. intros k Hk. apply Hfout. lia. }
    assert (Hok7 : lex_ok P7 sp0 s0 bs)
      by exact (lex_ok_below M P7 sp0 s0 bs (uint sp0 - 56) 56 Honly7
                  ltac:(lia) ltac:(lia) Hokm).
    (* ---- 0x458  c.addi4spn s0,sp,64 ---- *)
    assert (Hw64 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (mA !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8)))).
    { assert (Hs : mA !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64)) by exact HspA.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh P7 mA (mword_of_int 0x458)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_458 pt P7 Hltext (sh_img_text P7 Himg7))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw64
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    set (mB := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> mA).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x458 : mword 64) 2
                      = mword_of_int 0x45a)) in "Hpc".
    (* ---- 0x45a  c.mv s4,a0 ---- *)
    assert (Ha0B : mB !!! Regidx a0_idx = (mword_of_int psaddr : mword 64)).
    { rewrite (upd_ne mA (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresA a0_idx ltac:(vm_compute; discriminate)). exact Hps. }
    assert (Hws4 : (mword_of_int psaddr : mword 64)
                   = add_vec zero_reg (mB !!! Regidx a0_idx))
      by (rewrite Ha0B; symmetry; apply moi_add_zero_l).
    iApply (wp_uv_cmv C pt Psh P7 mB (mword_of_int 0x45a)
              s4_idx a0_idx (mword_of_int psaddr)
              (ui_sh_45a pt P7 Hltext (sh_img_text P7 Himg7))
              ltac:(vm_compute; discriminate) Hws4 with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    set (mC := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int psaddr : mword 64)]> mB).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x45a : mword 64) 2
                      = mword_of_int 0x45c)) in "Hpc".
    (* ---- 0x45c  c.mv s2,a1 ---- *)
    assert (Ha1C : mC !!! Regidx a1_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne mB (Regidx s4_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresA a1_idx ltac:(vm_compute; discriminate)). exact Hes. }
    assert (Hws2 : (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                   = add_vec zero_reg (mC !!! Regidx a1_idx))
      by (rewrite Ha1C; symmetry; apply moi_add_zero_l).
    iApply (wp_uv_cmv C pt Psh P7 mC (mword_of_int 0x45c)
              s2_idx a1_idx (mword_of_int (s0 + Z.of_nat (length bs)))
              (ui_sh_45c pt P7 Hltext (sh_img_text P7 Himg7))
              ltac:(vm_compute; discriminate) Hws2 with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    set (mD := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)]> mC).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x45c : mword 64) 2
                      = mword_of_int 0x45e)) in "Hpc".
    (* ---- 0x45e  c.mv s5,a2 ---- *)
    assert (Ha2D : mD !!! Regidx a2_idx = (mword_of_int toks : mword 64)).
    { rewrite (upd_ne mC (Regidx s2_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresA a2_idx ltac:(vm_compute; discriminate)). exact Htoks. }
    assert (Hws5 : (mword_of_int toks : mword 64)
                   = add_vec zero_reg (mD !!! Regidx a2_idx))
      by (rewrite Ha2D; symmetry; apply moi_add_zero_l).
    iApply (wp_uv_cmv C pt Psh P7 mD (mword_of_int 0x45e)
              s5_idx a2_idx (mword_of_int toks)
              (ui_sh_45e pt P7 Hltext (sh_img_text P7 Himg7))
              ltac:(vm_compute; discriminate) Hws5 with "Hcg Hpc").
    iIntros (CID12) "Hcg Hpc".
    set (mE0 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int toks : mword 64)]> mD).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x45e : mword 64) 2
                      = mword_of_int 0x460)) in "Hpc".
    (* ---- 0x460  c.ld s1,0(a0) ---- *)
    assert (Ha0E : mE0 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64)).
    { rewrite (upd_ne mD (Regidx s5_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha0B. }
    assert (Hvaps : (mword_of_int psaddr : mword 64)
                    = add_vec (mE0 !!! Regidx a0_idx)
                        (sign_extend' 64
                           (zero_extend' 12
                              (concat_vec (mword_of_int 0 : mword 5) ('b"000"))))).
    { rewrite Ha0E.
      assert (Hc : (sign_extend' 64
                      (zero_extend' 12
                         (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
                    : mword 64) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    assert (HpsrdP : uv_rd pt P7 psaddr 8)
      by exact (uv_rd_dom pt M P7 psaddr 8 Hfdom Hpsrd).
    assert (HcellP : uM_bytes P7 psaddr 8
                       (mword_of_int (s0 + Z.of_nat off) : mword 64)).
    { intros j Hj. rewrite (Hfout (psaddr + Z.of_nat j) ltac:(lia)).
      exact (Hcell j Hj). }
    destruct (uv_slot8_facts psaddr (mword_of_int psaddr) ltac:(lia) Hpsal
                ltac:(lia) eq_refl) as (Hups & Hcanps & Hpgps & Halps).
    destruct (uv_rd_leaf_at pt P7 psaddr 8 psaddr HpsrdP ltac:(lia))
      as (wps & Hlps & Hokps).
    iApply (wp_uv_cld C pt Psh P7 mE0 (mword_of_int 0x460)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx
              wps (mword_of_int psaddr)
              (mword_of_int (s0 + Z.of_nat off))
              (ui_sh_460 pt P7 Hltext (sh_img_text P7 Himg7))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hvaps Hlps Hokps Hcanps Hpgps Halps
              ltac:(rewrite Hups; exact HcellP)
              with "Hcg Hpc").
    iIntros (CID13) "Hcg Hpc".
    set (mF0 := <[Regidx s1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat off) : mword 64)]> mE0).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x460 : mword 64) 2
                      = mword_of_int 0x462)) in "Hpc".
    (* ---- 0x462  auipc s3,0x2 ---- *)
    iApply (wp_uv_auipc C pt Psh P7 mF0 (mword_of_int 0x462)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x2462)
              (ui_sh_462 pt P7 Hltext (sh_img_text P7 Himg7))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    set (mG := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x2462 : mword 64)]> mF0).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x462 : mword 64) 4
                      = mword_of_int 0x466)) in "Hpc".
    (* ---- 0x466  addi s3,s3,-1114 ---- *)
    assert (Hs3G : mG !!! Regidx s3_idx = (mword_of_int 0x2462 : mword 64))
      by exact (upd_eq mF0 (Regidx s3_idx) _).
    assert (Hwws : (mword_of_int SH_WHITESPACE : mword 64)
                   = add_vec (mG !!! Regidx s3_idx)
                       (sign_extend' 64 (mword_of_int 2982 : mword 12))).
    { rewrite Hs3G.
      assert (Hc : (sign_extend' 64 (mword_of_int 2982 : mword 12) : mword 64)
                   = mword_of_int (-1114))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. unfold SH_WHITESPACE, SH_DATA_PG. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh P7 mG (mword_of_int 0x466)
              (mword_of_int 2982 : mword 12) s3_idx s3_idx
              (mword_of_int SH_WHITESPACE)
              (ui_sh_466 pt P7 Hltext (sh_img_text P7 Himg7))
              ltac:(vm_compute; discriminate) Hwws with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    set (mH := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int SH_WHITESPACE : mword 64)]> mG).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x466 : mword 64) 4
                      = mword_of_int 0x46a)) in "Hpc".
    (* the register file entering the scan *)
    assert (HpresH : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> mH !!! Regidx r = m !!! Regidx r).
    { intros r Nsp N0 N1 N2 N3 N4 N5.
      rewrite (upd_ne mG (Regidx s3_idx) (Regidx r) _ N3).
      rewrite (upd_ne mF0 (Regidx s3_idx) (Regidx r) _ N3).
      rewrite (upd_ne mE0 (Regidx s1_idx) (Regidx r) _ N1).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx r) _ N5).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx r) _ N2).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx r) _ N4).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx r) _ N0).
      exact (HpresA r Nsp). }
    assert (Hs1H : mH !!! Regidx s1_idx
                   = (mword_of_int (s0 + Z.of_nat off) : mword 64)).
    { rewrite (upd_ne mG (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF0 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE0 (Regidx s1_idx) _). }
    assert (Hs2H : mH !!! Regidx s2_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne mG (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF0 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mC (Regidx s2_idx) _). }
    assert (Hs3H : mH !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64))
      by exact (upd_eq mG (Regidx s3_idx) _).
    assert (Hs4H : mH !!! Regidx s4_idx = (mword_of_int psaddr : mword 64)).
    { rewrite (upd_ne mG (Regidx s3_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF0 (Regidx s3_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s1_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mB (Regidx s4_idx) _). }
    assert (Hs5H : mH !!! Regidx s5_idx = (mword_of_int toks : mword 64)).
    { rewrite (upd_ne mG (Regidx s3_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF0 (Regidx s3_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s1_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mD (Regidx s5_idx) _). }
    assert (Ha1H : mH !!! Regidx a1_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (HpresH a1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact Hes. }
    assert (HspH : mH !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne mG (Regidx s3_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF0 (Regidx s3_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s1_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)). exact HspA. }
    assert (Hs0H : mH !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64)).
    { rewrite (upd_ne mG (Regidx s3_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF0 (Regidx s3_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s0_idx) _). }
    (* ---- 0x46a..0x480  the whitespace scan ---- *)
    iApply (wp_sh_wsskip CID15 0x46a (mword_of_int 1550) a1_idx
              P7 mH sp0 s0 bs off
              Hlay Hok7 ltac:(unfold sh_frame_ok; lia) Hs0p Hbufhi Hoff
              (fun Mx Hx => ui_sh_46a pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_46e pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_472 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_474 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_478 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_47a pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_47c pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_480 pt Mx Hltext Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hsstrchr; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hsstrchr; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Ha1H Hs1H Hs2H Hs3H HspH
              with "Hcg Hpc").
    iIntros (CID16 mI MI) "%Hs1I %HpresI %HonlyI Hcg Hpc".
    (* ---- the image and the registers the scan left ---- *)
    assert (HokI : lex_ok MI sp0 s0 bs)
      by exact (lex_ok_below P7 MI sp0 s0 bs (uint sp0 - 80) 16 HonlyI
                  ltac:(lia) ltac:(lia) Hok7).
    pose proof HokI as HokI'.
    destruct HokI' as (HimgI & HtabI & HbufI & HrdI & HstI).
    assert (Hs1I' : mI !!! Regidx s1_idx
                    = (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64))
      by exact Hs1I.
    assert (Hs4I : mI !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (HpresI s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4H).
    assert (Hs5I : mI !!! Regidx s5_idx = (mword_of_int toks : mword 64))
      by (rewrite (HpresI s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs5H).
    assert (HspI : mI !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (HpresI sp_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HspH).
    assert (HwrI : uv_wr pt MI psaddr 8).
    { apply (uv_wr_dom pt P7 MI psaddr 8); [ exact (proj1 HonlyI) | ].
      exact (uv_wr_dom pt M P7 psaddr 8 Hfdom Hcellw). }
    (* ---- 0x482  sd s1,0(s4) ---- *)
    assert (Hvps : (mword_of_int psaddr : mword 64)
                   = add_vec (mI !!! Regidx s4_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hs4I.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uwr_leaf _ _ _ _ HwrI 0 ltac:(lia)) as (wst & Hlst & Hokst).
    rewrite Z.add_0_r in Hlst.
    iApply (wp_uv_sd C pt Psh MI mI (mword_of_int 0x482)
              (mword_of_int 0 : mword 12) s4_idx s1_idx
              wst (mword_of_int psaddr)
              (mword_of_int (s0 + Z.of_nat (off + kk)))
              (ui_sh_482 pt MI Hltext (sh_img_text MI HimgI))
              Hvps (eq_sym Hs1I') Hlst Hokst Hcanps Hpgps Halps
              ltac:(rewrite Hups; intros j Hj;
                    exact (uwr_bytes _ _ _ _ HwrI (Z.of_nat j) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CID17) "Hcg Hpc".
    iEval (rewrite Hups) in "Hcg".
    set (M2 := uM_store8 MI psaddr
                 (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64)).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x482 : mword 64) 4
                      = mword_of_int 0x486)) in "Hpc".
    assert (Hcell2 : uM_bytes M2 psaddr 8
                       (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64))
      by exact (uM_store8_bytes MI psaddr _).
    assert (HonlyPS : uM_only MI M2 psaddr 8).
    { split.
      - intros k Hk. exact (uM_store8_is_Some MI psaddr _ k Hk).
      - intros k Hk. exact (um_st8_ne MI psaddr _ k Hk). }
    assert (Hok2 : lex_ok M2 sp0 s0 bs)
      by exact (lex_ok_below MI M2 sp0 s0 bs psaddr 8 HonlyPS
                  ltac:(lia) ltac:(lia) HokI).
    pose proof Hok2 as Hok2'.
    destruct Hok2' as (HimgW & HtabW & HbufW & HrdW & HstW).
    (* ---- 0x486  lbu a1,0(s1) ---- *)
    assert (Hbex : exists bp : bv 8,
              M2 !! (s0 + Z.of_nat (off + kk)) = Some bp /\
              ((off + kk)%nat = length bs -> bv_unsigned bp = 0) /\
              ((off + kk < length bs)%nat ->
                 bs !! (off + kk)%nat = Some bp /\ bv_unsigned bp <> 0)).
    { destruct HbufW as ((Hb2body & Hb2nul) & Hb2nz).
      destruct (decide ((off + kk)%nat = length bs)) as [He | Hne].
      - exists ubyte0. split_and!.
        + rewrite He. exact Hb2nul.
        + intros _. vm_compute. reflexivity.
        + intro Hc'. exfalso. lia.
      - assert (Hlt2 : (off + kk < length bs)%nat) by lia.
        destruct (lookup_lt_is_Some_2 bs (off + kk)%nat Hlt2) as (bp & Hbp).
        exists bp. split_and!.
        + exact (Hb2body (off + kk)%nat bp Hbp).
        + intro Hc'. exfalso. lia.
        + intros _. split; [ exact Hbp | ].
          intro H0. exact (Hb2nz (off + kk)%nat bp Hbp (proj1 (bv8_is0 bp) H0)). }
    destruct Hbex as (bp & Hbpm & Hbpz & Hbpn).
    assert (Hval : (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64)
                   = add_vec (mI !!! Regidx s1_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hs1I'.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M2 s0 (Z.of_nat (length bs) + 1)
                (s0 + Z.of_nat (off + kk)) HrdW ltac:(lia)) as (wb & Hlb & Hokb).
    assert (Huvb : uint (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64)
                   = s0 + Z.of_nat (off + kk)) by (apply uint_moi; unfold Z64; lia).
    assert (Hcanb : uva_canon
                      (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    iApply (wp_uv_lbu C pt Psh M2 mI (mword_of_int 0x486)
              (mword_of_int 0 : mword 12) s1_idx a1_idx
              wb (mword_of_int (s0 + Z.of_nat (off + kk)))
              (mword_of_int (bv_unsigned bp)) bp
              (ui_sh_486 pt M2 Hltext (sh_img_text M2 HimgW))
              ltac:(vm_compute; discriminate) Hval Hlb Hokb Hcanb
              ltac:(rewrite Huvb; exact Hbpm)
              ltac:(symmetry; apply zext8_moi)
              with "Hcg Hpc").
    iIntros (CID18) "Hcg Hpc".
    set (mJ := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (bv_unsigned bp) : mword 64)]> mI).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x486 : mword 64) 4
                      = mword_of_int 0x48a)) in "Hpc".
    (* ---- 0x48a  c.li a0,0 ---- *)
    iApply (wp_uv_cli C pt Psh M2 mJ (mword_of_int 0x48a)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
              (ui_sh_48a pt M2 Hltext (sh_img_text M2 HimgW))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID19) "Hcg Hpc".
    set (mK := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> mJ).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x48a : mword 64) 2
                      = mword_of_int 0x48c)) in "Hpc".
    (* the registers that reach the exit either way *)
    assert (HpresK : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> mK !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp N0 N1 N2 N3 N4 N5.
      rewrite (upd_ne mJ (Regidx a0_idx) (Regidx r) _
                 ltac:(intro E; injection E as E'; subst r;
                       vm_compute in Hr; discriminate)).
      rewrite (upd_ne mI (Regidx a1_idx) (Regidx r) _
                 ltac:(intro E; injection E as E'; subst r;
                       vm_compute in Hr; discriminate)).
      rewrite (HpresI r Hr N1). exact (HpresH r Nsp N0 N1 N2 N3 N4 N5). }
    assert (HspK : mK !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne mJ (Regidx a0_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mI (Regidx a1_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)). exact HspI. }
    assert (Hs5K : mK !!! Regidx s5_idx = (mword_of_int toks : mword 64)).
    { rewrite (upd_ne mJ (Regidx a0_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mI (Regidx a1_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs5I. }
    assert (Ha1K : mK !!! Regidx a1_idx
                   = (mword_of_int (bv_unsigned bp) : mword 64)).
    { rewrite (upd_ne mJ (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mI (Regidx a1_idx) _). }
    (* every byte below the frame is still the entry image's *)
    assert (Hbelow2 : forall k : Z, k < uint sp0 - 80 -> M2 !! k = M !! k).
    { intros k Hk. unfold M2.
      rewrite (um_st8_ne MI psaddr _ k ltac:(lia)).
      rewrite (proj2 HonlyI k ltac:(lia)). apply Hfout. lia. }
    assert (Hframe2 : forall k : Z, uint sp0 - 56 <= k < uint sp0 ->
              M2 !! k = P7 !! k).
    { intros k Hk. unfold M2. rewrite (um_st8_ne MI psaddr _ k ltac:(lia)).
      exact (proj2 HonlyI k ltac:(lia)). }
    assert (Hdom2 : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k)).
    { intros k Hk. unfold M2. apply uM_store8_is_Some.
      exact (proj1 HonlyI k (Hfdom k Hk)). }
    (* ---- 0x48c  c.bnez a1,0x4a0 ---- *)
    destruct (decide ((off + kk)%nat = length bs)) as [Hend | Hne].
    - (* END OF INPUT: *s == 0, the return value is 0 ---- *)
      assert (Hz : bv_unsigned bp = 0) by exact (Hbpz Hend).
      assert (Htk : false = neq_vec (mK !!! Regidx a1_idx) zero_reg).
      { rewrite Ha1K (moi_neq_zero (bv_unsigned bp) (bv8_rng bp)) Hz.
        reflexivity. }
      iApply (wp_uv_cbnez C pt Psh M2 mK (mword_of_int 0x48c)
                (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                false (mword_of_int 0x4a0)
                (ui_sh_48c pt M2 Hltext (sh_img_text M2 HimgW))
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID20) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x4a0 : mword 64)
                         else add_vec_int (mword_of_int 0x48c : mword 64) 2)
                        = mword_of_int 0x48e)) in "Hpc".
      assert (Hret0 : sh_peek_ret bs off tbs = 0).
      { unfold sh_peek_ret. cbn zeta.
        rewrite (lookup_drop bs (off + sh_skipws (drop off bs))%nat 0%nat).
        replace (off + sh_skipws (drop off bs) + 0)%nat with (length bs)
          by (unfold kk in Hend; lia).
        rewrite (lookup_ge_None_2 bs (length bs) ltac:(lia)). reflexivity. }
      assert (Ha0K : mK !!! Regidx a0_idx
                     = (mword_of_int (sh_peek_ret bs off tbs) : mword 64))
        by (rewrite Hret0; exact (upd_eq mJ (Regidx a0_idx) _)).
      iApply (wp_sh_peek_exit CID20 M2 mK m sp0 (sh_peek_ret bs off tbs)
                Hltext (sh_img_text M2 HimgW)
                ltac:(apply (uv_stack_split pt M2 sp0 80 64 16 ltac:(lia)
                               ltac:(lia) ltac:(reflexivity) ltac:(lia) HstW))
                Hret2 Hsp HspK Ha0K
                ltac:(intros j Hj;
                      rewrite (Hframe2 (uint sp0 - 8 + Z.of_nat j) ltac:(lia));
                      exact (Hg0 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe2 (uint sp0 - 16 + Z.of_nat j) ltac:(lia));
                      exact (Hg1 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe2 (uint sp0 - 24 + Z.of_nat j) ltac:(lia));
                      exact (Hg2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe2 (uint sp0 - 32 + Z.of_nat j) ltac:(lia));
                      exact (Hg3 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe2 (uint sp0 - 40 + Z.of_nat j) ltac:(lia));
                      exact (Hg4 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe2 (uint sp0 - 48 + Z.of_nat j) ltac:(lia));
                      exact (Hg5 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe2 (uint sp0 - 56 + Z.of_nat j) ltac:(lia));
                      exact (Hg6 j Hj))
                HpresK
                with "Hcg Hpc [Hcont]").
      iIntros (CID21 m') "%Hcs %Ha0' Hcg Hpc".
      iApply ("Hcont" $! CID21 m' M2 with "[] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0'.
      + iPureIntro. exact Hcell2.
      + iPureIntro. split.
        * intros k Hk. exact (Hdom2 k Hk).
        * intros k Hk.
          destruct (not_in_win _ psaddr 8 k
                      ltac:(apply elem_of_list_here) Hk) as [Hlt | Hge].
          -- unfold M2. rewrite (um_st8_ne MI psaddr _ k ltac:(lia)).
             destruct (not_in_win _ (uint sp0 - 80) 80 k
                         ltac:(apply elem_of_list_further; apply elem_of_list_here)
                         Hk) as [Hlt2 | Hge2].
             ++ rewrite (proj2 HonlyI k ltac:(lia)). apply Hfout. lia.
             ++ rewrite (proj2 HonlyI k ltac:(lia)). apply Hfout. lia.
          -- unfold M2. rewrite (um_st8_ne MI psaddr _ k ltac:(lia)).
             destruct (not_in_win _ (uint sp0 - 80) 80 k
                         ltac:(apply elem_of_list_further; apply elem_of_list_here)
                         Hk) as [Hlt2 | Hge2].
             ++ rewrite (proj2 HonlyI k ltac:(lia)). apply Hfout. lia.
             ++ rewrite (proj2 HonlyI k ltac:(lia)). apply Hfout. lia.
    - (* A REAL BYTE: the second strchr decides the answer ---- *)
      assert (Hlt2 : (off + kk < length bs)%nat) by lia.
      destruct (Hbpn Hlt2) as (Hbpl & Hbnz).
      assert (Htk : true = neq_vec (mK !!! Regidx a1_idx) zero_reg).
      { rewrite Ha1K (moi_neq_zero (bv_unsigned bp) (bv8_rng bp)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hbnz. }
      iApply (wp_uv_cbnez C pt Psh M2 mK (mword_of_int 0x48c)
                (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                true (mword_of_int 0x4a0)
                (ui_sh_48c pt M2 Hltext (sh_img_text M2 HimgW))
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID20) "Hcg Hpc".
      (* ---- 0x4a0  c.mv a0,s5 ---- *)
      iApply (wp_uv_cmv C pt Psh M2 mK (mword_of_int 0x4a0)
                a0_idx s5_idx (mword_of_int toks)
                (ui_sh_4a0 pt M2 Hltext (sh_img_text M2 HimgW))
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs5K; symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID21) "Hcg Hpc".
      set (mL := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int toks : mword 64)]> mK).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x4a0 : mword 64) 2
                        = mword_of_int 0x4a2)) in "Hpc".
      (* ---- 0x4a2  jal ra,strchr ---- *)
      iApply (wp_uv_jal C pt Psh M2 mL (mword_of_int 0x4a2)
                (mword_of_int 1504 : mword 21) ra_idx
                (mword_of_int ShSyms.strchr) (mword_of_int 0x4a6)
                (ui_sh_4a2 pt M2 Hltext (sh_img_text M2 HimgW))
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hsstrchr; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hsstrchr; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID22) "Hcg Hpc".
      set (mM := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x4a6 : mword 64)]> mL).
      (* ---- the call: strchr(toks, *s) ---- *)
      destruct (spA_facts M2 sp0 HstW) as (HstA2 & HuA2).
      assert (HspM : mM !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
      { rewrite (upd_ne mL (Regidx ra_idx) (Regidx sp_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne mK (Regidx a0_idx) (Regidx sp_idx) _
                   ltac:(vm_compute; discriminate)). exact HspK. }
      assert (Ha0M : mM !!! Regidx a0_idx = (mword_of_int toks : mword 64)).
      { rewrite (upd_ne mL (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq mK (Regidx a0_idx) _). }
      assert (Ha1M : mM !!! Regidx a1_idx
                     = (mword_of_int (bv_unsigned bp) : mword 64)).
      { rewrite (upd_ne mL (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne mK (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate)). exact Ha1K. }
      assert (HraM : mM !!! Regidx ra_idx = (mword_of_int 0x4a6 : mword 64))
        by exact (upd_eq mL (Regidx ra_idx) _).
      assert (Htbs2 : ustr_at M2 toks tbs).
      { destruct Htbs as (Hb & Hn). split.
        - intros j b Hj. pose proof (lookup_lt_Some tbs j b Hj) as Hjl.
          rewrite (Hbelow2 (toks + Z.of_nat j) ltac:(lia)). exact (Hb j b Hj).
        - rewrite (Hbelow2 (toks + Z.of_nat (length tbs)) ltac:(lia)). exact Hn. }
      assert (Htrd2 : uv_rd pt M2 toks (Z.of_nat (length tbs) + 1)).
      { constructor; try (destruct Htrd; assumption).
        intros j Hj. destruct (urd_bytes _ _ _ _ Htrd j Hj) as (b & Hb).
        exists b. rewrite (Hbelow2 (toks + j) ltac:(lia)). exact Hb. }
      iApply (wp_sh_strchr C pt gin gbrk hbase hlen Q CID22 M2 mM
                (mword_of_int (uint sp0 - 64)) toks tbs bp
                Hlay (sh_img_text M2 HimgW) HspM HstA2 Ha0M Ha1M Htnz Htbs2
                Htrd2
                ltac:(right; rewrite HuA2; lia)
                ltac:(unfold sh_frame_ok; rewrite HuA2; lia)
                ltac:(rewrite HraM; vm_compute; reflexivity)
                with "Hcg Hpc [Hcont]").
      iIntros (CID23 m4 M3) "%Hcs4 %Ha0_4 %Honly4 Hcg Hpc".
      iEval (rewrite HraM) in "Hpc".
      rewrite HuA2 in Honly4.
      assert (Honly4' : uM_only M2 M3 (uint sp0 - 80) 16).
      { destruct Honly4 as (D & E). split; [ exact D | ].
        intros k Hk. apply E. lia. }
      assert (Hok3 : lex_ok M3 sp0 s0 bs)
        by exact (lex_ok_below M2 M3 sp0 s0 bs (uint sp0 - 80) 16 Honly4'
                    ltac:(lia) ltac:(lia) Hok2).
      pose proof Hok3 as Hok3'.
      destruct Hok3' as (HimgX & HtabX & HbufX & HrdX & HstX).
      (* ---- 0x4a6  snez a0,a0 ---- *)
      assert (Hretv : sh_peek_ret bs off tbs
                      = (if bool_decide (bp ∈ tbs) then 1 else 0)).
      { unfold sh_peek_ret. cbn zeta.
        rewrite (lookup_drop bs (off + sh_skipws (drop off bs))%nat 0%nat).
        replace (off + sh_skipws (drop off bs) + 0)%nat with (off + kk)%nat
          by (unfold kk; lia).
        rewrite Hbpl. reflexivity. }
      iDestruct "Hcg" as "(Hcap & Hlin & Hgpr)".
      iDestruct (gpr_file_x0 m4 (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hgpr") as "[%Hz Hgpr]".
      iAssert (uv_cap_gpr (CID := CID23) C pt Psh M3 m4)
        with "[Hcap Hlin Hgpr]" as "Hcg".
      { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
      assert (Hwsnez : (mword_of_int (sh_peek_ret bs off tbs) : mword 64)
                       = zero_extend' 64
                           (bool_to_bit
                              (zopz0zI_u (m4 !!! Regidx (mword_of_int 0 : mword 5))
                                 (m4 !!! Regidx a0_idx)))).
      { rewrite Hz Ha0_4 zero_reg_moi Hretv.
        destruct (decide (bp ∈ tbs)) as [Hin | Hnin].
        - destruct (ustr_find_elem tbs bp Hin) as (i & Hi & Hilt).
          rewrite Hi (bool_decide_eq_true_2 _ Hin).
          rewrite (moi_lt_u 0 (toks + Z.of_nat i) ltac:(unfold Z64; lia)
                     ltac:(unfold Z64; lia)).
          replace (0 <? toks + Z.of_nat i) with true
            by (symmetry; apply Z.ltb_lt; lia).
          apply bv_eq; vm_compute; reflexivity.
        - rewrite (ustr_find_not_elem tbs bp Hnin)
                  (bool_decide_eq_false_2 _ Hnin).
          rewrite (moi_lt_u 0 0 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
          apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_uv_sltu C pt Psh M3 m4 (mword_of_int 0x4a6)
                (mword_of_int 0 : mword 5) a0_idx a0_idx
                (mword_of_int (sh_peek_ret bs off tbs))
                (ui_sh_4a6 pt M3 Hltext (sh_img_text M3 HimgX))
                ltac:(vm_compute; discriminate) Hwsnez with "Hcg Hpc").
      iIntros (CID24) "Hcg Hpc".
      set (mN := <[Regidx a0_idx
                   := regval_into_reg
                        (mword_of_int (sh_peek_ret bs off tbs) : mword 64)]> m4).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x4a6 : mword 64) 4
                        = mword_of_int 0x4aa)) in "Hpc".
      (* ---- 0x4aa  c.j 0x48e ---- *)
      iApply (wp_uv_cj C pt Psh M3 mN (mword_of_int 0x4aa)
                (mword_of_int 2034 : mword 11) (mword_of_int 0x48e)
                (ui_sh_4aa pt M3 Hltext (sh_img_text M3 HimgX))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc").
      iIntros (CID25) "Hcg Hpc".
      (* ---- the exit ---- *)
      assert (Hbelow3 : forall k : Z, k < uint sp0 - 80 -> M3 !! k = M !! k).
      { intros k Hk. rewrite (proj2 Honly4' k ltac:(lia)). exact (Hbelow2 k Hk). }
      assert (Hframe3 : forall k : Z, uint sp0 - 56 <= k < uint sp0 ->
                M3 !! k = P7 !! k).
      { intros k Hk. rewrite (proj2 Honly4' k ltac:(lia)).
        exact (Hframe2 k Hk). }
      assert (HspN : mN !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
      { rewrite (upd_ne m4 (Regidx a0_idx) (Regidx sp_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (Hcs4 sp_idx ltac:(vm_compute; reflexivity)). exact HspM. }
      assert (Ha0N : mN !!! Regidx a0_idx
                     = (mword_of_int (sh_peek_ret bs off tbs) : mword 64))
        by exact (upd_eq m4 (Regidx a0_idx) _).
      assert (HpresN : forall r : mword 5, ucallee_saved_idx r = true ->
                Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
                Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
                Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
                Regidx r <> Regidx s5_idx -> mN !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp N0 N1 N2 N3 N4 N5.
        rewrite (upd_ne m4 (Regidx a0_idx) (Regidx r) _
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate)).
        rewrite (Hcs4 r Hr).
        rewrite (upd_ne mL (Regidx ra_idx) (Regidx r) _
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate)).
        rewrite (upd_ne mK (Regidx a0_idx) (Regidx r) _
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate)).
        exact (HpresK r Hr Nsp N0 N1 N2 N3 N4 N5). }
      iApply (wp_sh_peek_exit CID25 M3 mN m sp0 (sh_peek_ret bs off tbs)
                Hltext (sh_img_text M3 HimgX)
                ltac:(apply (uv_stack_split pt M3 sp0 80 64 16 ltac:(lia)
                               ltac:(lia) ltac:(reflexivity) ltac:(lia) HstX))
                Hret2 Hsp HspN Ha0N
                ltac:(intros j Hj;
                      rewrite (Hframe3 (uint sp0 - 8 + Z.of_nat j) ltac:(lia));
                      exact (Hg0 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe3 (uint sp0 - 16 + Z.of_nat j) ltac:(lia));
                      exact (Hg1 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe3 (uint sp0 - 24 + Z.of_nat j) ltac:(lia));
                      exact (Hg2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe3 (uint sp0 - 32 + Z.of_nat j) ltac:(lia));
                      exact (Hg3 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe3 (uint sp0 - 40 + Z.of_nat j) ltac:(lia));
                      exact (Hg4 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe3 (uint sp0 - 48 + Z.of_nat j) ltac:(lia));
                      exact (Hg5 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hframe3 (uint sp0 - 56 + Z.of_nat j) ltac:(lia));
                      exact (Hg6 j Hj))
                HpresN
                with "Hcg Hpc [Hcont]").
      iIntros (CID26 m') "%Hcs %Ha0' Hcg Hpc".
      iApply ("Hcont" $! CID26 m' M3 with "[] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0'.
      + iPureIntro. intros j Hj.
        rewrite (proj2 Honly4' (psaddr + Z.of_nat j) ltac:(lia)).
        exact (Hcell2 j Hj).
      + iPureIntro. split.
        * intros k Hk. exact (proj1 Honly4' k (Hdom2 k Hk)).
        * intros k Hk.
          destruct (not_in_win _ psaddr 8 k
                      ltac:(apply elem_of_list_here) Hk) as [Hlt | Hge];
            destruct (not_in_win _ (uint sp0 - 80) 80 k
                        ltac:(apply elem_of_list_further; apply elem_of_list_here)
                        Hk) as [Hlt3 | Hge3];
            rewrite (proj2 Honly4' k ltac:(lia));
            unfold M2;
            rewrite (um_st8_ne MI psaddr _ k ltac:(lia));
            rewrite (proj2 HonlyI k ltac:(lia));
            apply Hfout; lia.
  Qed.

  (* ===================================================================== *)
  (* §5 gettoken @0x310 -- the eight-slot frame and the three tails.        *)
  (* ===================================================================== *)

  Local Lemma spill8_facts (M M8 : gmap Z (bv 8)) (bot : Z)
      (v0 v1 v2 v3 v4 v5 v6 v7 : mword 64) :
    M8 = uM_store8 (uM_store8 (uM_store8 (uM_store8 (uM_store8
             (uM_store8 (uM_store8 (uM_store8 M (bot + 56) v0)
                (bot + 48) v1) (bot + 40) v2) (bot + 32) v3)
                (bot + 24) v4) (bot + 16) v5) (bot + 8) v6) (bot + 0) v7 ->
    uM_bytes M8 (bot + 56) 8 v0 /\ uM_bytes M8 (bot + 48) 8 v1 /\
    uM_bytes M8 (bot + 40) 8 v2 /\ uM_bytes M8 (bot + 32) 8 v3 /\
    uM_bytes M8 (bot + 24) 8 v4 /\ uM_bytes M8 (bot + 16) 8 v5 /\
    uM_bytes M8 (bot + 8) 8 v6 /\ uM_bytes M8 (bot + 0) 8 v7 /\
    (forall k : Z, k < bot + 0 \/ bot + 64 <= k -> M8 !! k = M !! k) /\
    (forall k : Z, is_Some (M !! k) -> is_Some (M8 !! k)).
  Proof.
    intro H8. subst M8.
    destruct (spill7_facts M _ bot v0 v1 v2 v3 v4 v5 v6 eq_refl)
      as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & Hout & Hdom).
    split_and!.
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 0) v7 (bot + 56 + Z.of_nat j) ltac:(lia)).
      exact (H0 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 0) v7 (bot + 48 + Z.of_nat j) ltac:(lia)).
      exact (H1 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 0) v7 (bot + 40 + Z.of_nat j) ltac:(lia)).
      exact (H2 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 0) v7 (bot + 32 + Z.of_nat j) ltac:(lia)).
      exact (H3 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 0) v7 (bot + 24 + Z.of_nat j) ltac:(lia)).
      exact (H4 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 0) v7 (bot + 16 + Z.of_nat j) ltac:(lia)).
      exact (H5 j Hj).
    - intros j Hj.
      rewrite (um_st8_ne _ (bot + 0) v7 (bot + 8 + Z.of_nat j) ltac:(lia)).
      exact (H6 j Hj).
    - exact (uM_store8_bytes _ (bot + 0) v7).
    - intros k Hk. rewrite (um_st8_ne _ (bot + 0) v7 k ltac:(lia)).
      apply Hout. lia.
    - intros k Hk. apply uM_store8_is_Some. exact (Hdom k Hk).
  Qed.

  (* the eight spilled words, and the callee-saved registers the epilogue
     does NOT restore -- bundled, because every tail lemma carries both *)
  Definition gt_slots (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) : Prop :=
    uM_bytes M (uint sp0 - 8) 8 (m !!! Regidx ra_idx) /\
    uM_bytes M (uint sp0 - 16) 8 (m !!! Regidx s0_idx) /\
    uM_bytes M (uint sp0 - 24) 8 (m !!! Regidx s1_idx) /\
    uM_bytes M (uint sp0 - 32) 8 (m !!! Regidx s2_idx) /\
    uM_bytes M (uint sp0 - 40) 8 (m !!! Regidx s3_idx) /\
    uM_bytes M (uint sp0 - 48) 8 (m !!! Regidx s4_idx) /\
    uM_bytes M (uint sp0 - 56) 8 (m !!! Regidx s5_idx) /\
    uM_bytes M (uint sp0 - 64) 8 (m !!! Regidx s6_idx).

  Definition gt_pres (mF m : regfile) : Prop :=
    forall r : mword 5, ucallee_saved_idx r = true ->
      Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
      Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
      Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
      Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s6_idx ->
      mF !!! Regidx r = m !!! Regidx r.

  Local Lemma gt_slots_eq (M M' : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) :
    (forall k : Z, uint sp0 - 64 <= k < uint sp0 -> M' !! k = M !! k) ->
    gt_slots M m sp0 -> gt_slots M' m sp0.
  Proof.
    intros Heq (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7).
    split_and!;
      [ exact (uM_bytes_eq8 M M' (uint sp0 - 8) _ ltac:(intros k Hk; apply Heq; lia) A0)
      | exact (uM_bytes_eq8 M M' (uint sp0 - 16) _ ltac:(intros k Hk; apply Heq; lia) A1)
      | exact (uM_bytes_eq8 M M' (uint sp0 - 24) _ ltac:(intros k Hk; apply Heq; lia) A2)
      | exact (uM_bytes_eq8 M M' (uint sp0 - 32) _ ltac:(intros k Hk; apply Heq; lia) A3)
      | exact (uM_bytes_eq8 M M' (uint sp0 - 40) _ ltac:(intros k Hk; apply Heq; lia) A4)
      | exact (uM_bytes_eq8 M M' (uint sp0 - 48) _ ltac:(intros k Hk; apply Heq; lia) A5)
      | exact (uM_bytes_eq8 M M' (uint sp0 - 56) _ ltac:(intros k Hk; apply Heq; lia) A6)
      | exact (uM_bytes_eq8 M M' (uint sp0 - 64) _ ltac:(intros k Hk; apply Heq; lia) A7) ].
  Qed.

  (* ---- gettoken's EXIT: eight reloads, [c.addi16sp sp,+64], [c.jr ra] -- *)
  Local Lemma wp_sh_gt_exit (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64) (ret : Z) :
    sh_text_layout pt -> sh_text_sub M ->
    uv_stack pt M sp0 64 ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx a0_idx = (mword_of_int ret : mword 64) ->
    gt_slots M m sp0 ->
    gt_pres mF m ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x3b6) -∗
    (∀ (CID : CpuId) (m' : regfile),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int ret : mword 64)⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hltext Htext Hst Hret2 Hspm HspF Ha0F Hslots Hpres.
    destruct Hslots as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7).
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_sh_epi7 CIDp 0x3b6 M mF sp0
              (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s1_idx)
              (m !!! Regidx s2_idx) (m !!! Regidx s3_idx) (m !!! Regidx s4_idx)
              (m !!! Regidx s5_idx)
              Hst HspF A0 A1 A2 A3 A4 A5 A6
              (ui_sh_3b6 pt M Hltext Htext) (ui_sh_3b8 pt M Hltext Htext)
              (ui_sh_3ba pt M Hltext Htext) (ui_sh_3bc pt M Hltext Htext)
              (ui_sh_3be pt M Hltext Htext) (ui_sh_3c0 pt M Hltext Htext)
              (ui_sh_3c2 pt M Hltext Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros (CID1 mR) "%Hra %Hs0 %Hs1 %Hs2 %Hs3 %Hs4 %Hs5 %HpR Hcg Hpc".
    (* ---- 0x3c4  c.ldsp s6,0(sp) ---- *)
    assert (HspR : mR !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (HpR sp_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HspF. }
    assert (Hw7 : uM_word M (uint sp0 - 64 + 0) 8 = m !!! Regidx s6_idx).
    { replace (uint sp0 - 64 + 0) with (uint sp0 - 64) by lia.
      exact (uM_word_of_bytes M (uint sp0 - 64) _ A7). }
    iApply (wp_uv_frame_load C pt CID1 Psh M mR sp0 (mword_of_int 0x3c4)
              (mword_of_int 0 : mword 6) s6_idx 64 0 (m !!! Regidx s6_idx)
              (ui_sh_3c4 pt M Hltext Htext) ltac:(vm_compute; discriminate) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) HspR
              ltac:(apply bv_eq; vm_compute; reflexivity) (eq_sym Hw7)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3c4 : mword 64) 2
                      = mword_of_int 0x3c6)) in "Hpc".
    set (mS := <[Regidx s6_idx := regval_into_reg (m !!! Regidx s6_idx)]> mR).
    (* ---- 0x3c6  c.addi16sp sp,sp,64 ---- *)
    assert (HspS : mS !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne mR (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact HspR. }
    assert (Hwsp : sp0 = add_vec (mS !!! Regidx csp_rs1)
                          (sign_extend' 64
                             (caddi16sp_imm (mword_of_int 4 : mword 6)))).
    { rewrite HspS.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 64 + 64) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh M mS (mword_of_int 0x3c6)
              (mword_of_int 4 : mword 6) sp0
              (ui_sh_3c6 pt M Hltext Htext) Hwsp with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mT := <[Regidx csp_rs1 := regval_into_reg sp0]> mS).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3c6 : mword 64) 2
                      = mword_of_int 0x3c8)) in "Hpc".
    (* ---- 0x3c8  c.jr ra ---- *)
    assert (HraT : mT !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne mS (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mR (Regidx s6_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)). exact Hra. }
    assert (Htgt : (m !!! Regidx ra_idx) = ret_pc (mT !!! Regidx ra_idx)).
    { rewrite HraT. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh M mT (mword_of_int 0x3c8)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_3c8 pt M Hltext Htext)
              ltac:(vm_compute; discriminate) Htgt with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iApply ("Hcont" $! CID4 mT with "[] [] Hcg Hpc").
    - iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
      { rewrite Esp. rewrite (upd_eq mS (Regidx csp_rs1) _). symmetry. exact Hspm. }
      rewrite (upd_ne mS (Regidx csp_rs1) (Regidx r) _ Nsp).
      destruct (decide (Regidx r = Regidx s6_idx)) as [E6 | N6].
      { rewrite E6. exact (upd_eq mR (Regidx s6_idx) _). }
      rewrite (upd_ne mR (Regidx s6_idx) (Regidx r) _ N6).
      destruct (decide (Regidx r = Regidx s0_idx)) as [E0 | N0].
      { rewrite E0. exact Hs0. }
      destruct (decide (Regidx r = Regidx s1_idx)) as [E1 | N1].
      { rewrite E1. exact Hs1. }
      destruct (decide (Regidx r = Regidx s2_idx)) as [E2 | N2].
      { rewrite E2. exact Hs2. }
      destruct (decide (Regidx r = Regidx s3_idx)) as [E3 | N3].
      { rewrite E3. exact Hs3. }
      destruct (decide (Regidx r = Regidx s4_idx)) as [E4 | N4].
      { rewrite E4. exact Hs4. }
      destruct (decide (Regidx r = Regidx s5_idx)) as [E5 | N5].
      { rewrite E5. exact Hs5. }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HpR r Nra N0 N1 N2 N3 N4 N5).
      exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5 N6).
    - iPureIntro.
      rewrite (upd_ne mS (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mR (Regidx s6_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpR a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact Ha0F.
  Qed.

  Local Lemma uM_only_in_of_only (M M' : gmap Z (bv 8)) (a n : Z)
      (ws : list (Z * Z)) :
    uM_only M M' a n -> (a, n) ∈ ws -> uM_only_in M M' ws.
  Proof.
    intros H Hin. apply (uM_only_in_weaken M M' [(a, n)] ws).
    - apply uM_only_in_one. exact H.
    - intros x Hx. apply elem_of_list_singleton in Hx. subst x. exact Hin.
  Qed.

  (* ---- the tail from 0x3b0: [*ps = s], [a0 = ret], the epilogue ------- *)
  Local Lemma wp_sh_gt_tail3b0 (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64)
      (psaddr v ret : Z) :
    sh_text_layout pt -> sh_text_sub M ->
    uv_stack pt M sp0 64 ->
    12288 <= uint sp0 ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    uv_wr pt M psaddr 8 -> psaddr mod 8 = 0 ->
    uint sp0 <= psaddr -> psaddr + 8 <= 2 ^ 38 ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx s1_idx = (mword_of_int v : mword 64) ->
    mF !!! Regidx s4_idx = (mword_of_int psaddr : mword 64) ->
    mF !!! Regidx s5_idx = (mword_of_int ret : mword 64) ->
    gt_slots M m sp0 -> gt_pres mF m ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x3b0) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int ret : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8 (mword_of_int v : mword 64)⌝ -∗
       ⌜uM_only M M' psaddr 8⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hltext Htext Hst Hsphi Hret2 Hspm Hwr Hpsal Hpshi Hpshi2
           HspF Hs1F Hs4F Hs5F Hslots Hpres.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    change (2 ^ 38) with 274877906944 in Hpshi2.
    destruct (uv_slot8_facts psaddr (mword_of_int psaddr) ltac:(lia) Hpsal
                ltac:(lia) eq_refl) as (Hups & Hcanps & Hpgps & Halps).
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x3b0  sd s1,0(s4) ---- *)
    assert (Hva : (mword_of_int psaddr : mword 64)
                  = add_vec (mF !!! Regidx s4_idx)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hs4F.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uwr_leaf _ _ _ _ Hwr 0 ltac:(lia)) as (wst & Hlst & Hokst).
    rewrite Z.add_0_r in Hlst.
    iApply (wp_uv_sd C pt Psh M mF (mword_of_int 0x3b0)
              (mword_of_int 0 : mword 12) s4_idx s1_idx
              wst (mword_of_int psaddr) (mword_of_int v)
              (ui_sh_3b0 pt M Hltext Htext)
              Hva (eq_sym Hs1F) Hlst Hokst Hcanps Hpgps Halps
              ltac:(rewrite Hups; intros j Hj;
                    exact (uwr_bytes _ _ _ _ Hwr (Z.of_nat j) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    iEval (rewrite Hups) in "Hcg".
    set (M2 := uM_store8 M psaddr (mword_of_int v : mword 64)).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3b0 : mword 64) 4
                      = mword_of_int 0x3b4)) in "Hpc".
    assert (Honly : uM_only M M2 psaddr 8).
    { split.
      - intros k Hk. exact (uM_store8_is_Some M psaddr _ k Hk).
      - intros k Hk. exact (um_st8_ne M psaddr _ k Hk). }
    assert (Hcellv : uM_bytes M2 psaddr 8 (mword_of_int v : mword 64))
      by exact (uM_store8_bytes M psaddr _).
    assert (Htext2 : sh_text_sub M2).
    { intros k b Hk. unfold M2.
      rewrite (um_st8_ne M psaddr _ k
                 ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hst2 : uv_stack pt M2 sp0 64)
      by (unfold M2; apply stack_store8; exact Hst).
    assert (Hslots2 : gt_slots M2 m sp0)
      by (apply (gt_slots_eq M M2 m sp0);
          [ intros k Hk; unfold M2; apply um_st8_ne; lia | exact Hslots ]).
    (* ---- 0x3b4  c.mv a0,s5 ---- *)
    iApply (wp_uv_cmv C pt Psh M2 mF (mword_of_int 0x3b4)
              a0_idx s5_idx (mword_of_int ret)
              (ui_sh_3b4 pt M2 Hltext Htext2)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5F; symmetry; apply moi_add_zero_l)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mG := <[Regidx a0_idx := regval_into_reg (mword_of_int ret : mword 64)]> mF).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3b4 : mword 64) 2
                      = mword_of_int 0x3b6)) in "Hpc".
    assert (HspG : mG !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne mF (Regidx a0_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)). exact HspF. }
    assert (Ha0G : mG !!! Regidx a0_idx = (mword_of_int ret : mword 64))
      by exact (upd_eq mF (Regidx a0_idx) _).
    assert (HpresG : gt_pres mG m).
    { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6.
      rewrite (upd_ne mF (Regidx a0_idx) (Regidx r) _
                 ltac:(intro E; injection E as E'; subst r;
                       vm_compute in Hr; discriminate)).
      exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5 N6). }
    iApply (wp_sh_gt_exit CID2 M2 mG m sp0 ret
              Hltext Htext2 Hst2 Hret2 Hspm HspG Ha0G Hslots2 HpresG
              with "Hcg Hpc [Hcont]").
    iIntros (CID3 m') "%Hcs %Ha0' Hcg Hpc".
    iApply ("Hcont" $! CID3 m' M2 with "[] [] [] [] Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
    - iPureIntro. exact Hcellv.
    - iPureIntro. exact Honly.
  Qed.

  (* ---- the tail from 0x390: s3 := whitespace, the SECOND scan, then     *)
  (*      [*ps = s] and the epilogue ------------------------------------- *)
  Local Lemma wp_sh_gt_tail390 (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64)
      (psaddr s0 : Z) (bs : list (bv 8)) (p : nat) (ret : Z) :
    sh_layout pt hbase hlen ->
    lex_ok M sp0 s0 bs ->
    sh_frame_ok hbase hlen sp0 80 ->
    0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
    (p <= length bs)%nat ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    uv_wr pt M psaddr 8 -> psaddr mod 8 = 0 ->
    uint sp0 <= psaddr -> psaddr + 8 <= 2 ^ 38 ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat p) : mword 64) ->
    mF !!! Regidx s2_idx
      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    mF !!! Regidx s4_idx = (mword_of_int psaddr : mword 64) ->
    mF !!! Regidx s5_idx = (mword_of_int ret : mword 64) ->
    gt_slots M m sp0 -> gt_pres mF m ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x390) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int ret : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (p + sh_skipws (drop p bs)))
           : mword 64)⌝ -∗
       ⌜uM_only_in M M' [(psaddr, 8); (uint sp0 - 80, 80)]⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hok Hfr Hs0p Hbufhi Hp Hret2 Hspm Hwr Hpsal Hpshi Hpshi2
           HspF Hs1F Hs2F Hs4F Hs5F Hslots Hpres.
    unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & Hsstrchr & _).
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x390  auipc s3,0x2 ---- *)
    iApply (wp_uv_auipc C pt Psh M mF (mword_of_int 0x390)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x2390)
              (ui_sh_390 pt M Hltext Htext)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mG := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x2390 : mword 64)]> mF).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x390 : mword 64) 4
                      = mword_of_int 0x394)) in "Hpc".
    (* ---- 0x394  addi s3,s3,-904 ---- *)
    assert (Hs3G : mG !!! Regidx s3_idx = (mword_of_int 0x2390 : mword 64))
      by exact (upd_eq mF (Regidx s3_idx) _).
    assert (Hwws : (mword_of_int SH_WHITESPACE : mword 64)
                   = add_vec (mG !!! Regidx s3_idx)
                       (sign_extend' 64 (mword_of_int 3192 : mword 12))).
    { rewrite Hs3G.
      assert (Hc : (sign_extend' 64 (mword_of_int 3192 : mword 12) : mword 64)
                   = mword_of_int (-904))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. unfold SH_WHITESPACE, SH_DATA_PG. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh M mG (mword_of_int 0x394)
              (mword_of_int 3192 : mword 12) s3_idx s3_idx
              (mword_of_int SH_WHITESPACE)
              (ui_sh_394 pt M Hltext Htext)
              ltac:(vm_compute; discriminate) Hwws with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mH := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int SH_WHITESPACE : mword 64)]> mG).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x394 : mword 64) 4
                      = mword_of_int 0x398)) in "Hpc".
    assert (HpresH : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              mH !!! Regidx r = mF !!! Regidx r).
    { intros r Hr.
      exact (eq_trans (upd_ne mG (Regidx s3_idx) (Regidx r) _ Hr)
               (upd_ne mF (Regidx s3_idx) (Regidx r) _ Hr)). }
    assert (Hs3H : mH !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64))
      by exact (upd_eq mG (Regidx s3_idx) _).
    (* ---- 0x398..0x3ae  the second whitespace scan ---- *)
    iApply (wp_sh_wsskip CID2 0x398 (mword_of_int 1760) s2_idx
              M mH sp0 s0 bs p
              Hlay Hok0 ltac:(unfold sh_frame_ok; lia) Hs0p Hbufhi Hp
              (fun Mx Hx => ui_sh_398 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_39c pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_3a0 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_3a2 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_3a6 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_3a8 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_3aa pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_3ae pt Mx Hltext Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hsstrchr; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hsstrchr; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite (HpresH s2_idx ltac:(vm_compute; discriminate));
                    exact Hs2F)
              ltac:(rewrite (HpresH s1_idx ltac:(vm_compute; discriminate));
                    exact Hs1F)
              ltac:(rewrite (HpresH s2_idx ltac:(vm_compute; discriminate));
                    exact Hs2F)
              Hs3H
              ltac:(rewrite (HpresH sp_idx ltac:(vm_compute; discriminate));
                    exact HspF)
              with "Hcg Hpc").
    iIntros (CID3 mI MI) "%Hs1I %HpresI %HonlyI Hcg Hpc".
    (* ---- 0x3b0..0x3c8  the store-back and the epilogue ---- *)
    assert (HokI : lex_ok MI sp0 s0 bs)
      by exact (lex_ok_below M MI sp0 s0 bs (uint sp0 - 80) 16 HonlyI
                  ltac:(lia) ltac:(lia) Hok0).
    pose proof HokI as HokI'.
    destruct HokI' as (HimgI & HtabI & HbufI & HrdI & HstI).
    destruct (uv_stack_split pt MI sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) HstI) as (HstI64 & _).
    assert (HwrI : uv_wr pt MI psaddr 8)
      by exact (uv_wr_dom pt M MI psaddr 8 (proj1 HonlyI) Hwr).
    assert (HslotsI : gt_slots MI m sp0)
      by (apply (gt_slots_eq M MI m sp0);
          [ intros k Hk; apply (proj2 HonlyI); lia | exact Hslots ]).
    assert (HpresI' : gt_pres mI m).
    { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6.
      rewrite (HpresI r Hr N1). rewrite (HpresH r N3).
      exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5 N6). }
    assert (Hs2I : mI !!! Regidx s2_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (HpresI s2_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresH s2_idx ltac:(vm_compute; discriminate)). exact Hs2F. }
    assert (Hs4I : mI !!! Regidx s4_idx = (mword_of_int psaddr : mword 64)).
    { rewrite (HpresI s4_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresH s4_idx ltac:(vm_compute; discriminate)). exact Hs4F. }
    assert (Hs5I : mI !!! Regidx s5_idx = (mword_of_int ret : mword 64)).
    { rewrite (HpresI s5_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresH s5_idx ltac:(vm_compute; discriminate)). exact Hs5F. }
    assert (HspI : mI !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (HpresI sp_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresH sp_idx ltac:(vm_compute; discriminate)). exact HspF. }
    iApply (wp_sh_gt_tail3b0 CID3 MI mI m sp0 psaddr
              (s0 + Z.of_nat (p + sh_skipws (drop p bs))) ret
              Hltext (sh_img_text MI HimgI) HstI64 ltac:(lia) Hret2 Hspm
              HwrI Hpsal Hpshi Hpshi2 HspI Hs1I Hs4I Hs5I HslotsI HpresI'
              with "Hcg Hpc [Hcont]").
    iIntros (CID4 m' M') "%Hcs %Ha0' %Hcell' %Honly' Hcg Hpc".
    iApply ("Hcont" $! CID4 m' M' with "[] [] [] [] Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
    - iPureIntro. exact Hcell'.
    - iPureIntro.
      apply (uM_only_in_trans M MI M').
      + apply (uM_only_in_of_only M MI (uint sp0 - 80) 80).
        * exact (uM_only_widen M MI (uint sp0 - 80) 16 (uint sp0 - 80) 80
                   HonlyI ltac:(lia) ltac:(lia)).
        * apply elem_of_list_further. apply elem_of_list_here.
      + apply (uM_only_in_of_only MI M' psaddr 8).
        * exact Honly'.
        * apply elem_of_list_here.
  Qed.

  (* ---- the [*eq = s] store at 0x38c, then the above ------------------ *)
  Local Lemma wp_sh_gt_tail38c (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64)
      (psaddr eqaddr s0 : Z) (bs : list (bv 8)) (p : nat) (ret : Z) :
    sh_layout pt hbase hlen ->
    lex_ok M sp0 s0 bs ->
    sh_frame_ok hbase hlen sp0 80 ->
    0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
    (p <= length bs)%nat ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    uv_wr pt M psaddr 8 -> psaddr mod 8 = 0 ->
    uint sp0 <= psaddr -> psaddr + 8 <= 2 ^ 38 ->
    uv_wr pt M eqaddr 8 -> eqaddr mod 8 = 0 ->
    uint sp0 <= eqaddr -> eqaddr + 8 <= 2 ^ 38 ->
    (eqaddr + 8 <= psaddr \/ psaddr + 8 <= eqaddr) ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat p) : mword 64) ->
    mF !!! Regidx s2_idx
      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    mF !!! Regidx s4_idx = (mword_of_int psaddr : mword 64) ->
    mF !!! Regidx s5_idx = (mword_of_int ret : mword 64) ->
    mF !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64) ->
    gt_slots M m sp0 -> gt_pres mF m ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x38c) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int ret : mword 64)⌝ -∗
       ⌜uM_bytes M' eqaddr 8 (mword_of_int (s0 + Z.of_nat p) : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (p + sh_skipws (drop p bs)))
           : mword 64)⌝ -∗
       ⌜uM_only_in M M' [(psaddr, 8); (eqaddr, 8); (uint sp0 - 80, 80)]⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hok Hfr Hs0p Hbufhi Hp Hret2 Hspm Hwr Hpsal Hpshi Hpshi2
           Hewr Heqal Heqhi Heqhi2 Hdis HspF Hs1F Hs2F Hs4F Hs5F Hs6F
           Hslots Hpres.
    unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (uwr_lo _ _ _ _ Hewr) as Heqlo.
    change (2 ^ 38) with 274877906944 in Heqhi2.
    change (2 ^ 38) with 274877906944 in Hpshi2.
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x38c  sd s1,0(s6) ---- *)
    destruct (uv_slot8_facts eqaddr (mword_of_int eqaddr) ltac:(lia) Heqal
                ltac:(lia) eq_refl) as (Hueq & Hcaneq & Hpgeq & Haleq).
    assert (Hva : (mword_of_int eqaddr : mword 64)
                  = add_vec (mF !!! Regidx s6_idx)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hs6F.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uwr_leaf _ _ _ _ Hewr 0 ltac:(lia)) as (wst & Hlst & Hokst).
    rewrite Z.add_0_r in Hlst.
    iApply (wp_uv_sd C pt Psh M mF (mword_of_int 0x38c)
              (mword_of_int 0 : mword 12) s6_idx s1_idx
              wst (mword_of_int eqaddr) (mword_of_int (s0 + Z.of_nat p))
              (ui_sh_38c pt M Hltext Htext)
              Hva (eq_sym Hs1F) Hlst Hokst Hcaneq Hpgeq Haleq
              ltac:(rewrite Hueq; intros j Hj;
                    exact (uwr_bytes _ _ _ _ Hewr (Z.of_nat j) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Hueq) in "Hcg".
    set (Me := uM_store8 M eqaddr (mword_of_int (s0 + Z.of_nat p) : mword 64)).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x38c : mword 64) 4
                      = mword_of_int 0x390)) in "Hpc".
    assert (HonlyE : uM_only M Me eqaddr 8).
    { split.
      - intros k Hk. exact (uM_store8_is_Some M eqaddr _ k Hk).
      - intros k Hk. exact (um_st8_ne M eqaddr _ k Hk). }
    assert (HcellE : uM_bytes Me eqaddr 8
                       (mword_of_int (s0 + Z.of_nat p) : mword 64))
      by exact (uM_store8_bytes M eqaddr _).
    assert (HokE : lex_ok Me sp0 s0 bs)
      by exact (lex_ok_below M Me sp0 s0 bs eqaddr 8 HonlyE
                  ltac:(lia) ltac:(lia) Hok0).
    assert (HwrE : uv_wr pt Me psaddr 8)
      by exact (uv_wr_dom pt M Me psaddr 8 (proj1 HonlyE) Hwr).
    assert (HslotsE : gt_slots Me m sp0)
      by (apply (gt_slots_eq M Me m sp0);
          [ intros k Hk; unfold Me; apply um_st8_ne; lia | exact Hslots ]).
    iApply (wp_sh_gt_tail390 CID2 Me mF m sp0 psaddr s0 bs p ret
              Hlay HokE ltac:(unfold sh_frame_ok; lia) Hs0p Hbufhi Hp
              Hret2 Hspm HwrE Hpsal Hpshi
              ltac:(change (2 ^ 38) with 274877906944; lia)
              HspF Hs1F Hs2F Hs4F Hs5F HslotsE Hpres
              with "Hcg Hpc [Hcont]").
    iIntros (CID3 m' M') "%Hcs %Ha0' %Hcell' %Honly' Hcg Hpc".
    iApply ("Hcont" $! CID3 m' M' with "[] [] [] [] [] Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
    - iPureIntro. intros j Hj.
      rewrite (proj2 Honly' (eqaddr + Z.of_nat j)
                 ltac:(intros (w & Hw & Hin);
                       apply elem_of_cons in Hw as [-> | Hw];
                       [ simpl in Hin; lia | ];
                       apply elem_of_list_singleton in Hw; subst w;
                       simpl in Hin; lia)).
      exact (HcellE j Hj).
    - iPureIntro. exact Hcell'.
    - iPureIntro.
      apply (uM_only_in_trans M Me M').
      + apply (uM_only_in_of_only M Me eqaddr 8); [ exact HonlyE | ].
        apply elem_of_list_further. apply elem_of_list_here.
      + apply (uM_only_in_weaken Me M' [(psaddr, 8); (uint sp0 - 80, 80)]);
          [ exact Honly' | ].
        intros x Hx. apply elem_of_cons in Hx as [-> | Hx].
        * apply elem_of_list_here.
        * apply elem_of_list_singleton in Hx. subst x.
          apply elem_of_list_further. apply elem_of_list_further.
          apply elem_of_list_here.
  Qed.

  (* ---- the tail from 0x388: [if (eq) *eq = s], then the above --------- *)
  Local Lemma wp_sh_gt_tail388 (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64)
      (psaddr eqaddr s0 : Z) (bs : list (bv 8)) (p : nat) (ret : Z) :
    sh_layout pt hbase hlen ->
    lex_ok M sp0 s0 bs ->
    sh_frame_ok hbase hlen sp0 80 ->
    0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
    (p <= length bs)%nat ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    uv_wr pt M psaddr 8 -> psaddr mod 8 = 0 ->
    uint sp0 <= psaddr -> psaddr + 8 <= 2 ^ 38 ->
    (eqaddr = 0 \/ (uv_wr pt M eqaddr 8 /\ eqaddr mod 8 = 0 /\
                    uint sp0 <= eqaddr /\ eqaddr + 8 <= 2 ^ 38)) ->
    (eqaddr = 0 \/ eqaddr + 8 <= psaddr \/ psaddr + 8 <= eqaddr) ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat p) : mword 64) ->
    mF !!! Regidx s2_idx
      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    mF !!! Regidx s4_idx = (mword_of_int psaddr : mword 64) ->
    mF !!! Regidx s5_idx = (mword_of_int ret : mword 64) ->
    mF !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64) ->
    gt_slots M m sp0 -> gt_pres mF m ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x388) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int ret : mword 64)⌝ -∗
       ⌜eqaddr <> 0 ->
          uM_bytes M' eqaddr 8 (mword_of_int (s0 + Z.of_nat p) : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (p + sh_skipws (drop p bs)))
           : mword 64)⌝ -∗
       ⌜uM_only_in M M' [(psaddr, 8); (eqaddr, 8); (uint sp0 - 80, 80)]⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hok Hfr Hs0p Hbufhi Hp Hret2 Hspm Hwr Hpsal Hpshi Hpshi2
           Heqw Hdis2 HspF Hs1F Hs2F Hs4F Hs5F Hs6F Hslots Hpres.
    pose proof Hfr as Hfr0. unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    iIntros "Hcg Hpc Hcont".
    destruct (decide (eqaddr = 0)) as [Heq0 | Heqnz].
    - (* eq == NULL: the branch is taken, nothing is written ---- *)
      assert (Htk : true = uv_btaken BEQ (mF !!! Regidx s6_idx)
                             zero_reg).
      { cbn [uv_btaken]. rewrite Hs6F Heq0.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uv_btype0 C pt Psh M mF (mword_of_int 0x388)
                (mword_of_int 8 : mword 13) s6_idx BEQ
                true (mword_of_int 0x390)
                (ui_sh_388 pt M Hltext Htext) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID1) "Hcg Hpc".
      iApply (wp_sh_gt_tail390 CID1 M mF m sp0 psaddr s0 bs p ret
                Hlay Hok0 Hfr0 Hs0p Hbufhi Hp
                Hret2 Hspm Hwr Hpsal Hpshi Hpshi2
                HspF Hs1F Hs2F Hs4F Hs5F Hslots Hpres
                with "Hcg Hpc [Hcont]").
      iIntros (CID2 m' M') "%Hcs %Ha0' %Hcell' %Honly' Hcg Hpc".
      iApply ("Hcont" $! CID2 m' M' with "[] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0'.
      + iPureIntro. intro Hc'. exfalso. exact (Hc' Heq0).
      + iPureIntro. exact Hcell'.
      + iPureIntro.
        apply (uM_only_in_weaken M M' [(psaddr, 8); (uint sp0 - 80, 80)]);
          [ exact Honly' | ].
        intros x Hx. apply elem_of_cons in Hx as [-> | Hx].
        * apply elem_of_list_here.
        * apply elem_of_list_singleton in Hx. subst x.
          apply elem_of_list_further. apply elem_of_list_further.
          apply elem_of_list_here.
    - (* eq != NULL: fall through to the store ---- *)
      destruct Heqw as [Hc0 | (Hewr & Heqal & Heqhi & Heqhi2)];
        [ exfalso; exact (Heqnz Hc0) | ].
      pose proof (uwr_lo _ _ _ _ Hewr) as Heqlo.
      pose proof Heqhi2 as Heqhi2'.
      change (2 ^ 38) with 274877906944 in Heqhi2'.
      assert (Hdis : eqaddr + 8 <= psaddr \/ psaddr + 8 <= eqaddr)
        by (destruct Hdis2 as [Hc0 | Hd];
            [ exfalso; exact (Heqnz Hc0) | exact Hd ]).
      assert (Htk : false = uv_btaken BEQ (mF !!! Regidx s6_idx)
                              zero_reg).
      { cbn [uv_btaken]. rewrite Hs6F.
        rewrite (moi_eq_zero eqaddr ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact Heqnz. }
      iApply (wp_uv_btype0 C pt Psh M mF (mword_of_int 0x388)
                (mword_of_int 8 : mword 13) s6_idx BEQ
                false (mword_of_int 0x390)
                (ui_sh_388 pt M Hltext Htext) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID1) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x390 : mword 64)
                         else add_vec_int (mword_of_int 0x388 : mword 64) 4)
                        = mword_of_int 0x38c)) in "Hpc".
      iApply (wp_sh_gt_tail38c CID1 M mF m sp0 psaddr eqaddr s0 bs p ret
                Hlay Hok0 Hfr0 Hs0p Hbufhi Hp Hret2 Hspm
                Hwr Hpsal Hpshi Hpshi2 Hewr Heqal Heqhi Heqhi2 Hdis
                HspF Hs1F Hs2F Hs4F Hs5F Hs6F Hslots Hpres
                with "Hcg Hpc [Hcont]").
      iIntros (CID2 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
      iApply ("Hcont" $! CID2 m' M' with "[] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0'.
      + iPureIntro. intros _. exact Hceq.
      + iPureIntro. exact Hcell'.
      + iPureIntro. exact Honly'.
  Qed.

  (* ---- THE WORD SCAN, 0x400..0x41a.                                     *)
  (*   400  lbu a1,0(s1) ; 404 c.mv a0,s3 ; 406 jal strchr(whitespace)     *)
  (*   40a  c.bnez a0,438   -- a whitespace byte ends the token            *)
  (*   40c  lbu a1,0(s1) ; 410 c.mv a0,s5 ; 412 jal strchr(symbols)        *)
  (*   416  c.bnez a0,432   -- UNREACHABLE under [sh_no_symbols]           *)
  (*   418  c.addi s1,s1,1 ; 41a bne s2,s1,400                             *)
  (*   41e  -- the buffer ran out                                          *)
  (* The two exits are told apart by [atend], which is INVARIANT along the *)
  (* loop because [i + sh_toklen (drop i bs)] is.                          *)
  Local Lemma wp_sh_wordloop (nn : nat) :
    forall (CIDp : CpuId) (M : gmap Z (bv 8)) (mE : regfile) (sp0 : mword 64)
      (s0 : Z) (bs : list (bv 8)) (i : nat) (bi : bv 8) (atend : bool),
      (length bs - i < nn)%nat ->
      sh_layout pt hbase hlen ->
      lex_ok M sp0 s0 bs ->
      sh_no_symbols bs ->
      sh_frame_ok hbase hlen sp0 80 ->
      0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
      (i < length bs)%nat -> bs !! i = Some bi ->
      atend = bool_decide ((i + sh_toklen (drop i bs))%nat = length bs) ->
      mE !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat i) : mword 64) ->
      mE !!! Regidx s2_idx
        = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
      mE !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64) ->
      mE !!! Regidx s5_idx = (mword_of_int SH_SYMBOLS : mword 64) ->
      mE !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh M mE -∗
      pc_is (CID := CIDp) (mword_of_int 0x400) -∗
      (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
         ⌜m' !!! Regidx s1_idx
            = (mword_of_int (s0 + Z.of_nat (i + sh_toklen (drop i bs)))
               : mword 64)⌝ -∗
         ⌜forall r : mword 5, ucallee_saved_idx r = true ->
            Regidx r <> Regidx s1_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         ⌜uM_only M M' (uint sp0 - 80) 16⌝ -∗
         uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
         pc_is (CID := CID)
           (if atend then mword_of_int 0x41e else mword_of_int 0x438) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction nn as [ | nn IH ];
      intros CIDp M mE sp0 s0 bs i bi atend Hmeas Hlay Hok Hnosym Hfr Hs0p
             Hbufhi Hi Hbi Hatend Hs1 Hs2 Hs3 Hs5 Hsp.
    { exfalso. lia. }
    unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & Hsstrchr & _).
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    destruct (spA_facts M sp0 Hst) as (HstA & HuA).
    pose proof Hbuf as Hbuf0.
    destruct Hbuf as ((Hbody & Hnul) & Hnzb).
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    assert (Hdrop : drop i bs = bi :: drop (S i) bs) by (apply drop_S; exact Hbi).
    assert (Hsymb : sh_is_sym bi = false) by exact (Hnosym i bi Hbi).
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x400  lbu a1,0(s1) ---- *)
    assert (Hva : (mword_of_int (s0 + Z.of_nat i) : mword 64)
                  = add_vec (mE !!! Regidx s1_idx)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hs1.
      assert (Hc0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc0 moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M s0 (Z.of_nat (length bs) + 1)
                (s0 + Z.of_nat i) Hrd ltac:(lia)) as (wl & Hll & Hokl).
    assert (Huva : uint (mword_of_int (s0 + Z.of_nat i) : mword 64)
                   = s0 + Z.of_nat i) by (apply uint_moi; unfold Z64; lia).
    assert (Hcanon : uva_canon (mword_of_int (s0 + Z.of_nat i) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    iApply (wp_uv_lbu C pt Psh M mE (mword_of_int 0x400)
              (mword_of_int 0 : mword 12) s1_idx a1_idx
              wl (mword_of_int (s0 + Z.of_nat i))
              (mword_of_int (bv_unsigned bi)) bi
              (ui_sh_400 pt M Hltext Htext)
              ltac:(vm_compute; discriminate) Hva Hll Hokl Hcanon
              ltac:(rewrite Huva; exact (Hbody i bi Hbi))
              ltac:(symmetry; apply zext8_moi)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (bv_unsigned bi) : mword 64)]> mE).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x400 : mword 64) 4
                      = mword_of_int 0x404)) in "Hpc".
    (* ---- 0x404  c.mv a0,s3 ---- *)
    assert (Hs3_1 : m1 !!! Regidx s3_idx = (mword_of_int SH_WHITESPACE : mword 64))
      by exact (eq_trans (upd_ne mE (Regidx a1_idx) (Regidx s3_idx) _
                            ltac:(vm_compute; discriminate)) Hs3).
    iApply (wp_uv_cmv C pt Psh M m1 (mword_of_int 0x404)
              a0_idx s3_idx (mword_of_int SH_WHITESPACE)
              (ui_sh_404 pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_1; symmetry; apply moi_add_zero_l)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int SH_WHITESPACE : mword 64)]> m1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x404 : mword 64) 2
                      = mword_of_int 0x406)) in "Hpc".
    (* ---- 0x406  jal ra,strchr ---- *)
    iApply (wp_uv_jal C pt Psh M m2 (mword_of_int 0x406)
              (mword_of_int 1660 : mword 21) ra_idx
              (mword_of_int ShSyms.strchr) (mword_of_int 0x40a)
              (ui_sh_406 pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsstrchr; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hsstrchr; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x40a : mword 64)]> m2).
    assert (Hpres3 : forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx a0_idx ->
              Regidx r <> Regidx a1_idx -> m3 !!! Regidx r = mE !!! Regidx r).
    { intros r H1 H2 H3.
      exact (eq_trans (upd_ne m2 (Regidx ra_idx) (Regidx r) _ H1)
               (eq_trans (upd_ne m1 (Regidx a0_idx) (Regidx r) _ H2)
                  (upd_ne mE (Regidx a1_idx) (Regidx r) _ H3))). }
    assert (Hsp3 : m3 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hpres3 sp_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = (mword_of_int SH_WHITESPACE : mword 64))
      by exact (eq_trans (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate))
                 (upd_eq m1 (Regidx a0_idx) _)).
    assert (Ha1_3 : m3 !!! Regidx a1_idx
                    = (mword_of_int (bv_unsigned bi) : mword 64))
      by exact (eq_trans (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                            ltac:(vm_compute; discriminate))
                 (eq_trans (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
                              ltac:(vm_compute; discriminate))
                    (upd_eq mE (Regidx a1_idx) _))).
    assert (Hra3 : m3 !!! Regidx ra_idx = (mword_of_int 0x40a : mword 64))
      by exact (upd_eq m2 (Regidx ra_idx) _).
    assert (HfrA : sh_frame_ok hbase hlen
                     (mword_of_int (uint sp0 - 64) : mword 64) 16)
      by (unfold sh_frame_ok; rewrite HuA; lia).
    iApply (wp_sh_strchr C pt gin gbrk hbase hlen Q CID3 M m3
              (mword_of_int (uint sp0 - 64)) SH_WHITESPACE sh_ws_bytes bi
              Hlay Htext Hsp3 HstA Ha0_3 Ha1_3 sh_ws_nz (proj1 Htab)
              (ws_table_rd M Hlay Htab)
              ltac:(right; rewrite HuA sh_ws_len;
                    unfold SH_WHITESPACE, SH_DATA_PG; lia)
              HfrA ltac:(rewrite Hra3; vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros (CID4 m4 M4) "%Hcs4 %Ha0_4 %Honly4 Hcg Hpc".
    iEval (rewrite Hra3) in "Hpc".
    rewrite HuA in Honly4.
    assert (HonlyA : uM_only M M4 (uint sp0 - 80) 16).
    { destruct Honly4 as (D & E). split; [ exact D | ].
      intros k Hk. apply E. lia. }
    assert (Hok4 : lex_ok M4 sp0 s0 bs)
      by exact (lex_ok_below M M4 sp0 s0 bs (uint sp0 - 80) 16 HonlyA
                  ltac:(lia) ltac:(lia) Hok0).
    pose proof Hok4 as Hok4'.
    destruct Hok4' as (Himg4 & Htab4 & Hbuf4 & Hrd4 & Hst4).
    pose proof (sh_img_text M4 Himg4) as Htext4.
    assert (Hpres4 : forall r : mword 5, ucallee_saved_idx r = true ->
              m4 !!! Regidx r = mE !!! Regidx r).
    { intros r Hr. rewrite (Hcs4 r Hr).
      exact (Hpres3 r
               ltac:(intro E; injection E as E'; subst r;
                     vm_compute in Hr; discriminate)
               ltac:(intro E; injection E as E'; subst r;
                     vm_compute in Hr; discriminate)
               ltac:(intro E; injection E as E'; subst r;
                     vm_compute in Hr; discriminate)). }
    assert (Hs1_4 : m4 !!! Regidx s1_idx
                    = (mword_of_int (s0 + Z.of_nat i) : mword 64))
      by (rewrite (Hpres4 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hs2_4 : m4 !!! Regidx s2_idx
                    = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hpres4 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_4 : m4 !!! Regidx s3_idx
                    = (mword_of_int SH_WHITESPACE : mword 64))
      by (rewrite (Hpres4 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (Hs5_4 : m4 !!! Regidx s5_idx = (mword_of_int SH_SYMBOLS : mword 64))
      by (rewrite (Hpres4 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
    assert (Hsp4 : m4 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hpres4 sp_idx ltac:(vm_compute; reflexivity)); exact Hsp).
    (* ---- 0x40a  c.bnez a0,0x438 ---- *)
    destruct (bool_dec (sh_is_ws bi) true) as [Hws | Hnws].
    - (* A WHITESPACE BYTE ends the token here ---- *)
      destruct (sh_ws_chr_ws bi Hws) as (kk & Hkk & Hkklt).
      rewrite Hkk in Ha0_4.
      assert (Htk : true = neq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (moi_neq_zero (SH_WHITESPACE + Z.of_nat kk)
                         ltac:(unfold SH_WHITESPACE, SH_DATA_PG, Z64; lia)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq.
        unfold SH_WHITESPACE, SH_DATA_PG. lia. }
      assert (Htok0 : sh_toklen (drop i bs) = 0%nat)
        by (rewrite Hdrop; apply sh_toklen_cons_stop; rewrite Hws; reflexivity).
      assert (Hab : atend = false)
        by (rewrite Hatend; apply bool_decide_eq_false_2; rewrite Htok0; lia).
      clear Hatend. subst atend.
      iApply (wp_uv_cbnez C pt Psh M4 m4 (mword_of_int 0x40a)
                (mword_of_int 23 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x438)
                (ui_sh_40a pt M4 Hltext Htext4)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      iApply ("Hcont" $! CID5 m4 M4 with "[] [] [] Hcg Hpc").
      + iPureIntro. rewrite Hs1_4 Htok0. f_equal; lia.
      + iPureIntro. intros r Hr _. exact (Hpres4 r Hr).
      + iPureIntro. exact HonlyA.
    - (* A TOKEN BYTE: check the symbols table, then advance ---- *)
      assert (Hnws' : sh_is_ws bi = false)
        by (destruct (sh_is_ws bi); [ exfalso; exact (Hnws eq_refl) | reflexivity ]).
      rewrite (sh_ws_chr_nws bi Hnws') in Ha0_4.
      assert (Htk : false = neq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uv_cbnez C pt Psh M4 m4 (mword_of_int 0x40a)
                (mword_of_int 23 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x438)
                (ui_sh_40a pt M4 Hltext Htext4)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x438 : mword 64)
                         else add_vec_int (mword_of_int 0x40a : mword 64) 2)
                        = mword_of_int 0x40c)) in "Hpc".
      (* ---- 0x40c  lbu a1,0(s1) ---- *)
      destruct Hbuf4 as ((Hbody4 & Hnul4) & _).
      assert (Hva4 : (mword_of_int (s0 + Z.of_nat i) : mword 64)
                     = add_vec (m4 !!! Regidx s1_idx)
                         (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite Hs1_4.
        assert (Hc0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                      = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc0 moi_add. f_equal; lia. }
      destruct (uv_rd_leaf_at pt M4 s0 (Z.of_nat (length bs) + 1)
                  (s0 + Z.of_nat i) Hrd4 ltac:(lia)) as (wl4 & Hll4 & Hokl4).
      iApply (wp_uv_lbu C pt Psh M4 m4 (mword_of_int 0x40c)
                (mword_of_int 0 : mword 12) s1_idx a1_idx
                wl4 (mword_of_int (s0 + Z.of_nat i))
                (mword_of_int (bv_unsigned bi)) bi
                (ui_sh_40c pt M4 Hltext Htext4)
                ltac:(vm_compute; discriminate) Hva4 Hll4 Hokl4 Hcanon
                ltac:(rewrite Huva; exact (Hbody4 i bi Hbi))
                ltac:(symmetry; apply zext8_moi)
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      set (m5 := <[Regidx a1_idx
                   := regval_into_reg
                        (mword_of_int (bv_unsigned bi) : mword 64)]> m4).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x40c : mword 64) 4
                        = mword_of_int 0x410)) in "Hpc".
      (* ---- 0x410  c.mv a0,s5 ---- *)
      assert (Hs5_5 : m5 !!! Regidx s5_idx = (mword_of_int SH_SYMBOLS : mword 64))
        by exact (eq_trans (upd_ne m4 (Regidx a1_idx) (Regidx s5_idx) _
                              ltac:(vm_compute; discriminate)) Hs5_4).
      iApply (wp_uv_cmv C pt Psh M4 m5 (mword_of_int 0x410)
                a0_idx s5_idx (mword_of_int SH_SYMBOLS)
                (ui_sh_410 pt M4 Hltext Htext4)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs5_5; symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID7) "Hcg Hpc".
      set (m6 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int SH_SYMBOLS : mword 64)]> m5).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x410 : mword 64) 2
                        = mword_of_int 0x412)) in "Hpc".
      (* ---- 0x412  jal ra,strchr ---- *)
      iApply (wp_uv_jal C pt Psh M4 m6 (mword_of_int 0x412)
                (mword_of_int 1648 : mword 21) ra_idx
                (mword_of_int ShSyms.strchr) (mword_of_int 0x416)
                (ui_sh_412 pt M4 Hltext Htext4) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hsstrchr; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hsstrchr; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID8) "Hcg Hpc".
      set (m7 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x416 : mword 64)]> m6).
      assert (Hpres7 : forall r : mword 5,
                Regidx r <> Regidx ra_idx -> Regidx r <> Regidx a0_idx ->
                Regidx r <> Regidx a1_idx -> m7 !!! Regidx r = m4 !!! Regidx r).
      { intros r H1 H2 H3.
        exact (eq_trans (upd_ne m6 (Regidx ra_idx) (Regidx r) _ H1)
                 (eq_trans (upd_ne m5 (Regidx a0_idx) (Regidx r) _ H2)
                    (upd_ne m4 (Regidx a1_idx) (Regidx r) _ H3))). }
      assert (Hsp7 : m7 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64))
        by (rewrite (Hpres7 sp_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hsp4).
      assert (Ha0_7 : m7 !!! Regidx a0_idx = (mword_of_int SH_SYMBOLS : mword 64))
        by exact (eq_trans (upd_ne m6 (Regidx ra_idx) (Regidx a0_idx) _
                              ltac:(vm_compute; discriminate))
                   (upd_eq m5 (Regidx a0_idx) _)).
      assert (Ha1_7 : m7 !!! Regidx a1_idx
                      = (mword_of_int (bv_unsigned bi) : mword 64))
        by exact (eq_trans (upd_ne m6 (Regidx ra_idx) (Regidx a1_idx) _
                              ltac:(vm_compute; discriminate))
                   (eq_trans (upd_ne m5 (Regidx a0_idx) (Regidx a1_idx) _
                                ltac:(vm_compute; discriminate))
                      (upd_eq m4 (Regidx a1_idx) _))).
      assert (Hra7 : m7 !!! Regidx ra_idx = (mword_of_int 0x416 : mword 64))
        by exact (upd_eq m6 (Regidx ra_idx) _).
      destruct (spA_facts M4 sp0 Hst4) as (HstA4 & HuA4).
      iApply (wp_sh_strchr C pt gin gbrk hbase hlen Q CID8 M4 m7
                (mword_of_int (uint sp0 - 64)) SH_SYMBOLS sh_sym_bytes bi
                Hlay Htext4 Hsp7 HstA4 Ha0_7 Ha1_7 sh_sym_nz (proj2 Htab4)
                (sym_table_rd M4 Hlay Htab4)
                ltac:(right; rewrite HuA4 sh_sym_len;
                      unfold SH_SYMBOLS, SH_DATA_PG; lia)
                ltac:(unfold sh_frame_ok; rewrite HuA4; lia)
                ltac:(rewrite Hra7; vm_compute; reflexivity)
                with "Hcg Hpc [Hcont]").
      iIntros (CID9 m8 M8) "%Hcs8 %Ha0_8 %Honly8 Hcg Hpc".
      iEval (rewrite Hra7) in "Hpc".
      rewrite HuA4 in Honly8.
      assert (HonlyB : uM_only M4 M8 (uint sp0 - 80) 16).
      { destruct Honly8 as (D & E). split; [ exact D | ].
        intros k Hk. apply E. lia. }
      assert (Hok8 : lex_ok M8 sp0 s0 bs)
        by exact (lex_ok_below M4 M8 sp0 s0 bs (uint sp0 - 80) 16 HonlyB
                    ltac:(lia) ltac:(lia) Hok4).
      pose proof Hok8 as Hok8'.
      destruct Hok8' as (Himg8 & Htab8 & Hbuf8 & Hrd8 & Hst8).
      pose proof (sh_img_text M8 Himg8) as Htext8.
      assert (HonlyAB : uM_only M M8 (uint sp0 - 80) 16)
        by exact (uM_only_trans M M4 M8 (uint sp0 - 80) 16 HonlyA HonlyB).
      assert (Hpres8 : forall r : mword 5, ucallee_saved_idx r = true ->
                m8 !!! Regidx r = mE !!! Regidx r).
      { intros r Hr. rewrite (Hcs8 r Hr).
        rewrite (Hpres7 r
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate)
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate)
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate)).
        exact (Hpres4 r Hr). }
      (* ---- 0x416  c.bnez a0,0x432 -- never taken ---- *)
      rewrite (sh_sym_chr_nsym bi Hsymb) in Ha0_8.
      assert (Htk2 : false = neq_vec (m8 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_8 (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uv_cbnez C pt Psh M8 m8 (mword_of_int 0x416)
                (mword_of_int 14 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x432)
                (ui_sh_416 pt M8 Hltext Htext8)
                ltac:(vm_compute; reflexivity) Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID10) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x432 : mword 64)
                         else add_vec_int (mword_of_int 0x416 : mword 64) 2)
                        = mword_of_int 0x418)) in "Hpc".
      (* ---- 0x418  c.addi s1,s1,1 ---- *)
      assert (Hs1_8 : m8 !!! Regidx s1_idx
                      = (mword_of_int (s0 + Z.of_nat i) : mword 64))
        by (rewrite (Hpres8 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
      assert (Hadd : (mword_of_int (s0 + Z.of_nat i + 1) : mword 64)
                     = add_vec (m8 !!! Regidx s1_idx)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 1 : mword 6)))).
      { rewrite Hs1_8.
        assert (Hc1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                       : mword 64) = mword_of_int 1)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc1 moi_add. f_equal; lia. }
      iApply (wp_uv_caddi C pt Psh M8 m8 (mword_of_int 0x418)
                (mword_of_int 1 : mword 6) s1_idx
                (mword_of_int (s0 + Z.of_nat i + 1))
                (ui_sh_418 pt M8 Hltext Htext8)
                ltac:(vm_compute; discriminate) Hadd with "Hcg Hpc").
      iIntros (CID11) "Hcg Hpc".
      set (m9 := <[Regidx s1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat i + 1) : mword 64)]> m8).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x418 : mword 64) 2
                        = mword_of_int 0x41a)) in "Hpc".
      assert (Hs1_9 : m9 !!! Regidx s1_idx
                      = (mword_of_int (s0 + Z.of_nat i + 1) : mword 64))
        by exact (upd_eq m8 (Regidx s1_idx) _).
      assert (Hpres9 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                m9 !!! Regidx r = m8 !!! Regidx r)
        by (intros r Hr; exact (upd_ne m8 (Regidx s1_idx) (Regidx r) _ Hr)).
      assert (Hs2_9 : m9 !!! Regidx s2_idx
                      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
        by (rewrite (Hpres9 s2_idx ltac:(vm_compute; discriminate));
            rewrite (Hpres8 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
      assert (Hs3_9 : m9 !!! Regidx s3_idx
                      = (mword_of_int SH_WHITESPACE : mword 64))
        by (rewrite (Hpres9 s3_idx ltac:(vm_compute; discriminate));
            rewrite (Hpres8 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
      assert (Hs5_9 : m9 !!! Regidx s5_idx = (mword_of_int SH_SYMBOLS : mword 64))
        by (rewrite (Hpres9 s5_idx ltac:(vm_compute; discriminate));
            rewrite (Hpres8 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
      assert (Hsp9 : m9 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64))
        by (rewrite (Hpres9 sp_idx ltac:(vm_compute; discriminate));
            rewrite (Hpres8 sp_idx ltac:(vm_compute; reflexivity)); exact Hsp).
      (* ---- 0x41a  bne s2,s1,0x400 ---- *)
      destruct (decide (S i = length bs)%nat) as [Hend | Hne].
      + (* the buffer ran out: the token ends at es ---- *)
        assert (Htok1 : sh_toklen (drop i bs) = 1%nat).
        { rewrite Hdrop (sh_toklen_cons_in bi (drop (S i) bs)
                           ltac:(rewrite Hnws' Hsymb; reflexivity)).
          assert (Hd : drop (S i) bs = []) by (apply drop_ge; lia).
          rewrite Hd sh_toklen_nil. reflexivity. }
        assert (Hab : atend = true)
          by (rewrite Hatend; apply bool_decide_eq_true_2; rewrite Htok1; lia).
        clear Hatend. subst atend.
        assert (Htk3 : false = uv_btaken BNE (m9 !!! Regidx s2_idx)
                                 (m9 !!! Regidx s1_idx)).
        { cbn [uv_btaken]. rewrite Hs2_9 Hs1_9.
          rewrite (moi_neq_vec (s0 + Z.of_nat (length bs)) (s0 + Z.of_nat i + 1)
                     ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
          symmetry. apply negb_false_iff. apply Z.eqb_eq. lia. }
        iApply (wp_uv_btype C pt Psh M8 m9 (mword_of_int 0x41a)
                  (mword_of_int 8166 : mword 13) s1_idx s2_idx BNE
                  false (mword_of_int 0x400)
                  (ui_sh_41a pt M8 Hltext Htext8) Htk3
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intro Hc'; discriminate Hc')
                  with "Hcg Hpc").
        iIntros (CID12) "Hcg Hpc".
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : (if false then (mword_of_int 0x400 : mword 64)
                           else add_vec_int (mword_of_int 0x41a : mword 64) 4)
                          = mword_of_int 0x41e)) in "Hpc".
        iApply ("Hcont" $! CID12 m9 M8 with "[] [] [] Hcg Hpc").
        * iPureIntro. rewrite Hs1_9 Htok1. f_equal; lia.
        * iPureIntro. intros r Hr Hne1.
          rewrite (Hpres9 r Hne1). exact (Hpres8 r Hr).
        * iPureIntro. exact HonlyAB.
      + (* another byte: take the back edge ---- *)
        assert (Hlt : (S i < length bs)%nat) by lia.
        assert (Htk3 : true = uv_btaken BNE (m9 !!! Regidx s2_idx)
                                (m9 !!! Regidx s1_idx)).
        { cbn [uv_btaken]. rewrite Hs2_9 Hs1_9.
          rewrite (moi_neq_vec (s0 + Z.of_nat (length bs)) (s0 + Z.of_nat i + 1)
                     ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
          symmetry. apply negb_true_iff. apply Z.eqb_neq. lia. }
        iApply (wp_uv_btype C pt Psh M8 m9 (mword_of_int 0x41a)
                  (mword_of_int 8166 : mword 13) s1_idx s2_idx BNE
                  true (mword_of_int 0x400)
                  (ui_sh_41a pt M8 Hltext Htext8) Htk3
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID12) "Hcg Hpc".
        destruct (lookup_lt_is_Some_2 bs (S i) Hlt) as (bn & Hbn).
        assert (Htokstep : sh_toklen (drop i bs)
                           = S (sh_toklen (drop (S i) bs)))
          by (rewrite Hdrop; apply sh_toklen_cons_in;
              rewrite Hnws' Hsymb; reflexivity).
        assert (Hs1_9' : m9 !!! Regidx s1_idx
                         = (mword_of_int (s0 + Z.of_nat (S i)) : mword 64))
          by (rewrite Hs1_9; f_equal; lia).
        assert (Hatend' : atend
                          = bool_decide
                              ((S i + sh_toklen (drop (S i) bs))%nat
                               = length bs)).
        { rewrite Hatend.
          destruct (decide ((i + sh_toklen (drop i bs))%nat = length bs))
            as [He | He].
          - rewrite (bool_decide_eq_true_2 _ He). symmetry.
            apply bool_decide_eq_true_2. lia.
          - rewrite (bool_decide_eq_false_2 _ He). symmetry.
            apply bool_decide_eq_false_2. lia. }
        iApply (IH CID12 M8 m9 sp0 s0 bs (S i) bn atend
                  ltac:(lia) Hlay Hok8 Hnosym ltac:(unfold sh_frame_ok; lia)
                  Hs0p Hbufhi Hlt Hbn Hatend'
                  Hs1_9' Hs2_9 Hs3_9 Hs5_9 Hsp9
                  with "Hcg Hpc").
        iIntros (CID13 m' M') "%Hv' %Hp' %Ho' Hcg Hpc".
        iApply ("Hcont" $! CID13 m' M' with "[] [] [] Hcg Hpc").
        * iPureIntro. rewrite Hv' Htokstep. f_equal; lia.
        * iPureIntro. intros r Hr Hne1.
          rewrite (Hp' r Hr Hne1). rewrite (Hpres9 r Hne1). exact (Hpres8 r Hr).
        * iPureIntro.
          exact (uM_only_trans M M8 M' (uint sp0 - 80) 16 HonlyAB Ho').
  Qed.

  (* ---- THE WORD ARM, 0x3ec onwards: s3 := whitespace, s5 := symbols,   *)
  (*      the scan, [ret := 'a'], and then one of the three tails --------- *)
  Local Lemma wp_sh_gt_word (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64)
      (psaddr eqaddr s0 : Z) (bs : list (bv 8)) (q : nat) (bq : bv 8) :
    sh_layout pt hbase hlen ->
    lex_ok M sp0 s0 bs ->
    sh_no_symbols bs ->
    sh_frame_ok hbase hlen sp0 80 ->
    0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
    (q < length bs)%nat -> bs !! q = Some bq -> sh_is_ws bq = false ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    uv_wr pt M psaddr 8 -> psaddr mod 8 = 0 ->
    uint sp0 <= psaddr -> psaddr + 8 <= 2 ^ 38 ->
    (eqaddr = 0 \/ (uv_wr pt M eqaddr 8 /\ eqaddr mod 8 = 0 /\
                    uint sp0 <= eqaddr /\ eqaddr + 8 <= 2 ^ 38)) ->
    (eqaddr = 0 \/ eqaddr + 8 <= psaddr \/ psaddr + 8 <= eqaddr) ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat q) : mword 64) ->
    mF !!! Regidx s2_idx
      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    mF !!! Regidx s4_idx = (mword_of_int psaddr : mword 64) ->
    mF !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64) ->
    gt_slots M m sp0 -> gt_pres mF m ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x3ec) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int 97 : mword 64)⌝ -∗
       ⌜eqaddr <> 0 ->
          uM_bytes M' eqaddr 8
            (mword_of_int (s0 + Z.of_nat (q + sh_toklen (drop q bs)))
             : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int
             (s0 + Z.of_nat (q + sh_toklen (drop q bs)
                             + sh_skipws (drop (q + sh_toklen (drop q bs)) bs)))
           : mword 64)⌝ -∗
       ⌜uM_only_in M M' [(psaddr, 8); (eqaddr, 8); (uint sp0 - 80, 80)]⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hok Hnosym Hfr Hs0p Hbufhi Hq Hbq Hnws Hret2 Hspm
           Hwr Hpsal Hpshi Hpshi2 Heqw Hdis2 HspF Hs1F Hs2F Hs4F Hs6F
           Hslots Hpres.
    pose proof Hfr as Hfr0. unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    (* the token's length, and the fact that it is at least one byte *)
    set (t := sh_toklen (drop q bs)).
    assert (Htle : (q + t <= length bs)%nat).
    { unfold t. pose proof (sh_toklen_le (drop q bs)) as H.
      rewrite length_drop in H. lia. }
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x3ec  auipc s3,0x2 ---- *)
    iApply (wp_uv_auipc C pt Psh M mF (mword_of_int 0x3ec)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x23ec)
              (ui_sh_3ec pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mG := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x23ec : mword 64)]> mF).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                      = mword_of_int 0x3f0)) in "Hpc".
    (* ---- 0x3f0  addi s3,s3,-996 ---- *)
    assert (Hs3G : mG !!! Regidx s3_idx = (mword_of_int 0x23ec : mword 64))
      by exact (upd_eq mF (Regidx s3_idx) _).
    iApply (wp_uv_addi C pt Psh M mG (mword_of_int 0x3f0)
              (mword_of_int 3100 : mword 12) s3_idx s3_idx
              (mword_of_int SH_WHITESPACE)
              (ui_sh_3f0 pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3G;
                    rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                             : (sign_extend' 64 (mword_of_int 3100 : mword 12)
                                : mword 64) = mword_of_int (-996));
                    rewrite moi_add; unfold SH_WHITESPACE, SH_DATA_PG;
                    f_equal; lia)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mH := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int SH_WHITESPACE : mword 64)]> mG).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3f0 : mword 64) 4
                      = mword_of_int 0x3f4)) in "Hpc".
    (* ---- 0x3f4  auipc s5,0x2 ---- *)
    iApply (wp_uv_auipc C pt Psh M mH (mword_of_int 0x3f4)
              (mword_of_int 2 : mword 20) s5_idx (mword_of_int 0x23f4)
              (ui_sh_3f4 pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mI := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 0x23f4 : mword 64)]> mH).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3f4 : mword 64) 4
                      = mword_of_int 0x3f8)) in "Hpc".
    (* ---- 0x3f8  addi s5,s5,-1012 ---- *)
    assert (Hs5I : mI !!! Regidx s5_idx = (mword_of_int 0x23f4 : mword 64))
      by exact (upd_eq mH (Regidx s5_idx) _).
    iApply (wp_uv_addi C pt Psh M mI (mword_of_int 0x3f8)
              (mword_of_int 3084 : mword 12) s5_idx s5_idx
              (mword_of_int SH_SYMBOLS)
              (ui_sh_3f8 pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5I;
                    rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                             : (sign_extend' 64 (mword_of_int 3084 : mword 12)
                                : mword 64) = mword_of_int (-1012));
                    rewrite moi_add; unfold SH_SYMBOLS, SH_DATA_PG;
                    f_equal; lia)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (mJ := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int SH_SYMBOLS : mword 64)]> mI).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x3f8 : mword 64) 4
                      = mword_of_int 0x3fc)) in "Hpc".
    (* the register file entering the scan *)
    assert (HpresJ : forall r : mword 5,
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s5_idx ->
              mJ !!! Regidx r = mF !!! Regidx r).
    { intros r N3 N5.
      exact (eq_trans (upd_ne mI (Regidx s5_idx) (Regidx r) _ N5)
               (eq_trans (upd_ne mH (Regidx s5_idx) (Regidx r) _ N5)
                  (eq_trans (upd_ne mG (Regidx s3_idx) (Regidx r) _ N3)
                     (upd_ne mF (Regidx s3_idx) (Regidx r) _ N3)))). }
    assert (Hs3J : mJ !!! Regidx s3_idx
                   = (mword_of_int SH_WHITESPACE : mword 64)).
    { rewrite (upd_ne mI (Regidx s5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mH (Regidx s5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mG (Regidx s3_idx) _). }
    assert (Hs5J : mJ !!! Regidx s5_idx = (mword_of_int SH_SYMBOLS : mword 64))
      by exact (upd_eq mI (Regidx s5_idx) _).
    assert (Hs1J : mJ !!! Regidx s1_idx
                   = (mword_of_int (s0 + Z.of_nat q) : mword 64))
      by (rewrite (HpresJ s1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs1F).
    assert (Hs2J : mJ !!! Regidx s2_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (HpresJ s2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs2F).
    assert (Hs4J : mJ !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (HpresJ s4_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs4F).
    assert (Hs6J : mJ !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64))
      by (rewrite (HpresJ s6_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs6F).
    assert (HspJ : mJ !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (HpresJ sp_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact HspF).
    (* ---- 0x3fc  bgeu s1,s2,0x43e -- never taken (q < |bs|) ---- *)
    assert (Htk0 : false = uv_btaken BGEU (mJ !!! Regidx s1_idx)
                             (mJ !!! Regidx s2_idx)).
    { cbn [uv_btaken]. rewrite Hs1J Hs2J.
      rewrite (moi_ge_u (s0 + Z.of_nat q) (s0 + Z.of_nat (length bs))
                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uv_btype C pt Psh M mJ (mword_of_int 0x3fc)
              (mword_of_int 66 : mword 13) s2_idx s1_idx BGEU
              false (mword_of_int 0x43e)
              (ui_sh_3fc pt M Hltext Htext) Htk0
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc'; discriminate Hc')
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : (if false then (mword_of_int 0x43e : mword 64)
                       else add_vec_int (mword_of_int 0x3fc : mword 64) 4)
                      = mword_of_int 0x400)) in "Hpc".
    (* ---- 0x400..0x41a  the word scan ---- *)
    iApply (wp_sh_wordloop (S (length bs)) CID5 M mJ sp0 s0 bs q bq
              (bool_decide ((q + t)%nat = length bs))
              ltac:(lia) Hlay Hok0 Hnosym Hfr0 Hs0p Hbufhi Hq Hbq
              eq_refl Hs1J Hs2J Hs3J Hs5J HspJ
              with "Hcg Hpc").
    iIntros (CID6 mK MK) "%Hs1K %HpresK %HonlyK Hcg Hpc".
    assert (HokK : lex_ok MK sp0 s0 bs)
      by exact (lex_ok_below M MK sp0 s0 bs (uint sp0 - 80) 16 HonlyK
                  ltac:(lia) ltac:(lia) Hok0).
    pose proof HokK as HokK'.
    destruct HokK' as (HimgK & HtabK & HbufK & HrdK & HstK).
    pose proof (sh_img_text MK HimgK) as HtextK.
    assert (HwrK : uv_wr pt MK psaddr 8)
      by exact (uv_wr_dom pt M MK psaddr 8 (proj1 HonlyK) Hwr).
    assert (HeqwK : eqaddr = 0 \/ (uv_wr pt MK eqaddr 8 /\ eqaddr mod 8 = 0 /\
                                   uint sp0 <= eqaddr /\ eqaddr + 8 <= 2 ^ 38)).
    { destruct Heqw as [H0 | (Hw & Ha & Hb & Hc)]; [ by left | right ].
      split_and!; try assumption.
      exact (uv_wr_dom pt M MK eqaddr 8 (proj1 HonlyK) Hw). }
    assert (HslotsK : gt_slots MK m sp0)
      by (apply (gt_slots_eq M MK m sp0);
          [ intros k Hk; apply (proj2 HonlyK); lia | exact Hslots ]).
    assert (Hs2K : mK !!! Regidx s2_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (HpresK s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs2J).
    assert (Hs4K : mK !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (HpresK s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4J).
    assert (Hs6K : mK !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64))
      by (rewrite (HpresK s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs6J).
    assert (HspK : mK !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (HpresK sp_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HspJ).
    destruct (decide ((q + t)%nat = length bs)) as [Hend | Hne].
    - (* THE TOKEN RUNS TO [es] ---- *)
      rewrite (bool_decide_eq_true_2 _ Hend).
      (* ---- 0x41e  c.mv s1,s2 ---- *)
      iApply (wp_uv_cmv C pt Psh MK mK (mword_of_int 0x41e)
                s1_idx s2_idx (mword_of_int (s0 + Z.of_nat (length bs)))
                (ui_sh_41e pt MK Hltext HtextK)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2K; symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID7) "Hcg Hpc".
      set (mL := <[Regidx s1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat (length bs))
                         : mword 64)]> mK).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x41e : mword 64) 2
                        = mword_of_int 0x420)) in "Hpc".
      (* ---- 0x420  li s5,97 ---- *)
      iApply (wp_uv_li C pt Psh MK mL (mword_of_int 0x420)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97)
                (ui_sh_420 pt MK Hltext HtextK) ltac:(vm_compute; discriminate)
                ltac:(rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                         : (sign_extend' 64 (mword_of_int 97 : mword 12)
                            : mword 64) = mword_of_int 97);
                      symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID8) "Hcg Hpc".
      set (mN := <[Regidx s5_idx
                   := regval_into_reg (mword_of_int 97 : mword 64)]> mL).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x420 : mword 64) 4
                        = mword_of_int 0x424)) in "Hpc".
      assert (HpresN : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                Regidx r <> Regidx s5_idx -> mN !!! Regidx r = mK !!! Regidx r).
      { intros r N1 N5.
        exact (eq_trans (upd_ne mL (Regidx s5_idx) (Regidx r) _ N5)
                 (upd_ne mK (Regidx s1_idx) (Regidx r) _ N1)). }
      assert (Hs1N : mN !!! Regidx s1_idx
                     = (mword_of_int (s0 + Z.of_nat (q + t)) : mword 64)).
      { rewrite (upd_ne mL (Regidx s5_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        replace (s0 + Z.of_nat (q + t))
          with (s0 + Z.of_nat (length bs)) by lia.
        exact (upd_eq mK (Regidx s1_idx) _). }
      assert (Hs5N : mN !!! Regidx s5_idx = (mword_of_int 97 : mword 64))
        by exact (upd_eq mL (Regidx s5_idx) _).
      assert (Hs2N : mN !!! Regidx s2_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
        by (rewrite (HpresN s2_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs2K).
      assert (Hs4N : mN !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
        by (rewrite (HpresN s4_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs4K).
      assert (Hs6N : mN !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64))
        by (rewrite (HpresN s6_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs6K).
      assert (HspN : mN !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64))
        by (rewrite (HpresN sp_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact HspK).
      assert (HpresN' : gt_pres mN m).
      { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6.
        rewrite (HpresN r N1 N5). rewrite (HpresK r Hr N1).
        rewrite (HpresJ r N3 N5). exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5 N6). }
      assert (Hk2 : sh_skipws (drop (q + t) bs) = 0%nat)
        by (rewrite (ltac:(apply drop_ge; lia) : drop (q + t) bs = []);
            exact sh_skipws_nil).
      (* ---- 0x424  bnez s6,0x38c ---- *)
      destruct (decide (eqaddr = 0)) as [Heq0 | Heqnz].
      + (* eq == NULL: jump straight to [*ps = s] ---- *)
        assert (Htk : false = uv_btaken BNE (mN !!! Regidx s6_idx)
                                zero_reg).
        { cbn [uv_btaken]. rewrite Hs6N Heq0.
          rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
        iApply (wp_uv_btype0 C pt Psh MK mN (mword_of_int 0x424)
                  (mword_of_int 8040 : mword 13) s6_idx BNE false (mword_of_int 0x38c)
                  (ui_sh_424 pt MK Hltext HtextK) Htk
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intro Hc'; discriminate Hc')
                  with "Hcg Hpc").
        iIntros (CID9) "Hcg Hpc".
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : (if false then (mword_of_int 0x38c : mword 64)
                           else add_vec_int (mword_of_int 0x424 : mword 64) 4)
                          = mword_of_int 0x428)) in "Hpc".
        (* ---- 0x428  c.j 0x3b0 ---- *)
        iApply (wp_uv_cj C pt Psh MK mN (mword_of_int 0x428)
                  (mword_of_int 1988 : mword 11) (mword_of_int 0x3b0)
                  (ui_sh_428 pt MK Hltext HtextK)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc").
        iIntros (CID10) "Hcg Hpc".
        destruct (uv_stack_split pt MK sp0 80 64 16 ltac:(lia) ltac:(lia)
                    ltac:(reflexivity) ltac:(lia) HstK) as (HstK64 & _).
        iApply (wp_sh_gt_tail3b0 CID10 MK mN m sp0 psaddr
                  (s0 + Z.of_nat (q + t)) 97
                  Hltext HtextK HstK64 ltac:(lia) Hret2 Hspm
                  HwrK Hpsal Hpshi Hpshi2 HspN Hs1N Hs4N Hs5N HslotsK HpresN'
                  with "Hcg Hpc [Hcont]").
        iIntros (CID11 m' M') "%Hcs %Ha0' %Hcell' %Honly' Hcg Hpc".
        iApply ("Hcont" $! CID11 m' M' with "[] [] [] [] [] Hcg Hpc").
        * iPureIntro. exact Hcs.
        * iPureIntro. exact Ha0'.
        * iPureIntro. intro Hc'. exfalso. exact (Hc' Heq0).
        * iPureIntro.
          apply (uM_bytes_val M' psaddr (mword_of_int (s0 + Z.of_nat (q + t))));
            [ | exact Hcell' ].
          fold t. rewrite Hk2. f_equal. lia.
        * iPureIntro.
          apply (uM_only_in_trans M MK M').
          -- apply (uM_only_in_of_only M MK (uint sp0 - 80) 80).
             ++ exact (uM_only_widen M MK (uint sp0 - 80) 16 (uint sp0 - 80) 80
                         HonlyK ltac:(lia) ltac:(lia)).
             ++ apply elem_of_list_further. apply elem_of_list_further.
                apply elem_of_list_here.
          -- apply (uM_only_in_of_only MK M' psaddr 8); [ exact Honly' | ].
             apply elem_of_list_here.
      + (* eq != NULL: store through it, then the second scan ---- *)
        destruct HeqwK as [Hc0 | (Hewr & Heqal & Heqhi & Heqhi2)];
          [ exfalso; exact (Heqnz Hc0) | ].
        pose proof (uwr_lo _ _ _ _ Hewr) as Heqlo.
        pose proof Heqhi2 as Heqhi2'.
        change (2 ^ 38) with 274877906944 in Heqhi2'.
        assert (Hdis : eqaddr + 8 <= psaddr \/ psaddr + 8 <= eqaddr)
          by (destruct Hdis2 as [Hc0 | Hd];
              [ exfalso; exact (Heqnz Hc0) | exact Hd ]).
        assert (Htk : true = uv_btaken BNE (mN !!! Regidx s6_idx)
                               zero_reg).
        { cbn [uv_btaken]. rewrite Hs6N.
          rewrite (moi_neq_zero eqaddr ltac:(unfold Z64; lia)).
          symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Heqnz. }
        iApply (wp_uv_btype0 C pt Psh MK mN (mword_of_int 0x424)
                  (mword_of_int 8040 : mword 13) s6_idx BNE true (mword_of_int 0x38c)
                  (ui_sh_424 pt MK Hltext HtextK) Htk
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID9) "Hcg Hpc".
        iApply (wp_sh_gt_tail38c CID9 MK mN m sp0 psaddr eqaddr s0 bs
                  (q + t)%nat 97
                  Hlay HokK Hfr0 Hs0p Hbufhi ltac:(lia) Hret2 Hspm
                  HwrK Hpsal Hpshi Hpshi2 Hewr Heqal Heqhi Heqhi2 Hdis
                  HspN Hs1N Hs2N Hs4N Hs5N Hs6N HslotsK HpresN'
                  with "Hcg Hpc [Hcont]").
        iIntros (CID10 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
        iApply ("Hcont" $! CID10 m' M' with "[] [] [] [] [] Hcg Hpc").
        * iPureIntro. exact Hcs.
        * iPureIntro. exact Ha0'.
        * iPureIntro. intros _. exact Hceq.
        * iPureIntro. exact Hcell'.
        * iPureIntro.
          apply (uM_only_in_trans M MK M').
          -- apply (uM_only_in_of_only M MK (uint sp0 - 80) 80).
             ++ exact (uM_only_widen M MK (uint sp0 - 80) 16 (uint sp0 - 80) 80
                         HonlyK ltac:(lia) ltac:(lia)).
             ++ apply elem_of_list_further. apply elem_of_list_further.
                apply elem_of_list_here.
          -- exact Honly'.
    - (* A WHITESPACE BYTE ENDED THE TOKEN ---- *)
      rewrite (bool_decide_eq_false_2 _ Hne).
      (* ---- 0x438  li s5,97 ---- *)
      iApply (wp_uv_li C pt Psh MK mK (mword_of_int 0x438)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97)
                (ui_sh_438 pt MK Hltext HtextK) ltac:(vm_compute; discriminate)
                ltac:(rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                         : (sign_extend' 64 (mword_of_int 97 : mword 12)
                            : mword 64) = mword_of_int 97);
                      symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID7) "Hcg Hpc".
      set (mN := <[Regidx s5_idx
                   := regval_into_reg (mword_of_int 97 : mword 64)]> mK).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x438 : mword 64) 4
                        = mword_of_int 0x43c)) in "Hpc".
      (* ---- 0x43c  c.j 0x388 ---- *)
      iApply (wp_uv_cj C pt Psh MK mN (mword_of_int 0x43c)
                (mword_of_int 1958 : mword 11) (mword_of_int 0x388)
                (ui_sh_43c pt MK Hltext HtextK)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc").
      iIntros (CID8) "Hcg Hpc".
      assert (HpresN : forall r : mword 5, Regidx r <> Regidx s5_idx ->
                mN !!! Regidx r = mK !!! Regidx r)
        by (intros r N5; exact (upd_ne mK (Regidx s5_idx) (Regidx r) _ N5)).
      assert (Hs1N : mN !!! Regidx s1_idx
                     = (mword_of_int (s0 + Z.of_nat (q + t)) : mword 64))
        by (rewrite (HpresN s1_idx ltac:(vm_compute; discriminate)); exact Hs1K).
      assert (Hs5N : mN !!! Regidx s5_idx = (mword_of_int 97 : mword 64))
        by exact (upd_eq mK (Regidx s5_idx) _).
      assert (Hs2N : mN !!! Regidx s2_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
        by (rewrite (HpresN s2_idx ltac:(vm_compute; discriminate)); exact Hs2K).
      assert (Hs4N : mN !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
        by (rewrite (HpresN s4_idx ltac:(vm_compute; discriminate)); exact Hs4K).
      assert (Hs6N : mN !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64))
        by (rewrite (HpresN s6_idx ltac:(vm_compute; discriminate)); exact Hs6K).
      assert (HspN : mN !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64))
        by (rewrite (HpresN sp_idx ltac:(vm_compute; discriminate)); exact HspK).
      assert (HpresN' : gt_pres mN m).
      { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6.
        rewrite (HpresN r N5). rewrite (HpresK r Hr N1).
        rewrite (HpresJ r N3 N5). exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5 N6). }
      iApply (wp_sh_gt_tail388 CID8 MK mN m sp0 psaddr eqaddr s0 bs
                (q + t)%nat 97
                Hlay HokK Hfr0 Hs0p Hbufhi ltac:(lia) Hret2 Hspm
                HwrK Hpsal Hpshi Hpshi2 HeqwK Hdis2
                HspN Hs1N Hs2N Hs4N Hs5N Hs6N HslotsK HpresN'
                with "Hcg Hpc [Hcont]").
      iIntros (CID9 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
      iApply ("Hcont" $! CID9 m' M' with "[] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0'.
      + iPureIntro. exact Hceq.
      + iPureIntro. exact Hcell'.
      + iPureIntro.
        apply (uM_only_in_trans M MK M').
        * apply (uM_only_in_of_only M MK (uint sp0 - 80) 80).
          -- exact (uM_only_widen M MK (uint sp0 - 80) 16 (uint sp0 - 80) 80
                      HonlyK ltac:(lia) ltac:(lia)).
          -- apply elem_of_list_further. apply elem_of_list_further.
             apply elem_of_list_here.
        * exact Honly'.
  Qed.

  (* ---- THE SWITCH, 0x356..0x3e8.  Only two arms are reachable:          *)
  (*      [case 0] (the buffer's NUL) and the default (a word).            *)
  Local Lemma wp_sh_gt_from356 (CIDp : CpuId)
      (M : gmap Z (bv 8)) (mF m : regfile) (sp0 : mword 64)
      (psaddr eqaddr s0 : Z) (bs : list (bv 8)) (q : nat) :
    sh_layout pt hbase hlen ->
    lex_ok M sp0 s0 bs ->
    sh_no_symbols bs ->
    sh_frame_ok hbase hlen sp0 80 ->
    0 < s0 -> s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 80 ->
    (q <= length bs)%nat ->
    (forall b : bv 8, bs !! q = Some b -> sh_is_ws b = false) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    uv_wr pt M psaddr 8 -> psaddr mod 8 = 0 ->
    uint sp0 <= psaddr -> psaddr + 8 <= 2 ^ 38 ->
    (eqaddr = 0 \/ (uv_wr pt M eqaddr 8 /\ eqaddr mod 8 = 0 /\
                    uint sp0 <= eqaddr /\ eqaddr + 8 <= 2 ^ 38)) ->
    (eqaddr = 0 \/ eqaddr + 8 <= psaddr \/ psaddr + 8 <= eqaddr) ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mF !!! Regidx s1_idx = (mword_of_int (s0 + Z.of_nat q) : mword 64) ->
    mF !!! Regidx s2_idx
      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    mF !!! Regidx s4_idx = (mword_of_int psaddr : mword 64) ->
    mF !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64) ->
    gt_slots M m sp0 -> gt_pres mF m ->
    uv_cap_gpr (CID := CIDp) C pt Psh M mF -∗
    pc_is (CID := CIDp) (mword_of_int 0x356) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (if bool_decide (q = length bs) then 0 else 97)
             : mword 64)⌝ -∗
       ⌜eqaddr <> 0 ->
          uM_bytes M' eqaddr 8
            (mword_of_int (s0 + Z.of_nat (q + sh_toklen (drop q bs)))
             : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int
             (s0 + Z.of_nat (q + sh_toklen (drop q bs)
                             + sh_skipws (drop (q + sh_toklen (drop q bs)) bs)))
           : mword 64)⌝ -∗
       ⌜uM_only_in M M' [(psaddr, 8); (eqaddr, 8); (uint sp0 - 80, 80)]⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hok Hnosym Hfr Hs0p Hbufhi Hq Hnwq Hret2 Hspm
           Hwr Hpsal Hpshi Hpshi2 Heqw Hdis2 HspF Hs1F Hs2F Hs4F Hs6F
           Hslots Hpres.
    pose proof Hfr as Hfr0. unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof Hok as Hok0.
    destruct Hok as (Himg & Htab & Hbuf & Hrd & Hst).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    pose proof Hbuf as Hbuf0.
    destruct Hbuf as ((Hbody & Hnul) & Hnzb).
    (* the byte the switch dispatches on *)
    assert (Hbex : exists bq : bv 8,
              M !! (s0 + Z.of_nat q) = Some bq /\
              (q = length bs -> bv_unsigned bq = 0) /\
              ((q < length bs)%nat ->
                 bs !! q = Some bq /\ bv_unsigned bq <> 0)).
    { destruct (decide (q = length bs)) as [He | Hne].
      - exists ubyte0. split_and!.
        + rewrite He. exact Hnul.
        + intros _. vm_compute. reflexivity.
        + intro Hc'. exfalso. lia.
      - assert (Hlt : (q < length bs)%nat) by lia.
        destruct (lookup_lt_is_Some_2 bs q Hlt) as (bq & Hbq).
        exists bq. split_and!.
        + exact (Hbody q bq Hbq).
        + intro Hc'. exfalso. lia.
        + intros _. split; [ exact Hbq | ].
          intro H0. exact (Hnzb q bq Hbq (proj1 (bv8_is0 bq) H0)). }
    destruct Hbex as (bq & Hbqm & Hbqz & Hbqn).
    pose proof (bv8_rng bq) as Hbrng.
    assert (Hb255 : 0 <= bv_unsigned bq < 256).
    { pose proof (bv_unsigned_in_range 8 bq) as Hr.
      assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite E in Hr. lia. }
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x356  lbu a5,0(s1) ---- *)
    assert (Hva : (mword_of_int (s0 + Z.of_nat q) : mword 64)
                  = add_vec (mF !!! Regidx s1_idx)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hs1F.
      assert (Hc0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc0 moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M s0 (Z.of_nat (length bs) + 1)
                (s0 + Z.of_nat q) Hrd ltac:(lia)) as (wl & Hll & Hokl).
    assert (Huva : uint (mword_of_int (s0 + Z.of_nat q) : mword 64)
                   = s0 + Z.of_nat q) by (apply uint_moi; unfold Z64; lia).
    assert (Hcanon : uva_canon (mword_of_int (s0 + Z.of_nat q) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    iApply (wp_uv_lbu C pt Psh M mF (mword_of_int 0x356)
              (mword_of_int 0 : mword 12) s1_idx a5_idx
              wl (mword_of_int (s0 + Z.of_nat q))
              (mword_of_int (bv_unsigned bq)) bq
              (ui_sh_356 pt M Hltext Htext)
              ltac:(vm_compute; discriminate) Hva Hll Hokl Hcanon
              ltac:(rewrite Huva; exact Hbqm)
              ltac:(symmetry; apply zext8_moi)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mA := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned bq) : mword 64)]> mF).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x356 : mword 64) 4
                      = mword_of_int 0x35a)) in "Hpc".
    assert (Ha5A : mA !!! Regidx a5_idx
                   = (mword_of_int (bv_unsigned bq) : mword 64))
      by exact (upd_eq mF (Regidx a5_idx) _).
    (* ---- 0x35a  sext.w s5,a5 ---- *)
    iApply (wp_uv_addiw C pt Psh M mA (mword_of_int 0x35a)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int (bv_unsigned bq))
              (ui_sh_35a pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5A;
                    rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                             : (sign_extend' 64 (mword_of_int 0 : mword 12)
                                : mword 64) = mword_of_int 0);
                    rewrite (moi_addw (bv_unsigned bq) 0
                               ltac:(unfold Z31; lia));
                    f_equal; lia)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mB := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned bq) : mword 64)]> mA).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x35a : mword 64) 4
                      = mword_of_int 0x35e)) in "Hpc".
    assert (HpresB : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              Regidx r <> Regidx s5_idx -> mB !!! Regidx r = mF !!! Regidx r).
    { intros r N5 Ns5.
      exact (eq_trans (upd_ne mA (Regidx s5_idx) (Regidx r) _ Ns5)
               (upd_ne mF (Regidx a5_idx) (Regidx r) _ N5)). }
    assert (Ha5B : mB !!! Regidx a5_idx
                   = (mword_of_int (bv_unsigned bq) : mword 64))
      by (rewrite (upd_ne mA (Regidx s5_idx) (Regidx a5_idx) _
                     ltac:(vm_compute; discriminate)); exact Ha5A).
    assert (Hs5B : mB !!! Regidx s5_idx
                   = (mword_of_int (bv_unsigned bq) : mword 64))
      by exact (upd_eq mA (Regidx s5_idx) _).
    (* ---- 0x35e  li a4,60 ---- *)
    iApply (wp_uv_li C pt Psh M mB (mword_of_int 0x35e)
              (mword_of_int 60 : mword 12) a4_idx (mword_of_int 60)
              (ui_sh_35e pt M Hltext Htext) ltac:(vm_compute; discriminate)
              ltac:(rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                       : (sign_extend' 64 (mword_of_int 60 : mword 12)
                          : mword 64) = mword_of_int 60);
                    symmetry; apply moi_add_zero_l)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mC := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 60 : mword 64)]> mB).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x35e : mword 64) 4
                      = mword_of_int 0x362)) in "Hpc".
    assert (HpresC : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              mC !!! Regidx r = mB !!! Regidx r)
      by (intros r N4; exact (upd_ne mB (Regidx a4_idx) (Regidx r) _ N4)).
    assert (Ha4C : mC !!! Regidx a4_idx = (mword_of_int 60 : mword 64))
      by exact (upd_eq mB (Regidx a4_idx) _).
    assert (Ha5C : mC !!! Regidx a5_idx
                   = (mword_of_int (bv_unsigned bq) : mword 64))
      by (rewrite (HpresC a5_idx ltac:(vm_compute; discriminate)); exact Ha5B).
    (* ---- 0x362  bltu a4,a5,0x3ca ---- *)
    destruct (Z_le_gt_dec (bv_unsigned bq) 60) as [Hble | Hbgt].
    - (* the byte is at most '<' ---- *)
      assert (Htk : false = uv_btaken BLTU (mC !!! Regidx a4_idx)
                              (mC !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha4C Ha5C.
        rewrite (moi_lt_u 60 (bv_unsigned bq) ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.ltb_ge. lia. }
      iApply (wp_uv_btype C pt Psh M mC (mword_of_int 0x362)
                (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU
                false (mword_of_int 0x3ca)
                (ui_sh_362 pt M Hltext Htext) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x3ca : mword 64)
                         else add_vec_int (mword_of_int 0x362 : mword 64) 4)
                        = mword_of_int 0x366)) in "Hpc".
      (* ---- 0x366  li a4,58 ---- *)
      iApply (wp_uv_li C pt Psh M mC (mword_of_int 0x366)
                (mword_of_int 58 : mword 12) a4_idx (mword_of_int 58)
                (ui_sh_366 pt M Hltext Htext) ltac:(vm_compute; discriminate)
                ltac:(rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                         : (sign_extend' 64 (mword_of_int 58 : mword 12)
                            : mword 64) = mword_of_int 58);
                      symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      set (mD := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 58 : mword 64)]> mC).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x366 : mword 64) 4
                        = mword_of_int 0x36a)) in "Hpc".
      assert (HpresD : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                mD !!! Regidx r = mB !!! Regidx r).
      { intros r N4.
        exact (eq_trans (upd_ne mC (Regidx a4_idx) (Regidx r) _ N4)
                 (HpresC r N4)). }
      assert (Ha4D : mD !!! Regidx a4_idx = (mword_of_int 58 : mword 64))
        by exact (upd_eq mC (Regidx a4_idx) _).
      assert (Ha5D : mD !!! Regidx a5_idx
                     = (mword_of_int (bv_unsigned bq) : mword 64))
        by (rewrite (HpresD a5_idx ltac:(vm_compute; discriminate)); exact Ha5B).
      (* the byte is at most ';' - 1, because ';' and '<' are SYMBOLS *)
      assert (Hb58 : bv_unsigned bq <= 58).
      { destruct (decide (q = length bs)) as [He | Hne].
        - rewrite (Hbqz He). lia.
        - assert (Hlt : (q < length bs)%nat) by lia.
          destruct (Hbqn Hlt) as (Hbql & _).
          pose proof (Hnosym q bq Hbql) as Hsymb.
          pose proof (sym_excl bq 59 Hsymb ltac:(lia)
                        ltac:(vm_compute; reflexivity)) as H59.
          pose proof (sym_excl bq 60 Hsymb ltac:(lia)
                        ltac:(vm_compute; reflexivity)) as H60.
          lia. }
      (* ---- 0x36a  bltu a4,a5,0x386 ---- *)
      assert (Htk2 : false = uv_btaken BLTU (mD !!! Regidx a4_idx)
                               (mD !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha4D Ha5D.
        rewrite (moi_lt_u 58 (bv_unsigned bq) ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.ltb_ge. lia. }
      iApply (wp_uv_btype C pt Psh M mD (mword_of_int 0x36a)
                (mword_of_int 28 : mword 13) a5_idx a4_idx BLTU
                false (mword_of_int 0x386)
                (ui_sh_36a pt M Hltext Htext) Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x386 : mword 64)
                         else add_vec_int (mword_of_int 0x36a : mword 64) 4)
                        = mword_of_int 0x36e)) in "Hpc".
      assert (Hs5D : mD !!! Regidx s5_idx
                     = (mword_of_int (bv_unsigned bq) : mword 64))
        by (rewrite (HpresD s5_idx ltac:(vm_compute; discriminate)); exact Hs5B).
      assert (Hs1D : mD !!! Regidx s1_idx
                     = (mword_of_int (s0 + Z.of_nat q) : mword 64)).
      { rewrite (HpresD s1_idx ltac:(vm_compute; discriminate)).
        rewrite (HpresB s1_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs1F. }
      assert (Hs2D : mD !!! Regidx s2_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
      { rewrite (HpresD s2_idx ltac:(vm_compute; discriminate)).
        rewrite (HpresB s2_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs2F. }
      assert (Hs4D : mD !!! Regidx s4_idx = (mword_of_int psaddr : mword 64)).
      { rewrite (HpresD s4_idx ltac:(vm_compute; discriminate)).
        rewrite (HpresB s4_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs4F. }
      assert (Hs6D : mD !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64)).
      { rewrite (HpresD s6_idx ltac:(vm_compute; discriminate)).
        rewrite (HpresB s6_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs6F. }
      assert (HspD : mD !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
      { rewrite (HpresD sp_idx ltac:(vm_compute; discriminate)).
        rewrite (HpresB sp_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact HspF. }
      assert (HpresD' : gt_pres mD m).
      { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6.
        rewrite (HpresD r
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate)).
        rewrite (HpresB r
                   ltac:(intro E; injection E as E'; subst r;
                         vm_compute in Hr; discriminate) N5).
        exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5 N6). }
      (* ---- 0x36e  c.beqz a5,0x388 ---- *)
      destruct (decide (q = length bs)) as [Hqend | Hqne].
      + (* CASE 0: end of input ---- *)
        assert (Hb0 : bv_unsigned bq = 0) by exact (Hbqz Hqend).
        assert (Htk3 : true = eq_vec (mD !!! Regidx a5_idx) zero_reg).
        { rewrite Ha5D (moi_eq_zero (bv_unsigned bq) ltac:(unfold Z64; lia)) Hb0.
          reflexivity. }
        iApply (wp_uv_cbeqz C pt Psh M mD (mword_of_int 0x36e)
                  (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                  true (mword_of_int 0x388)
                  (ui_sh_36e pt M Hltext Htext)
                  ltac:(vm_compute; reflexivity) Htk3
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID7) "Hcg Hpc".
        assert (Htok0 : sh_toklen (drop q bs) = 0%nat)
          by (rewrite (ltac:(apply drop_ge; lia) : drop q bs = []);
              exact sh_toklen_nil).
        iApply (wp_sh_gt_tail388 CID7 M mD m sp0 psaddr eqaddr s0 bs q 0
                  Hlay Hok0 Hfr0 Hs0p Hbufhi Hq Hret2 Hspm
                  Hwr Hpsal Hpshi Hpshi2 Heqw Hdis2
                  HspD Hs1D Hs2D Hs4D ltac:(rewrite Hs5D Hb0; reflexivity) Hs6D
                  Hslots HpresD'
                  with "Hcg Hpc [Hcont]").
        iIntros (CID8 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
        iApply ("Hcont" $! CID8 m' M' with "[] [] [] [] [] Hcg Hpc").
        * iPureIntro. exact Hcs.
        * iPureIntro. rewrite (bool_decide_eq_true_2 _ Hqend). exact Ha0'.
        * iPureIntro. intro Hc'.
          replace (q + sh_toklen (drop q bs))%nat with q
            by (rewrite Htok0; lia).
          exact (Hceq Hc').
        * iPureIntro.
          replace (q + sh_toklen (drop q bs))%nat with q
            by (rewrite Htok0; lia).
          exact Hcell'.
        * iPureIntro. exact Honly'.
      + (* THE DEFAULT ARM, reached with a byte in [1, 58] ---- *)
        assert (Hlt : (q < length bs)%nat) by lia.
        destruct (Hbqn Hlt) as (Hbql & Hbnz).
        pose proof (Hnosym q bq Hbql) as Hsymb.
        pose proof (sym_excl bq 38 Hsymb ltac:(lia)
                      ltac:(vm_compute; reflexivity)) as H38.
        pose proof (sym_excl bq 40 Hsymb ltac:(lia)
                      ltac:(vm_compute; reflexivity)) as H40.
        pose proof (sym_excl bq 41 Hsymb ltac:(lia)
                      ltac:(vm_compute; reflexivity)) as H41.
        assert (Htk3 : false = eq_vec (mD !!! Regidx a5_idx) zero_reg).
        { rewrite Ha5D (moi_eq_zero (bv_unsigned bq) ltac:(unfold Z64; lia)).
          symmetry. apply Z.eqb_neq. exact Hbnz. }
        iApply (wp_uv_cbeqz C pt Psh M mD (mword_of_int 0x36e)
                  (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                  false (mword_of_int 0x388)
                  (ui_sh_36e pt M Hltext Htext)
                  ltac:(vm_compute; reflexivity) Htk3
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intro Hc'; discriminate Hc')
                  with "Hcg Hpc").
        iIntros (CID7) "Hcg Hpc".
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : (if false then (mword_of_int 0x388 : mword 64)
                           else add_vec_int (mword_of_int 0x36e : mword 64) 2)
                          = mword_of_int 0x370)) in "Hpc".
        (* ---- 0x370  li a4,38 ---- *)
        iApply (wp_uv_li C pt Psh M mD (mword_of_int 0x370)
                  (mword_of_int 38 : mword 12) a4_idx (mword_of_int 38)
                  (ui_sh_370 pt M Hltext Htext) ltac:(vm_compute; discriminate)
                  ltac:(rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                           : (sign_extend' 64 (mword_of_int 38 : mword 12)
                              : mword 64) = mword_of_int 38);
                        symmetry; apply moi_add_zero_l)
                  with "Hcg Hpc").
        iIntros (CID8) "Hcg Hpc".
        set (mE0 := <[Regidx a4_idx
                      := regval_into_reg (mword_of_int 38 : mword 64)]> mD).
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : add_vec_int (mword_of_int 0x370 : mword 64) 4
                          = mword_of_int 0x374)) in "Hpc".
        assert (Ha4E : mE0 !!! Regidx a4_idx = (mword_of_int 38 : mword 64))
          by exact (upd_eq mD (Regidx a4_idx) _).
        assert (Ha5E : mE0 !!! Regidx a5_idx
                       = (mword_of_int (bv_unsigned bq) : mword 64))
          by (rewrite (upd_ne mD (Regidx a4_idx) (Regidx a5_idx) _
                         ltac:(vm_compute; discriminate)); exact Ha5D).
        (* ---- 0x374  beq a5,a4,0x386 ---- *)
        assert (Htk4 : false = uv_btaken BEQ (mE0 !!! Regidx a5_idx)
                                 (mE0 !!! Regidx a4_idx)).
        { cbn [uv_btaken]. rewrite Ha5E Ha4E.
          rewrite (moi_eq_vec (bv_unsigned bq) 38 ltac:(unfold Z64; lia)
                     ltac:(unfold Z64; lia)).
          symmetry. apply Z.eqb_neq. exact H38. }
        iApply (wp_uv_btype C pt Psh M mE0 (mword_of_int 0x374)
                  (mword_of_int 18 : mword 13) a4_idx a5_idx BEQ
                  false (mword_of_int 0x386)
                  (ui_sh_374 pt M Hltext Htext) Htk4
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intro Hc'; discriminate Hc')
                  with "Hcg Hpc").
        iIntros (CID9) "Hcg Hpc".
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : (if false then (mword_of_int 0x386 : mword 64)
                           else add_vec_int (mword_of_int 0x374 : mword 64) 4)
                          = mword_of_int 0x378)) in "Hpc".
        (* ---- 0x378  addiw a5,a5,-40 ---- *)
        iApply (wp_uv_addiw C pt Psh M mE0 (mword_of_int 0x378)
                  (mword_of_int 4056 : mword 12) a5_idx a5_idx
                  (mword_of_int (bv_unsigned bq - 40))
                  (ui_sh_378 pt M Hltext Htext) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha5E;
                        rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                                 : (sign_extend' 64 (mword_of_int 4056 : mword 12)
                                    : mword 64) = mword_of_int (-40));
                        rewrite moi_add;
                        symmetry;
                        exact (sext32_low32 (bv_unsigned bq + -40)
                                 ltac:(unfold Z31; lia)))
                  with "Hcg Hpc").
        iIntros (CID10) "Hcg Hpc".
        set (mF2 := <[Regidx a5_idx
                      := regval_into_reg
                           (mword_of_int (bv_unsigned bq - 40) : mword 64)]> mE0).
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : add_vec_int (mword_of_int 0x378 : mword 64) 4
                          = mword_of_int 0x37c)) in "Hpc".
        assert (Ha5F2 : mF2 !!! Regidx a5_idx
                        = (mword_of_int (bv_unsigned bq - 40) : mword 64))
          by exact (upd_eq mE0 (Regidx a5_idx) _).
        (* ---- 0x37c  andi a5,a5,255 ---- *)
        iApply (wp_uv_andi C pt Psh M mF2 (mword_of_int 0x37c)
                  (mword_of_int 255 : mword 12) a5_idx a5_idx
                  (mword_of_int ((bv_unsigned bq - 40) mod 256))
                  (ui_sh_37c pt M Hltext Htext) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha5F2;
                        rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                                 : (sign_extend' 64 (mword_of_int 255 : mword 12)
                                    : mword 64) = mword_of_int 255);
                        symmetry; apply moi_and255)
                  with "Hcg Hpc").
        iIntros (CID11) "Hcg Hpc".
        set (mG2 := <[Regidx a5_idx
                      := regval_into_reg
                           (mword_of_int ((bv_unsigned bq - 40) mod 256)
                            : mword 64)]> mF2).
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : add_vec_int (mword_of_int 0x37c : mword 64) 4
                          = mword_of_int 0x380)) in "Hpc".
        (* ---- 0x380  c.li a4,1 ---- *)
        iApply (wp_uv_cli C pt Psh M mG2 (mword_of_int 0x380)
                  (mword_of_int 1 : mword 6) a4_idx (mword_of_int 1 : mword 64)
                  (ui_sh_380 pt M Hltext Htext) ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID12) "Hcg Hpc".
        set (mH2 := <[Regidx a4_idx
                      := regval_into_reg (mword_of_int 1 : mword 64)]> mG2).
        iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                        : add_vec_int (mword_of_int 0x380 : mword 64) 2
                          = mword_of_int 0x382)) in "Hpc".
        assert (Ha4H : mH2 !!! Regidx a4_idx = (mword_of_int 1 : mword 64))
          by exact (upd_eq mG2 (Regidx a4_idx) _).
        assert (Ha5H : mH2 !!! Regidx a5_idx
                       = (mword_of_int ((bv_unsigned bq - 40) mod 256)
                          : mword 64))
          by (rewrite (upd_ne mG2 (Regidx a4_idx) (Regidx a5_idx) _
                         ltac:(vm_compute; discriminate));
              exact (upd_eq mF2 (Regidx a5_idx) _)).
        (* ---- 0x382  bltu a4,a5,0x3ec -- ALWAYS taken here ---- *)
        assert (Hmod : 1 < (bv_unsigned bq - 40) mod 256).
        { destruct (Z_le_gt_dec 40 (bv_unsigned bq)) as [Hge | Hlt40].
          - rewrite (Z.mod_small (bv_unsigned bq - 40) 256 ltac:(lia)). lia.
          - assert (Hm : (bv_unsigned bq - 40) mod 256 = bv_unsigned bq - 40 + 256)
              by (symmetry;
                  apply (Zmod_unique (bv_unsigned bq - 40) 256 (-1)
                           (bv_unsigned bq - 40 + 256)); lia).
            rewrite Hm. lia. }
        assert (Htk5 : true = uv_btaken BLTU (mH2 !!! Regidx a4_idx)
                                (mH2 !!! Regidx a5_idx)).
        { cbn [uv_btaken]. rewrite Ha4H Ha5H.
          pose proof (Z.mod_pos_bound (bv_unsigned bq - 40) 256 ltac:(lia)).
          rewrite (moi_lt_u 1 ((bv_unsigned bq - 40) mod 256)
                     ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
          symmetry. apply Z.ltb_lt. lia. }
        iApply (wp_uv_btype C pt Psh M mH2 (mword_of_int 0x382)
                  (mword_of_int 106 : mword 13) a5_idx a4_idx BLTU
                  true (mword_of_int 0x3ec)
                  (ui_sh_382 pt M Hltext Htext) Htk5
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID13) "Hcg Hpc".
        assert (HpresH : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                  Regidx r <> Regidx a5_idx -> mH2 !!! Regidx r = mD !!! Regidx r).
        { intros r N4 N5.
          exact (eq_trans (upd_ne mG2 (Regidx a4_idx) (Regidx r) _ N4)
                   (eq_trans (upd_ne mF2 (Regidx a5_idx) (Regidx r) _ N5)
                      (eq_trans (upd_ne mE0 (Regidx a5_idx) (Regidx r) _ N5)
                         (upd_ne mD (Regidx a4_idx) (Regidx r) _ N4)))). }
        iApply (wp_sh_gt_word CID13 M mH2 m sp0 psaddr eqaddr s0 bs q bq
                  Hlay Hok0 Hnosym Hfr0 Hs0p Hbufhi Hlt Hbql (Hnwq bq Hbql)
                  Hret2 Hspm Hwr Hpsal Hpshi Hpshi2 Heqw Hdis2
                  ltac:(rewrite (HpresH sp_idx ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)); exact HspD)
                  ltac:(rewrite (HpresH s1_idx ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)); exact Hs1D)
                  ltac:(rewrite (HpresH s2_idx ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)); exact Hs2D)
                  ltac:(rewrite (HpresH s4_idx ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)); exact Hs4D)
                  ltac:(rewrite (HpresH s6_idx ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)); exact Hs6D)
                  Hslots
                  ltac:(intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6;
                        rewrite (HpresH r
                                   ltac:(intro E; injection E as E'; subst r;
                                         vm_compute in Hr; discriminate)
                                   ltac:(intro E; injection E as E'; subst r;
                                         vm_compute in Hr; discriminate));
                        exact (HpresD' r Hr Nsp N0 N1 N2 N3 N4 N5 N6))
                  with "Hcg Hpc [Hcont]").
        iIntros (CID14 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
        iApply ("Hcont" $! CID14 m' M' with "[] [] [] [] [] Hcg Hpc").
        * iPureIntro. exact Hcs.
        * iPureIntro. rewrite (bool_decide_eq_false_2 _ Hqne). exact Ha0'.
        * iPureIntro. exact Hceq.
        * iPureIntro. exact Hcell'.
        * iPureIntro. exact Honly'.
    - (* the byte is above '<': only the [>] and [|] cases remain, and both
         are SYMBOLS, so the default arm is reached ---- *)
      assert (Hqne : q <> length bs)
        by (intro He; pose proof (Hbqz He); lia).
      assert (Hlt : (q < length bs)%nat) by lia.
      destruct (Hbqn Hlt) as (Hbql & Hbnz).
      pose proof (Hnosym q bq Hbql) as Hsymb.
      pose proof (sym_excl bq 62 Hsymb ltac:(lia)
                    ltac:(vm_compute; reflexivity)) as H62.
      pose proof (sym_excl bq 124 Hsymb ltac:(lia)
                    ltac:(vm_compute; reflexivity)) as H124.
      assert (Htk : true = uv_btaken BLTU (mC !!! Regidx a4_idx)
                             (mC !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha4C Ha5C.
        rewrite (moi_lt_u 60 (bv_unsigned bq) ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.ltb_lt. lia. }
      iApply (wp_uv_btype C pt Psh M mC (mword_of_int 0x362)
                (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU
                true (mword_of_int 0x3ca)
                (ui_sh_362 pt M Hltext Htext) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      (* ---- 0x3ca  li a4,62 ---- *)
      iApply (wp_uv_li C pt Psh M mC (mword_of_int 0x3ca)
                (mword_of_int 62 : mword 12) a4_idx (mword_of_int 62)
                (ui_sh_3ca pt M Hltext Htext) ltac:(vm_compute; discriminate)
                ltac:(rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                         : (sign_extend' 64 (mword_of_int 62 : mword 12)
                            : mword 64) = mword_of_int 62);
                      symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      set (mD2 := <[Regidx a4_idx
                    := regval_into_reg (mword_of_int 62 : mword 64)]> mC).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x3ca : mword 64) 4
                        = mword_of_int 0x3ce)) in "Hpc".
      assert (Ha4D2 : mD2 !!! Regidx a4_idx = (mword_of_int 62 : mword 64))
        by exact (upd_eq mC (Regidx a4_idx) _).
      assert (Ha5D2 : mD2 !!! Regidx a5_idx
                      = (mword_of_int (bv_unsigned bq) : mword 64))
        by (rewrite (upd_ne mC (Regidx a4_idx) (Regidx a5_idx) _
                       ltac:(vm_compute; discriminate)); exact Ha5C).
      (* ---- 0x3ce  bne a5,a4,0x3e4 ---- *)
      assert (Htk2 : true = uv_btaken BNE (mD2 !!! Regidx a5_idx)
                              (mD2 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha5D2 Ha4D2.
        rewrite (moi_neq_vec (bv_unsigned bq) 62 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. exact H62. }
      iApply (wp_uv_btype C pt Psh M mD2 (mword_of_int 0x3ce)
                (mword_of_int 22 : mword 13) a4_idx a5_idx BNE
                true (mword_of_int 0x3e4)
                (ui_sh_3ce pt M Hltext Htext) Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      (* ---- 0x3e4  li a4,124 ---- *)
      iApply (wp_uv_li C pt Psh M mD2 (mword_of_int 0x3e4)
                (mword_of_int 124 : mword 12) a4_idx (mword_of_int 124)
                (ui_sh_3e4 pt M Hltext Htext) ltac:(vm_compute; discriminate)
                ltac:(rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                         : (sign_extend' 64 (mword_of_int 124 : mword 12)
                            : mword 64) = mword_of_int 124);
                      symmetry; apply moi_add_zero_l)
                with "Hcg Hpc").
      iIntros (CID7) "Hcg Hpc".
      set (mE2 := <[Regidx a4_idx
                    := regval_into_reg (mword_of_int 124 : mword 64)]> mD2).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x3e4 : mword 64) 4
                        = mword_of_int 0x3e8)) in "Hpc".
      assert (Ha4E2 : mE2 !!! Regidx a4_idx = (mword_of_int 124 : mword 64))
        by exact (upd_eq mD2 (Regidx a4_idx) _).
      assert (Ha5E2 : mE2 !!! Regidx a5_idx
                      = (mword_of_int (bv_unsigned bq) : mword 64))
        by (rewrite (upd_ne mD2 (Regidx a4_idx) (Regidx a5_idx) _
                       ltac:(vm_compute; discriminate)); exact Ha5D2).
      (* ---- 0x3e8  beq a5,a4,0x386 ---- *)
      assert (Htk3 : false = uv_btaken BEQ (mE2 !!! Regidx a5_idx)
                               (mE2 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha5E2 Ha4E2.
        rewrite (moi_eq_vec (bv_unsigned bq) 124 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact H124. }
      iApply (wp_uv_btype C pt Psh M mE2 (mword_of_int 0x3e8)
                (mword_of_int 8094 : mword 13) a4_idx a5_idx BEQ
                false (mword_of_int 0x386)
                (ui_sh_3e8 pt M Hltext Htext) Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID8) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x386 : mword 64)
                         else add_vec_int (mword_of_int 0x3e8 : mword 64) 4)
                        = mword_of_int 0x3ec)) in "Hpc".
      assert (HpresE2 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                Regidx r <> Regidx a5_idx -> Regidx r <> Regidx s5_idx ->
                mE2 !!! Regidx r = mF !!! Regidx r).
      { intros r N4 N5 Ns5.
        exact (eq_trans (upd_ne mD2 (Regidx a4_idx) (Regidx r) _ N4)
                 (eq_trans (upd_ne mC (Regidx a4_idx) (Regidx r) _ N4)
                    (eq_trans (HpresC r N4) (HpresB r N5 Ns5)))). }
      iApply (wp_sh_gt_word CID8 M mE2 m sp0 psaddr eqaddr s0 bs q bq
                Hlay Hok0 Hnosym Hfr0 Hs0p Hbufhi Hlt Hbql (Hnwq bq Hbql)
                Hret2 Hspm Hwr Hpsal Hpshi Hpshi2 Heqw Hdis2
                ltac:(rewrite (HpresE2 sp_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact HspF)
                ltac:(rewrite (HpresE2 s1_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hs1F)
                ltac:(rewrite (HpresE2 s2_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hs2F)
                ltac:(rewrite (HpresE2 s4_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hs4F)
                ltac:(rewrite (HpresE2 s6_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hs6F)
                Hslots
                ltac:(intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6;
                      rewrite (HpresE2 r
                                 ltac:(intro E; injection E as E'; subst r;
                                       vm_compute in Hr; discriminate)
                                 ltac:(intro E; injection E as E'; subst r;
                                       vm_compute in Hr; discriminate) N5);
                      exact (Hpres r Hr Nsp N0 N1 N2 N3 N4 N5 N6))
                with "Hcg Hpc [Hcont]").
      iIntros (CID9 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
      iApply ("Hcont" $! CID9 m' M' with "[] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. rewrite (bool_decide_eq_false_2 _ Hqne). exact Ha0'.
      + iPureIntro. exact Hceq.
      + iPureIntro. exact Hcell'.
      + iPureIntro. exact Honly'.
  Qed.

  (* ===================================================================== *)
  (* §6 gettoken @0x310 -- the whole function.                              *)
  (*                                                                        *)
  (*   310..322  the 64-byte prologue (ra, s0..s6 spilled)                  *)
  (*   324..332  s4 := ps, s2 := es, s5 := q, s6 := eq, s1 := *ps,          *)
  (*             s3 := whitespace                                           *)
  (*   336..34c  the leading whitespace scan ([wp_sh_wsskip])               *)
  (*   34e..352  if (q) *q = s                                              *)
  (*   356..3e8  ret := *s, and the switch -- only [case 0] and the         *)
  (*             default are reachable, which is what [sh_no_symbols] buys  *)
  (*   3ec..41a  the word scan; 388..3ae  if (eq) *eq = s, then the second  *)
  (*             whitespace scan; 3b0..3c8  *ps = s and the epilogue        *)
  (* ===================================================================== *)

  Lemma wp_sh_gettoken (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr qaddr eqaddr s0 : Z) (bs : list (bv 8))
      (off : nat) :
    wp_sh_gettoken_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 psaddr qaddr eqaddr s0 bs off.
  Proof.
    intros Hpre Hsp Hst Hps Hes Hqr Heqr Hcellp Hqw Heqw Hdis1 Hdis2 Hdis3
           Hoff Hret2.
    destruct Hpre as (Hlay & Himg & Htab & Hbuf & Hnosym & Hrd & Hwr & Hs0lo &
                      Hs0hi & Hfr & Hbufhi).
    (* [sh_parse_pre]'s 8th conjunct is now [8208 <= s0] (the buffer is above
       the loaded image); the block lemmas below only need it positive. *)
    assert (Hs0p : 0 < s0) by lia.
    destruct Hcellp as (Hcell & Hpsrd & Hcellw & Hpsal & Hpshi & Hpshi2).
    pose proof Hfr as Hfr0. unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & Hsgt & _ & _ & _ & Hsstrchr & _).
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi.
    pose proof Hpshi2 as Hpshi2'. change (2 ^ 38) with 274877906944 in Hpshi2'.
    destruct (uv_stack_split pt M sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hst64 & _).
    assert (Hokm : lex_ok M sp0 s0 bs) by (split_and!; assumption).
    (* the leading whitespace run, and the byte it stops on *)
    set (kk := sh_skipws (drop off bs)).
    assert (Hkk : (off + kk <= length bs)%nat).
    { unfold kk. pose proof (sh_skipws_le (drop off bs)) as H.
      rewrite length_drop in H. lia. }
    assert (Hnwq : forall b : bv 8, bs !! (off + kk)%nat = Some b ->
              sh_is_ws b = false).
    { intros b Hb. apply (sh_skipws_stop (drop off bs)).
      rewrite (lookup_drop bs off (sh_skipws (drop off bs))). exact Hb. }
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsgt) in "Hpc".
    (* ---- 0x310  c.addi16sp sp,sp,-64 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 64) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))
                    : mword 64) = mword_of_int (-64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x310)
              (mword_of_int 60 : mword 6) (mword_of_int (uint sp0 - 64))
              (ui_sh_310 pt M Hltext (sh_img_text M Himg)) Hwsp with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mA := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64)]> m).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x310 : mword 64) 2
                      = mword_of_int 0x312)) in "Hpc".
    assert (HspA : mA !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (HpresA : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              mA !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0x312  c.sdsp ra_idx ---- *)
    iApply (wp_uv_frame_store C pt CID1 Psh M mA sp0 (mword_of_int 0x312)
              (mword_of_int 7 : mword 6) ra_idx 64 56
              (ui_sh_312 pt M Hltext (sh_img_text M Himg))
              Hst64 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x312 : mword 64) 2
                      = mword_of_int 0x314)) in "Hpc".
    set (Q1 := uM_store8 M (uint sp0 - 64 + 56) (mA !!! Regidx ra_idx)).
    assert (Himg1 : sh_img_sub Q1)
      by (unfold Q1; apply img_store8; [ exact Himg | lia ]).
    assert (Hstk1 : uv_stack pt Q1 sp0 64)
      by (unfold Q1; apply stack_store8; exact Hst64).
    (* ---- 0x314  c.sdsp s0_idx ---- *)
    iApply (wp_uv_frame_store C pt CID2 Psh Q1 mA sp0 (mword_of_int 0x314)
              (mword_of_int 6 : mword 6) s0_idx 64 48
              (ui_sh_314 pt Q1 Hltext (sh_img_text Q1 Himg1))
              Hstk1 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x314 : mword 64) 2
                      = mword_of_int 0x316)) in "Hpc".
    set (Q2 := uM_store8 Q1 (uint sp0 - 64 + 48) (mA !!! Regidx s0_idx)).
    assert (Himg2 : sh_img_sub Q2)
      by (unfold Q2; apply img_store8; [ exact Himg1 | lia ]).
    assert (Hstk2 : uv_stack pt Q2 sp0 64)
      by (unfold Q2; apply stack_store8; exact Hstk1).
    (* ---- 0x316  c.sdsp s1_idx ---- *)
    iApply (wp_uv_frame_store C pt CID3 Psh Q2 mA sp0 (mword_of_int 0x316)
              (mword_of_int 5 : mword 6) s1_idx 64 40
              (ui_sh_316 pt Q2 Hltext (sh_img_text Q2 Himg2))
              Hstk2 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x316 : mword 64) 2
                      = mword_of_int 0x318)) in "Hpc".
    set (Q3 := uM_store8 Q2 (uint sp0 - 64 + 40) (mA !!! Regidx s1_idx)).
    assert (Himg3 : sh_img_sub Q3)
      by (unfold Q3; apply img_store8; [ exact Himg2 | lia ]).
    assert (Hstk3 : uv_stack pt Q3 sp0 64)
      by (unfold Q3; apply stack_store8; exact Hstk2).
    (* ---- 0x318  c.sdsp s2_idx ---- *)
    iApply (wp_uv_frame_store C pt CID4 Psh Q3 mA sp0 (mword_of_int 0x318)
              (mword_of_int 4 : mword 6) s2_idx 64 32
              (ui_sh_318 pt Q3 Hltext (sh_img_text Q3 Himg3))
              Hstk3 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x318 : mword 64) 2
                      = mword_of_int 0x31a)) in "Hpc".
    set (Q4 := uM_store8 Q3 (uint sp0 - 64 + 32) (mA !!! Regidx s2_idx)).
    assert (Himg4 : sh_img_sub Q4)
      by (unfold Q4; apply img_store8; [ exact Himg3 | lia ]).
    assert (Hstk4 : uv_stack pt Q4 sp0 64)
      by (unfold Q4; apply stack_store8; exact Hstk3).
    (* ---- 0x31a  c.sdsp s3_idx ---- *)
    iApply (wp_uv_frame_store C pt CID5 Psh Q4 mA sp0 (mword_of_int 0x31a)
              (mword_of_int 3 : mword 6) s3_idx 64 24
              (ui_sh_31a pt Q4 Hltext (sh_img_text Q4 Himg4))
              Hstk4 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x31a : mword 64) 2
                      = mword_of_int 0x31c)) in "Hpc".
    set (Q5 := uM_store8 Q4 (uint sp0 - 64 + 24) (mA !!! Regidx s3_idx)).
    assert (Himg5 : sh_img_sub Q5)
      by (unfold Q5; apply img_store8; [ exact Himg4 | lia ]).
    assert (Hstk5 : uv_stack pt Q5 sp0 64)
      by (unfold Q5; apply stack_store8; exact Hstk4).
    (* ---- 0x31c  c.sdsp s4_idx ---- *)
    iApply (wp_uv_frame_store C pt CID6 Psh Q5 mA sp0 (mword_of_int 0x31c)
              (mword_of_int 2 : mword 6) s4_idx 64 16
              (ui_sh_31c pt Q5 Hltext (sh_img_text Q5 Himg5))
              Hstk5 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x31c : mword 64) 2
                      = mword_of_int 0x31e)) in "Hpc".
    set (Q6 := uM_store8 Q5 (uint sp0 - 64 + 16) (mA !!! Regidx s4_idx)).
    assert (Himg6 : sh_img_sub Q6)
      by (unfold Q6; apply img_store8; [ exact Himg5 | lia ]).
    assert (Hstk6 : uv_stack pt Q6 sp0 64)
      by (unfold Q6; apply stack_store8; exact Hstk5).
    (* ---- 0x31e  c.sdsp s5_idx ---- *)
    iApply (wp_uv_frame_store C pt CID7 Psh Q6 mA sp0 (mword_of_int 0x31e)
              (mword_of_int 1 : mword 6) s5_idx 64 8
              (ui_sh_31e pt Q6 Hltext (sh_img_text Q6 Himg6))
              Hstk6 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x31e : mword 64) 2
                      = mword_of_int 0x320)) in "Hpc".
    set (Q7 := uM_store8 Q6 (uint sp0 - 64 + 8) (mA !!! Regidx s5_idx)).
    assert (Himg7 : sh_img_sub Q7)
      by (unfold Q7; apply img_store8; [ exact Himg6 | lia ]).
    assert (Hstk7 : uv_stack pt Q7 sp0 64)
      by (unfold Q7; apply stack_store8; exact Hstk6).
    (* ---- 0x320  c.sdsp s6_idx ---- *)
    iApply (wp_uv_frame_store C pt CID8 Psh Q7 mA sp0 (mword_of_int 0x320)
              (mword_of_int 0 : mword 6) s6_idx 64 0
              (ui_sh_320 pt Q7 Hltext (sh_img_text Q7 Himg7))
              Hstk7 ltac:(lia) ltac:(lia) ltac:(reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x320 : mword 64) 2
                      = mword_of_int 0x322)) in "Hpc".
    set (Q8 := uM_store8 Q7 (uint sp0 - 64 + 0) (mA !!! Regidx s6_idx)).
    assert (Himg8 : sh_img_sub Q8)
      by (unfold Q8; apply img_store8; [ exact Himg7 | lia ]).
    assert (Hstk8 : uv_stack pt Q8 sp0 64)
      by (unfold Q8; apply stack_store8; exact Hstk7).
    (* ---- the frame, read back ---- *)
    destruct (spill8_facts M Q8 (uint sp0 - 64)
                (mA !!! Regidx ra_idx) (mA !!! Regidx s0_idx)
                (mA !!! Regidx s1_idx) (mA !!! Regidx s2_idx)
                (mA !!! Regidx s3_idx) (mA !!! Regidx s4_idx)
                (mA !!! Regidx s5_idx) (mA !!! Regidx s6_idx) eq_refl)
      as (Hf0 & Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hfout & Hfdom).
    assert (Honly8 : uM_only M Q8 (uint sp0 - 64) 64).
    { split; [ exact Hfdom | ]. intros k Hk. apply Hfout. lia. }
    assert (Hok8 : lex_ok Q8 sp0 s0 bs)
      by exact (lex_ok_below M Q8 sp0 s0 bs (uint sp0 - 64) 64 Honly8
                  ltac:(lia) ltac:(lia) Hokm).
    assert (Hslots8 : gt_slots Q8 m sp0).
    { split_and!;
        [ apply (uM_bytes_val Q8 (uint sp0 - 8) (mA !!! Regidx ra_idx))
        | apply (uM_bytes_val Q8 (uint sp0 - 16) (mA !!! Regidx s0_idx))
        | apply (uM_bytes_val Q8 (uint sp0 - 24) (mA !!! Regidx s1_idx))
        | apply (uM_bytes_val Q8 (uint sp0 - 32) (mA !!! Regidx s2_idx))
        | apply (uM_bytes_val Q8 (uint sp0 - 40) (mA !!! Regidx s3_idx))
        | apply (uM_bytes_val Q8 (uint sp0 - 48) (mA !!! Regidx s4_idx))
        | apply (uM_bytes_val Q8 (uint sp0 - 56) (mA !!! Regidx s5_idx))
        | apply (uM_bytes_val Q8 (uint sp0 - 64) (mA !!! Regidx s6_idx)) ];
        try (apply HpresA; vm_compute; discriminate);
        intros j Hj;
        [ replace (uint sp0 - 8 + Z.of_nat j)
            with (uint sp0 - 64 + 56 + Z.of_nat j) by lia; exact (Hf0 j Hj)
        | replace (uint sp0 - 16 + Z.of_nat j)
            with (uint sp0 - 64 + 48 + Z.of_nat j) by lia; exact (Hf1 j Hj)
        | replace (uint sp0 - 24 + Z.of_nat j)
            with (uint sp0 - 64 + 40 + Z.of_nat j) by lia; exact (Hf2 j Hj)
        | replace (uint sp0 - 32 + Z.of_nat j)
            with (uint sp0 - 64 + 32 + Z.of_nat j) by lia; exact (Hf3 j Hj)
        | replace (uint sp0 - 40 + Z.of_nat j)
            with (uint sp0 - 64 + 24 + Z.of_nat j) by lia; exact (Hf4 j Hj)
        | replace (uint sp0 - 48 + Z.of_nat j)
            with (uint sp0 - 64 + 16 + Z.of_nat j) by lia; exact (Hf5 j Hj)
        | replace (uint sp0 - 56 + Z.of_nat j)
            with (uint sp0 - 64 + 8 + Z.of_nat j) by lia; exact (Hf6 j Hj)
        | replace (uint sp0 - 64 + Z.of_nat j)
            with (uint sp0 - 64 + 0 + Z.of_nat j) by lia; exact (Hf7 j Hj) ]. }
    (* ---- 0x322  c.addi4spn s0,sp,64 ---- *)
    assert (Hw64 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (mA !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi4spn_imm (mword_of_int 16 : mword 8)))).
    { assert (Hs : mA !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64)) by exact HspA.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh Q8 mA (mword_of_int 0x322)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_322 pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw64
              with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    set (mB := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> mA).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x322 : mword 64) 2
                      = mword_of_int 0x324)) in "Hpc".
    (* ---- 0x324  c.mv s4,a0 ---- *)
    assert (Ha0B : mB !!! Regidx a0_idx = (mword_of_int psaddr : mword 64)).
    { rewrite (upd_ne mA (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresA a0_idx ltac:(vm_compute; discriminate)). exact Hps. }
    iApply (wp_uv_cmv C pt Psh Q8 mB (mword_of_int 0x324)
              s4_idx a0_idx (mword_of_int psaddr)
              (ui_sh_324 pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0B; symmetry; apply moi_add_zero_l)
              with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    set (mC := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int psaddr : mword 64)]> mB).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x324 : mword 64) 2
                      = mword_of_int 0x326)) in "Hpc".
    (* ---- 0x326  c.mv s2,a1 ---- *)
    assert (Ha1C : mC !!! Regidx a1_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne mB (Regidx s4_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresA a1_idx ltac:(vm_compute; discriminate)). exact Hes. }
    iApply (wp_uv_cmv C pt Psh Q8 mC (mword_of_int 0x326)
              s2_idx a1_idx (mword_of_int (s0 + Z.of_nat (length bs)))
              (ui_sh_326 pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1C; symmetry; apply moi_add_zero_l)
              with "Hcg Hpc").
    iIntros (CID12) "Hcg Hpc".
    set (mD := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)]> mC).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x326 : mword 64) 2
                      = mword_of_int 0x328)) in "Hpc".
    (* ---- 0x328  c.mv s5,a2 ---- *)
    assert (Ha2D : mD !!! Regidx a2_idx = (mword_of_int qaddr : mword 64)).
    { rewrite (upd_ne mC (Regidx s2_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresA a2_idx ltac:(vm_compute; discriminate)). exact Hqr. }
    iApply (wp_uv_cmv C pt Psh Q8 mD (mword_of_int 0x328)
              s5_idx a2_idx (mword_of_int qaddr)
              (ui_sh_328 pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2D; symmetry; apply moi_add_zero_l)
              with "Hcg Hpc").
    iIntros (CID13) "Hcg Hpc".
    set (mE0 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int qaddr : mword 64)]> mD).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x328 : mword 64) 2
                      = mword_of_int 0x32a)) in "Hpc".
    (* ---- 0x32a  c.mv s6,a3 ---- *)
    assert (Ha3E : mE0 !!! Regidx a3_idx = (mword_of_int eqaddr : mword 64)).
    { rewrite (upd_ne mD (Regidx s5_idx) (Regidx a3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx a3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx a3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx a3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresA a3_idx ltac:(vm_compute; discriminate)). exact Heqr. }
    iApply (wp_uv_cmv C pt Psh Q8 mE0 (mword_of_int 0x32a)
              s6_idx a3_idx (mword_of_int eqaddr)
              (ui_sh_32a pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha3E; symmetry; apply moi_add_zero_l)
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    set (mF2 := <[Regidx s6_idx
                  := regval_into_reg (mword_of_int eqaddr : mword 64)]> mE0).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x32a : mword 64) 2
                      = mword_of_int 0x32c)) in "Hpc".
    (* ---- 0x32c  c.ld s1,0(a0) ---- *)
    assert (Ha0F : mF2 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64)).
    { rewrite (upd_ne mE0 (Regidx s6_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha0B. }
    assert (Hvaps : (mword_of_int psaddr : mword 64)
                    = add_vec (mF2 !!! Regidx a0_idx)
                        (sign_extend' 64
                           (zero_extend' 12
                              (concat_vec (mword_of_int 0 : mword 5) ('b"000"))))).
    { rewrite Ha0F.
      assert (Hc : (sign_extend' 64
                      (zero_extend' 12
                         (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
                    : mword 64) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    assert (HpsrdQ : uv_rd pt Q8 psaddr 8)
      by exact (uv_rd_dom pt M Q8 psaddr 8 Hfdom Hpsrd).
    assert (HcellQ : uM_bytes Q8 psaddr 8
                       (mword_of_int (s0 + Z.of_nat off) : mword 64)).
    { intros j Hj. rewrite (Hfout (psaddr + Z.of_nat j) ltac:(lia)).
      exact (Hcell j Hj). }
    destruct (uv_slot8_facts psaddr (mword_of_int psaddr) ltac:(lia) Hpsal
                ltac:(lia) eq_refl) as (Hups & Hcanps & Hpgps & Halps).
    destruct (uv_rd_leaf_at pt Q8 psaddr 8 psaddr HpsrdQ ltac:(lia))
      as (wps & Hlps & Hokps).
    iApply (wp_uv_cld C pt Psh Q8 mF2 (mword_of_int 0x32c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx
              wps (mword_of_int psaddr) (mword_of_int (s0 + Z.of_nat off))
              (ui_sh_32c pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hvaps Hlps Hokps Hcanps Hpgps Halps
              ltac:(rewrite Hups; exact HcellQ)
              with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    set (mG2 := <[Regidx s1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat off) : mword 64)]> mF2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x32c : mword 64) 2
                      = mword_of_int 0x32e)) in "Hpc".
    (* ---- 0x32e  auipc s3,0x2 ---- *)
    iApply (wp_uv_auipc C pt Psh Q8 mG2 (mword_of_int 0x32e)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x232e)
              (ui_sh_32e pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CID16) "Hcg Hpc".
    set (mH2 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int 0x232e : mword 64)]> mG2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x32e : mword 64) 4
                      = mword_of_int 0x332)) in "Hpc".
    (* ---- 0x332  addi s3,s3,-806 ---- *)
    assert (Hs3H : mH2 !!! Regidx s3_idx = (mword_of_int 0x232e : mword 64))
      by exact (upd_eq mG2 (Regidx s3_idx) _).
    iApply (wp_uv_addi C pt Psh Q8 mH2 (mword_of_int 0x332)
              (mword_of_int 3290 : mword 12) s3_idx s3_idx
              (mword_of_int SH_WHITESPACE)
              (ui_sh_332 pt Q8 Hltext (sh_img_text Q8 Himg8))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3H;
                    rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                             : (sign_extend' 64 (mword_of_int 3290 : mword 12)
                                : mword 64) = mword_of_int (-806));
                    rewrite moi_add; unfold SH_WHITESPACE, SH_DATA_PG;
                    f_equal; lia)
              with "Hcg Hpc").
    iIntros (CID17) "Hcg Hpc".
    set (mI2 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int SH_WHITESPACE : mword 64)]> mH2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x332 : mword 64) 4
                      = mword_of_int 0x336)) in "Hpc".
    (* the register file entering the first scan *)
    assert (HpresI : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s6_idx ->
              mI2 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp N0 N1 N2 N3 N4 N5 N6.
      rewrite (upd_ne mH2 (Regidx s3_idx) (Regidx r) _ N3).
      rewrite (upd_ne mG2 (Regidx s3_idx) (Regidx r) _ N3).
      rewrite (upd_ne mF2 (Regidx s1_idx) (Regidx r) _ N1).
      rewrite (upd_ne mE0 (Regidx s6_idx) (Regidx r) _ N6).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx r) _ N5).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx r) _ N2).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx r) _ N4).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx r) _ N0).
      exact (HpresA r Nsp). }
    assert (Hpres0 : gt_pres mI2 m)
      by (intros r _ Nsp N0 N1 N2 N3 N4 N5 N6;
          exact (HpresI r Nsp N0 N1 N2 N3 N4 N5 N6)).
    assert (Hs1I : mI2 !!! Regidx s1_idx
                   = (mword_of_int (s0 + Z.of_nat off) : mword 64)).
    { rewrite (upd_ne mH2 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mG2 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mF2 (Regidx s1_idx) _). }
    assert (Hs2I : mI2 !!! Regidx s2_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne mH2 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mG2 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF2 (Regidx s1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s6_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mC (Regidx s2_idx) _). }
    assert (Hs3I : mI2 !!! Regidx s3_idx
                   = (mword_of_int SH_WHITESPACE : mword 64))
      by exact (upd_eq mH2 (Regidx s3_idx) _).
    assert (Hs4I : mI2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64)).
    { rewrite (upd_ne mH2 (Regidx s3_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mG2 (Regidx s3_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF2 (Regidx s1_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s6_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mB (Regidx s4_idx) _). }
    assert (Hs5I : mI2 !!! Regidx s5_idx = (mword_of_int qaddr : mword 64)).
    { rewrite (upd_ne mH2 (Regidx s3_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mG2 (Regidx s3_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF2 (Regidx s1_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s6_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mD (Regidx s5_idx) _). }
    assert (Hs6I : mI2 !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64)).
    { rewrite (upd_ne mH2 (Regidx s3_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mG2 (Regidx s3_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF2 (Regidx s1_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE0 (Regidx s6_idx) _). }
    assert (Ha1I : mI2 !!! Regidx a1_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (HpresI a1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hes. }
    assert (HspI : mI2 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne mH2 (Regidx s3_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mG2 (Regidx s3_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mF2 (Regidx s1_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE0 (Regidx s6_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mD (Regidx s5_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mC (Regidx s2_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mB (Regidx s4_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mA (Regidx s0_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)). exact HspA. }
    (* ---- 0x336..0x34c  the leading whitespace scan ---- *)
    iApply (wp_sh_wsskip CID17 0x336 (mword_of_int 1858) a1_idx
              Q8 mI2 sp0 s0 bs off
              Hlay Hok8 Hfr0 Hs0p Hbufhi Hoff
              (fun Mx Hx => ui_sh_336 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_33a pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_33e pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_340 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_344 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_346 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_348 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_34c pt Mx Hltext Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hsstrchr; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hsstrchr; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Ha1I Hs1I Hs2I Hs3I HspI
              with "Hcg Hpc").
    iIntros (CID18 mJ2 MJ) "%Hs1J %HpresJ %HonlyJ Hcg Hpc".
    assert (HokJ : lex_ok MJ sp0 s0 bs)
      by exact (lex_ok_below Q8 MJ sp0 s0 bs (uint sp0 - 80) 16 HonlyJ
                  ltac:(lia) ltac:(lia) Hok8).
    assert (HslotsJ : gt_slots MJ m sp0)
      by (apply (gt_slots_eq Q8 MJ m sp0);
          [ intros k Hk; apply (proj2 HonlyJ); lia | exact Hslots8 ]).
    assert (HwrJ : uv_wr pt MJ psaddr 8).
    { apply (uv_wr_dom pt Q8 MJ psaddr 8); [ exact (proj1 HonlyJ) | ].
      exact (uv_wr_dom pt M Q8 psaddr 8 Hfdom Hcellw). }
    assert (Hs1J' : mJ2 !!! Regidx s1_idx
                    = (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64))
      by exact Hs1J.
    assert (Hs2J : mJ2 !!! Regidx s2_idx
                   = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (HpresJ s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs2I).
    assert (Hs4J : mJ2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (HpresJ s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4I).
    assert (Hs5J : mJ2 !!! Regidx s5_idx = (mword_of_int qaddr : mword 64))
      by (rewrite (HpresJ s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs5I).
    assert (Hs6J : mJ2 !!! Regidx s6_idx = (mword_of_int eqaddr : mword 64))
      by (rewrite (HpresJ s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs6I).
    assert (HspJ : mJ2 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (HpresJ sp_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact HspI).
    assert (HpresJ' : gt_pres mJ2 m).
    { intros r Hr Nsp N0 N1 N2 N3 N4 N5 N6.
      rewrite (HpresJ r Hr N1). exact (HpresI r Nsp N0 N1 N2 N3 N4 N5 N6). }
    assert (HeqwJ : eqaddr = 0 \/ (uv_wr pt MJ eqaddr 8 /\ eqaddr mod 8 = 0 /\
                                   uint sp0 <= eqaddr /\ eqaddr + 8 <= 2 ^ 38)).
    { destruct Heqw as [H0 | (Hw & Ha & Hb & Hc)]; [ by left | right ].
      split_and!; try assumption.
      apply (uv_wr_dom pt Q8 MJ eqaddr 8); [ exact (proj1 HonlyJ) | ].
      exact (uv_wr_dom pt M Q8 eqaddr 8 Hfdom Hw). }
    (* ---- 0x34e  beqz s5,0x356 -- [if (q) *q = s] ---- *)
    destruct (decide (qaddr = 0)) as [Hq0 | Hqnz].
    - (* q == NULL: nothing is written ---- *)
      assert (Htk : true = uv_btaken BEQ (mJ2 !!! Regidx s5_idx)
                             zero_reg).
      { cbn [uv_btaken]. rewrite Hs5J Hq0.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uv_btype0 C pt Psh MJ mJ2 (mword_of_int 0x34e)
                (mword_of_int 8 : mword 13) s5_idx BEQ
                true (mword_of_int 0x356)
                (ui_sh_34e pt MJ Hltext (sh_img_text MJ (proj1 HokJ))) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID19) "Hcg Hpc".
      iApply (wp_sh_gt_from356 CID19 MJ mJ2 m sp0 psaddr eqaddr s0 bs
                (off + kk)%nat
                Hlay HokJ Hnosym Hfr0 Hs0p Hbufhi Hkk Hnwq Hret2 Hsp
                HwrJ Hpsal Hpshi Hpshi2 HeqwJ Hdis2
                HspJ Hs1J' Hs2J Hs4J Hs6J HslotsJ HpresJ'
                with "Hcg Hpc [Hcont]").
      iIntros (CID20 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
      iApply ("Hcont" $! CID20 m' M' with "[] [] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0'.
      + iPureIntro. intro Hc'. exfalso. exact (Hc' Hq0).
      + iPureIntro. exact Hceq.
      + iPureIntro. exact Hcell'.
      + iPureIntro.
        apply (uM_only_in_trans M Q8 M').
        * apply (uM_only_in_of_only M Q8 (uint sp0 - 80) 80).
          -- exact (uM_only_widen M Q8 (uint sp0 - 64) 64 (uint sp0 - 80) 80
                      Honly8 ltac:(lia) ltac:(lia)).
          -- apply elem_of_list_further. apply elem_of_list_further.
             apply elem_of_list_further. apply elem_of_list_here.
        * apply (uM_only_in_trans Q8 MJ M').
          -- apply (uM_only_in_of_only Q8 MJ (uint sp0 - 80) 80).
             ++ exact (uM_only_widen Q8 MJ (uint sp0 - 80) 16 (uint sp0 - 80) 80
                         HonlyJ ltac:(lia) ltac:(lia)).
             ++ apply elem_of_list_further. apply elem_of_list_further.
                apply elem_of_list_further. apply elem_of_list_here.
          -- apply (uM_only_in_weaken MJ M'
                      [(psaddr, 8); (eqaddr, 8); (uint sp0 - 80, 80)]);
               [ exact Honly' | ].
             intros x Hx. apply elem_of_cons in Hx as [-> | Hx].
             ++ apply elem_of_list_here.
             ++ apply elem_of_cons in Hx as [-> | Hx].
                ** apply elem_of_list_further. apply elem_of_list_further.
                   apply elem_of_list_here.
                ** apply elem_of_list_singleton in Hx. subst x.
                   apply elem_of_list_further. apply elem_of_list_further.
                   apply elem_of_list_further. apply elem_of_list_here.
    - (* q != NULL: store the token's start ---- *)
      destruct Hqw as [Hc0 | (Hqwr & Hqal & Hqhi & Hqhi2)];
        [ exfalso; exact (Hqnz Hc0) | ].
      assert (HqwrJ : uv_wr pt MJ qaddr 8).
      { apply (uv_wr_dom pt Q8 MJ qaddr 8); [ exact (proj1 HonlyJ) | ].
        exact (uv_wr_dom pt M Q8 qaddr 8 Hfdom Hqwr). }
      pose proof (uwr_lo _ _ _ _ HqwrJ) as Hqlo.
      pose proof Hqhi2 as Hqhi2'. change (2 ^ 38) with 274877906944 in Hqhi2'.
      assert (HdisQP : qaddr + 8 <= psaddr \/ psaddr + 8 <= qaddr)
        by (destruct Hdis1 as [Hc0 | Hd]; [ exfalso; exact (Hqnz Hc0) | exact Hd ]).
      assert (HdisQE : eqaddr = 0 \/ qaddr + 8 <= eqaddr \/ eqaddr + 8 <= qaddr)
        by (destruct Hdis3 as [Hc0 | [Hc1 | Hd]];
            [ exfalso; exact (Hqnz Hc0) | by left | by right ]).
      assert (Htk : false = uv_btaken BEQ (mJ2 !!! Regidx s5_idx)
                              zero_reg).
      { cbn [uv_btaken]. rewrite Hs5J.
        rewrite (moi_eq_zero qaddr ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact Hqnz. }
      iApply (wp_uv_btype0 C pt Psh MJ mJ2 (mword_of_int 0x34e)
                (mword_of_int 8 : mword 13) s5_idx BEQ
                false (mword_of_int 0x356)
                (ui_sh_34e pt MJ Hltext (sh_img_text MJ (proj1 HokJ))) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID19) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : (if false then (mword_of_int 0x356 : mword 64)
                         else add_vec_int (mword_of_int 0x34e : mword 64) 4)
                        = mword_of_int 0x352)) in "Hpc".
      (* ---- 0x352  sd s1,0(s5) ---- *)
      destruct (uv_slot8_facts qaddr (mword_of_int qaddr) ltac:(lia) Hqal
                  ltac:(lia) eq_refl) as (Huq & Hcanq & Hpgq & Halq).
      assert (Hvaq : (mword_of_int qaddr : mword 64)
                     = add_vec (mJ2 !!! Regidx s5_idx)
                         (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite Hs5J.
        assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                     = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal; lia. }
      destruct (uwr_leaf _ _ _ _ HqwrJ 0 ltac:(lia)) as (wq & Hlq & Hokq).
      rewrite Z.add_0_r in Hlq.
      iApply (wp_uv_sd C pt Psh MJ mJ2 (mword_of_int 0x352)
                (mword_of_int 0 : mword 12) s5_idx s1_idx
                wq (mword_of_int qaddr)
                (mword_of_int (s0 + Z.of_nat (off + kk)))
                (ui_sh_352 pt MJ Hltext (sh_img_text MJ (proj1 HokJ)))
                Hvaq (eq_sym Hs1J') Hlq Hokq Hcanq Hpgq Halq
                ltac:(rewrite Huq; intros j Hj;
                      exact (uwr_bytes _ _ _ _ HqwrJ (Z.of_nat j) ltac:(lia)))
                with "Hcg Hpc").
      iIntros (CID20) "Hcg Hpc".
      iEval (rewrite Huq) in "Hcg".
      set (MQ := uM_store8 MJ qaddr
                   (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64)).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x352 : mword 64) 4
                        = mword_of_int 0x356)) in "Hpc".
      assert (HonlyQ : uM_only MJ MQ qaddr 8).
      { split.
        - intros k Hk. exact (uM_store8_is_Some MJ qaddr _ k Hk).
        - intros k Hk. exact (um_st8_ne MJ qaddr _ k Hk). }
      assert (HcellQq : uM_bytes MQ qaddr 8
                          (mword_of_int (s0 + Z.of_nat (off + kk)) : mword 64))
        by exact (uM_store8_bytes MJ qaddr _).
      assert (HokQ : lex_ok MQ sp0 s0 bs)
        by exact (lex_ok_below MJ MQ sp0 s0 bs qaddr 8 HonlyQ
                    ltac:(lia) ltac:(lia) HokJ).
      assert (HwrQ : uv_wr pt MQ psaddr 8)
        by exact (uv_wr_dom pt MJ MQ psaddr 8 (proj1 HonlyQ) HwrJ).
      assert (HeqwQ : eqaddr = 0 \/ (uv_wr pt MQ eqaddr 8 /\ eqaddr mod 8 = 0 /\
                                     uint sp0 <= eqaddr /\ eqaddr + 8 <= 2 ^ 38)).
      { destruct HeqwJ as [H0 | (Hw & Ha & Hb & Hc)]; [ by left | right ].
        split_and!; try assumption.
        exact (uv_wr_dom pt MJ MQ eqaddr 8 (proj1 HonlyQ) Hw). }
      assert (HslotsQ : gt_slots MQ m sp0)
        by (apply (gt_slots_eq MJ MQ m sp0);
            [ intros k Hk; unfold MQ; apply um_st8_ne; lia | exact HslotsJ ]).
      iApply (wp_sh_gt_from356 CID20 MQ mJ2 m sp0 psaddr eqaddr s0 bs
                (off + kk)%nat
                Hlay HokQ Hnosym Hfr0 Hs0p Hbufhi Hkk Hnwq Hret2 Hsp
                HwrQ Hpsal Hpshi Hpshi2 HeqwQ Hdis2
                HspJ Hs1J' Hs2J Hs4J Hs6J HslotsQ HpresJ'
                with "Hcg Hpc [Hcont]").
      iIntros (CID21 m' M') "%Hcs %Ha0' %Hceq %Hcell' %Honly' Hcg Hpc".
      iApply ("Hcont" $! CID21 m' M' with "[] [] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0'.
      + iPureIntro. intros _. intros j Hj.
        rewrite (proj2 Honly' (qaddr + Z.of_nat j)
                   ltac:(intros (w & Hw & Hin);
                         apply elem_of_cons in Hw as [-> | Hw];
                         [ simpl in Hin; lia | ];
                         apply elem_of_cons in Hw as [-> | Hw];
                         [ simpl in Hin;
                           destruct HdisQE as [He | Hd];
                           [ lia | lia ] | ];
                         apply elem_of_list_singleton in Hw; subst w;
                         simpl in Hin; lia)).
        exact (HcellQq j Hj).
      + iPureIntro. exact Hceq.
      + iPureIntro. exact Hcell'.
      + iPureIntro.
        apply (uM_only_in_trans M Q8 M').
        * apply (uM_only_in_of_only M Q8 (uint sp0 - 80) 80).
          -- exact (uM_only_widen M Q8 (uint sp0 - 64) 64 (uint sp0 - 80) 80
                      Honly8 ltac:(lia) ltac:(lia)).
          -- apply elem_of_list_further. apply elem_of_list_further.
             apply elem_of_list_further. apply elem_of_list_here.
        * apply (uM_only_in_trans Q8 MJ M').
          -- apply (uM_only_in_of_only Q8 MJ (uint sp0 - 80) 80).
             ++ exact (uM_only_widen Q8 MJ (uint sp0 - 80) 16 (uint sp0 - 80) 80
                         HonlyJ ltac:(lia) ltac:(lia)).
             ++ apply elem_of_list_further. apply elem_of_list_further.
                apply elem_of_list_further. apply elem_of_list_here.
          -- apply (uM_only_in_trans MJ MQ M').
             ++ apply (uM_only_in_of_only MJ MQ qaddr 8); [ exact HonlyQ | ].
                apply elem_of_list_further. apply elem_of_list_here.
             ++ apply (uM_only_in_weaken MQ M'
                         [(psaddr, 8); (eqaddr, 8); (uint sp0 - 80, 80)]);
                  [ exact Honly' | ].
                intros x Hx. apply elem_of_cons in Hx as [-> | Hx].
                ** apply elem_of_list_here.
                ** apply elem_of_cons in Hx as [-> | Hx].
                   --- apply elem_of_list_further. apply elem_of_list_further.
                       apply elem_of_list_here.
                   --- apply elem_of_list_singleton in Hx. subst x.
                       apply elem_of_list_further. apply elem_of_list_further.
                       apply elem_of_list_further. apply elem_of_list_here.
  Qed.

End UProofShLex.
