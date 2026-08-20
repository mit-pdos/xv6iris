(* UProofShParse.v -- the VERIFIED-EXECUTION proofs of `sh''s RECURSIVE-DESCENT
   PARSER (claude-notes/projects/user-sh.md):

     wp_sh_parseredirs  parseredirs @0x4ac  112-byte frame, ra + s0..s9
     wp_sh_parseexec    parseexec   @0x590  128-byte frame, the arg LOOP
     wp_sh_parsepipe    parsepipe   @0x682   48-byte frame
     wp_sh_parseline    parseline   @0x6e2   48-byte frame

   All four discharge USpecShParse.v's contracts AS THEY STAND.

   THE SHAPE.  On this input the buffer has no `<|>&;()' ([sh_no_symbols]),
   so every one of the six [peek] calls in these four functions returns 0:
   §2's [peek_ret_0] is that argument, and [wp_sh_peek_zero] is the one
   call-site wrapper the six share.  That is what keeps [parseredirs]' loop,
   [parsepipe]'s [pipecmd] arm and [parseline]'s [backcmd] / [listcmd] arms
   out of reach -- and [parseexec]'s [parseblock] arm with them, so the
   parser recurses no further than [parseexec].

   [parseexec] is the only one that does work: [execcmd] (hence the run's
   single [malloc]), [parseredirs], and then the argument loop, whose
   invariant is literally the [ShTokCons] constructor of USpecShParse's
   [sh_tokens] -- the loop is a plain Rocq induction on the length of the
   REMAINING token list (a BOUNDED loop, so no [iLob] and no [>]; see
   claude-notes/projects/user-echo.md).

   ==================================================================
   TWO CONTRACT DEFECTS THIS PROOF FOUND.  Both are FIXED in the specs;
   recorded here for the shape, which is the part that recurs.
   ==================================================================

   (D6) [wp_sh_execcmd_body] / [wp_sh_malloc_first_body] carried
     [Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88].  That range is
     0x2010..0x2098 and so COVERS `buf.0' at 0x2020 -- it asserted the
     command buffer was all zeros, which is false at the one site that
     calls malloc ([parseexec], after [gets] filled the buffer).  The
     premise is satisfiable in isolation, so the callee's own proof and
     its [Print Assumptions] are both clean; only the CALLER ever finds
     it.  malloc reads exactly two windows -- freep (offsets 0..8) and
     the top eight bytes of `base' (128..136) -- and those two are what
     the contracts now carry.

   (D7) [wp_sh_parse_body]'s postcondition said nothing about where the
     parse left [*ps].  [uM_only_in] gives the cell's bytes are still
     PRESENT, never what they SPELL, and a value recovered with [uM_word]
     cannot be put in [peek]'s required [s0 + Z.of_nat off] form -- so
     [parsepipe] and [parseline] could not run the [peek] they do next,
     and neither could [parsecmd].  The conjunct now states the exact
     truth: on a buffer with no symbol bytes the parse always stops at
     the END, so the cell holds [s0 + |bs|].

   Every instruction is one application of a leaf from WpUmodeLeaf.v /
   WpUmodeBranch.v / WpUmodeStore.v / WpUmodeLoad.v fed the matching
   [ui_sh_<hexpc>] fact from UCodeSh.v; the frames are built one slot at a
   time out of UmodeFrame.v's [wp_uv_frame_store] / [wp_uv_frame_load],
   because the spill SETS differ (ra+s0..s9 / ra+s0,s1,s4,s5 then
   s2,s3,s6..s11 / ra+s0..s4) and a per-size prologue lemma would have to
   fix the register list too. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import RiscvModelBytes.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeArith UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeSh USpecSh USpecShParse.
Require Import UProofShHeap UProofShLex.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
(* re-imported LAST on purpose: WpUmodeStep.v's funnel names its optional
   gpr write [uv_wr], which otherwise shadows UmodeAbi's writable-window
   record of the same name. *)
Require Import UmodeAbi.
Require User.ShSyms User.ShInstrs User.ShData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 THE TOKEN TABLES, and why every [peek] on this input returns 0.     *)
(*                                                                        *)
(* Each [peek] call site hands a NUL-terminated string of SYMBOL bytes     *)
(* out of .rodata; [sh_no_symbols] says the buffer contains none of them,  *)
(* so the byte the whitespace skip stops on is never in the table.  The    *)
(* six tables are named here as pure byte lists.                          *)
(* ===================================================================== *)

Definition sh_tb_lt   : list (bv 8) := sh_bytes [60; 62].       (* "<>"   *)
Definition sh_tb_lp   : list (bv 8) := sh_bytes [40].           (* "("    *)
Definition sh_tb_end  : list (bv 8) := sh_bytes [124; 41; 38; 59]. (* "|)&;" *)
Definition sh_tb_pipe : list (bv 8) := sh_bytes [124].          (* "|"    *)
Definition sh_tb_amp  : list (bv 8) := sh_bytes [38].           (* "&"    *)
Definition sh_tb_semi : list (bv 8) := sh_bytes [59].           (* ";"    *)

(* the byte the skip stops on is not in a table of symbol bytes, so the
   [strchr] guarding [peek]'s return fails and the call returns 0 *)
Lemma peek_ret_0 (bs : list (bv 8)) (off : nat) (tbs : list (bv 8)) :
  sh_no_symbols bs ->
  (forall b : bv 8, b ∈ tbs -> sh_is_sym b = true) ->
  sh_peek_ret bs off tbs = 0.
Proof.
  intros Hns Hsym. unfold sh_peek_ret. cbn zeta.
  destruct (drop (off + sh_skipws (drop off bs)) bs !! 0%nat) as [ b | ] eqn:E;
    [ | reflexivity ].
  destruct (bool_decide_reflect (b ∈ tbs)) as [ Hin | _ ]; [ | reflexivity ].
  exfalso.
  rewrite lookup_drop Nat.add_0_r in E.
  pose proof (Hsym b Hin) as Ht. rewrite (Hns _ b E) in Ht. discriminate.
Qed.

(* the six tables' bytes really are symbol bytes *)
Lemma sh_tb_lt_sym   : forall b : bv 8, b ∈ sh_tb_lt   -> sh_is_sym b = true.
Proof.
  intros b Hb. unfold sh_tb_lt, sh_bytes in Hb. cbn [fmap list_fmap] in Hb.
  repeat (apply elem_of_cons in Hb as [ -> | Hb ]; [ vm_compute; reflexivity | ]).
  exfalso. exact (not_elem_of_nil _ Hb).
Qed.
Lemma sh_tb_lp_sym   : forall b : bv 8, b ∈ sh_tb_lp   -> sh_is_sym b = true.
Proof.
  intros b Hb. unfold sh_tb_lp, sh_bytes in Hb. cbn [fmap list_fmap] in Hb.
  repeat (apply elem_of_cons in Hb as [ -> | Hb ]; [ vm_compute; reflexivity | ]).
  exfalso. exact (not_elem_of_nil _ Hb).
Qed.
Lemma sh_tb_end_sym  : forall b : bv 8, b ∈ sh_tb_end  -> sh_is_sym b = true.
Proof.
  intros b Hb. unfold sh_tb_end, sh_bytes in Hb. cbn [fmap list_fmap] in Hb.
  repeat (apply elem_of_cons in Hb as [ -> | Hb ]; [ vm_compute; reflexivity | ]).
  exfalso. exact (not_elem_of_nil _ Hb).
Qed.
Lemma sh_tb_pipe_sym : forall b : bv 8, b ∈ sh_tb_pipe -> sh_is_sym b = true.
Proof.
  intros b Hb. unfold sh_tb_pipe, sh_bytes in Hb. cbn [fmap list_fmap] in Hb.
  repeat (apply elem_of_cons in Hb as [ -> | Hb ]; [ vm_compute; reflexivity | ]).
  exfalso. exact (not_elem_of_nil _ Hb).
Qed.
Lemma sh_tb_amp_sym  : forall b : bv 8, b ∈ sh_tb_amp  -> sh_is_sym b = true.
Proof.
  intros b Hb. unfold sh_tb_amp, sh_bytes in Hb. cbn [fmap list_fmap] in Hb.
  repeat (apply elem_of_cons in Hb as [ -> | Hb ]; [ vm_compute; reflexivity | ]).
  exfalso. exact (not_elem_of_nil _ Hb).
Qed.
Lemma sh_tb_semi_sym : forall b : bv 8, b ∈ sh_tb_semi -> sh_is_sym b = true.
Proof.
  intros b Hb. unfold sh_tb_semi, sh_bytes in Hb. cbn [fmap list_fmap] in Hb.
  repeat (apply elem_of_cons in Hb as [ -> | Hb ]; [ vm_compute; reflexivity | ]).
  exfalso. exact (not_elem_of_nil _ Hb).
Qed.

(* ... and no table byte is NUL, which is [peek]'s [Htnz] *)
Lemma sh_tb_nz (tbs : list (bv 8)) :
  (forall b : bv 8, b ∈ tbs -> sh_is_sym b = true) ->
  forall (j : nat) (b : bv 8), tbs !! j = Some b -> b <> ubyte0.
Proof.
  intros Hsym j b Hj He.
  assert (Hin : b ∈ tbs) by (apply (elem_of_list_lookup_2 tbs j b); exact Hj).
  pose proof (Hsym b Hin) as Ht. rewrite He in Ht.
  vm_compute in Ht. discriminate.
Qed.

Lemma sh_tb_lt_len : Z.of_nat (length sh_tb_lt) = 2.
Proof. vm_compute. reflexivity. Qed.
Lemma sh_tb_lp_len : Z.of_nat (length sh_tb_lp) = 1.
Proof. vm_compute. reflexivity. Qed.
Lemma sh_tb_end_len : Z.of_nat (length sh_tb_end) = 4.
Proof. vm_compute. reflexivity. Qed.
Lemma sh_tb_pipe_len : Z.of_nat (length sh_tb_pipe) = 1.
Proof. vm_compute. reflexivity. Qed.
Lemma sh_tb_amp_len : Z.of_nat (length sh_tb_amp) = 1.
Proof. vm_compute. reflexivity. Qed.
Lemma sh_tb_semi_len : Z.of_nat (length sh_tb_semi) = 1.
Proof. vm_compute. reflexivity. Qed.

(* the six tables, verbatim in the dumped .rodata *)
Lemma sh_tb_lt_data   : ustr_at ShData.sh_data 4848 sh_tb_lt.
Proof.
  split; [ | vm_compute; reflexivity ].
  intros j b Hj. destruct j as [ | [ | j ] ]; cbn in Hj; try discriminate;
    injection Hj as <-; vm_compute; reflexivity.
Qed.
Lemma sh_tb_lp_data   : ustr_at ShData.sh_data 4856 sh_tb_lp.
Proof.
  split; [ | vm_compute; reflexivity ].
  intros j b Hj. destruct j as [ | j ]; cbn in Hj; try discriminate;
    injection Hj as <-; vm_compute; reflexivity.
Qed.
Lemma sh_tb_end_data  : ustr_at ShData.sh_data 4888 sh_tb_end.
Proof.
  split; [ | vm_compute; reflexivity ].
  intros j b Hj. destruct j as [ | [ | [ | [ | j ] ] ] ]; cbn in Hj;
    try discriminate; injection Hj as <-; vm_compute; reflexivity.
Qed.
Lemma sh_tb_pipe_data : ustr_at ShData.sh_data 4896 sh_tb_pipe.
Proof.
  split; [ | vm_compute; reflexivity ].
  intros j b Hj. destruct j as [ | j ]; cbn in Hj; try discriminate;
    injection Hj as <-; vm_compute; reflexivity.
Qed.
Lemma sh_tb_amp_data  : ustr_at ShData.sh_data 4904 sh_tb_amp.
Proof.
  split; [ | vm_compute; reflexivity ].
  intros j b Hj. destruct j as [ | j ]; cbn in Hj; try discriminate;
    injection Hj as <-; vm_compute; reflexivity.
Qed.
Lemma sh_tb_semi_data : ustr_at ShData.sh_data 4912 sh_tb_semi.
Proof.
  split; [ | vm_compute; reflexivity ].
  intros j b Hj. destruct j as [ | j ]; cbn in Hj; try discriminate;
    injection Hj as <-; vm_compute; reflexivity.
Qed.

(* ---- the token model's arithmetic ---------------------------------- *)
Lemma sh_skipws_idem (l : list (bv 8)) : sh_skipws (drop (sh_skipws l) l) = 0%nat.
Proof.
  destruct (list_find (fun b : bv 8 => sh_is_ws b = false) l) as [ [i x] | ] eqn:E.
  - assert (Hk : sh_skipws l = i) by (unfold sh_skipws; rewrite E; reflexivity).
    rewrite Hk.
    apply list_find_Some in E as (Hi & HP & _).
    assert (Hd : drop i l !! 0%nat = Some x)
      by (rewrite lookup_drop Nat.add_0_r; exact Hi).
    destruct (drop i l) as [ | y tl ] eqn:Ed; [ discriminate Hd | ].
    cbn in Hd. injection Hd as <-.
    exact (sh_skipws_cons_nws y tl HP).
  - assert (Hk : sh_skipws l = length l)
      by (unfold sh_skipws; rewrite E; reflexivity).
    rewrite Hk drop_all. exact sh_skipws_nil.
Qed.

Lemma sh_skipws_drop_idem (bs : list (bv 8)) (j : nat) :
  sh_skipws (drop (j + sh_skipws (drop j bs))%nat bs) = 0%nat.
Proof. rewrite <- drop_drop. exact (sh_skipws_idem (drop j bs)). Qed.

Lemma sh_tok_cons_gen (bs : list (bv 8)) (off a b : nat)
    (toks : list (nat * nat)) :
  a = (off + sh_skipws (drop off bs))%nat ->
  b = (a + sh_toklen (drop a bs))%nat ->
  (a < b)%nat ->
  sh_tokens bs b toks ->
  sh_tokens bs off ((a, b) :: toks).
Proof.
  intros -> -> Hlt Hrest. apply ShTokCons; [ lia | exact Hrest ].
Qed.

Lemma sh_tokens_nil_inv (bs : list (bv 8)) (off : nat) :
  sh_tokens bs off [] -> (off + sh_skipws (drop off bs))%nat = length bs.
Proof. intro H. inversion H; subst; assumption. Qed.

Lemma sh_tokens_cons_inv (bs : list (bv 8)) (off : nat) (t : nat * nat)
    (toks : list (nat * nat)) :
  sh_tokens bs off (t :: toks) ->
  (0 < sh_toklen (drop (off + sh_skipws (drop off bs))%nat bs))%nat /\
  t = ((off + sh_skipws (drop off bs))%nat,
       (off + sh_skipws (drop off bs)
        + sh_toklen (drop (off + sh_skipws (drop off bs))%nat bs))%nat) /\
  sh_tokens bs (off + sh_skipws (drop off bs)
                + sh_toklen (drop (off + sh_skipws (drop off bs))%nat bs))%nat toks.
Proof.
  intro H. inversion H; subst. split_and!; first [ assumption | reflexivity ].
Qed.

Lemma sh_tokens_shift (bs : list (bv 8)) (j : nat) (toks : list (nat * nat)) :
  sh_tokens bs j toks ->
  sh_tokens bs (j + sh_skipws (drop j bs))%nat toks.
Proof.
  intro H. destruct toks as [ | t toks' ].
  - apply ShTokNil.
    rewrite (sh_skipws_drop_idem bs j) Nat.add_0_r.
    exact (sh_tokens_nil_inv bs j H).
  - destruct (sh_tokens_cons_inv bs j t toks' H) as (Hn & -> & Hrest).
    apply (sh_tok_cons_gen bs (j + sh_skipws (drop j bs))
             (j + sh_skipws (drop j bs))
             (j + sh_skipws (drop j bs)
              + sh_toklen (drop (j + sh_skipws (drop j bs))%nat bs))
             toks').
    + rewrite (sh_skipws_drop_idem bs j). lia.
    + reflexivity.
    + lia.
    + exact Hrest.
Qed.

Lemma sh_toklen_pos_lt (bs : list (bv 8)) (j : nat) :
  (0 < sh_toklen (drop j bs))%nat -> (j < length bs)%nat.
Proof.
  intro H. pose proof (sh_toklen_le (drop j bs)) as Hle.
  rewrite length_drop in Hle. lia.
Qed.

(* The dumped .rodata/.data stops at 0x2010 -- BELOW [freep].  UCodeSh's
   [sh_data_key_lt] rounds that up to the next page (12288), which is too
   coarse here: [parseexec]'s window list disturbs [SH_FREEP] at 8208, and
   the image inclusion has to survive it. *)
Lemma sh_data_key_lt8208 (k : Z) (b : bv 8) :
  ShData.sh_data !! k = Some b -> k < 8208.
Proof.
  intro Hk.
  apply elem_of_list_to_map_2 in Hk.
  apply elem_of_list_In in Hk.
  refine (list_key_lt _ 8208 k b _ Hk).
  vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 WINDOW PLUMBING.  [uM_only_in] over a literal list is the largest    *)
(* single piece of boilerplate these proofs carry; these two are the       *)
(* introduction and elimination rules at the two arities that occur.       *)
(* ===================================================================== *)

Lemma win_out (ws : list (Z * Z)) (a n k : Z) :
  (a, n) ∈ ws -> ~ uM_in_windows ws k -> k < a \/ a + n <= k.
Proof.
  intros Hin Hnot.
  destruct (Z.lt_ge_cases k a) as [ Hlt | Hge ]; [ left; lia | ].
  destruct (Z.lt_ge_cases k (a + n)) as [ Hlt2 | Hge2 ]; [ | right; lia ].
  exfalso. apply Hnot. exists (a, n). split; [ exact Hin | simpl; lia ].
Qed.

Lemma win2_out (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 k : Z) :
  uM_only_in M M' [(a1, n1); (a2, n2)] ->
  (k < a1 \/ a1 + n1 <= k) -> (k < a2 \/ a2 + n2 <= k) ->
  M' !! k = M !! k.
Proof.
  intros [ _ E ] H1 H2. apply E. intros ((a, n) & Hin & Hk). simpl in Hk.
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  exact (not_elem_of_nil _ Hin).
Qed.

Lemma win2_in (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 : Z) :
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
  (forall k : Z, (k < a1 \/ a1 + n1 <= k) -> (k < a2 \/ a2 + n2 <= k) ->
     M' !! k = M !! k) ->
  uM_only_in M M' [(a1, n1); (a2, n2)].
Proof.
  intros Hd He. split; [ exact Hd | ]. intros k Hk. apply He.
  - apply (win_out _ a1 n1 k ltac:(apply elem_of_list_here) Hk).
  - apply (win_out _ a2 n2 k
             ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk).
Qed.

Lemma win5_out (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 a3 n3 a4 n4 a5 n5 k : Z) :
  uM_only_in M M' [(a1,n1); (a2,n2); (a3,n3); (a4,n4); (a5,n5)] ->
  (k < a1 \/ a1 + n1 <= k) -> (k < a2 \/ a2 + n2 <= k) ->
  (k < a3 \/ a3 + n3 <= k) -> (k < a4 \/ a4 + n4 <= k) ->
  (k < a5 \/ a5 + n5 <= k) ->
  M' !! k = M !! k.
Proof.
  intros [ _ E ] H1 H2 H3 H4 H5. apply E.
  intros ((a, n) & Hin & Hk). simpl in Hk.
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  exact (not_elem_of_nil _ Hin).
Qed.

Lemma win5_in (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 a3 n3 a4 n4 a5 n5 : Z) :
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
  (forall k : Z, (k < a1 \/ a1 + n1 <= k) -> (k < a2 \/ a2 + n2 <= k) ->
     (k < a3 \/ a3 + n3 <= k) -> (k < a4 \/ a4 + n4 <= k) ->
     (k < a5 \/ a5 + n5 <= k) -> M' !! k = M !! k) ->
  uM_only_in M M' [(a1,n1); (a2,n2); (a3,n3); (a4,n4); (a5,n5)].
Proof.
  intros Hd He. split; [ exact Hd | ]. intros k Hk. apply He.
  - apply (win_out _ a1 n1 k ltac:(apply elem_of_list_here) Hk).
  - apply (win_out _ a2 n2 k
             ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk).
  - apply (win_out _ a3 n3 k
             ltac:(apply elem_of_list_further; apply elem_of_list_further;
                   apply elem_of_list_here) Hk).
  - apply (win_out _ a4 n4 k
             ltac:(apply elem_of_list_further; apply elem_of_list_further;
                   apply elem_of_list_further; apply elem_of_list_here) Hk).
  - apply (win_out _ a5 n5 k
             ltac:(apply elem_of_list_further; apply elem_of_list_further;
                   apply elem_of_list_further; apply elem_of_list_further;
                   apply elem_of_list_here) Hk).
Qed.

Lemma win4_out (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 a3 n3 a4 n4 k : Z) :
  uM_only_in M M' [(a1,n1); (a2,n2); (a3,n3); (a4,n4)] ->
  (k < a1 \/ a1 + n1 <= k) -> (k < a2 \/ a2 + n2 <= k) ->
  (k < a3 \/ a3 + n3 <= k) -> (k < a4 \/ a4 + n4 <= k) ->
  M' !! k = M !! k.
Proof.
  intros [ _ E ] H1 H2 H3 H4. apply E.
  intros ((a, n) & Hin & Hk). simpl in Hk.
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
  exact (not_elem_of_nil _ Hin).
Qed.

(* ---- one 8-byte store, at the granularity every frame slot uses ------ *)

Lemma um8_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  (k < a \/ a + 8 <= k) -> uM_store8 M a v !! k = M !! k.
Proof. intro H. apply uM_store8_lookup_ne. intros j Hj. lia. Qed.

Lemma only_step8 (M Mk : gmap Z (bv 8)) (lo a n : Z) (v : mword 64) :
  lo <= a -> a + 8 <= lo + n ->
  uM_only M Mk lo n -> uM_only M (uM_store8 Mk a v) lo n.
Proof.
  intros H1 H2 (Hd & Ho). split.
  - intros k Hk. apply uM_store8_is_Some. exact (Hd k Hk).
  - intros k Hk. rewrite (um8_ne Mk a v k ltac:(lia)). exact (Ho k Hk).
Qed.

Lemma st8_bytes_ne (M : gmap Z (bv 8)) (a b : Z) (v w : mword 64) :
  (b + 8 <= a \/ a + 8 <= b) ->
  uM_bytes M a 8 v -> uM_bytes (uM_store8 M b w) a 8 v.
Proof.
  intros Hd Hby j Hj.
  rewrite (um8_ne M b w (a + Z.of_nat j) ltac:(lia)). exact (Hby j Hj).
Qed.

Lemma bytes_eq8 (M M' : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  (forall k : Z, a <= k < a + 8 -> M' !! k = M !! k) ->
  uM_bytes M a 8 v -> uM_bytes M' a 8 v.
Proof.
  intros Heq Hb j Hj. rewrite (Heq (a + Z.of_nat j) ltac:(lia)). exact (Hb j Hj).
Qed.

Lemma bytes_eqk {n : N} (M M' : gmap Z (bv 8)) (a : Z) (k : nat) (v : bv n) :
  (forall j : Z, a <= j < a + Z.of_nat k -> M' !! j = M !! j) ->
  uM_bytes M a k v -> uM_bytes M' a k v.
Proof.
  intros Heq Hb j Hj. rewrite (Heq (a + Z.of_nat j) ltac:(lia)). exact (Hb j Hj).
Qed.

Lemma word_of_bytes8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_bytes M a 8 v -> uM_word M a 8 = v.
Proof.
  intro Hb. apply (uM_bytes_inj M a); [ | exact Hb ].
  exact (uM_word_bytes M a 8 ltac:(lia) (uM_bytes_exists M a 8 v Hb)).
Qed.

(* the image survives a store above the dumped data *)
Lemma img_store8 (Mx : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_img_sub Mx -> 8208 <= a -> sh_img_sub (uM_store8 Mx a v).
Proof.
  intros (Ht & Hd) Ha. split.
  - intros k b Hk.
    rewrite (um8_ne Mx a v k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
    exact (Ht k b Hk).
  - intros k b Hk.
    rewrite (um8_ne Mx a v k ltac:(pose proof (sh_data_key_lt8208 k b Hk); lia)).
    exact (Hd k b Hk).
Qed.

(* the image predicates, across an image that only moved at or above [a] *)
Lemma only_img (M M' : gmap Z (bv 8)) (a n : Z) :
  uM_only M M' a n -> 12288 <= a -> sh_img_sub M -> sh_img_sub M'.
Proof.
  intros (Hd & Ho) Ha (Ht & Hda). split.
  - intros k b Hk.
    rewrite (Ho k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
    exact (Ht k b Hk).
  - intros k b Hk.
    rewrite (Ho k ltac:(pose proof (sh_data_key_lt k b Hk); lia)).
    exact (Hda k b Hk).
Qed.

(* ===================================================================== *)
(* §3 THE PARSER.                                                         *)
(* ===================================================================== *)

Section UProofShParse.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx  := (mword_of_int 8  : mword 5).
  Local Notation s1_idx  := (mword_of_int 9  : mword 5).
  Local Notation a4_idx  := (mword_of_int 14 : mword 5).
  Local Notation a5_idx  := (mword_of_int 15 : mword 5).
  Local Notation s2_idx  := (mword_of_int 18 : mword 5).
  Local Notation s3_idx  := (mword_of_int 19 : mword 5).
  Local Notation s4_idx  := (mword_of_int 20 : mword 5).
  Local Notation s5_idx  := (mword_of_int 21 : mword 5).
  Local Notation s6_idx  := (mword_of_int 22 : mword 5).
  Local Notation s7_idx  := (mword_of_int 23 : mword 5).
  Local Notation s8_idx  := (mword_of_int 24 : mword 5).
  Local Notation s9_idx  := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* §3a  Transports.                                                      *)
  (* ------------------------------------------------------------------- *)

  (* the stack budget survives any key-preserving image update *)
  Local Lemma stk_dom (M M' : gmap Z (bv 8)) (sp0 : mword 64) (n : Z) :
    (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
    uv_stack pt M sp0 n -> uv_stack pt M' sp0 n.
  Proof. intros Hd HS. exact (uv_stack_dom pt M M' sp0 n Hd HS). Qed.

  Local Lemma stk_store8 (M : gmap Z (bv 8)) (sp0 : mword 64) (n a : Z)
      (v : mword 64) :
    uv_stack pt M sp0 n -> uv_stack pt (uM_store8 M a v) sp0 n.
  Proof.
    intro H. apply (stk_dom M _ sp0 n); [ | exact H ].
    intros k Hk. exact (uM_store8_is_Some M a v k Hk).
  Qed.

  (* THE transport every callee call needs: the shared parse premises move
     to a LOWER sp / SMALLER budget across an image that only changed at or
     above [lo], with [lo] above the image, the tables and the buffer. *)
  Local Lemma parse_pre_move (M M' : gmap Z (bv 8)) (s0 : Z) (bs : list (bv 8))
      (sp0 sp1 : mword 64) (n n1 : Z) :
    (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
    (* the image and the two static tables live below [SH_FREEP] ... *)
    (forall k : Z, k < 8208 -> M' !! k = M !! k) ->
    (* ... and the command buffer is named on its own, because on this
       program it sits ABOVE [freep] (`buf.0' @0x2020) *)
    (forall k : Z, s0 <= k < s0 + Z.of_nat (length bs) + 1 -> M' !! k = M !! k) ->
    hbase + hlen <= uint sp1 - n1 ->
    s0 + Z.of_nat (length bs) + 1 <= uint sp1 - n1 ->
    sh_parse_pre pt hbase hlen M s0 bs sp0 n ->
    sh_parse_pre pt hbase hlen M' s0 bs sp1 n1.
  Proof.
    intros Hdom Hlow Hbufa Hfr1 Hbuf1
           (Hlay & Himg & Htab & Hbuf & Hns & Hrd & Hwr & Hs0p & Hs0hi & _ & _).
    assert (Himg' : sh_img_sub M').
    { destruct Himg as (Ht & Hd). split.
      - intros k b Hk.
        rewrite (Hlow k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
        exact (Ht k b Hk).
      - intros k b Hk.
        rewrite (Hlow k ltac:(pose proof (sh_data_key_lt8208 k b Hk); lia)).
        exact (Hd k b Hk). }
    assert (Htab' : sh_tables_ok M').
    { destruct Htab as ((Hw1 & Hw2) & (Hs1 & Hs2)).
      split; split.
      - intros j b Hj.
        rewrite (Hlow (SH_WHITESPACE + Z.of_nat j)
                   ltac:(pose proof (lookup_lt_Some sh_ws_bytes j b Hj) as Hl;
                         rewrite sh_ws_len in Hl;
                         unfold SH_WHITESPACE, SH_DATA_PG; lia)).
        exact (Hw1 j b Hj).
      - rewrite (Hlow (SH_WHITESPACE + Z.of_nat (length sh_ws_bytes))
                   ltac:(rewrite sh_ws_len;
                         unfold SH_WHITESPACE, SH_DATA_PG; lia)).
        exact Hw2.
      - intros j b Hj.
        rewrite (Hlow (SH_SYMBOLS + Z.of_nat j)
                   ltac:(pose proof (lookup_lt_Some sh_sym_bytes j b Hj) as Hl;
                         rewrite sh_sym_len in Hl;
                         unfold SH_SYMBOLS, SH_DATA_PG; lia)).
        exact (Hs1 j b Hj).
      - rewrite (Hlow (SH_SYMBOLS + Z.of_nat (length sh_sym_bytes))
                   ltac:(rewrite sh_sym_len;
                         unfold SH_SYMBOLS, SH_DATA_PG; lia)).
        exact Hs2. }
    assert (Hbuf' : sh_buf_ok M' s0 bs).
    { destruct Hbuf as ((Hc1 & Hc2) & Hnz). split; [ split | exact Hnz ].
      - intros j b Hj. rewrite (Hbufa (s0 + Z.of_nat j)
          ltac:(pose proof (lookup_lt_Some bs j b Hj); lia)).
        exact (Hc1 j b Hj).
      - rewrite (Hbufa (s0 + Z.of_nat (length bs)) ltac:(lia)). exact Hc2. }
    assert (Hrd' : uv_rd pt M' s0 (Z.of_nat (length bs) + 1)).
    { destruct Hrd as [ A B Cc D E ]. constructor; try assumption.
      intros j Hj. rewrite (Hbufa (s0 + j) ltac:(lia)). exact (E j Hj). }
    assert (Hwr' : uv_wr pt M' s0 (Z.of_nat (length bs) + 1)).
    { destruct Hwr as [ A B Cc D E ]. constructor; try assumption.
      intros j Hj. rewrite (Hbufa (s0 + j) ltac:(lia)). exact (E j Hj). }
    split_and!; assumption.
  Qed.

  (* a `char **' cell moves the same way; it only has to stay ABOVE the
     callee's (lower) entry sp, which it does *)
  Local Lemma ptr_cell_move (M M' : gmap Z (bv 8)) (a v : Z)
      (sp0 sp1 : mword 64) :
    (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
    (forall k : Z, a <= k < a + 8 -> M' !! k = M !! k) ->
    uint sp1 <= uint sp0 ->
    sh_ptr_cell pt M a v sp0 -> sh_ptr_cell pt M' a v sp1.
  Proof.
    intros Hdom Heq Hsp (Hby & Hrd & Hwr & Hal & Hlo & Hhi).
    split_and!.
    - exact (bytes_eq8 M M' a _ Heq Hby).
    - exact (uv_rd_dom pt M M' a 8 Hdom Hrd).
    - exact (uv_wr_dom pt M M' a 8 Hdom Hwr).
    - exact Hal.
    - lia.
    - exact Hhi.
  Qed.

  (* a token table, from the dumped .rodata into the process image *)
  Local Lemma rodata_tok (M : gmap Z (bv 8)) (a : Z) (tbs : list (bv 8)) :
    sh_text_layout pt -> sh_data_sub M ->
    0 <= a -> a + Z.of_nat (length tbs) + 1 <= 8192 ->
    ustr_at ShData.sh_data a tbs ->
    ustr_at M a tbs /\ uv_rd pt M a (Z.of_nat (length tbs) + 1).
  Proof.
    intros Hl Hsub Ha0 Hahi (Hb & Hn). split.
    - split.
      + intros j b Hj. exact (Hsub _ b (Hb j b Hj)).
      + exact (Hsub _ ubyte0 Hn).
    - constructor.
      + lia.
      + lia.
      + change (2 ^ 38) with 274877906944. lia.
      + intros j Hj. exact (sh_text_layout_load pt (a + j) Hl ltac:(lia)).
      + intros j Hj.
        destruct (decide (j = Z.of_nat (length tbs))) as [ -> | Hne ].
        * exists ubyte0. exact (Hsub _ ubyte0 Hn).
        * destruct (lookup_lt_is_Some_2 tbs (Z.to_nat j) ltac:(lia))
            as (b & Hbj).
          exists b. replace (a + j) with (a + Z.of_nat (Z.to_nat j)) by lia.
          exact (Hsub _ b (Hb (Z.to_nat j) b Hbj)).
  Qed.


  (* ---- accessors: one 8-byte slot on the stack, and one in the node --- *)

  Local Lemma stk_leaf8 (Mx : gmap Z (bv 8)) (spx : mword 64) (n a : Z) :
    uv_stack pt Mx spx n -> uint spx - n <= a -> a < uint spx ->
    exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
      uleaf_ok (Store Data) w /\ uleaf_ok (Load Data) w.
  Proof.
    intros HS Hlo Hhi.
    pose proof (us_lo _ _ _ _ HS) as Hlo0.
    pose proof (us_page _ _ _ _ HS) as Hpg.
    pose proof (us_canon _ _ _ _ HS) as Hc.
    pose proof (us_n0 _ _ _ _ HS) as Hn0.
    change (2 ^ 38) with 274877906944 in Hc.
    rewrite Z.rem_mod_nonneg in Hpg; [ | lia | lia ].
    destruct (us_leaf _ _ _ _ HS ltac:(lia)) as (w & Hw & Hst & Hld).
    rewrite (uv_stack_sp_moi pt Mx spx n HS) in Hw.
    pose proof (Z.div_mod (uint spx - n) 4096 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (uint spx - n) 4096 ltac:(lia)) as Hmb.
    assert (Hq : a / 4096 = (uint spx - n) / 4096).
    { symmetry.
      apply (Zdiv_unique a 4096 ((uint spx - n) / 4096)
               ((uint spx - n) mod 4096 + (a - (uint spx - n)))); lia. }
    exists w.
    rewrite (sh_svpn_page a ltac:(lia)).
    rewrite (sh_svpn_page (uint spx - n) ltac:(lia)) in Hw.
    rewrite Hq. split_and!; assumption.
  Qed.

  Local Lemma stk_bytes8 (Mx : gmap Z (bv 8)) (spx : mword 64) (n a : Z) :
    uv_stack pt Mx spx n -> uint spx - n <= a -> a + 8 <= uint spx ->
    forall j : nat, (j < 8)%nat -> exists b : bv 8, Mx !! (a + Z.of_nat j) = Some b.
  Proof.
    intros HS Hlo Hhi j Hj.
    destruct (us_bytes _ _ _ _ HS (a + Z.of_nat j - (uint spx - n)) ltac:(lia))
      as (b & Hb).
    exists b.
    replace (a + Z.of_nat j)
      with (uint spx - n + (a + Z.of_nat j - (uint spx - n))) by lia.
    exact Hb.
  Qed.

  Local Lemma stk_wr8 (Mx : gmap Z (bv 8)) (spx : mword 64) (n a : Z) :
    uv_stack pt Mx spx n -> uint spx - n <= a -> a + 8 <= uint spx ->
    uv_wr pt Mx a 8.
  Proof.
    intros HS Hlo Hhi.
    pose proof (us_lo _ _ _ _ HS) as H0.
    pose proof (us_canon _ _ _ _ HS) as Hc.
    change (2 ^ 38) with 274877906944 in Hc.
    constructor.
    - lia.
    - lia.
    - change (2 ^ 38) with 274877906944. lia.
    - intros j Hj.
      destruct (stk_leaf8 Mx spx n (a + j) HS ltac:(lia) ltac:(lia))
        as (w & Hw & Hst & _).
      exists w. exact (conj Hw Hst).
    - intros j Hj.
      destruct (us_bytes _ _ _ _ HS (a + j - (uint spx - n)) ltac:(lia))
        as (b & Hb).
      exists b.
      replace (a + j) with (uint spx - n + (a + j - (uint spx - n))) by lia.
      exact Hb.
  Qed.

  Local Lemma stk_rd8 (Mx : gmap Z (bv 8)) (spx : mword 64) (n a : Z) :
    uv_stack pt Mx spx n -> uint spx - n <= a -> a + 8 <= uint spx ->
    uv_rd pt Mx a 8.
  Proof.
    intros HS Hlo Hhi.
    pose proof (us_lo _ _ _ _ HS) as H0.
    pose proof (us_canon _ _ _ _ HS) as Hc.
    change (2 ^ 38) with 274877906944 in Hc.
    constructor.
    - lia.
    - lia.
    - change (2 ^ 38) with 274877906944. lia.
    - intros j Hj.
      destruct (stk_leaf8 Mx spx n (a + j) HS ltac:(lia) ltac:(lia))
        as (w & Hw & _ & Hld).
      exists w. exact (conj Hw Hld).
    - intros j Hj.
      destruct (us_bytes _ _ _ _ HS (a + j - (uint spx - n)) ltac:(lia))
        as (b & Hb).
      exists b.
      replace (a + j) with (uint spx - n + (a + j - (uint spx - n))) by lia.
      exact Hb.
  Qed.

  (* the three-window invariant [parseexec]'s loop carries, and what it
     re-establishes about the image at every iteration *)
  Local Lemma win3_out (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 a3 n3 k : Z) :
    uM_only_in M M' [(a1,n1); (a2,n2); (a3,n3)] ->
    (k < a1 \/ a1 + n1 <= k) -> (k < a2 \/ a2 + n2 <= k) ->
    (k < a3 \/ a3 + n3 <= k) ->
    M' !! k = M !! k.
  Proof.
    intros [ _ Ee ] H1 H2 H3. apply Ee.
    intros ((a, n) & Hin & Hk). simpl in Hk.
    apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
    apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
    apply elem_of_cons in Hin as [ He | Hin ]; [ injection He as -> ->; lia | ].
    exact (not_elem_of_nil _ Hin).
  Qed.

  Local Lemma win3_in (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 a3 n3 : Z) :
    (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
    (forall k : Z, (k < a1 \/ a1 + n1 <= k) -> (k < a2 \/ a2 + n2 <= k) ->
       (k < a3 \/ a3 + n3 <= k) -> M' !! k = M !! k) ->
    uM_only_in M M' [(a1,n1); (a2,n2); (a3,n3)].
  Proof.
    intros Hd He. split; [ exact Hd | ]. intros k Hk. apply He.
    - apply (win_out _ a1 n1 k ltac:(apply elem_of_list_here) Hk).
    - apply (win_out _ a2 n2 k
               ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk).
    - apply (win_out _ a3 n3 k
               ltac:(apply elem_of_list_further; apply elem_of_list_further;
                     apply elem_of_list_here) Hk).
  Qed.

  Local Lemma pe_w3_pre (Mi0 Mx : gmap Z (bv 8)) (sb psaddr : Z)
      (bs : list (bv 8)) (sp0 : mword 64) :
    uM_only_in Mi0 Mx [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)] ->
    sh_buf_clear hbase sb (Z.of_nat (length bs) + 1) ->
    uint sp0 <= psaddr ->
    sh_parse_pre pt hbase hlen Mi0 sb bs sp0 320 ->
    sh_parse_pre pt hbase hlen Mx sb bs sp0 320.
  Proof.
    intros HW Hbc Hps Hpre0.
    pose proof Hpre0 as (Hlay & _ & _ & _ & _ & _ & _ & Hs0p & Hs0hi & Hfr & Hbufhi).
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hroom.
    unfold sh_frame_ok in Hfr.
    pose proof Hbc as (Hd1 & Hd2 & Hd3).
    unfold sh_disj in Hd1, Hd2, Hd3.
    change SH_FREEP with 8208 in Hd1. change SH_BASE with 8328 in Hd2.
    apply (parse_pre_move Mi0 Mx sb bs sp0 sp0 320 320).
    - exact (proj1 HW).
    - intros k Hk.
      exact (win3_out Mi0 Mx hbase 65536 psaddr 8 (uint sp0 - 320) 208 k HW
               ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros k Hk.
      exact (win3_out Mi0 Mx hbase 65536 psaddr 8 (uint sp0 - 320) 208 k HW
               ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact Hfr.
    - exact Hbufhi.
    - exact Hpre0.
  Qed.

  Local Lemma node_leaf (Mx : gmap Z (bv 8)) (cmd a : Z) :
    uv_wr pt Mx cmd 168 -> cmd <= a -> a + 8 <= cmd + 168 ->
    exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
      uleaf_ok (Store Data) w.
  Proof.
    intros Hw Hlo Hhi.
    destruct (uwr_leaf _ _ _ _ Hw (a - cmd) ltac:(lia)) as (w & Hw' & Hok).
    replace (cmd + (a - cmd)) with a in Hw' by lia.
    exists w. exact (conj Hw' Hok).
  Qed.

  Local Lemma node_bytes (Mx : gmap Z (bv 8)) (cmd a : Z) :
    uv_wr pt Mx cmd 168 -> cmd <= a -> a + 8 <= cmd + 168 ->
    forall j : nat, (j < 8)%nat -> exists b : bv 8, Mx !! (a + Z.of_nat j) = Some b.
  Proof.
    intros Hw Hlo Hhi j Hj.
    destruct (uwr_bytes _ _ _ _ Hw (a - cmd + Z.of_nat j) ltac:(lia)) as (b & Hb).
    exists b.
    replace (a + Z.of_nat j) with (cmd + (a - cmd + Z.of_nat j)) by lia.
    exact Hb.
  Qed.

  (* [uv_rd] of the execcmd node: the bytes come from its writability, the
     LOAD leaf from the heap's own mapping. *)
  Local Lemma pe_heap_leaf (a : Z) :
    sh_layout pt hbase hlen -> hbase <= a < hbase + hlen ->
    exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
      uleaf_ok (Load Data) w /\ uleaf_ok (Store Data) w.
  Proof.
    intros Hlay Ha.
    pose proof (shl_hbase _ _ _ Hlay) as Hhb.
    pose proof (shl_hlen _ _ _ Hlay) as Hhl.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    unfold SH_DATA_PG in Hhlo.
    change (2 ^ 38) with 274877906944 in Hhhi.
    rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
    rewrite Z.rem_mod_nonneg in Hhl; [ | lia | lia ].
    assert (Hhlq : hlen = 4096 * (hlen / 4096))
      by (pose proof (Z.div_mod hlen 4096 ltac:(lia)); lia).
    assert (Hbq : hbase = 4096 * (hbase / 4096))
      by (pose proof (Z.div_mod hbase 4096 ltac:(lia)); lia).
    pose proof (Z.div_mod a 4096 ltac:(lia)) as Haq.
    pose proof (Z.div_mod (a - hbase) 4096 ltac:(lia)) as Hdq.
    pose proof (Z.mod_pos_bound a 4096 ltac:(lia)) as Har.
    pose proof (Z.mod_pos_bound (a - hbase) 4096 ltac:(lia)) as Hdr.
    assert (Hi : 0 <= (a - hbase) / 4096 < hlen / 4096).
    { split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
    destruct (shl_heap _ _ _ Hlay ((a - hbase) / 4096) Hi) as (w & Hw & Hld & Hst).
    assert (He : hbase + 4096 * ((a - hbase) / 4096) = 4096 * (a / 4096)) by lia.
    exists w. rewrite (sh_svpn_page a ltac:(lia)). rewrite <- He.
    split_and!; assumption.
  Qed.

  Local Lemma heap_rd (Mx : gmap Z (bv 8)) (a n : Z) :
    sh_layout pt hbase hlen -> uv_wr pt Mx a n ->
    hbase <= a -> a + n <= hbase + 65536 -> uv_rd pt Mx a n.
  Proof.
    intros Hlay Hw Hlo Hhi.
    pose proof (shl_hroom _ _ _ Hlay) as Hroom.
    destruct Hw as [ A B Cc D E ]. constructor; try assumption.
    intros j Hj.
    destruct (pe_heap_leaf (a + j) Hlay ltac:(lia)) as (w & Hw' & Hld & _).
    exists w. exact (conj Hw' Hld).
  Qed.

  Local Lemma mk_ptr_cell (Mx : gmap Z (bv 8)) (a v : Z) (spx : mword 64) :
    uM_bytes Mx a 8 (mword_of_int v : mword 64) ->
    uv_rd pt Mx a 8 -> uv_wr pt Mx a 8 ->
    a mod 8 = 0 -> uint spx <= a -> a + 8 <= 2 ^ 38 ->
    sh_ptr_cell pt Mx a v spx.
  Proof. intros; split_and!; assumption. Qed.

  (* ------------------------------------------------------------------- *)
  (* §3b  peek, at the six call sites where it returns 0.                  *)
  (* ------------------------------------------------------------------- *)

  Local Lemma wp_sh_peek_zero (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (spk : mword 64) (psaddr s0 tk : Z) (bs : list (bv 8)) (off : nat)
      (tbs : list (bv 8)) :
    sh_parse_pre pt hbase hlen M s0 bs spk 80 ->
    m !!! Regidx sp_idx = spk ->
    uv_stack pt M spk 80 ->
    m !!! Regidx a0_idx = (mword_of_int psaddr : mword 64) ->
    m !!! Regidx a1_idx
      = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64) ->
    m !!! Regidx a2_idx = (mword_of_int tk : mword 64) ->
    sh_ptr_cell pt M psaddr (s0 + Z.of_nat off) spk ->
    (off <= length bs)%nat ->
    0 < tk ->
    tk + Z.of_nat (length tbs) + 1 <= 8192 ->
    tk + Z.of_nat (length tbs) + 1 <= uint spk - 80 ->
    ustr_at ShData.sh_data tk tbs ->
    (forall b : bv 8, b ∈ tbs -> sh_is_sym b = true) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    uv_cap_gpr (CID := CIDp) C pt Psh M m -∗
    pc_is (CID := CIDp) (mword_of_int 0x448) -∗
    (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int 0 : mword 64)⌝ -∗
       ⌜uM_bytes M' psaddr 8
          (mword_of_int (s0 + Z.of_nat (off + sh_skipws (drop off bs)))
           : mword 64)⌝ -∗
       ⌜uM_only_in M M' [(psaddr, 8); (uint spk - 80, 80)]⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpre Hsp Hst Hps Hes Htkr Hcell Hoff Htnn Hdhi Uthi Hdat Hsym Hret2.
    pose proof Hpre as (Hlay & Himg & _ & _ & Hns & _).
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    destruct (rodata_tok M tk tbs Hltext (sh_img_data M Himg)
                ltac:(lia) Hdhi Hdat) as (Hstr & Hrdt).
    assert (Hspeek : ShSyms.peek = 0x448)
      by (destruct sh_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite <- Hspeek) in "Hpc".
    iApply (wp_sh_peek C pt gin gbrk hbase hlen Q CIDp M m spk psaddr s0 bs off
              tk tbs Hpre Hsp Hst Hps Hes Htkr Hcell Hoff Htnn Hstr
              (sh_tb_nz tbs Hsym) Hrdt Uthi Hret2 with "Hcg Hpc [Hcont]").
    iIntros (CIDk mk Mk) "%Hcs %Ha0 %Hpsc %Honly Hcg Hpc".
    rewrite (peek_ret_0 bs off tbs Hns Hsym) in Ha0.
    iApply ("Hcont" $! CIDk mk Mk with "[] [] [] [] Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0.
    - iPureIntro. exact Hpsc.
    - iPureIntro. exact Honly.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3c  parseredirs @0x4ac.                                              *)
  (*                                                                       *)
  (*   struct cmd *parseredirs(struct cmd *cmd, char **ps, char *es) {     *)
  (*     while (peek(ps, es, "<>")) { ... }                                *)
  (*     return cmd; }                                                     *)
  (*                                                                       *)
  (*   4ac..4c4  the 112-byte prologue (ra, s0..s9 spilled)                *)
  (*   4c6..4e0  s4 := cmd, s3 := ps, s2 := es, s6 := "<>", s9/s8 := &q/&eq *)
  (*             (dead on this input), s7 := 'a'; jump into the loop test  *)
  (*   502..510  s5 := '<'; peek(ps, es, "<>") -- 0, so the loop never runs *)
  (*   574..58e  a0 := cmd and the epilogue                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_parseredirs (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (cmd psaddr s0 : Z) (bs : list (bv 8)) (off : nat) :
    wp_sh_parseredirs_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 cmd psaddr s0 bs off.
  Proof.
    intros Hpre Hsp Hst0 Hcmd Hps Hes Hcell Hoff Hret2.
    pose proof Hpre as (Hlay & Himg & Htab & Hbuf & Hns & Hrdb & Hwrb & Hs0p &
                        Hs0hi & Hfr & Hbufhi).
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    unfold sh_frame_ok in Hfr.
    assert (Hst : uv_stack pt M sp0 192) by exact Hst0.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi.
    assert (Hfrz : hbase + hlen <= uint sp0 - 192) by exact Hfr.
    assert (Hbufz : s0 + Z.of_nat (length bs) + 1 <= uint sp0 - 192)
      by exact Hbufhi.
    pose proof Hcell as (Hcb & Hcrd & Hcwr & Hcal & Hclo & Hchi).
    change (2 ^ 38) with 274877906944 in Hchi.
    destruct (uv_stack_split pt M sp0 192 112 80 ltac:(lia) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hst)
      as (Hst112 & Hstk80).
    rewrite (uv_stack_sp_moi pt M sp0 112 Hst112) in Hstk80.
    assert (Huspk : uint (mword_of_int (uint sp0 - 112) : mword 64)
                    = uint sp0 - 112)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hspr : ShSyms.parseredirs = 0x4ac)
      by (destruct sh_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hspr) in "Hpc".
    (* ---- 0x4ac  c.addi16sp sp,sp,-112 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 112) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi16sp_imm (mword_of_int 57 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))
                    : mword 64) = mword_of_int (-112))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x4ac)
              (mword_of_int 57 : mword 6) (mword_of_int (uint sp0 - 112))
              (ui_sh_4ac pt M Hltext (sh_img_text M Himg)) Hwsp with "Hcg Hpc").
    iIntros (CIDs0) "Hcg Hpc".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 112) : mword 64)]> m).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4ac : mword 64) 2
                      = mword_of_int 0x4ae)) in "Hpc".
    assert (Hq1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_1 : m1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hv_a0_idx_1 : m1 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq1 a0_idx ltac:(vm_compute; discriminate)); exact Hcmd).
    assert (Hv_a1_idx_1 : m1 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq1 a1_idx ltac:(vm_compute; discriminate)); exact Hps).
    assert (Hv_a2_idx_1 : m1 !!! Regidx a2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq1 a2_idx ltac:(vm_compute; discriminate)); exact Hes).

    (* ---- 0x4ae  c.sdsp ra,104(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs0 Psh M m1 sp0 (mword_of_int 0x4ae)
              (mword_of_int 13 : mword 6) ra_idx 112 104
              (ui_sh_4ae pt M Hltext (sh_img_text M Himg)) Hst112
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4ae : mword 64) 2
                      = mword_of_int 0x4b0)) in "Hpc".
    set (P1 := uM_store8 M (uint sp0 - 112 + 104) (m1 !!! Regidx ra_idx)).
    assert (Ho1 : uM_only M P1 (uint sp0 - 112 + 24) 88)
      by (unfold P1; apply only_step8; [ lia | lia | apply uM_only_refl ]).
    assert (Hg1 : sh_img_sub P1)
      by (exact (only_img M P1 (uint sp0 - 112 + 24) 88 Ho1 ltac:(lia) Himg)).
    assert (Hk1 : uv_stack pt P1 sp0 112)
      by (exact (stk_dom M P1 sp0 112 (proj1 Ho1) Hst112)).

    (* ---- 0x4b0  c.sdsp s0,96(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs1 Psh P1 m1 sp0 (mword_of_int 0x4b0)
              (mword_of_int 12 : mword 6) s0_idx 112 96
              (ui_sh_4b0 pt P1 Hltext (sh_img_text P1 Hg1)) Hk1
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4b0 : mword 64) 2
                      = mword_of_int 0x4b2)) in "Hpc".
    set (P2 := uM_store8 P1 (uint sp0 - 112 + 96) (m1 !!! Regidx s0_idx)).
    assert (Ho2 : uM_only M P2 (uint sp0 - 112 + 24) 88)
      by (unfold P2; apply only_step8; [ lia | lia | exact Ho1 ]).
    assert (Hg2 : sh_img_sub P2)
      by (exact (only_img M P2 (uint sp0 - 112 + 24) 88 Ho2 ltac:(lia) Himg)).
    assert (Hk2 : uv_stack pt P2 sp0 112)
      by (exact (stk_dom M P2 sp0 112 (proj1 Ho2) Hst112)).

    (* ---- 0x4b2  c.sdsp s1,88(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs2 Psh P2 m1 sp0 (mword_of_int 0x4b2)
              (mword_of_int 11 : mword 6) s1_idx 112 88
              (ui_sh_4b2 pt P2 Hltext (sh_img_text P2 Hg2)) Hk2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4b2 : mword 64) 2
                      = mword_of_int 0x4b4)) in "Hpc".
    set (P3 := uM_store8 P2 (uint sp0 - 112 + 88) (m1 !!! Regidx s1_idx)).
    assert (Ho3 : uM_only M P3 (uint sp0 - 112 + 24) 88)
      by (unfold P3; apply only_step8; [ lia | lia | exact Ho2 ]).
    assert (Hg3 : sh_img_sub P3)
      by (exact (only_img M P3 (uint sp0 - 112 + 24) 88 Ho3 ltac:(lia) Himg)).
    assert (Hk3 : uv_stack pt P3 sp0 112)
      by (exact (stk_dom M P3 sp0 112 (proj1 Ho3) Hst112)).

    (* ---- 0x4b4  c.sdsp s2,80(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs3 Psh P3 m1 sp0 (mword_of_int 0x4b4)
              (mword_of_int 10 : mword 6) s2_idx 112 80
              (ui_sh_4b4 pt P3 Hltext (sh_img_text P3 Hg3)) Hk3
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4b4 : mword 64) 2
                      = mword_of_int 0x4b6)) in "Hpc".
    set (P4 := uM_store8 P3 (uint sp0 - 112 + 80) (m1 !!! Regidx s2_idx)).
    assert (Ho4 : uM_only M P4 (uint sp0 - 112 + 24) 88)
      by (unfold P4; apply only_step8; [ lia | lia | exact Ho3 ]).
    assert (Hg4 : sh_img_sub P4)
      by (exact (only_img M P4 (uint sp0 - 112 + 24) 88 Ho4 ltac:(lia) Himg)).
    assert (Hk4 : uv_stack pt P4 sp0 112)
      by (exact (stk_dom M P4 sp0 112 (proj1 Ho4) Hst112)).

    (* ---- 0x4b6  c.sdsp s3,72(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs4 Psh P4 m1 sp0 (mword_of_int 0x4b6)
              (mword_of_int 9 : mword 6) s3_idx 112 72
              (ui_sh_4b6 pt P4 Hltext (sh_img_text P4 Hg4)) Hk4
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4b6 : mword 64) 2
                      = mword_of_int 0x4b8)) in "Hpc".
    set (P5 := uM_store8 P4 (uint sp0 - 112 + 72) (m1 !!! Regidx s3_idx)).
    assert (Ho5 : uM_only M P5 (uint sp0 - 112 + 24) 88)
      by (unfold P5; apply only_step8; [ lia | lia | exact Ho4 ]).
    assert (Hg5 : sh_img_sub P5)
      by (exact (only_img M P5 (uint sp0 - 112 + 24) 88 Ho5 ltac:(lia) Himg)).
    assert (Hk5 : uv_stack pt P5 sp0 112)
      by (exact (stk_dom M P5 sp0 112 (proj1 Ho5) Hst112)).

    (* ---- 0x4b8  c.sdsp s4,64(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs5 Psh P5 m1 sp0 (mword_of_int 0x4b8)
              (mword_of_int 8 : mword 6) s4_idx 112 64
              (ui_sh_4b8 pt P5 Hltext (sh_img_text P5 Hg5)) Hk5
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4b8 : mword 64) 2
                      = mword_of_int 0x4ba)) in "Hpc".
    set (P6 := uM_store8 P5 (uint sp0 - 112 + 64) (m1 !!! Regidx s4_idx)).
    assert (Ho6 : uM_only M P6 (uint sp0 - 112 + 24) 88)
      by (unfold P6; apply only_step8; [ lia | lia | exact Ho5 ]).
    assert (Hg6 : sh_img_sub P6)
      by (exact (only_img M P6 (uint sp0 - 112 + 24) 88 Ho6 ltac:(lia) Himg)).
    assert (Hk6 : uv_stack pt P6 sp0 112)
      by (exact (stk_dom M P6 sp0 112 (proj1 Ho6) Hst112)).

    (* ---- 0x4ba  c.sdsp s5,56(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs6 Psh P6 m1 sp0 (mword_of_int 0x4ba)
              (mword_of_int 7 : mword 6) s5_idx 112 56
              (ui_sh_4ba pt P6 Hltext (sh_img_text P6 Hg6)) Hk6
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs7) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4ba : mword 64) 2
                      = mword_of_int 0x4bc)) in "Hpc".
    set (P7 := uM_store8 P6 (uint sp0 - 112 + 56) (m1 !!! Regidx s5_idx)).
    assert (Ho7 : uM_only M P7 (uint sp0 - 112 + 24) 88)
      by (unfold P7; apply only_step8; [ lia | lia | exact Ho6 ]).
    assert (Hg7 : sh_img_sub P7)
      by (exact (only_img M P7 (uint sp0 - 112 + 24) 88 Ho7 ltac:(lia) Himg)).
    assert (Hk7 : uv_stack pt P7 sp0 112)
      by (exact (stk_dom M P7 sp0 112 (proj1 Ho7) Hst112)).

    (* ---- 0x4bc  c.sdsp s6,48(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs7 Psh P7 m1 sp0 (mword_of_int 0x4bc)
              (mword_of_int 6 : mword 6) s6_idx 112 48
              (ui_sh_4bc pt P7 Hltext (sh_img_text P7 Hg7)) Hk7
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs8) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4bc : mword 64) 2
                      = mword_of_int 0x4be)) in "Hpc".
    set (P8 := uM_store8 P7 (uint sp0 - 112 + 48) (m1 !!! Regidx s6_idx)).
    assert (Ho8 : uM_only M P8 (uint sp0 - 112 + 24) 88)
      by (unfold P8; apply only_step8; [ lia | lia | exact Ho7 ]).
    assert (Hg8 : sh_img_sub P8)
      by (exact (only_img M P8 (uint sp0 - 112 + 24) 88 Ho8 ltac:(lia) Himg)).
    assert (Hk8 : uv_stack pt P8 sp0 112)
      by (exact (stk_dom M P8 sp0 112 (proj1 Ho8) Hst112)).

    (* ---- 0x4be  c.sdsp s7,40(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs8 Psh P8 m1 sp0 (mword_of_int 0x4be)
              (mword_of_int 5 : mword 6) s7_idx 112 40
              (ui_sh_4be pt P8 Hltext (sh_img_text P8 Hg8)) Hk8
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs9) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4be : mword 64) 2
                      = mword_of_int 0x4c0)) in "Hpc".
    set (P9 := uM_store8 P8 (uint sp0 - 112 + 40) (m1 !!! Regidx s7_idx)).
    assert (Ho9 : uM_only M P9 (uint sp0 - 112 + 24) 88)
      by (unfold P9; apply only_step8; [ lia | lia | exact Ho8 ]).
    assert (Hg9 : sh_img_sub P9)
      by (exact (only_img M P9 (uint sp0 - 112 + 24) 88 Ho9 ltac:(lia) Himg)).
    assert (Hk9 : uv_stack pt P9 sp0 112)
      by (exact (stk_dom M P9 sp0 112 (proj1 Ho9) Hst112)).

    (* ---- 0x4c0  c.sdsp s8,32(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs9 Psh P9 m1 sp0 (mword_of_int 0x4c0)
              (mword_of_int 4 : mword 6) s8_idx 112 32
              (ui_sh_4c0 pt P9 Hltext (sh_img_text P9 Hg9)) Hk9
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs10) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4c0 : mword 64) 2
                      = mword_of_int 0x4c2)) in "Hpc".
    set (P10 := uM_store8 P9 (uint sp0 - 112 + 32) (m1 !!! Regidx s8_idx)).
    assert (Ho10 : uM_only M P10 (uint sp0 - 112 + 24) 88)
      by (unfold P10; apply only_step8; [ lia | lia | exact Ho9 ]).
    assert (Hg10 : sh_img_sub P10)
      by (exact (only_img M P10 (uint sp0 - 112 + 24) 88 Ho10 ltac:(lia) Himg)).
    assert (Hk10 : uv_stack pt P10 sp0 112)
      by (exact (stk_dom M P10 sp0 112 (proj1 Ho10) Hst112)).

    (* ---- 0x4c2  c.sdsp s9,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDs10 Psh P10 m1 sp0 (mword_of_int 0x4c2)
              (mword_of_int 3 : mword 6) s9_idx 112 24
              (ui_sh_4c2 pt P10 Hltext (sh_img_text P10 Hg10)) Hk10
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs11) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4c2 : mword 64) 2
                      = mword_of_int 0x4c4)) in "Hpc".
    set (P11 := uM_store8 P10 (uint sp0 - 112 + 24) (m1 !!! Regidx s9_idx)).
    assert (Ho11 : uM_only M P11 (uint sp0 - 112 + 24) 88)
      by (unfold P11; apply only_step8; [ lia | lia | exact Ho10 ]).
    assert (Hg11 : sh_img_sub P11)
      by (exact (only_img M P11 (uint sp0 - 112 + 24) 88 Ho11 ltac:(lia) Himg)).
    assert (Hk11 : uv_stack pt P11 sp0 112)
      by (exact (stk_dom M P11 sp0 112 (proj1 Ho11) Hst112)).


    (* ---- 0x4c4  c.addi4spn s0,sp,112 ---- *)
    assert (Hw2 : (mword_of_int (uint sp0) : mword 64)
                  = add_vec (m1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8)))).
    { rewrite Hv_csp_rs1_1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))
                    : mword 64) = mword_of_int 112)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh P11 m1 (mword_of_int 0x4c4)
              (mword_of_int 0 : mword 3) (mword_of_int 28 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_4c4 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw2
              with "Hcg Hpc").
    iIntros (CIDm2) "Hcg Hpc".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4c4 : mword 64) 2
                      = mword_of_int 0x4c6)) in "Hpc".
    assert (Hq2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_2 : m2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_1).
    assert (Hv_a0_idx_2 : m2 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq2 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_1).
    assert (Hv_a1_idx_2 : m2 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq2 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_1).
    assert (Hv_a2_idx_2 : m2 !!! Regidx a2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq2 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_1).
    assert (Hv_s0_idx_2 : m2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by exact (upd_eq m1 (Regidx s0_idx) _).

    (* ---- 0x4c6  c.mv ---- *)
    assert (Hw3 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (m2 !!! Regidx a0_idx))
      by (rewrite Hv_a0_idx_2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P11 m2 (mword_of_int 0x4c6)
              s4_idx a0_idx (mword_of_int cmd : mword 64)
              (ui_sh_4c6 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw3 with "Hcg Hpc").
    iIntros (CIDm3) "Hcg Hpc".
    set (m3 := <[Regidx s4_idx := regval_into_reg (mword_of_int cmd : mword 64)]> m2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4c6 : mword 64) 2
                      = mword_of_int 0x4c8)) in "Hpc".
    assert (Hq3 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_3 : m3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_2).
    assert (Hv_a1_idx_3 : m3 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq3 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_2).
    assert (Hv_a2_idx_3 : m3 !!! Regidx a2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq3 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_2).
    assert (Hv_s0_idx_3 : m3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq3 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_2).
    assert (Hv_s4_idx_3 : m3 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq m2 (Regidx s4_idx) _).

    (* ---- 0x4c8  c.mv ---- *)
    assert (Hw4 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (m3 !!! Regidx a1_idx))
      by (rewrite Hv_a1_idx_3 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P11 m3 (mword_of_int 0x4c8)
              s3_idx a1_idx (mword_of_int psaddr : mword 64)
              (ui_sh_4c8 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw4 with "Hcg Hpc").
    iIntros (CIDm4) "Hcg Hpc".
    set (m4 := <[Regidx s3_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> m3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4c8 : mword 64) 2
                      = mword_of_int 0x4ca)) in "Hpc".
    assert (Hq4 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_4 : m4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq4 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_3).
    assert (Hv_a2_idx_4 : m4 !!! Regidx a2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq4 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_3).
    assert (Hv_s0_idx_4 : m4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq4 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_3).
    assert (Hv_s3_idx_4 : m4 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq m3 (Regidx s3_idx) _).
    assert (Hv_s4_idx_4 : m4 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq4 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_3).

    (* ---- 0x4ca  c.mv ---- *)
    assert (Hw5 : (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (m4 !!! Regidx a2_idx))
      by (rewrite Hv_a2_idx_4 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P11 m4 (mword_of_int 0x4ca)
              s2_idx a2_idx (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
              (ui_sh_4ca pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw5 with "Hcg Hpc").
    iIntros (CIDm5) "Hcg Hpc".
    set (m5 := <[Regidx s2_idx := regval_into_reg (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)]> m4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4ca : mword 64) 2
                      = mword_of_int 0x4cc)) in "Hpc".
    assert (Hq5 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_5 : m5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq5 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_4).
    assert (Hv_s0_idx_5 : m5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq5 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_4).
    assert (Hv_s2_idx_5 : m5 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq m4 (Regidx s2_idx) _).
    assert (Hv_s3_idx_5 : m5 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_4).
    assert (Hv_s4_idx_5 : m5 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq5 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_4).

    (* ---- 0x4cc  auipc s6,0x1 ---- *)
    assert (Hw6 : (mword_of_int 5324 : mword 64)
                  = add_vec (mword_of_int 0x4cc) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh P11 m5 (mword_of_int 0x4cc)
              (mword_of_int 1 : mword 20) s6_idx (mword_of_int 5324)
              (ui_sh_4cc pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw6 with "Hcg Hpc").
    iIntros (CIDm6) "Hcg Hpc".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 5324 : mword 64)]> m5).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4cc : mword 64) 4
                      = mword_of_int 0x4d0)) in "Hpc".
    assert (Hq6 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
              m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx s6_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_6 : m6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq6 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_5).
    assert (Hv_s0_idx_6 : m6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq6 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_5).
    assert (Hv_s6_idx_6 : m6 !!! Regidx s6_idx = (mword_of_int 5324 : mword 64))
      by exact (upd_eq m5 (Regidx s6_idx) _).
    assert (Hv_s2_idx_6 : m6 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq6 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_5).
    assert (Hv_s3_idx_6 : m6 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq6 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_5).
    assert (Hv_s4_idx_6 : m6 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq6 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_5).

    (* ---- 0x4d0  addi ---- *)
    assert (Hw7 : (mword_of_int 4848 : mword 64)
                  = add_vec (m6 !!! Regidx s6_idx)
                      (sign_extend' 64 (mword_of_int 3620 : mword 12))).
    { rewrite Hv_s6_idx_6.
      assert (Hc : (sign_extend' 64 (mword_of_int 3620 : mword 12) : mword 64)
                   = mword_of_int (-476))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh P11 m6 (mword_of_int 0x4d0)
              (mword_of_int 3620 : mword 12) s6_idx s6_idx (mword_of_int 4848 : mword 64)
              (ui_sh_4d0 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw7 with "Hcg Hpc").
    iIntros (CIDm7) "Hcg Hpc".
    set (m7 := <[Regidx s6_idx := regval_into_reg (mword_of_int 4848 : mword 64)]> m6).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4d0 : mword 64) 4
                      = mword_of_int 0x4d4)) in "Hpc".
    assert (Hq7 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
              m7 !!! Regidx r = m6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m6 (Regidx s6_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_7 : m7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq7 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_6).
    assert (Hv_s0_idx_7 : m7 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq7 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_6).
    assert (Hv_s6_idx_7 : m7 !!! Regidx s6_idx = (mword_of_int 4848 : mword 64))
      by exact (upd_eq m6 (Regidx s6_idx) _).
    assert (Hv_s2_idx_7 : m7 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq7 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_6).
    assert (Hv_s3_idx_7 : m7 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq7 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_6).
    assert (Hv_s4_idx_7 : m7 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq7 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_6).

    (* ---- 0x4d4  addi ---- *)
    assert (Hw8 : (mword_of_int (uint sp0 - 112) : mword 64)
                  = add_vec (m7 !!! Regidx s0_idx)
                      (sign_extend' 64 (mword_of_int 3984 : mword 12))).
    { rewrite Hv_s0_idx_7.
      assert (Hc : (sign_extend' 64 (mword_of_int 3984 : mword 12) : mword 64)
                   = mword_of_int (-112))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh P11 m7 (mword_of_int 0x4d4)
              (mword_of_int 3984 : mword 12) s0_idx s9_idx (mword_of_int (uint sp0 - 112) : mword 64)
              (ui_sh_4d4 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw8 with "Hcg Hpc").
    iIntros (CIDm8) "Hcg Hpc".
    set (m8 := <[Regidx s9_idx := regval_into_reg (mword_of_int (uint sp0 - 112) : mword 64)]> m7).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4d4 : mword 64) 4
                      = mword_of_int 0x4d8)) in "Hpc".
    assert (Hq8 : forall r : mword 5, Regidx r <> Regidx s9_idx ->
              m8 !!! Regidx r = m7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m7 (Regidx s9_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_8 : m8 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq8 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_7).
    assert (Hv_s0_idx_8 : m8 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq8 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_7).
    assert (Hv_s6_idx_8 : m8 !!! Regidx s6_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq8 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_7).
    assert (Hv_s2_idx_8 : m8 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq8 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_7).
    assert (Hv_s3_idx_8 : m8 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq8 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_7).
    assert (Hv_s4_idx_8 : m8 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq8 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_7).

    (* ---- 0x4d8  addi ---- *)
    assert (Hw9 : (mword_of_int (uint sp0 - 104) : mword 64)
                  = add_vec (m8 !!! Regidx s0_idx)
                      (sign_extend' 64 (mword_of_int 3992 : mword 12))).
    { rewrite Hv_s0_idx_8.
      assert (Hc : (sign_extend' 64 (mword_of_int 3992 : mword 12) : mword 64)
                   = mword_of_int (-104))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh P11 m8 (mword_of_int 0x4d8)
              (mword_of_int 3992 : mword 12) s0_idx s8_idx (mword_of_int (uint sp0 - 104) : mword 64)
              (ui_sh_4d8 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw9 with "Hcg Hpc").
    iIntros (CIDm9) "Hcg Hpc".
    set (m9 := <[Regidx s8_idx := regval_into_reg (mword_of_int (uint sp0 - 104) : mword 64)]> m8).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4d8 : mword 64) 4
                      = mword_of_int 0x4dc)) in "Hpc".
    assert (Hq9 : forall r : mword 5, Regidx r <> Regidx s8_idx ->
              m9 !!! Regidx r = m8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m8 (Regidx s8_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_9 : m9 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq9 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_8).
    assert (Hv_s0_idx_9 : m9 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq9 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_8).
    assert (Hv_s6_idx_9 : m9 !!! Regidx s6_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq9 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_8).
    assert (Hv_s2_idx_9 : m9 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq9 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_8).
    assert (Hv_s3_idx_9 : m9 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq9 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_8).
    assert (Hv_s4_idx_9 : m9 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq9 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_8).

    (* ---- 0x4dc  li ---- *)
    assert (Hw10 : (mword_of_int 97 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (mword_of_int 97 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_li C pt Psh P11 m9 (mword_of_int 0x4dc)
              (mword_of_int 97 : mword 12) s7_idx (mword_of_int 97 : mword 64)
              (ui_sh_4dc pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw10 with "Hcg Hpc").
    iIntros (CIDm10) "Hcg Hpc".
    set (m10 := <[Regidx s7_idx := regval_into_reg (mword_of_int 97 : mword 64)]> m9).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x4dc : mword 64) 4
                      = mword_of_int 0x4e0)) in "Hpc".
    assert (Hq10 : forall r : mword 5, Regidx r <> Regidx s7_idx ->
              m10 !!! Regidx r = m9 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m9 (Regidx s7_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_10 : m10 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq10 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_9).
    assert (Hv_s6_idx_10 : m10 !!! Regidx s6_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq10 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_9).
    assert (Hv_s2_idx_10 : m10 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq10 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_9).
    assert (Hv_s3_idx_10 : m10 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq10 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_9).
    assert (Hv_s4_idx_10 : m10 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq10 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_9).

    (* ---- 0x4e0  c.j 0x502 ---- *)
    iApply (wp_uv_cj C pt Psh P11 m10 (mword_of_int 0x4e0)
              (mword_of_int 17 : mword 11) (mword_of_int 0x502)
              (ui_sh_4e0 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDj) "Hcg Hpc".

    (* ---- 0x502  li ---- *)
    assert (Hw11 : (mword_of_int 60 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (mword_of_int 60 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_li C pt Psh P11 m10 (mword_of_int 0x502)
              (mword_of_int 60 : mword 12) s5_idx (mword_of_int 60 : mword 64)
              (ui_sh_502 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw11 with "Hcg Hpc").
    iIntros (CIDm11) "Hcg Hpc".
    set (m11 := <[Regidx s5_idx := regval_into_reg (mword_of_int 60 : mword 64)]> m10).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x502 : mword 64) 4
                      = mword_of_int 0x506)) in "Hpc".
    assert (Hq11 : forall r : mword 5, Regidx r <> Regidx s5_idx ->
              m11 !!! Regidx r = m10 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m10 (Regidx s5_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_11 : m11 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq11 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_10).
    assert (Hv_s6_idx_11 : m11 !!! Regidx s6_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq11 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_10).
    assert (Hv_s2_idx_11 : m11 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq11 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_10).
    assert (Hv_s3_idx_11 : m11 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq11 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_10).
    assert (Hv_s4_idx_11 : m11 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq11 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_10).

    (* ---- 0x506  c.mv ---- *)
    assert (Hw12 : (mword_of_int 4848 : mword 64)
                  = add_vec zero_reg (m11 !!! Regidx s6_idx))
      by (rewrite Hv_s6_idx_11 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P11 m11 (mword_of_int 0x506)
              a2_idx s6_idx (mword_of_int 4848 : mword 64)
              (ui_sh_506 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw12 with "Hcg Hpc").
    iIntros (CIDm12) "Hcg Hpc".
    set (m12 := <[Regidx a2_idx := regval_into_reg (mword_of_int 4848 : mword 64)]> m11).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x506 : mword 64) 2
                      = mword_of_int 0x508)) in "Hpc".
    assert (Hq12 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              m12 !!! Regidx r = m11 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m11 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_12 : m12 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq12 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_11).
    assert (Hv_s6_idx_12 : m12 !!! Regidx s6_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq12 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_11).
    assert (Hv_s2_idx_12 : m12 !!! Regidx s2_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq12 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_11).
    assert (Hv_s3_idx_12 : m12 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq12 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_11).
    assert (Hv_s4_idx_12 : m12 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq12 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_11).
    assert (Hv_a2_idx_12 : m12 !!! Regidx a2_idx = (mword_of_int 4848 : mword 64))
      by exact (upd_eq m11 (Regidx a2_idx) _).

    (* ---- 0x508  c.mv ---- *)
    assert (Hw13 : (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (m12 !!! Regidx s2_idx))
      by (rewrite Hv_s2_idx_12 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P11 m12 (mword_of_int 0x508)
              a1_idx s2_idx (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
              (ui_sh_508 pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw13 with "Hcg Hpc").
    iIntros (CIDm13) "Hcg Hpc".
    set (m13 := <[Regidx a1_idx := regval_into_reg (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)]> m12).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x508 : mword 64) 2
                      = mword_of_int 0x50a)) in "Hpc".
    assert (Hq13 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              m13 !!! Regidx r = m12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m12 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_13 : m13 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq13 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_12).
    assert (Hv_s3_idx_13 : m13 !!! Regidx s3_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_12).
    assert (Hv_s4_idx_13 : m13 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq13 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_12).
    assert (Hv_a2_idx_13 : m13 !!! Regidx a2_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq13 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_12).
    assert (Hv_a1_idx_13 : m13 !!! Regidx a1_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq m12 (Regidx a1_idx) _).

    (* ---- 0x50a  c.mv ---- *)
    assert (Hw14 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (m13 !!! Regidx s3_idx))
      by (rewrite Hv_s3_idx_13 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P11 m13 (mword_of_int 0x50a)
              a0_idx s3_idx (mword_of_int psaddr : mword 64)
              (ui_sh_50a pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Hw14 with "Hcg Hpc").
    iIntros (CIDm14) "Hcg Hpc".
    set (m14 := <[Regidx a0_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> m13).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x50a : mword 64) 2
                      = mword_of_int 0x50c)) in "Hpc".
    assert (Hq14 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              m14 !!! Regidx r = m13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m13 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_14 : m14 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq14 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_13).
    assert (Hv_s4_idx_14 : m14 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq14 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_13).
    assert (Hv_a2_idx_14 : m14 !!! Regidx a2_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq14 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_13).
    assert (Hv_a1_idx_14 : m14 !!! Regidx a1_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq14 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_13).
    assert (Hv_a0_idx_14 : m14 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq m13 (Regidx a0_idx) _).

    (* ---- 0x50c  jal ra, 0x448 <peek> ---- *)
    assert (Htgtp : (mword_of_int 0x448 : mword 64)
                    = add_vec (mword_of_int 0x50c)
                        (sign_extend' 64 (mword_of_int 2096956 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlinkp : (mword_of_int 0x510 : mword 64)
                     = add_vec_int (mword_of_int 0x50c : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh P11 m14 (mword_of_int 0x50c)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x510)
              (ui_sh_50c pt P11 Hltext (sh_img_text P11 Hg11))
              ltac:(vm_compute; discriminate) Htgtp Hlinkp
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDpk) "Hcg Hpc".
    set (m15 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x510 : mword 64)]> m14).
    assert (Hq15 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              m15 !!! Regidx r = m14 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m14 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_15 : m15 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 112) : mword 64))
      by (rewrite (Hq15 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_14).
    assert (Hv_s4_idx_15 : m15 !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_14).
    assert (Hv_a2_idx_15 : m15 !!! Regidx a2_idx = (mword_of_int 4848 : mword 64))
      by (rewrite (Hq15 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_14).
    assert (Hv_a1_idx_15 : m15 !!! Regidx a1_idx = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq15 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_14).
    assert (Hv_a0_idx_15 : m15 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq15 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_14).
    assert (Hv_ra_idx_15 : m15 !!! Regidx ra_idx = (mword_of_int 0x510 : mword 64))
      by exact (upd_eq m14 (Regidx ra_idx) _).


    (* ---- the eleven spilled slots, read back out of the tower ---- *)
    assert (HbNra : uM_bytes P11 (uint sp0 - 112 + 104) 8 (m1 !!! Regidx ra_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs0 : uM_bytes P11 (uint sp0 - 112 + 96) 8 (m1 !!! Regidx s0_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs1 : uM_bytes P11 (uint sp0 - 112 + 88) 8 (m1 !!! Regidx s1_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs2 : uM_bytes P11 (uint sp0 - 112 + 80) 8 (m1 !!! Regidx s2_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs3 : uM_bytes P11 (uint sp0 - 112 + 72) 8 (m1 !!! Regidx s3_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs4 : uM_bytes P11 (uint sp0 - 112 + 64) 8 (m1 !!! Regidx s4_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs5 : uM_bytes P11 (uint sp0 - 112 + 56) 8 (m1 !!! Regidx s5_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs6 : uM_bytes P11 (uint sp0 - 112 + 48) 8 (m1 !!! Regidx s6_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs7 : uM_bytes P11 (uint sp0 - 112 + 40) 8 (m1 !!! Regidx s7_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs8 : uM_bytes P11 (uint sp0 - 112 + 32) 8 (m1 !!! Regidx s8_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbNs9 : uM_bytes P11 (uint sp0 - 112 + 24) 8 (m1 !!! Regidx s9_idx)).
    { unfold P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }

    (* ---- 0x448  peek(ps, es, "<>") -- returns 0 ---- *)
    assert (HpreK : sh_parse_pre pt hbase hlen P11 s0 bs
                      (mword_of_int (uint sp0 - 112) : mword 64) 80).
    { apply (parse_pre_move M P11 s0 bs sp0 (mword_of_int (uint sp0 - 112))
               192 80).
      - exact (proj1 Ho11).
      - intros k Hk. exact (proj2 Ho11 k ltac:(lia)).
      - intros k Hk. exact (proj2 Ho11 k ltac:(lia)).
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hpre. }
    assert (HstkK : uv_stack pt P11 (mword_of_int (uint sp0 - 112) : mword 64) 80)
      by exact (stk_dom M P11 _ 80 (proj1 Ho11) Hstk80).
    assert (HcellK : sh_ptr_cell pt P11 psaddr (s0 + Z.of_nat off)
                       (mword_of_int (uint sp0 - 112) : mword 64)).
    { apply (ptr_cell_move M P11 psaddr (s0 + Z.of_nat off) sp0).
      - exact (proj1 Ho11).
      - intros k Hk. exact (proj2 Ho11 k ltac:(lia)).
      - rewrite Huspk. lia.
      - exact Hcell. }
    assert (Htbhi : 4848 + Z.of_nat (length sh_tb_lt) + 1 <= 8192)
      by (rewrite sh_tb_lt_len; lia).
    assert (Htbfr : 4848 + Z.of_nat (length sh_tb_lt) + 1
                    <= uint (mword_of_int (uint sp0 - 112) : mword 64) - 80)
      by (rewrite Huspk sh_tb_lt_len; lia).
    assert (Hret2K : is_aligned_vaddr (Virtaddr (m15 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_15; vm_compute; reflexivity).
    iApply (wp_sh_peek_zero CIDpk P11 m15 (mword_of_int (uint sp0 - 112))
              psaddr s0 4848 bs off sh_tb_lt
              HpreK Hv_csp_rs1_15 HstkK Hv_a0_idx_15 Hv_a1_idx_15 Hv_a2_idx_15
              HcellK Hoff ltac:(lia) Htbhi Htbfr
              sh_tb_lt_data sh_tb_lt_sym Hret2K with "Hcg Hpc [Hcont]").
    iIntros (CIDk mk Mk) "%HcsK %Ha0K %HpscK %HonlyK Hcg Hpc".
    iEval (rewrite Hv_ra_idx_15) in "Hpc".
    rewrite Huspk in HonlyK.
    assert (HgK : sh_img_sub Mk).
    { destruct Hg11 as (Ht & Hd). split.
      - intros k b Hk.
        rewrite (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k HonlyK
                   ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)
                   ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
        exact (Ht k b Hk).
      - intros k b Hk.
        rewrite (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k HonlyK
                   ltac:(pose proof (sh_data_key_lt k b Hk); lia)
                   ltac:(pose proof (sh_data_key_lt k b Hk); lia)).
        exact (Hd k b Hk). }
    assert (HkK : uv_stack pt Mk sp0 112)
      by exact (stk_dom P11 Mk sp0 112 (proj1 HonlyK) Hk11).
    assert (HbKra : uM_bytes Mk (uint sp0 - 112 + 104) 8 (m1 !!! Regidx ra_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 104)); [ | exact HbNra ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs0 : uM_bytes Mk (uint sp0 - 112 + 96) 8 (m1 !!! Regidx s0_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 96)); [ | exact HbNs0 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs1 : uM_bytes Mk (uint sp0 - 112 + 88) 8 (m1 !!! Regidx s1_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 88)); [ | exact HbNs1 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs2 : uM_bytes Mk (uint sp0 - 112 + 80) 8 (m1 !!! Regidx s2_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 80)); [ | exact HbNs2 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs3 : uM_bytes Mk (uint sp0 - 112 + 72) 8 (m1 !!! Regidx s3_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 72)); [ | exact HbNs3 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs4 : uM_bytes Mk (uint sp0 - 112 + 64) 8 (m1 !!! Regidx s4_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 64)); [ | exact HbNs4 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs5 : uM_bytes Mk (uint sp0 - 112 + 56) 8 (m1 !!! Regidx s5_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 56)); [ | exact HbNs5 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs6 : uM_bytes Mk (uint sp0 - 112 + 48) 8 (m1 !!! Regidx s6_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 48)); [ | exact HbNs6 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs7 : uM_bytes Mk (uint sp0 - 112 + 40) 8 (m1 !!! Regidx s7_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 40)); [ | exact HbNs7 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs8 : uM_bytes Mk (uint sp0 - 112 + 32) 8 (m1 !!! Regidx s8_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 32)); [ | exact HbNs8 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }
    assert (HbKs9 : uM_bytes Mk (uint sp0 - 112 + 24) 8 (m1 !!! Regidx s9_idx)).
    { apply (bytes_eq8 P11 Mk (uint sp0 - 112 + 24)); [ | exact HbNs9 ].
      intros k Hk. exact (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k
                            HonlyK ltac:(lia) ltac:(lia)). }

    (* ---- 0x510  c.beqz a0,0x574  -- TAKEN ---- *)
    assert (Htk0 : true = eq_vec (mk !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0K (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    assert (Htgt0 : (mword_of_int 0x574 : mword 64)
                    = add_vec (mword_of_int 0x510)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 50 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cbeqz C pt Psh Mk mk (mword_of_int 0x510)
              (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x574)
              (ui_sh_510 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; reflexivity) Htk0 Htgt0
              ltac:(intros _; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDbz) "Hcg Hpc".
    (* ---- 0x574  c.mv a0,s4 ---- *)
    assert (Hs4K : mk !!! Regidx s4_idx = (mword_of_int cmd : mword 64))
      by (rewrite (HcsK s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_15).
    assert (Hw574 : (mword_of_int cmd : mword 64)
                    = add_vec zero_reg (mk !!! Regidx s4_idx))
      by (rewrite Hs4K moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mk mk (mword_of_int 0x574)
              a0_idx s4_idx (mword_of_int cmd)
              (ui_sh_574 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) Hw574 with "Hcg Hpc").
    iIntros (CIDe0) "Hcg Hpc".
    set (mA := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> mk).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x574 : mword 64) 2
                      = mword_of_int 0x576)) in "Hpc".
    assert (HspA : mA !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 112) : mword 64)).
    { rewrite (upd_ne mk (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HcsK csp_rs1 ltac:(vm_compute; reflexivity)).
      exact Hv_csp_rs1_15. }
    assert (Ha0A : mA !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq mk (Regidx a0_idx) _).

    (* ---- 0x576  c.ldsp ra,104(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe0 Psh Mk mA sp0 (mword_of_int 0x576)
              (mword_of_int 13 : mword 6) ra_idx 112 104 (m1 !!! Regidx ra_idx)
              (ui_sh_576 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspA
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 104)
                        (m1 !!! Regidx ra_idx) HbKra))
              with "Hcg Hpc").
    iIntros (CIDe1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x576 : mword 64) 2
                      = mword_of_int 0x578)) in "Hpc".
    set (mR1 := <[Regidx ra_idx := regval_into_reg (m1 !!! Regidx ra_idx)]> mA).
    assert (HspR1 : mR1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mA (Regidx ra_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspA).
    assert (Hvra1 : mR1 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (upd_eq mA (Regidx ra_idx) _).

    (* ---- 0x578  c.ldsp s0,96(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe1 Psh Mk mR1 sp0 (mword_of_int 0x578)
              (mword_of_int 12 : mword 6) s0_idx 112 96 (m1 !!! Regidx s0_idx)
              (ui_sh_578 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 96)
                        (m1 !!! Regidx s0_idx) HbKs0))
              with "Hcg Hpc").
    iIntros (CIDe2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x578 : mword 64) 2
                      = mword_of_int 0x57a)) in "Hpc".
    set (mR2 := <[Regidx s0_idx := regval_into_reg (m1 !!! Regidx s0_idx)]> mR1).
    assert (HspR2 : mR2 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR1 (Regidx s0_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR1).
    assert (Hvs02 : mR2 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (upd_eq mR1 (Regidx s0_idx) _).
    assert (Hvra2 : mR2 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR1 (Regidx s0_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra1).

    (* ---- 0x57a  c.ldsp s1,88(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe2 Psh Mk mR2 sp0 (mword_of_int 0x57a)
              (mword_of_int 11 : mword 6) s1_idx 112 88 (m1 !!! Regidx s1_idx)
              (ui_sh_57a pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 88)
                        (m1 !!! Regidx s1_idx) HbKs1))
              with "Hcg Hpc").
    iIntros (CIDe3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x57a : mword 64) 2
                      = mword_of_int 0x57c)) in "Hpc".
    set (mR3 := <[Regidx s1_idx := regval_into_reg (m1 !!! Regidx s1_idx)]> mR2).
    assert (HspR3 : mR3 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR2 (Regidx s1_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR2).
    assert (Hvs13 : mR3 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (upd_eq mR2 (Regidx s1_idx) _).
    assert (Hvra3 : mR3 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR2 (Regidx s1_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra2).
    assert (Hvs03 : mR3 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR2 (Regidx s1_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs02).

    (* ---- 0x57c  c.ldsp s2,80(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe3 Psh Mk mR3 sp0 (mword_of_int 0x57c)
              (mword_of_int 10 : mword 6) s2_idx 112 80 (m1 !!! Regidx s2_idx)
              (ui_sh_57c pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 80)
                        (m1 !!! Regidx s2_idx) HbKs2))
              with "Hcg Hpc").
    iIntros (CIDe4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x57c : mword 64) 2
                      = mword_of_int 0x57e)) in "Hpc".
    set (mR4 := <[Regidx s2_idx := regval_into_reg (m1 !!! Regidx s2_idx)]> mR3).
    assert (HspR4 : mR4 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR3).
    assert (Hvs24 : mR4 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (upd_eq mR3 (Regidx s2_idx) _).
    assert (Hvra4 : mR4 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra3).
    assert (Hvs04 : mR4 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs03).
    assert (Hvs14 : mR4 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR3 (Regidx s2_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs13).

    (* ---- 0x57e  c.ldsp s3,72(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe4 Psh Mk mR4 sp0 (mword_of_int 0x57e)
              (mword_of_int 9 : mword 6) s3_idx 112 72 (m1 !!! Regidx s3_idx)
              (ui_sh_57e pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 72)
                        (m1 !!! Regidx s3_idx) HbKs3))
              with "Hcg Hpc").
    iIntros (CIDe5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x57e : mword 64) 2
                      = mword_of_int 0x580)) in "Hpc".
    set (mR5 := <[Regidx s3_idx := regval_into_reg (m1 !!! Regidx s3_idx)]> mR4).
    assert (HspR5 : mR5 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR4).
    assert (Hvs35 : mR5 !!! Regidx s3_idx = m1 !!! Regidx s3_idx)
      by exact (upd_eq mR4 (Regidx s3_idx) _).
    assert (Hvra5 : mR5 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra4).
    assert (Hvs05 : mR5 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs04).
    assert (Hvs15 : mR5 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs14).
    assert (Hvs25 : mR5 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne mR4 (Regidx s3_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs24).

    (* ---- 0x580  c.ldsp s4,64(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe5 Psh Mk mR5 sp0 (mword_of_int 0x580)
              (mword_of_int 8 : mword 6) s4_idx 112 64 (m1 !!! Regidx s4_idx)
              (ui_sh_580 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 64)
                        (m1 !!! Regidx s4_idx) HbKs4))
              with "Hcg Hpc").
    iIntros (CIDe6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x580 : mword 64) 2
                      = mword_of_int 0x582)) in "Hpc".
    set (mR6 := <[Regidx s4_idx := regval_into_reg (m1 !!! Regidx s4_idx)]> mR5).
    assert (HspR6 : mR6 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR5).
    assert (Hvs46 : mR6 !!! Regidx s4_idx = m1 !!! Regidx s4_idx)
      by exact (upd_eq mR5 (Regidx s4_idx) _).
    assert (Hvra6 : mR6 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra5).
    assert (Hvs06 : mR6 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs05).
    assert (Hvs16 : mR6 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs15).
    assert (Hvs26 : mR6 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs25).
    assert (Hvs36 : mR6 !!! Regidx s3_idx = m1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne mR5 (Regidx s4_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs35).

    (* ---- 0x582  c.ldsp s5,56(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe6 Psh Mk mR6 sp0 (mword_of_int 0x582)
              (mword_of_int 7 : mword 6) s5_idx 112 56 (m1 !!! Regidx s5_idx)
              (ui_sh_582 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR6
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 56)
                        (m1 !!! Regidx s5_idx) HbKs5))
              with "Hcg Hpc").
    iIntros (CIDe7) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x582 : mword 64) 2
                      = mword_of_int 0x584)) in "Hpc".
    set (mR7 := <[Regidx s5_idx := regval_into_reg (m1 !!! Regidx s5_idx)]> mR6).
    assert (HspR7 : mR7 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR6).
    assert (Hvs57 : mR7 !!! Regidx s5_idx = m1 !!! Regidx s5_idx)
      by exact (upd_eq mR6 (Regidx s5_idx) _).
    assert (Hvra7 : mR7 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra6).
    assert (Hvs07 : mR7 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs06).
    assert (Hvs17 : mR7 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs16).
    assert (Hvs27 : mR7 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs26).
    assert (Hvs37 : mR7 !!! Regidx s3_idx = m1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs36).
    assert (Hvs47 : mR7 !!! Regidx s4_idx = m1 !!! Regidx s4_idx)
      by exact (eq_trans (upd_ne mR6 (Regidx s5_idx) (Regidx s4_idx) _
                           ltac:(vm_compute; discriminate)) Hvs46).

    (* ---- 0x584  c.ldsp s6,48(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe7 Psh Mk mR7 sp0 (mword_of_int 0x584)
              (mword_of_int 6 : mword 6) s6_idx 112 48 (m1 !!! Regidx s6_idx)
              (ui_sh_584 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR7
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 48)
                        (m1 !!! Regidx s6_idx) HbKs6))
              with "Hcg Hpc").
    iIntros (CIDe8) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x584 : mword 64) 2
                      = mword_of_int 0x586)) in "Hpc".
    set (mR8 := <[Regidx s6_idx := regval_into_reg (m1 !!! Regidx s6_idx)]> mR7).
    assert (HspR8 : mR8 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR7).
    assert (Hvs68 : mR8 !!! Regidx s6_idx = m1 !!! Regidx s6_idx)
      by exact (upd_eq mR7 (Regidx s6_idx) _).
    assert (Hvra8 : mR8 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra7).
    assert (Hvs08 : mR8 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs07).
    assert (Hvs18 : mR8 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs17).
    assert (Hvs28 : mR8 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs27).
    assert (Hvs38 : mR8 !!! Regidx s3_idx = m1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs37).
    assert (Hvs48 : mR8 !!! Regidx s4_idx = m1 !!! Regidx s4_idx)
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx s4_idx) _
                           ltac:(vm_compute; discriminate)) Hvs47).
    assert (Hvs58 : mR8 !!! Regidx s5_idx = m1 !!! Regidx s5_idx)
      by exact (eq_trans (upd_ne mR7 (Regidx s6_idx) (Regidx s5_idx) _
                           ltac:(vm_compute; discriminate)) Hvs57).

    (* ---- 0x586  c.ldsp s7,40(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe8 Psh Mk mR8 sp0 (mword_of_int 0x586)
              (mword_of_int 5 : mword 6) s7_idx 112 40 (m1 !!! Regidx s7_idx)
              (ui_sh_586 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 40)
                        (m1 !!! Regidx s7_idx) HbKs7))
              with "Hcg Hpc").
    iIntros (CIDe9) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x586 : mword 64) 2
                      = mword_of_int 0x588)) in "Hpc".
    set (mR9 := <[Regidx s7_idx := regval_into_reg (m1 !!! Regidx s7_idx)]> mR8).
    assert (HspR9 : mR9 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR8).
    assert (Hvs79 : mR9 !!! Regidx s7_idx = m1 !!! Regidx s7_idx)
      by exact (upd_eq mR8 (Regidx s7_idx) _).
    assert (Hvra9 : mR9 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra8).
    assert (Hvs09 : mR9 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs08).
    assert (Hvs19 : mR9 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs18).
    assert (Hvs29 : mR9 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs28).
    assert (Hvs39 : mR9 !!! Regidx s3_idx = m1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs38).
    assert (Hvs49 : mR9 !!! Regidx s4_idx = m1 !!! Regidx s4_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx s4_idx) _
                           ltac:(vm_compute; discriminate)) Hvs48).
    assert (Hvs59 : mR9 !!! Regidx s5_idx = m1 !!! Regidx s5_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx s5_idx) _
                           ltac:(vm_compute; discriminate)) Hvs58).
    assert (Hvs69 : mR9 !!! Regidx s6_idx = m1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne mR8 (Regidx s7_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs68).

    (* ---- 0x588  c.ldsp s8,32(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe9 Psh Mk mR9 sp0 (mword_of_int 0x588)
              (mword_of_int 4 : mword 6) s8_idx 112 32 (m1 !!! Regidx s8_idx)
              (ui_sh_588 pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 32)
                        (m1 !!! Regidx s8_idx) HbKs8))
              with "Hcg Hpc").
    iIntros (CIDe10) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x588 : mword 64) 2
                      = mword_of_int 0x58a)) in "Hpc".
    set (mR10 := <[Regidx s8_idx := regval_into_reg (m1 !!! Regidx s8_idx)]> mR9).
    assert (HspR10 : mR10 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR9).
    assert (Hvs810 : mR10 !!! Regidx s8_idx = m1 !!! Regidx s8_idx)
      by exact (upd_eq mR9 (Regidx s8_idx) _).
    assert (Hvra10 : mR10 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra9).
    assert (Hvs010 : mR10 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs09).
    assert (Hvs110 : mR10 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs19).
    assert (Hvs210 : mR10 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs29).
    assert (Hvs310 : mR10 !!! Regidx s3_idx = m1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs39).
    assert (Hvs410 : mR10 !!! Regidx s4_idx = m1 !!! Regidx s4_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s4_idx) _
                           ltac:(vm_compute; discriminate)) Hvs49).
    assert (Hvs510 : mR10 !!! Regidx s5_idx = m1 !!! Regidx s5_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s5_idx) _
                           ltac:(vm_compute; discriminate)) Hvs59).
    assert (Hvs610 : mR10 !!! Regidx s6_idx = m1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs69).
    assert (Hvs710 : mR10 !!! Regidx s7_idx = m1 !!! Regidx s7_idx)
      by exact (eq_trans (upd_ne mR9 (Regidx s8_idx) (Regidx s7_idx) _
                           ltac:(vm_compute; discriminate)) Hvs79).

    (* ---- 0x58a  c.ldsp s9,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDe10 Psh Mk mR10 sp0 (mword_of_int 0x58a)
              (mword_of_int 3 : mword 6) s9_idx 112 24 (m1 !!! Regidx s9_idx)
              (ui_sh_58a pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) HkK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR10
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 112 + 24)
                        (m1 !!! Regidx s9_idx) HbKs9))
              with "Hcg Hpc").
    iIntros (CIDe11) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x58a : mword 64) 2
                      = mword_of_int 0x58c)) in "Hpc".
    set (mR11 := <[Regidx s9_idx := regval_into_reg (m1 !!! Regidx s9_idx)]> mR10).
    assert (HspR11 : mR11 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 112) : mword 64))
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR10).
    assert (Hvs911 : mR11 !!! Regidx s9_idx = m1 !!! Regidx s9_idx)
      by exact (upd_eq mR10 (Regidx s9_idx) _).
    assert (Hvra11 : mR11 !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra10).
    assert (Hvs011 : mR11 !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs010).
    assert (Hvs111 : mR11 !!! Regidx s1_idx = m1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs110).
    assert (Hvs211 : mR11 !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs210).
    assert (Hvs311 : mR11 !!! Regidx s3_idx = m1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs310).
    assert (Hvs411 : mR11 !!! Regidx s4_idx = m1 !!! Regidx s4_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s4_idx) _
                           ltac:(vm_compute; discriminate)) Hvs410).
    assert (Hvs511 : mR11 !!! Regidx s5_idx = m1 !!! Regidx s5_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s5_idx) _
                           ltac:(vm_compute; discriminate)) Hvs510).
    assert (Hvs611 : mR11 !!! Regidx s6_idx = m1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs610).
    assert (Hvs711 : mR11 !!! Regidx s7_idx = m1 !!! Regidx s7_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s7_idx) _
                           ltac:(vm_compute; discriminate)) Hvs710).
    assert (Hvs811 : mR11 !!! Regidx s8_idx = m1 !!! Regidx s8_idx)
      by exact (eq_trans (upd_ne mR10 (Regidx s9_idx) (Regidx s8_idx) _
                           ltac:(vm_compute; discriminate)) Hvs810).

    assert (HpR : forall r : mword 5,
              Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx ->
              Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx ->
              Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx ->
              Regidx r <> Regidx s6_idx ->
              Regidx r <> Regidx s7_idx ->
              Regidx r <> Regidx s8_idx ->
              Regidx r <> Regidx s9_idx ->
              mR11 !!! Regidx r = mA !!! Regidx r).
    { intros r N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11.
      rewrite (upd_ne mR10 (Regidx s9_idx) (Regidx r) _ N11).
      rewrite (upd_ne mR9 (Regidx s8_idx) (Regidx r) _ N10).
      rewrite (upd_ne mR8 (Regidx s7_idx) (Regidx r) _ N9).
      rewrite (upd_ne mR7 (Regidx s6_idx) (Regidx r) _ N8).
      rewrite (upd_ne mR6 (Regidx s5_idx) (Regidx r) _ N7).
      rewrite (upd_ne mR5 (Regidx s4_idx) (Regidx r) _ N6).
      rewrite (upd_ne mR4 (Regidx s3_idx) (Regidx r) _ N5).
      rewrite (upd_ne mR3 (Regidx s2_idx) (Regidx r) _ N4).
      rewrite (upd_ne mR2 (Regidx s1_idx) (Regidx r) _ N3).
      rewrite (upd_ne mR1 (Regidx s0_idx) (Regidx r) _ N2).
      exact (upd_ne mA (Regidx ra_idx) (Regidx r) _ N1). }

    (* ---- 0x58c  c.addi16sp sp,sp,112 ---- *)
    assert (Hwsp2 : sp0 = add_vec (mR11 !!! Regidx csp_rs1)
                            (sign_extend' 64
                               (caddi16sp_imm (mword_of_int 7 : mword 6)))).
    { rewrite HspR11.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))
                    : mword 64) = mword_of_int 112)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 112 + 112) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh Mk mR11 (mword_of_int 0x58c)
              (mword_of_int 7 : mword 6) sp0
              (ui_sh_58c pt Mk Hltext (sh_img_text Mk HgK)) Hwsp2
              with "Hcg Hpc").
    iIntros (CIDf) "Hcg Hpc".
    set (mS := <[Regidx csp_rs1 := regval_into_reg sp0]> mR11).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x58c : mword 64) 2
                      = mword_of_int 0x58e)) in "Hpc".
    (* ---- 0x58e  c.jr ra ---- *)
    assert (HraS : mS !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne mR11 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite Hvra11. exact (Hq1 ra_idx ltac:(vm_compute; discriminate)). }
    assert (Htgtr : (m !!! Regidx ra_idx) = ret_pc (mS !!! Regidx ra_idx)).
    { rewrite HraS. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh Mk mS (mword_of_int 0x58e)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_58e pt Mk Hltext (sh_img_text Mk HgK))
              ltac:(vm_compute; discriminate) Htgtr with "Hcg Hpc").
    iIntros (CIDz) "Hcg Hpc".
    iApply ("Hcont" $! CIDz mS Mk with "[] [] [] [] Hcg Hpc").
    - (* ucallee_saved *)
      iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Nsp ].
      { rewrite Esp. rewrite (upd_eq mR11 (Regidx csp_rs1) _). symmetry. exact Hsp. }
      rewrite (upd_ne mR11 (Regidx csp_rs1) (Regidx r) _ Nsp).
      destruct (decide (Regidx r = Regidx s0_idx)) as [ Es0 | Ns0 ].
      { rewrite Es0 Hvs011.
        exact (Hq1 s0_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s1_idx)) as [ Es1 | Ns1 ].
      { rewrite Es1 Hvs111.
        exact (Hq1 s1_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s2_idx)) as [ Es2 | Ns2 ].
      { rewrite Es2 Hvs211.
        exact (Hq1 s2_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s3_idx)) as [ Es3 | Ns3 ].
      { rewrite Es3 Hvs311.
        exact (Hq1 s3_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s4_idx)) as [ Es4 | Ns4 ].
      { rewrite Es4 Hvs411.
        exact (Hq1 s4_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s5_idx)) as [ Es5 | Ns5 ].
      { rewrite Es5 Hvs511.
        exact (Hq1 s5_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s6_idx)) as [ Es6 | Ns6 ].
      { rewrite Es6 Hvs611.
        exact (Hq1 s6_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s7_idx)) as [ Es7 | Ns7 ].
      { rewrite Es7 Hvs711.
        exact (Hq1 s7_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s8_idx)) as [ Es8 | Ns8 ].
      { rewrite Es8 Hvs811.
        exact (Hq1 s8_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s9_idx)) as [ Es9 | Ns9 ].
      { rewrite Es9 Hvs911.
        exact (Hq1 s9_idx ltac:(vm_compute; discriminate)). }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HpR r Nra Ns0 Ns1 Ns2 Ns3 Ns4 Ns5 Ns6 Ns7 Ns8 Ns9).
      rewrite (upd_ne mk (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (HcsK r Hr).
      rewrite (Hq15 r Nra) (Hq14 r Na0) (Hq13 r Na1) (Hq12 r Na2)
              (Hq11 r Ns5) (Hq10 r Ns7) (Hq9 r Ns8) (Hq8 r Ns9)
              (Hq7 r Ns6) (Hq6 r Ns6) (Hq5 r Ns2) (Hq4 r Ns3)
              (Hq3 r Ns4) (Hq2 r Ns0).
      exact (Hq1 r Nsp).
    - (* a0 = cmd *)
      iPureIntro.
      rewrite (upd_ne mR11 (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpR a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact Ha0A.
    - (* the [ps] cell *)
      iPureIntro. exact HpscK.
    - (* the disturbed windows *)
      iPureIntro. cbv [sh_win].
      apply (win2_in M Mk psaddr 8 (uint sp0 - 192) 192).
      + intros k Hk. exact (proj1 HonlyK k (proj1 Ho11 k Hk)).
      + intros k H1 H2.
        rewrite (win2_out P11 Mk psaddr 8 (uint sp0 - 112 - 80) 80 k HonlyK
                   H1 ltac:(lia)).
        exact (proj2 Ho11 k ltac:(lia)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3d  parseexec's ARGUMENT LOOP, head 0x622, back edge 0x620.          *)
  (*                                                                       *)
  (*   622  mv a2,s6; mv a1,s5; mv a0,s4; jal peek   -- 0, so the body runs *)
  (*   62c  bnez a0,662         -- not taken                               *)
  (*   62e  mv a3,s8; mv a2,s7; mv a1,s5; mv a0,s4; jal gettoken           *)
  (*   63a  beqz a0,662         -- TAKEN exactly when no token is left     *)
  (*   63c  bne a0,s10,608      -- the `syntax' panic: never, the token    *)
  (*                               arm always returns 'a'                  *)
  (*   640  ld a5,-120(s0); sd a5,0(s3)     -- argv[argc]  = q             *)
  (*   648  ld a5,-128(s0); sd a5,80(s3)    -- eargv[argc] = eq            *)
  (*   650  addiw s2,s2,1; bne s2,s9,614    -- the MAXARGS panic: never    *)
  (*   614  addi s3,s3,8; mv a2,s5; mv a1,s4; mv a0,s1; jal parseredirs    *)
  (*   620  mv s1,a0            -- back to 622                             *)
  (*                                                                       *)
  (* Ordinary Rocq induction on the STRICT measure [|toksR|]: the branch    *)
  (* leaves are later-free, so a bounded loop pays no [>].  The invariant   *)
  (* IS [sh_tokens bs offi toksR] -- one constructor per iteration.         *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_pe_loop (nn : nat) :
    forall (CIDp : CpuId) (Mi0 Mi : gmap Z (bv 8)) (mE : regfile)
      (sp0 : mword 64) (psaddr sb cmd : Z) (bs : list (bv 8))
      (offi i : nat) (toks toksR : list (nat * nat)),
      (length toksR < nn)%nat ->
      sh_parse_pre pt hbase hlen Mi0 sb bs sp0 320 ->
      sh_buf_clear hbase sb (Z.of_nat (length bs) + 1) ->
      uv_stack pt Mi0 sp0 320 ->
      (i <= length toks)%nat ->
      toksR = drop i toks ->
      sh_tokens bs offi toksR ->
      (length toks < 10)%nat ->
      (offi <= length bs)%nat ->
      hbase <= cmd -> cmd + 168 <= hbase + 65536 -> cmd mod 16 = 0 ->
      uint sp0 <= psaddr -> psaddr + 8 <= 2 ^ 38 -> psaddr mod 8 = 0 ->
      uv_rd pt Mi0 psaddr 8 -> uv_wr pt Mi0 psaddr 8 -> uv_wr pt Mi0 cmd 168 ->
      uM_only_in Mi0 Mi [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)] ->
      uM_bytes Mi psaddr 8 (mword_of_int (sb + Z.of_nat offi) : mword 64) ->
      uM_bytes Mi cmd 4 (mword_of_int 1 : mword 32) ->
      (forall (j : nat) (t : nat * nat), take i toks !! j = Some t ->
         uM_bytes Mi (cmd + 8 + 8 * Z.of_nat j) 8
           (mword_of_int (sb + Z.of_nat (fst t)) : mword 64) /\
         uM_bytes Mi (cmd + 88 + 8 * Z.of_nat j) 8
           (mword_of_int (sb + Z.of_nat (snd t)) : mword 64)) ->
      mE !!! Regidx sp_idx  = (mword_of_int (uint sp0 - 128) : mword 64) ->
      mE !!! Regidx s0_idx  = (mword_of_int (uint sp0) : mword 64) ->
      mE !!! Regidx s1_idx  = (mword_of_int cmd : mword 64) ->
      mE !!! Regidx s2_idx  = (mword_of_int (Z.of_nat i) : mword 64) ->
      mE !!! Regidx s3_idx  = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64) ->
      mE !!! Regidx s4_idx  = (mword_of_int psaddr : mword 64) ->
      mE !!! Regidx s5_idx
        = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64) ->
      mE !!! Regidx s6_idx  = (mword_of_int 4888 : mword 64) ->
      mE !!! Regidx s7_idx  = (mword_of_int (uint sp0 - 120) : mword 64) ->
      mE !!! Regidx s8_idx  = (mword_of_int (uint sp0 - 128) : mword 64) ->
      mE !!! Regidx s9_idx  = (mword_of_int 10 : mword 64) ->
      mE !!! Regidx s10_idx = (mword_of_int 97 : mword 64) ->
      mE !!! Regidx s11_idx = (mword_of_int cmd : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh Mi mE -∗
      pc_is (CID := CIDp) (mword_of_int 0x622) -∗
      (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
         ⌜uM_only_in Mi0 M'
            [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)]⌝ -∗
         ⌜uM_bytes M' cmd 4 (mword_of_int 1 : mword 32)⌝ -∗
         ⌜forall (j : nat) (t : nat * nat), toks !! j = Some t ->
            uM_bytes M' (cmd + 8 + 8 * Z.of_nat j) 8
              (mword_of_int (sb + Z.of_nat (fst t)) : mword 64) /\
            uM_bytes M' (cmd + 88 + 8 * Z.of_nat j) 8
              (mword_of_int (sb + Z.of_nat (snd t)) : mword 64)⌝ -∗
         (* WHERE THE PARSE STOPPED: at the end of the buffer.  Without it
            no caller can run the [peek] it does next. *)
         ⌜uM_bytes M' psaddr 8
            (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)⌝ -∗
         ⌜m' !!! Regidx s1_idx = (mword_of_int cmd : mword 64)⌝ -∗
         ⌜m' !!! Regidx s2_idx
            = (mword_of_int (Z.of_nat (length toks)) : mword 64)⌝ -∗
         ⌜forall r : mword 5, ucallee_saved_idx r = true ->
            Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
            Regidx r <> Regidx s3_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
         pc_is (CID := CID) (mword_of_int 0x662) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction nn as [ | nn IH ];
      intros CIDp Mi0 Mi mE sp0 psaddr sb cmd bs offi i toks toksR
             Hmeas Hpre0 Hbc Hstk0 Hile HtR Htoks Hmax Hoff
             Hcmdlo Hcmdhi Hcmd16 Hpslo Hpshi Hpsal Hrdps0 Hwrps0 Hwrnd0
             HW Hcell Htype Harg
             HspE Hs0E Hs1E Hs2E Hs3E Hs4E Hs5E Hs6E Hs7E Hs8E Hs9E Hs10E Hs11E.
    { exfalso. lia. }
    pose proof Hpre0 as (Hlay & Himg0 & Htab0 & Hbuf0 & Hns & Hrdb0 & Hwrb0 &
                         Hs0p & Hs0hi & Hfr & Hbufhi).
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    unfold sh_frame_ok in Hfr.
    pose proof (us_lo _ _ _ _ Hstk0) as Hlo.
    pose proof (us_canon _ _ _ _ Hstk0) as Hcan.
    pose proof (us_al _ _ _ _ Hstk0) as Hal16.
    rewrite Z.rem_mod_nonneg in Hal16; [ | lia | lia ].
    change (2 ^ 38) with 274877906944 in Hcan, Hs0hi, Hpshi.
    pose proof Hbc as (Hbd1 & Hbd2 & Hbd3). unfold sh_disj in Hbd1, Hbd2, Hbd3.
    change SH_FREEP with 8208 in Hbd1. change SH_BASE with 8328 in Hbd2.
    (* everything about the CURRENT image, off the three-window invariant *)
    assert (Hprei : sh_parse_pre pt hbase hlen Mi sb bs sp0 320)
      by exact (pe_w3_pre Mi0 Mi sb psaddr bs sp0 HW Hbc Hpslo Hpre0).
    pose proof Hprei as (_ & Hgi & _ & _ & _ & Hrdbi & Hwrbi & _).
    assert (Hstki : uv_stack pt Mi sp0 320)
      by exact (stk_dom Mi0 Mi sp0 320 (proj1 HW) Hstk0).
    assert (Hrdpsi : uv_rd pt Mi psaddr 8)
      by exact (uv_rd_dom pt Mi0 Mi psaddr 8 (proj1 HW) Hrdps0).
    assert (Hwrpsi : uv_wr pt Mi psaddr 8)
      by exact (uv_wr_dom pt Mi0 Mi psaddr 8 (proj1 HW) Hwrps0).
    assert (Hwrndi : uv_wr pt Mi cmd 168)
      by exact (uv_wr_dom pt Mi0 Mi cmd 168 (proj1 HW) Hwrnd0).
    (* the two stack slices the callees get *)
    destruct (uv_stack_split pt Mi sp0 320 128 192 ltac:(lia) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hstki)
      as (Hstk128 & Hstk192).
    rewrite (uv_stack_sp_moi pt Mi sp0 128 Hstk128) in Hstk192.
    assert (Huspk : uint (mword_of_int (uint sp0 - 128) : mword 64)
                    = uint sp0 - 128)
      by (apply uint_moi; unfold Z64; lia).
    destruct (uv_stack_split pt Mi (mword_of_int (uint sp0 - 128)) 192 80 112
                ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                Hstk192) as (Hstk80 & _).
    (* the two 8-alignments every slot access needs *)
    assert (Hsp16q : uint sp0 = 16 * (uint sp0 / 16))
      by (pose proof (Z.div_mod (uint sp0) 16 ltac:(lia)); lia).
    assert (Hspmod8 : forall z : Z, (uint sp0 + 8 * z) mod 8 = 0).
    { intro z.
      assert (Hz : uint sp0 + 8 * z = 8 * (2 * (uint sp0 / 16) + z)) by lia.
      rewrite Hz Z.mul_comm. apply Z_mod_mult. }
    assert (Halq8 : (uint sp0 - 120) mod 8 = 0)
      by (replace (uint sp0 - 120) with (uint sp0 + 8 * (-15)) by lia;
          apply Hspmod8).
    assert (Haleq8 : (uint sp0 - 128) mod 8 = 0)
      by (replace (uint sp0 - 128) with (uint sp0 + 8 * (-16)) by lia;
          apply Hspmod8).
    assert (Hcmd16q : cmd = 16 * (cmd / 16))
      by (pose proof (Z.div_mod cmd 16 ltac:(lia)); lia).
    assert (Hmod8 : forall z : Z, (cmd + 8 * z) mod 8 = 0).
    { intro z.
      assert (Hz : cmd + 8 * z = 8 * (2 * (cmd / 16) + z)) by lia.
      rewrite Hz Z.mul_comm. apply Z_mod_mult. }
    (* the leading whitespace run this iteration skips *)
    assert (Hkwle : (sh_skipws (drop offi bs) <= length bs - offi)%nat).
    { pose proof (sh_skipws_le (drop offi bs)) as H. rewrite length_drop in H. lia. }
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x622  c.mv ---- *)
    assert (Hw1 : (mword_of_int 4888 : mword 64)
                  = add_vec zero_reg (mE !!! Regidx s6_idx))
      by (rewrite Hs6E moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mi mE (mword_of_int 0x622)
              a2_idx s6_idx (mword_of_int 4888 : mword 64)
              (ui_sh_622 pt Mi Hltext (sh_img_text Mi Hgi))
              ltac:(vm_compute; discriminate) Hw1 with "Hcg Hpc").
    iIntros (CIDL1) "Hcg Hpc".
    set (n1 := <[Regidx a2_idx := regval_into_reg (mword_of_int 4888 : mword 64)]> mE).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x622 : mword 64) 2
                      = mword_of_int 0x624)) in "Hpc".
    assert (Hq1 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              n1 !!! Regidx r = mE !!! Regidx r)
      by (intros r Hr; exact (upd_ne mE (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_1 : n1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq1 csp_rs1 ltac:(vm_compute; discriminate)); exact HspE).
    assert (Hv_s0_idx_1 : n1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq1 s0_idx ltac:(vm_compute; discriminate)); exact Hs0E).
    assert (Hv_s1_idx_1 : n1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1E).
    assert (Hv_s2_idx_1 : n1 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq1 s2_idx ltac:(vm_compute; discriminate)); exact Hs2E).
    assert (Hv_s3_idx_1 : n1 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq1 s3_idx ltac:(vm_compute; discriminate)); exact Hs3E).
    assert (Hv_s4_idx_1 : n1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq1 s4_idx ltac:(vm_compute; discriminate)); exact Hs4E).
    assert (Hv_s5_idx_1 : n1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq1 s5_idx ltac:(vm_compute; discriminate)); exact Hs5E).
    assert (Hv_s6_idx_1 : n1 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq1 s6_idx ltac:(vm_compute; discriminate)); exact Hs6E).
    assert (Hv_s7_idx_1 : n1 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq1 s7_idx ltac:(vm_compute; discriminate)); exact Hs7E).
    assert (Hv_s8_idx_1 : n1 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq1 s8_idx ltac:(vm_compute; discriminate)); exact Hs8E).
    assert (Hv_s9_idx_1 : n1 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq1 s9_idx ltac:(vm_compute; discriminate)); exact Hs9E).
    assert (Hv_s10_idx_1 : n1 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq1 s10_idx ltac:(vm_compute; discriminate)); exact Hs10E).
    assert (Hv_s11_idx_1 : n1 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq1 s11_idx ltac:(vm_compute; discriminate)); exact Hs11E).
    assert (Hv_a2_idx_1 : n1 !!! Regidx a2_idx = (mword_of_int 4888 : mword 64))
      by exact (upd_eq mE (Regidx a2_idx) _).

    (* ---- 0x624  c.mv ---- *)
    assert (Hw2 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (n1 !!! Regidx s5_idx))
      by (rewrite Hv_s5_idx_1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mi n1 (mword_of_int 0x624)
              a1_idx s5_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_624 pt Mi Hltext (sh_img_text Mi Hgi))
              ltac:(vm_compute; discriminate) Hw2 with "Hcg Hpc").
    iIntros (CIDL2) "Hcg Hpc".
    set (n2 := <[Regidx a1_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> n1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x624 : mword 64) 2
                      = mword_of_int 0x626)) in "Hpc".
    assert (Hq2 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              n2 !!! Regidx r = n1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n1 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_2 : n2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_1).
    assert (Hv_s0_idx_2 : n2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq2 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_1).
    assert (Hv_s1_idx_2 : n2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq2 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_1).
    assert (Hv_s2_idx_2 : n2 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq2 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_1).
    assert (Hv_s3_idx_2 : n2 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq2 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_1).
    assert (Hv_s4_idx_2 : n2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq2 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_1).
    assert (Hv_s5_idx_2 : n2 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq2 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_1).
    assert (Hv_s6_idx_2 : n2 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq2 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_1).
    assert (Hv_s7_idx_2 : n2 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq2 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_1).
    assert (Hv_s8_idx_2 : n2 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq2 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_1).
    assert (Hv_s9_idx_2 : n2 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq2 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_1).
    assert (Hv_s10_idx_2 : n2 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq2 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_1).
    assert (Hv_s11_idx_2 : n2 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq2 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_1).
    assert (Hv_a1_idx_2 : n2 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq n1 (Regidx a1_idx) _).
    assert (Hv_a2_idx_2 : n2 !!! Regidx a2_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq2 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_1).

    (* ---- 0x626  c.mv ---- *)
    assert (Hw3 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (n2 !!! Regidx s4_idx))
      by (rewrite Hv_s4_idx_2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mi n2 (mword_of_int 0x626)
              a0_idx s4_idx (mword_of_int psaddr : mword 64)
              (ui_sh_626 pt Mi Hltext (sh_img_text Mi Hgi))
              ltac:(vm_compute; discriminate) Hw3 with "Hcg Hpc").
    iIntros (CIDL3) "Hcg Hpc".
    set (n3 := <[Regidx a0_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> n2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x626 : mword 64) 2
                      = mword_of_int 0x628)) in "Hpc".
    assert (Hq3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              n3 !!! Regidx r = n2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n2 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_3 : n3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_2).
    assert (Hv_s0_idx_3 : n3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq3 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_2).
    assert (Hv_s1_idx_3 : n3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq3 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_2).
    assert (Hv_s2_idx_3 : n3 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq3 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_2).
    assert (Hv_s3_idx_3 : n3 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq3 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_2).
    assert (Hv_s4_idx_3 : n3 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq3 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_2).
    assert (Hv_s5_idx_3 : n3 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq3 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_2).
    assert (Hv_s6_idx_3 : n3 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq3 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_2).
    assert (Hv_s7_idx_3 : n3 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq3 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_2).
    assert (Hv_s8_idx_3 : n3 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq3 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_2).
    assert (Hv_s9_idx_3 : n3 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq3 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_2).
    assert (Hv_s10_idx_3 : n3 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq3 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_2).
    assert (Hv_s11_idx_3 : n3 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq3 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_2).
    assert (Hv_a0_idx_3 : n3 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq n2 (Regidx a0_idx) _).
    assert (Hv_a1_idx_3 : n3 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq3 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_2).
    assert (Hv_a2_idx_3 : n3 !!! Regidx a2_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq3 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_2).

    (* ---- 0x628  jal ra, 0x448 ---- *)
    assert (Ht4 : (mword_of_int 0x448 : mword 64)
                   = add_vec (mword_of_int 0x628)
                       (sign_extend' 64 (mword_of_int 2096672 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl4 : (mword_of_int 0x62c : mword 64)
                   = add_vec_int (mword_of_int 0x628 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh Mi n3 (mword_of_int 0x628)
              (mword_of_int 2096672 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x62c)
              (ui_sh_628 pt Mi Hltext (sh_img_text Mi Hgi))
              ltac:(vm_compute; discriminate) Ht4 Hl4
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDL4) "Hcg Hpc".
    set (n4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x62c : mword 64)]> n3).
    assert (Hq4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              n4 !!! Regidx r = n3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n3 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_4 : n4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq4 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_3).
    assert (Hv_s0_idx_4 : n4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq4 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_3).
    assert (Hv_s1_idx_4 : n4 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq4 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_3).
    assert (Hv_s2_idx_4 : n4 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq4 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_3).
    assert (Hv_s3_idx_4 : n4 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq4 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_3).
    assert (Hv_s4_idx_4 : n4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_3).
    assert (Hv_s5_idx_4 : n4 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq4 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_3).
    assert (Hv_s6_idx_4 : n4 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq4 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_3).
    assert (Hv_s7_idx_4 : n4 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq4 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_3).
    assert (Hv_s8_idx_4 : n4 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq4 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_3).
    assert (Hv_s9_idx_4 : n4 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq4 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_3).
    assert (Hv_s10_idx_4 : n4 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq4 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_3).
    assert (Hv_s11_idx_4 : n4 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq4 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_3).
    assert (Hv_a0_idx_4 : n4 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_3).
    assert (Hv_a1_idx_4 : n4 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq4 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_3).
    assert (Hv_a2_idx_4 : n4 !!! Regidx a2_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq4 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_3).
    assert (Hv_ra_idx_4 : n4 !!! Regidx ra_idx = (mword_of_int 0x62c : mword 64))
      by exact (upd_eq n3 (Regidx ra_idx) _).
    (* ---- 0x448  peek(ps, es, "|)&;") -- 0, so the loop body runs ---- *)
    assert (HpreK : sh_parse_pre pt hbase hlen Mi sb bs
                      (mword_of_int (uint sp0 - 128) : mword 64) 80).
    { apply (parse_pre_move Mi Mi sb bs sp0 (mword_of_int (uint sp0 - 128))
               320 80).
      - intros k H; exact H.
      - intros k _; reflexivity.
      - intros k _; reflexivity.
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hprei. }
    assert (HcellK : sh_ptr_cell pt Mi psaddr (sb + Z.of_nat offi)
                       (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (mk_ptr_cell Mi psaddr (sb + Z.of_nat offi)
                  (mword_of_int (uint sp0 - 128))
                  Hcell Hrdpsi Hwrpsi Hpsal ltac:(rewrite Huspk; lia)
                  ltac:(change (2 ^ 38) with 274877906944; lia)).
    assert (Htbhi1 : 4888 + Z.of_nat (length sh_tb_end) + 1 <= 8192)
      by (rewrite sh_tb_end_len; lia).
    assert (Htbfr1 : 4888 + Z.of_nat (length sh_tb_end) + 1
                     <= uint (mword_of_int (uint sp0 - 128) : mword 64) - 80)
      by (rewrite Huspk sh_tb_end_len; lia).
    assert (Hret2a : is_aligned_vaddr (Virtaddr (n4 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_4; vm_compute; reflexivity).
    iApply (wp_sh_peek_zero CIDL4 Mi n4 (mword_of_int (uint sp0 - 128))
              psaddr sb 4888 bs offi sh_tb_end
              HpreK Hv_csp_rs1_4 Hstk80 Hv_a0_idx_4 Hv_a1_idx_4 Hv_a2_idx_4
              HcellK Hoff ltac:(lia) Htbhi1 Htbfr1
              sh_tb_end_data sh_tb_end_sym Hret2a with "Hcg Hpc [Hcont]").
    iIntros (CIDL5 p1 Mp) "%Hcs1 %Ha0p %Hcellp %Honly1 Hcg Hpc".
    iEval (rewrite Hv_ra_idx_4) in "Hpc".
    assert (Hv_csp_rs1_5 : p1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_4).
    assert (Hv_s0_idx_5 : p1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcs1 s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_4).
    assert (Hv_s1_idx_5 : p1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcs1 s1_idx ltac:(vm_compute; reflexivity)); exact Hv_s1_idx_4).
    assert (Hv_s2_idx_5 : p1 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hcs1 s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_4).
    assert (Hv_s3_idx_5 : p1 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hcs1 s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_4).
    assert (Hv_s4_idx_5 : p1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcs1 s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_4).
    assert (Hv_s5_idx_5 : p1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcs1 s5_idx ltac:(vm_compute; reflexivity)); exact Hv_s5_idx_4).
    assert (Hv_s6_idx_5 : p1 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hcs1 s6_idx ltac:(vm_compute; reflexivity)); exact Hv_s6_idx_4).
    assert (Hv_s7_idx_5 : p1 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hcs1 s7_idx ltac:(vm_compute; reflexivity)); exact Hv_s7_idx_4).
    assert (Hv_s8_idx_5 : p1 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hcs1 s8_idx ltac:(vm_compute; reflexivity)); exact Hv_s8_idx_4).
    assert (Hv_s9_idx_5 : p1 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hcs1 s9_idx ltac:(vm_compute; reflexivity)); exact Hv_s9_idx_4).
    assert (Hv_s10_idx_5 : p1 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hcs1 s10_idx ltac:(vm_compute; reflexivity)); exact Hv_s10_idx_4).
    assert (Hv_s11_idx_5 : p1 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcs1 s11_idx ltac:(vm_compute; reflexivity)); exact Hv_s11_idx_4).
    rewrite Huspk in Honly1.
    assert (HWp : uM_only_in Mi0 Mp
                    [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)]).
    { apply (uM_only_in_trans Mi0 Mi Mp); [ exact HW | ].
      apply (win3_in Mi Mp hbase 65536 psaddr 8 (uint sp0 - 320) 208).
      - exact (proj1 Honly1).
      - intros k H1 H2 H3.
        exact (win2_out Mi Mp psaddr 8 (uint sp0 - 128 - 80) 80 k Honly1
                 H2 ltac:(lia)). }
    assert (Hprep : sh_parse_pre pt hbase hlen Mp sb bs sp0 320)
      by exact (pe_w3_pre Mi0 Mp sb psaddr bs sp0 HWp Hbc Hpslo Hpre0).
    pose proof Hprep as (_ & Hgp & _ & _ & _ & _ & _ & _).
    assert (Hstkp : uv_stack pt Mp sp0 320)
      by exact (stk_dom Mi0 Mp sp0 320 (proj1 HWp) Hstk0).
    assert (Hstkp80 : uv_stack pt Mp (mword_of_int (uint sp0 - 128)) 80)
      by exact (stk_dom Mi Mp _ 80 (proj1 Honly1) Hstk80).
    assert (Hrdpsp : uv_rd pt Mp psaddr 8)
      by exact (uv_rd_dom pt Mi0 Mp psaddr 8 (proj1 HWp) Hrdps0).
    assert (Hwrpsp : uv_wr pt Mp psaddr 8)
      by exact (uv_wr_dom pt Mi0 Mp psaddr 8 (proj1 HWp) Hwrps0).
    assert (Hwrndp : uv_wr pt Mp cmd 168)
      by exact (uv_wr_dom pt Mi0 Mp cmd 168 (proj1 HWp) Hwrnd0).
    (* the node is untouched by [peek] *)
    assert (Hnodep : forall k : Z, cmd <= k < cmd + 168 -> Mp !! k = Mi !! k)
      by (intros k Hk;
          exact (win2_out Mi Mp psaddr 8 (uint sp0 - 128 - 80) 80 k Honly1
                   ltac:(lia) ltac:(lia))).
    assert (Htypep : uM_bytes Mp cmd 4 (mword_of_int 1 : mword 32))
      by (intros j Hj; rewrite (Hnodep (cmd + Z.of_nat j) ltac:(lia));
          exact (Htype j Hj)).
    assert (Hargp : forall (j : nat) (t : nat * nat), take i toks !! j = Some t ->
              uM_bytes Mp (cmd + 8 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (fst t)) : mword 64) /\
              uM_bytes Mp (cmd + 88 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (snd t)) : mword 64)).
    { intros j t Hj.
      assert (Hjl : (j < i)%nat)
        by (pose proof (lookup_lt_Some _ j t Hj) as Hx;
            rewrite length_take in Hx; lia).
      destruct (Harg j t Hj) as (Hb1 & Hb2). split.
      - intros u Hu.
        rewrite (Hnodep (cmd + 8 + 8 * Z.of_nat j + Z.of_nat u) ltac:(lia)).
        exact (Hb1 u Hu).
      - intros u Hu.
        rewrite (Hnodep (cmd + 88 + 8 * Z.of_nat j + Z.of_nat u) ltac:(lia)).
        exact (Hb2 u Hu). }
    (* ---- 0x62c  c.bnez a0,0x662 -- NOT taken ([peek] returned 0) ---- *)
    assert (Htkp : false = neq_vec (p1 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0p. unfold neq_vec.
      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    assert (Htgtp : (mword_of_int 0x662 : mword 64)
                    = add_vec (mword_of_int 0x62c)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 27 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cbnez C pt Psh Mp p1 (mword_of_int 0x62c)
              (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x662)
              (ui_sh_62c pt Mp Hltext (sh_img_text Mp Hgp))
              ltac:(vm_compute; reflexivity) Htkp Htgtp
              ltac:(intro Hx; discriminate) with "Hcg Hpc").
    iIntros (CIDbz) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x62c : mword 64) 2
                      = mword_of_int 0x62e)) in "Hpc".
    (* ---- 0x62e  c.mv ---- *)
    assert (Hw6 : (mword_of_int (uint sp0 - 128) : mword 64)
                  = add_vec zero_reg (p1 !!! Regidx s8_idx))
      by (rewrite Hv_s8_idx_5 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mp p1 (mword_of_int 0x62e)
              a3_idx s8_idx (mword_of_int (uint sp0 - 128) : mword 64)
              (ui_sh_62e pt Mp Hltext (sh_img_text Mp Hgp))
              ltac:(vm_compute; discriminate) Hw6 with "Hcg Hpc").
    iIntros (CIDL6) "Hcg Hpc".
    set (q1 := <[Regidx a3_idx := regval_into_reg (mword_of_int (uint sp0 - 128) : mword 64)]> p1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x62e : mword 64) 2
                      = mword_of_int 0x630)) in "Hpc".
    assert (Hq6 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
              q1 !!! Regidx r = p1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p1 (Regidx a3_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_6 : q1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq6 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_5).
    assert (Hv_s0_idx_6 : q1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq6 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_5).
    assert (Hv_s1_idx_6 : q1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq6 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_5).
    assert (Hv_s2_idx_6 : q1 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq6 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_5).
    assert (Hv_s3_idx_6 : q1 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq6 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_5).
    assert (Hv_s4_idx_6 : q1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq6 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_5).
    assert (Hv_s5_idx_6 : q1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq6 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_5).
    assert (Hv_s6_idx_6 : q1 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq6 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_5).
    assert (Hv_s7_idx_6 : q1 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq6 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_5).
    assert (Hv_s8_idx_6 : q1 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq6 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_5).
    assert (Hv_s9_idx_6 : q1 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq6 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_5).
    assert (Hv_s10_idx_6 : q1 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq6 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_5).
    assert (Hv_s11_idx_6 : q1 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq6 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_5).
    assert (Hv_a3_idx_6 : q1 !!! Regidx a3_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (upd_eq p1 (Regidx a3_idx) _).

    (* ---- 0x630  c.mv ---- *)
    assert (Hw7 : (mword_of_int (uint sp0 - 120) : mword 64)
                  = add_vec zero_reg (q1 !!! Regidx s7_idx))
      by (rewrite Hv_s7_idx_6 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mp q1 (mword_of_int 0x630)
              a2_idx s7_idx (mword_of_int (uint sp0 - 120) : mword 64)
              (ui_sh_630 pt Mp Hltext (sh_img_text Mp Hgp))
              ltac:(vm_compute; discriminate) Hw7 with "Hcg Hpc").
    iIntros (CIDL7) "Hcg Hpc".
    set (q2 := <[Regidx a2_idx := regval_into_reg (mword_of_int (uint sp0 - 120) : mword 64)]> q1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x630 : mword 64) 2
                      = mword_of_int 0x632)) in "Hpc".
    assert (Hq7 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              q2 !!! Regidx r = q1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q1 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_7 : q2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq7 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_6).
    assert (Hv_s0_idx_7 : q2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq7 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_6).
    assert (Hv_s1_idx_7 : q2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq7 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_6).
    assert (Hv_s2_idx_7 : q2 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq7 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_6).
    assert (Hv_s3_idx_7 : q2 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq7 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_6).
    assert (Hv_s4_idx_7 : q2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq7 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_6).
    assert (Hv_s5_idx_7 : q2 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq7 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_6).
    assert (Hv_s6_idx_7 : q2 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq7 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_6).
    assert (Hv_s7_idx_7 : q2 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq7 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_6).
    assert (Hv_s8_idx_7 : q2 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq7 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_6).
    assert (Hv_s9_idx_7 : q2 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq7 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_6).
    assert (Hv_s10_idx_7 : q2 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq7 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_6).
    assert (Hv_s11_idx_7 : q2 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq7 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_6).
    assert (Hv_a2_idx_7 : q2 !!! Regidx a2_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by exact (upd_eq q1 (Regidx a2_idx) _).
    assert (Hv_a3_idx_7 : q2 !!! Regidx a3_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq7 a3_idx ltac:(vm_compute; discriminate)); exact Hv_a3_idx_6).

    (* ---- 0x632  c.mv ---- *)
    assert (Hw8 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (q2 !!! Regidx s5_idx))
      by (rewrite Hv_s5_idx_7 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mp q2 (mword_of_int 0x632)
              a1_idx s5_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_632 pt Mp Hltext (sh_img_text Mp Hgp))
              ltac:(vm_compute; discriminate) Hw8 with "Hcg Hpc").
    iIntros (CIDL8) "Hcg Hpc".
    set (q3 := <[Regidx a1_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> q2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x632 : mword 64) 2
                      = mword_of_int 0x634)) in "Hpc".
    assert (Hq8 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              q3 !!! Regidx r = q2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q2 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_8 : q3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq8 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_7).
    assert (Hv_s0_idx_8 : q3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq8 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_7).
    assert (Hv_s1_idx_8 : q3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq8 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_7).
    assert (Hv_s2_idx_8 : q3 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq8 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_7).
    assert (Hv_s3_idx_8 : q3 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq8 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_7).
    assert (Hv_s4_idx_8 : q3 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq8 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_7).
    assert (Hv_s5_idx_8 : q3 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq8 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_7).
    assert (Hv_s6_idx_8 : q3 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq8 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_7).
    assert (Hv_s7_idx_8 : q3 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq8 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_7).
    assert (Hv_s8_idx_8 : q3 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq8 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_7).
    assert (Hv_s9_idx_8 : q3 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq8 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_7).
    assert (Hv_s10_idx_8 : q3 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq8 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_7).
    assert (Hv_s11_idx_8 : q3 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq8 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_7).
    assert (Hv_a1_idx_8 : q3 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq q2 (Regidx a1_idx) _).
    assert (Hv_a2_idx_8 : q3 !!! Regidx a2_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq8 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_7).
    assert (Hv_a3_idx_8 : q3 !!! Regidx a3_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq8 a3_idx ltac:(vm_compute; discriminate)); exact Hv_a3_idx_7).

    (* ---- 0x634  c.mv ---- *)
    assert (Hw9 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (q3 !!! Regidx s4_idx))
      by (rewrite Hv_s4_idx_8 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mp q3 (mword_of_int 0x634)
              a0_idx s4_idx (mword_of_int psaddr : mword 64)
              (ui_sh_634 pt Mp Hltext (sh_img_text Mp Hgp))
              ltac:(vm_compute; discriminate) Hw9 with "Hcg Hpc").
    iIntros (CIDL9) "Hcg Hpc".
    set (q4 := <[Regidx a0_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> q3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x634 : mword 64) 2
                      = mword_of_int 0x636)) in "Hpc".
    assert (Hq9 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              q4 !!! Regidx r = q3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q3 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_9 : q4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq9 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_8).
    assert (Hv_s0_idx_9 : q4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq9 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_8).
    assert (Hv_s1_idx_9 : q4 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq9 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_8).
    assert (Hv_s2_idx_9 : q4 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq9 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_8).
    assert (Hv_s3_idx_9 : q4 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq9 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_8).
    assert (Hv_s4_idx_9 : q4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq9 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_8).
    assert (Hv_s5_idx_9 : q4 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq9 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_8).
    assert (Hv_s6_idx_9 : q4 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq9 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_8).
    assert (Hv_s7_idx_9 : q4 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq9 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_8).
    assert (Hv_s8_idx_9 : q4 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq9 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_8).
    assert (Hv_s9_idx_9 : q4 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq9 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_8).
    assert (Hv_s10_idx_9 : q4 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq9 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_8).
    assert (Hv_s11_idx_9 : q4 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq9 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_8).
    assert (Hv_a0_idx_9 : q4 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq q3 (Regidx a0_idx) _).
    assert (Hv_a1_idx_9 : q4 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq9 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_8).
    assert (Hv_a2_idx_9 : q4 !!! Regidx a2_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq9 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_8).
    assert (Hv_a3_idx_9 : q4 !!! Regidx a3_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq9 a3_idx ltac:(vm_compute; discriminate)); exact Hv_a3_idx_8).

    (* ---- 0x636  jal ra, 0x310 ---- *)
    assert (Ht10 : (mword_of_int 0x310 : mword 64)
                   = add_vec (mword_of_int 0x636)
                       (sign_extend' 64 (mword_of_int 2096346 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl10 : (mword_of_int 0x63a : mword 64)
                   = add_vec_int (mword_of_int 0x636 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh Mp q4 (mword_of_int 0x636)
              (mword_of_int 2096346 : mword 21) ra_idx
              (mword_of_int 0x310) (mword_of_int 0x63a)
              (ui_sh_636 pt Mp Hltext (sh_img_text Mp Hgp))
              ltac:(vm_compute; discriminate) Ht10 Hl10
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDL10) "Hcg Hpc".
    set (q5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x63a : mword 64)]> q4).
    assert (Hq10 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              q5 !!! Regidx r = q4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q4 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_10 : q5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq10 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_9).
    assert (Hv_s0_idx_10 : q5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq10 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_9).
    assert (Hv_s1_idx_10 : q5 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq10 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_9).
    assert (Hv_s2_idx_10 : q5 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq10 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_9).
    assert (Hv_s3_idx_10 : q5 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq10 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_9).
    assert (Hv_s4_idx_10 : q5 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq10 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_9).
    assert (Hv_s5_idx_10 : q5 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq10 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_9).
    assert (Hv_s6_idx_10 : q5 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq10 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_9).
    assert (Hv_s7_idx_10 : q5 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq10 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_9).
    assert (Hv_s8_idx_10 : q5 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq10 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_9).
    assert (Hv_s9_idx_10 : q5 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq10 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_9).
    assert (Hv_s10_idx_10 : q5 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq10 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_9).
    assert (Hv_s11_idx_10 : q5 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq10 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_9).
    assert (Hv_a0_idx_10 : q5 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq10 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_9).
    assert (Hv_a1_idx_10 : q5 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq10 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_9).
    assert (Hv_a2_idx_10 : q5 !!! Regidx a2_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq10 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_9).
    assert (Hv_a3_idx_10 : q5 !!! Regidx a3_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq10 a3_idx ltac:(vm_compute; discriminate)); exact Hv_a3_idx_9).
    assert (Hv_ra_idx_10 : q5 !!! Regidx ra_idx = (mword_of_int 0x63a : mword 64))
      by exact (upd_eq q4 (Regidx ra_idx) _).
    (* ---- 0x310  gettoken(ps, es, &q, &eq) ---- *)
    assert (Hk0 : sh_skipws (drop (offi + sh_skipws (drop offi bs))%nat bs)
                  = 0%nat)
      by exact (sh_skipws_drop_idem bs offi).
    assert (HpreG : sh_parse_pre pt hbase hlen Mp sb bs
                      (mword_of_int (uint sp0 - 128) : mword 64) 80).
    { apply (parse_pre_move Mp Mp sb bs sp0 (mword_of_int (uint sp0 - 128))
               320 80).
      - intros k H; exact H.
      - intros k _; reflexivity.
      - intros k _; reflexivity.
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hprep. }
    assert (HcellG : sh_ptr_cell pt Mp psaddr
                       (sb + Z.of_nat (offi + sh_skipws (drop offi bs)))
                       (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (mk_ptr_cell Mp psaddr
                  (sb + Z.of_nat (offi + sh_skipws (drop offi bs)))
                  (mword_of_int (uint sp0 - 128))
                  Hcellp Hrdpsp Hwrpsp Hpsal ltac:(rewrite Huspk; lia)
                  ltac:(change (2 ^ 38) with 274877906944; lia)).
    assert (Hqw : uv_wr pt Mp (uint sp0 - 120) 8)
      by exact (stk_wr8 Mp sp0 320 (uint sp0 - 120) Hstkp ltac:(lia) ltac:(lia)).
    assert (Heqw : uv_wr pt Mp (uint sp0 - 128) 8)
      by exact (stk_wr8 Mp sp0 320 (uint sp0 - 128) Hstkp ltac:(lia) ltac:(lia)).
    assert (Hqlo : uint (mword_of_int (uint sp0 - 128) : mword 64)
                   <= uint sp0 - 120) by (rewrite Huspk; lia).
    assert (Hqhi : uint sp0 - 120 + 8 <= 2 ^ 38)
      by (change (2 ^ 38) with 274877906944; lia).
    assert (Heqlo : uint (mword_of_int (uint sp0 - 128) : mword 64)
                    <= uint sp0 - 128) by (rewrite Huspk; lia).
    assert (Heqhi : uint sp0 - 128 + 8 <= 2 ^ 38)
      by (change (2 ^ 38) with 274877906944; lia).
    assert (Hret2b : is_aligned_vaddr (Virtaddr (q5 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_10; vm_compute; reflexivity).
    iApply (wp_sh_gettoken C pt gin gbrk hbase hlen Q CIDL10 Mp q5
              (mword_of_int (uint sp0 - 128)) psaddr (uint sp0 - 120)
              (uint sp0 - 128) sb bs (offi + sh_skipws (drop offi bs))%nat
              HpreG Hv_csp_rs1_10 Hstkp80 Hv_a0_idx_10 Hv_a1_idx_10
              Hv_a2_idx_10 Hv_a3_idx_10 HcellG
              (or_intror (conj Hqw (conj Halq8
                                     (conj Hqlo Hqhi))))
              (or_intror (conj Heqw (conj Haleq8
                                      (conj Heqlo Heqhi))))
              ltac:(right; left; lia) ltac:(right; left; lia)
              ltac:(right; right; right; lia)
              ltac:(lia) Hret2b with "Hcg Hpc [Hcont]").
    iIntros (CIDL11 g1 Mg) "%Hcs2 %Ha0g %Hqv %Heqv %Hpsg %Honly2 Hcg Hpc".
    iEval (rewrite Hv_ra_idx_10) in "Hpc".
    assert (Hv_csp_rs1_11 : g1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_10).
    assert (Hv_s0_idx_11 : g1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcs2 s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_10).
    assert (Hv_s1_idx_11 : g1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcs2 s1_idx ltac:(vm_compute; reflexivity)); exact Hv_s1_idx_10).
    assert (Hv_s2_idx_11 : g1 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hcs2 s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_10).
    assert (Hv_s3_idx_11 : g1 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hcs2 s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_10).
    assert (Hv_s4_idx_11 : g1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcs2 s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_10).
    assert (Hv_s5_idx_11 : g1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcs2 s5_idx ltac:(vm_compute; reflexivity)); exact Hv_s5_idx_10).
    assert (Hv_s6_idx_11 : g1 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hcs2 s6_idx ltac:(vm_compute; reflexivity)); exact Hv_s6_idx_10).
    assert (Hv_s7_idx_11 : g1 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hcs2 s7_idx ltac:(vm_compute; reflexivity)); exact Hv_s7_idx_10).
    assert (Hv_s8_idx_11 : g1 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hcs2 s8_idx ltac:(vm_compute; reflexivity)); exact Hv_s8_idx_10).
    assert (Hv_s9_idx_11 : g1 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hcs2 s9_idx ltac:(vm_compute; reflexivity)); exact Hv_s9_idx_10).
    assert (Hv_s10_idx_11 : g1 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hcs2 s10_idx ltac:(vm_compute; reflexivity)); exact Hv_s10_idx_10).
    assert (Hv_s11_idx_11 : g1 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcs2 s11_idx ltac:(vm_compute; reflexivity)); exact Hv_s11_idx_10).
    cbv zeta in Ha0g, Hqv, Heqv, Hpsg.
    rewrite Hk0 in Ha0g Hqv Heqv Hpsg.
    rewrite !Nat.add_0_r in Ha0g Hqv Heqv Hpsg.
    assert (HWg : uM_only_in Mi0 Mg
                    [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)]).
    { apply (uM_only_in_trans Mi0 Mp Mg); [ exact HWp | ].
      apply (win3_in Mp Mg hbase 65536 psaddr 8 (uint sp0 - 320) 208).
      - exact (proj1 Honly2).
      - intros k H1 H2 H3.
        exact (win4_out Mp Mg psaddr 8 (uint sp0 - 120) 8 (uint sp0 - 128) 8
                 (uint (mword_of_int (uint sp0 - 128) : mword 64) - 80) 80 k
                 Honly2 H2 ltac:(lia) ltac:(lia) ltac:(rewrite Huspk; lia)). }
    assert (Hpreg : sh_parse_pre pt hbase hlen Mg sb bs sp0 320)
      by exact (pe_w3_pre Mi0 Mg sb psaddr bs sp0 HWg Hbc Hpslo Hpre0).
    pose proof Hpreg as (_ & Hgg & _ & _ & _ & _ & _ & _).
    assert (Hstkg : uv_stack pt Mg sp0 320)
      by exact (stk_dom Mi0 Mg sp0 320 (proj1 HWg) Hstk0).
    assert (Hwrndg : uv_wr pt Mg cmd 168)
      by exact (uv_wr_dom pt Mi0 Mg cmd 168 (proj1 HWg) Hwrnd0).
    assert (Hnodeg : forall k : Z, cmd <= k < cmd + 168 -> Mg !! k = Mp !! k).
    { intros k Hk.
      exact (win4_out Mp Mg psaddr 8 (uint sp0 - 120) 8 (uint sp0 - 128) 8
               (uint (mword_of_int (uint sp0 - 128) : mword 64) - 80) 80 k
               Honly2 ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(rewrite Huspk; lia)). }
    assert (Htypeg : uM_bytes Mg cmd 4 (mword_of_int 1 : mword 32))
      by (intros j Hj; rewrite (Hnodeg (cmd + Z.of_nat j) ltac:(lia));
          exact (Htypep j Hj)).
    assert (Hargg : forall (j : nat) (t : nat * nat), take i toks !! j = Some t ->
              uM_bytes Mg (cmd + 8 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (fst t)) : mword 64) /\
              uM_bytes Mg (cmd + 88 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (snd t)) : mword 64)).
    { intros j t Hj.
      assert (Hjl : (j < i)%nat)
        by (pose proof (lookup_lt_Some _ j t Hj) as Hx;
            rewrite length_take in Hx; lia).
      destruct (Hargp j t Hj) as (Hb1 & Hb2). split.
      - intros u Hu.
        rewrite (Hnodeg (cmd + 8 + 8 * Z.of_nat j + Z.of_nat u) ltac:(lia)).
        exact (Hb1 u Hu).
      - intros u Hu.
        rewrite (Hnodeg (cmd + 88 + 8 * Z.of_nat j + Z.of_nat u) ltac:(lia)).
        exact (Hb2 u Hu). }
    destruct toksR as [ | t rest ].
    - (* =============== no token left: [gettoken] returns 0 =============== *)
      assert (Hend : (offi + sh_skipws (drop offi bs))%nat = length bs)
        by exact (sh_tokens_nil_inv bs offi Htoks).
      rewrite (bool_decide_eq_true_2 _ Hend) in Ha0g.
      assert (Hilen : i = length toks).
      { assert (Hz : length (drop i toks) = 0%nat)
          by (rewrite <- HtR; reflexivity).
        rewrite length_drop in Hz. lia. }
      (* ---- 0x63a  c.beqz a0,0x662 -- TAKEN ---- *)
      assert (Htk0 : true = eq_vec (g1 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0g (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      assert (Htgt0 : (mword_of_int 0x662 : mword 64)
                      = add_vec (mword_of_int 0x63a)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 20 : mword 8) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cbeqz C pt Psh Mg g1 (mword_of_int 0x63a)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x662)
                (ui_sh_63a pt Mg Hltext (sh_img_text Mg Hgg))
                ltac:(vm_compute; reflexivity) Htk0 Htgt0
                ltac:(intros _; vm_compute; reflexivity) with "Hcg Hpc").
      iIntros (CIDx) "Hcg Hpc".
      assert (Htn0 : sh_toklen (drop (offi + sh_skipws (drop offi bs))%nat bs)
                     = 0%nat)
        by (rewrite Hend drop_all; exact sh_toklen_nil).
      rewrite Htn0 in Hpsg. rewrite !Nat.add_0_r in Hpsg.
      rewrite Hk0 in Hpsg. rewrite !Nat.add_0_r in Hpsg.
      rewrite Hend in Hpsg.
      iApply ("Hcont" $! CIDx g1 Mg with "[] [] [] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact HWg.
      + iPureIntro. exact Htypeg.
      + iPureIntro. intros j t Hj. apply Hargg.
        rewrite Hilen (take_ge toks (length toks) ltac:(lia)). exact Hj.
      + iPureIntro. exact Hpsg.
      + iPureIntro. exact Hv_s1_idx_11.
      + iPureIntro. rewrite <- Hilen. exact Hv_s2_idx_11.
      + iPureIntro. intros r Hr N1 N2 N3.
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na1 : Regidx r <> Regidx a1_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na2 : Regidx r <> Regidx a2_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na3 : Regidx r <> Regidx a3_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (Hcs2 r Hr) (Hq10 r Nra) (Hq9 r Na0) (Hq8 r Na1) (Hq7 r Na2)
                (Hq6 r Na3) (Hcs1 r Hr) (Hq4 r Nra) (Hq3 r Na0) (Hq2 r Na1)
                (Hq1 r Na2).
        reflexivity.
    - (* =============== a token follows =============== *)
      destruct (sh_tokens_cons_inv bs offi t rest Htoks) as (Htn & Hteq & Hrest).
      assert (Hlt : (offi + sh_skipws (drop offi bs) < length bs)%nat)
        by exact (sh_toklen_pos_lt bs _ Htn).
      assert (Hnend : (offi + sh_skipws (drop offi bs))%nat <> length bs) by lia.
      rewrite (bool_decide_eq_false_2 _ Hnend) in Ha0g.
      destruct t as (ta, tb). injection Hteq as Hta Htb.
      rewrite <- Hta in Htb, Htn, Hrest, Hqv, Heqv, Hpsg, Hlt.
      rewrite <- Htb in Hrest, Heqv, Hpsg.
      assert (Hti : toks !! i = Some (ta, tb)).
      { pose proof (lookup_drop toks i 0) as Hd. rewrite Nat.add_0_r in Hd.
        rewrite <- Hd, <- HtR. reflexivity. }
      assert (Hdropi : drop (S i) toks = rest).
      { replace (S i) with (i + 1)%nat by lia.
        rewrite <- drop_drop, <- HtR. reflexivity. }
      assert (Hilt : (i < length toks)%nat)
        by exact (lookup_lt_Some toks i (ta, tb) Hti).
      assert (Htblen : (tb <= length bs)%nat).
      { rewrite Htb.
        pose proof (sh_toklen_le (drop ta bs)) as Hx.
        rewrite length_drop in Hx. lia. }
      assert (Htalt : (ta < tb)%nat) by (rewrite Htb; lia).
      (* ---- 0x63a  c.beqz a0,0x662 -- NOT taken ---- *)
      assert (Htk0 : false = eq_vec (g1 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0g (moi_eq_zero 97 ltac:(unfold Z64; lia)). reflexivity. }
      assert (Htgt0 : (mword_of_int 0x662 : mword 64)
                      = add_vec (mword_of_int 0x63a)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 20 : mword 8) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cbeqz C pt Psh Mg g1 (mword_of_int 0x63a)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x662)
                (ui_sh_63a pt Mg Hltext (sh_img_text Mg Hgg))
                ltac:(vm_compute; reflexivity) Htk0 Htgt0
                ltac:(intro Hx; discriminate) with "Hcg Hpc").
      iIntros (CIDc1) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x63a : mword 64) 2
                        = mword_of_int 0x63c)) in "Hpc".
      (* ---- 0x63c  bne a0,s10,0x608 -- NOT taken ---- *)
      assert (Htkb : false
                     = uv_btaken BNE (g1 !!! Regidx a0_idx) (g1 !!! Regidx s10_idx)).
      { cbn [uv_btaken]. rewrite Ha0g Hv_s10_idx_11.
        rewrite (moi_neq_vec 97 97 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        reflexivity. }
      assert (Htgtb : (mword_of_int 0x608 : mword 64)
                      = add_vec (mword_of_int 0x63c)
                          (sign_extend' 64 (mword_of_int 8140 : mword 13)))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_btype C pt Psh Mg g1 (mword_of_int 0x63c)
                (mword_of_int 8140 : mword 13) s10_idx a0_idx BNE
                false (mword_of_int 0x608)
                (ui_sh_63c pt Mg Hltext (sh_img_text Mg Hgg))
                Htkb Htgtb ltac:(intro Hx; discriminate) with "Hcg Hpc").
      iIntros (CIDc2) "Hcg Hpc".
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x63c : mword 64) 4
                        = mword_of_int 0x640)) in "Hpc".
      (* ---- 0x640  ld a5,-120(s0)  -- a5 := q ---- *)
      assert (Hva1 : (mword_of_int (uint sp0 - 120) : mword 64)
                     = add_vec (g1 !!! Regidx s0_idx)
                         (sign_extend' 64 (mword_of_int 3976 : mword 12))).
      { rewrite Hv_s0_idx_11.
        assert (Hc : (sign_extend' 64 (mword_of_int 3976 : mword 12) : mword 64)
                     = mword_of_int (-120))
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal; lia. }
      destruct (uv_slot8_facts (uint sp0 - 120)
                  (mword_of_int (uint sp0 - 120)) ltac:(lia) Halq8
                  ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
        as (Hu1 & Hcn1 & Hpg1 & Hal1).
      destruct (stk_leaf8 Mg sp0 320 (uint sp0 - 120) Hstkg ltac:(lia) ltac:(lia))
        as (wq & Hwq & _ & Hwql).
      iApply (wp_uv_ld C pt Psh Mg g1 (mword_of_int 0x640)
                (mword_of_int 3976 : mword 12) s0_idx a5_idx
                wq (mword_of_int (uint sp0 - 120))
                (mword_of_int (sb + Z.of_nat ta))
                (ui_sh_640 pt Mg Hltext (sh_img_text Mg Hgg))
                ltac:(vm_compute; discriminate) Hva1 Hwq Hwql Hcn1 Hpg1 Hal1
                ltac:(rewrite Hu1;
                      exact (stk_bytes8 Mg sp0 320 (uint sp0 - 120) Hstkg
                               ltac:(lia) ltac:(lia)))
                ltac:(rewrite Hu1; symmetry;
                      exact (word_of_bytes8 Mg (uint sp0 - 120)
                               (mword_of_int (sb + Z.of_nat ta))
                               (Hqv ltac:(lia))))
                with "Hcg Hpc").
      iIntros (CIDc3) "Hcg Hpc".
      set (g2 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (sb + Z.of_nat ta) : mword 64)]> g1).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x640 : mword 64) 4
                        = mword_of_int 0x644)) in "Hpc".
    assert (Hq12 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              g2 !!! Regidx r = g1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g1 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_12 : g2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq12 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_11).
    assert (Hv_s0_idx_12 : g2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq12 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_11).
    assert (Hv_s1_idx_12 : g2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq12 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_11).
    assert (Hv_s2_idx_12 : g2 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq12 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_11).
    assert (Hv_s3_idx_12 : g2 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq12 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_11).
    assert (Hv_s4_idx_12 : g2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq12 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_11).
    assert (Hv_s5_idx_12 : g2 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq12 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_11).
    assert (Hv_s6_idx_12 : g2 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq12 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_11).
    assert (Hv_s7_idx_12 : g2 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq12 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_11).
    assert (Hv_s8_idx_12 : g2 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq12 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_11).
    assert (Hv_s9_idx_12 : g2 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq12 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_11).
    assert (Hv_s10_idx_12 : g2 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq12 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_11).
    assert (Hv_s11_idx_12 : g2 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq12 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_11).
    assert (Hv_a5_idx_12 : g2 !!! Regidx a5_idx = (mword_of_int (sb + Z.of_nat ta) : mword 64))
      by exact (upd_eq g1 (Regidx a5_idx) _).

      (* ---- 0x644  sd a5,0(s3)  -- argv[argc] := q ---- *)
      assert (Hva2 : (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64)
                     = add_vec (g2 !!! Regidx s3_idx)
                         (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite Hv_s3_idx_12.
        assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                     = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal; lia. }
      assert (Hnd1 : (cmd + 8 + 8 * Z.of_nat i) mod 8 = 0)
        by (replace (cmd + 8 + 8 * Z.of_nat i) with (cmd + 8 * (1 + Z.of_nat i))
              by lia; apply Hmod8).
      destruct (uv_slot8_facts (cmd + 8 + 8 * Z.of_nat i)
                  (mword_of_int (cmd + 8 + 8 * Z.of_nat i)) ltac:(lia) Hnd1
                  ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
        as (Hu2 & Hcn2 & Hpg2 & Hal2).
      destruct (node_leaf Mg cmd (cmd + 8 + 8 * Z.of_nat i) Hwrndg
                  ltac:(lia) ltac:(lia)) as (wn1 & Hwn1 & Hwn1s).
      iApply (wp_uv_sd C pt Psh Mg g2 (mword_of_int 0x644)
                (mword_of_int 0 : mword 12) s3_idx a5_idx
                wn1 (mword_of_int (cmd + 8 + 8 * Z.of_nat i))
                (mword_of_int (sb + Z.of_nat ta))
                (ui_sh_644 pt Mg Hltext (sh_img_text Mg Hgg))
                Hva2 (eq_sym Hv_a5_idx_12) Hwn1 Hwn1s Hcn2 Hpg2 Hal2
                ltac:(rewrite Hu2;
                      exact (node_bytes Mg cmd (cmd + 8 + 8 * Z.of_nat i) Hwrndg
                               ltac:(lia) ltac:(lia)))
                with "Hcg Hpc").
      iIntros (CIDc4) "Hcg Hpc".
      iEval (rewrite Hu2) in "Hcg".
      set (Ms1 := uM_store8 Mg (cmd + 8 + 8 * Z.of_nat i)
                    (mword_of_int (sb + Z.of_nat ta) : mword 64)).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x644 : mword 64) 4
                        = mword_of_int 0x648)) in "Hpc".
      assert (Hgs1 : sh_img_sub Ms1)
        by (unfold Ms1; apply img_store8; [ exact Hgg | lia ]).
      assert (Hstks1 : uv_stack pt Ms1 sp0 320)
        by (unfold Ms1; apply stk_store8; exact Hstkg).
      assert (Hwrnds1 : uv_wr pt Ms1 cmd 168).
      { apply (uv_wr_dom pt Mg Ms1 cmd 168); [ | exact Hwrndg ].
        intros kk Hk. unfold Ms1. apply uM_store8_is_Some. exact Hk. }
      assert (Hbeq1 : uM_bytes Ms1 (uint sp0 - 128) 8
                        (mword_of_int (sb + Z.of_nat tb) : mword 64))
        by (unfold Ms1; apply st8_bytes_ne; [ lia | exact (Heqv ltac:(lia)) ]).
      (* ---- 0x648  ld a5,-128(s0)  -- a5 := eq ---- *)
      assert (Hva3 : (mword_of_int (uint sp0 - 128) : mword 64)
                     = add_vec (g2 !!! Regidx s0_idx)
                         (sign_extend' 64 (mword_of_int 3968 : mword 12))).
      { rewrite Hv_s0_idx_12.
        assert (Hc : (sign_extend' 64 (mword_of_int 3968 : mword 12) : mword 64)
                     = mword_of_int (-128))
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal; lia. }
      destruct (uv_slot8_facts (uint sp0 - 128)
                  (mword_of_int (uint sp0 - 128)) ltac:(lia) Haleq8
                  ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
        as (Hu3 & Hcn3 & Hpg3 & Hal3).
      destruct (stk_leaf8 Ms1 sp0 320 (uint sp0 - 128) Hstks1
                  ltac:(lia) ltac:(lia)) as (we & Hwe & _ & Hwel).
      iApply (wp_uv_ld C pt Psh Ms1 g2 (mword_of_int 0x648)
                (mword_of_int 3968 : mword 12) s0_idx a5_idx
                we (mword_of_int (uint sp0 - 128))
                (mword_of_int (sb + Z.of_nat tb))
                (ui_sh_648 pt Ms1 Hltext (sh_img_text Ms1 Hgs1))
                ltac:(vm_compute; discriminate) Hva3 Hwe Hwel Hcn3 Hpg3 Hal3
                ltac:(rewrite Hu3;
                      exact (stk_bytes8 Ms1 sp0 320 (uint sp0 - 128) Hstks1
                               ltac:(lia) ltac:(lia)))
                ltac:(rewrite Hu3; symmetry;
                      exact (word_of_bytes8 Ms1 (uint sp0 - 128)
                               (mword_of_int (sb + Z.of_nat tb)) Hbeq1))
                with "Hcg Hpc").
      iIntros (CIDc5) "Hcg Hpc".
      set (g3 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (sb + Z.of_nat tb) : mword 64)]> g2).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x648 : mword 64) 4
                        = mword_of_int 0x64c)) in "Hpc".
    assert (Hq13 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              g3 !!! Regidx r = g2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g2 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_13 : g3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq13 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_12).
    assert (Hv_s0_idx_13 : g3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq13 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_12).
    assert (Hv_s1_idx_13 : g3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq13 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_12).
    assert (Hv_s2_idx_13 : g3 !!! Regidx s2_idx = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite (Hq13 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_12).
    assert (Hv_s3_idx_13 : g3 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq13 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_12).
    assert (Hv_s4_idx_13 : g3 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_12).
    assert (Hv_s5_idx_13 : g3 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq13 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_12).
    assert (Hv_s6_idx_13 : g3 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq13 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_12).
    assert (Hv_s7_idx_13 : g3 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq13 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_12).
    assert (Hv_s8_idx_13 : g3 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq13 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_12).
    assert (Hv_s9_idx_13 : g3 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq13 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_12).
    assert (Hv_s10_idx_13 : g3 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq13 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_12).
    assert (Hv_s11_idx_13 : g3 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq13 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_12).
    assert (Hv_a5_idx_13 : g3 !!! Regidx a5_idx = (mword_of_int (sb + Z.of_nat tb) : mword 64))
      by exact (upd_eq g2 (Regidx a5_idx) _).

      (* ---- 0x64c  sd a5,80(s3)  -- eargv[argc] := eq ---- *)
      assert (Hva4 : (mword_of_int (cmd + 88 + 8 * Z.of_nat i) : mword 64)
                     = add_vec (g3 !!! Regidx s3_idx)
                         (sign_extend' 64 (mword_of_int 80 : mword 12))).
      { rewrite Hv_s3_idx_13.
        assert (Hc : (sign_extend' 64 (mword_of_int 80 : mword 12) : mword 64)
                     = mword_of_int 80)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal; lia. }
      assert (Hnd2 : (cmd + 88 + 8 * Z.of_nat i) mod 8 = 0)
        by (replace (cmd + 88 + 8 * Z.of_nat i) with (cmd + 8 * (11 + Z.of_nat i))
              by lia; apply Hmod8).
      destruct (uv_slot8_facts (cmd + 88 + 8 * Z.of_nat i)
                  (mword_of_int (cmd + 88 + 8 * Z.of_nat i)) ltac:(lia) Hnd2
                  ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
        as (Hu4 & Hcn4 & Hpg4 & Hal4).
      destruct (node_leaf Ms1 cmd (cmd + 88 + 8 * Z.of_nat i) Hwrnds1
                  ltac:(lia) ltac:(lia)) as (wn2 & Hwn2 & Hwn2s).
      iApply (wp_uv_sd C pt Psh Ms1 g3 (mword_of_int 0x64c)
                (mword_of_int 80 : mword 12) s3_idx a5_idx
                wn2 (mword_of_int (cmd + 88 + 8 * Z.of_nat i))
                (mword_of_int (sb + Z.of_nat tb))
                (ui_sh_64c pt Ms1 Hltext (sh_img_text Ms1 Hgs1))
                Hva4 (eq_sym Hv_a5_idx_13) Hwn2 Hwn2s Hcn4 Hpg4 Hal4
                ltac:(rewrite Hu4;
                      exact (node_bytes Ms1 cmd (cmd + 88 + 8 * Z.of_nat i)
                               Hwrnds1 ltac:(lia) ltac:(lia)))
                with "Hcg Hpc").
      iIntros (CIDc6) "Hcg Hpc".
      iEval (rewrite Hu4) in "Hcg".
      set (Ms2 := uM_store8 Ms1 (cmd + 88 + 8 * Z.of_nat i)
                    (mword_of_int (sb + Z.of_nat tb) : mword 64)).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x64c : mword 64) 4
                        = mword_of_int 0x650)) in "Hpc".
      assert (Hgs2 : sh_img_sub Ms2)
        by (unfold Ms2; apply img_store8; [ exact Hgs1 | lia ]).
      assert (Hstks2 : uv_stack pt Ms2 sp0 320)
        by (unfold Ms2; apply stk_store8; exact Hstks1).
      assert (Hwrnds2 : uv_wr pt Ms2 cmd 168).
      { apply (uv_wr_dom pt Ms1 Ms2 cmd 168); [ | exact Hwrnds1 ].
        intros kk Hk. unfold Ms2. apply uM_store8_is_Some. exact Hk. }
      (* ---- 0x650  c.addiw s2,s2,1  -- argc++ ---- *)
      assert (Hwaw : (mword_of_int (Z.of_nat (S i)) : mword 64)
                     = sign_extend' 64
                         (subrange_vec_dec
                            (add_vec (g3 !!! Regidx s2_idx)
                               (sign_extend' 64
                                  (sign_extend' 12 (mword_of_int 1 : mword 6))))
                            31 0)).
      { rewrite Hv_s2_idx_13.
        assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                      : mword 64) = mword_of_int 1)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc.
        rewrite (moi_addw (Z.of_nat i) 1 ltac:(unfold Z31; lia)).
        f_equal. lia. }
      iApply (wp_uv_caddiw C pt Psh Ms2 g3 (mword_of_int 0x650)
                (mword_of_int 1 : mword 6) s2_idx
                (mword_of_int (Z.of_nat (S i)))
                (ui_sh_650 pt Ms2 Hltext (sh_img_text Ms2 Hgs2))
                ltac:(vm_compute; discriminate) Hwaw with "Hcg Hpc").
      iIntros (CIDc7) "Hcg Hpc".
      set (g4 := <[Regidx s2_idx
                   := regval_into_reg (mword_of_int (Z.of_nat (S i)) : mword 64)]> g3).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x650 : mword 64) 2
                        = mword_of_int 0x652)) in "Hpc".
    assert (Hq14 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              g4 !!! Regidx r = g3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g3 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_14 : g4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq14 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_13).
    assert (Hv_s0_idx_14 : g4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq14 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_13).
    assert (Hv_s1_idx_14 : g4 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq14 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_13).
    assert (Hv_s2_idx_14 : g4 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
      by exact (upd_eq g3 (Regidx s2_idx) _).
    assert (Hv_s3_idx_14 : g4 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat i) : mword 64))
      by (rewrite (Hq14 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_13).
    assert (Hv_s4_idx_14 : g4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq14 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_13).
    assert (Hv_s5_idx_14 : g4 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq14 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_13).
    assert (Hv_s6_idx_14 : g4 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq14 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_13).
    assert (Hv_s7_idx_14 : g4 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq14 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_13).
    assert (Hv_s8_idx_14 : g4 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq14 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_13).
    assert (Hv_s9_idx_14 : g4 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq14 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_13).
    assert (Hv_s10_idx_14 : g4 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq14 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_13).
    assert (Hv_s11_idx_14 : g4 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq14 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_13).

      (* ---- 0x652  bne s2,s9,0x614 -- TAKEN (argc never reaches MAXARGS) ---- *)
      assert (Htkc : true
                     = uv_btaken BNE (g4 !!! Regidx s2_idx) (g4 !!! Regidx s9_idx)).
      { cbn [uv_btaken]. rewrite Hv_s2_idx_14 Hv_s9_idx_14.
        rewrite (moi_neq_vec (Z.of_nat (S i)) 10
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        replace (Z.eqb (Z.of_nat (S i)) 10) with false
          by (symmetry; apply Z.eqb_neq; lia).
        reflexivity. }
      assert (Htgtc : (mword_of_int 0x614 : mword 64)
                      = add_vec (mword_of_int 0x652)
                          (sign_extend' 64 (mword_of_int 8130 : mword 13)))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_btype C pt Psh Ms2 g4 (mword_of_int 0x652)
                (mword_of_int 8130 : mword 13) s9_idx s2_idx BNE
                true (mword_of_int 0x614)
                (ui_sh_652 pt Ms2 Hltext (sh_img_text Ms2 Hgs2))
                Htkc Htgtc ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CIDc8) "Hcg Hpc".
      (* ---- 0x614  c.addi s3,s3,8 ---- *)
      assert (Hwad : (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64)
                     = add_vec (g4 !!! Regidx s3_idx)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 8 : mword 6)))).
      { rewrite Hv_s3_idx_14.
        assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))
                      : mword 64) = mword_of_int 8)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal. rewrite Nat2Z.inj_succ. lia. }
      iApply (wp_uv_caddi C pt Psh Ms2 g4 (mword_of_int 0x614)
                (mword_of_int 8 : mword 6) s3_idx
                (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)))
                (ui_sh_614 pt Ms2 Hltext (sh_img_text Ms2 Hgs2))
                ltac:(vm_compute; discriminate) Hwad with "Hcg Hpc").
      iIntros (CIDc9) "Hcg Hpc".
      set (g5 := <[Regidx s3_idx
                   := regval_into_reg
                        (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64)]> g4).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x614 : mword 64) 2
                        = mword_of_int 0x616)) in "Hpc".
    assert (Hq15 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              g5 !!! Regidx r = g4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g4 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_15 : g5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq15 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_14).
    assert (Hv_s0_idx_15 : g5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq15 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_14).
    assert (Hv_s1_idx_15 : g5 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_14).
    assert (Hv_s2_idx_15 : g5 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq15 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_14).
    assert (Hv_s3_idx_15 : g5 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64))
      by exact (upd_eq g4 (Regidx s3_idx) _).
    assert (Hv_s4_idx_15 : g5 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq15 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_14).
    assert (Hv_s5_idx_15 : g5 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq15 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_14).
    assert (Hv_s6_idx_15 : g5 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq15 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_14).
    assert (Hv_s7_idx_15 : g5 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq15 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_14).
    assert (Hv_s8_idx_15 : g5 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq15 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_14).
    assert (Hv_s9_idx_15 : g5 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq15 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_14).
    assert (Hv_s10_idx_15 : g5 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq15 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_14).
    assert (Hv_s11_idx_15 : g5 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_14).
      (* ---- 0x616  c.mv ---- *)
      assert (Hw16 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                    = add_vec zero_reg (g5 !!! Regidx s5_idx))
        by (rewrite Hv_s5_idx_15 moi_add_zero_l; reflexivity).
      iApply (wp_uv_cmv C pt Psh Ms2 g5 (mword_of_int 0x616)
                a2_idx s5_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                (ui_sh_616 pt Ms2 Hltext (sh_img_text Ms2 Hgs2))
                ltac:(vm_compute; discriminate) Hw16 with "Hcg Hpc").
      iIntros (CIDL16) "Hcg Hpc".
      set (g6 := <[Regidx a2_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> g5).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x616 : mword 64) 2
                      = mword_of_int 0x618)) in "Hpc".
    assert (Hq16 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              g6 !!! Regidx r = g5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g5 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_16 : g6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq16 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_15).
    assert (Hv_s0_idx_16 : g6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq16 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_15).
    assert (Hv_s1_idx_16 : g6 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq16 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_15).
    assert (Hv_s2_idx_16 : g6 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq16 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_15).
    assert (Hv_s3_idx_16 : g6 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq16 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_15).
    assert (Hv_s4_idx_16 : g6 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq16 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_15).
    assert (Hv_s5_idx_16 : g6 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq16 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_15).
    assert (Hv_s6_idx_16 : g6 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq16 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_15).
    assert (Hv_s7_idx_16 : g6 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq16 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_15).
    assert (Hv_s8_idx_16 : g6 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq16 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_15).
    assert (Hv_s9_idx_16 : g6 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq16 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_15).
    assert (Hv_s10_idx_16 : g6 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq16 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_15).
    assert (Hv_s11_idx_16 : g6 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq16 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_15).
    assert (Hv_a2_idx_16 : g6 !!! Regidx a2_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq g5 (Regidx a2_idx) _).

      (* ---- 0x618  c.mv ---- *)
      assert (Hw17 : (mword_of_int psaddr : mword 64)
                    = add_vec zero_reg (g6 !!! Regidx s4_idx))
        by (rewrite Hv_s4_idx_16 moi_add_zero_l; reflexivity).
      iApply (wp_uv_cmv C pt Psh Ms2 g6 (mword_of_int 0x618)
                a1_idx s4_idx (mword_of_int psaddr : mword 64)
                (ui_sh_618 pt Ms2 Hltext (sh_img_text Ms2 Hgs2))
                ltac:(vm_compute; discriminate) Hw17 with "Hcg Hpc").
      iIntros (CIDL17) "Hcg Hpc".
      set (g7 := <[Regidx a1_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> g6).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x618 : mword 64) 2
                      = mword_of_int 0x61a)) in "Hpc".
    assert (Hq17 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              g7 !!! Regidx r = g6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g6 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_17 : g7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq17 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_16).
    assert (Hv_s0_idx_17 : g7 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq17 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_16).
    assert (Hv_s1_idx_17 : g7 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq17 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_16).
    assert (Hv_s2_idx_17 : g7 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq17 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_16).
    assert (Hv_s3_idx_17 : g7 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq17 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_16).
    assert (Hv_s4_idx_17 : g7 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq17 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_16).
    assert (Hv_s5_idx_17 : g7 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq17 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_16).
    assert (Hv_s6_idx_17 : g7 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq17 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_16).
    assert (Hv_s7_idx_17 : g7 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq17 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_16).
    assert (Hv_s8_idx_17 : g7 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq17 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_16).
    assert (Hv_s9_idx_17 : g7 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq17 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_16).
    assert (Hv_s10_idx_17 : g7 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq17 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_16).
    assert (Hv_s11_idx_17 : g7 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq17 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_16).
    assert (Hv_a1_idx_17 : g7 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq g6 (Regidx a1_idx) _).
    assert (Hv_a2_idx_17 : g7 !!! Regidx a2_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq17 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_16).

      (* ---- 0x61a  c.mv ---- *)
      assert (Hw18 : (mword_of_int cmd : mword 64)
                    = add_vec zero_reg (g7 !!! Regidx s1_idx))
        by (rewrite Hv_s1_idx_17 moi_add_zero_l; reflexivity).
      iApply (wp_uv_cmv C pt Psh Ms2 g7 (mword_of_int 0x61a)
                a0_idx s1_idx (mword_of_int cmd : mword 64)
                (ui_sh_61a pt Ms2 Hltext (sh_img_text Ms2 Hgs2))
                ltac:(vm_compute; discriminate) Hw18 with "Hcg Hpc").
      iIntros (CIDL18) "Hcg Hpc".
      set (g8 := <[Regidx a0_idx := regval_into_reg (mword_of_int cmd : mword 64)]> g7).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x61a : mword 64) 2
                      = mword_of_int 0x61c)) in "Hpc".
    assert (Hq18 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              g8 !!! Regidx r = g7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g7 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_18 : g8 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq18 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_17).
    assert (Hv_s0_idx_18 : g8 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq18 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_17).
    assert (Hv_s1_idx_18 : g8 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq18 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_17).
    assert (Hv_s2_idx_18 : g8 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq18 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_17).
    assert (Hv_s3_idx_18 : g8 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq18 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_17).
    assert (Hv_s4_idx_18 : g8 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq18 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_17).
    assert (Hv_s5_idx_18 : g8 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq18 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_17).
    assert (Hv_s6_idx_18 : g8 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq18 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_17).
    assert (Hv_s7_idx_18 : g8 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq18 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_17).
    assert (Hv_s8_idx_18 : g8 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq18 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_17).
    assert (Hv_s9_idx_18 : g8 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq18 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_17).
    assert (Hv_s10_idx_18 : g8 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq18 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_17).
    assert (Hv_s11_idx_18 : g8 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq18 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_17).
    assert (Hv_a0_idx_18 : g8 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq g7 (Regidx a0_idx) _).
    assert (Hv_a1_idx_18 : g8 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq18 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_17).
    assert (Hv_a2_idx_18 : g8 !!! Regidx a2_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq18 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_17).

      (* ---- 0x61c  jal ra, 0x4ac ---- *)
      assert (Ht19 : (mword_of_int 0x4ac : mword 64)
                     = add_vec (mword_of_int 0x61c)
                         (sign_extend' 64 (mword_of_int 2096784 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hl19 : (mword_of_int 0x620 : mword 64)
                     = add_vec_int (mword_of_int 0x61c : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_jal C pt Psh Ms2 g8 (mword_of_int 0x61c)
                (mword_of_int 2096784 : mword 21) ra_idx
                (mword_of_int 0x4ac) (mword_of_int 0x620)
                (ui_sh_61c pt Ms2 Hltext (sh_img_text Ms2 Hgs2))
                ltac:(vm_compute; discriminate) Ht19 Hl19
                ltac:(vm_compute; reflexivity) with "Hcg Hpc").
      iIntros (CIDL19) "Hcg Hpc".
      set (g9 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x620 : mword 64)]> g8).
    assert (Hq19 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              g9 !!! Regidx r = g8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g8 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_19 : g9 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq19 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_18).
    assert (Hv_s0_idx_19 : g9 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq19 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_18).
    assert (Hv_s1_idx_19 : g9 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq19 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_18).
    assert (Hv_s2_idx_19 : g9 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq19 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_18).
    assert (Hv_s3_idx_19 : g9 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64))
      by (rewrite (Hq19 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_18).
    assert (Hv_s4_idx_19 : g9 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq19 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_18).
    assert (Hv_s5_idx_19 : g9 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq19 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_18).
    assert (Hv_s6_idx_19 : g9 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq19 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_18).
    assert (Hv_s7_idx_19 : g9 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq19 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_18).
    assert (Hv_s8_idx_19 : g9 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq19 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_18).
    assert (Hv_s9_idx_19 : g9 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hq19 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_18).
    assert (Hv_s10_idx_19 : g9 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq19 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_18).
    assert (Hv_s11_idx_19 : g9 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq19 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_18).
    assert (Hv_a0_idx_19 : g9 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq19 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_18).
    assert (Hv_a1_idx_19 : g9 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq19 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_18).
    assert (Hv_a2_idx_19 : g9 !!! Regidx a2_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq19 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_18).
    assert (Hv_ra_idx_19 : g9 !!! Regidx ra_idx = (mword_of_int 0x620 : mword 64))
      by exact (upd_eq g8 (Regidx ra_idx) _).
      assert (HWs1 : uM_only_in Mi0 Ms1
                       [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)]).
      { apply (uM_only_in_trans Mi0 Mg Ms1); [ exact HWg | ].
        apply (win3_in Mg Ms1 hbase 65536 psaddr 8 (uint sp0 - 320) 208).
        - intros kk Hk. unfold Ms1. apply uM_store8_is_Some. exact Hk.
        - intros kk H1 H2 H3. unfold Ms1. apply um8_ne. lia. }
      assert (HWs2 : uM_only_in Mi0 Ms2
                       [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)]).
      { apply (uM_only_in_trans Mi0 Ms1 Ms2); [ exact HWs1 | ].
        apply (win3_in Ms1 Ms2 hbase 65536 psaddr 8 (uint sp0 - 320) 208).
        - intros kk Hk. unfold Ms2. apply uM_store8_is_Some. exact Hk.
        - intros kk H1 H2 H3. unfold Ms2. apply um8_ne. lia. }
      assert (Hpres2 : sh_parse_pre pt hbase hlen Ms2 sb bs sp0 320)
        by exact (pe_w3_pre Mi0 Ms2 sb psaddr bs sp0 HWs2 Hbc Hpslo Hpre0).
      assert (HpreR : sh_parse_pre pt hbase hlen Ms2 sb bs
                        (mword_of_int (uint sp0 - 128) : mword 64) 192).
      { apply (parse_pre_move Ms2 Ms2 sb bs sp0
                 (mword_of_int (uint sp0 - 128)) 320 192).
        - intros kk H; exact H.
        - intros kk _; reflexivity.
        - intros kk _; reflexivity.
        - rewrite Huspk. lia.
        - rewrite Huspk. lia.
        - exact Hpres2. }
      destruct (uv_stack_split pt Ms2 sp0 320 128 192 ltac:(lia) ltac:(lia)
                  ltac:(vm_compute; reflexivity) ltac:(lia) Hstks2)
        as (Hstks2a & HstkR).
      rewrite (uv_stack_sp_moi pt Ms2 sp0 128 Hstks2a) in HstkR.
      assert (Hcs2ps : uM_bytes Ms2 psaddr 8
                (mword_of_int (sb + Z.of_nat (tb + sh_skipws (drop tb bs)))
                 : mword 64)).
      { unfold Ms2, Ms1. apply st8_bytes_ne; [ lia | ].
        apply st8_bytes_ne; [ lia | ]. exact Hpsg. }
      assert (Hrdpss2 : uv_rd pt Ms2 psaddr 8)
        by exact (uv_rd_dom pt Mi0 Ms2 psaddr 8 (proj1 HWs2) Hrdps0).
      assert (Hwrpss2 : uv_wr pt Ms2 psaddr 8)
        by exact (uv_wr_dom pt Mi0 Ms2 psaddr 8 (proj1 HWs2) Hwrps0).
      assert (HcellR : sh_ptr_cell pt Ms2 psaddr
                         (sb + Z.of_nat (tb + sh_skipws (drop tb bs)))
                         (mword_of_int (uint sp0 - 128) : mword 64))
        by exact (mk_ptr_cell Ms2 psaddr
                    (sb + Z.of_nat (tb + sh_skipws (drop tb bs)))
                    (mword_of_int (uint sp0 - 128))
                    Hcs2ps Hrdpss2 Hwrpss2 Hpsal
                    ltac:(rewrite Huspk; lia)
                    ltac:(change (2 ^ 38) with 274877906944; lia)).
      assert (Hoff2 : (tb + sh_skipws (drop tb bs) <= length bs)%nat).
      { pose proof (sh_skipws_le (drop tb bs)) as Hx.
        rewrite length_drop in Hx. lia. }
      assert (Hret2c : is_aligned_vaddr (Virtaddr (g9 !!! Regidx ra_idx)) 2 = true)
        by (rewrite Hv_ra_idx_19; vm_compute; reflexivity).
      assert (Hargs2 : forall (j : nat) (t' : nat * nat),
                take (S i) toks !! j = Some t' ->
                uM_bytes Ms2 (cmd + 8 + 8 * Z.of_nat j) 8
                  (mword_of_int (sb + Z.of_nat (fst t')) : mword 64) /\
                uM_bytes Ms2 (cmd + 88 + 8 * Z.of_nat j) 8
                  (mword_of_int (sb + Z.of_nat (snd t')) : mword 64)).
      { intros j t' Hj.
        rewrite (take_S_r toks i (ta, tb) Hti) in Hj.
        assert (Hlen : length (take i toks) = i) by (rewrite length_take; lia).
        destruct (decide (j < i)%nat) as [ Hjlt | Hjge ].
        - rewrite (lookup_app_l (take i toks) [(ta, tb)] j ltac:(lia)) in Hj.
          destruct (Hargg j t' Hj) as (Hb1 & Hb2). split.
          + unfold Ms2, Ms1. apply st8_bytes_ne; [ lia | ].
            apply st8_bytes_ne; [ lia | ]. exact Hb1.
          + unfold Ms2, Ms1. apply st8_bytes_ne; [ lia | ].
            apply st8_bytes_ne; [ lia | ]. exact Hb2.
        - assert (Hji : j = i).
          { pose proof (lookup_lt_Some _ j t' Hj) as Hx.
            rewrite length_app length_take in Hx. cbn [length] in Hx. lia. }
          subst j.
          rewrite (lookup_app_r (take i toks) [(ta, tb)] i ltac:(lia)) in Hj.
          rewrite Hlen Nat.sub_diag in Hj. cbn [lookup list_lookup] in Hj.
          injection Hj as Hj. subst t'. cbn [fst snd]. split.
          + unfold Ms2. apply st8_bytes_ne; [ lia | ].
            unfold Ms1. apply uM_store8_bytes.
          + unfold Ms2. apply uM_store8_bytes. }
      assert (Htypes2 : uM_bytes Ms2 cmd 4 (mword_of_int 1 : mword 32)).
      { intros j Hj. unfold Ms2.
        rewrite (um8_ne Ms1 (cmd + 88 + 8 * Z.of_nat i) _ (cmd + Z.of_nat j)
                   ltac:(lia)).
        unfold Ms1.
        rewrite (um8_ne Mg (cmd + 8 + 8 * Z.of_nat i) _ (cmd + Z.of_nat j)
                   ltac:(lia)).
        exact (Htypeg j Hj). }
      (* ---- 0x4ac  parseredirs(ret, ps, es) -- returns [ret] ---- *)
      iApply (wp_sh_parseredirs CIDL19 Ms2 g9
                (mword_of_int (uint sp0 - 128)) cmd psaddr sb bs
                (tb + sh_skipws (drop tb bs))%nat
                HpreR Hv_csp_rs1_19 HstkR Hv_a0_idx_19 Hv_a1_idx_19
                Hv_a2_idx_19 HcellR Hoff2 Hret2c with "Hcg Hpc [Hcont]").
      iIntros (CIDL20 r1 Mr) "%Hcs3 %Ha0r %Hpsr %Honly3 Hcg Hpc".
      iEval (rewrite Hv_ra_idx_19) in "Hpc".
      assert (Hv_csp_rs1_20 : r1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
        by (rewrite (Hcs3 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_19).
      assert (Hv_s0_idx_20 : r1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
        by (rewrite (Hcs3 s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_19).
      assert (Hv_s1_idx_20 : r1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
        by (rewrite (Hcs3 s1_idx ltac:(vm_compute; reflexivity)); exact Hv_s1_idx_19).
      assert (Hv_s2_idx_20 : r1 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
        by (rewrite (Hcs3 s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_19).
      assert (Hv_s3_idx_20 : r1 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64))
        by (rewrite (Hcs3 s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_19).
      assert (Hv_s4_idx_20 : r1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
        by (rewrite (Hcs3 s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_19).
      assert (Hv_s5_idx_20 : r1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
        by (rewrite (Hcs3 s5_idx ltac:(vm_compute; reflexivity)); exact Hv_s5_idx_19).
      assert (Hv_s6_idx_20 : r1 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
        by (rewrite (Hcs3 s6_idx ltac:(vm_compute; reflexivity)); exact Hv_s6_idx_19).
      assert (Hv_s7_idx_20 : r1 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
        by (rewrite (Hcs3 s7_idx ltac:(vm_compute; reflexivity)); exact Hv_s7_idx_19).
      assert (Hv_s8_idx_20 : r1 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
        by (rewrite (Hcs3 s8_idx ltac:(vm_compute; reflexivity)); exact Hv_s8_idx_19).
      assert (Hv_s9_idx_20 : r1 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
        by (rewrite (Hcs3 s9_idx ltac:(vm_compute; reflexivity)); exact Hv_s9_idx_19).
      assert (Hv_s10_idx_20 : r1 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
        by (rewrite (Hcs3 s10_idx ltac:(vm_compute; reflexivity)); exact Hv_s10_idx_19).
      assert (Hv_s11_idx_20 : r1 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
        by (rewrite (Hcs3 s11_idx ltac:(vm_compute; reflexivity)); exact Hv_s11_idx_19).
      rewrite Huspk in Honly3.
      rewrite (sh_skipws_drop_idem bs tb) Nat.add_0_r in Hpsr.
      assert (HWr : uM_only_in Mi0 Mr
                      [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)]).
      { apply (uM_only_in_trans Mi0 Ms2 Mr); [ exact HWs2 | ].
        apply (win3_in Ms2 Mr hbase 65536 psaddr 8 (uint sp0 - 320) 208).
        - exact (proj1 Honly3).
        - intros kk H1 H2 H3.
          exact (win2_out Ms2 Mr psaddr 8 (uint sp0 - 128 - 192) 192 kk
                   Honly3 H2 ltac:(lia)). }
      assert (Hnoder : forall kk : Z, cmd <= kk < cmd + 168 -> Mr !! kk = Ms2 !! kk)
        by (intros kk Hk;
            exact (win2_out Ms2 Mr psaddr 8 (uint sp0 - 128 - 192) 192 kk
                     Honly3 ltac:(lia) ltac:(lia))).
      assert (HtypeR : uM_bytes Mr cmd 4 (mword_of_int 1 : mword 32))
        by (intros j Hj; rewrite (Hnoder (cmd + Z.of_nat j) ltac:(lia));
            exact (Htypes2 j Hj)).
      assert (HargR : forall (j : nat) (t' : nat * nat),
                take (S i) toks !! j = Some t' ->
                uM_bytes Mr (cmd + 8 + 8 * Z.of_nat j) 8
                  (mword_of_int (sb + Z.of_nat (fst t')) : mword 64) /\
                uM_bytes Mr (cmd + 88 + 8 * Z.of_nat j) 8
                  (mword_of_int (sb + Z.of_nat (snd t')) : mword 64)).
      { intros j t' Hj.
        assert (Hjl : (j < S i)%nat)
          by (pose proof (lookup_lt_Some _ j t' Hj) as Hx;
              rewrite length_take in Hx; lia).
        destruct (Hargs2 j t' Hj) as (Hb1 & Hb2). split.
        - intros u Hu.
          rewrite (Hnoder (cmd + 8 + 8 * Z.of_nat j + Z.of_nat u) ltac:(lia)).
          exact (Hb1 u Hu).
        - intros u Hu.
          rewrite (Hnoder (cmd + 88 + 8 * Z.of_nat j + Z.of_nat u) ltac:(lia)).
          exact (Hb2 u Hu). }
      (* ---- 0x620  c.mv s1,a0 ---- *)
      assert (Hw21 : (mword_of_int cmd : mword 64)
                     = add_vec zero_reg (r1 !!! Regidx a0_idx))
        by (rewrite Ha0r moi_add_zero_l; reflexivity).
      assert (Hgr : sh_img_sub Mr).
      { pose proof (pe_w3_pre Mi0 Mr sb psaddr bs sp0 HWr Hbc Hpslo Hpre0)
          as (_ & Hx & _). exact Hx. }
      iApply (wp_uv_cmv C pt Psh Mr r1 (mword_of_int 0x620)
                s1_idx a0_idx (mword_of_int cmd)
                (ui_sh_620 pt Mr Hltext (sh_img_text Mr Hgr))
                ltac:(vm_compute; discriminate) Hw21 with "Hcg Hpc").
      iIntros (CIDL21) "Hcg Hpc".
      set (r2 := <[Regidx s1_idx
                   := regval_into_reg (mword_of_int cmd : mword 64)]> r1).
      iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                      : add_vec_int (mword_of_int 0x620 : mword 64) 2
                        = mword_of_int 0x622)) in "Hpc".
      assert (Hq21 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                r2 !!! Regidx r = r1 !!! Regidx r)
        by (intros r Hr; exact (upd_ne r1 (Regidx s1_idx) (Regidx r) _ Hr)).
      assert (Hv_csp_rs1_21 : r2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
        by (rewrite (Hq21 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_20).
      assert (Hv_s0_idx_21 : r2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
        by (rewrite (Hq21 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_20).
      assert (Hv_s1_idx_21 : r2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
        by exact (upd_eq r1 (Regidx s1_idx) _).
      assert (Hv_s2_idx_21 : r2 !!! Regidx s2_idx = (mword_of_int (Z.of_nat (S i)) : mword 64))
        by (rewrite (Hq21 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_20).
      assert (Hv_s3_idx_21 : r2 !!! Regidx s3_idx = (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64))
        by (rewrite (Hq21 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_20).
      assert (Hv_s4_idx_21 : r2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
        by (rewrite (Hq21 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_20).
      assert (Hv_s5_idx_21 : r2 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
        by (rewrite (Hq21 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_20).
      assert (Hv_s6_idx_21 : r2 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
        by (rewrite (Hq21 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_20).
      assert (Hv_s7_idx_21 : r2 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
        by (rewrite (Hq21 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_20).
      assert (Hv_s8_idx_21 : r2 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
        by (rewrite (Hq21 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_20).
      assert (Hv_s9_idx_21 : r2 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
        by (rewrite (Hq21 s9_idx ltac:(vm_compute; discriminate)); exact Hv_s9_idx_20).
      assert (Hv_s10_idx_21 : r2 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
        by (rewrite (Hq21 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_20).
      assert (Hv_s11_idx_21 : r2 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
        by (rewrite (Hq21 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_20).
      (* ---- the back edge: one fewer token to go ---- *)
      assert (Hmeas2 : (length rest < nn)%nat)
        by (cbn [length] in Hmeas; lia).
      assert (Hile2 : (S i <= length toks)%nat) by lia.
      iApply (IH CIDL21 Mi0 Mr r2 sp0 psaddr sb cmd bs
                (tb + sh_skipws (drop tb bs))%nat (S i) toks rest
                Hmeas2 Hpre0 Hbc Hstk0 Hile2 (eq_sym Hdropi)
                (sh_tokens_shift bs tb rest Hrest) Hmax Hoff2
                Hcmdlo Hcmdhi Hcmd16 Hpslo Hpshi Hpsal Hrdps0 Hwrps0 Hwrnd0
                HWr Hpsr HtypeR HargR
                Hv_csp_rs1_21 Hv_s0_idx_21 Hv_s1_idx_21 Hv_s2_idx_21
                Hv_s3_idx_21 Hv_s4_idx_21 Hv_s5_idx_21 Hv_s6_idx_21
                Hv_s7_idx_21 Hv_s8_idx_21 Hv_s9_idx_21 Hv_s10_idx_21
                Hv_s11_idx_21 with "Hcg Hpc [Hcont]").
      iIntros (CIDz mz Mz) "%HWz %Htypez %Hargz %Hpsz %Hs1z %Hs2z %Hpresz Hcg Hpc".
      iApply ("Hcont" $! CIDz mz Mz with "[] [] [] [] [] [] [] Hcg Hpc").
      + iPureIntro. exact HWz.
      + iPureIntro. exact Htypez.
      + iPureIntro. exact Hargz.
      + iPureIntro. exact Hpsz.
      + iPureIntro. exact Hs1z.
      + iPureIntro. exact Hs2z.
      + iPureIntro. intros r Hr N1 N2 N3.
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na1 : Regidx r <> Regidx a1_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na2 : Regidx r <> Regidx a2_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na3 : Regidx r <> Regidx a3_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (Hpresz r Hr N1 N2 N3).
        rewrite (Hq21 r N1) (Hcs3 r Hr) (Hq19 r Nra) (Hq18 r Na0) (Hq17 r Na1)
                (Hq16 r Na2) (Hq15 r N3) (Hq14 r N2) (Hq13 r Na5) (Hq12 r Na5)
                (Hcs2 r Hr) (Hq10 r Nra) (Hq9 r Na0) (Hq8 r Na1) (Hq7 r Na2)
                (Hq6 r Na3) (Hcs1 r Hr) (Hq4 r Nra) (Hq3 r Na0) (Hq2 r Na1)
                (Hq1 r Na2).
        reflexivity.
  Qed.



  (* ------------------------------------------------------------------- *)
  (* §3e  parseexec @0x590 -- the only one of the four that does work.     *)
  (*                                                                       *)
  (*   590..59a  the 128-byte prologue's FIRST half (ra, s0, s1, s4, s5)   *)
  (*   59c..5aa  s4 := ps, s5 := es; peek(ps, es, "(") -- 0, no block      *)
  (*   5ae       bnez a0,5ee   -- not taken                                *)
  (*   5b0..5be  the prologue's SECOND half (s2, s3, s6..s11)              *)
  (*   5c0       argc := 0 (a0 is peek's 0)                                *)
  (*   5c2       execcmd()  -- the run's single malloc                      *)
  (*   5c6..5ce  s3 := &argv[0], parseredirs(ret, ps, es)                   *)
  (*   5d2..5ec  s6 := "|)&;", s8/s7 := &eq/&q, s10 := 'a', s9 := MAXARGS   *)
  (*   622..620  the argument loop (§3d)                                    *)
  (*   662..680  argv[argc] = eargv[argc] = 0 and the second half's reload  *)
  (*   5f8..606  a0 := ret and the first half's reload                      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_parseexec (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr sb : Z) (bs : list (bv 8)) (off : nat)
      (toks : list (nat * nat)) :
    wp_sh_parseexec_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 psaddr sb bs off toks.
  Proof.
    intros Hpre Hsp Hst Hps Hes Hcell Hbufc Hoff Htoks Hmax
           Hfreep0 Hbasesz0 Hbssw Hret2.
    pose proof Hpre as (Hlay & Himg & Htab & Hbuf & Hns & Hrdb & Hwrb & Hs0p &
                        Hs0hi & Hfr & Hbufhi).
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    unfold sh_frame_ok in Hfr.
    assert (Hst320 : uv_stack pt M sp0 320) by exact Hst.
    pose proof (us_lo _ _ _ _ Hst320) as Hlo.
    pose proof (us_canon _ _ _ _ Hst320) as Hcan.
    pose proof (us_al _ _ _ _ Hst320) as Hal16.
    rewrite Z.rem_mod_nonneg in Hal16; [ | lia | lia ].
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi.
    assert (Hfrz : hbase + hlen <= uint sp0 - 320) by exact Hfr.
    assert (Hbufz : sb + Z.of_nat (length bs) + 1 <= uint sp0 - 320)
      by exact Hbufhi.
    pose proof Hcell as (Hcb & Hcrd & Hcwr & Hcal & Hclo & Hchi).
    change (2 ^ 38) with 274877906944 in Hchi.
    pose proof Hbufc as (Hbd1 & Hbd2 & Hbd3).
    unfold sh_disj in Hbd1, Hbd2, Hbd3.
    change SH_FREEP with 8208 in Hbd1. change SH_BASE with 8328 in Hbd2.
    assert (Hhb4096 : hbase = 4096 * (hbase / 4096)).
    { pose proof (shl_hbase _ _ _ Hlay) as Hx.
      rewrite Z.rem_mod_nonneg in Hx; [ | lia | lia ].
      pose proof (Z.div_mod hbase 4096 ltac:(lia)). lia. }
    destruct (uv_stack_split pt M sp0 320 128 192 ltac:(lia) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hst320)
      as (Hst128 & Hst192).
    rewrite (uv_stack_sp_moi pt M sp0 128 Hst128) in Hst192.
    assert (Huspk : uint (mword_of_int (uint sp0 - 128) : mword 64)
                    = uint sp0 - 128)
      by (apply uint_moi; unfold Z64; lia).
    destruct (uv_stack_split pt M (mword_of_int (uint sp0 - 128)) 192 80 112
                ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                Hst192) as (Hstpk80 & _).
    destruct (uv_stack_split pt M (mword_of_int (uint sp0 - 128)) 192 128 64
                ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                Hst192) as (Hstpk128 & _).
    assert (Hsx : ShSyms.parseexec = 0x590)
      by (destruct sh_syms_pins as (_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hsx) in "Hpc".
    (* ---- 0x590  c.addi16sp sp,sp,-128 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 128) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi16sp_imm (mword_of_int 56 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp. rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 56 : mword 6))
                    : mword 64) = mword_of_int (-128))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x590)
              (mword_of_int 56 : mword 6) (mword_of_int (uint sp0 - 128))
              (ui_sh_590 pt M Hltext (sh_img_text M Himg)) Hwsp with "Hcg Hpc").
    iIntros (CIDp0) "Hcg Hpc".
    set (e1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 128) : mword 64)]> m).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x590 : mword 64) 2
                      = mword_of_int 0x592)) in "Hpc".
    assert (Hq1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              e1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_1 : e1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hv_a0_idx_1 : e1 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq1 a0_idx ltac:(vm_compute; discriminate)); exact Hps).
    assert (Hv_a1_idx_1 : e1 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq1 a1_idx ltac:(vm_compute; discriminate)); exact Hes).
    (* ---- 0x592  c.sdsp ra,120(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp0 Psh M e1 sp0 (mword_of_int 0x592)
              (mword_of_int 15 : mword 6) ra_idx 128 120
              (ui_sh_592 pt M Hltext (sh_img_text M Himg)) Hst128
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x592 : mword 64) 2
                      = mword_of_int 0x594)) in "Hpc".
    set (P1 := uM_store8 M (uint sp0 - 128 + 120) (e1 !!! Regidx ra_idx)).
    assert (HoP1 : uM_only M P1 (uint sp0 - 128 + 72) 56)
      by (unfold P1; apply only_step8; [ lia | lia | apply uM_only_refl ]).
    assert (HgP1 : sh_img_sub P1)
      by (exact (only_img M P1 (uint sp0 - 128 + 72) 56 HoP1 ltac:(lia) Himg)).
    assert (HkP1 : uv_stack pt P1 sp0 320)
      by (exact (stk_dom M P1 sp0 320 (proj1 HoP1) Hst)).
    assert (HfP1 : uv_stack pt P1 sp0 128)
      by (exact (stk_dom M P1 sp0 128 (proj1 HoP1) Hst128)).

    (* ---- 0x594  c.sdsp s0,112(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp1 Psh P1 e1 sp0 (mword_of_int 0x594)
              (mword_of_int 14 : mword 6) s0_idx 128 112
              (ui_sh_594 pt P1 Hltext (sh_img_text P1 HgP1)) HfP1
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x594 : mword 64) 2
                      = mword_of_int 0x596)) in "Hpc".
    set (P2 := uM_store8 P1 (uint sp0 - 128 + 112) (e1 !!! Regidx s0_idx)).
    assert (HoP2 : uM_only M P2 (uint sp0 - 128 + 72) 56)
      by (unfold P2; apply only_step8; [ lia | lia | exact HoP1 ]).
    assert (HgP2 : sh_img_sub P2)
      by (exact (only_img M P2 (uint sp0 - 128 + 72) 56 HoP2 ltac:(lia) Himg)).
    assert (HkP2 : uv_stack pt P2 sp0 320)
      by (exact (stk_dom M P2 sp0 320 (proj1 HoP2) Hst)).
    assert (HfP2 : uv_stack pt P2 sp0 128)
      by (exact (stk_dom M P2 sp0 128 (proj1 HoP2) Hst128)).

    (* ---- 0x596  c.sdsp s1,104(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp2 Psh P2 e1 sp0 (mword_of_int 0x596)
              (mword_of_int 13 : mword 6) s1_idx 128 104
              (ui_sh_596 pt P2 Hltext (sh_img_text P2 HgP2)) HfP2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x596 : mword 64) 2
                      = mword_of_int 0x598)) in "Hpc".
    set (P3 := uM_store8 P2 (uint sp0 - 128 + 104) (e1 !!! Regidx s1_idx)).
    assert (HoP3 : uM_only M P3 (uint sp0 - 128 + 72) 56)
      by (unfold P3; apply only_step8; [ lia | lia | exact HoP2 ]).
    assert (HgP3 : sh_img_sub P3)
      by (exact (only_img M P3 (uint sp0 - 128 + 72) 56 HoP3 ltac:(lia) Himg)).
    assert (HkP3 : uv_stack pt P3 sp0 320)
      by (exact (stk_dom M P3 sp0 320 (proj1 HoP3) Hst)).
    assert (HfP3 : uv_stack pt P3 sp0 128)
      by (exact (stk_dom M P3 sp0 128 (proj1 HoP3) Hst128)).

    (* ---- 0x598  c.sdsp s4,80(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp3 Psh P3 e1 sp0 (mword_of_int 0x598)
              (mword_of_int 10 : mword 6) s4_idx 128 80
              (ui_sh_598 pt P3 Hltext (sh_img_text P3 HgP3)) HfP3
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x598 : mword 64) 2
                      = mword_of_int 0x59a)) in "Hpc".
    set (P4 := uM_store8 P3 (uint sp0 - 128 + 80) (e1 !!! Regidx s4_idx)).
    assert (HoP4 : uM_only M P4 (uint sp0 - 128 + 72) 56)
      by (unfold P4; apply only_step8; [ lia | lia | exact HoP3 ]).
    assert (HgP4 : sh_img_sub P4)
      by (exact (only_img M P4 (uint sp0 - 128 + 72) 56 HoP4 ltac:(lia) Himg)).
    assert (HkP4 : uv_stack pt P4 sp0 320)
      by (exact (stk_dom M P4 sp0 320 (proj1 HoP4) Hst)).
    assert (HfP4 : uv_stack pt P4 sp0 128)
      by (exact (stk_dom M P4 sp0 128 (proj1 HoP4) Hst128)).

    (* ---- 0x59a  c.sdsp s5,72(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp4 Psh P4 e1 sp0 (mword_of_int 0x59a)
              (mword_of_int 9 : mword 6) s5_idx 128 72
              (ui_sh_59a pt P4 Hltext (sh_img_text P4 HgP4)) HfP4
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x59a : mword 64) 2
                      = mword_of_int 0x59c)) in "Hpc".
    set (P5 := uM_store8 P4 (uint sp0 - 128 + 72) (e1 !!! Regidx s5_idx)).
    assert (HoP5 : uM_only M P5 (uint sp0 - 128 + 72) 56)
      by (unfold P5; apply only_step8; [ lia | lia | exact HoP4 ]).
    assert (HgP5 : sh_img_sub P5)
      by (exact (only_img M P5 (uint sp0 - 128 + 72) 56 HoP5 ltac:(lia) Himg)).
    assert (HkP5 : uv_stack pt P5 sp0 320)
      by (exact (stk_dom M P5 sp0 320 (proj1 HoP5) Hst)).
    assert (HfP5 : uv_stack pt P5 sp0 128)
      by (exact (stk_dom M P5 sp0 128 (proj1 HoP5) Hst128)).
    (* ---- 0x59c  c.addi4spn s0,sp,128 ---- *)
    assert (Hw2 : (mword_of_int (uint sp0) : mword 64)
                  = add_vec (e1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 32 : mword 8)))).
    { rewrite Hv_csp_rs1_1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 32 : mword 8))
                    : mword 64) = mword_of_int 128)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh P5 e1 (mword_of_int 0x59c)
              (mword_of_int 0 : mword 3) (mword_of_int 32 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_59c pt P5 Hltext (sh_img_text P5 HgP5))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw2
              with "Hcg Hpc").
    iIntros (CIDa2) "Hcg Hpc".
    set (e2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> e1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x59c : mword 64) 2
                      = mword_of_int 0x59e)) in "Hpc".
    assert (Hq2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              e2 !!! Regidx r = e1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_2 : e2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_1).
    assert (Hv_s0_idx_2 : e2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by exact (upd_eq e1 (Regidx s0_idx) _).
    assert (Hv_a0_idx_2 : e2 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq2 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_1).
    assert (Hv_a1_idx_2 : e2 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq2 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_1).

    (* ---- 0x59e  c.mv ---- *)
    assert (Hw3 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (e2 !!! Regidx a0_idx))
      by (rewrite Hv_a0_idx_2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P5 e2 (mword_of_int 0x59e)
              s4_idx a0_idx (mword_of_int psaddr : mword 64)
              (ui_sh_59e pt P5 Hltext (sh_img_text P5 HgP5))
              ltac:(vm_compute; discriminate) Hw3 with "Hcg Hpc").
    iIntros (CIDa3) "Hcg Hpc".
    set (e3 := <[Regidx s4_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> e2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x59e : mword 64) 2
                      = mword_of_int 0x5a0)) in "Hpc".
    assert (Hq3 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              e3 !!! Regidx r = e2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e2 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_3 : e3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_2).
    assert (Hv_s0_idx_3 : e3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq3 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_2).
    assert (Hv_s4_idx_3 : e3 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq e2 (Regidx s4_idx) _).
    assert (Hv_a0_idx_3 : e3 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq3 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_2).
    assert (Hv_a1_idx_3 : e3 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq3 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_2).

    (* ---- 0x5a0  c.mv ---- *)
    assert (Hw4 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (e3 !!! Regidx a1_idx))
      by (rewrite Hv_a1_idx_3 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P5 e3 (mword_of_int 0x5a0)
              s5_idx a1_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_5a0 pt P5 Hltext (sh_img_text P5 HgP5))
              ltac:(vm_compute; discriminate) Hw4 with "Hcg Hpc").
    iIntros (CIDa4) "Hcg Hpc".
    set (e4 := <[Regidx s5_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> e3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5a0 : mword 64) 2
                      = mword_of_int 0x5a2)) in "Hpc".
    assert (Hq4 : forall r : mword 5, Regidx r <> Regidx s5_idx ->
              e4 !!! Regidx r = e3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e3 (Regidx s5_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_4 : e4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq4 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_3).
    assert (Hv_s0_idx_4 : e4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq4 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_3).
    assert (Hv_s4_idx_4 : e4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_3).
    assert (Hv_s5_idx_4 : e4 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq e3 (Regidx s5_idx) _).
    assert (Hv_a0_idx_4 : e4 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_3).
    assert (Hv_a1_idx_4 : e4 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq4 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_3).

    (* ---- 0x5a2  auipc a2,0x1 ---- *)
    assert (Hw5 : (mword_of_int 5538 : mword 64)
                  = add_vec (mword_of_int 0x5a2) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh P5 e4 (mword_of_int 0x5a2)
              (mword_of_int 1 : mword 20) a2_idx (mword_of_int 5538)
              (ui_sh_5a2 pt P5 Hltext (sh_img_text P5 HgP5))
              ltac:(vm_compute; discriminate) Hw5 with "Hcg Hpc").
    iIntros (CIDa5) "Hcg Hpc".
    set (e5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 5538 : mword 64)]> e4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5a2 : mword 64) 4
                      = mword_of_int 0x5a6)) in "Hpc".
    assert (Hq5 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              e5 !!! Regidx r = e4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e4 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_5 : e5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq5 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_4).
    assert (Hv_s0_idx_5 : e5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq5 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_4).
    assert (Hv_s4_idx_5 : e5 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_4).
    assert (Hv_s5_idx_5 : e5 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq5 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_4).
    assert (Hv_a2_idx_5 : e5 !!! Regidx a2_idx = (mword_of_int 5538 : mword 64))
      by exact (upd_eq e4 (Regidx a2_idx) _).
    assert (Hv_a0_idx_5 : e5 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_4).
    assert (Hv_a1_idx_5 : e5 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq5 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_4).

    (* ---- 0x5a6  addi ---- *)
    assert (Hw6 : (mword_of_int 4856 : mword 64)
                  = add_vec (e5 !!! Regidx a2_idx)
                      (sign_extend' 64 (mword_of_int 3414 : mword 12))).
    { rewrite Hv_a2_idx_5.
      assert (Hc : (sign_extend' 64 (mword_of_int 3414 : mword 12) : mword 64)
                   = mword_of_int (-682))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh P5 e5 (mword_of_int 0x5a6)
              (mword_of_int 3414 : mword 12) a2_idx a2_idx (mword_of_int 4856 : mword 64)
              (ui_sh_5a6 pt P5 Hltext (sh_img_text P5 HgP5))
              ltac:(vm_compute; discriminate) Hw6 with "Hcg Hpc").
    iIntros (CIDa6) "Hcg Hpc".
    set (e6 := <[Regidx a2_idx := regval_into_reg (mword_of_int 4856 : mword 64)]> e5).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5a6 : mword 64) 4
                      = mword_of_int 0x5aa)) in "Hpc".
    assert (Hq6 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              e6 !!! Regidx r = e5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e5 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_6 : e6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq6 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_5).
    assert (Hv_s0_idx_6 : e6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq6 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_5).
    assert (Hv_s4_idx_6 : e6 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq6 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_5).
    assert (Hv_s5_idx_6 : e6 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq6 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_5).
    assert (Hv_a2_idx_6 : e6 !!! Regidx a2_idx = (mword_of_int 4856 : mword 64))
      by exact (upd_eq e5 (Regidx a2_idx) _).
    assert (Hv_a0_idx_6 : e6 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq6 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_5).
    assert (Hv_a1_idx_6 : e6 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq6 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_5).

    (* ---- 0x5aa  jal ra, 0x448 ---- *)
    assert (Ht7 : (mword_of_int 0x448 : mword 64)
                   = add_vec (mword_of_int 0x5aa)
                       (sign_extend' 64 (mword_of_int 2096798 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl7 : (mword_of_int 0x5ae : mword 64)
                   = add_vec_int (mword_of_int 0x5aa : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh P5 e6 (mword_of_int 0x5aa)
              (mword_of_int 2096798 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x5ae)
              (ui_sh_5aa pt P5 Hltext (sh_img_text P5 HgP5))
              ltac:(vm_compute; discriminate) Ht7 Hl7
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDa7) "Hcg Hpc".
    set (e7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x5ae : mword 64)]> e6).
    assert (Hq7 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              e7 !!! Regidx r = e6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e6 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_7 : e7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq7 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_6).
    assert (Hv_s0_idx_7 : e7 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq7 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_6).
    assert (Hv_s4_idx_7 : e7 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq7 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_6).
    assert (Hv_s5_idx_7 : e7 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq7 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_6).
    assert (Hv_a2_idx_7 : e7 !!! Regidx a2_idx = (mword_of_int 4856 : mword 64))
      by (rewrite (Hq7 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_6).
    assert (Hv_a0_idx_7 : e7 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq7 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_6).
    assert (Hv_a1_idx_7 : e7 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq7 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_6).
    assert (Hv_ra_idx_7 : e7 !!! Regidx ra_idx = (mword_of_int 0x5ae : mword 64))
      by exact (upd_eq e6 (Regidx ra_idx) _).
    (* ---- 0x448  peek(ps, es, "(") -- 0, so [parseblock] is unreachable -- *)
    assert (HpreK : sh_parse_pre pt hbase hlen P5 sb bs
                      (mword_of_int (uint sp0 - 128) : mword 64) 80).
    { apply (parse_pre_move M P5 sb bs sp0 (mword_of_int (uint sp0 - 128))
               320 80).
      - exact (proj1 HoP5).
      - intros k Hk. exact (proj2 HoP5 k ltac:(lia)).
      - intros k Hk. exact (proj2 HoP5 k ltac:(lia)).
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hpre. }
    assert (HcellK : sh_ptr_cell pt P5 psaddr (sb + Z.of_nat off)
                       (mword_of_int (uint sp0 - 128) : mword 64)).
    { apply (ptr_cell_move M P5 psaddr (sb + Z.of_nat off) sp0).
      - exact (proj1 HoP5).
      - intros k Hk. exact (proj2 HoP5 k ltac:(lia)).
      - rewrite Huspk. lia.
      - exact Hcell. }
    assert (HstkK : uv_stack pt P5 (mword_of_int (uint sp0 - 128)) 80)
      by exact (stk_dom M P5 _ 80 (proj1 HoP5) Hstpk80).
    assert (Htbhi0 : 4856 + Z.of_nat (length sh_tb_lp) + 1 <= 8192)
      by (rewrite sh_tb_lp_len; lia).
    assert (Htbfr0 : 4856 + Z.of_nat (length sh_tb_lp) + 1
                     <= uint (mword_of_int (uint sp0 - 128) : mword 64) - 80)
      by (rewrite Huspk sh_tb_lp_len; lia).
    assert (Hret2p : is_aligned_vaddr (Virtaddr (e7 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_7; vm_compute; reflexivity).
    iApply (wp_sh_peek_zero CIDa7 P5 e7 (mword_of_int (uint sp0 - 128))
              psaddr sb 4856 bs off sh_tb_lp
              HpreK Hv_csp_rs1_7 HstkK Hv_a0_idx_7 Hv_a1_idx_7 Hv_a2_idx_7
              HcellK Hoff ltac:(lia) Htbhi0 Htbfr0
              sh_tb_lp_data sh_tb_lp_sym Hret2p with "Hcg Hpc [Hcont Hbrk]").
    iIntros (CIDa8 f1 Mq) "%Hcsp %Ha0p %Hcellq %Honlyq Hcg Hpc".
    iEval (rewrite Hv_ra_idx_7) in "Hpc".
    rewrite Huspk in Honlyq.
    assert (Hlowq : forall k : Z, k < uint sp0 - 208 -> Mq !! k = M !! k).
    { intros k Hk.
      rewrite (win2_out P5 Mq psaddr 8 (uint sp0 - 128 - 80) 80 k Honlyq
                 ltac:(lia) ltac:(lia)).
      exact (proj2 HoP5 k ltac:(lia)). }
    assert (Hhighq : forall k : Z,
              uint sp0 - 112 <= k < uint sp0 -> Mq !! k = P5 !! k)
      by (intros k Hk;
          exact (win2_out P5 Mq psaddr 8 (uint sp0 - 128 - 80) 80 k Honlyq
                   ltac:(lia) ltac:(lia))).
    assert (Hdomq : forall k : Z, is_Some (M !! k) -> is_Some (Mq !! k))
      by (intros k Hk; exact (proj1 Honlyq k (proj1 HoP5 k Hk))).
    assert (Hpreq : sh_parse_pre pt hbase hlen Mq sb bs sp0 320).
    { apply (parse_pre_move M Mq sb bs sp0 sp0 320 320).
      - exact Hdomq.
      - intros k Hk. exact (Hlowq k ltac:(lia)).
      - intros k Hk. exact (Hlowq k ltac:(lia)).
      - exact Hfrz.
      - exact Hbufz.
      - exact Hpre. }
    pose proof Hpreq as (_ & Hgq & _ & _ & _ & _ & _ & _).
    assert (Hstq : uv_stack pt Mq sp0 320)
      by exact (stk_dom M Mq sp0 320 Hdomq Hst320).
    assert (Hstq128 : uv_stack pt Mq sp0 128)
      by exact (stk_dom M Mq sp0 128 Hdomq Hst128).
    (* ---- 0x5ae  c.bnez a0,0x5ee -- NOT taken ---- *)
    assert (Htkq : false = neq_vec (f1 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0p. unfold neq_vec.
      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    assert (Htgtq : (mword_of_int 0x5ee : mword 64)
                    = add_vec (mword_of_int 0x5ae)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 32 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cbnez C pt Psh Mq f1 (mword_of_int 0x5ae)
              (mword_of_int 32 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x5ee)
              (ui_sh_5ae pt Mq Hltext (sh_img_text Mq Hgq))
              ltac:(vm_compute; reflexivity) Htkq Htgtq
              ltac:(intro Hx; discriminate) with "Hcg Hpc").
    iIntros (CIDq0) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5ae : mword 64) 2
                      = mword_of_int 0x5b0)) in "Hpc".
    assert (Hv_csp_rs1_8 : f1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hcsp csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_7).
    assert (Hv_s0_idx_8 : f1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcsp s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_7).
    assert (Hv_s4_idx_8 : f1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsp s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_7).
    assert (Hv_s5_idx_8 : f1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcsp s5_idx ltac:(vm_compute; reflexivity)); exact Hv_s5_idx_7).
    (* ---- 0x5b0  c.sdsp s2,96(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq0 Psh Mq f1 sp0 (mword_of_int 0x5b0)
              (mword_of_int 12 : mword 6) s2_idx 128 96
              (ui_sh_5b0 pt Mq Hltext (sh_img_text Mq Hgq)) Hstq128
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5b0 : mword 64) 2
                      = mword_of_int 0x5b2)) in "Hpc".
    set (N1 := uM_store8 Mq (uint sp0 - 128 + 96) (f1 !!! Regidx s2_idx)).
    assert (HoN1 : uM_only Mq N1 (uint sp0 - 128 + 24) 104)
      by (unfold N1; apply only_step8; [ lia | lia | apply uM_only_refl ]).
    assert (HgN1 : sh_img_sub N1)
      by (exact (only_img Mq N1 (uint sp0 - 128 + 24) 104 HoN1 ltac:(lia) Hgq)).
    assert (HkN1 : uv_stack pt N1 sp0 320)
      by (exact (stk_dom Mq N1 sp0 320 (proj1 HoN1) Hstq)).
    assert (HfN1 : uv_stack pt N1 sp0 128)
      by (exact (stk_dom Mq N1 sp0 128 (proj1 HoN1) Hstq128)).

    (* ---- 0x5b2  c.sdsp s3,88(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq1 Psh N1 f1 sp0 (mword_of_int 0x5b2)
              (mword_of_int 11 : mword 6) s3_idx 128 88
              (ui_sh_5b2 pt N1 Hltext (sh_img_text N1 HgN1)) HfN1
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5b2 : mword 64) 2
                      = mword_of_int 0x5b4)) in "Hpc".
    set (N2 := uM_store8 N1 (uint sp0 - 128 + 88) (f1 !!! Regidx s3_idx)).
    assert (HoN2 : uM_only Mq N2 (uint sp0 - 128 + 24) 104)
      by (unfold N2; apply only_step8; [ lia | lia | exact HoN1 ]).
    assert (HgN2 : sh_img_sub N2)
      by (exact (only_img Mq N2 (uint sp0 - 128 + 24) 104 HoN2 ltac:(lia) Hgq)).
    assert (HkN2 : uv_stack pt N2 sp0 320)
      by (exact (stk_dom Mq N2 sp0 320 (proj1 HoN2) Hstq)).
    assert (HfN2 : uv_stack pt N2 sp0 128)
      by (exact (stk_dom Mq N2 sp0 128 (proj1 HoN2) Hstq128)).

    (* ---- 0x5b4  c.sdsp s6,64(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq2 Psh N2 f1 sp0 (mword_of_int 0x5b4)
              (mword_of_int 8 : mword 6) s6_idx 128 64
              (ui_sh_5b4 pt N2 Hltext (sh_img_text N2 HgN2)) HfN2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5b4 : mword 64) 2
                      = mword_of_int 0x5b6)) in "Hpc".
    set (N3 := uM_store8 N2 (uint sp0 - 128 + 64) (f1 !!! Regidx s6_idx)).
    assert (HoN3 : uM_only Mq N3 (uint sp0 - 128 + 24) 104)
      by (unfold N3; apply only_step8; [ lia | lia | exact HoN2 ]).
    assert (HgN3 : sh_img_sub N3)
      by (exact (only_img Mq N3 (uint sp0 - 128 + 24) 104 HoN3 ltac:(lia) Hgq)).
    assert (HkN3 : uv_stack pt N3 sp0 320)
      by (exact (stk_dom Mq N3 sp0 320 (proj1 HoN3) Hstq)).
    assert (HfN3 : uv_stack pt N3 sp0 128)
      by (exact (stk_dom Mq N3 sp0 128 (proj1 HoN3) Hstq128)).

    (* ---- 0x5b6  c.sdsp s7,56(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq3 Psh N3 f1 sp0 (mword_of_int 0x5b6)
              (mword_of_int 7 : mword 6) s7_idx 128 56
              (ui_sh_5b6 pt N3 Hltext (sh_img_text N3 HgN3)) HfN3
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5b6 : mword 64) 2
                      = mword_of_int 0x5b8)) in "Hpc".
    set (N4 := uM_store8 N3 (uint sp0 - 128 + 56) (f1 !!! Regidx s7_idx)).
    assert (HoN4 : uM_only Mq N4 (uint sp0 - 128 + 24) 104)
      by (unfold N4; apply only_step8; [ lia | lia | exact HoN3 ]).
    assert (HgN4 : sh_img_sub N4)
      by (exact (only_img Mq N4 (uint sp0 - 128 + 24) 104 HoN4 ltac:(lia) Hgq)).
    assert (HkN4 : uv_stack pt N4 sp0 320)
      by (exact (stk_dom Mq N4 sp0 320 (proj1 HoN4) Hstq)).
    assert (HfN4 : uv_stack pt N4 sp0 128)
      by (exact (stk_dom Mq N4 sp0 128 (proj1 HoN4) Hstq128)).

    (* ---- 0x5b8  c.sdsp s8,48(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq4 Psh N4 f1 sp0 (mword_of_int 0x5b8)
              (mword_of_int 6 : mword 6) s8_idx 128 48
              (ui_sh_5b8 pt N4 Hltext (sh_img_text N4 HgN4)) HfN4
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5b8 : mword 64) 2
                      = mword_of_int 0x5ba)) in "Hpc".
    set (N5 := uM_store8 N4 (uint sp0 - 128 + 48) (f1 !!! Regidx s8_idx)).
    assert (HoN5 : uM_only Mq N5 (uint sp0 - 128 + 24) 104)
      by (unfold N5; apply only_step8; [ lia | lia | exact HoN4 ]).
    assert (HgN5 : sh_img_sub N5)
      by (exact (only_img Mq N5 (uint sp0 - 128 + 24) 104 HoN5 ltac:(lia) Hgq)).
    assert (HkN5 : uv_stack pt N5 sp0 320)
      by (exact (stk_dom Mq N5 sp0 320 (proj1 HoN5) Hstq)).
    assert (HfN5 : uv_stack pt N5 sp0 128)
      by (exact (stk_dom Mq N5 sp0 128 (proj1 HoN5) Hstq128)).

    (* ---- 0x5ba  c.sdsp s9,40(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq5 Psh N5 f1 sp0 (mword_of_int 0x5ba)
              (mword_of_int 5 : mword 6) s9_idx 128 40
              (ui_sh_5ba pt N5 Hltext (sh_img_text N5 HgN5)) HfN5
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5ba : mword 64) 2
                      = mword_of_int 0x5bc)) in "Hpc".
    set (N6 := uM_store8 N5 (uint sp0 - 128 + 40) (f1 !!! Regidx s9_idx)).
    assert (HoN6 : uM_only Mq N6 (uint sp0 - 128 + 24) 104)
      by (unfold N6; apply only_step8; [ lia | lia | exact HoN5 ]).
    assert (HgN6 : sh_img_sub N6)
      by (exact (only_img Mq N6 (uint sp0 - 128 + 24) 104 HoN6 ltac:(lia) Hgq)).
    assert (HkN6 : uv_stack pt N6 sp0 320)
      by (exact (stk_dom Mq N6 sp0 320 (proj1 HoN6) Hstq)).
    assert (HfN6 : uv_stack pt N6 sp0 128)
      by (exact (stk_dom Mq N6 sp0 128 (proj1 HoN6) Hstq128)).

    (* ---- 0x5bc  c.sdsp s10,32(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq6 Psh N6 f1 sp0 (mword_of_int 0x5bc)
              (mword_of_int 4 : mword 6) s10_idx 128 32
              (ui_sh_5bc pt N6 Hltext (sh_img_text N6 HgN6)) HfN6
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq7) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5bc : mword 64) 2
                      = mword_of_int 0x5be)) in "Hpc".
    set (N7 := uM_store8 N6 (uint sp0 - 128 + 32) (f1 !!! Regidx s10_idx)).
    assert (HoN7 : uM_only Mq N7 (uint sp0 - 128 + 24) 104)
      by (unfold N7; apply only_step8; [ lia | lia | exact HoN6 ]).
    assert (HgN7 : sh_img_sub N7)
      by (exact (only_img Mq N7 (uint sp0 - 128 + 24) 104 HoN7 ltac:(lia) Hgq)).
    assert (HkN7 : uv_stack pt N7 sp0 320)
      by (exact (stk_dom Mq N7 sp0 320 (proj1 HoN7) Hstq)).
    assert (HfN7 : uv_stack pt N7 sp0 128)
      by (exact (stk_dom Mq N7 sp0 128 (proj1 HoN7) Hstq128)).

    (* ---- 0x5be  c.sdsp s11,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDq7 Psh N7 f1 sp0 (mword_of_int 0x5be)
              (mword_of_int 3 : mword 6) s11_idx 128 24
              (ui_sh_5be pt N7 Hltext (sh_img_text N7 HgN7)) HfN7
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDq8) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5be : mword 64) 2
                      = mword_of_int 0x5c0)) in "Hpc".
    set (N8 := uM_store8 N7 (uint sp0 - 128 + 24) (f1 !!! Regidx s11_idx)).
    assert (HoN8 : uM_only Mq N8 (uint sp0 - 128 + 24) 104)
      by (unfold N8; apply only_step8; [ lia | lia | exact HoN7 ]).
    assert (HgN8 : sh_img_sub N8)
      by (exact (only_img Mq N8 (uint sp0 - 128 + 24) 104 HoN8 ltac:(lia) Hgq)).
    assert (HkN8 : uv_stack pt N8 sp0 320)
      by (exact (stk_dom Mq N8 sp0 320 (proj1 HoN8) Hstq)).
    assert (HfN8 : uv_stack pt N8 sp0 128)
      by (exact (stk_dom Mq N8 sp0 128 (proj1 HoN8) Hstq128)).
    (* ---- 0x5c0  c.mv ---- *)
    assert (Hw9 : (mword_of_int 0 : mword 64)
                  = add_vec zero_reg (f1 !!! Regidx a0_idx))
      by (rewrite Ha0p moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh N8 f1 (mword_of_int 0x5c0)
              s2_idx a0_idx (mword_of_int 0 : mword 64)
              (ui_sh_5c0 pt N8 Hltext (sh_img_text N8 HgN8))
              ltac:(vm_compute; discriminate) Hw9 with "Hcg Hpc").
    iIntros (CIDa9) "Hcg Hpc".
    set (g1 := <[Regidx s2_idx := regval_into_reg (mword_of_int 0 : mword 64)]> f1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5c0 : mword 64) 2
                      = mword_of_int 0x5c2)) in "Hpc".
    assert (Hq9 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              g1 !!! Regidx r = f1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne f1 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_9 : g1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq9 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_8).
    assert (Hv_s0_idx_9 : g1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq9 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_8).
    assert (Hv_s4_idx_9 : g1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq9 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_8).
    assert (Hv_s5_idx_9 : g1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq9 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_8).
    assert (Hv_s2_idx_9 : g1 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by exact (upd_eq f1 (Regidx s2_idx) _).

    (* ---- 0x5c2  jal ra, 0x1d2 ---- *)
    assert (Ht10 : (mword_of_int 0x1d2 : mword 64)
                   = add_vec (mword_of_int 0x5c2)
                       (sign_extend' 64 (mword_of_int 2096144 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl10 : (mword_of_int 0x5c6 : mword 64)
                   = add_vec_int (mword_of_int 0x5c2 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh N8 g1 (mword_of_int 0x5c2)
              (mword_of_int 2096144 : mword 21) ra_idx
              (mword_of_int 0x1d2) (mword_of_int 0x5c6)
              (ui_sh_5c2 pt N8 Hltext (sh_img_text N8 HgN8))
              ltac:(vm_compute; discriminate) Ht10 Hl10
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDa10) "Hcg Hpc".
    set (g2 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x5c6 : mword 64)]> g1).
    assert (Hq10 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              g2 !!! Regidx r = g1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g1 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_10 : g2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq10 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_9).
    assert (Hv_s0_idx_10 : g2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq10 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_9).
    assert (Hv_s4_idx_10 : g2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq10 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_9).
    assert (Hv_s5_idx_10 : g2 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq10 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_9).
    assert (Hv_ra_idx_10 : g2 !!! Regidx ra_idx = (mword_of_int 0x5c6 : mword 64))
      by exact (upd_eq g1 (Regidx ra_idx) _).
    assert (Hv_s2_idx_10 : g2 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq10 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_9).
    (* ---- 0x1d2  execcmd() -- malloc(168), memset, type := EXEC ---- *)
    assert (HlowN : forall k : Z, k < uint sp0 - 208 -> N8 !! k = M !! k).
    { intros k Hk. rewrite (proj2 HoN8 k ltac:(lia)).
      exact (Hlowq k ltac:(lia)). }
    assert (HdomN : forall k : Z, is_Some (M !! k) -> is_Some (N8 !! k))
      by (intros k Hk; exact (proj1 HoN8 k (Hdomq k Hk))).
    assert (Hfp8 : sh_zeroed N8 SH_FREEP 0 8).
    { intros j Hj. rewrite (HlowN (SH_FREEP + j)
        ltac:(unfold SH_FREEP, SH_DATA_PG; lia)). exact (Hfreep0 j Hj). }
    assert (Hbs8 : sh_zeroed N8 (SH_BASE + 8) 0 8).
    { intros j Hj. rewrite (HlowN (SH_BASE + 8 + j)
        ltac:(unfold SH_BASE, SH_DATA_PG; lia)). exact (Hbasesz0 j Hj). }
    assert (Hbssw8 : uv_wr pt N8 SH_FREEP 0x88)
      by exact (uv_wr_dom pt M N8 SH_FREEP 0x88 HdomN Hbssw).
    assert (HstN128 : uv_stack pt N8 (mword_of_int (uint sp0 - 128)) 128)
      by exact (stk_dom M N8 _ 128 HdomN Hstpk128).
    assert (Hret2e : is_aligned_vaddr (Virtaddr (g2 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_10; vm_compute; reflexivity).
    iApply (wp_sh_execcmd C pt gin gbrk hbase hlen Q CIDa10 N8 g2
              (mword_of_int (uint sp0 - 128))
              Hlay (sh_img_text N8 HgN8) Hv_csp_rs1_10 HstN128
              Hfp8 Hbs8 Hbssw8
              ltac:(unfold sh_frame_ok; rewrite Huspk; lia) Hret2e
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CIDa11 h1 Me cmd) "%Hcse %Ha0e %Hcmdv %Htype0 %Hzer0 %Hwrnd0
                                %Honlye Hbrk Hcg Hpc".
    iEval (rewrite Hv_ra_idx_10) in "Hpc".
    assert (Hv_csp_rs1_11 : h1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hcse csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_10).
    assert (Hv_s0_idx_11 : h1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcse s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_10).
    assert (Hv_s4_idx_11 : h1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcse s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_10).
    assert (Hv_s5_idx_11 : h1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcse s5_idx ltac:(vm_compute; reflexivity)); exact Hv_s5_idx_10).
    assert (Hv_s2_idx_11 : h1 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hcse s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_10).
    rewrite Huspk in Honlye.
    assert (Hnun : sh_nunits SH_EXECCMD_SZ = 12)
      by (unfold sh_nunits, SH_EXECCMD_SZ; vm_compute; reflexivity).
    assert (Hcmdz : cmd = hbase + 65360) by (rewrite Hcmdv Hnun; lia).
    assert (Hcmd16 : cmd mod 16 = 0).
    { assert (Hz : cmd = 16 * (256 * (hbase / 4096) + 4085)) by lia.
      rewrite Hz Z.mul_comm. apply Z_mod_mult. }
    assert (Hlowe : forall k : Z, k < 8208 -> Me !! k = M !! k).
    { intros k Hk.
      rewrite (win5_out N8 Me hbase 65536 SH_FREEP 8 SH_BASE 16 cmd 168
                 (uint sp0 - 128 - 128) 128 k Honlye
                 ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                 ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia) ltac:(lia)).
      exact (HlowN k ltac:(lia)). }
    assert (Hbufe : forall k : Z,
              sb <= k < sb + Z.of_nat (length bs) + 1 -> Me !! k = M !! k).
    { intros k Hk.
      rewrite (win5_out N8 Me hbase 65536 SH_FREEP 8 SH_BASE 16 cmd 168
                 (uint sp0 - 128 - 128) 128 k Honlye
                 ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                 ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia) ltac:(lia)).
      exact (HlowN k ltac:(lia)). }
    assert (Hdome : forall k : Z, is_Some (M !! k) -> is_Some (Me !! k))
      by (intros k Hk; exact (proj1 Honlye k (HdomN k Hk))).
    assert (Hpree : sh_parse_pre pt hbase hlen Me sb bs sp0 320).
    { apply (parse_pre_move M Me sb bs sp0 sp0 320 320).
      - exact Hdome.
      - exact Hlowe.
      - exact Hbufe.
      - exact Hfrz.
      - exact Hbufz.
      - exact Hpre. }
    pose proof Hpree as (_ & Hge & _ & _ & _ & _ & _ & _).
    assert (Hste : uv_stack pt Me sp0 320)
      by exact (stk_dom M Me sp0 320 Hdome Hst320).
    assert (Hhighe : forall k : Z,
              uint sp0 - 112 <= k < uint sp0 -> Me !! k = N8 !! k)
      by (intros k Hk;
          exact (win5_out N8 Me hbase 65536 SH_FREEP 8 SH_BASE 16 cmd 168
                   (uint sp0 - 128 - 128) 128 k Honlye
                   ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                   ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia)
                   ltac:(lia))).
    (* ---- 0x5c6  c.mv ---- *)
    assert (Hw12 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (h1 !!! Regidx a0_idx))
      by (rewrite Ha0e moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Me h1 (mword_of_int 0x5c6)
              s3_idx a0_idx (mword_of_int cmd : mword 64)
              (ui_sh_5c6 pt Me Hltext (sh_img_text Me Hge))
              ltac:(vm_compute; discriminate) Hw12 with "Hcg Hpc").
    iIntros (CIDa12) "Hcg Hpc".
    set (h2 := <[Regidx s3_idx := regval_into_reg (mword_of_int cmd : mword 64)]> h1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5c6 : mword 64) 2
                      = mword_of_int 0x5c8)) in "Hpc".
    assert (Hq12 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              h2 !!! Regidx r = h1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne h1 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_12 : h2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq12 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_11).
    assert (Hv_s0_idx_12 : h2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq12 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_11).
    assert (Hv_s4_idx_12 : h2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq12 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_11).
    assert (Hv_s5_idx_12 : h2 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq12 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_11).
    assert (Hv_a0_idx_12 : h2 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq12 a0_idx ltac:(vm_compute; discriminate)); exact Ha0e).
    assert (Hv_s2_idx_12 : h2 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq12 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_11).
    assert (Hv_s3_idx_12 : h2 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq h1 (Regidx s3_idx) _).

    (* ---- 0x5c8  c.mv ---- *)
    assert (Hw13 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (h2 !!! Regidx a0_idx))
      by (rewrite Hv_a0_idx_12 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Me h2 (mword_of_int 0x5c8)
              s11_idx a0_idx (mword_of_int cmd : mword 64)
              (ui_sh_5c8 pt Me Hltext (sh_img_text Me Hge))
              ltac:(vm_compute; discriminate) Hw13 with "Hcg Hpc").
    iIntros (CIDa13) "Hcg Hpc".
    set (h3 := <[Regidx s11_idx := regval_into_reg (mword_of_int cmd : mword 64)]> h2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5c8 : mword 64) 2
                      = mword_of_int 0x5ca)) in "Hpc".
    assert (Hq13 : forall r : mword 5, Regidx r <> Regidx s11_idx ->
              h3 !!! Regidx r = h2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne h2 (Regidx s11_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_13 : h3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq13 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_12).
    assert (Hv_s0_idx_13 : h3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq13 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_12).
    assert (Hv_s4_idx_13 : h3 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_12).
    assert (Hv_s5_idx_13 : h3 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq13 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_12).
    assert (Hv_a0_idx_13 : h3 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq13 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_12).
    assert (Hv_s2_idx_13 : h3 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq13 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_12).
    assert (Hv_s3_idx_13 : h3 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq13 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_12).
    assert (Hv_s11_idx_13 : h3 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq h2 (Regidx s11_idx) _).

    (* ---- 0x5ca  c.mv ---- *)
    assert (Hw14 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (h3 !!! Regidx s5_idx))
      by (rewrite Hv_s5_idx_13 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Me h3 (mword_of_int 0x5ca)
              a2_idx s5_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_5ca pt Me Hltext (sh_img_text Me Hge))
              ltac:(vm_compute; discriminate) Hw14 with "Hcg Hpc").
    iIntros (CIDa14) "Hcg Hpc".
    set (h4 := <[Regidx a2_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> h3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5ca : mword 64) 2
                      = mword_of_int 0x5cc)) in "Hpc".
    assert (Hq14 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              h4 !!! Regidx r = h3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne h3 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_14 : h4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq14 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_13).
    assert (Hv_s0_idx_14 : h4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq14 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_13).
    assert (Hv_s4_idx_14 : h4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq14 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_13).
    assert (Hv_s5_idx_14 : h4 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq14 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_13).
    assert (Hv_a2_idx_14 : h4 !!! Regidx a2_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq h3 (Regidx a2_idx) _).
    assert (Hv_a0_idx_14 : h4 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq14 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_13).
    assert (Hv_s2_idx_14 : h4 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq14 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_13).
    assert (Hv_s3_idx_14 : h4 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq14 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_13).
    assert (Hv_s11_idx_14 : h4 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq14 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_13).

    (* ---- 0x5cc  c.mv ---- *)
    assert (Hw15 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (h4 !!! Regidx s4_idx))
      by (rewrite Hv_s4_idx_14 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Me h4 (mword_of_int 0x5cc)
              a1_idx s4_idx (mword_of_int psaddr : mword 64)
              (ui_sh_5cc pt Me Hltext (sh_img_text Me Hge))
              ltac:(vm_compute; discriminate) Hw15 with "Hcg Hpc").
    iIntros (CIDa15) "Hcg Hpc".
    set (h5 := <[Regidx a1_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> h4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5cc : mword 64) 2
                      = mword_of_int 0x5ce)) in "Hpc".
    assert (Hq15 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              h5 !!! Regidx r = h4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne h4 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_15 : h5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq15 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_14).
    assert (Hv_s0_idx_15 : h5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq15 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_14).
    assert (Hv_s4_idx_15 : h5 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq15 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_14).
    assert (Hv_s5_idx_15 : h5 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq15 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_14).
    assert (Hv_a2_idx_15 : h5 !!! Regidx a2_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq15 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_14).
    assert (Hv_a0_idx_15 : h5 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_14).
    assert (Hv_a1_idx_15 : h5 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq h4 (Regidx a1_idx) _).
    assert (Hv_s2_idx_15 : h5 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq15 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_14).
    assert (Hv_s3_idx_15 : h5 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_14).
    assert (Hv_s11_idx_15 : h5 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_14).

    (* ---- 0x5ce  jal ra, 0x4ac ---- *)
    assert (Ht16 : (mword_of_int 0x4ac : mword 64)
                   = add_vec (mword_of_int 0x5ce)
                       (sign_extend' 64 (mword_of_int 2096862 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl16 : (mword_of_int 0x5d2 : mword 64)
                   = add_vec_int (mword_of_int 0x5ce : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh Me h5 (mword_of_int 0x5ce)
              (mword_of_int 2096862 : mword 21) ra_idx
              (mword_of_int 0x4ac) (mword_of_int 0x5d2)
              (ui_sh_5ce pt Me Hltext (sh_img_text Me Hge))
              ltac:(vm_compute; discriminate) Ht16 Hl16
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDa16) "Hcg Hpc".
    set (h6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x5d2 : mword 64)]> h5).
    assert (Hq16 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              h6 !!! Regidx r = h5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne h5 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_16 : h6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq16 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_15).
    assert (Hv_s0_idx_16 : h6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq16 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_15).
    assert (Hv_s4_idx_16 : h6 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq16 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_15).
    assert (Hv_s5_idx_16 : h6 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq16 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_15).
    assert (Hv_a2_idx_16 : h6 !!! Regidx a2_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq16 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_15).
    assert (Hv_a0_idx_16 : h6 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq16 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_15).
    assert (Hv_a1_idx_16 : h6 !!! Regidx a1_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq16 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_15).
    assert (Hv_ra_idx_16 : h6 !!! Regidx ra_idx = (mword_of_int 0x5d2 : mword 64))
      by exact (upd_eq h5 (Regidx ra_idx) _).
    assert (Hv_s2_idx_16 : h6 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq16 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_15).
    assert (Hv_s3_idx_16 : h6 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq16 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_15).
    assert (Hv_s11_idx_16 : h6 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq16 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_15).
    (* ---- 0x4ac  parseredirs(ret, ps, es) ---- *)
    assert (Hkw0 : (off + sh_skipws (drop off bs) <= length bs)%nat).
    { pose proof (sh_skipws_le (drop off bs)) as Hx.
      rewrite length_drop in Hx. lia. }
    assert (Hcelle : uM_bytes Me psaddr 8
              (mword_of_int (sb + Z.of_nat (off + sh_skipws (drop off bs)))
               : mword 64)).
    { apply (bytes_eq8 N8 Me psaddr).
      - intros k Hk.
        exact (win5_out N8 Me hbase 65536 SH_FREEP 8 SH_BASE 16 cmd 168
                 (uint sp0 - 128 - 128) 128 k Honlye
                 ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                 ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia) ltac:(lia)).
      - apply (bytes_eq8 Mq N8 psaddr); [ | exact Hcellq ].
        intros k Hk. exact (proj2 HoN8 k ltac:(lia)). }
    assert (Hrdpse : uv_rd pt Me psaddr 8)
      by exact (uv_rd_dom pt M Me psaddr 8 Hdome Hcrd).
    assert (Hwrpse : uv_wr pt Me psaddr 8)
      by exact (uv_wr_dom pt M Me psaddr 8 Hdome Hcwr).
    assert (HcellE : sh_ptr_cell pt Me psaddr
                       (sb + Z.of_nat (off + sh_skipws (drop off bs)))
                       (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (mk_ptr_cell Me psaddr
                  (sb + Z.of_nat (off + sh_skipws (drop off bs)))
                  (mword_of_int (uint sp0 - 128))
                  Hcelle Hrdpse Hwrpse Hcal ltac:(rewrite Huspk; lia)
                  ltac:(change (2 ^ 38) with 274877906944; lia)).
    assert (HpreE : sh_parse_pre pt hbase hlen Me sb bs
                      (mword_of_int (uint sp0 - 128) : mword 64) 192).
    { apply (parse_pre_move Me Me sb bs sp0 (mword_of_int (uint sp0 - 128))
               320 192).
      - intros k H; exact H.
      - intros k _; reflexivity.
      - intros k _; reflexivity.
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hpree. }
    assert (HstE : uv_stack pt Me (mword_of_int (uint sp0 - 128)) 192)
      by exact (stk_dom M Me _ 192 Hdome Hst192).
    assert (Hret2r : is_aligned_vaddr (Virtaddr (h6 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_16; vm_compute; reflexivity).
    iApply (wp_sh_parseredirs CIDa16 Me h6 (mword_of_int (uint sp0 - 128))
              cmd psaddr sb bs (off + sh_skipws (drop off bs))%nat
              HpreE Hv_csp_rs1_16 HstE Hv_a0_idx_16 Hv_a1_idx_16 Hv_a2_idx_16
              HcellE Hkw0 Hret2r with "Hcg Hpc [Hcont Hbrk]").
    iIntros (CIDa17 j1 Mr0) "%Hcsr %Ha0r %Hpsr0 %Honlyr Hcg Hpc".
    iEval (rewrite Hv_ra_idx_16) in "Hpc".
    assert (Hv_csp_rs1_17 : j1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_16).
    assert (Hv_s0_idx_17 : j1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcsr s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_16).
    assert (Hv_s4_idx_17 : j1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsr s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_16).
    assert (Hv_s5_idx_17 : j1 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcsr s5_idx ltac:(vm_compute; reflexivity)); exact Hv_s5_idx_16).
    assert (Hv_s2_idx_17 : j1 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hcsr s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_16).
    assert (Hv_s3_idx_17 : j1 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcsr s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_16).
    assert (Hv_s11_idx_17 : j1 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcsr s11_idx ltac:(vm_compute; reflexivity)); exact Hv_s11_idx_16).
    rewrite Huspk in Honlyr.
    rewrite (sh_skipws_drop_idem bs off) Nat.add_0_r in Hpsr0.
    assert (Hlowr : forall k : Z, k < 8208 -> Mr0 !! k = M !! k).
    { intros k Hk.
      rewrite (win2_out Me Mr0 psaddr 8 (uint sp0 - 128 - 192) 192 k Honlyr
                 ltac:(lia) ltac:(lia)).
      exact (Hlowe k Hk). }
    assert (Hbufr : forall k : Z,
              sb <= k < sb + Z.of_nat (length bs) + 1 -> Mr0 !! k = M !! k).
    { intros k Hk.
      rewrite (win2_out Me Mr0 psaddr 8 (uint sp0 - 128 - 192) 192 k Honlyr
                 ltac:(lia) ltac:(lia)).
      exact (Hbufe k Hk). }
    assert (Hdomr : forall k : Z, is_Some (M !! k) -> is_Some (Mr0 !! k))
      by (intros k Hk; exact (proj1 Honlyr k (Hdome k Hk))).
    assert (Hprer : sh_parse_pre pt hbase hlen Mr0 sb bs sp0 320).
    { apply (parse_pre_move M Mr0 sb bs sp0 sp0 320 320).
      - exact Hdomr.
      - exact Hlowr.
      - exact Hbufr.
      - exact Hfrz.
      - exact Hbufz.
      - exact Hpre. }
    pose proof Hprer as (_ & Hgr0 & _ & _ & _ & _ & _ & _).
    assert (Hstr : uv_stack pt Mr0 sp0 320)
      by exact (stk_dom M Mr0 sp0 320 Hdomr Hst320).
    assert (Hhighr : forall k : Z,
              uint sp0 - 112 <= k < uint sp0 -> Mr0 !! k = Me !! k)
      by (intros k Hk;
          exact (win2_out Me Mr0 psaddr 8 (uint sp0 - 128 - 192) 192 k Honlyr
                   ltac:(lia) ltac:(lia))).
    assert (Hnoder : forall k : Z, cmd <= k < cmd + 168 -> Mr0 !! k = Me !! k)
      by (intros k Hk;
          exact (win2_out Me Mr0 psaddr 8 (uint sp0 - 128 - 192) 192 k Honlyr
                   ltac:(lia) ltac:(lia))).
    assert (HtypeR0 : uM_bytes Mr0 cmd 4 (mword_of_int 1 : mword 32))
      by (intros j Hj; rewrite (Hnoder (cmd + Z.of_nat j) ltac:(lia));
          exact (Htype0 j Hj)).
    assert (HwrndR0 : uv_wr pt Mr0 cmd 168)
      by (apply (uv_wr_dom pt Me Mr0 cmd 168);
          [ exact (proj1 Honlyr) | exact Hwrnd0 ]).
    (* ---- 0x5d2  c.mv ---- *)
    assert (Hw18 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (j1 !!! Regidx a0_idx))
      by (rewrite Ha0r moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mr0 j1 (mword_of_int 0x5d2)
              s1_idx a0_idx (mword_of_int cmd : mword 64)
              (ui_sh_5d2 pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw18 with "Hcg Hpc").
    iIntros (CIDa18) "Hcg Hpc".
    set (j2 := <[Regidx s1_idx := regval_into_reg (mword_of_int cmd : mword 64)]> j1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5d2 : mword 64) 2
                      = mword_of_int 0x5d4)) in "Hpc".
    assert (Hq18 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              j2 !!! Regidx r = j1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j1 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_18 : j2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq18 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_17).
    assert (Hv_s0_idx_18 : j2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq18 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_17).
    assert (Hv_s4_idx_18 : j2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq18 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_17).
    assert (Hv_s5_idx_18 : j2 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq18 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_17).
    assert (Hv_s2_idx_18 : j2 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq18 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_17).
    assert (Hv_s3_idx_18 : j2 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq18 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_17).
    assert (Hv_s11_idx_18 : j2 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq18 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_17).
    assert (Hv_s1_idx_18 : j2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq j1 (Regidx s1_idx) _).

    (* ---- 0x5d4  c.addi s3,s3,8 ---- *)
    assert (Hw19 : (mword_of_int (cmd + 8) : mword 64)
                   = add_vec (j2 !!! Regidx s3_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))).
    { rewrite Hv_s3_idx_18.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))
                    : mword 64) = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Psh Mr0 j2 (mword_of_int 0x5d4)
              (mword_of_int 8 : mword 6) s3_idx (mword_of_int (cmd + 8))
              (ui_sh_5d4 pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw19 with "Hcg Hpc").
    iIntros (CIDa19) "Hcg Hpc".
    set (j3 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (cmd + 8) : mword 64)]> j2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5d4 : mword 64) 2
                      = mword_of_int 0x5d6)) in "Hpc".
    assert (Hq19 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              j3 !!! Regidx r = j2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j2 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_19 : j3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq19 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_18).
    assert (Hv_s0_idx_19 : j3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq19 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_18).
    assert (Hv_s4_idx_19 : j3 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq19 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_18).
    assert (Hv_s5_idx_19 : j3 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq19 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_18).
    assert (Hv_s2_idx_19 : j3 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq19 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_18).
    assert (Hv_s3_idx_19 : j3 !!! Regidx s3_idx = (mword_of_int (cmd + 8) : mword 64))
      by exact (upd_eq j2 (Regidx s3_idx) _).
    assert (Hv_s11_idx_19 : j3 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq19 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_18).
    assert (Hv_s1_idx_19 : j3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq19 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_18).

    (* ---- 0x5d6  auipc s6,0x1 ---- *)
    assert (Hw20 : (mword_of_int 5590 : mword 64)
                   = add_vec (mword_of_int 0x5d6) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh Mr0 j3 (mword_of_int 0x5d6)
              (mword_of_int 1 : mword 20) s6_idx (mword_of_int 5590)
              (ui_sh_5d6 pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw20 with "Hcg Hpc").
    iIntros (CIDa20) "Hcg Hpc".
    set (j4 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 5590 : mword 64)]> j3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5d6 : mword 64) 4
                      = mword_of_int 0x5da)) in "Hpc".
    assert (Hq20 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
              j4 !!! Regidx r = j3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j3 (Regidx s6_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_20 : j4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq20 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_19).
    assert (Hv_s0_idx_20 : j4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq20 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_19).
    assert (Hv_s4_idx_20 : j4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq20 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_19).
    assert (Hv_s5_idx_20 : j4 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq20 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_19).
    assert (Hv_s2_idx_20 : j4 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq20 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_19).
    assert (Hv_s3_idx_20 : j4 !!! Regidx s3_idx = (mword_of_int (cmd + 8) : mword 64))
      by (rewrite (Hq20 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_19).
    assert (Hv_s11_idx_20 : j4 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq20 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_19).
    assert (Hv_s1_idx_20 : j4 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq20 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_19).
    assert (Hv_s6_idx_20 : j4 !!! Regidx s6_idx = (mword_of_int 5590 : mword 64))
      by exact (upd_eq j3 (Regidx s6_idx) _).

    (* ---- 0x5da  addi ---- *)
    assert (Hw21 : (mword_of_int 4888 : mword 64)
                  = add_vec (j4 !!! Regidx s6_idx)
                      (sign_extend' 64 (mword_of_int 3394 : mword 12))).
    { rewrite Hv_s6_idx_20.
      assert (Hc : (sign_extend' 64 (mword_of_int 3394 : mword 12) : mword 64)
                   = mword_of_int (-702))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh Mr0 j4 (mword_of_int 0x5da)
              (mword_of_int 3394 : mword 12) s6_idx s6_idx (mword_of_int 4888 : mword 64)
              (ui_sh_5da pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw21 with "Hcg Hpc").
    iIntros (CIDa21) "Hcg Hpc".
    set (j5 := <[Regidx s6_idx := regval_into_reg (mword_of_int 4888 : mword 64)]> j4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5da : mword 64) 4
                      = mword_of_int 0x5de)) in "Hpc".
    assert (Hq21 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
              j5 !!! Regidx r = j4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j4 (Regidx s6_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_21 : j5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq21 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_20).
    assert (Hv_s0_idx_21 : j5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq21 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_20).
    assert (Hv_s4_idx_21 : j5 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq21 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_20).
    assert (Hv_s5_idx_21 : j5 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq21 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_20).
    assert (Hv_s2_idx_21 : j5 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq21 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_20).
    assert (Hv_s3_idx_21 : j5 !!! Regidx s3_idx = (mword_of_int (cmd + 8) : mword 64))
      by (rewrite (Hq21 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_20).
    assert (Hv_s11_idx_21 : j5 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq21 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_20).
    assert (Hv_s1_idx_21 : j5 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq21 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_20).
    assert (Hv_s6_idx_21 : j5 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by exact (upd_eq j4 (Regidx s6_idx) _).

    (* ---- 0x5de  addi ---- *)
    assert (Hw22 : (mword_of_int (uint sp0 - 128) : mword 64)
                  = add_vec (j5 !!! Regidx s0_idx)
                      (sign_extend' 64 (mword_of_int 3968 : mword 12))).
    { rewrite Hv_s0_idx_21.
      assert (Hc : (sign_extend' 64 (mword_of_int 3968 : mword 12) : mword 64)
                   = mword_of_int (-128))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh Mr0 j5 (mword_of_int 0x5de)
              (mword_of_int 3968 : mword 12) s0_idx s8_idx (mword_of_int (uint sp0 - 128) : mword 64)
              (ui_sh_5de pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw22 with "Hcg Hpc").
    iIntros (CIDa22) "Hcg Hpc".
    set (j6 := <[Regidx s8_idx := regval_into_reg (mword_of_int (uint sp0 - 128) : mword 64)]> j5).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5de : mword 64) 4
                      = mword_of_int 0x5e2)) in "Hpc".
    assert (Hq22 : forall r : mword 5, Regidx r <> Regidx s8_idx ->
              j6 !!! Regidx r = j5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j5 (Regidx s8_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_22 : j6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq22 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_21).
    assert (Hv_s0_idx_22 : j6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq22 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_21).
    assert (Hv_s4_idx_22 : j6 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq22 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_21).
    assert (Hv_s5_idx_22 : j6 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq22 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_21).
    assert (Hv_s2_idx_22 : j6 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq22 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_21).
    assert (Hv_s3_idx_22 : j6 !!! Regidx s3_idx = (mword_of_int (cmd + 8) : mword 64))
      by (rewrite (Hq22 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_21).
    assert (Hv_s11_idx_22 : j6 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq22 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_21).
    assert (Hv_s1_idx_22 : j6 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq22 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_21).
    assert (Hv_s6_idx_22 : j6 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq22 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_21).
    assert (Hv_s8_idx_22 : j6 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (upd_eq j5 (Regidx s8_idx) _).

    (* ---- 0x5e2  addi ---- *)
    assert (Hw23 : (mword_of_int (uint sp0 - 120) : mword 64)
                  = add_vec (j6 !!! Regidx s0_idx)
                      (sign_extend' 64 (mword_of_int 3976 : mword 12))).
    { rewrite Hv_s0_idx_22.
      assert (Hc : (sign_extend' 64 (mword_of_int 3976 : mword 12) : mword 64)
                   = mword_of_int (-120))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh Mr0 j6 (mword_of_int 0x5e2)
              (mword_of_int 3976 : mword 12) s0_idx s7_idx (mword_of_int (uint sp0 - 120) : mword 64)
              (ui_sh_5e2 pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw23 with "Hcg Hpc").
    iIntros (CIDa23) "Hcg Hpc".
    set (j7 := <[Regidx s7_idx := regval_into_reg (mword_of_int (uint sp0 - 120) : mword 64)]> j6).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5e2 : mword 64) 4
                      = mword_of_int 0x5e6)) in "Hpc".
    assert (Hq23 : forall r : mword 5, Regidx r <> Regidx s7_idx ->
              j7 !!! Regidx r = j6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j6 (Regidx s7_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_23 : j7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq23 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_22).
    assert (Hv_s0_idx_23 : j7 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq23 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_22).
    assert (Hv_s4_idx_23 : j7 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq23 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_22).
    assert (Hv_s5_idx_23 : j7 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq23 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_22).
    assert (Hv_s2_idx_23 : j7 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq23 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_22).
    assert (Hv_s3_idx_23 : j7 !!! Regidx s3_idx = (mword_of_int (cmd + 8) : mword 64))
      by (rewrite (Hq23 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_22).
    assert (Hv_s11_idx_23 : j7 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq23 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_22).
    assert (Hv_s1_idx_23 : j7 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq23 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_22).
    assert (Hv_s6_idx_23 : j7 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq23 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_22).
    assert (Hv_s7_idx_23 : j7 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by exact (upd_eq j6 (Regidx s7_idx) _).
    assert (Hv_s8_idx_23 : j7 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq23 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_22).

    (* ---- 0x5e6  li s10,97 ---- *)
    assert (Hw24 : (mword_of_int 97 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (mword_of_int 97 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_li C pt Psh Mr0 j7 (mword_of_int 0x5e6)
              (mword_of_int 97 : mword 12) s10_idx (mword_of_int 97)
              (ui_sh_5e6 pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw24 with "Hcg Hpc").
    iIntros (CIDa24) "Hcg Hpc".
    set (j8 := <[Regidx s10_idx
                 := regval_into_reg (mword_of_int 97 : mword 64)]> j7).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5e6 : mword 64) 4
                      = mword_of_int 0x5ea)) in "Hpc".
    assert (Hq24 : forall r : mword 5, Regidx r <> Regidx s10_idx ->
              j8 !!! Regidx r = j7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j7 (Regidx s10_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_24 : j8 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq24 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_23).
    assert (Hv_s0_idx_24 : j8 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq24 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_23).
    assert (Hv_s4_idx_24 : j8 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq24 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_23).
    assert (Hv_s5_idx_24 : j8 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq24 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_23).
    assert (Hv_s2_idx_24 : j8 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq24 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_23).
    assert (Hv_s3_idx_24 : j8 !!! Regidx s3_idx = (mword_of_int (cmd + 8) : mword 64))
      by (rewrite (Hq24 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_23).
    assert (Hv_s11_idx_24 : j8 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq24 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_23).
    assert (Hv_s1_idx_24 : j8 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq24 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_23).
    assert (Hv_s6_idx_24 : j8 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq24 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_23).
    assert (Hv_s7_idx_24 : j8 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq24 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_23).
    assert (Hv_s8_idx_24 : j8 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq24 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_23).
    assert (Hv_s10_idx_24 : j8 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by exact (upd_eq j7 (Regidx s10_idx) _).

    (* ---- 0x5ea  c.li s9,10 ---- *)
    assert (Hw25 : (mword_of_int 10 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 10 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh Mr0 j8 (mword_of_int 0x5ea)
              (mword_of_int 10 : mword 6) s9_idx (mword_of_int 10)
              (ui_sh_5ea pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(vm_compute; discriminate) Hw25 with "Hcg Hpc").
    iIntros (CIDa25) "Hcg Hpc".
    set (j9 := <[Regidx s9_idx
                 := regval_into_reg (mword_of_int 10 : mword 64)]> j8).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5ea : mword 64) 2
                      = mword_of_int 0x5ec)) in "Hpc".
    assert (Hq25 : forall r : mword 5, Regidx r <> Regidx s9_idx ->
              j9 !!! Regidx r = j8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne j8 (Regidx s9_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_25 : j9 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq25 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_24).
    assert (Hv_s0_idx_25 : j9 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq25 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_24).
    assert (Hv_s4_idx_25 : j9 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq25 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_24).
    assert (Hv_s5_idx_25 : j9 !!! Regidx s5_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq25 s5_idx ltac:(vm_compute; discriminate)); exact Hv_s5_idx_24).
    assert (Hv_s2_idx_25 : j9 !!! Regidx s2_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hq25 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_24).
    assert (Hv_s3_idx_25 : j9 !!! Regidx s3_idx = (mword_of_int (cmd + 8) : mword 64))
      by (rewrite (Hq25 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_24).
    assert (Hv_s11_idx_25 : j9 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq25 s11_idx ltac:(vm_compute; discriminate)); exact Hv_s11_idx_24).
    assert (Hv_s1_idx_25 : j9 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq25 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_24).
    assert (Hv_s6_idx_25 : j9 !!! Regidx s6_idx = (mword_of_int 4888 : mword 64))
      by (rewrite (Hq25 s6_idx ltac:(vm_compute; discriminate)); exact Hv_s6_idx_24).
    assert (Hv_s7_idx_25 : j9 !!! Regidx s7_idx = (mword_of_int (uint sp0 - 120) : mword 64))
      by (rewrite (Hq25 s7_idx ltac:(vm_compute; discriminate)); exact Hv_s7_idx_24).
    assert (Hv_s8_idx_25 : j9 !!! Regidx s8_idx = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (Hq25 s8_idx ltac:(vm_compute; discriminate)); exact Hv_s8_idx_24).
    assert (Hv_s9_idx_25 : j9 !!! Regidx s9_idx = (mword_of_int 10 : mword 64))
      by exact (upd_eq j8 (Regidx s9_idx) _).
    assert (Hv_s10_idx_25 : j9 !!! Regidx s10_idx = (mword_of_int 97 : mword 64))
      by (rewrite (Hq25 s10_idx ltac:(vm_compute; discriminate)); exact Hv_s10_idx_24).

    (* ---- 0x5ec  c.j 0x622 ---- *)
    iApply (wp_uv_cj C pt Psh Mr0 j9 (mword_of_int 0x5ec)
              (mword_of_int 27 : mword 11) (mword_of_int 0x622)
              (ui_sh_5ec pt Mr0 Hltext (sh_img_text Mr0 Hgr0))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDaj) "Hcg Hpc".
    (* ---- 0x622..0x620  the argument loop (§3d) ---- *)
    assert (Hpres8 : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s4_idx -> Regidx r <> Regidx s5_idx ->
              f1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Dsp D0 D4 D5.
      assert (Dra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (Hcsp r Hr) (Hq7 r Dra) (Hq6 r Da2) (Hq5 r Da2) (Hq4 r D5)
              (Hq3 r D4) (Hq2 r D0).
      exact (Hq1 r Dsp). }
    assert (HpresA : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s6_idx ->
              Regidx r <> Regidx s7_idx -> Regidx r <> Regidx s8_idx ->
              Regidx r <> Regidx s9_idx -> Regidx r <> Regidx s10_idx ->
              Regidx r <> Regidx s11_idx ->
              j9 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Dsp D0 D1 D2 D3 D4 D5 D6 D7 N8' D9 D10 D11.
      assert (Dra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (Hq25 r D9) (Hq24 r D10) (Hq23 r D7) (Hq22 r N8') (Hq21 r D6)
              (Hq20 r D6) (Hq19 r D3) (Hq18 r D1) (Hcsr r Hr) (Hq16 r Dra)
              (Hq15 r Da1) (Hq14 r Da2) (Hq13 r D11) (Hq12 r D3)
              (Hcse r Hr) (Hq10 r Dra) (Hq9 r D2).
      exact (Hpres8 r Hr Dsp D0 D4 D5). }
    assert (HWid : uM_only_in Mr0 Mr0
                     [(hbase, 65536); (psaddr, 8); (uint sp0 - 320, 208)]).
    { apply (win3_in Mr0 Mr0 hbase 65536 psaddr 8 (uint sp0 - 320) 208).
      - intros k H; exact H.
      - intros k _ _ _; reflexivity. }
    assert (Hargnil : forall (j : nat) (t : nat * nat),
              take 0 toks !! j = Some t ->
              uM_bytes Mr0 (cmd + 8 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (fst t)) : mword 64) /\
              uM_bytes Mr0 (cmd + 88 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (snd t)) : mword 64))
      by (intros j t Hj; cbn [take] in Hj; destruct j; discriminate).
    assert (Hs3L0 : j9 !!! Regidx s3_idx
                    = (mword_of_int (cmd + 8 + 8 * Z.of_nat 0%nat) : mword 64))
      by (replace (cmd + 8 + 8 * Z.of_nat 0%nat) with (cmd + 8) by lia;
          exact Hv_s3_idx_25).
    assert (Hs2L0 : j9 !!! Regidx s2_idx
                    = (mword_of_int (Z.of_nat 0%nat) : mword 64))
      by (replace (Z.of_nat 0%nat) with 0 by lia; exact Hv_s2_idx_25).
    iApply (wp_sh_pe_loop (S (length toks)) CIDaj Mr0 Mr0 j9 sp0 psaddr sb cmd
              bs (off + sh_skipws (drop off bs))%nat 0%nat toks toks
              ltac:(lia) Hprer Hbufc Hstr ltac:(lia) (eq_sym (drop_0 toks))
              (sh_tokens_shift bs off toks Htoks) Hmax Hkw0
              ltac:(lia) ltac:(lia) Hcmd16 Hclo Hchi Hcal
              (uv_rd_dom pt M Mr0 psaddr 8 Hdomr Hcrd)
              (uv_wr_dom pt M Mr0 psaddr 8 Hdomr Hcwr) HwrndR0
              HWid Hpsr0 HtypeR0 Hargnil
              Hv_csp_rs1_25 Hv_s0_idx_25 Hv_s1_idx_25 Hs2L0 Hs3L0
              Hv_s4_idx_25 Hv_s5_idx_25 Hv_s6_idx_25 Hv_s7_idx_25
              Hv_s8_idx_25 Hv_s9_idx_25 Hv_s10_idx_25 Hv_s11_idx_25
              with "Hcg Hpc [Hcont Hbrk]").
    iIntros (CIDL mL ML) "%HWL %HtypeL %HargL %HcellL %Hs1L %Hs2L %HpresL Hcg Hpc".
    (* ================= the exit path, 0x662 .. 0x606 ================= *)
    assert (Hdoml : forall k : Z, is_Some (M !! k) -> is_Some (ML !! k)).
    { intros k Hk. apply (proj1 HWL). apply (proj1 Honlyr). apply (proj1 Honlye).
      apply (proj1 HoN8). apply (proj1 Honlyq). exact (proj1 HoP5 k Hk). }
    assert (Hprel : sh_parse_pre pt hbase hlen ML sb bs sp0 320)
      by exact (pe_w3_pre Mr0 ML sb psaddr bs sp0 HWL Hbufc Hclo Hprer).
    pose proof Hprel as (_ & Hgl & _ & _ & _ & _ & _ & _).
    assert (Hstl : uv_stack pt ML sp0 320)
      by exact (stk_dom M ML sp0 320 Hdoml Hst320).
    assert (Hstl128 : uv_stack pt ML sp0 128)
      by exact (stk_dom M ML sp0 128 Hdoml Hst128).
    assert (Hwrndl : uv_wr pt ML cmd 168)
      by (apply (uv_wr_dom pt Mr0 ML cmd 168);
          [ exact (proj1 HWL) | exact HwrndR0 ]).
    assert (Hlenlt : Z.of_nat (length toks) < 10) by lia.
    assert (Hspl : mL !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 128) : mword 64))
      by (rewrite (HpresL csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate));
          exact Hv_csp_rs1_25).
    assert (Hs11L : mL !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by (rewrite (HpresL s11_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate));
          exact Hv_s11_idx_25).
    (* ---- 0x662  c.slli s2,s2,0x3 ---- *)
    assert (Hwsl : (mword_of_int (8 * Z.of_nat (length toks)) : mword 64)
                   = shift_bits_left (mL !!! Regidx s2_idx)
                       (subrange_vec_dec (mword_of_int 3 : mword 6)
                          (Z.sub log2_xlen 1) 0)).
    { rewrite Hs2L (moi_shl (Z.of_nat (length toks)) 3 ltac:(lia)).
      change (2 ^ 3) with 8. f_equal. lia. }
    iApply (wp_uv_cslli C pt Psh ML mL (mword_of_int 0x662)
              (mword_of_int 3 : mword 6) s2_idx
              (mword_of_int (8 * Z.of_nat (length toks)))
              (ui_sh_662 pt ML Hltext (sh_img_text ML Hgl))
              ltac:(vm_compute; discriminate) Hwsl with "Hcg Hpc").
    iIntros (CIDc0) "Hcg Hpc".
    set (c1 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (8 * Z.of_nat (length toks)) : mword 64)]> mL).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x662 : mword 64) 2
                      = mword_of_int 0x664)) in "Hpc".
    assert (Hspc1 : c1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne mL (Regidx s2_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hspl).
    assert (Hs11c1 : c1 !!! Regidx s11_idx = (mword_of_int cmd : mword 64))
      by exact (eq_trans (upd_ne mL (Regidx s2_idx) (Regidx s11_idx) _
                            ltac:(vm_compute; discriminate)) Hs11L).
    assert (Hs2c1 : c1 !!! Regidx s2_idx
                    = (mword_of_int (8 * Z.of_nat (length toks)) : mword 64))
      by exact (upd_eq mL (Regidx s2_idx) _).
    assert (Hs1c1 : c1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by exact (eq_trans (upd_ne mL (Regidx s2_idx) (Regidx s1_idx) _
                            ltac:(vm_compute; discriminate)) Hs1L).
    (* ---- 0x664  add a5,s11,s2 ---- *)
    assert (Hwadd : (mword_of_int (cmd + 8 * Z.of_nat (length toks)) : mword 64)
                    = add_vec (c1 !!! Regidx s11_idx) (c1 !!! Regidx s2_idx)).
    { rewrite Hs11c1 Hs2c1 moi_add. reflexivity. }
    iApply (wp_uv_add C pt Psh ML c1 (mword_of_int 0x664)
              s11_idx s2_idx a5_idx
              (mword_of_int (cmd + 8 * Z.of_nat (length toks)))
              (ui_sh_664 pt ML Hltext (sh_img_text ML Hgl))
              ltac:(vm_compute; discriminate) Hwadd with "Hcg Hpc").
    iIntros (CIDc1) "Hcg Hpc".
    set (c2 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (cmd + 8 * Z.of_nat (length toks))
                       : mword 64)]> c1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x664 : mword 64) 4
                      = mword_of_int 0x668)) in "Hpc".
    assert (Hspc2 : c2 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne c1 (Regidx a5_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hspc1).
    assert (Ha5c2 : c2 !!! Regidx a5_idx
                    = (mword_of_int (cmd + 8 * Z.of_nat (length toks))
                       : mword 64))
      by exact (upd_eq c1 (Regidx a5_idx) _).
    assert (Hs1c2 : c2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by exact (eq_trans (upd_ne c1 (Regidx a5_idx) (Regidx s1_idx) _
                            ltac:(vm_compute; discriminate)) Hs1c1).
    (* the machine's x0, for the two [sd zero] ---- *)
    iDestruct "Hcg" as "(Hcap & Hlin & Hgpr)".
    iDestruct (gpr_file_x0 c2 (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hgpr") as "[%Hzx Hgpr]".
    iAssert (uv_cap_gpr C pt Psh ML c2) with "[Hcap Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    assert (Hz0 : (mword_of_int 0 : mword 64) = c2 !!! Regidx (mword_of_int 0))
      by (rewrite Hzx; apply bv_eq; vm_compute; reflexivity).
    assert (Hmod8c : forall z : Z, (cmd + 8 * z) mod 8 = 0).
    { intro z.
      assert (Hz : cmd + 8 * z = 8 * (2 * (cmd / 16) + z))
        by (pose proof (Z.div_mod cmd 16 ltac:(lia)); lia).
      rewrite Hz Z.mul_comm. apply Z_mod_mult. }
    (* ---- 0x668  sd zero,8(a5)  -- argv[argc] := 0 ---- *)
    assert (Hva5 : (mword_of_int (cmd + 8 + 8 * Z.of_nat (length toks))
                    : mword 64)
                   = add_vec (c2 !!! Regidx a5_idx)
                       (sign_extend' 64 (mword_of_int 8 : mword 12))).
    { rewrite Ha5c2.
      assert (Hc : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                   = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    assert (Hnda : (cmd + 8 + 8 * Z.of_nat (length toks)) mod 8 = 0)
      by (replace (cmd + 8 + 8 * Z.of_nat (length toks))
            with (cmd + 8 * (1 + Z.of_nat (length toks))) by lia;
          apply Hmod8c).
    destruct (uv_slot8_facts (cmd + 8 + 8 * Z.of_nat (length toks))
                (mword_of_int (cmd + 8 + 8 * Z.of_nat (length toks)))
                ltac:(lia) Hnda
                ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
      as (Hua & Hcna & Hpga & Hala).
    destruct (node_leaf ML cmd (cmd + 8 + 8 * Z.of_nat (length toks)) Hwrndl
                ltac:(lia) ltac:(lia)) as (wa & Hwa & Hwas).
    iApply (wp_uv_sd C pt Psh ML c2 (mword_of_int 0x668)
              (mword_of_int 8 : mword 12) a5_idx (mword_of_int 0 : mword 5)
              wa (mword_of_int (cmd + 8 + 8 * Z.of_nat (length toks)))
              (mword_of_int 0)
              (ui_sh_668 pt ML Hltext (sh_img_text ML Hgl))
              Hva5 Hz0 Hwa Hwas Hcna Hpga Hala
              ltac:(rewrite Hua;
                    exact (node_bytes ML cmd
                             (cmd + 8 + 8 * Z.of_nat (length toks)) Hwrndl
                             ltac:(lia) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CIDc2) "Hcg Hpc".
    iEval (rewrite Hua) in "Hcg".
    set (MC1 := uM_store8 ML (cmd + 8 + 8 * Z.of_nat (length toks))
                  (mword_of_int 0 : mword 64)).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x668 : mword 64) 4
                      = mword_of_int 0x66c)) in "Hpc".
    assert (HgC1 : sh_img_sub MC1)
      by (unfold MC1; apply img_store8; [ exact Hgl | lia ]).
    assert (Hwrndc1 : uv_wr pt MC1 cmd 168).
    { apply (uv_wr_dom pt ML MC1 cmd 168); [ | exact Hwrndl ].
      intros kk Hk. unfold MC1. apply uM_store8_is_Some. exact Hk. }
    (* ---- 0x66c  sd zero,88(a5)  -- eargv[argc] := 0 ---- *)
    assert (Hvb5 : (mword_of_int (cmd + 88 + 8 * Z.of_nat (length toks))
                    : mword 64)
                   = add_vec (c2 !!! Regidx a5_idx)
                       (sign_extend' 64 (mword_of_int 88 : mword 12))).
    { rewrite Ha5c2.
      assert (Hc : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
                   = mword_of_int 88)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    assert (Hndb : (cmd + 88 + 8 * Z.of_nat (length toks)) mod 8 = 0)
      by (replace (cmd + 88 + 8 * Z.of_nat (length toks))
            with (cmd + 8 * (11 + Z.of_nat (length toks))) by lia;
          apply Hmod8c).
    destruct (uv_slot8_facts (cmd + 88 + 8 * Z.of_nat (length toks))
                (mword_of_int (cmd + 88 + 8 * Z.of_nat (length toks)))
                ltac:(lia) Hndb
                ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
      as (Hub & Hcnb & Hpgb & Halb).
    destruct (node_leaf MC1 cmd (cmd + 88 + 8 * Z.of_nat (length toks)) Hwrndc1
                ltac:(lia) ltac:(lia)) as (wb & Hwb & Hwbs).
    iApply (wp_uv_sd C pt Psh MC1 c2 (mword_of_int 0x66c)
              (mword_of_int 88 : mword 12) a5_idx (mword_of_int 0 : mword 5)
              wb (mword_of_int (cmd + 88 + 8 * Z.of_nat (length toks)))
              (mword_of_int 0)
              (ui_sh_66c pt MC1 Hltext (sh_img_text MC1 HgC1))
              Hvb5 Hz0 Hwb Hwbs Hcnb Hpgb Halb
              ltac:(rewrite Hub;
                    exact (node_bytes MC1 cmd
                             (cmd + 88 + 8 * Z.of_nat (length toks)) Hwrndc1
                             ltac:(lia) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CIDr0) "Hcg Hpc".
    iEval (rewrite Hub) in "Hcg".
    set (MC2 := uM_store8 MC1 (cmd + 88 + 8 * Z.of_nat (length toks))
                  (mword_of_int 0 : mword 64)).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x66c : mword 64) 4
                      = mword_of_int 0x670)) in "Hpc".
    assert (HgC2 : sh_img_sub MC2)
      by (unfold MC2; apply img_store8; [ exact HgC1 | lia ]).
    assert (Hwrndc2 : uv_wr pt MC2 cmd 168).
    { apply (uv_wr_dom pt MC1 MC2 cmd 168); [ | exact Hwrndc1 ].
      intros kk Hk. unfold MC2. apply uM_store8_is_Some. exact Hk. }
    assert (HdomC : forall k : Z, is_Some (M !! k) -> is_Some (MC2 !! k)).
    { intros k Hk. unfold MC2. apply uM_store8_is_Some.
      unfold MC1. apply uM_store8_is_Some. exact (Hdoml k Hk). }
    assert (HfC2 : uv_stack pt MC2 sp0 128)
      by exact (stk_dom M MC2 sp0 128 HdomC Hst128).
    assert (HhiC : forall k : Z,
              uint sp0 - 112 <= k < uint sp0 -> MC2 !! k = N8 !! k).
    { intros k Hk.
      unfold MC2.
      rewrite (um8_ne MC1 (cmd + 88 + 8 * Z.of_nat (length toks)) _ k
                 ltac:(lia)).
      unfold MC1.
      rewrite (um8_ne ML (cmd + 8 + 8 * Z.of_nat (length toks)) _ k
                 ltac:(lia)).
      rewrite (win3_out Mr0 ML hbase 65536 psaddr 8 (uint sp0 - 320) 208 k HWL
                 ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (Hhighr k ltac:(lia)). exact (Hhighe k ltac:(lia)). }
    assert (HbCra : uM_bytes MC2 (uint sp0 - 128 + 120) 8 (e1 !!! Regidx ra_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 120));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]).
      apply (bytes_eq8 P5 Mq (uint sp0 - 128 + 120));
        [ intros k Hk; apply Hhighq; lia | ].
      unfold P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs0 : uM_bytes MC2 (uint sp0 - 128 + 112) 8 (e1 !!! Regidx s0_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 112));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]).
      apply (bytes_eq8 P5 Mq (uint sp0 - 128 + 112));
        [ intros k Hk; apply Hhighq; lia | ].
      unfold P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs1 : uM_bytes MC2 (uint sp0 - 128 + 104) 8 (e1 !!! Regidx s1_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 104));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]).
      apply (bytes_eq8 P5 Mq (uint sp0 - 128 + 104));
        [ intros k Hk; apply Hhighq; lia | ].
      unfold P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs4 : uM_bytes MC2 (uint sp0 - 128 + 80) 8 (e1 !!! Regidx s4_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 80));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]).
      apply (bytes_eq8 P5 Mq (uint sp0 - 128 + 80));
        [ intros k Hk; apply Hhighq; lia | ].
      unfold P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs5 : uM_bytes MC2 (uint sp0 - 128 + 72) 8 (e1 !!! Regidx s5_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 72));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]).
      apply (bytes_eq8 P5 Mq (uint sp0 - 128 + 72));
        [ intros k Hk; apply Hhighq; lia | ].
      unfold P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs2 : uM_bytes MC2 (uint sp0 - 128 + 96) 8 (f1 !!! Regidx s2_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 96));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs3 : uM_bytes MC2 (uint sp0 - 128 + 88) 8 (f1 !!! Regidx s3_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 88));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs6 : uM_bytes MC2 (uint sp0 - 128 + 64) 8 (f1 !!! Regidx s6_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 64));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs7 : uM_bytes MC2 (uint sp0 - 128 + 56) 8 (f1 !!! Regidx s7_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 56));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs8 : uM_bytes MC2 (uint sp0 - 128 + 48) 8 (f1 !!! Regidx s8_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 48));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs9 : uM_bytes MC2 (uint sp0 - 128 + 40) 8 (f1 !!! Regidx s9_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 40));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs10 : uM_bytes MC2 (uint sp0 - 128 + 32) 8 (f1 !!! Regidx s10_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 32));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs11 : uM_bytes MC2 (uint sp0 - 128 + 24) 8 (f1 !!! Regidx s11_idx)).
    { apply (bytes_eq8 N8 MC2 (uint sp0 - 128 + 24));
        [ intros k Hk; apply HhiC; lia | ].
      unfold N8, N7, N6, N5, N4, N3, N2, N1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    (* ---- 0x670  c.ldsp s2,96(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr0 Psh MC2 c2 sp0 (mword_of_int 0x670)
              (mword_of_int 12 : mword 6) s2_idx 128 96 (f1 !!! Regidx s2_idx)
              (ui_sh_670 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hspc2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 96)
                        (f1 !!! Regidx s2_idx) HbCs2))
              with "Hcg Hpc").
    iIntros (CIDr1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x670 : mword 64) 2
                      = mword_of_int 0x672)) in "Hpc".
    set (R1 := <[Regidx s2_idx := regval_into_reg (f1 !!! Regidx s2_idx)]> c2).
    assert (HspR1 : R1 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne c2 (Regidx s2_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) Hspc2).
    assert (Hvs21 : R1 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (upd_eq c2 (Regidx s2_idx) _).

    (* ---- 0x672  c.ldsp s3,88(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr1 Psh MC2 R1 sp0 (mword_of_int 0x672)
              (mword_of_int 11 : mword 6) s3_idx 128 88 (f1 !!! Regidx s3_idx)
              (ui_sh_672 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 88)
                        (f1 !!! Regidx s3_idx) HbCs3))
              with "Hcg Hpc").
    iIntros (CIDr2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x672 : mword 64) 2
                      = mword_of_int 0x674)) in "Hpc".
    set (R2 := <[Regidx s3_idx := regval_into_reg (f1 !!! Regidx s3_idx)]> R1).
    assert (HspR2 : R2 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R1 (Regidx s3_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR1).
    assert (Hvs32 : R2 !!! Regidx s3_idx = f1 !!! Regidx s3_idx)
      by exact (upd_eq R1 (Regidx s3_idx) _).
    assert (Hvs22 : R2 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R1 (Regidx s3_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs21).

    (* ---- 0x674  c.ldsp s6,64(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr2 Psh MC2 R2 sp0 (mword_of_int 0x674)
              (mword_of_int 8 : mword 6) s6_idx 128 64 (f1 !!! Regidx s6_idx)
              (ui_sh_674 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 64)
                        (f1 !!! Regidx s6_idx) HbCs6))
              with "Hcg Hpc").
    iIntros (CIDr3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x674 : mword 64) 2
                      = mword_of_int 0x676)) in "Hpc".
    set (R3 := <[Regidx s6_idx := regval_into_reg (f1 !!! Regidx s6_idx)]> R2).
    assert (HspR3 : R3 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R2 (Regidx s6_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR2).
    assert (Hvs63 : R3 !!! Regidx s6_idx = f1 !!! Regidx s6_idx)
      by exact (upd_eq R2 (Regidx s6_idx) _).
    assert (Hvs23 : R3 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R2 (Regidx s6_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs22).
    assert (Hvs33 : R3 !!! Regidx s3_idx = f1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R2 (Regidx s6_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs32).

    (* ---- 0x676  c.ldsp s7,56(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr3 Psh MC2 R3 sp0 (mword_of_int 0x676)
              (mword_of_int 7 : mword 6) s7_idx 128 56 (f1 !!! Regidx s7_idx)
              (ui_sh_676 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 56)
                        (f1 !!! Regidx s7_idx) HbCs7))
              with "Hcg Hpc").
    iIntros (CIDr4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x676 : mword 64) 2
                      = mword_of_int 0x678)) in "Hpc".
    set (R4 := <[Regidx s7_idx := regval_into_reg (f1 !!! Regidx s7_idx)]> R3).
    assert (HspR4 : R4 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R3 (Regidx s7_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR3).
    assert (Hvs74 : R4 !!! Regidx s7_idx = f1 !!! Regidx s7_idx)
      by exact (upd_eq R3 (Regidx s7_idx) _).
    assert (Hvs24 : R4 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s7_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs23).
    assert (Hvs34 : R4 !!! Regidx s3_idx = f1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s7_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs33).
    assert (Hvs64 : R4 !!! Regidx s6_idx = f1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s7_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs63).

    (* ---- 0x678  c.ldsp s8,48(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr4 Psh MC2 R4 sp0 (mword_of_int 0x678)
              (mword_of_int 6 : mword 6) s8_idx 128 48 (f1 !!! Regidx s8_idx)
              (ui_sh_678 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 48)
                        (f1 !!! Regidx s8_idx) HbCs8))
              with "Hcg Hpc").
    iIntros (CIDr5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x678 : mword 64) 2
                      = mword_of_int 0x67a)) in "Hpc".
    set (R5 := <[Regidx s8_idx := regval_into_reg (f1 !!! Regidx s8_idx)]> R4).
    assert (HspR5 : R5 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R4 (Regidx s8_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR4).
    assert (Hvs85 : R5 !!! Regidx s8_idx = f1 !!! Regidx s8_idx)
      by exact (upd_eq R4 (Regidx s8_idx) _).
    assert (Hvs25 : R5 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s8_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs24).
    assert (Hvs35 : R5 !!! Regidx s3_idx = f1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s8_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs34).
    assert (Hvs65 : R5 !!! Regidx s6_idx = f1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s8_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs64).
    assert (Hvs75 : R5 !!! Regidx s7_idx = f1 !!! Regidx s7_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s8_idx) (Regidx s7_idx) _
                           ltac:(vm_compute; discriminate)) Hvs74).

    (* ---- 0x67a  c.ldsp s9,40(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr5 Psh MC2 R5 sp0 (mword_of_int 0x67a)
              (mword_of_int 5 : mword 6) s9_idx 128 40 (f1 !!! Regidx s9_idx)
              (ui_sh_67a pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 40)
                        (f1 !!! Regidx s9_idx) HbCs9))
              with "Hcg Hpc").
    iIntros (CIDr6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x67a : mword 64) 2
                      = mword_of_int 0x67c)) in "Hpc".
    set (R6 := <[Regidx s9_idx := regval_into_reg (f1 !!! Regidx s9_idx)]> R5).
    assert (HspR6 : R6 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R5 (Regidx s9_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR5).
    assert (Hvs96 : R6 !!! Regidx s9_idx = f1 !!! Regidx s9_idx)
      by exact (upd_eq R5 (Regidx s9_idx) _).
    assert (Hvs26 : R6 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s9_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs25).
    assert (Hvs36 : R6 !!! Regidx s3_idx = f1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s9_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs35).
    assert (Hvs66 : R6 !!! Regidx s6_idx = f1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s9_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs65).
    assert (Hvs76 : R6 !!! Regidx s7_idx = f1 !!! Regidx s7_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s9_idx) (Regidx s7_idx) _
                           ltac:(vm_compute; discriminate)) Hvs75).
    assert (Hvs86 : R6 !!! Regidx s8_idx = f1 !!! Regidx s8_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s9_idx) (Regidx s8_idx) _
                           ltac:(vm_compute; discriminate)) Hvs85).

    (* ---- 0x67c  c.ldsp s10,32(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr6 Psh MC2 R6 sp0 (mword_of_int 0x67c)
              (mword_of_int 4 : mword 6) s10_idx 128 32 (f1 !!! Regidx s10_idx)
              (ui_sh_67c pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR6
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 32)
                        (f1 !!! Regidx s10_idx) HbCs10))
              with "Hcg Hpc").
    iIntros (CIDr7) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x67c : mword 64) 2
                      = mword_of_int 0x67e)) in "Hpc".
    set (R7 := <[Regidx s10_idx := regval_into_reg (f1 !!! Regidx s10_idx)]> R6).
    assert (HspR7 : R7 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R6 (Regidx s10_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR6).
    assert (Hvs107 : R7 !!! Regidx s10_idx = f1 !!! Regidx s10_idx)
      by exact (upd_eq R6 (Regidx s10_idx) _).
    assert (Hvs27 : R7 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R6 (Regidx s10_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs26).
    assert (Hvs37 : R7 !!! Regidx s3_idx = f1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R6 (Regidx s10_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs36).
    assert (Hvs67 : R7 !!! Regidx s6_idx = f1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne R6 (Regidx s10_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs66).
    assert (Hvs77 : R7 !!! Regidx s7_idx = f1 !!! Regidx s7_idx)
      by exact (eq_trans (upd_ne R6 (Regidx s10_idx) (Regidx s7_idx) _
                           ltac:(vm_compute; discriminate)) Hvs76).
    assert (Hvs87 : R7 !!! Regidx s8_idx = f1 !!! Regidx s8_idx)
      by exact (eq_trans (upd_ne R6 (Regidx s10_idx) (Regidx s8_idx) _
                           ltac:(vm_compute; discriminate)) Hvs86).
    assert (Hvs97 : R7 !!! Regidx s9_idx = f1 !!! Regidx s9_idx)
      by exact (eq_trans (upd_ne R6 (Regidx s10_idx) (Regidx s9_idx) _
                           ltac:(vm_compute; discriminate)) Hvs96).

    (* ---- 0x67e  c.ldsp s11,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr7 Psh MC2 R7 sp0 (mword_of_int 0x67e)
              (mword_of_int 3 : mword 6) s11_idx 128 24 (f1 !!! Regidx s11_idx)
              (ui_sh_67e pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR7
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 24)
                        (f1 !!! Regidx s11_idx) HbCs11))
              with "Hcg Hpc").
    iIntros (CIDr8) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x67e : mword 64) 2
                      = mword_of_int 0x680)) in "Hpc".
    set (R8 := <[Regidx s11_idx := regval_into_reg (f1 !!! Regidx s11_idx)]> R7).
    assert (HspR8 : R8 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR7).
    assert (Hvs118 : R8 !!! Regidx s11_idx = f1 !!! Regidx s11_idx)
      by exact (upd_eq R7 (Regidx s11_idx) _).
    assert (Hvs28 : R8 !!! Regidx s2_idx = f1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs27).
    assert (Hvs38 : R8 !!! Regidx s3_idx = f1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs37).
    assert (Hvs68 : R8 !!! Regidx s6_idx = f1 !!! Regidx s6_idx)
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hvs67).
    assert (Hvs78 : R8 !!! Regidx s7_idx = f1 !!! Regidx s7_idx)
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx s7_idx) _
                           ltac:(vm_compute; discriminate)) Hvs77).
    assert (Hvs88 : R8 !!! Regidx s8_idx = f1 !!! Regidx s8_idx)
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx s8_idx) _
                           ltac:(vm_compute; discriminate)) Hvs87).
    assert (Hvs98 : R8 !!! Regidx s9_idx = f1 !!! Regidx s9_idx)
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx s9_idx) _
                           ltac:(vm_compute; discriminate)) Hvs97).
    assert (Hvs108 : R8 !!! Regidx s10_idx = f1 !!! Regidx s10_idx)
      by exact (eq_trans (upd_ne R7 (Regidx s11_idx) (Regidx s10_idx) _
                           ltac:(vm_compute; discriminate)) Hvs107).

    assert (HpresR : forall r : mword 5,
              Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx ->
              Regidx r <> Regidx s6_idx ->
              Regidx r <> Regidx s7_idx ->
              Regidx r <> Regidx s8_idx ->
              Regidx r <> Regidx s9_idx ->
              Regidx r <> Regidx s10_idx ->
              Regidx r <> Regidx s11_idx ->
              R8 !!! Regidx r = c2 !!! Regidx r).
    { intros r W1 W2 W3 W4 W5 W6 W7 W8.
      rewrite (upd_ne R7 (Regidx s11_idx) (Regidx r) _ W8).
      rewrite (upd_ne R6 (Regidx s10_idx) (Regidx r) _ W7).
      rewrite (upd_ne R5 (Regidx s9_idx) (Regidx r) _ W6).
      rewrite (upd_ne R4 (Regidx s8_idx) (Regidx r) _ W5).
      rewrite (upd_ne R3 (Regidx s7_idx) (Regidx r) _ W4).
      rewrite (upd_ne R2 (Regidx s6_idx) (Regidx r) _ W3).
      rewrite (upd_ne R1 (Regidx s3_idx) (Regidx r) _ W2).
      exact (upd_ne c2 (Regidx s2_idx) (Regidx r) _ W1). }
    (* ---- 0x680  c.j 0x5f8 ---- *)
    iApply (wp_uv_cj C pt Psh MC2 R8 (mword_of_int 0x680)
              (mword_of_int 1980 : mword 11) (mword_of_int 0x5f8)
              (ui_sh_680 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDcj) "Hcg Hpc".
    (* ---- 0x5f8  c.mv a0,s1 ---- *)
    assert (Hs1R8 : R8 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (HpresR s1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate));
          exact Hs1c2).
    assert (Hwa0 : (mword_of_int cmd : mword 64)
                   = add_vec zero_reg (R8 !!! Regidx s1_idx))
      by (rewrite Hs1R8 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MC2 R8 (mword_of_int 0x5f8)
              a0_idx s1_idx (mword_of_int cmd)
              (ui_sh_5f8 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) Hwa0 with "Hcg Hpc").
    iIntros (CIDs0) "Hcg Hpc".
    set (c11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int cmd : mword 64)]> R8).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5f8 : mword 64) 2
                      = mword_of_int 0x5fa)) in "Hpc".
    assert (Hspc11 : c11 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne R8 (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) HspR8).
    assert (Ha0c11 : c11 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq R8 (Regidx a0_idx) _).
    (* ---- 0x5fa  c.ldsp ra,120(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDs0 Psh MC2 c11 sp0 (mword_of_int 0x5fa)
              (mword_of_int 15 : mword 6) ra_idx 128 120 (e1 !!! Regidx ra_idx)
              (ui_sh_5fa pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hspc11
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 120)
                        (e1 !!! Regidx ra_idx) HbCra))
              with "Hcg Hpc").
    iIntros (CIDs1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5fa : mword 64) 2
                      = mword_of_int 0x5fc)) in "Hpc".
    set (S1 := <[Regidx ra_idx := regval_into_reg (e1 !!! Regidx ra_idx)]> c11).
    assert (HspS1 : S1 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne c11 (Regidx ra_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) Hspc11).
    assert (Hvra1 : S1 !!! Regidx ra_idx = e1 !!! Regidx ra_idx)
      by exact (upd_eq c11 (Regidx ra_idx) _).

    (* ---- 0x5fc  c.ldsp s0,112(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDs1 Psh MC2 S1 sp0 (mword_of_int 0x5fc)
              (mword_of_int 14 : mword 6) s0_idx 128 112 (e1 !!! Regidx s0_idx)
              (ui_sh_5fc pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspS1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 112)
                        (e1 !!! Regidx s0_idx) HbCs0))
              with "Hcg Hpc").
    iIntros (CIDs2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5fc : mword 64) 2
                      = mword_of_int 0x5fe)) in "Hpc".
    set (S2 := <[Regidx s0_idx := regval_into_reg (e1 !!! Regidx s0_idx)]> S1).
    assert (HspS2 : S2 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne S1 (Regidx s0_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspS1).
    assert (Hvs02 : S2 !!! Regidx s0_idx = e1 !!! Regidx s0_idx)
      by exact (upd_eq S1 (Regidx s0_idx) _).
    assert (Hvra2 : S2 !!! Regidx ra_idx = e1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne S1 (Regidx s0_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra1).

    (* ---- 0x5fe  c.ldsp s1,104(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDs2 Psh MC2 S2 sp0 (mword_of_int 0x5fe)
              (mword_of_int 13 : mword 6) s1_idx 128 104 (e1 !!! Regidx s1_idx)
              (ui_sh_5fe pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspS2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 104)
                        (e1 !!! Regidx s1_idx) HbCs1))
              with "Hcg Hpc").
    iIntros (CIDs3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x5fe : mword 64) 2
                      = mword_of_int 0x600)) in "Hpc".
    set (S3 := <[Regidx s1_idx := regval_into_reg (e1 !!! Regidx s1_idx)]> S2).
    assert (HspS3 : S3 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne S2 (Regidx s1_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspS2).
    assert (Hvs13 : S3 !!! Regidx s1_idx = e1 !!! Regidx s1_idx)
      by exact (upd_eq S2 (Regidx s1_idx) _).
    assert (Hvra3 : S3 !!! Regidx ra_idx = e1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne S2 (Regidx s1_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra2).
    assert (Hvs03 : S3 !!! Regidx s0_idx = e1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne S2 (Regidx s1_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs02).

    (* ---- 0x600  c.ldsp s4,80(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDs3 Psh MC2 S3 sp0 (mword_of_int 0x600)
              (mword_of_int 10 : mword 6) s4_idx 128 80 (e1 !!! Regidx s4_idx)
              (ui_sh_600 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspS3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 80)
                        (e1 !!! Regidx s4_idx) HbCs4))
              with "Hcg Hpc").
    iIntros (CIDs4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x600 : mword 64) 2
                      = mword_of_int 0x602)) in "Hpc".
    set (S4 := <[Regidx s4_idx := regval_into_reg (e1 !!! Regidx s4_idx)]> S3).
    assert (HspS4 : S4 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne S3 (Regidx s4_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspS3).
    assert (Hvs44 : S4 !!! Regidx s4_idx = e1 !!! Regidx s4_idx)
      by exact (upd_eq S3 (Regidx s4_idx) _).
    assert (Hvra4 : S4 !!! Regidx ra_idx = e1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne S3 (Regidx s4_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra3).
    assert (Hvs04 : S4 !!! Regidx s0_idx = e1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne S3 (Regidx s4_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs03).
    assert (Hvs14 : S4 !!! Regidx s1_idx = e1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne S3 (Regidx s4_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs13).

    (* ---- 0x602  c.ldsp s5,72(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDs4 Psh MC2 S4 sp0 (mword_of_int 0x602)
              (mword_of_int 9 : mword 6) s5_idx 128 72 (e1 !!! Regidx s5_idx)
              (ui_sh_602 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) HfC2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspS4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 MC2 (uint sp0 - 128 + 72)
                        (e1 !!! Regidx s5_idx) HbCs5))
              with "Hcg Hpc").
    iIntros (CIDs5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x602 : mword 64) 2
                      = mword_of_int 0x604)) in "Hpc".
    set (S5 := <[Regidx s5_idx := regval_into_reg (e1 !!! Regidx s5_idx)]> S4).
    assert (HspS5 : S5 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 128) : mword 64))
      by exact (eq_trans (upd_ne S4 (Regidx s5_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspS4).
    assert (Hvs55 : S5 !!! Regidx s5_idx = e1 !!! Regidx s5_idx)
      by exact (upd_eq S4 (Regidx s5_idx) _).
    assert (Hvra5 : S5 !!! Regidx ra_idx = e1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne S4 (Regidx s5_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra4).
    assert (Hvs05 : S5 !!! Regidx s0_idx = e1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne S4 (Regidx s5_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs04).
    assert (Hvs15 : S5 !!! Regidx s1_idx = e1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne S4 (Regidx s5_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs14).
    assert (Hvs45 : S5 !!! Regidx s4_idx = e1 !!! Regidx s4_idx)
      by exact (eq_trans (upd_ne S4 (Regidx s5_idx) (Regidx s4_idx) _
                           ltac:(vm_compute; discriminate)) Hvs44).

    assert (HpresS : forall r : mword 5,
              Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx ->
              Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx ->
              S5 !!! Regidx r = c11 !!! Regidx r).
    { intros r W1 W2 W3 W4 W5.
      rewrite (upd_ne S4 (Regidx s5_idx) (Regidx r) _ W5).
      rewrite (upd_ne S3 (Regidx s4_idx) (Regidx r) _ W4).
      rewrite (upd_ne S2 (Regidx s1_idx) (Regidx r) _ W3).
      rewrite (upd_ne S1 (Regidx s0_idx) (Regidx r) _ W2).
      exact (upd_ne c11 (Regidx ra_idx) (Regidx r) _ W1). }
    (* ---- 0x604  c.addi16sp sp,sp,128 ---- *)
    assert (Hwsp2 : sp0 = add_vec (S5 !!! Regidx csp_rs1)
                            (sign_extend' 64
                               (caddi16sp_imm (mword_of_int 8 : mword 6)))).
    { rewrite HspS5.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 8 : mword 6))
                    : mword 64) = mword_of_int 128)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 128 + 128) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh MC2 S5 (mword_of_int 0x604)
              (mword_of_int 8 : mword 6) sp0
              (ui_sh_604 pt MC2 Hltext (sh_img_text MC2 HgC2)) Hwsp2
              with "Hcg Hpc").
    iIntros (CIDcf) "Hcg Hpc".
    set (c17 := <[Regidx csp_rs1 := regval_into_reg sp0]> S5).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x604 : mword 64) 2
                      = mword_of_int 0x606)) in "Hpc".
    (* ---- 0x606  c.jr ra ---- *)
    assert (HraS : c17 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne S5 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite Hvra5. exact (Hq1 ra_idx ltac:(vm_compute; discriminate)). }
    assert (Htgtr : (m !!! Regidx ra_idx) = ret_pc (c17 !!! Regidx ra_idx)).
    { rewrite HraS. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh MC2 c17 (mword_of_int 0x606)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_606 pt MC2 Hltext (sh_img_text MC2 HgC2))
              ltac:(vm_compute; discriminate) Htgtr with "Hcg Hpc").
    iIntros (CIDcz) "Hcg Hpc".
    (* ---- the postcondition ---- *)
    assert (Hnodec : forall k : Z, cmd <= k < cmd + 8 + 8 * Z.of_nat (length toks) ->
              MC2 !! k = ML !! k).
    { intros k Hk. unfold MC2.
      rewrite (um8_ne MC1 (cmd + 88 + 8 * Z.of_nat (length toks)) _ k
                 ltac:(lia)).
      unfold MC1. apply um8_ne. lia. }
    assert (HargF : forall (j : nat) (t : nat * nat), toks !! j = Some t ->
              uM_bytes MC2 (cmd + 8 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (fst t)) : mword 64) /\
              uM_bytes MC2 (cmd + 88 + 8 * Z.of_nat j) 8
                (mword_of_int (sb + Z.of_nat (snd t)) : mword 64)).
    { intros j t Hj.
      assert (Hjl : (j < length toks)%nat) by exact (lookup_lt_Some toks j t Hj).
      destruct (HargL j t Hj) as (Hb1 & Hb2). split.
      - unfold MC2, MC1. apply st8_bytes_ne; [ lia | ].
        apply st8_bytes_ne; [ lia | ]. exact Hb1.
      - unfold MC2, MC1. apply st8_bytes_ne; [ lia | ].
        apply st8_bytes_ne; [ lia | ]. exact Hb2. }
    assert (HtypeF : uM_bytes MC2 cmd 4 (mword_of_int 1 : mword 32))
      by (intros j Hj; rewrite (Hnodec (cmd + Z.of_nat j) ltac:(lia));
          exact (HtypeL j Hj)).
    assert (HonlyF : uM_only_in M MC2
              [(hbase, 65536); (SH_FREEP, 8); (SH_BASE, 16); (psaddr, 8);
               (uint sp0 - 320, 320)]).
    { apply (win5_in M MC2 hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
               (uint sp0 - 320) 320).
      - exact HdomC.
      - intros k W1 W2 W3 W4 W5.
        unfold MC2.
        rewrite (um8_ne MC1 (cmd + 88 + 8 * Z.of_nat (length toks)) _ k
                   ltac:(lia)).
        unfold MC1.
        rewrite (um8_ne ML (cmd + 8 + 8 * Z.of_nat (length toks)) _ k
                   ltac:(lia)).
        rewrite (win3_out Mr0 ML hbase 65536 psaddr 8 (uint sp0 - 320) 208 k
                   HWL W1 W4 ltac:(lia)).
        rewrite (win2_out Me Mr0 psaddr 8 (uint sp0 - 128 - 192) 192 k Honlyr
                   W4 ltac:(lia)).
        rewrite (win5_out N8 Me hbase 65536 SH_FREEP 8 SH_BASE 16 cmd 168
                   (uint sp0 - 128 - 128) 128 k Honlye W1 W2 W3
                   ltac:(lia) ltac:(lia)).
        rewrite (proj2 HoN8 k ltac:(lia)).
        rewrite (win2_out P5 Mq psaddr 8 (uint sp0 - 128 - 80) 80 k Honlyq
                   W4 ltac:(lia)).
        exact (proj2 HoP5 k ltac:(lia)). }
    assert (HcellF : uM_bytes MC2 psaddr 8
              (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)).
    { unfold MC2, MC1. apply st8_bytes_ne; [ lia | ].
      apply st8_bytes_ne; [ lia | ]. exact HcellL. }
    iApply ("Hcont" $! CIDcz c17 MC2 cmd with
              "[] [] [] [] [] [] [] [] Hbrk Hcg Hpc").
    - (* ucallee_saved *)
      iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Dsp ].
      { rewrite Esp. rewrite (upd_eq S5 (Regidx csp_rs1) _). symmetry. exact Hsp. }
      rewrite (upd_ne S5 (Regidx csp_rs1) (Regidx r) _ Dsp).
      destruct (decide (Regidx r = Regidx s0_idx)) as [ E0 | D0 ].
      { rewrite E0 Hvs05. exact (Hq1 s0_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s1_idx)) as [ E1 | D1 ].
      { rewrite E1 Hvs15. exact (Hq1 s1_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s4_idx)) as [ E4 | D4 ].
      { rewrite E4 Hvs45. exact (Hq1 s4_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s5_idx)) as [ E5 | D5 ].
      { rewrite E5 Hvs55. exact (Hq1 s5_idx ltac:(vm_compute; discriminate)). }
      assert (Dra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da5 : Regidx r <> Regidx a5_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HpresS r Dra D0 D1 D4 D5).
      rewrite (upd_ne R8 (Regidx a0_idx) (Regidx r) _ Da0).
      destruct (decide (Regidx r = Regidx s2_idx)) as [ E2 | D2 ].
      { rewrite E2 Hvs28.
        exact (Hpres8 s2_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s3_idx)) as [ E3 | D3 ].
      { rewrite E3 Hvs38.
        exact (Hpres8 s3_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s6_idx)) as [ E6 | D6 ].
      { rewrite E6 Hvs68.
        exact (Hpres8 s6_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s7_idx)) as [ E7 | D7 ].
      { rewrite E7 Hvs78.
        exact (Hpres8 s7_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s8_idx)) as [ E8 | N8' ].
      { rewrite E8 Hvs88.
        exact (Hpres8 s8_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s9_idx)) as [ E9 | D9 ].
      { rewrite E9 Hvs98.
        exact (Hpres8 s9_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s10_idx)) as [ E10 | D10 ].
      { rewrite E10 Hvs108.
        exact (Hpres8 s10_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s11_idx)) as [ E11 | D11 ].
      { rewrite E11 Hvs118.
        exact (Hpres8 s11_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). }
      rewrite (HpresR r D2 D3 D6 D7 N8' D9 D10 D11).
      rewrite (upd_ne c1 (Regidx a5_idx) (Regidx r) _ Da5).
      rewrite (upd_ne mL (Regidx s2_idx) (Regidx r) _ D2).
      rewrite (HpresL r Hr D1 D2 D3).
      exact (HpresA r Hr Dsp D0 D1 D2 D3 D4 D5 D6 D7 N8' D9 D10 D11).
    - (* a0 = cmd *)
      iPureIntro.
      rewrite (upd_ne S5 (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresS a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Ha0c11.
    - iPureIntro. exact Hcmdv.
    - iPureIntro. exact HtypeF.
    - iPureIntro. split_and!.
      + exact HargF.
      + unfold MC2, MC1. apply st8_bytes_ne; [ lia | ]. apply uM_store8_bytes.
      + unfold MC2. apply uM_store8_bytes.
    - iPureIntro. exact HcellF.
    - iPureIntro. apply (heap_rd MC2 cmd SH_EXECCMD_SZ Hlay);
        [ exact Hwrndc2 | lia | unfold SH_EXECCMD_SZ; lia ].
    - iPureIntro. exact HonlyF.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §3f  parsepipe @0x682 -- delegate, then a [peek] for `|'.             *)
  (*                                                                       *)
  (*   682..690  the 48-byte prologue (ra, s0..s4)                          *)
  (*   692..698  s2/s4 := ps, s1 := es; parseexec(ps, es)                   *)
  (*   69c..6aa  s3 := cmd; peek(ps, es, "|") -- 0, so [pipecmd] is         *)
  (*             unreachable and the recursion stops here                   *)
  (*   6ae..6c0  a0 := cmd and the epilogue                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_parsepipe (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr sb : Z) (bs : list (bv 8)) (off : nat)
      (toks : list (nat * nat)) :
    wp_sh_parsepipe_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 psaddr sb bs off toks.
  Proof.
    intros Hpre Hsp Hst Hps Hes Hcell Hbufc Hoff Htoks Hmax
           Hfreep0 Hbasesz0 Hbssw Hret2.
    pose proof Hpre as (Hlay & Himg & Htab & Hbuf & Hns & Hrdb & Hwrb & Hs0p &
                        Hs0hi & Hfr & Hbufhi).
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    unfold sh_frame_ok in Hfr.
    assert (Hstb : uv_stack pt M sp0 368) by exact Hst.
    pose proof (us_lo _ _ _ _ Hstb) as Hlo.
    pose proof (us_canon _ _ _ _ Hstb) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi.
    assert (Hfrz : hbase + hlen <= uint sp0 - 368) by exact Hfr.
    assert (Hbufz : sb + Z.of_nat (length bs) + 1 <= uint sp0 - 368)
      by exact Hbufhi.
    pose proof Hcell as (Hcb & Hcrd & Hcwr & Hcal & Hclo & Hchi).
    change (2 ^ 38) with 274877906944 in Hchi.
    destruct (uv_stack_split pt M sp0 368 48 320 ltac:(lia) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hstb)
      as (Hst48 & Hst320).
    rewrite (uv_stack_sp_moi pt M sp0 48 Hst48) in Hst320.
    assert (Huspk : uint (mword_of_int (uint sp0 - 48) : mword 64)
                    = uint sp0 - 48)
      by (apply uint_moi; unfold Z64; lia).
    destruct (uv_stack_split pt M (mword_of_int (uint sp0 - 48)) 320 80 240
                ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                Hst320) as (Hstpk80 & _).
    assert (Hsx : ShSyms.parsepipe = 0x682)
      by (destruct sh_syms_pins as (_&_&_&_&_&_&_&_&_&H&_); exact H).
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hsx) in "Hpc".
    (* ---- 0x682  c.addi16sp sp,sp,-48 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 48) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp. rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))
                    : mword 64) = mword_of_int (-48))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x682)
              (mword_of_int 61 : mword 6) (mword_of_int (uint sp0 - 48))
              (ui_sh_682 pt M Hltext (sh_img_text M Himg)) Hwsp with "Hcg Hpc").
    iIntros (CIDp0) "Hcg Hpc".
    set (p1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 48) : mword 64)]> m).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x682 : mword 64) 2
                      = mword_of_int 0x684)) in "Hpc".
    assert (Hq1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              p1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_1 : p1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hv_a0_idx_1 : p1 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq1 a0_idx ltac:(vm_compute; discriminate)); exact Hps).
    assert (Hv_a1_idx_1 : p1 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq1 a1_idx ltac:(vm_compute; discriminate)); exact Hes).
    (* ---- 0x684  c.sdsp ra,40(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp0 Psh M p1 sp0 (mword_of_int 0x684)
              (mword_of_int 5 : mword 6) ra_idx 48 40
              (ui_sh_684 pt M Hltext (sh_img_text M Himg)) Hst48
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x684 : mword 64) 2
                      = mword_of_int 0x686)) in "Hpc".
    set (P1 := uM_store8 M (uint sp0 - 48 + 40) (p1 !!! Regidx ra_idx)).
    assert (HoP1 : uM_only M P1 (uint sp0 - 48) 48)
      by (unfold P1; apply only_step8; [ lia | lia | apply uM_only_refl ]).
    assert (HgP1 : sh_img_sub P1)
      by (exact (only_img M P1 (uint sp0 - 48) 48 HoP1 ltac:(lia) Himg)).
    assert (HkP1 : uv_stack pt P1 sp0 368)
      by (exact (stk_dom M P1 sp0 368 (proj1 HoP1) Hstb)).
    assert (HfP1 : uv_stack pt P1 sp0 48)
      by (exact (stk_dom M P1 sp0 48 (proj1 HoP1) Hst48)).

    (* ---- 0x686  c.sdsp s0,32(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp1 Psh P1 p1 sp0 (mword_of_int 0x686)
              (mword_of_int 4 : mword 6) s0_idx 48 32
              (ui_sh_686 pt P1 Hltext (sh_img_text P1 HgP1)) HfP1
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x686 : mword 64) 2
                      = mword_of_int 0x688)) in "Hpc".
    set (P2 := uM_store8 P1 (uint sp0 - 48 + 32) (p1 !!! Regidx s0_idx)).
    assert (HoP2 : uM_only M P2 (uint sp0 - 48) 48)
      by (unfold P2; apply only_step8; [ lia | lia | exact HoP1 ]).
    assert (HgP2 : sh_img_sub P2)
      by (exact (only_img M P2 (uint sp0 - 48) 48 HoP2 ltac:(lia) Himg)).
    assert (HkP2 : uv_stack pt P2 sp0 368)
      by (exact (stk_dom M P2 sp0 368 (proj1 HoP2) Hstb)).
    assert (HfP2 : uv_stack pt P2 sp0 48)
      by (exact (stk_dom M P2 sp0 48 (proj1 HoP2) Hst48)).

    (* ---- 0x688  c.sdsp s1,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp2 Psh P2 p1 sp0 (mword_of_int 0x688)
              (mword_of_int 3 : mword 6) s1_idx 48 24
              (ui_sh_688 pt P2 Hltext (sh_img_text P2 HgP2)) HfP2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x688 : mword 64) 2
                      = mword_of_int 0x68a)) in "Hpc".
    set (P3 := uM_store8 P2 (uint sp0 - 48 + 24) (p1 !!! Regidx s1_idx)).
    assert (HoP3 : uM_only M P3 (uint sp0 - 48) 48)
      by (unfold P3; apply only_step8; [ lia | lia | exact HoP2 ]).
    assert (HgP3 : sh_img_sub P3)
      by (exact (only_img M P3 (uint sp0 - 48) 48 HoP3 ltac:(lia) Himg)).
    assert (HkP3 : uv_stack pt P3 sp0 368)
      by (exact (stk_dom M P3 sp0 368 (proj1 HoP3) Hstb)).
    assert (HfP3 : uv_stack pt P3 sp0 48)
      by (exact (stk_dom M P3 sp0 48 (proj1 HoP3) Hst48)).

    (* ---- 0x68a  c.sdsp s2,16(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp3 Psh P3 p1 sp0 (mword_of_int 0x68a)
              (mword_of_int 2 : mword 6) s2_idx 48 16
              (ui_sh_68a pt P3 Hltext (sh_img_text P3 HgP3)) HfP3
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x68a : mword 64) 2
                      = mword_of_int 0x68c)) in "Hpc".
    set (P4 := uM_store8 P3 (uint sp0 - 48 + 16) (p1 !!! Regidx s2_idx)).
    assert (HoP4 : uM_only M P4 (uint sp0 - 48) 48)
      by (unfold P4; apply only_step8; [ lia | lia | exact HoP3 ]).
    assert (HgP4 : sh_img_sub P4)
      by (exact (only_img M P4 (uint sp0 - 48) 48 HoP4 ltac:(lia) Himg)).
    assert (HkP4 : uv_stack pt P4 sp0 368)
      by (exact (stk_dom M P4 sp0 368 (proj1 HoP4) Hstb)).
    assert (HfP4 : uv_stack pt P4 sp0 48)
      by (exact (stk_dom M P4 sp0 48 (proj1 HoP4) Hst48)).

    (* ---- 0x68c  c.sdsp s3,8(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp4 Psh P4 p1 sp0 (mword_of_int 0x68c)
              (mword_of_int 1 : mword 6) s3_idx 48 8
              (ui_sh_68c pt P4 Hltext (sh_img_text P4 HgP4)) HfP4
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x68c : mword 64) 2
                      = mword_of_int 0x68e)) in "Hpc".
    set (P5 := uM_store8 P4 (uint sp0 - 48 + 8) (p1 !!! Regidx s3_idx)).
    assert (HoP5 : uM_only M P5 (uint sp0 - 48) 48)
      by (unfold P5; apply only_step8; [ lia | lia | exact HoP4 ]).
    assert (HgP5 : sh_img_sub P5)
      by (exact (only_img M P5 (uint sp0 - 48) 48 HoP5 ltac:(lia) Himg)).
    assert (HkP5 : uv_stack pt P5 sp0 368)
      by (exact (stk_dom M P5 sp0 368 (proj1 HoP5) Hstb)).
    assert (HfP5 : uv_stack pt P5 sp0 48)
      by (exact (stk_dom M P5 sp0 48 (proj1 HoP5) Hst48)).

    (* ---- 0x68e  c.sdsp s4,0(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp5 Psh P5 p1 sp0 (mword_of_int 0x68e)
              (mword_of_int 0 : mword 6) s4_idx 48 0
              (ui_sh_68e pt P5 Hltext (sh_img_text P5 HgP5)) HfP5
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x68e : mword 64) 2
                      = mword_of_int 0x690)) in "Hpc".
    set (P6 := uM_store8 P5 (uint sp0 - 48 + 0) (p1 !!! Regidx s4_idx)).
    assert (HoP6 : uM_only M P6 (uint sp0 - 48) 48)
      by (unfold P6; apply only_step8; [ lia | lia | exact HoP5 ]).
    assert (HgP6 : sh_img_sub P6)
      by (exact (only_img M P6 (uint sp0 - 48) 48 HoP6 ltac:(lia) Himg)).
    assert (HkP6 : uv_stack pt P6 sp0 368)
      by (exact (stk_dom M P6 sp0 368 (proj1 HoP6) Hstb)).
    assert (HfP6 : uv_stack pt P6 sp0 48)
      by (exact (stk_dom M P6 sp0 48 (proj1 HoP6) Hst48)).
    (* ---- 0x690  c.addi4spn s0,sp,48 ---- *)
    assert (Hw2 : (mword_of_int (uint sp0) : mword 64)
                  = add_vec (p1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8)))).
    { rewrite Hv_csp_rs1_1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))
                    : mword 64) = mword_of_int 48)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh P6 p1 (mword_of_int 0x690)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_690 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw2
              with "Hcg Hpc").
    iIntros (CIDb2) "Hcg Hpc".
    set (p2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> p1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x690 : mword 64) 2
                      = mword_of_int 0x692)) in "Hpc".
    assert (Hq2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              p2 !!! Regidx r = p1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_2 : p2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_1).
    assert (Hv_s0_idx_2 : p2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by exact (upd_eq p1 (Regidx s0_idx) _).
    assert (Hv_a0_idx_2 : p2 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq2 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_1).
    assert (Hv_a1_idx_2 : p2 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq2 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_1).

    (* ---- 0x692  c.mv ---- *)
    assert (Hw3 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (p2 !!! Regidx a0_idx))
      by (rewrite Hv_a0_idx_2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P6 p2 (mword_of_int 0x692)
              s2_idx a0_idx (mword_of_int psaddr : mword 64)
              (ui_sh_692 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; discriminate) Hw3 with "Hcg Hpc").
    iIntros (CIDb3) "Hcg Hpc".
    set (p3 := <[Regidx s2_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> p2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x692 : mword 64) 2
                      = mword_of_int 0x694)) in "Hpc".
    assert (Hq3 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              p3 !!! Regidx r = p2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p2 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_3 : p3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_2).
    assert (Hv_s0_idx_3 : p3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq3 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_2).
    assert (Hv_s2_idx_3 : p3 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq p2 (Regidx s2_idx) _).
    assert (Hv_a0_idx_3 : p3 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq3 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_2).
    assert (Hv_a1_idx_3 : p3 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq3 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_2).

    (* ---- 0x694  c.mv ---- *)
    assert (Hw4 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (p3 !!! Regidx a0_idx))
      by (rewrite Hv_a0_idx_3 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P6 p3 (mword_of_int 0x694)
              s4_idx a0_idx (mword_of_int psaddr : mword 64)
              (ui_sh_694 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; discriminate) Hw4 with "Hcg Hpc").
    iIntros (CIDb4) "Hcg Hpc".
    set (p4 := <[Regidx s4_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> p3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x694 : mword 64) 2
                      = mword_of_int 0x696)) in "Hpc".
    assert (Hq4 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              p4 !!! Regidx r = p3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p3 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_4 : p4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq4 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_3).
    assert (Hv_s0_idx_4 : p4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq4 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_3).
    assert (Hv_s2_idx_4 : p4 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_3).
    assert (Hv_s4_idx_4 : p4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq p3 (Regidx s4_idx) _).
    assert (Hv_a0_idx_4 : p4 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_3).
    assert (Hv_a1_idx_4 : p4 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq4 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_3).

    (* ---- 0x696  c.mv ---- *)
    assert (Hw5 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (p4 !!! Regidx a1_idx))
      by (rewrite Hv_a1_idx_4 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P6 p4 (mword_of_int 0x696)
              s1_idx a1_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_696 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; discriminate) Hw5 with "Hcg Hpc").
    iIntros (CIDb5) "Hcg Hpc".
    set (p5 := <[Regidx s1_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> p4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x696 : mword 64) 2
                      = mword_of_int 0x698)) in "Hpc".
    assert (Hq5 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              p5 !!! Regidx r = p4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p4 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_5 : p5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq5 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_4).
    assert (Hv_s0_idx_5 : p5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq5 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_4).
    assert (Hv_s2_idx_5 : p5 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_4).
    assert (Hv_s4_idx_5 : p5 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_4).
    assert (Hv_s1_idx_5 : p5 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq p4 (Regidx s1_idx) _).
    assert (Hv_a0_idx_5 : p5 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_4).
    assert (Hv_a1_idx_5 : p5 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq5 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_4).

    (* ---- 0x698  jal ra, 0x590 ---- *)
    assert (Ht6 : (mword_of_int 0x590 : mword 64)
                   = add_vec (mword_of_int 0x698)
                       (sign_extend' 64 (mword_of_int 2096888 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl6 : (mword_of_int 0x69c : mword 64)
                   = add_vec_int (mword_of_int 0x698 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh P6 p5 (mword_of_int 0x698)
              (mword_of_int 2096888 : mword 21) ra_idx
              (mword_of_int 0x590) (mword_of_int 0x69c)
              (ui_sh_698 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; discriminate) Ht6 Hl6
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDb6) "Hcg Hpc".
    set (p6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x69c : mword 64)]> p5).
    assert (Hq6 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              p6 !!! Regidx r = p5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p5 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_6 : p6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq6 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_5).
    assert (Hv_s0_idx_6 : p6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq6 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_5).
    assert (Hv_s2_idx_6 : p6 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq6 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_5).
    assert (Hv_s4_idx_6 : p6 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq6 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_5).
    assert (Hv_s1_idx_6 : p6 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq6 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_5).
    assert (Hv_a0_idx_6 : p6 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq6 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_5).
    assert (Hv_a1_idx_6 : p6 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq6 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_5).
    assert (Hv_ra_idx_6 : p6 !!! Regidx ra_idx = (mword_of_int 0x69c : mword 64))
      by exact (upd_eq p5 (Regidx ra_idx) _).
    (* ---- 0x590  parseexec(ps, es) ---- *)
    assert (HpreX : sh_parse_pre pt hbase hlen P6 sb bs
                      (mword_of_int (uint sp0 - 48) : mword 64) 320).
    { apply (parse_pre_move M P6 sb bs sp0 (mword_of_int (uint sp0 - 48))
               368 320).
      - exact (proj1 HoP6).
      - intros k Hk. exact (proj2 HoP6 k ltac:(lia)).
      - intros k Hk. exact (proj2 HoP6 k ltac:(lia)).
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hpre. }
    assert (HcellX : sh_ptr_cell pt P6 psaddr (sb + Z.of_nat off)
                       (mword_of_int (uint sp0 - 48) : mword 64)).
    { apply (ptr_cell_move M P6 psaddr (sb + Z.of_nat off) sp0).
      - exact (proj1 HoP6).
      - intros k Hk. exact (proj2 HoP6 k ltac:(lia)).
      - rewrite Huspk. lia.
      - exact Hcell. }
    assert (HstX : uv_stack pt P6 (mword_of_int (uint sp0 - 48)) 320)
      by exact (stk_dom M P6 _ 320 (proj1 HoP6) Hst320).
    assert (HfpX : sh_zeroed P6 SH_FREEP 0 8).
    { intros j Hj. rewrite (proj2 HoP6 (SH_FREEP + j)
        ltac:(unfold SH_FREEP, SH_DATA_PG; lia)). exact (Hfreep0 j Hj). }
    assert (HbsX : sh_zeroed P6 (SH_BASE + 8) 0 8).
    { intros j Hj. rewrite (proj2 HoP6 (SH_BASE + 8 + j)
        ltac:(unfold SH_BASE, SH_DATA_PG; lia)). exact (Hbasesz0 j Hj). }
    assert (HbsswX : uv_wr pt P6 SH_FREEP 0x88)
      by exact (uv_wr_dom pt M P6 SH_FREEP 0x88 (proj1 HoP6) Hbssw).
    assert (Hret2x : is_aligned_vaddr (Virtaddr (p6 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_6; vm_compute; reflexivity).
    iApply (wp_sh_parseexec CIDb6 P6 p6 (mword_of_int (uint sp0 - 48))
              psaddr sb bs off toks
              HpreX Hv_csp_rs1_6 HstX Hv_a0_idx_6 Hv_a1_idx_6 HcellX Hbufc
              Hoff Htoks Hmax HfpX HbsX HbsswX Hret2x
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CIDb7 q1 Mx cmd) "%Hcsx %Ha0x %Hcmdv %Htypex %Hargx %Hpsx %Hrdx
                               %Honlyx Hbrk Hcg Hpc".
    iEval (rewrite Hv_ra_idx_6) in "Hpc".
    assert (Hv_csp_rs1_7 : q1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hcsx csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_6).
    assert (Hv_s0_idx_7 : q1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcsx s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_6).
    assert (Hv_s2_idx_7 : q1 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsx s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_6).
    assert (Hv_s4_idx_7 : q1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsx s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_6).
    assert (Hv_s1_idx_7 : q1 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcsx s1_idx ltac:(vm_compute; reflexivity)); exact Hv_s1_idx_6).
    rewrite Huspk in Honlyx.
    assert (Hnun : sh_nunits SH_EXECCMD_SZ = 12)
      by (unfold sh_nunits, SH_EXECCMD_SZ; vm_compute; reflexivity).
    assert (Hcmdz : cmd = hbase + 65360) by (rewrite Hcmdv Hnun; lia).
    assert (Hlowx : forall k : Z, k < 8208 -> Mx !! k = M !! k).
    { intros k Hk.
      rewrite (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                 (uint sp0 - 48 - 320) 320 k Honlyx
                 ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                 ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia) ltac:(lia)).
      exact (proj2 HoP6 k ltac:(lia)). }
    assert (Hbufx : forall k : Z,
              sb <= k < sb + Z.of_nat (length bs) + 1 -> Mx !! k = M !! k).
    { intros k Hk.
      pose proof Hbufc as (Hd1 & Hd2 & Hd3). unfold sh_disj in Hd1, Hd2, Hd3.
      rewrite (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                 (uint sp0 - 48 - 320) 320 k Honlyx
                 ltac:(lia)
                 ltac:(unfold SH_FREEP, SH_DATA_PG in Hd1 |- *; lia)
                 ltac:(unfold SH_BASE, SH_DATA_PG in Hd2 |- *; lia)
                 ltac:(lia) ltac:(lia)).
      exact (proj2 HoP6 k ltac:(lia)). }
    assert (Hdomx : forall k : Z, is_Some (M !! k) -> is_Some (Mx !! k))
      by (intros k Hk; exact (proj1 Honlyx k (proj1 HoP6 k Hk))).
    assert (Hprex : sh_parse_pre pt hbase hlen Mx sb bs sp0 368).
    { apply (parse_pre_move M Mx sb bs sp0 sp0 368 368).
      - exact Hdomx.
      - exact Hlowx.
      - exact Hbufx.
      - exact Hfrz.
      - exact Hbufz.
      - exact Hpre. }
    pose proof Hprex as (_ & Hgx & _ & _ & _ & _ & _ & _).
    assert (Hstx : uv_stack pt Mx sp0 368)
      by exact (stk_dom M Mx sp0 368 Hdomx Hstb).
    assert (Hhighx : forall k : Z,
              uint sp0 - 48 <= k < uint sp0 -> Mx !! k = P6 !! k)
      by (intros k Hk;
          exact (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                   (uint sp0 - 48 - 320) 320 k Honlyx
                   ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                   ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia)
                   ltac:(lia))).
    (* ---- 0x69c  c.mv ---- *)
    assert (Hw8 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (q1 !!! Regidx a0_idx))
      by (rewrite Ha0x moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx q1 (mword_of_int 0x69c)
              s3_idx a0_idx (mword_of_int cmd : mword 64)
              (ui_sh_69c pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw8 with "Hcg Hpc").
    iIntros (CIDb8) "Hcg Hpc".
    set (q2 := <[Regidx s3_idx := regval_into_reg (mword_of_int cmd : mword 64)]> q1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x69c : mword 64) 2
                      = mword_of_int 0x69e)) in "Hpc".
    assert (Hq8 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              q2 !!! Regidx r = q1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q1 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_8 : q2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq8 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_7).
    assert (Hv_s0_idx_8 : q2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq8 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_7).
    assert (Hv_s2_idx_8 : q2 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq8 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_7).
    assert (Hv_s4_idx_8 : q2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq8 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_7).
    assert (Hv_s1_idx_8 : q2 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq8 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_7).
    assert (Hv_s3_idx_8 : q2 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq q1 (Regidx s3_idx) _).

    (* ---- 0x69e  auipc ---- *)
    assert (Hw9 : (mword_of_int 5790 : mword 64)
                  = add_vec (mword_of_int 0x69e)
                      (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh Mx q2 (mword_of_int 0x69e)
              (mword_of_int 1 : mword 20) a2_idx (mword_of_int 5790)
              (ui_sh_69e pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw9 with "Hcg Hpc").
    iIntros (CIDb9) "Hcg Hpc".
    set (q3 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 5790 : mword 64)]> q2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x69e : mword 64) 4
                      = mword_of_int 0x6a2)) in "Hpc".
    assert (Hq9 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              q3 !!! Regidx r = q2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q2 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_9 : q3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq9 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_8).
    assert (Hv_s0_idx_9 : q3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq9 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_8).
    assert (Hv_s2_idx_9 : q3 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq9 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_8).
    assert (Hv_s4_idx_9 : q3 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq9 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_8).
    assert (Hv_s1_idx_9 : q3 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq9 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_8).
    assert (Hv_s3_idx_9 : q3 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq9 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_8).
    assert (Hv_a2_idx_9 : q3 !!! Regidx a2_idx = (mword_of_int 5790 : mword 64))
      by exact (upd_eq q2 (Regidx a2_idx) _).

    (* ---- 0x6a2  addi ---- *)
    assert (Hw10 : (mword_of_int 4896 : mword 64)
                  = add_vec (q3 !!! Regidx a2_idx)
                      (sign_extend' 64 (mword_of_int 3202 : mword 12))).
    { rewrite Hv_a2_idx_9.
      assert (Hc : (sign_extend' 64 (mword_of_int 3202 : mword 12) : mword 64)
                   = mword_of_int (-894))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh Mx q3 (mword_of_int 0x6a2)
              (mword_of_int 3202 : mword 12) a2_idx a2_idx (mword_of_int 4896)
              (ui_sh_6a2 pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw10 with "Hcg Hpc").
    iIntros (CIDb10) "Hcg Hpc".
    set (q4 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 4896 : mword 64)]> q3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6a2 : mword 64) 4
                      = mword_of_int 0x6a6)) in "Hpc".
    assert (Hq10 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              q4 !!! Regidx r = q3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q3 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_10 : q4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq10 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_9).
    assert (Hv_s0_idx_10 : q4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq10 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_9).
    assert (Hv_s2_idx_10 : q4 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq10 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_9).
    assert (Hv_s4_idx_10 : q4 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq10 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_9).
    assert (Hv_s1_idx_10 : q4 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq10 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_9).
    assert (Hv_s3_idx_10 : q4 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq10 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_9).
    assert (Hv_a2_idx_10 : q4 !!! Regidx a2_idx = (mword_of_int 4896 : mword 64))
      by exact (upd_eq q3 (Regidx a2_idx) _).

    (* ---- 0x6a6  c.mv ---- *)
    assert (Hw11 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (q4 !!! Regidx s1_idx))
      by (rewrite Hv_s1_idx_10 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx q4 (mword_of_int 0x6a6)
              a1_idx s1_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_6a6 pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw11 with "Hcg Hpc").
    iIntros (CIDb11) "Hcg Hpc".
    set (q5 := <[Regidx a1_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> q4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6a6 : mword 64) 2
                      = mword_of_int 0x6a8)) in "Hpc".
    assert (Hq11 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              q5 !!! Regidx r = q4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q4 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_11 : q5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq11 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_10).
    assert (Hv_s0_idx_11 : q5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq11 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_10).
    assert (Hv_s2_idx_11 : q5 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq11 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_10).
    assert (Hv_s4_idx_11 : q5 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq11 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_10).
    assert (Hv_s1_idx_11 : q5 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq11 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_10).
    assert (Hv_s3_idx_11 : q5 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq11 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_10).
    assert (Hv_a2_idx_11 : q5 !!! Regidx a2_idx = (mword_of_int 4896 : mword 64))
      by (rewrite (Hq11 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_10).
    assert (Hv_a1_idx_11 : q5 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq q4 (Regidx a1_idx) _).

    (* ---- 0x6a8  c.mv ---- *)
    assert (Hw12 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (q5 !!! Regidx s2_idx))
      by (rewrite Hv_s2_idx_11 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx q5 (mword_of_int 0x6a8)
              a0_idx s2_idx (mword_of_int psaddr : mword 64)
              (ui_sh_6a8 pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw12 with "Hcg Hpc").
    iIntros (CIDb12) "Hcg Hpc".
    set (q6 := <[Regidx a0_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> q5).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6a8 : mword 64) 2
                      = mword_of_int 0x6aa)) in "Hpc".
    assert (Hq12 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              q6 !!! Regidx r = q5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q5 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_12 : q6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq12 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_11).
    assert (Hv_s0_idx_12 : q6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq12 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_11).
    assert (Hv_s2_idx_12 : q6 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq12 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_11).
    assert (Hv_s4_idx_12 : q6 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq12 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_11).
    assert (Hv_s1_idx_12 : q6 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq12 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_11).
    assert (Hv_s3_idx_12 : q6 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq12 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_11).
    assert (Hv_a2_idx_12 : q6 !!! Regidx a2_idx = (mword_of_int 4896 : mword 64))
      by (rewrite (Hq12 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_11).
    assert (Hv_a1_idx_12 : q6 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq12 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_11).
    assert (Hv_a0_idx_12 : q6 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq q5 (Regidx a0_idx) _).

    (* ---- 0x6aa  jal ra, 0x448 ---- *)
    assert (Ht13 : (mword_of_int 0x448 : mword 64)
                   = add_vec (mword_of_int 0x6aa)
                       (sign_extend' 64 (mword_of_int 2096542 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl13 : (mword_of_int 0x6ae : mword 64)
                   = add_vec_int (mword_of_int 0x6aa : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh Mx q6 (mword_of_int 0x6aa)
              (mword_of_int 2096542 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x6ae)
              (ui_sh_6aa pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Ht13 Hl13
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDb13) "Hcg Hpc".
    set (q7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6ae : mword 64)]> q6).
    assert (Hq13 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              q7 !!! Regidx r = q6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q6 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_13 : q7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq13 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_12).
    assert (Hv_s0_idx_13 : q7 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq13 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_12).
    assert (Hv_s2_idx_13 : q7 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_12).
    assert (Hv_s4_idx_13 : q7 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_12).
    assert (Hv_s1_idx_13 : q7 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq13 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_12).
    assert (Hv_s3_idx_13 : q7 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq13 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_12).
    assert (Hv_a2_idx_13 : q7 !!! Regidx a2_idx = (mword_of_int 4896 : mword 64))
      by (rewrite (Hq13 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_12).
    assert (Hv_a1_idx_13 : q7 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq13 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_12).
    assert (Hv_a0_idx_13 : q7 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_12).
    assert (Hv_ra_idx_13 : q7 !!! Regidx ra_idx = (mword_of_int 0x6ae : mword 64))
      by exact (upd_eq q6 (Regidx ra_idx) _).
    (* ---- 0x448  peek(ps, es, "|") -- 0 ---- *)
    assert (HpreP : sh_parse_pre pt hbase hlen Mx sb bs
                      (mword_of_int (uint sp0 - 48) : mword 64) 80).
    { apply (parse_pre_move Mx Mx sb bs sp0 (mword_of_int (uint sp0 - 48))
               368 80).
      - intros k H; exact H.
      - intros k _; reflexivity.
      - intros k _; reflexivity.
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hprex. }
    assert (HstP : uv_stack pt Mx (mword_of_int (uint sp0 - 48)) 80)
      by exact (stk_dom M Mx _ 80 Hdomx Hstpk80).
    assert (HcellP : sh_ptr_cell pt Mx psaddr (sb + Z.of_nat (length bs))
                       (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (mk_ptr_cell Mx psaddr (sb + Z.of_nat (length bs))
                  (mword_of_int (uint sp0 - 48)) Hpsx
                  (uv_rd_dom pt M Mx psaddr 8 Hdomx Hcrd)
                  (uv_wr_dom pt M Mx psaddr 8 Hdomx Hcwr) Hcal
                  ltac:(rewrite Huspk; lia)
                  ltac:(change (2 ^ 38) with 274877906944; lia)).
    assert (Htbhi : 4896 + Z.of_nat (length sh_tb_pipe) + 1 <= 8192)
      by (rewrite sh_tb_pipe_len; lia).
    assert (Htbfr : 4896 + Z.of_nat (length sh_tb_pipe) + 1
                    <= uint (mword_of_int (uint sp0 - 48) : mword 64) - 80)
      by (rewrite Huspk sh_tb_pipe_len; lia).
    assert (Hret2k : is_aligned_vaddr (Virtaddr (q7 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_13; vm_compute; reflexivity).
    iApply (wp_sh_peek_zero CIDb13 Mx q7 (mword_of_int (uint sp0 - 48))
              psaddr sb 4896 bs (length bs) sh_tb_pipe
              HpreP Hv_csp_rs1_13 HstP Hv_a0_idx_13 Hv_a1_idx_13 Hv_a2_idx_13
              HcellP ltac:(lia) ltac:(lia) Htbhi Htbfr
              sh_tb_pipe_data sh_tb_pipe_sym Hret2k with "Hcg Hpc [Hcont Hbrk]").
    iIntros (CIDb14 r1 Mk) "%Hcsk %Ha0k %Hpsk %Honlyk Hcg Hpc".
    iEval (rewrite Hv_ra_idx_13) in "Hpc".
    assert (Hv_csp_rs1_14 : r1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hcsk csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_13).
    assert (Hv_s0_idx_14 : r1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcsk s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_13).
    assert (Hv_s2_idx_14 : r1 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsk s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_13).
    assert (Hv_s4_idx_14 : r1 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsk s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_13).
    assert (Hv_s1_idx_14 : r1 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcsk s1_idx ltac:(vm_compute; reflexivity)); exact Hv_s1_idx_13).
    assert (Hv_s3_idx_14 : r1 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcsk s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_13).
    rewrite Huspk in Honlyk.
    rewrite drop_all sh_skipws_nil Nat.add_0_r in Hpsk.
    assert (Hlowk : forall k : Z, k < 8208 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    assert (Hbufk : forall k : Z,
              sb <= k < sb + Z.of_nat (length bs) + 1 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    assert (Hdomk : forall k : Z, is_Some (M !! k) -> is_Some (Mk !! k))
      by (intros k Hk; exact (proj1 Honlyk k (Hdomx k Hk))).
    assert (Hprek : sh_parse_pre pt hbase hlen Mk sb bs sp0 368).
    { apply (parse_pre_move Mx Mk sb bs sp0 sp0 368 368).
      - exact (proj1 Honlyk).
      - exact Hlowk.
      - exact Hbufk.
      - exact Hfrz.
      - exact Hbufz.
      - exact Hprex. }
    pose proof Hprek as (_ & Hgk & _ & _ & _ & _ & _ & _).
    assert (HfK : uv_stack pt Mk sp0 48)
      by exact (stk_dom M Mk sp0 48 Hdomk Hst48).
    assert (Hnodek : forall k : Z, cmd <= k < cmd + 168 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    assert (Hhighk : forall k : Z,
              uint sp0 - 48 <= k < uint sp0 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    (* ---- 0x6ae  c.bnez a0,0x6c2 -- NOT taken ---- *)
    assert (Htkk : false = neq_vec (r1 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0k. unfold neq_vec.
      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    assert (Htgtk : (mword_of_int 0x6c2 : mword 64)
                    = add_vec (mword_of_int 0x6ae)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 10 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cbnez C pt Psh Mk r1 (mword_of_int 0x6ae)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x6c2)
              (ui_sh_6ae pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; reflexivity) Htkk Htgtk
              ltac:(intro Hx; discriminate) with "Hcg Hpc").
    iIntros (CIDbz) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6ae : mword 64) 2
                      = mword_of_int 0x6b0)) in "Hpc".
    (* ---- 0x6b0  c.mv ---- *)
    assert (Hw15 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (r1 !!! Regidx s3_idx))
      by (rewrite Hv_s3_idx_14 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mk r1 (mword_of_int 0x6b0)
              a0_idx s3_idx (mword_of_int cmd : mword 64)
              (ui_sh_6b0 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) Hw15 with "Hcg Hpc").
    iIntros (CIDr0) "Hcg Hpc".
    set (r2 := <[Regidx a0_idx := regval_into_reg (mword_of_int cmd : mword 64)]> r1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6b0 : mword 64) 2
                      = mword_of_int 0x6b2)) in "Hpc".
    assert (Hq15 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              r2 !!! Regidx r = r1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r1 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_15 : r2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq15 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_14).
    assert (Hv_s0_idx_15 : r2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq15 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_14).
    assert (Hv_s2_idx_15 : r2 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq15 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_14).
    assert (Hv_s4_idx_15 : r2 !!! Regidx s4_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq15 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_14).
    assert (Hv_s1_idx_15 : r2 !!! Regidx s1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq15 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_14).
    assert (Hv_s3_idx_15 : r2 !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_14).
    assert (Hv_a0_idx_15 : r2 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq r1 (Regidx a0_idx) _).
    assert (HhiC : forall k : Z,
              uint sp0 - 48 <= k < uint sp0 -> Mk !! k = P6 !! k)
      by (intros k Hk; rewrite (Hhighk k Hk); exact (Hhighx k Hk)).
    assert (HbCra : uM_bytes Mk (uint sp0 - 48 + 40) 8 (p1 !!! Regidx ra_idx)).
    { apply (bytes_eq8 P6 Mk (uint sp0 - 48 + 40));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs0 : uM_bytes Mk (uint sp0 - 48 + 32) 8 (p1 !!! Regidx s0_idx)).
    { apply (bytes_eq8 P6 Mk (uint sp0 - 48 + 32));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs1 : uM_bytes Mk (uint sp0 - 48 + 24) 8 (p1 !!! Regidx s1_idx)).
    { apply (bytes_eq8 P6 Mk (uint sp0 - 48 + 24));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs2 : uM_bytes Mk (uint sp0 - 48 + 16) 8 (p1 !!! Regidx s2_idx)).
    { apply (bytes_eq8 P6 Mk (uint sp0 - 48 + 16));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs3 : uM_bytes Mk (uint sp0 - 48 + 8) 8 (p1 !!! Regidx s3_idx)).
    { apply (bytes_eq8 P6 Mk (uint sp0 - 48 + 8));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs4 : uM_bytes Mk (uint sp0 - 48 + 0) 8 (p1 !!! Regidx s4_idx)).
    { apply (bytes_eq8 P6 Mk (uint sp0 - 48 + 0));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    (* ---- 0x6b2  c.ldsp ra,40(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr0 Psh Mk r2 sp0 (mword_of_int 0x6b2)
              (mword_of_int 5 : mword 6) ra_idx 48 40 (p1 !!! Regidx ra_idx)
              (ui_sh_6b2 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) HfK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_15
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 48 + 40)
                        (p1 !!! Regidx ra_idx) HbCra))
              with "Hcg Hpc").
    iIntros (CIDr1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6b2 : mword 64) 2
                      = mword_of_int 0x6b4)) in "Hpc".
    set (R1 := <[Regidx ra_idx := regval_into_reg (p1 !!! Regidx ra_idx)]> r2).
    assert (HspR1 : R1 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne r2 (Regidx ra_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) Hv_csp_rs1_15).
    assert (Hvra1 : R1 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (upd_eq r2 (Regidx ra_idx) _).

    (* ---- 0x6b4  c.ldsp s0,32(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr1 Psh Mk R1 sp0 (mword_of_int 0x6b4)
              (mword_of_int 4 : mword 6) s0_idx 48 32 (p1 !!! Regidx s0_idx)
              (ui_sh_6b4 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) HfK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 48 + 32)
                        (p1 !!! Regidx s0_idx) HbCs0))
              with "Hcg Hpc").
    iIntros (CIDr2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6b4 : mword 64) 2
                      = mword_of_int 0x6b6)) in "Hpc".
    set (R2 := <[Regidx s0_idx := regval_into_reg (p1 !!! Regidx s0_idx)]> R1).
    assert (HspR2 : R2 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R1 (Regidx s0_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR1).
    assert (Hvs02 : R2 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (upd_eq R1 (Regidx s0_idx) _).
    assert (Hvra2 : R2 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R1 (Regidx s0_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra1).

    (* ---- 0x6b6  c.ldsp s1,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr2 Psh Mk R2 sp0 (mword_of_int 0x6b6)
              (mword_of_int 3 : mword 6) s1_idx 48 24 (p1 !!! Regidx s1_idx)
              (ui_sh_6b6 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) HfK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 48 + 24)
                        (p1 !!! Regidx s1_idx) HbCs1))
              with "Hcg Hpc").
    iIntros (CIDr3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6b6 : mword 64) 2
                      = mword_of_int 0x6b8)) in "Hpc".
    set (R3 := <[Regidx s1_idx := regval_into_reg (p1 !!! Regidx s1_idx)]> R2).
    assert (HspR3 : R3 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R2 (Regidx s1_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR2).
    assert (Hvs13 : R3 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (upd_eq R2 (Regidx s1_idx) _).
    assert (Hvra3 : R3 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R2 (Regidx s1_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra2).
    assert (Hvs03 : R3 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R2 (Regidx s1_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs02).

    (* ---- 0x6b8  c.ldsp s2,16(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr3 Psh Mk R3 sp0 (mword_of_int 0x6b8)
              (mword_of_int 2 : mword 6) s2_idx 48 16 (p1 !!! Regidx s2_idx)
              (ui_sh_6b8 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) HfK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 48 + 16)
                        (p1 !!! Regidx s2_idx) HbCs2))
              with "Hcg Hpc").
    iIntros (CIDr4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6b8 : mword 64) 2
                      = mword_of_int 0x6ba)) in "Hpc".
    set (R4 := <[Regidx s2_idx := regval_into_reg (p1 !!! Regidx s2_idx)]> R3).
    assert (HspR4 : R4 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR3).
    assert (Hvs24 : R4 !!! Regidx s2_idx = p1 !!! Regidx s2_idx)
      by exact (upd_eq R3 (Regidx s2_idx) _).
    assert (Hvra4 : R4 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra3).
    assert (Hvs04 : R4 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs03).
    assert (Hvs14 : R4 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs13).

    (* ---- 0x6ba  c.ldsp s3,8(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr4 Psh Mk R4 sp0 (mword_of_int 0x6ba)
              (mword_of_int 1 : mword 6) s3_idx 48 8 (p1 !!! Regidx s3_idx)
              (ui_sh_6ba pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) HfK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 48 + 8)
                        (p1 !!! Regidx s3_idx) HbCs3))
              with "Hcg Hpc").
    iIntros (CIDr5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6ba : mword 64) 2
                      = mword_of_int 0x6bc)) in "Hpc".
    set (R5 := <[Regidx s3_idx := regval_into_reg (p1 !!! Regidx s3_idx)]> R4).
    assert (HspR5 : R5 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR4).
    assert (Hvs35 : R5 !!! Regidx s3_idx = p1 !!! Regidx s3_idx)
      by exact (upd_eq R4 (Regidx s3_idx) _).
    assert (Hvra5 : R5 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra4).
    assert (Hvs05 : R5 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs04).
    assert (Hvs15 : R5 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs14).
    assert (Hvs25 : R5 !!! Regidx s2_idx = p1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs24).

    (* ---- 0x6bc  c.ldsp s4,0(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr5 Psh Mk R5 sp0 (mword_of_int 0x6bc)
              (mword_of_int 0 : mword 6) s4_idx 48 0 (p1 !!! Regidx s4_idx)
              (ui_sh_6bc pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) HfK
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mk (uint sp0 - 48 + 0)
                        (p1 !!! Regidx s4_idx) HbCs4))
              with "Hcg Hpc").
    iIntros (CIDr6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6bc : mword 64) 2
                      = mword_of_int 0x6be)) in "Hpc".
    set (R6 := <[Regidx s4_idx := regval_into_reg (p1 !!! Regidx s4_idx)]> R5).
    assert (HspR6 : R6 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR5).
    assert (Hvs46 : R6 !!! Regidx s4_idx = p1 !!! Regidx s4_idx)
      by exact (upd_eq R5 (Regidx s4_idx) _).
    assert (Hvra6 : R6 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra5).
    assert (Hvs06 : R6 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs05).
    assert (Hvs16 : R6 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs15).
    assert (Hvs26 : R6 !!! Regidx s2_idx = p1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs25).
    assert (Hvs36 : R6 !!! Regidx s3_idx = p1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs35).

    assert (HpresR : forall r : mword 5,
              Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx ->
              Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx ->
              Regidx r <> Regidx s4_idx ->
              R6 !!! Regidx r = r2 !!! Regidx r).
    { intros r W1 W2 W3 W4 W5 W6.
      rewrite (upd_ne R5 (Regidx s4_idx) (Regidx r) _ W6).
      rewrite (upd_ne R4 (Regidx s3_idx) (Regidx r) _ W5).
      rewrite (upd_ne R3 (Regidx s2_idx) (Regidx r) _ W4).
      rewrite (upd_ne R2 (Regidx s1_idx) (Regidx r) _ W3).
      rewrite (upd_ne R1 (Regidx s0_idx) (Regidx r) _ W2).
      exact (upd_ne r2 (Regidx ra_idx) (Regidx r) _ W1). }
    (* ---- 0x6be  c.addi16sp sp,sp,48 ---- *)
    assert (Hwsp2 : sp0 = add_vec (R6 !!! Regidx csp_rs1)
                            (sign_extend' 64
                               (caddi16sp_imm (mword_of_int 3 : mword 6)))).
    { rewrite HspR6.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))
                    : mword 64) = mword_of_int 48)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 48 + 48) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh Mk R6 (mword_of_int 0x6be)
              (mword_of_int 3 : mword 6) sp0
              (ui_sh_6be pt Mk Hltext (sh_img_text Mk Hgk)) Hwsp2
              with "Hcg Hpc").
    iIntros (CIDf) "Hcg Hpc".
    set (cF := <[Regidx csp_rs1 := regval_into_reg sp0]> R6).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6be : mword 64) 2
                      = mword_of_int 0x6c0)) in "Hpc".
    (* ---- 0x6c0  c.jr ra ---- *)
    assert (HraF : cF !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne R6 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite Hvra6. exact (Hq1 ra_idx ltac:(vm_compute; discriminate)). }
    assert (Htgtf : (m !!! Regidx ra_idx) = ret_pc (cF !!! Regidx ra_idx)).
    { rewrite HraF. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh Mk cF (mword_of_int 0x6c0)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_6c0 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) Htgtf with "Hcg Hpc").
    iIntros (CIDfz) "Hcg Hpc".
    assert (Ha0F : cF !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { rewrite (upd_ne R6 (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresR a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hv_a0_idx_15. }
    assert (HonlyF : uM_only_in M Mk
              [(hbase, 65536); (SH_FREEP, 8); (SH_BASE, 16); (psaddr, 8);
               (uint sp0 - 368, 368)]).
    { apply (win5_in M Mk hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
               (uint sp0 - 368) 368).
      - exact Hdomk.
      - intros k W1 W2 W3 W4 W5.
        rewrite (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   W4 ltac:(lia)).
        rewrite (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                   (uint sp0 - 48 - 320) 320 k Honlyx W1 W2 W3 W4 ltac:(lia)).
        exact (proj2 HoP6 k ltac:(lia)). }
    iApply ("Hcont" $! CIDfz cF Mk cmd with
              "[] [] [] [] [] [] [] [] Hbrk Hcg Hpc").
    - (* ucallee_saved *)
      iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Dsp ].
      { rewrite Esp. rewrite (upd_eq R6 (Regidx csp_rs1) _). symmetry. exact Hsp. }
      rewrite (upd_ne R6 (Regidx csp_rs1) (Regidx r) _ Dsp).
      destruct (decide (Regidx r = Regidx s0_idx)) as [ E0 | D0 ].
      { rewrite E0 Hvs06. exact (Hq1 s0_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s1_idx)) as [ E1 | D1 ].
      { rewrite E1 Hvs16. exact (Hq1 s1_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s2_idx)) as [ E2 | D2 ].
      { rewrite E2 Hvs26. exact (Hq1 s2_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s3_idx)) as [ E3 | D3 ].
      { rewrite E3 Hvs36. exact (Hq1 s3_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s4_idx)) as [ E4 | D4 ].
      { rewrite E4 Hvs46. exact (Hq1 s4_idx ltac:(vm_compute; discriminate)). }
      assert (Dra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HpresR r Dra D0 D1 D2 D3 D4).
      rewrite (upd_ne r1 (Regidx a0_idx) (Regidx r) _ Da0).
      rewrite (Hcsk r Hr) (Hq13 r Dra) (Hq12 r Da0) (Hq11 r Da1) (Hq10 r Da2)
              (Hq9 r Da2) (Hq8 r D3) (Hcsx r Hr) (Hq6 r Dra) (Hq5 r D1)
              (Hq4 r D4) (Hq3 r D2) (Hq2 r D0).
      exact (Hq1 r Dsp).
    - iPureIntro. exact Ha0F.
    - iPureIntro. exact Hcmdv.
    - iPureIntro. apply (bytes_eqk Mx Mk cmd 4%nat);
        [ intros j Hj; apply Hnodek; lia | exact Htypex ].
    - iPureIntro. destruct Hargx as (Ha & Hb & Hc). split_and!.
      + intros i t Hi. destruct (Ha i t Hi) as (Hb1 & Hb2).
        assert (Hil : (i < length toks)%nat) by exact (lookup_lt_Some toks i t Hi).
        split.
        * apply (bytes_eq8 Mx Mk (cmd + 8 + 8 * Z.of_nat i));
            [ intros j Hj; apply Hnodek; lia | exact Hb1 ].
        * apply (bytes_eq8 Mx Mk (cmd + 88 + 8 * Z.of_nat i));
            [ intros j Hj; apply Hnodek; lia | exact Hb2 ].
      + apply (bytes_eq8 Mx Mk (cmd + 8 + 8 * Z.of_nat (length toks)));
          [ intros j Hj; apply Hnodek; lia | exact Hb ].
      + apply (bytes_eq8 Mx Mk (cmd + 88 + 8 * Z.of_nat (length toks)));
          [ intros j Hj; apply Hnodek; lia | exact Hc ].
    - iPureIntro. exact Hpsk.
    - iPureIntro. exact (uv_rd_dom pt Mx Mk cmd SH_EXECCMD_SZ
                           (proj1 Honlyk) Hrdx).
    - iPureIntro. exact HonlyF.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §3g  parseline @0x6e2 -- delegate, then a [peek] for `&' and one             *)
  (*                                                                       *)
  (*   for `;'.                                                            *)
  (*                                                                       *)
  (*   6e2..6f0  the 48-byte prologue (ra, s0..s4)                          *)
  (*   6f2..6f6  s2 := ps, s3 := es; parsepipe(ps, es)                      *)
  (*   6fa..724  s1 := cmd, s4 := "&"; peek(ps, es, "&") -- 0, so the       *)
  (*             [backcmd] loop never runs                                  *)
  (*   726..736  peek(ps, es, ";") -- 0, so [listcmd] is unreachable        *)
  (*   738..748  a0 := cmd and the epilogue                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_parseline (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (psaddr sb : Z) (bs : list (bv 8)) (off : nat)
      (toks : list (nat * nat)) :
    wp_sh_parseline_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 psaddr sb bs off toks.
  Proof.
    intros Hpre Hsp Hst Hps Hes Hcell Hbufc Hoff Htoks Hmax
           Hfreep0 Hbasesz0 Hbssw Hret2.
    pose proof Hpre as (Hlay & Himg & Htab & Hbuf & Hns & Hrdb & Hwrb & Hs0p &
                        Hs0hi & Hfr & Hbufhi).
    pose proof (shl_text _ _ _ Hlay) as Hltext.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    unfold sh_frame_ok in Hfr.
    assert (Hstb : uv_stack pt M sp0 416) by exact Hst.
    pose proof (us_lo _ _ _ _ Hstb) as Hlo.
    pose proof (us_canon _ _ _ _ Hstb) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi.
    assert (Hfrz : hbase + hlen <= uint sp0 - 416) by exact Hfr.
    assert (Hbufz : sb + Z.of_nat (length bs) + 1 <= uint sp0 - 416)
      by exact Hbufhi.
    pose proof Hcell as (Hcb & Hcrd & Hcwr & Hcal & Hclo & Hchi).
    change (2 ^ 38) with 274877906944 in Hchi.
    destruct (uv_stack_split pt M sp0 416 48 368 ltac:(lia) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hstb)
      as (Hst48 & Hst368).
    rewrite (uv_stack_sp_moi pt M sp0 48 Hst48) in Hst368.
    assert (Huspk : uint (mword_of_int (uint sp0 - 48) : mword 64)
                    = uint sp0 - 48)
      by (apply uint_moi; unfold Z64; lia).
    destruct (uv_stack_split pt M (mword_of_int (uint sp0 - 48)) 368 80 288
                ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                Hst368) as (Hstpk80 & _).
    assert (Hsx : ShSyms.parseline = 0x6e2)
      by (destruct sh_syms_pins as (_&_&_&_&_&_&_&_&H&_); exact H).
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hsx) in "Hpc".
    (* ---- 0x682  c.addi16sp sp,sp,-48 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 48) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp. rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))
                    : mword 64) = mword_of_int (-48))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x6e2)
              (mword_of_int 61 : mword 6) (mword_of_int (uint sp0 - 48))
              (ui_sh_6e2 pt M Hltext (sh_img_text M Himg)) Hwsp with "Hcg Hpc").
    iIntros (CIDp0) "Hcg Hpc".
    set (p1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 48) : mword 64)]> m).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6e2 : mword 64) 2
                      = mword_of_int 0x6e4)) in "Hpc".
    assert (Hq1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              p1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_1 : p1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hv_a0_idx_1 : p1 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq1 a0_idx ltac:(vm_compute; discriminate)); exact Hps).
    assert (Hv_a1_idx_1 : p1 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq1 a1_idx ltac:(vm_compute; discriminate)); exact Hes).
    (* ---- 0x6e4  c.sdsp ra,40(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp0 Psh M p1 sp0 (mword_of_int 0x6e4)
              (mword_of_int 5 : mword 6) ra_idx 48 40
              (ui_sh_6e4 pt M Hltext (sh_img_text M Himg)) Hst48
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6e4 : mword 64) 2
                      = mword_of_int 0x6e6)) in "Hpc".
    set (P1 := uM_store8 M (uint sp0 - 48 + 40) (p1 !!! Regidx ra_idx)).
    assert (HoP1 : uM_only M P1 (uint sp0 - 48) 48)
      by (unfold P1; apply only_step8; [ lia | lia | apply uM_only_refl ]).
    assert (HgP1 : sh_img_sub P1)
      by (exact (only_img M P1 (uint sp0 - 48) 48 HoP1 ltac:(lia) Himg)).
    assert (HkP1 : uv_stack pt P1 sp0 416)
      by (exact (stk_dom M P1 sp0 416 (proj1 HoP1) Hstb)).
    assert (HfP1 : uv_stack pt P1 sp0 48)
      by (exact (stk_dom M P1 sp0 48 (proj1 HoP1) Hst48)).

    (* ---- 0x6e6  c.sdsp s0,32(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp1 Psh P1 p1 sp0 (mword_of_int 0x6e6)
              (mword_of_int 4 : mword 6) s0_idx 48 32
              (ui_sh_6e6 pt P1 Hltext (sh_img_text P1 HgP1)) HfP1
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6e6 : mword 64) 2
                      = mword_of_int 0x6e8)) in "Hpc".
    set (P2 := uM_store8 P1 (uint sp0 - 48 + 32) (p1 !!! Regidx s0_idx)).
    assert (HoP2 : uM_only M P2 (uint sp0 - 48) 48)
      by (unfold P2; apply only_step8; [ lia | lia | exact HoP1 ]).
    assert (HgP2 : sh_img_sub P2)
      by (exact (only_img M P2 (uint sp0 - 48) 48 HoP2 ltac:(lia) Himg)).
    assert (HkP2 : uv_stack pt P2 sp0 416)
      by (exact (stk_dom M P2 sp0 416 (proj1 HoP2) Hstb)).
    assert (HfP2 : uv_stack pt P2 sp0 48)
      by (exact (stk_dom M P2 sp0 48 (proj1 HoP2) Hst48)).

    (* ---- 0x6e8  c.sdsp s1,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp2 Psh P2 p1 sp0 (mword_of_int 0x6e8)
              (mword_of_int 3 : mword 6) s1_idx 48 24
              (ui_sh_6e8 pt P2 Hltext (sh_img_text P2 HgP2)) HfP2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6e8 : mword 64) 2
                      = mword_of_int 0x6ea)) in "Hpc".
    set (P3 := uM_store8 P2 (uint sp0 - 48 + 24) (p1 !!! Regidx s1_idx)).
    assert (HoP3 : uM_only M P3 (uint sp0 - 48) 48)
      by (unfold P3; apply only_step8; [ lia | lia | exact HoP2 ]).
    assert (HgP3 : sh_img_sub P3)
      by (exact (only_img M P3 (uint sp0 - 48) 48 HoP3 ltac:(lia) Himg)).
    assert (HkP3 : uv_stack pt P3 sp0 416)
      by (exact (stk_dom M P3 sp0 416 (proj1 HoP3) Hstb)).
    assert (HfP3 : uv_stack pt P3 sp0 48)
      by (exact (stk_dom M P3 sp0 48 (proj1 HoP3) Hst48)).

    (* ---- 0x6ea  c.sdsp s2,16(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp3 Psh P3 p1 sp0 (mword_of_int 0x6ea)
              (mword_of_int 2 : mword 6) s2_idx 48 16
              (ui_sh_6ea pt P3 Hltext (sh_img_text P3 HgP3)) HfP3
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6ea : mword 64) 2
                      = mword_of_int 0x6ec)) in "Hpc".
    set (P4 := uM_store8 P3 (uint sp0 - 48 + 16) (p1 !!! Regidx s2_idx)).
    assert (HoP4 : uM_only M P4 (uint sp0 - 48) 48)
      by (unfold P4; apply only_step8; [ lia | lia | exact HoP3 ]).
    assert (HgP4 : sh_img_sub P4)
      by (exact (only_img M P4 (uint sp0 - 48) 48 HoP4 ltac:(lia) Himg)).
    assert (HkP4 : uv_stack pt P4 sp0 416)
      by (exact (stk_dom M P4 sp0 416 (proj1 HoP4) Hstb)).
    assert (HfP4 : uv_stack pt P4 sp0 48)
      by (exact (stk_dom M P4 sp0 48 (proj1 HoP4) Hst48)).

    (* ---- 0x6ec  c.sdsp s3,8(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp4 Psh P4 p1 sp0 (mword_of_int 0x6ec)
              (mword_of_int 1 : mword 6) s3_idx 48 8
              (ui_sh_6ec pt P4 Hltext (sh_img_text P4 HgP4)) HfP4
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6ec : mword 64) 2
                      = mword_of_int 0x6ee)) in "Hpc".
    set (P5 := uM_store8 P4 (uint sp0 - 48 + 8) (p1 !!! Regidx s3_idx)).
    assert (HoP5 : uM_only M P5 (uint sp0 - 48) 48)
      by (unfold P5; apply only_step8; [ lia | lia | exact HoP4 ]).
    assert (HgP5 : sh_img_sub P5)
      by (exact (only_img M P5 (uint sp0 - 48) 48 HoP5 ltac:(lia) Himg)).
    assert (HkP5 : uv_stack pt P5 sp0 416)
      by (exact (stk_dom M P5 sp0 416 (proj1 HoP5) Hstb)).
    assert (HfP5 : uv_stack pt P5 sp0 48)
      by (exact (stk_dom M P5 sp0 48 (proj1 HoP5) Hst48)).

    (* ---- 0x6ee  c.sdsp s4,0(sp) ---- *)
    iApply (wp_uv_frame_store C pt CIDp5 Psh P5 p1 sp0 (mword_of_int 0x6ee)
              (mword_of_int 0 : mword 6) s4_idx 48 0
              (ui_sh_6ee pt P5 Hltext (sh_img_text P5 HgP5)) HfP5
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6ee : mword 64) 2
                      = mword_of_int 0x6f0)) in "Hpc".
    set (P6 := uM_store8 P5 (uint sp0 - 48 + 0) (p1 !!! Regidx s4_idx)).
    assert (HoP6 : uM_only M P6 (uint sp0 - 48) 48)
      by (unfold P6; apply only_step8; [ lia | lia | exact HoP5 ]).
    assert (HgP6 : sh_img_sub P6)
      by (exact (only_img M P6 (uint sp0 - 48) 48 HoP6 ltac:(lia) Himg)).
    assert (HkP6 : uv_stack pt P6 sp0 416)
      by (exact (stk_dom M P6 sp0 416 (proj1 HoP6) Hstb)).
    assert (HfP6 : uv_stack pt P6 sp0 48)
      by (exact (stk_dom M P6 sp0 48 (proj1 HoP6) Hst48)).
    (* ---- 0x6f0  c.addi4spn s0,sp,48 ---- *)
    assert (Hw2 : (mword_of_int (uint sp0) : mword 64)
                  = add_vec (p1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8)))).
    { rewrite Hv_csp_rs1_1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))
                    : mword 64) = mword_of_int 48)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh P6 p1 (mword_of_int 0x6f0)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_6f0 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw2
              with "Hcg Hpc").
    iIntros (CIDb2) "Hcg Hpc".
    set (p2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> p1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6f0 : mword 64) 2
                      = mword_of_int 0x6f2)) in "Hpc".
    assert (Hq2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              p2 !!! Regidx r = p1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_2 : p2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_1).
    assert (Hv_s0_idx_2 : p2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by exact (upd_eq p1 (Regidx s0_idx) _).
    assert (Hv_a0_idx_2 : p2 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq2 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_1).
    assert (Hv_a1_idx_2 : p2 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq2 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_1).

    (* ---- 0x6f2  c.mv ---- *)
    assert (Hw3 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (p2 !!! Regidx a0_idx))
      by (rewrite Hv_a0_idx_2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P6 p2 (mword_of_int 0x6f2)
              s2_idx a0_idx (mword_of_int psaddr : mword 64)
              (ui_sh_6f2 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; discriminate) Hw3 with "Hcg Hpc").
    iIntros (CIDb3) "Hcg Hpc".
    set (p3 := <[Regidx s2_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> p2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6f2 : mword 64) 2
                      = mword_of_int 0x6f4)) in "Hpc".
    assert (Hq3 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              p3 !!! Regidx r = p2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p2 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_3 : p3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_2).
    assert (Hv_s0_idx_3 : p3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq3 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_2).
    assert (Hv_s2_idx_3 : p3 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq p2 (Regidx s2_idx) _).
    assert (Hv_a0_idx_3 : p3 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq3 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_2).
    assert (Hv_a1_idx_3 : p3 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq3 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_2).

    (* ---- 0x6f4  c.mv ---- *)
    assert (Hw4 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (p3 !!! Regidx a1_idx))
      by (rewrite Hv_a1_idx_3 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh P6 p3 (mword_of_int 0x6f4)
              s3_idx a1_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_6f4 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; discriminate) Hw4 with "Hcg Hpc").
    iIntros (CIDb4) "Hcg Hpc".
    set (p4 := <[Regidx s3_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> p3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6f4 : mword 64) 2
                      = mword_of_int 0x6f6)) in "Hpc".
    assert (Hq4 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              p4 !!! Regidx r = p3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p3 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_4 : p4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq4 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_3).
    assert (Hv_s0_idx_4 : p4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq4 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_3).
    assert (Hv_s2_idx_4 : p4 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_3).
    assert (Hv_s3_idx_4 : p4 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq p3 (Regidx s3_idx) _).
    assert (Hv_a0_idx_4 : p4 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq4 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_3).
    assert (Hv_a1_idx_4 : p4 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq4 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_3).

    (* ---- 0x6f6  jal ra, 0x682 ---- *)
    assert (Ht5 : (mword_of_int 0x682 : mword 64)
                   = add_vec (mword_of_int 0x6f6)
                       (sign_extend' 64 (mword_of_int 2097036 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl5 : (mword_of_int 0x6fa : mword 64)
                   = add_vec_int (mword_of_int 0x6f6 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh P6 p4 (mword_of_int 0x6f6)
              (mword_of_int 2097036 : mword 21) ra_idx
              (mword_of_int 0x682) (mword_of_int 0x6fa)
              (ui_sh_6f6 pt P6 Hltext (sh_img_text P6 HgP6))
              ltac:(vm_compute; discriminate) Ht5 Hl5
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDb5) "Hcg Hpc".
    set (p5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6fa : mword 64)]> p4).
    assert (Hq5 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              p5 !!! Regidx r = p4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p4 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_5 : p5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq5 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_4).
    assert (Hv_s0_idx_5 : p5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq5 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_4).
    assert (Hv_s2_idx_5 : p5 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_4).
    assert (Hv_s3_idx_5 : p5 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq5 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_4).
    assert (Hv_a0_idx_5 : p5 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq5 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_4).
    assert (Hv_a1_idx_5 : p5 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq5 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_4).
    assert (Hv_ra_idx_5 : p5 !!! Regidx ra_idx = (mword_of_int 0x6fa : mword 64))
      by exact (upd_eq p4 (Regidx ra_idx) _).
    (* ---- 0x682  parsepipe(ps, es) ---- *)
    assert (HpreX : sh_parse_pre pt hbase hlen P6 sb bs
                      (mword_of_int (uint sp0 - 48) : mword 64) 368).
    { apply (parse_pre_move M P6 sb bs sp0 (mword_of_int (uint sp0 - 48))
               416 368).
      - exact (proj1 HoP6).
      - intros k Hk. exact (proj2 HoP6 k ltac:(lia)).
      - intros k Hk. exact (proj2 HoP6 k ltac:(lia)).
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hpre. }
    assert (HcellX : sh_ptr_cell pt P6 psaddr (sb + Z.of_nat off)
                       (mword_of_int (uint sp0 - 48) : mword 64)).
    { apply (ptr_cell_move M P6 psaddr (sb + Z.of_nat off) sp0).
      - exact (proj1 HoP6).
      - intros k Hk. exact (proj2 HoP6 k ltac:(lia)).
      - rewrite Huspk. lia.
      - exact Hcell. }
    assert (HstX : uv_stack pt P6 (mword_of_int (uint sp0 - 48)) 368)
      by exact (stk_dom M P6 _ 368 (proj1 HoP6) Hst368).
    assert (HfpX : sh_zeroed P6 SH_FREEP 0 8).
    { intros j Hj. rewrite (proj2 HoP6 (SH_FREEP + j)
        ltac:(unfold SH_FREEP, SH_DATA_PG; lia)). exact (Hfreep0 j Hj). }
    assert (HbsX : sh_zeroed P6 (SH_BASE + 8) 0 8).
    { intros j Hj. rewrite (proj2 HoP6 (SH_BASE + 8 + j)
        ltac:(unfold SH_BASE, SH_DATA_PG; lia)). exact (Hbasesz0 j Hj). }
    assert (HbsswX : uv_wr pt P6 SH_FREEP 0x88)
      by exact (uv_wr_dom pt M P6 SH_FREEP 0x88 (proj1 HoP6) Hbssw).
    assert (Hret2x : is_aligned_vaddr (Virtaddr (p5 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_5; vm_compute; reflexivity).
    iApply (wp_sh_parsepipe CIDb5 P6 p5 (mword_of_int (uint sp0 - 48))
              psaddr sb bs off toks
              HpreX Hv_csp_rs1_5 HstX Hv_a0_idx_5 Hv_a1_idx_5 HcellX Hbufc
              Hoff Htoks Hmax HfpX HbsX HbsswX Hret2x
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CIDb6 q1 Mx cmd) "%Hcsx %Ha0x %Hcmdv %Htypex %Hargx %Hpsx %Hrdx
                               %Honlyx Hbrk Hcg Hpc".
    iEval (rewrite Hv_ra_idx_5) in "Hpc".
    assert (Hv_csp_rs1_6 : q1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hcsx csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_5).
    assert (Hv_s0_idx_6 : q1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcsx s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_5).
    assert (Hv_s2_idx_6 : q1 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsx s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_5).
    assert (Hv_s3_idx_6 : q1 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcsx s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_5).
    rewrite Huspk in Honlyx.
    assert (Hnun : sh_nunits SH_EXECCMD_SZ = 12)
      by (unfold sh_nunits, SH_EXECCMD_SZ; vm_compute; reflexivity).
    assert (Hcmdz : cmd = hbase + 65360) by (rewrite Hcmdv Hnun; lia).
    assert (Hlowx : forall k : Z, k < 8208 -> Mx !! k = M !! k).
    { intros k Hk.
      rewrite (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                 (uint sp0 - 48 - 368) 368 k Honlyx
                 ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                 ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia) ltac:(lia)).
      exact (proj2 HoP6 k ltac:(lia)). }
    assert (Hbufx : forall k : Z,
              sb <= k < sb + Z.of_nat (length bs) + 1 -> Mx !! k = M !! k).
    { intros k Hk.
      pose proof Hbufc as (Hd1 & Hd2 & Hd3). unfold sh_disj in Hd1, Hd2, Hd3.
      rewrite (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                 (uint sp0 - 48 - 368) 368 k Honlyx
                 ltac:(lia)
                 ltac:(unfold SH_FREEP, SH_DATA_PG in Hd1 |- *; lia)
                 ltac:(unfold SH_BASE, SH_DATA_PG in Hd2 |- *; lia)
                 ltac:(lia) ltac:(lia)).
      exact (proj2 HoP6 k ltac:(lia)). }
    assert (Hdomx : forall k : Z, is_Some (M !! k) -> is_Some (Mx !! k))
      by (intros k Hk; exact (proj1 Honlyx k (proj1 HoP6 k Hk))).
    assert (Hprex : sh_parse_pre pt hbase hlen Mx sb bs sp0 416).
    { apply (parse_pre_move M Mx sb bs sp0 sp0 416 416).
      - exact Hdomx.
      - exact Hlowx.
      - exact Hbufx.
      - exact Hfrz.
      - exact Hbufz.
      - exact Hpre. }
    pose proof Hprex as (_ & Hgx & _ & _ & _ & _ & _ & _).
    assert (Hstx : uv_stack pt Mx sp0 416)
      by exact (stk_dom M Mx sp0 416 Hdomx Hstb).
    assert (Hhighx : forall k : Z,
              uint sp0 - 48 <= k < uint sp0 -> Mx !! k = P6 !! k)
      by (intros k Hk;
          exact (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                   (uint sp0 - 48 - 368) 368 k Honlyx
                   ltac:(lia) ltac:(unfold SH_FREEP, SH_DATA_PG; lia)
                   ltac:(unfold SH_BASE, SH_DATA_PG; lia) ltac:(lia)
                   ltac:(lia))).
    (* ---- 0x6fa  c.mv ---- *)
    assert (Hw7 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (q1 !!! Regidx a0_idx))
      by (rewrite Ha0x moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx q1 (mword_of_int 0x6fa)
              s1_idx a0_idx (mword_of_int cmd : mword 64)
              (ui_sh_6fa pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw7 with "Hcg Hpc").
    iIntros (CIDb7) "Hcg Hpc".
    set (q2 := <[Regidx s1_idx := regval_into_reg (mword_of_int cmd : mword 64)]> q1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6fa : mword 64) 2
                      = mword_of_int 0x6fc)) in "Hpc".
    assert (Hq7 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              q2 !!! Regidx r = q1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q1 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_7 : q2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq7 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_6).
    assert (Hv_s0_idx_7 : q2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq7 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_6).
    assert (Hv_s2_idx_7 : q2 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq7 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_6).
    assert (Hv_s3_idx_7 : q2 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq7 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_6).
    assert (Hv_s1_idx_7 : q2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq q1 (Regidx s1_idx) _).

    (* ---- 0x6fc  auipc ---- *)
    assert (Hw8 : (mword_of_int 5884 : mword 64)
                  = add_vec (mword_of_int 0x6fc)
                      (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh Mx q2 (mword_of_int 0x6fc)
              (mword_of_int 1 : mword 20) s4_idx (mword_of_int 5884)
              (ui_sh_6fc pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw8 with "Hcg Hpc").
    iIntros (CIDb8) "Hcg Hpc".
    set (q3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 5884 : mword 64)]> q2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x6fc : mword 64) 4
                      = mword_of_int 0x700)) in "Hpc".
    assert (Hq8 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              q3 !!! Regidx r = q2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q2 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_8 : q3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq8 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_7).
    assert (Hv_s0_idx_8 : q3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq8 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_7).
    assert (Hv_s2_idx_8 : q3 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq8 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_7).
    assert (Hv_s3_idx_8 : q3 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq8 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_7).
    assert (Hv_s1_idx_8 : q3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq8 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_7).
    assert (Hv_s4_idx_8 : q3 !!! Regidx s4_idx = (mword_of_int 5884 : mword 64))
      by exact (upd_eq q2 (Regidx s4_idx) _).

    (* ---- 0x700  addi ---- *)
    assert (Hw9 : (mword_of_int 4904 : mword 64)
                  = add_vec (q3 !!! Regidx s4_idx)
                      (sign_extend' 64 (mword_of_int 3116 : mword 12))).
    { rewrite Hv_s4_idx_8.
      assert (Hc : (sign_extend' 64 (mword_of_int 3116 : mword 12) : mword 64)
                   = mword_of_int (-980))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh Mx q3 (mword_of_int 0x700)
              (mword_of_int 3116 : mword 12) s4_idx s4_idx (mword_of_int 4904)
              (ui_sh_700 pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw9 with "Hcg Hpc").
    iIntros (CIDb9) "Hcg Hpc".
    set (q4 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 4904 : mword 64)]> q3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x700 : mword 64) 4
                      = mword_of_int 0x704)) in "Hpc".
    assert (Hq9 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              q4 !!! Regidx r = q3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q3 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_9 : q4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq9 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_8).
    assert (Hv_s0_idx_9 : q4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq9 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_8).
    assert (Hv_s2_idx_9 : q4 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq9 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_8).
    assert (Hv_s3_idx_9 : q4 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq9 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_8).
    assert (Hv_s1_idx_9 : q4 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq9 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_8).
    assert (Hv_s4_idx_9 : q4 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by exact (upd_eq q3 (Regidx s4_idx) _).

    (* ---- 0x704  c.j 0x71a ---- *)
    iApply (wp_uv_cj C pt Psh Mx q4 (mword_of_int 0x704)
              (mword_of_int 11 : mword 11) (mword_of_int 0x71a)
              (ui_sh_704 pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDbj) "Hcg Hpc".

    (* ---- 0x71a  c.mv ---- *)
    assert (Hw10 : (mword_of_int 4904 : mword 64)
                  = add_vec zero_reg (q4 !!! Regidx s4_idx))
      by (rewrite Hv_s4_idx_9 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx q4 (mword_of_int 0x71a)
              a2_idx s4_idx (mword_of_int 4904 : mword 64)
              (ui_sh_71a pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw10 with "Hcg Hpc").
    iIntros (CIDb10) "Hcg Hpc".
    set (q5 := <[Regidx a2_idx := regval_into_reg (mword_of_int 4904 : mword 64)]> q4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x71a : mword 64) 2
                      = mword_of_int 0x71c)) in "Hpc".
    assert (Hq10 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              q5 !!! Regidx r = q4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q4 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_10 : q5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq10 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_9).
    assert (Hv_s0_idx_10 : q5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq10 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_9).
    assert (Hv_s2_idx_10 : q5 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq10 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_9).
    assert (Hv_s3_idx_10 : q5 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq10 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_9).
    assert (Hv_s1_idx_10 : q5 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq10 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_9).
    assert (Hv_s4_idx_10 : q5 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq10 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_9).
    assert (Hv_a2_idx_10 : q5 !!! Regidx a2_idx = (mword_of_int 4904 : mword 64))
      by exact (upd_eq q4 (Regidx a2_idx) _).

    (* ---- 0x71c  c.mv ---- *)
    assert (Hw11 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (q5 !!! Regidx s3_idx))
      by (rewrite Hv_s3_idx_10 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx q5 (mword_of_int 0x71c)
              a1_idx s3_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_71c pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw11 with "Hcg Hpc").
    iIntros (CIDb11) "Hcg Hpc".
    set (q6 := <[Regidx a1_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> q5).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x71c : mword 64) 2
                      = mword_of_int 0x71e)) in "Hpc".
    assert (Hq11 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              q6 !!! Regidx r = q5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q5 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_11 : q6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq11 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_10).
    assert (Hv_s0_idx_11 : q6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq11 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_10).
    assert (Hv_s2_idx_11 : q6 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq11 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_10).
    assert (Hv_s3_idx_11 : q6 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq11 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_10).
    assert (Hv_s1_idx_11 : q6 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq11 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_10).
    assert (Hv_s4_idx_11 : q6 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq11 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_10).
    assert (Hv_a2_idx_11 : q6 !!! Regidx a2_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq11 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_10).
    assert (Hv_a1_idx_11 : q6 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq q5 (Regidx a1_idx) _).

    (* ---- 0x71e  c.mv ---- *)
    assert (Hw12 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (q6 !!! Regidx s2_idx))
      by (rewrite Hv_s2_idx_11 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx q6 (mword_of_int 0x71e)
              a0_idx s2_idx (mword_of_int psaddr : mword 64)
              (ui_sh_71e pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Hw12 with "Hcg Hpc").
    iIntros (CIDb12) "Hcg Hpc".
    set (q7 := <[Regidx a0_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> q6).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x71e : mword 64) 2
                      = mword_of_int 0x720)) in "Hpc".
    assert (Hq12 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              q7 !!! Regidx r = q6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q6 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_12 : q7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq12 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_11).
    assert (Hv_s0_idx_12 : q7 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq12 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_11).
    assert (Hv_s2_idx_12 : q7 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq12 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_11).
    assert (Hv_s3_idx_12 : q7 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq12 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_11).
    assert (Hv_s1_idx_12 : q7 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq12 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_11).
    assert (Hv_s4_idx_12 : q7 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq12 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_11).
    assert (Hv_a2_idx_12 : q7 !!! Regidx a2_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq12 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_11).
    assert (Hv_a1_idx_12 : q7 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq12 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_11).
    assert (Hv_a0_idx_12 : q7 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq q6 (Regidx a0_idx) _).

    (* ---- 0x720  jal ra, 0x448 ---- *)
    assert (Ht13 : (mword_of_int 0x448 : mword 64)
                   = add_vec (mword_of_int 0x720)
                       (sign_extend' 64 (mword_of_int 2096424 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl13 : (mword_of_int 0x724 : mword 64)
                   = add_vec_int (mword_of_int 0x720 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh Mx q7 (mword_of_int 0x720)
              (mword_of_int 2096424 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x724)
              (ui_sh_720 pt Mx Hltext (sh_img_text Mx Hgx))
              ltac:(vm_compute; discriminate) Ht13 Hl13
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDb13) "Hcg Hpc".
    set (q8 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x724 : mword 64)]> q7).
    assert (Hq13 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              q8 !!! Regidx r = q7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q7 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_13 : q8 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq13 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_12).
    assert (Hv_s0_idx_13 : q8 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq13 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_12).
    assert (Hv_s2_idx_13 : q8 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_12).
    assert (Hv_s3_idx_13 : q8 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq13 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_12).
    assert (Hv_s1_idx_13 : q8 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq13 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_12).
    assert (Hv_s4_idx_13 : q8 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq13 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_12).
    assert (Hv_a2_idx_13 : q8 !!! Regidx a2_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq13 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_12).
    assert (Hv_a1_idx_13 : q8 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq13 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_12).
    assert (Hv_a0_idx_13 : q8 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq13 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_12).
    assert (Hv_ra_idx_13 : q8 !!! Regidx ra_idx = (mword_of_int 0x724 : mword 64))
      by exact (upd_eq q7 (Regidx ra_idx) _).
    (* ---- 0x448  peek(ps, es, "&") -- 0 ---- *)
    assert (HpreP : sh_parse_pre pt hbase hlen Mx sb bs
                      (mword_of_int (uint sp0 - 48) : mword 64) 80).
    { apply (parse_pre_move Mx Mx sb bs sp0 (mword_of_int (uint sp0 - 48))
               416 80).
      - intros k H; exact H.
      - intros k _; reflexivity.
      - intros k _; reflexivity.
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hprex. }
    assert (HstP : uv_stack pt Mx (mword_of_int (uint sp0 - 48)) 80)
      by exact (stk_dom M Mx _ 80 Hdomx Hstpk80).
    assert (HcellP : sh_ptr_cell pt Mx psaddr (sb + Z.of_nat (length bs))
                       (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (mk_ptr_cell Mx psaddr (sb + Z.of_nat (length bs))
                  (mword_of_int (uint sp0 - 48)) Hpsx
                  (uv_rd_dom pt M Mx psaddr 8 Hdomx Hcrd)
                  (uv_wr_dom pt M Mx psaddr 8 Hdomx Hcwr) Hcal
                  ltac:(rewrite Huspk; lia)
                  ltac:(change (2 ^ 38) with 274877906944; lia)).
    assert (Htbhi : 4904 + Z.of_nat (length sh_tb_amp) + 1 <= 8192)
      by (rewrite sh_tb_amp_len; lia).
    assert (Htbfr : 4904 + Z.of_nat (length sh_tb_amp) + 1
                    <= uint (mword_of_int (uint sp0 - 48) : mword 64) - 80)
      by (rewrite Huspk sh_tb_amp_len; lia).
    assert (Hret2k : is_aligned_vaddr (Virtaddr (q8 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_13; vm_compute; reflexivity).
    iApply (wp_sh_peek_zero CIDb13 Mx q8 (mword_of_int (uint sp0 - 48))
              psaddr sb 4904 bs (length bs) sh_tb_amp
              HpreP Hv_csp_rs1_13 HstP Hv_a0_idx_13 Hv_a1_idx_13 Hv_a2_idx_13
              HcellP ltac:(lia) ltac:(lia) Htbhi Htbfr
              sh_tb_amp_data sh_tb_amp_sym Hret2k with "Hcg Hpc [Hcont Hbrk]").
    iIntros (CIDb14 r1 Mk) "%Hcsk %Ha0k %Hpsk %Honlyk Hcg Hpc".
    iEval (rewrite Hv_ra_idx_13) in "Hpc".
    assert (Hv_csp_rs1_14 : r1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hcsk csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_13).
    assert (Hv_s0_idx_14 : r1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcsk s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_13).
    assert (Hv_s2_idx_14 : r1 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsk s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_13).
    assert (Hv_s3_idx_14 : r1 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcsk s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_13).
    assert (Hv_s1_idx_14 : r1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcsk s1_idx ltac:(vm_compute; reflexivity)); exact Hv_s1_idx_13).
    assert (Hv_s4_idx_14 : r1 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hcsk s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_13).
    rewrite Huspk in Honlyk.
    rewrite drop_all sh_skipws_nil Nat.add_0_r in Hpsk.
    assert (Hlowk : forall k : Z, k < 8208 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    assert (Hbufk : forall k : Z,
              sb <= k < sb + Z.of_nat (length bs) + 1 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    assert (Hdomk : forall k : Z, is_Some (M !! k) -> is_Some (Mk !! k))
      by (intros k Hk; exact (proj1 Honlyk k (Hdomx k Hk))).
    assert (Hprek : sh_parse_pre pt hbase hlen Mk sb bs sp0 416).
    { apply (parse_pre_move Mx Mk sb bs sp0 sp0 416 416).
      - exact (proj1 Honlyk).
      - exact Hlowk.
      - exact Hbufk.
      - exact Hfrz.
      - exact Hbufz.
      - exact Hprex. }
    pose proof Hprek as (_ & Hgk & _ & _ & _ & _ & _ & _).
    assert (HfK : uv_stack pt Mk sp0 48)
      by exact (stk_dom M Mk sp0 48 Hdomk Hst48).
    assert (Hnodek : forall k : Z, cmd <= k < cmd + 168 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    assert (Hhighk : forall k : Z,
              uint sp0 - 48 <= k < uint sp0 -> Mk !! k = Mx !! k)
      by (intros k Hk;
          exact (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   ltac:(lia) ltac:(lia))).
    (* ---- 0x724  c.bnez a0,0x706 -- NOT taken ---- *)
    assert (Htkk : false = neq_vec (r1 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0k. unfold neq_vec.
      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    assert (Htgtk : (mword_of_int 0x706 : mword 64)
                    = add_vec (mword_of_int 0x724)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 241 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cbnez C pt Psh Mk r1 (mword_of_int 0x724)
              (mword_of_int 241 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x706)
              (ui_sh_724 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; reflexivity) Htkk Htgtk
              ltac:(intro Hx; discriminate) with "Hcg Hpc").
    iIntros (CIDbz) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x724 : mword 64) 2
                      = mword_of_int 0x726)) in "Hpc".
    (* ---- 0x726  auipc ---- *)
    assert (Hw15 : (mword_of_int 5926 : mword 64)
                  = add_vec (mword_of_int 0x726)
                      (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh Mk r1 (mword_of_int 0x726)
              (mword_of_int 1 : mword 20) a2_idx (mword_of_int 5926)
              (ui_sh_726 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) Hw15 with "Hcg Hpc").
    iIntros (CIDb15) "Hcg Hpc".
    set (r2 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 5926 : mword 64)]> r1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x726 : mword 64) 4
                      = mword_of_int 0x72a)) in "Hpc".
    assert (Hq15 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              r2 !!! Regidx r = r1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r1 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_15 : r2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq15 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_14).
    assert (Hv_s0_idx_15 : r2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq15 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_14).
    assert (Hv_s2_idx_15 : r2 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq15 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_14).
    assert (Hv_s3_idx_15 : r2 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq15 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_14).
    assert (Hv_s1_idx_15 : r2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq15 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_14).
    assert (Hv_s4_idx_15 : r2 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq15 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_14).
    assert (Hv_a2_idx_15 : r2 !!! Regidx a2_idx = (mword_of_int 5926 : mword 64))
      by exact (upd_eq r1 (Regidx a2_idx) _).

    (* ---- 0x72a  addi ---- *)
    assert (Hw16 : (mword_of_int 4912 : mword 64)
                  = add_vec (r2 !!! Regidx a2_idx)
                      (sign_extend' 64 (mword_of_int 3082 : mword 12))).
    { rewrite Hv_a2_idx_15.
      assert (Hc : (sign_extend' 64 (mword_of_int 3082 : mword 12) : mword 64)
                   = mword_of_int (-1014))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh Mk r2 (mword_of_int 0x72a)
              (mword_of_int 3082 : mword 12) a2_idx a2_idx (mword_of_int 4912)
              (ui_sh_72a pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) Hw16 with "Hcg Hpc").
    iIntros (CIDb16) "Hcg Hpc".
    set (r3 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 4912 : mword 64)]> r2).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x72a : mword 64) 4
                      = mword_of_int 0x72e)) in "Hpc".
    assert (Hq16 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              r3 !!! Regidx r = r2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r2 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_16 : r3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq16 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_15).
    assert (Hv_s0_idx_16 : r3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq16 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_15).
    assert (Hv_s2_idx_16 : r3 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq16 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_15).
    assert (Hv_s3_idx_16 : r3 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq16 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_15).
    assert (Hv_s1_idx_16 : r3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq16 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_15).
    assert (Hv_s4_idx_16 : r3 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq16 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_15).
    assert (Hv_a2_idx_16 : r3 !!! Regidx a2_idx = (mword_of_int 4912 : mword 64))
      by exact (upd_eq r2 (Regidx a2_idx) _).

    (* ---- 0x72e  c.mv ---- *)
    assert (Hw17 : (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
                  = add_vec zero_reg (r3 !!! Regidx s3_idx))
      by (rewrite Hv_s3_idx_16 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mk r3 (mword_of_int 0x72e)
              a1_idx s3_idx (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)
              (ui_sh_72e pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) Hw17 with "Hcg Hpc").
    iIntros (CIDb17) "Hcg Hpc".
    set (r4 := <[Regidx a1_idx := regval_into_reg (mword_of_int (sb + Z.of_nat (length bs)) : mword 64)]> r3).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x72e : mword 64) 2
                      = mword_of_int 0x730)) in "Hpc".
    assert (Hq17 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              r4 !!! Regidx r = r3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r3 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_17 : r4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq17 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_16).
    assert (Hv_s0_idx_17 : r4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq17 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_16).
    assert (Hv_s2_idx_17 : r4 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq17 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_16).
    assert (Hv_s3_idx_17 : r4 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq17 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_16).
    assert (Hv_s1_idx_17 : r4 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq17 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_16).
    assert (Hv_s4_idx_17 : r4 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq17 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_16).
    assert (Hv_a2_idx_17 : r4 !!! Regidx a2_idx = (mword_of_int 4912 : mword 64))
      by (rewrite (Hq17 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_16).
    assert (Hv_a1_idx_17 : r4 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq r3 (Regidx a1_idx) _).

    (* ---- 0x730  c.mv ---- *)
    assert (Hw18 : (mword_of_int psaddr : mword 64)
                  = add_vec zero_reg (r4 !!! Regidx s2_idx))
      by (rewrite Hv_s2_idx_17 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mk r4 (mword_of_int 0x730)
              a0_idx s2_idx (mword_of_int psaddr : mword 64)
              (ui_sh_730 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) Hw18 with "Hcg Hpc").
    iIntros (CIDb18) "Hcg Hpc".
    set (r5 := <[Regidx a0_idx := regval_into_reg (mword_of_int psaddr : mword 64)]> r4).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x730 : mword 64) 2
                      = mword_of_int 0x732)) in "Hpc".
    assert (Hq18 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              r5 !!! Regidx r = r4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r4 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_18 : r5 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq18 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_17).
    assert (Hv_s0_idx_18 : r5 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq18 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_17).
    assert (Hv_s2_idx_18 : r5 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq18 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_17).
    assert (Hv_s3_idx_18 : r5 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq18 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_17).
    assert (Hv_s1_idx_18 : r5 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq18 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_17).
    assert (Hv_s4_idx_18 : r5 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq18 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_17).
    assert (Hv_a2_idx_18 : r5 !!! Regidx a2_idx = (mword_of_int 4912 : mword 64))
      by (rewrite (Hq18 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_17).
    assert (Hv_a1_idx_18 : r5 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq18 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_17).
    assert (Hv_a0_idx_18 : r5 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by exact (upd_eq r4 (Regidx a0_idx) _).

    (* ---- 0x732  jal ra, 0x448 ---- *)
    assert (Ht19 : (mword_of_int 0x448 : mword 64)
                   = add_vec (mword_of_int 0x732)
                       (sign_extend' 64 (mword_of_int 2096406 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hl19 : (mword_of_int 0x736 : mword 64)
                   = add_vec_int (mword_of_int 0x732 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh Mk r5 (mword_of_int 0x732)
              (mword_of_int 2096406 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x736)
              (ui_sh_732 pt Mk Hltext (sh_img_text Mk Hgk))
              ltac:(vm_compute; discriminate) Ht19 Hl19
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDb19) "Hcg Hpc".
    set (r6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x736 : mword 64)]> r5).
    assert (Hq19 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              r6 !!! Regidx r = r5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r5 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_19 : r6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq19 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_18).
    assert (Hv_s0_idx_19 : r6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq19 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_18).
    assert (Hv_s2_idx_19 : r6 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq19 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_18).
    assert (Hv_s3_idx_19 : r6 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq19 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_18).
    assert (Hv_s1_idx_19 : r6 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq19 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_18).
    assert (Hv_s4_idx_19 : r6 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq19 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_18).
    assert (Hv_a2_idx_19 : r6 !!! Regidx a2_idx = (mword_of_int 4912 : mword 64))
      by (rewrite (Hq19 a2_idx ltac:(vm_compute; discriminate)); exact Hv_a2_idx_18).
    assert (Hv_a1_idx_19 : r6 !!! Regidx a1_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq19 a1_idx ltac:(vm_compute; discriminate)); exact Hv_a1_idx_18).
    assert (Hv_a0_idx_19 : r6 !!! Regidx a0_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq19 a0_idx ltac:(vm_compute; discriminate)); exact Hv_a0_idx_18).
    assert (Hv_ra_idx_19 : r6 !!! Regidx ra_idx = (mword_of_int 0x736 : mword 64))
      by exact (upd_eq r5 (Regidx ra_idx) _).
    (* ---- 0x448  peek(ps, es, ";") -- 0, so [listcmd] is unreachable ---- *)
    assert (HpreP2 : sh_parse_pre pt hbase hlen Mk sb bs
                       (mword_of_int (uint sp0 - 48) : mword 64) 80).
    { apply (parse_pre_move Mk Mk sb bs sp0 (mword_of_int (uint sp0 - 48))
               416 80).
      - intros k H; exact H.
      - intros k _; reflexivity.
      - intros k _; reflexivity.
      - rewrite Huspk. lia.
      - rewrite Huspk. lia.
      - exact Hprek. }
    assert (HstP2 : uv_stack pt Mk (mword_of_int (uint sp0 - 48)) 80)
      by exact (stk_dom M Mk _ 80 Hdomk Hstpk80).
    assert (HcellP2 : sh_ptr_cell pt Mk psaddr (sb + Z.of_nat (length bs))
                        (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (mk_ptr_cell Mk psaddr (sb + Z.of_nat (length bs))
                  (mword_of_int (uint sp0 - 48)) Hpsk
                  (uv_rd_dom pt M Mk psaddr 8 Hdomk Hcrd)
                  (uv_wr_dom pt M Mk psaddr 8 Hdomk Hcwr) Hcal
                  ltac:(rewrite Huspk; lia)
                  ltac:(change (2 ^ 38) with 274877906944; lia)).
    assert (Htbhi2 : 4912 + Z.of_nat (length sh_tb_semi) + 1 <= 8192)
      by (rewrite sh_tb_semi_len; lia).
    assert (Htbfr2 : 4912 + Z.of_nat (length sh_tb_semi) + 1
                     <= uint (mword_of_int (uint sp0 - 48) : mword 64) - 80)
      by (rewrite Huspk sh_tb_semi_len; lia).
    assert (Hret2k2 : is_aligned_vaddr (Virtaddr (r6 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hv_ra_idx_19; vm_compute; reflexivity).
    iApply (wp_sh_peek_zero CIDb19 Mk r6 (mword_of_int (uint sp0 - 48))
              psaddr sb 4912 bs (length bs) sh_tb_semi
              HpreP2 Hv_csp_rs1_19 HstP2 Hv_a0_idx_19 Hv_a1_idx_19 Hv_a2_idx_19
              HcellP2 ltac:(lia) ltac:(lia) Htbhi2 Htbfr2
              sh_tb_semi_data sh_tb_semi_sym Hret2k2
              with "Hcg Hpc [Hcont Hbrk]").
    iIntros (CIDb20 t1 Mz) "%Hcsk2 %Ha0k2 %Hpsk2 %Honlyk2 Hcg Hpc".
    iEval (rewrite Hv_ra_idx_19) in "Hpc".
    assert (Hv_csp_rs1_20 : t1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hcsk2 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hv_csp_rs1_19).
    assert (Hv_s0_idx_20 : t1 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcsk2 s0_idx ltac:(vm_compute; reflexivity)); exact Hv_s0_idx_19).
    assert (Hv_s2_idx_20 : t1 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hcsk2 s2_idx ltac:(vm_compute; reflexivity)); exact Hv_s2_idx_19).
    assert (Hv_s3_idx_20 : t1 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcsk2 s3_idx ltac:(vm_compute; reflexivity)); exact Hv_s3_idx_19).
    assert (Hv_s1_idx_20 : t1 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcsk2 s1_idx ltac:(vm_compute; reflexivity)); exact Hv_s1_idx_19).
    assert (Hv_s4_idx_20 : t1 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hcsk2 s4_idx ltac:(vm_compute; reflexivity)); exact Hv_s4_idx_19).
    rewrite Huspk in Honlyk2.
    rewrite drop_all sh_skipws_nil Nat.add_0_r in Hpsk2.
    assert (Hlowz : forall k : Z, k < 8208 -> Mz !! k = Mk !! k)
      by (intros k Hk;
          exact (win2_out Mk Mz psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk2
                   ltac:(lia) ltac:(lia))).
    assert (Hbufz2 : forall k : Z,
              sb <= k < sb + Z.of_nat (length bs) + 1 -> Mz !! k = Mk !! k)
      by (intros k Hk;
          exact (win2_out Mk Mz psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk2
                   ltac:(lia) ltac:(lia))).
    assert (Hdomz : forall k : Z, is_Some (M !! k) -> is_Some (Mz !! k))
      by (intros k Hk; exact (proj1 Honlyk2 k (Hdomk k Hk))).
    assert (Hprez : sh_parse_pre pt hbase hlen Mz sb bs sp0 416).
    { apply (parse_pre_move Mk Mz sb bs sp0 sp0 416 416).
      - exact (proj1 Honlyk2).
      - exact Hlowz.
      - exact Hbufz2.
      - exact Hfrz.
      - exact Hbufz.
      - exact Hprek. }
    pose proof Hprez as (_ & Hgz & _ & _ & _ & _ & _ & _).
    assert (HfZ : uv_stack pt Mz sp0 48)
      by exact (stk_dom M Mz sp0 48 Hdomz Hst48).
    assert (Hnodez : forall k : Z, cmd <= k < cmd + 168 -> Mz !! k = Mk !! k)
      by (intros k Hk;
          exact (win2_out Mk Mz psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk2
                   ltac:(lia) ltac:(lia))).
    assert (Hhighz : forall k : Z,
              uint sp0 - 48 <= k < uint sp0 -> Mz !! k = Mk !! k)
      by (intros k Hk;
          exact (win2_out Mk Mz psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk2
                   ltac:(lia) ltac:(lia))).
    (* ---- 0x736  c.bnez a0,0x74a -- NOT taken ---- *)
    assert (Htkk2 : false = neq_vec (t1 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0k2. unfold neq_vec.
      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    assert (Htgtk2 : (mword_of_int 0x74a : mword 64)
                     = add_vec (mword_of_int 0x736)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 10 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cbnez C pt Psh Mz t1 (mword_of_int 0x736)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x74a)
              (ui_sh_736 pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; reflexivity) Htkk2 Htgtk2
              ltac:(intro Hx; discriminate) with "Hcg Hpc").
    iIntros (CIDbz2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x736 : mword 64) 2
                      = mword_of_int 0x738)) in "Hpc".
    (* ---- 0x738  c.mv ---- *)
    assert (Hw21 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (t1 !!! Regidx s1_idx))
      by (rewrite Hv_s1_idx_20 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mz t1 (mword_of_int 0x738)
              a0_idx s1_idx (mword_of_int cmd : mword 64)
              (ui_sh_738 pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) Hw21 with "Hcg Hpc").
    iIntros (CIDr0) "Hcg Hpc".
    set (t2 := <[Regidx a0_idx := regval_into_reg (mword_of_int cmd : mword 64)]> t1).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x738 : mword 64) 2
                      = mword_of_int 0x73a)) in "Hpc".
    assert (Hq21 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              t2 !!! Regidx r = t1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne t1 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hv_csp_rs1_21 : t2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 48) : mword 64))
      by (rewrite (Hq21 csp_rs1 ltac:(vm_compute; discriminate)); exact Hv_csp_rs1_20).
    assert (Hv_s0_idx_21 : t2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hq21 s0_idx ltac:(vm_compute; discriminate)); exact Hv_s0_idx_20).
    assert (Hv_s2_idx_21 : t2 !!! Regidx s2_idx = (mword_of_int psaddr : mword 64))
      by (rewrite (Hq21 s2_idx ltac:(vm_compute; discriminate)); exact Hv_s2_idx_20).
    assert (Hv_s3_idx_21 : t2 !!! Regidx s3_idx = (mword_of_int (sb + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hq21 s3_idx ltac:(vm_compute; discriminate)); exact Hv_s3_idx_20).
    assert (Hv_s1_idx_21 : t2 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hq21 s1_idx ltac:(vm_compute; discriminate)); exact Hv_s1_idx_20).
    assert (Hv_s4_idx_21 : t2 !!! Regidx s4_idx = (mword_of_int 4904 : mword 64))
      by (rewrite (Hq21 s4_idx ltac:(vm_compute; discriminate)); exact Hv_s4_idx_20).
    assert (Hv_a0_idx_21 : t2 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq t1 (Regidx a0_idx) _).
    assert (HhiC : forall k : Z,
              uint sp0 - 48 <= k < uint sp0 -> Mz !! k = P6 !! k).
    { intros k Hk. rewrite (Hhighz k Hk) (Hhighk k Hk). exact (Hhighx k Hk). }
    assert (HbCra : uM_bytes Mz (uint sp0 - 48 + 40) 8 (p1 !!! Regidx ra_idx)).
    { apply (bytes_eq8 P6 Mz (uint sp0 - 48 + 40));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs0 : uM_bytes Mz (uint sp0 - 48 + 32) 8 (p1 !!! Regidx s0_idx)).
    { apply (bytes_eq8 P6 Mz (uint sp0 - 48 + 32));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs1 : uM_bytes Mz (uint sp0 - 48 + 24) 8 (p1 !!! Regidx s1_idx)).
    { apply (bytes_eq8 P6 Mz (uint sp0 - 48 + 24));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs2 : uM_bytes Mz (uint sp0 - 48 + 16) 8 (p1 !!! Regidx s2_idx)).
    { apply (bytes_eq8 P6 Mz (uint sp0 - 48 + 16));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs3 : uM_bytes Mz (uint sp0 - 48 + 8) 8 (p1 !!! Regidx s3_idx)).
    { apply (bytes_eq8 P6 Mz (uint sp0 - 48 + 8));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (HbCs4 : uM_bytes Mz (uint sp0 - 48 + 0) 8 (p1 !!! Regidx s4_idx)).
    { apply (bytes_eq8 P6 Mz (uint sp0 - 48 + 0));
        [ intros k Hk; apply HhiC; lia | ].
      unfold P6, P5, P4, P3, P2, P1.
      repeat (apply st8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    (* ---- 0x73a  c.ldsp ra,40(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr0 Psh Mz t2 sp0 (mword_of_int 0x73a)
              (mword_of_int 5 : mword 6) ra_idx 48 40 (p1 !!! Regidx ra_idx)
              (ui_sh_73a pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) HfZ
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hv_csp_rs1_21
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mz (uint sp0 - 48 + 40)
                        (p1 !!! Regidx ra_idx) HbCra))
              with "Hcg Hpc").
    iIntros (CIDr1) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x73a : mword 64) 2
                      = mword_of_int 0x73c)) in "Hpc".
    set (R1 := <[Regidx ra_idx := regval_into_reg (p1 !!! Regidx ra_idx)]> t2).
    assert (HspR1 : R1 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne t2 (Regidx ra_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) Hv_csp_rs1_21).
    assert (Hvra1 : R1 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (upd_eq t2 (Regidx ra_idx) _).

    (* ---- 0x73c  c.ldsp s0,32(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr1 Psh Mz R1 sp0 (mword_of_int 0x73c)
              (mword_of_int 4 : mword 6) s0_idx 48 32 (p1 !!! Regidx s0_idx)
              (ui_sh_73c pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) HfZ
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mz (uint sp0 - 48 + 32)
                        (p1 !!! Regidx s0_idx) HbCs0))
              with "Hcg Hpc").
    iIntros (CIDr2) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x73c : mword 64) 2
                      = mword_of_int 0x73e)) in "Hpc".
    set (R2 := <[Regidx s0_idx := regval_into_reg (p1 !!! Regidx s0_idx)]> R1).
    assert (HspR2 : R2 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R1 (Regidx s0_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR1).
    assert (Hvs02 : R2 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (upd_eq R1 (Regidx s0_idx) _).
    assert (Hvra2 : R2 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R1 (Regidx s0_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra1).

    (* ---- 0x73e  c.ldsp s1,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr2 Psh Mz R2 sp0 (mword_of_int 0x73e)
              (mword_of_int 3 : mword 6) s1_idx 48 24 (p1 !!! Regidx s1_idx)
              (ui_sh_73e pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) HfZ
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mz (uint sp0 - 48 + 24)
                        (p1 !!! Regidx s1_idx) HbCs1))
              with "Hcg Hpc").
    iIntros (CIDr3) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x73e : mword 64) 2
                      = mword_of_int 0x740)) in "Hpc".
    set (R3 := <[Regidx s1_idx := regval_into_reg (p1 !!! Regidx s1_idx)]> R2).
    assert (HspR3 : R3 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R2 (Regidx s1_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR2).
    assert (Hvs13 : R3 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (upd_eq R2 (Regidx s1_idx) _).
    assert (Hvra3 : R3 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R2 (Regidx s1_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra2).
    assert (Hvs03 : R3 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R2 (Regidx s1_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs02).

    (* ---- 0x740  c.ldsp s2,16(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr3 Psh Mz R3 sp0 (mword_of_int 0x740)
              (mword_of_int 2 : mword 6) s2_idx 48 16 (p1 !!! Regidx s2_idx)
              (ui_sh_740 pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) HfZ
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mz (uint sp0 - 48 + 16)
                        (p1 !!! Regidx s2_idx) HbCs2))
              with "Hcg Hpc").
    iIntros (CIDr4) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x740 : mword 64) 2
                      = mword_of_int 0x742)) in "Hpc".
    set (R4 := <[Regidx s2_idx := regval_into_reg (p1 !!! Regidx s2_idx)]> R3).
    assert (HspR4 : R4 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR3).
    assert (Hvs24 : R4 !!! Regidx s2_idx = p1 !!! Regidx s2_idx)
      by exact (upd_eq R3 (Regidx s2_idx) _).
    assert (Hvra4 : R4 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra3).
    assert (Hvs04 : R4 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs03).
    assert (Hvs14 : R4 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne R3 (Regidx s2_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs13).

    (* ---- 0x742  c.ldsp s3,8(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr4 Psh Mz R4 sp0 (mword_of_int 0x742)
              (mword_of_int 1 : mword 6) s3_idx 48 8 (p1 !!! Regidx s3_idx)
              (ui_sh_742 pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) HfZ
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mz (uint sp0 - 48 + 8)
                        (p1 !!! Regidx s3_idx) HbCs3))
              with "Hcg Hpc").
    iIntros (CIDr5) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x742 : mword 64) 2
                      = mword_of_int 0x744)) in "Hpc".
    set (R5 := <[Regidx s3_idx := regval_into_reg (p1 !!! Regidx s3_idx)]> R4).
    assert (HspR5 : R5 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR4).
    assert (Hvs35 : R5 !!! Regidx s3_idx = p1 !!! Regidx s3_idx)
      by exact (upd_eq R4 (Regidx s3_idx) _).
    assert (Hvra5 : R5 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra4).
    assert (Hvs05 : R5 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs04).
    assert (Hvs15 : R5 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs14).
    assert (Hvs25 : R5 !!! Regidx s2_idx = p1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R4 (Regidx s3_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs24).

    (* ---- 0x744  c.ldsp s4,0(sp) ---- *)
    iApply (wp_uv_frame_load C pt CIDr5 Psh Mz R5 sp0 (mword_of_int 0x744)
              (mword_of_int 0 : mword 6) s4_idx 48 0 (p1 !!! Regidx s4_idx)
              (ui_sh_744 pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) HfZ
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) HspR5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (eq_sym (word_of_bytes8 Mz (uint sp0 - 48 + 0)
                        (p1 !!! Regidx s4_idx) HbCs4))
              with "Hcg Hpc").
    iIntros (CIDr6) "Hcg Hpc".
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x744 : mword 64) 2
                      = mword_of_int 0x746)) in "Hpc".
    set (R6 := <[Regidx s4_idx := regval_into_reg (p1 !!! Regidx s4_idx)]> R5).
    assert (HspR6 : R6 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)) HspR5).
    assert (Hvs46 : R6 !!! Regidx s4_idx = p1 !!! Regidx s4_idx)
      by exact (upd_eq R5 (Regidx s4_idx) _).
    assert (Hvra6 : R6 !!! Regidx ra_idx = p1 !!! Regidx ra_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx ra_idx) _
                           ltac:(vm_compute; discriminate)) Hvra5).
    assert (Hvs06 : R6 !!! Regidx s0_idx = p1 !!! Regidx s0_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s0_idx) _
                           ltac:(vm_compute; discriminate)) Hvs05).
    assert (Hvs16 : R6 !!! Regidx s1_idx = p1 !!! Regidx s1_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)) Hvs15).
    assert (Hvs26 : R6 !!! Regidx s2_idx = p1 !!! Regidx s2_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)) Hvs25).
    assert (Hvs36 : R6 !!! Regidx s3_idx = p1 !!! Regidx s3_idx)
      by exact (eq_trans (upd_ne R5 (Regidx s4_idx) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)) Hvs35).

    assert (HpresR : forall r : mword 5,
              Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx ->
              Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx ->
              Regidx r <> Regidx s4_idx ->
              R6 !!! Regidx r = t2 !!! Regidx r).
    { intros r W1 W2 W3 W4 W5 W6.
      rewrite (upd_ne R5 (Regidx s4_idx) (Regidx r) _ W6).
      rewrite (upd_ne R4 (Regidx s3_idx) (Regidx r) _ W5).
      rewrite (upd_ne R3 (Regidx s2_idx) (Regidx r) _ W4).
      rewrite (upd_ne R2 (Regidx s1_idx) (Regidx r) _ W3).
      rewrite (upd_ne R1 (Regidx s0_idx) (Regidx r) _ W2).
      exact (upd_ne t2 (Regidx ra_idx) (Regidx r) _ W1). }
    (* ---- 0x746  c.addi16sp sp,sp,48 ---- *)
    assert (Hwsp2 : sp0 = add_vec (R6 !!! Regidx csp_rs1)
                            (sign_extend' 64
                               (caddi16sp_imm (mword_of_int 3 : mword 6)))).
    { rewrite HspR6.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))
                    : mword 64) = mword_of_int 48)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 48 + 48) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh Mz R6 (mword_of_int 0x746)
              (mword_of_int 3 : mword 6) sp0
              (ui_sh_746 pt Mz Hltext (sh_img_text Mz Hgz)) Hwsp2
              with "Hcg Hpc").
    iIntros (CIDf) "Hcg Hpc".
    set (cF := <[Regidx csp_rs1 := regval_into_reg sp0]> R6).
    iEval (rewrite (ltac:(apply bv_eq; vm_compute; reflexivity)
                    : add_vec_int (mword_of_int 0x746 : mword 64) 2
                      = mword_of_int 0x748)) in "Hpc".
    (* ---- 0x748  c.jr ra ---- *)
    assert (HraF : cF !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne R6 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite Hvra6. exact (Hq1 ra_idx ltac:(vm_compute; discriminate)). }
    assert (Htgtf : (m !!! Regidx ra_idx) = ret_pc (cF !!! Regidx ra_idx)).
    { rewrite HraF. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh Mz cF (mword_of_int 0x748)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_748 pt Mz Hltext (sh_img_text Mz Hgz))
              ltac:(vm_compute; discriminate) Htgtf with "Hcg Hpc").
    iIntros (CIDfz) "Hcg Hpc".
    assert (Ha0F : cF !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { rewrite (upd_ne R6 (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HpresR a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hv_a0_idx_21. }
    assert (HonlyF : uM_only_in M Mz
              [(hbase, 65536); (SH_FREEP, 8); (SH_BASE, 16); (psaddr, 8);
               (uint sp0 - 416, 416)]).
    { apply (win5_in M Mz hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
               (uint sp0 - 416) 416).
      - exact Hdomz.
      - intros k W1 W2 W3 W4 W5.
        rewrite (win2_out Mk Mz psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk2
                   W4 ltac:(lia)).
        rewrite (win2_out Mx Mk psaddr 8 (uint sp0 - 48 - 80) 80 k Honlyk
                   W4 ltac:(lia)).
        rewrite (win5_out P6 Mx hbase 65536 SH_FREEP 8 SH_BASE 16 psaddr 8
                   (uint sp0 - 48 - 368) 368 k Honlyx W1 W2 W3 W4 ltac:(lia)).
        exact (proj2 HoP6 k ltac:(lia)). }
    iApply ("Hcont" $! CIDfz cF Mz cmd with
              "[] [] [] [] [] [] [] [] Hbrk Hcg Hpc").
    - (* ucallee_saved *)
      iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Dsp ].
      { rewrite Esp. rewrite (upd_eq R6 (Regidx csp_rs1) _). symmetry. exact Hsp. }
      rewrite (upd_ne R6 (Regidx csp_rs1) (Regidx r) _ Dsp).
      destruct (decide (Regidx r = Regidx s0_idx)) as [ E0 | D0 ].
      { rewrite E0 Hvs06. exact (Hq1 s0_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s1_idx)) as [ E1 | D1 ].
      { rewrite E1 Hvs16. exact (Hq1 s1_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s2_idx)) as [ E2 | D2 ].
      { rewrite E2 Hvs26. exact (Hq1 s2_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s3_idx)) as [ E3 | D3 ].
      { rewrite E3 Hvs36. exact (Hq1 s3_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s4_idx)) as [ E4 | D4 ].
      { rewrite E4 Hvs46. exact (Hq1 s4_idx ltac:(vm_compute; discriminate)). }
      assert (Dra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Da2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HpresR r Dra D0 D1 D2 D3 D4).
      rewrite (Hq21 r Da0) (Hcsk2 r Hr) (Hq19 r Dra) (Hq18 r Da0) (Hq17 r Da1)
              (Hq16 r Da2) (Hq15 r Da2) (Hcsk r Hr) (Hq13 r Dra) (Hq12 r Da0)
              (Hq11 r Da1) (Hq10 r Da2) (Hq9 r D4) (Hq8 r D4) (Hq7 r D1)
              (Hcsx r Hr) (Hq5 r Dra) (Hq4 r D3) (Hq3 r D2) (Hq2 r D0).
      exact (Hq1 r Dsp).
    - iPureIntro. exact Ha0F.
    - iPureIntro. exact Hcmdv.
    - iPureIntro. apply (bytes_eqk Mk Mz cmd 4%nat);
        [ intros j Hj; apply Hnodez; lia | ].
      apply (bytes_eqk Mx Mk cmd 4%nat);
        [ intros j Hj; apply Hnodek; lia | exact Htypex ].
    - iPureIntro. destruct Hargx as (Ha & Hb & Hc). split_and!.
      + intros i t Hi. destruct (Ha i t Hi) as (Hb1 & Hb2).
        assert (Hil : (i < length toks)%nat) by exact (lookup_lt_Some toks i t Hi).
        split.
        * apply (bytes_eq8 Mk Mz (cmd + 8 + 8 * Z.of_nat i));
            [ intros j Hj; apply Hnodez; lia | ].
          apply (bytes_eq8 Mx Mk (cmd + 8 + 8 * Z.of_nat i));
            [ intros j Hj; apply Hnodek; lia | exact Hb1 ].
        * apply (bytes_eq8 Mk Mz (cmd + 88 + 8 * Z.of_nat i));
            [ intros j Hj; apply Hnodez; lia | ].
          apply (bytes_eq8 Mx Mk (cmd + 88 + 8 * Z.of_nat i));
            [ intros j Hj; apply Hnodek; lia | exact Hb2 ].
      + apply (bytes_eq8 Mk Mz (cmd + 8 + 8 * Z.of_nat (length toks)));
          [ intros j Hj; apply Hnodez; lia | ].
        apply (bytes_eq8 Mx Mk (cmd + 8 + 8 * Z.of_nat (length toks)));
          [ intros j Hj; apply Hnodek; lia | exact Hb ].
      + apply (bytes_eq8 Mk Mz (cmd + 88 + 8 * Z.of_nat (length toks)));
          [ intros j Hj; apply Hnodez; lia | ].
        apply (bytes_eq8 Mx Mk (cmd + 88 + 8 * Z.of_nat (length toks)));
          [ intros j Hj; apply Hnodek; lia | exact Hc ].
    - iPureIntro. exact Hpsk2.
    - iPureIntro. exact (uv_rd_dom pt Mk Mz cmd SH_EXECCMD_SZ
                           (proj1 Honlyk2)
                           (uv_rd_dom pt Mx Mk cmd SH_EXECCMD_SZ
                              (proj1 Honlyk) Hrdx)).
    - iPureIntro. exact HonlyF.
  Qed.

End UProofShParse.
