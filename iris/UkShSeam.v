(* ===================================================================== *)
(* UkShSeam.v -- THE SEAM AND THE CHILD AT THE REFERENCE PARSER, ONCE     *)
(* (design/user-once.md SS2, worklist A3a).                               *)
(*                                                                        *)
(* Below the parser theorem ([UkShParser.wp_ref_parser]) sat three copies *)
(* of the same two things, one per line shape:                            *)
(*                                                                        *)
(*   the SEAM   -- the parser's tree [UkShParse.ushp_tree s0 p t], owned   *)
(*                 at [DfracOwn 1] and naming its strings as INDEX PAIRS  *)
(*                 into the line, becomes the runner's persistent tree    *)
(*                 [UkShRun.ush_cmd g p c] over [UserHeap.uarg]s: the     *)
(*                 EXEC node in UkShMain, the REDIR node in UkShRedirSeam, *)
(*                 the PIPE node in UkShPipeSeam;                          *)
(*   the CHILD  -- the forked child's [parsecmd; runcmd] from 0x9c0, one   *)
(*                 walk per shape (UkShMain.wp_kshm_child, UkShRedirSeam.  *)
(*                 wp_kshm_child_redir_g, UkShPipeRound.wp_kshm_child_pipe *)
(*                 -- and two more in UkShEcho and UShPipeChild).           *)
(*                                                                        *)
(* Here each is stated once, over the whole tree, and the three landed    *)
(* statements above this file are corollaries in place.                   *)
(*                                                                        *)
(* (P) THE CUT, READ BACK (pure).  [nulterminate] zeroes the line at every *)
(*     index of [RefParse.ref_nulcut t]; the runner needs each token and   *)
(*     each file name to be a STRING afterwards -- its end byte zero and   *)
(*     no byte of its body zero.  The three landed seams each prove that  *)
(*     from their shape's own separation fact.  The general reason is     *)
(*     LOCAL and needs no ordering of tokens: every cut index is a         *)
(*     token's END, which is the end of the line or a byte the word scan  *)
(*     STOPPED on (blank or symbol), while every body byte is one the     *)
(*     scan ran over (neither) -- so no cut index lands in any body.      *)
(*     [ushp_toks_ok] is that reading of the reference's answer, proved   *)
(*     by the same induction as RefParseSym's [ushp_bounded]; [ushp_cut_ok] *)
(*     is what the seam consumes (its EXEC case is UkShPipeSeam.          *)
(*     ushq_cut_ok, verbatim), and [ushp_cut_ok_of_ref] is the theorem.    *)
(* (V) THE VOCABULARY, moved down from UkShMain SS1-SS3 verbatim (that     *)
(*     file re-exports every name): the persisting of a run, the          *)
(*     symbol-free separation fact, [ush_args], and the EXEC conversion   *)
(*     [ush_cmd_of_ushp_gen] -- which is the general seam's EXEC case.    *)
(* (S) THE SEAM.  [ushcmd_of_tree s0 g t] is the runner's tree read off   *)
(*     the parser's at the cut line [g]; [ush_cmd_of_ushp_tree] converts  *)
(*     [ushp_tree s0 p t] into [ush_cmd g p (ushcmd_of_tree s0 g t)] by   *)
(*     induction on [t] under [ushp_cut_ok] -- all five constructors, no  *)
(*     scope premise -- and [ush_cmd_of_ref] is it at the parser's own    *)
(*     cut.  The node's address bound is read off the run's heap, as the  *)
(*     landed seams read it.                                              *)
(* (C) THE CHILD.  [wp_ref_child]: from 0x9c0 through [parsecmd] (the     *)
(*     parser theorem at [ref_parsecmd len f = Some t], the allocator     *)
(*     chained [ushp_nodes t] calls) and the seam to [runcmd]'s ENTRY,     *)
(*     where the continuation -- the shape's ARM -- takes over with the   *)
(*     runner's tree, the persisted line and the callee-saved file intact. *)
(*     The room is [ushp_room t] over the runner's need.  The three arms   *)
(*     [wp_ref_child_exec] / [_redir] / [_pipe] dispatch on the top        *)
(*     constructor -- runcmd's EXEC arm (UkShDiag.wp_kshr_runcmd_final),   *)
(*     the redirect arm (UkShRedir.wp_kshr_redir_arm_g), the pipe arm      *)
(*     (UkShPipe.wp_kshr_pipe_arm) -- each with the arm's own              *)
(*     continuation as its parameter; the cut is a parameter [g] with its  *)
(*     equation, so a landed statement at its own spelling of the cut is  *)
(*     an instance by [reflexivity]-grade rewriting.                       *)
(* (A) THE ALLOCATOR FROM A FRESH STATE.  [ushm_chain_of_fresh]: [k]       *)
(*     calls out of [UkShMalloc.ushm_fresh] chain to [ushm_one_ge (sz +    *)
(*     65536) (4084 - 12 (k - 1))] -- the first call runs [morecore] and   *)
(*     leaves the 64 KiB chunk minus twelve units, every later call takes  *)
(*     twelve more -- for [1 <= k <= 341] (UkShMalloc.ushm_malloc_le_one   *)
(*     needs twelve units left).  The three landed lines chain 1, 2, 3.    *)
(*                                                                        *)
(* TAINT: nothing new -- the parser theorem's allocator chain premise and *)
(* the arms' own premises.                                                *)
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
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import RefParse.
Require Import RefParseSym.
Require Import UkShRedirs.     (* [ushp_malloc_chain] *)
Require Import UkShParser.     (* [wp_ref_parser], [ushp_zero_at], [ushp_room] *)
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShRedir.      (* the redirect arm *)
Require Import UkShPipe.       (* the pipe arm *)
Require Import UkShMalloc.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Require Import PipeNames.
Require Import UexecRet.     (* [uwait_ans] -- what the pipe arm's two waits answer *)
Local Open Scope Z_scope.
Import Defs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

(* ===================================================================== *)
(* (P) THE CUT, READ BACK -- pure                                          *)
(* ===================================================================== *)

(* a token (q, e) of the line as the word arm of [gettoken] produces it:
   nonempty, inside the line, its body run over by the scan (no blank, no
   symbol), its end where the scan stopped -- the end of the line or a
   blank or symbol byte *)
Definition ref_tok_ok (len : nat) (f : nat -> bv 8) (tk : nat * nat) : Prop :=
  (fst tk < snd tk)%nat /\ (snd tk <= len)%nat
  /\ (forall x : nat, (fst tk <= x < snd tk)%nat ->
        ushp_is_ws (f x) || ushp_is_sym (f x) = false)
  /\ (snd tk = len \/ ushp_is_ws (f (snd tk)) || ushp_is_sym (f (snd tk)) = true).

Definition ref_rr_ok (len : nat) (f : nat -> bv 8) (r : rredir) : Prop :=
  ref_tok_ok len f (rr_q r, rr_eq r).

(* ...over the whole tree: every argument token and every file name *)
Fixpoint ushp_toks_ok (len : nat) (f : nat -> bv 8) (t : ushp_cmd) : Prop :=
  match t with
  | UshpExec toks => Forall (ref_tok_ok len f) toks
  | UshpRedir c q e _ _ => ushp_toks_ok len f c /\ ref_tok_ok len f (q, e)
  | UshpPipe l r => ushp_toks_ok len f l /\ ushp_toks_ok len f r
  | UshpList l r => ushp_toks_ok len f l /\ ushp_toks_ok len f r
  | UshpBack c => ushp_toks_ok len f c
  end.

(* what the seam consumes, per node: each token is inside the line, its
   END byte of the cut line is zero and no byte of its BODY is.  The EXEC
   case is [UkShPipeSeam.ushq_cut_ok]'s body, conjunct for conjunct. *)
Fixpoint ushp_cut_ok (len : nat) (g : nat -> bv 8) (t : ushp_cmd) : Prop :=
  match t with
  | UshpExec toks =>
      (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
         (fst tk < snd tk)%nat /\ (snd tk <= len)%nat)
      /\ (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
            g (snd tk) = ubyte0)
      /\ (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
            forall j : nat, (j < snd tk - fst tk)%nat ->
              g (fst tk + j)%nat <> ubyte0)
  | UshpRedir c q e _ _ =>
      ushp_cut_ok len g c
      /\ ((q < e)%nat /\ (e <= len)%nat)
      /\ g e = ubyte0
      /\ (forall j : nat, (j < e - q)%nat -> g (q + j)%nat <> ubyte0)
  | UshpPipe l r => ushp_cut_ok len g l /\ ushp_cut_ok len g r
  | UshpList l r => ushp_cut_ok len g l /\ ushp_cut_ok len g r
  | UshpBack c => ushp_cut_ok len g c
  end.

(* ---- the scan's two readings --------------------------------------- *)

(* every byte the scan ran over is neither blank nor symbol *)
Lemma ushp_toklen_body (n i x : nat) (f : nat -> bv 8) :
  (x < ushp_toklen n i f)%nat ->
  ushp_is_ws (f (i + x)%nat) || ushp_is_sym (f (i + x)%nat) = false.
Proof using.
  revert i x. induction n as [| n IH ]; intros i x Hx;
    cbn [ushp_toklen] in Hx; [ lia | ].
  destruct (ushp_is_ws (f i) || ushp_is_sym (f i)) eqn:E; [ lia | ].
  destruct x as [| x ].
  - rewrite Nat.add_0_r. exact E.
  - replace (i + S x)%nat with (S i + x)%nat by lia. apply IH. lia.
Qed.

(* the byte a token stops on, when it did not run out of line -- the twin
   of [UkShParse.ushp_skipws_end] (UkShMain SS2, moved) *)
Lemma ushp_toklen_end (n i : nat) (f : nat -> bv 8) :
  (ushp_toklen n i f < n)%nat ->
  ushp_is_ws (f (i + ushp_toklen n i f)%nat)
  || ushp_is_sym (f (i + ushp_toklen n i f)%nat) = true.
Proof using .
  revert i. induction n as [| n IH ]; intros i H.
  - cbn [ushp_toklen] in H. lia.
  - cbn [ushp_toklen] in H |- *.
    destruct (ushp_is_ws (f i) || ushp_is_sym (f i)) eqn:Hw.
    + rewrite Nat.add_0_r. exact Hw.
    + assert (E : (i + S (ushp_toklen n (S i) f))%nat
                  = (S i + ushp_toklen n (S i) f)%nat) by lia.
      rewrite E. apply IH. lia.
Qed.

(* ---- gettoken's word arm produces an ok token ------------------------ *)
Lemma ref_gettoken_word_ok (len : nat) (f : nat -> bv 8) (i q e fin : nat) :
  ref_nonnul len f -> (i <= len)%nat ->
  ref_gettoken len f i = (rt_word, q, e, fin) -> ref_tok_ok len f (q, e).
Proof using.
  intros Hnn Hi H. unfold ref_gettoken in H.
  set (s := ref_skip len f i) in H.
  assert (Hs : (s <= len)%nat) by exact (ref_skip_le len f i Hi).
  destruct (bool_decide (ref_at len f s = ubyte0)) eqn:E0.
  { injection H as Hr _ _ _. exfalso. unfold rt_word in Hr. discriminate Hr. }
  apply bool_decide_eq_false_1 in E0.
  assert (Hlt : (s < len)%nat).
  { destruct (lt_dec s len) as [ | Hge ]; [ assumption | ].
    exfalso. apply E0. exact (ref_at_ge len f s ltac:(lia)). }
  rewrite (ref_at_lt len f s Hlt) in H.
  destruct (bool_decide (f s = rb_gt)) eqn:E1.
  - destruct (bool_decide (ref_at len f (S s) = rb_gt)) eqn:E2;
      injection H as Hr _ _ _; exfalso; vm_compute in Hr; discriminate Hr.
  - destruct (ushp_is_sym (f s)) eqn:Es.
    + injection H as Hr _ _ _. exfalso.
      assert (Ea : f s = Z_to_bv 8 97).
      { apply bv_eq. rewrite Hr. vm_compute. reflexivity. }
      rewrite Ea in Es. vm_compute in Es. discriminate Es.
    + injection H as <- <- _.
      assert (Hws : ushp_is_ws (f s) = false)
        by exact (ref_skip_nows len f i Hi Hlt).
      pose proof (ref_toklen_pos_of len f s Hlt Hws Es) as Hpos.
      pose proof (ushp_toklen_le (len - s) s f) as Hle.
      unfold ref_tok_ok, ref_tokend. cbn [fst snd].
      split_and!.
      * lia.
      * lia.
      * intros x Hx.
        replace x with (s + (x - s))%nat by lia.
        apply (ushp_toklen_body (len - s)). lia.
      * destruct (Nat.lt_ge_cases (ushp_toklen (len - s) s f) (len - s))
          as [ Hl | Hg ].
        -- right. exact (ushp_toklen_end _ _ f Hl).
        -- left. lia.
Qed.

(* ---- through the parser, by the induction RefParseSym's [ushp_bounded]
   family uses -------------------------------------------------------- *)

Lemma ref_redirs_ok (len : nat) (f : nat -> bv 8) (n : nat) :
  ref_nonnul len f ->
  forall (i : nat) (acc rs : list rredir) (fin : nat),
    (i <= len)%nat -> Forall (ref_rr_ok len f) acc ->
    ref_redirs len f n i acc = Some (rs, fin) -> Forall (ref_rr_ok len f) rs.
Proof using.
  intro Hnn. induction n as [| n IH ]; intros i acc rs fin Hi Hacc H;
    [ discriminate H | ].
  cbn [ref_redirs] in H.
  destruct (ref_peek len f i [rb_lt; rb_gt]) as [ hit s ] eqn:Epk.
  destruct hit.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es & _ & _).
    assert (Hs : (s <= len)%nat) by (rewrite Es; exact (ref_skip_le len f i Hi)).
    destruct (ref_gettoken len f s) as [[[ tok q0 ] e0 ] s1 ] eqn:E1.
    destruct (ref_gettoken len f s1) as [[[ t2 q ] e ] s2 ] eqn:E2.
    destruct (bool_decide (t2 = rt_word)) eqn:Ew; [ | discriminate H ].
    apply bool_decide_eq_true_1 in Ew. subst t2.
    assert (Hs1 : (s1 <= len)%nat) by exact (ref_gettoken_fin_le len f s _ _ _ _ Hs E1).
    destruct (ref_gettoken_bounds len f s1 _ _ _ _ Hs1 E2) as (_ & _ & Hs2).
    pose proof (ref_gettoken_word_ok len f s1 q e s2 Hnn Hs1 E2) as Hok.
    destruct (rredir_of tok q e) as [ r | ] eqn:Er; [ | discriminate H ].
    apply (IH s2 (acc ++ [r]) rs fin Hs2); [ | exact H ].
    apply Forall_app_2; [ exact Hacc | ].
    apply Forall_singleton.
    unfold rredir_of in Er.
    destruct (bool_decide (tok = bv_unsigned rb_lt));
      [ injection Er as <-; exact Hok | ].
    destruct (bool_decide (tok = bv_unsigned rb_gt));
      [ injection Er as <-; exact Hok | ].
    destruct (bool_decide (tok = rt_app));
      [ injection Er as <-; exact Hok | discriminate Er ].
  - injection H as <- <-. exact Hacc.
Qed.

Lemma ref_args_ok (len : nat) (f : nat -> bv 8) (n : nat) :
  ref_nonnul len f ->
  forall (i : nat) (toks0 toks : list (nat * nat)) (rs0 rs : list rredir) (fin : nat),
    (i <= len)%nat -> Forall (ref_tok_ok len f) toks0 -> Forall (ref_rr_ok len f) rs0 ->
    ref_args len f n i toks0 rs0 = Some (toks, rs, fin) ->
    Forall (ref_tok_ok len f) toks /\ Forall (ref_rr_ok len f) rs.
Proof using.
  intro Hnn. induction n as [| n IH ]; intros i toks0 toks rs0 rs fin Hi Htoks Hrs H;
    [ discriminate H | ].
  destruct (ref_args_inv len f n i toks0 toks rs0 rs fin Hi H)
    as [ (_ & -> & ->)
       | [ (s & q & e & _ & _ & _ & -> & ->)
         | (s & q & e & s1 & s2 & rs1 & _ & Hs & Eg & Hs1 & _ & Er & Hs2 & Hrec) ] ].
  - exact (conj Htoks Hrs).
  - exact (conj Htoks Hrs).
  - apply (IH s2 (toks0 ++ [(q, e)]) toks (rs0 ++ rs1) rs fin Hs2); [ | | exact Hrec ].
    + apply Forall_app_2; [ exact Htoks | ].
      apply Forall_singleton. exact (ref_gettoken_word_ok len f s q e s1 Hnn Hs Eg).
    + apply Forall_app_2; [ exact Hrs | ].
      exact (ref_redirs_ok len f n Hnn s1 [] rs1 s2 Hs1 (List.Forall_nil _) Er).
Qed.

Lemma ushp_toks_ok_wrap (len : nat) (f : nat -> bv 8) (rs : list rredir) :
  forall c : ushp_cmd,
    ushp_toks_ok len f c -> Forall (ref_rr_ok len f) rs ->
    ushp_toks_ok len f (ref_wrap c rs).
Proof using.
  induction rs as [| r rs IH ]; intros c Hc Hrs; [ exact Hc | ].
  rewrite ref_wrap_cons. apply Forall_cons_1 in Hrs as [ Hr Hrs ].
  apply IH; [ | exact Hrs ]. cbn [ushp_toks_ok]. exact (conj Hc Hr).
Qed.

Lemma ref_parseexec_ok (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) (fin : nat) :
  ref_nonnul len f -> (i <= len)%nat ->
  ref_parseexec len f n i = Some (t, fin) -> ushp_toks_ok len f t.
Proof using.
  intros Hnn Hi H. unfold ref_parseexec in H.
  destruct (ref_peek len f i [rb_lpar]) as [ blk s ] eqn:Epk. destruct blk; [ discriminate H | ].
  assert (Hs : (s <= len)%nat)
    by (rewrite (ref_peek_miss_inv _ _ _ _ _ Epk); exact (ref_skip_le len f i Hi)).
  destruct (ref_redirs len f n s []) as [[ rs1 s1 ] | ] eqn:Er; [ | discriminate H ].
  assert (Hs1 : (s1 <= len)%nat) by exact (ref_redirs_fin_le len f n s [] rs1 s1 Hs Er).
  pose proof (ref_redirs_ok len f n Hnn s [] rs1 s1 Hs (List.Forall_nil _) Er) as Hrs1.
  destruct (ref_args len f n s1 [] rs1) as [[[ toks rs ] s2 ] | ] eqn:Ea; [ | discriminate H ].
  injection H as <- <-.
  destruct (ref_args_ok len f n Hnn s1 [] toks rs1 rs s2 Hs1 (List.Forall_nil _) Hrs1 Ea)
    as (Htoks & Hrs).
  apply ushp_toks_ok_wrap; [ exact Htoks | exact Hrs ].
Qed.

Lemma ref_parsepipe_ok (len : nat) (f : nat -> bv 8) (n : nat) :
  ref_nonnul len f ->
  forall (i : nat) (t : ushp_cmd) (fin : nat),
    (i <= len)%nat -> ref_parsepipe len f n i = Some (t, fin) -> ushp_toks_ok len f t.
Proof using.
  intro Hnn. induction n as [| n IH ]; intros i t fin Hi H; [ discriminate H | ].
  cbn [ref_parsepipe] in H.
  destruct (ref_parseexec len f n i) as [[ t1 s ] | ] eqn:Ex; [ | discriminate H ].
  destruct (ref_parseexec_bounded len f n i t1 s Hi Ex) as (_ & Hs).
  pose proof (ref_parseexec_ok len f n i t1 s Hnn Hi Ex) as Ht1.
  destruct (ref_peek len f s [rb_bar]) as [ bar s1 ] eqn:Epk.
  destruct bar.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es1 & _ & _).
    assert (Hs1 : (s1 <= len)%nat) by (rewrite Es1; exact (ref_skip_le len f s Hs)).
    destruct (ref_gettoken len f s1) as [[[ tok q ] e ] s2 ] eqn:Eg.
    assert (Hs2 : (s2 <= len)%nat) by exact (ref_gettoken_fin_le len f s1 _ _ _ _ Hs1 Eg).
    destruct (ref_parsepipe len f n s2) as [[ r s3 ] | ] eqn:Er; [ | discriminate H ].
    injection H as <- <-.
    exact (conj Ht1 (IH s2 r s3 Hs2 Er)).
  - injection H as <- <-. exact Ht1.
Qed.

Lemma ref_backs_ok (len : nat) (f : nat -> bv 8) (n : nat) :
  forall (i : nat) (t t' : ushp_cmd) (fin : nat),
    (i <= len)%nat -> ushp_toks_ok len f t -> ref_backs len f n i t = Some (t', fin) ->
    ushp_toks_ok len f t'.
Proof using.
  induction n as [| n IH ]; intros i t t' fin Hi Ht H; [ discriminate H | ].
  cbn [ref_backs] in H.
  destruct (ref_peek len f i [rb_amp]) as [ amp s ] eqn:Epk.
  destruct amp.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es & _ & _).
    assert (Hs : (s <= len)%nat) by (rewrite Es; exact (ref_skip_le len f i Hi)).
    destruct (ref_gettoken len f s) as [[[ tok q ] e ] s1 ] eqn:Eg.
    exact (IH s1 (UshpBack t) t' fin (ref_gettoken_fin_le len f s _ _ _ _ Hs Eg) Ht H).
  - injection H as <- <-. exact Ht.
Qed.

Lemma ref_parseline_ok (len : nat) (f : nat -> bv 8) (n : nat) :
  ref_nonnul len f ->
  forall (i : nat) (t : ushp_cmd) (fin : nat),
    (i <= len)%nat -> ref_parseline len f n i = Some (t, fin) -> ushp_toks_ok len f t.
Proof using.
  intro Hnn. induction n as [| n IH ]; intros i t fin Hi H; [ discriminate H | ].
  cbn [ref_parseline] in H.
  destruct (ref_parsepipe len f n i) as [[ t1 s ] | ] eqn:Ep; [ | discriminate H ].
  destruct (ref_parsepipe_bounded len f n i t1 s Hi Ep) as (_ & Hs).
  pose proof (ref_parsepipe_ok len f n Hnn i t1 s Hi Ep) as Ht1.
  destruct (ref_backs len f n s t1) as [[ t2 s1 ] | ] eqn:Eb; [ | discriminate H ].
  destruct (ref_backs_bounded len f n s t1 t2 s1 Hs
              (proj1 (ref_parsepipe_bounded len f n i t1 s Hi Ep)) Eb) as (_ & Hs1).
  pose proof (ref_backs_ok len f n s t1 t2 s1 Hs Ht1 Eb) as Ht2.
  destruct (ref_peek len f s1 [rb_semi]) as [ semi s2 ] eqn:Epk.
  destruct semi.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es2 & _ & _).
    assert (Hs2 : (s2 <= len)%nat) by (rewrite Es2; exact (ref_skip_le len f s1 Hs1)).
    destruct (ref_gettoken len f s2) as [[[ tok q ] e ] s3 ] eqn:Eg.
    assert (Hs3 : (s3 <= len)%nat) by exact (ref_gettoken_fin_le len f s2 _ _ _ _ Hs2 Eg).
    destruct (ref_parseline len f n s3) as [[ r s4 ] | ] eqn:Er; [ | discriminate H ].
    injection H as <- <-.
    exact (conj Ht2 (IH s3 r s4 Hs3 Er)).
  - injection H as <- <-. exact Ht2.
Qed.

Theorem ref_parsecmd_toks_ok (len : nat) (f : nat -> bv 8) (t : ushp_cmd) :
  ref_nonnul len f -> ref_parsecmd len f = Some t -> ushp_toks_ok len f t.
Proof using.
  intros Hnn H. unfold ref_parsecmd in H.
  destruct (ref_parseline len f (ref_fuel len) 0%nat) as [[ t1 s ] | ] eqn:Ep;
    [ | discriminate H ].
  pose proof (ref_parseline_ok len f (ref_fuel len) Hnn 0%nat t1 s ltac:(lia) Ep) as Ht1.
  destruct (ref_peek len f s []) as [ b s1 ].
  destruct (bool_decide (s1 = len)); [ | discriminate H ].
  injection H as <-. exact Ht1.
Qed.

(* ---- every cut index is a token's end: the line's end or a stop byte -- *)
Lemma ref_nulcut_ends (len : nat) (f : nat -> bv 8) (t : ushp_cmd) :
  ushp_toks_ok len f t ->
  forall e : nat, e ∈ ref_nulcut t ->
    (e <= len)%nat /\ (e = len \/ ushp_is_ws (f e) || ushp_is_sym (f e) = true).
Proof using.
  induction t as [ toks | c IH q e0 mode fd | l IHl r IHr | l IHl r IHr | c IH ];
    cbn [ushp_toks_ok ref_nulcut]; intros Hok e He.
  - apply elem_of_list_In, in_map_iff in He. destruct He as (tk & <- & Hin).
    apply elem_of_list_In in Hin.
    destruct (elem_of_list_lookup_1 _ _ Hin) as (i & Hi).
    destruct (Forall_lookup_1 _ _ _ _ Hok Hi) as (_ & Hle & _ & Hend).
    exact (conj Hle Hend).
  - destruct Hok as [ Hc Htk ]. apply elem_of_app in He. destruct He as [ He | He ].
    + exact (IH Hc e He).
    + apply elem_of_list_singleton in He. subst e.
      destruct Htk as (_ & Hle & _ & Hend). exact (conj Hle Hend).
  - destruct Hok as [ Hl Hr ]. apply elem_of_app in He.
    destruct He as [ He | He ]; [ exact (IHl Hl e He) | exact (IHr Hr e He) ].
  - destruct Hok as [ Hl Hr ]. apply elem_of_app in He.
    destruct He as [ He | He ]; [ exact (IHl Hl e He) | exact (IHr Hr e He) ].
  - exact (IH Hok e He).
Qed.

(* the cut leaves a byte alone unless some index lands on it *)
Lemma ushp_zero_at_miss (js : list nat) (g : nat -> bv 8) (j : nat) :
  j ∉ js -> ushp_zero_at js g j = g j.
Proof using.
  revert g. induction js as [| k r IH ]; intros g Hj; [ reflexivity | ].
  unfold ushp_zero_at in IH |- *. cbn [fold_left]. rewrite IH.
  - rewrite /UkShParseCmd.ushp_setb.
    destruct (Nat.eqb j k) eqn:E; [ | reflexivity ].
    exfalso. apply Nat.eqb_eq in E. subst j. apply Hj. apply elem_of_cons. left. reflexivity.
  - intro Hin. apply Hj. apply elem_of_cons. right. exact Hin.
Qed.

(* one ok token, cut at a list of stop indices it ends in *)
Lemma ref_cut_tok_ok (len : nat) (f : nat -> bv 8) (js : list nat) (q e : nat) :
  ref_nonnul len f ->
  (forall x : nat, x ∈ js ->
     (x <= len)%nat /\ (x = len \/ ushp_is_ws (f x) || ushp_is_sym (f x) = true)) ->
  ref_tok_ok len f (q, e) -> e ∈ js ->
  ((q < e)%nat /\ (e <= len)%nat)
  /\ ushp_zero_at js (UkShParseCmd.ushp_ext len f) e = ubyte0
  /\ (forall j : nat, (j < e - q)%nat ->
        ushp_zero_at js (UkShParseCmd.ushp_ext len f) (q + j)%nat <> ubyte0).
Proof using.
  intros Hnn Hjs (Hlt & Hle & Hbody & _) Hin. cbn [fst snd] in Hlt, Hle, Hbody.
  split_and!; [ exact Hlt | exact Hle | exact (ushp_zero_at_hit js _ e Hin) | ].
  intros j Hj.
  rewrite ushp_zero_at_miss.
  - rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((q + j) < len)%nat ltac:(lia)).
    apply Hnn. lia.
  - intro Hx. destruct (Hjs _ Hx) as [ _ [ Heq | Hstop ] ]; [ lia | ].
    rewrite (Hbody (q + j)%nat ltac:(lia)) in Hstop. discriminate Hstop.
Qed.

(* ...and the whole tree, cut at any list of stop indices that has every
   end of the tree in it (the pipe's two sides are cut at ONE list) *)
Lemma ushp_cut_ok_of_toks_ok (len : nat) (f : nat -> bv 8) (js : list nat) :
  ref_nonnul len f ->
  (forall x : nat, x ∈ js ->
     (x <= len)%nat /\ (x = len \/ ushp_is_ws (f x) || ushp_is_sym (f x) = true)) ->
  forall t : ushp_cmd,
    ushp_toks_ok len f t -> (forall e : nat, e ∈ ref_nulcut t -> e ∈ js) ->
    ushp_cut_ok len (ushp_zero_at js (UkShParseCmd.ushp_ext len f)) t.
Proof using.
  intros Hnn Hjs.
  induction t as [ toks | c IH q e mode fd | l IHl r IHr | l IHl r IHr | c IH ];
    cbn [ushp_toks_ok ushp_cut_ok ref_nulcut]; intros Hok Hsub.
  - assert (Htk : forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
              ((fst tk < snd tk)%nat /\ (snd tk <= len)%nat)
              /\ ushp_zero_at js (UkShParseCmd.ushp_ext len f) (snd tk) = ubyte0
              /\ (forall j : nat, (j < snd tk - fst tk)%nat ->
                    ushp_zero_at js (UkShParseCmd.ushp_ext len f) (fst tk + j)%nat
                    <> ubyte0)).
    { intros i tk Hi. destruct tk as [ q e ]. cbn [fst snd].
      apply (ref_cut_tok_ok len f js q e Hnn Hjs (Forall_lookup_1 _ _ _ _ Hok Hi)).
      apply Hsub. apply elem_of_list_In, in_map_iff. exists (q, e).
      split; [ reflexivity | ].
      apply elem_of_list_In. exact (elem_of_list_lookup_2 _ _ _ Hi). }
    split_and!.
    + intros i tk Hi. exact (proj1 (Htk i tk Hi)).
    + intros i tk Hi. exact (proj1 (proj2 (Htk i tk Hi))).
    + intros i tk Hi. exact (proj2 (proj2 (Htk i tk Hi))).
  - destruct Hok as [ Hc Htk ]. split.
    + apply IH; [ exact Hc | ]. intros x Hx. apply Hsub. apply elem_of_app. left. exact Hx.
    + apply (ref_cut_tok_ok len f js q e Hnn Hjs Htk).
      apply Hsub. apply elem_of_app. right. apply elem_of_list_singleton. reflexivity.
  - destruct Hok as [ Hl Hr ].
    split; [ apply IHl; [ exact Hl | ] | apply IHr; [ exact Hr | ] ];
      intros x Hx; apply Hsub; apply elem_of_app; [ left | right ]; exact Hx.
  - destruct Hok as [ Hl Hr ].
    split; [ apply IHl; [ exact Hl | ] | apply IHr; [ exact Hr | ] ];
      intros x Hx; apply Hsub; apply elem_of_app; [ left | right ]; exact Hx.
  - apply IH; [ exact Hok | exact Hsub ].
Qed.

(* THE CUT THEOREM: the line the parser theorem hands back, cut at
   [ref_nulcut t], is readable at every node of [t] *)
Theorem ushp_cut_ok_of_ref (len : nat) (f : nat -> bv 8) (t : ushp_cmd) :
  ref_nonnul len f -> ref_parsecmd len f = Some t ->
  ushp_cut_ok len (ushp_zero_at (ref_nulcut t) (UkShParseCmd.ushp_ext len f)) t.
Proof using.
  intros Hnn Href. pose proof (ref_parsecmd_toks_ok len f t Hnn Href) as Hok.
  apply (ushp_cut_ok_of_toks_ok len f (ref_nulcut t) Hnn
           (ref_nulcut_ends len f t Hok) t Hok).
  intros e He. exact He.
Qed.

(* ===================================================================== *)
(* (V) THE ARGUMENT VECTOR, AND THE RUNNER'S TREE OFF THE PARSER'S         *)
(* ===================================================================== *)

(* THE ARGUMENT VECTOR the runner reads, out of the token boundaries the
   parser recorded: a token (i,j) is the string at [s0+i] of length [j-i],
   whose bytes are the line's and whose terminator is the zero
   [nulterminate] wrote at [j].  (UkShMain SS3, moved.) *)
Definition ush_args (s0 : Z) (g : nat -> bv 8) (toks : list (nat * nat))
    : list uarg :=
  map (fun tk : nat * nat =>
         UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
              (fun j : nat => g (fst tk + j)%nat)) toks.

Lemma ush_args_length (s0 : Z) (g : nat -> bv 8) (toks : list (nat * nat)) :
  length (ush_args s0 g toks) = length toks.
Proof using . unfold ush_args. rewrite length_map. reflexivity. Qed.

Lemma ush_args_lookup (s0 : Z) (g : nat -> bv 8) (toks : list (nat * nat))
    (i : nat) (tk : nat * nat) :
  toks !! i = Some tk ->
  ush_args s0 g toks !! i
  = Some (UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
               (fun j : nat => g (fst tk + j)%nat)).
Proof using . intro Hi. unfold ush_args. rewrite list_lookup_fmap Hi. reflexivity. Qed.

(* THE RUNNER'S TREE, read off the parser's at the cut line [g]: an EXEC
   node's index pairs become its argument vector, a REDIR node's file
   indices its file name as a string, and the shape is kept *)
Fixpoint ushcmd_of_tree (s0 : Z) (g : nat -> bv 8) (t : ushp_cmd) : ushcmd :=
  match t with
  | UshpExec toks => UExec (ush_args s0 g toks)
  | UshpRedir c q e mode fd =>
      URedir (ushcmd_of_tree s0 g c)
             (UArg (s0 + Z.of_nat q) (e - q)%nat (fun j : nat => g (q + j)%nat))
             mode fd
  | UshpPipe l r => UPipe (ushcmd_of_tree s0 g l) (ushcmd_of_tree s0 g r)
  | UshpList l r => UList (ushcmd_of_tree s0 g l) (ushcmd_of_tree s0 g r)
  | UshpBack c => UBack (ushcmd_of_tree s0 g c)
  end.

(* the runner's height IS the parser's *)
Lemma ush_ht_of_tree (s0 : Z) (g : nat -> bv 8) (t : ushp_cmd) :
  ush_ht (ushcmd_of_tree s0 g t) = ushp_ht t.
Proof using.
  induction t as [ toks | c IH q e mode fd | l IHl r IHr | l IHl r IHr | c IH ];
    cbn [ushcmd_of_tree ush_ht ushp_ht]; congruence.
Qed.

Section UkShSeam.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.

  (* the four ghost names a program proof runs at, as every file in the
     lane binds them *)
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_triv]). *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]) -- as
     UkShMain binds it: a SECTION hypothesis the program's kernel-side
     constructor discharges, at the free numbers and no more. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  Local Notation ushp_malloc_chain := (UkShRedirs.ushp_malloc_chain N).
  Local Notation ushp_ext := UkShParseCmd.ushp_ext.

  (* ===================================================================== *)
  (* (V1) PERSISTING A RUN (UkShMain SS1, moved).                            *)
  (*                                                                        *)
  (* [UserHeap.uarea_persist] does this for a MAP; the seam below holds     *)
  (* RUNS, so here are the two run-shaped twins.                            *)
  (* ===================================================================== *)
  Lemma ubytes_persist (g : gname) (a : Z) (n : nat) (f : nat -> bv 8) :
    ubytes g a n f ==∗ ubytesq g DfracDiscarded a n f.
  Proof using .
    iIntros "H". rewrite /ubytes /ubytesq.
    iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iIntros "!>" (i j _) "Hb". rewrite /ubyteq /ubyte.
    iApply (ghost_map_elem_persist with "Hb").
  Qed.

  Lemma uword_persist (g : gname) (a : Z) (w : mword 64) :
    uword g a w ==∗ uwordq g DfracDiscarded a w.
  Proof using .
    iIntros "H". rewrite /uword /uwordq.
    iApply (ubytes_persist g a 8 (nth_byte w) with "H").
  Qed.

  Lemma ustr_persist (g : gname) (a : Z) (n : nat) (f : nat -> bv 8) :
    ustr g (DfracOwn 1) a n f ==∗ ustr g DfracDiscarded a n f.
  Proof using .
    iIntros "(%Hne & %Hlen & Hbs & Hnul)".
    iMod (ubytes_persist g a n f with "Hbs") as "#Hbs".
    iMod (ghost_map_elem_persist with "Hnul") as "#Hnul".
    iModIntro. iSplitR; [ iPureIntro; exact Hne | ].
    iSplitR; [ iPureIntro; exact Hlen | ].
    iSplitR; [ iExact "Hbs" | iExact "Hnul" ].
  Qed.

  (* ===================================================================== *)
  (* (V2) THE TOKEN MODEL, ONE STEP FURTHER: SEPARATION (UkShMain SS2,      *)
  (* moved).  On a symbol-free line no token's end lands inside another    *)
  (* token's body.  The general seam does not need it -- (P) above reads   *)
  (* the same fact off the reference's answer -- but the landed symbol-    *)
  (* free seam and its consumers do.                                        *)
  (* ===================================================================== *)

  (* the fold leaves a byte alone unless some token ends there *)
  Lemma ushp_nulfold_miss (toks : list (nat * nat)) (g : nat -> bv 8) (j : nat) :
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk -> j <> snd tk) ->
    ushp_nulfold toks g j = g j.
  Proof using .
    revert g. induction toks as [| tk r IH ]; intros g Hmiss;
      cbn [ushp_nulfold]; [ reflexivity | ].
    rewrite (IH (ushp_setb g (snd tk) ubyte0)).
    - rewrite /ushp_setb.
      destruct (Nat.eqb j (snd tk)) eqn:E; [ | reflexivity ].
      exfalso. apply Nat.eqb_eq in E.
      exact (Hmiss 0%nat tk eq_refl E).
    - intros i t Hi. exact (Hmiss (S i) t Hi).
  Qed.

  (* THE SEPARATION FACT.  On a symbol-free line, a token's end is either
     the end of the line or a whitespace byte, so the NEXT token starts
     strictly after it -- and therefore no token end falls inside another
     token's body. *)
  Lemma ushp_tokens_gap (len : nat) (f : nat -> bv 8) (off : nat)
      (toks : list (nat * nat)) :
    ushp_no_symbols len f ->
    ushp_tokens len f off toks -> (off <= len)%nat ->
    forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
    forall (j : nat) (tk' : nat * nat), toks !! j = Some tk' ->
    forall x : nat, (fst tk <= x < snd tk)%nat -> x <> snd tk'.
  Proof using .
    intros Hns Htoks. revert Hns.
    induction Htoks as [ off Hnil | off toks k n Hn Htoks IH ];
      intros Hns Hoff i tk Hi j tk' Hj x Hx.
    - destruct i; cbn in Hi; discriminate Hi.
    - (* the head's own bounds, and where the rest starts *)
      assert (Hk : (k <= len - off)%nat) by exact (ushp_skipws_le (len - off) off f).
      assert (Hnle : (n <= len - (off + k))%nat)
        by exact (ushp_toklen_le (len - (off + k)) (off + k) f).
      assert (Hrest : forall (q : nat) (t : nat * nat), toks !! q = Some t ->
                (off + k + n <= fst t < snd t /\ snd t <= len)%nat)
        by (intros q t Hq;
            exact (ushp_tokens_in len f (off + k + n)%nat toks Htoks
                     ltac:(lia) q t Hq)).
      destruct i as [| i ]; cbn [lookup] in Hi.
      + (* x is in the HEAD token's body: [off+k, off+k+n) *)
        injection Hi as <-. cbn [fst snd] in Hx.
        destruct j as [| j ]; cbn [lookup] in Hj.
        * injection Hj as <-. cbn [snd]. lia.
        * destruct (Hrest j tk' Hj) as [Hlo _]. lia.
      + (* x is in a LATER token's body, hence at or above [off+k+n] *)
        destruct (Hrest i tk Hi) as [Hlo _].
        destruct j as [| j ]; cbn [lookup] in Hj.
        * (* the head's end is [off+k+n], and every later token starts
             STRICTLY above it: the head stopped on a whitespace byte (the
             line has no symbol), which the next scan skips *)
          injection Hj as <-. cbn [snd].
          assert (Hgap : forall (q : nat) (t : nat * nat),
                    toks !! q = Some t -> (off + k + n < fst t)%nat).
          { intros q t Hq.
            assert (Hlt : (n < len - (off + k))%nat).
            { destruct (Nat.lt_ge_cases n (len - (off + k))) as [Hc | Hc];
                [ exact Hc | exfalso ].
              destruct (Hrest q t Hq) as [Hlo' Hhi']. lia. }
            pose proof (ushp_toklen_end (len - (off + k)) (off + k) f Hlt) as Hstop.
            assert (Hwsb : ushp_is_ws (f (off + k + n)%nat) = true).
            { apply orb_true_iff in Hstop as [Hw | Hsy]; [ exact Hw | exfalso ].
              assert (Hin : (off + k + n < len)%nat) by lia.
              rewrite (Hns (off + k + n)%nat Hin) in Hsy. discriminate Hsy. }
            destruct toks as [| t0 rest ];
              [ destruct q; cbn in Hq; discriminate Hq | ].
            destruct (ushp_tokens_cons_inv len (off + k + n)%nat f t0 rest Htoks)
              as (Hpos & Ht0 & Hrest').
            assert (Hk0 : (0 < ushp_skipws (len - (off + k + n))
                                 (off + k + n) f)%nat).
            { destruct (len - (off + k + n))%nat as [| mm ] eqn:Em.
              - exfalso. destruct (Hrest q t Hq) as [Hlo2 Hhi2]. lia.
              - cbn [ushp_skipws]. rewrite Hwsb. lia. }
            destruct (Hrest 0%nat t0 eq_refl) as [Hlo0 Hhi0].
            rewrite Ht0 in Hlo0, Hhi0. cbn [fst snd] in Hlo0, Hhi0.
            destruct q as [| q' ]; cbn [lookup] in Hq.
            - injection Hq as <-. rewrite Ht0. cbn [fst]. lia.
            - destruct (ushp_tokens_in len f _ rest Hrest' Hhi0 q' t Hq)
                as [Hlo3 _].
              lia. }
          pose proof (Hgap i tk Hi). lia.
        * (* both tokens are in the tail: the induction hypothesis *)
          exact (IH Hns ltac:(lia) i tk Hi j tk' Hj x Hx).
  Qed.

  (* ===================================================================== *)
  (* (V3) THE EXEC CONVERSION (UkShMain SS3, moved): the parser's NODE is   *)
  (* the runner's TREE, at one EXEC node.                                   *)
  (* ===================================================================== *)

  (* a sub-run of a PERSISTED run -- the discarded twin of                  *)
  (* [UkRunSys.ubytes_split], and easier: a persistent run can be read      *)
  (* wherever it is needed and never has to be given back. *)
  Lemma ubytesq_sub (g : gname) (a : Z) (n : nat) (f : nat -> bv 8)
      (i m : nat) :
    (i + m <= n)%nat ->
    ubytesq g DfracDiscarded a n f -∗
    ubytesq g DfracDiscarded (a + Z.of_nat i) m (fun j => f (i + j)%nat).
  Proof using .
    intros Hle. iIntros "#H". rewrite {2}/ubytesq.
    iApply big_sepL_intro. iIntros "!>" (k j Hkj).
    apply lookup_seq in Hkj as [-> Hlt].
    iDestruct (big_sepL_lookup _ (seq 0 n) (i + k)%nat (i + k)%nat with "H")
      as "Hb"; [ apply lookup_seq; lia | ].
    assert (E : (a + Z.of_nat (i + k))%Z = (a + Z.of_nat i + Z.of_nat k)%Z)
      by lia.
    iEval (rewrite E) in "Hb". iExact "Hb".
  Qed.

  (* one byte of a persisted run *)
  Lemma ubytesq_at (g : gname) (a : Z) (n : nat) (f : nat -> bv 8) (i : nat) :
    (i < n)%nat ->
    ubytesq g DfracDiscarded a n f -∗
    ubyteq g DfracDiscarded (a + Z.of_nat i) (f i).
  Proof using .
    intros Hi. iIntros "#H".
    iDestruct (big_sepL_lookup _ (seq 0 n) i i with "H") as "Hb";
      [ apply lookup_seq; lia | ]. iExact "Hb".
  Qed.

  (* every byte a program owns is inside the user region -- read off the
     run's own heap, and the run survives because the conclusion is pure *)
  Lemma urun_ubytes_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (a : Z) (nb : nat) (fb : nat -> bv 8) :
    urun N h m pc avail -∗ ubytes γd a nb fb -∗
    ⌜ forall j : nat, (j < nb)%nat -> 0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hbs".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
      "(_ & _ & _ & _ & Hheap & _)".
    iDestruct (uheap_ubytes_img γt γd γs M pm sz a nb fb with "Hheap Hbs")
      as %Hall.
    iPureIntro. intros j Hj. exact (proj2 (Hall j Hj)).
  Qed.

  (* THE CONVERSION, at what it actually needs.  The NUL cut enters the     *)
  (* argument only through three facts about the line's bytes -- each       *)
  (* token is inside the line, its END byte is zero, and no byte of its     *)
  (* BODY is -- so those are the premises, and the cut that produced them   *)
  (* is the caller's business.  Every byte of the node is DISCARDED on the  *)
  (* way, which is what makes the tree persistent, hence what lets it cross *)
  (* the fork as a payload.  This is the general seam's EXEC case.          *)
  Lemma ush_cmd_of_ushp_gen (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (s0 p : Z) (len : nat) (g : nat -> bv 8)
      (toks : list (nat * nat)) :
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       (fst tk < snd tk)%nat /\ (snd tk <= len)%nat) ->
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       g (snd tk) = ubyte0) ->
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       forall j : nat, (j < snd tk - fst tk)%nat ->
         g (fst tk + j)%nat <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (* the run is here only to read the node's address bound off the heap *)
    urun N h m pc avail -∗
    ushp_tree N s0 p (UshpExec toks) -∗
    (* the line ALREADY PERSISTED: a caller with a second string to cut out
       of it (the redirect's file name) needs it afterwards, and the cut is
       done by then either way *)
    ubytesq γd DfracDiscarded s0 (S len) g ==∗
    urun N h m pc avail ∗
    ush_cmd γd p (UExec (ush_args s0 g toks)).
  Proof using .
    intros Hin Hend Hbod Hlen31 Hs0 Hs0hi.
    iIntros "Hrun Hnode #Hline".
    iDestruct "Hnode" as "(%Hlt10 & %Hp0 & %Hp8 & [Hty _] & Hargv & _)".
    iDestruct (urun_ubytes_bnd h m pc avail p 4 _ with "Hrun Hty") as %Hpb.
    assert (Hp : 0 < p < 2 ^ 38).
    { split; [ exact Hp0 | ].
      destruct (Hpb 0%nat ltac:(lia)) as [_ Hhi]. lia. }
    iMod (ubytes_persist γd p 4 _ with "Hty") as "#Hty".
    (* ---- the ten argv slots, persisted down to the ones that matter ---- *)
    assert (E10 : (10 = S (length toks) + (10 - S (length toks)))%nat) by lia.
    rewrite E10 seq_app big_sepL_app.
    iDestruct "Hargv" as "[Hargv _]".
    iAssert (|==> [∗ list] i ∈ seq 0 (S (length toks)),
               uwordq γd DfracDiscarded (p + 8 + 8 * Z.of_nat i)
                 (mword_of_int (match toks !! i with
                                | Some tk => s0 + Z.of_nat (fst tk)
                                | None => 0
                                end)))%I with "[Hargv]" as ">#Hargv".
    { iApply big_sepL_bupd. iApply (big_sepL_impl with "Hargv").
      iIntros "!>" (i j Hij) "Hs".
      apply lookup_seq in Hij as [Hje Hlt].
      rewrite Nat.add_0_l in Hje. subst j.
      rewrite /ushp_slot.
      destruct (toks !! i) as [tk |] eqn:Etk.
      - iApply (uword_persist with "Hs").
      - rewrite (bool_decide_eq_true_2 (i = length toks)).
        + iApply (uword_persist with "Hs").
        + apply lookup_ge_None_1 in Etk. lia. }
    (* ---- every token, as a string ---- *)
    iAssert ([∗ list] x ∈ ush_args s0 g toks, ush_str γd x)%I as "#Hstrs".
    { rewrite /ush_args big_sepL_fmap.
      iApply big_sepL_intro. iIntros "!>" (i tk Hi).
      rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes fst snd].
      destruct (Hin i tk Hi) as [Hlo Hhi].
      iSplitR; [ iPureIntro; lia | ].
      iSplitR; [ iPureIntro; exact (Hbod i tk Hi) | ].
      iSplitR; [ iPureIntro; lia | ].
      iSplitL.
      - (* the bytes *)
        iDestruct (ubytesq_sub γd s0 (S len) g (fst tk) (snd tk - fst tk)%nat
                     ltac:(lia) with "Hline") as "Hb". iExact "Hb".
      - (* the terminator, which is the zero [nulterminate] wrote *)
        iDestruct (ubytesq_at γd s0 (S len) g (snd tk) ltac:(lia) with "Hline")
          as "Hb".
        rewrite (Hend i tk Hi).
        assert (Ea : (s0 + Z.of_nat (snd tk))%Z
                     = (s0 + Z.of_nat (fst tk) + Z.of_nat (snd tk - fst tk))%Z)
          by lia.
        iEval (rewrite Ea) in "Hb". iExact "Hb". }
    (* ---- assemble ---- *)
    iModIntro. iFrame "Hrun". rewrite /ush_cmd.
    iSplitR; [ iPureIntro; lia | ].
    iSplitR; [ iPureIntro; exact Hp8 | ].
    iSplitR.
    { (* the type word: EXEC is 1 *)
      rewrite /ush_w32. iExact "Hty". }
    iSplit.
    { (* the vector *)
      rewrite /uargv.
      iSplit; [ iPureIntro; rewrite Zplus_mod Hp8; reflexivity | ].
      iSplit; [ iPureIntro; rewrite ush_args_length; lia | ].
      iApply big_sepL_intro. iIntros "!>" (i x Hi).
      (* the element is the token's image, so its fields are the token's *)
      assert (Htk : exists tk : nat * nat,
                toks !! i = Some tk /\
                x = UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
                         (fun j : nat => g (fst tk + j)%nat)).
      { unfold ush_args in Hi. rewrite list_lookup_fmap in Hi.
        destruct (toks !! i) as [tk |] eqn:Etk; [ | discriminate Hi ].
        injection Hi as <-. exists tk. split; [ reflexivity | reflexivity ]. }
      destruct Htk as (tk & Hi' & ->).
      cbn [ua_ptr ua_len ua_bytes].
      iSplit.
      - iDestruct (big_sepL_lookup _ (seq 0 (S (length toks))) i i with "Hargv")
          as "Hw"; [ apply lookup_seq;
                     pose proof (lookup_lt_Some toks i tk Hi'); lia | ].
        rewrite Hi'. iExact "Hw".
      - iDestruct (big_sepL_lookup _ (ush_args s0 g toks) i
                     (UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
                           (fun j : nat => g (fst tk + j)%nat)) with "Hstrs")
          as "Hs"; [ exact (ush_args_lookup s0 g toks i tk Hi') | ].
        rewrite /ush_str. iDestruct "Hs" as "[_ Hs]".
        cbn [ua_ptr ua_len ua_bytes]. iExact "Hs". }
    iSplit; [ | iExact "Hstrs" ].
    (* the NULL cap, at the slot just past the last token *)
    rewrite /ush_ptr ush_args_length.
    iDestruct (big_sepL_lookup _ (seq 0 (S (length toks)))
                 (length toks) (length toks) with "Hargv") as "Hw";
      [ apply lookup_seq; lia | ].
    rewrite (lookup_ge_None_2 toks (length toks) ltac:(lia)).
    iExact "Hw".
  Qed.

  (* ===================================================================== *)
  (* (S) THE SEAM, over the whole tree.                                     *)
  (* ===================================================================== *)

  (* the four inner rows, INTRODUCED rather than unfolded: the sub-trees
     are variables here, so [cbn] reduces the outer node and cannot touch
     them (UkShRedirSeam.ush_cmd_redir_intro's shape, one per constructor) *)
  Lemma ush_cmd_redir_of (g : gname) (t q : Z) (c1 : ushcmd)
      (file : uarg) (mode fd : Z) :
    0 < t < 2 ^ 38 -> t mod 8 = 0 ->
    ush_w32 g t 2 -∗ ush_ptr g (t + 8) q -∗ ush_cmd g q c1 -∗
    ush_ptr g (t + 16) (ua_ptr file) -∗ ush_str g file -∗
    ush_w32 g (t + 32) mode -∗ ush_w32 g (t + 36) fd -∗
    ush_cmd g t (URedir c1 file mode fd).
  Proof using .
    intros Ht38 Ht8.
    iIntros "#Hty #Hp #Hc #Hfp #Hfs #Hm #Hf".
    cbn [ush_cmd ush_ty].
    iSplit; [ iPureIntro; exact Ht38 | ].
    iSplit; [ iPureIntro; exact Ht8 | ].
    iSplit; [ iExact "Hty" | ].
    iSplit; [ iExists q; iSplit; [ iExact "Hp" | iExact "Hc" ] | ].
    iSplit; [ iExact "Hfp" | ].
    iSplit; [ iExact "Hfs" | ].
    iSplit; [ iExact "Hm" | iExact "Hf" ].
  Qed.

  Lemma ush_cmd_pipe_of (g : gname) (t ql qr : Z) (l r : ushcmd) :
    0 < t < 2 ^ 38 -> t mod 8 = 0 ->
    ush_w32 g t 3 -∗ ush_ptr g (t + 8) ql -∗ ush_cmd g ql l -∗
    ush_ptr g (t + 16) qr -∗ ush_cmd g qr r -∗
    ush_cmd g t (UPipe l r).
  Proof using .
    intros Ht38 Ht8.
    iIntros "#Hty #Hpl #Hl #Hpr #Hr".
    cbn [ush_cmd ush_ty].
    iSplit; [ iPureIntro; exact Ht38 | ].
    iSplit; [ iPureIntro; exact Ht8 | ].
    iSplit; [ iExact "Hty" | ].
    iSplit; [ iExists ql; iSplit; [ iExact "Hpl" | iExact "Hl" ]
            | iExists qr; iSplit; [ iExact "Hpr" | iExact "Hr" ] ].
  Qed.

  Lemma ush_cmd_list_of (g : gname) (t ql qr : Z) (l r : ushcmd) :
    0 < t < 2 ^ 38 -> t mod 8 = 0 ->
    ush_w32 g t 4 -∗ ush_ptr g (t + 8) ql -∗ ush_cmd g ql l -∗
    ush_ptr g (t + 16) qr -∗ ush_cmd g qr r -∗
    ush_cmd g t (UList l r).
  Proof using .
    intros Ht38 Ht8.
    iIntros "#Hty #Hpl #Hl #Hpr #Hr".
    cbn [ush_cmd ush_ty].
    iSplit; [ iPureIntro; exact Ht38 | ].
    iSplit; [ iPureIntro; exact Ht8 | ].
    iSplit; [ iExact "Hty" | ].
    iSplit; [ iExists ql; iSplit; [ iExact "Hpl" | iExact "Hl" ]
            | iExists qr; iSplit; [ iExact "Hpr" | iExact "Hr" ] ].
  Qed.

  Lemma ush_cmd_back_of (g : gname) (t q : Z) (c1 : ushcmd) :
    0 < t < 2 ^ 38 -> t mod 8 = 0 ->
    ush_w32 g t 5 -∗ ush_ptr g (t + 8) q -∗ ush_cmd g q c1 -∗
    ush_cmd g t (UBack c1).
  Proof using .
    intros Ht38 Ht8.
    iIntros "#Hty #Hp #Hc".
    cbn [ush_cmd ush_ty].
    iSplit; [ iPureIntro; exact Ht38 | ].
    iSplit; [ iPureIntro; exact Ht8 | ].
    iSplit; [ iExact "Hty" | ].
    iExists q. iSplit; [ iExact "Hp" | iExact "Hc" ].
  Qed.

  (* a node's type word and its address bound, off the run's heap; the
     word persisted *)
  Local Lemma ushp_type_persist (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (p : Z) (t : ushp_cmd) :
    0 < p ->
    urun N h m pc avail -∗ UkShParse.ushp_type_at N p t ==∗
    urun N h m pc avail ∗ ⌜ 0 < p < 2 ^ 38 ⌝ ∗ ush_w32 γd p (UkShParse.ushp_ty t).
  Proof using .
    intro Hp0. iIntros "Hrun [Hty _]".
    iDestruct (urun_ubytes_bnd h m pc avail p 4 _ with "Hrun Hty") as %Hpb.
    iMod (ubytes_persist γd p 4 _ with "Hty") as "#Htyq".
    iModIntro. iFrame "Hrun". iSplitR.
    - iPureIntro. split; [ exact Hp0 | destruct (Hpb 0%nat ltac:(lia)) as [ _ Hhi ]; lia ].
    - rewrite /ush_w32. iExact "Htyq".
  Qed.

  (* a file name (q, e) of the cut line, as the runner's string *)
  Local Lemma ush_str_of_line (s0 : Z) (len : nat) (g : nat -> bv 8) (q e : nat) :
    (q < e)%nat -> (e <= len)%nat -> g e = ubyte0 ->
    (forall j : nat, (j < e - q)%nat -> g (q + j)%nat <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 -> 0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ubytesq γd DfracDiscarded s0 (S len) g -∗
    ush_str γd (UArg (s0 + Z.of_nat q) (e - q)%nat (fun j : nat => g (q + j)%nat)).
  Proof using .
    intros Hqe Hle Hz Hbod Hlen31 Hs0 Hs0hi. iIntros "#Hline".
    rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
    iSplit; [ iPureIntro; lia | ].
    rewrite /ustr.
    iSplit; [ iPureIntro; exact Hbod | ].
    iSplit; [ iPureIntro; lia | ].
    iSplit.
    - iApply (ubytesq_sub γd s0 (S len) g q (e - q)%nat ltac:(lia) with "Hline").
    - iDestruct (ubytesq_at γd s0 (S len) g e ltac:(lia) with "Hline") as "Hb".
      iEval (rewrite Hz) in "Hb".
      assert (Ea : (s0 + Z.of_nat e)%Z = (s0 + Z.of_nat q + Z.of_nat (e - q))%Z) by lia.
      iEval (rewrite Ea) in "Hb". iExact "Hb".
  Qed.

  (* THE SEAM.  By induction on the tree: each node's fields are persisted,
     its address bound read off the run, its strings cut out of the line.
     Every constructor, no scope premise -- [ushp_cut_ok] is all it needs. *)
  Lemma ush_cmd_of_ushp_tree (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (s0 : Z) (len : nat) (g : nat -> bv 8) (t : ushp_cmd) :
    ushp_cut_ok len g t ->
    Z.of_nat len < 2 ^ 31 -> 0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    forall p : Z,
    urun N h m pc avail -∗
    ushp_tree N s0 p t -∗
    ubytesq γd DfracDiscarded s0 (S len) g ==∗
    urun N h m pc avail ∗ ush_cmd γd p (ushcmd_of_tree s0 g t).
  Proof using .
    intros Hcut Hlen31 Hs0 Hs0hi. revert Hcut.
    induction t as [ toks | c IH q e mode fd | l IHl r IHr | l IHl r IHr | c IH ];
      intros Hcut p.
    - (* EXEC *)
      destruct Hcut as (Hin & Hend & Hbod).
      iIntros "Hrun Hnode #Hline".
      iApply (ush_cmd_of_ushp_gen h m pc avail s0 p len g toks
                Hin Hend Hbod Hlen31 Hs0 Hs0hi with "Hrun Hnode Hline").
    - (* REDIR *)
      destruct Hcut as (Hc & Hqe & Hz & Hbod).
      iIntros "Hrun Hnode #Hline".
      cbn [UkShParse.ushp_tree].
      iDestruct "Hnode" as "(%Hp0 & %Hp8 & Hty & (%pc1 & Hcp & Hsub) & Hfile & Hefile & Hmode & Hfd)".
      iMod (ushp_type_persist h m pc avail p _ Hp0 with "Hrun Hty") as "(Hrun & %Hp & #Htyq)".
      iMod (IH Hc pc1 with "Hrun Hsub Hline") as "[Hrun #Hsubq]".
      iMod (uword_persist γd (p + 8) _ with "Hcp") as "#Hcpq".
      iMod (uword_persist γd (p + 16) _ with "Hfile") as "#Hfileq".
      iMod (ubytes_persist γd (p + 32) 4 _ with "Hmode") as "#Hmodeq".
      iMod (ubytes_persist γd (p + 36) 4 _ with "Hfd") as "#Hfdq".
      iClear "Hefile".
      iModIntro. iFrame "Hrun".
      cbn [ushcmd_of_tree].
      iApply (ush_cmd_redir_of γd p pc1 (ushcmd_of_tree s0 g c)
                (UArg (s0 + Z.of_nat q) (e - q)%nat (fun j : nat => g (q + j)%nat))
                mode fd Hp Hp8 with "[] [] Hsubq [] [] [] []").
      + cbn [UkShParse.ushp_ty]. iExact "Htyq".
      + rewrite /ush_ptr. iExact "Hcpq".
      + rewrite /ush_ptr. cbn [ua_ptr]. iExact "Hfileq".
      + iApply (ush_str_of_line s0 len g q e (proj1 Hqe) (proj2 Hqe) Hz Hbod
                  Hlen31 Hs0 Hs0hi with "Hline").
      + rewrite /ush_w32. iExact "Hmodeq".
      + rewrite /ush_w32. iExact "Hfdq".
    - (* PIPE *)
      destruct Hcut as [ Hl Hr ].
      iIntros "Hrun Hnode #Hline".
      cbn [UkShParse.ushp_tree].
      iDestruct "Hnode" as "(%Hp0 & %Hp8 & Hty & (%pl & Hpl & Hsl) & (%pr & Hpr & Hsr))".
      iMod (ushp_type_persist h m pc avail p _ Hp0 with "Hrun Hty") as "(Hrun & %Hp & #Htyq)".
      iMod (IHl Hl pl with "Hrun Hsl Hline") as "[Hrun #Hlq]".
      iMod (IHr Hr pr with "Hrun Hsr Hline") as "[Hrun #Hrq]".
      iMod (uword_persist γd (p + 8) _ with "Hpl") as "#Hplq".
      iMod (uword_persist γd (p + 16) _ with "Hpr") as "#Hprq".
      iModIntro. iFrame "Hrun". cbn [ushcmd_of_tree].
      iApply (ush_cmd_pipe_of γd p pl pr _ _ Hp Hp8 with "[] [] Hlq [] Hrq").
      + cbn [UkShParse.ushp_ty]. iExact "Htyq".
      + rewrite /ush_ptr. iExact "Hplq".
      + rewrite /ush_ptr. iExact "Hprq".
    - (* LIST *)
      destruct Hcut as [ Hl Hr ].
      iIntros "Hrun Hnode #Hline".
      cbn [UkShParse.ushp_tree].
      iDestruct "Hnode" as "(%Hp0 & %Hp8 & Hty & (%pl & Hpl & Hsl) & (%pr & Hpr & Hsr))".
      iMod (ushp_type_persist h m pc avail p _ Hp0 with "Hrun Hty") as "(Hrun & %Hp & #Htyq)".
      iMod (IHl Hl pl with "Hrun Hsl Hline") as "[Hrun #Hlq]".
      iMod (IHr Hr pr with "Hrun Hsr Hline") as "[Hrun #Hrq]".
      iMod (uword_persist γd (p + 8) _ with "Hpl") as "#Hplq".
      iMod (uword_persist γd (p + 16) _ with "Hpr") as "#Hprq".
      iModIntro. iFrame "Hrun". cbn [ushcmd_of_tree].
      iApply (ush_cmd_list_of γd p pl pr _ _ Hp Hp8 with "[] [] Hlq [] Hrq").
      + cbn [UkShParse.ushp_ty]. iExact "Htyq".
      + rewrite /ush_ptr. iExact "Hplq".
      + rewrite /ush_ptr. iExact "Hprq".
    - (* BACK *)
      iIntros "Hrun Hnode #Hline".
      cbn [UkShParse.ushp_tree].
      iDestruct "Hnode" as "(%Hp0 & %Hp8 & Hty & (%pc1 & Hcp & Hsub))".
      iMod (ushp_type_persist h m pc avail p _ Hp0 with "Hrun Hty") as "(Hrun & %Hp & #Htyq)".
      iMod (IH Hcut pc1 with "Hrun Hsub Hline") as "[Hrun #Hsubq]".
      iMod (uword_persist γd (p + 8) _ with "Hcp") as "#Hcpq".
      iModIntro. iFrame "Hrun". cbn [ushcmd_of_tree].
      iApply (ush_cmd_back_of γd p pc1 _ Hp Hp8 with "[] [] Hsubq").
      + cbn [UkShParse.ushp_ty]. iExact "Htyq".
      + rewrite /ush_ptr. iExact "Hcpq".
  Qed.

  (* ...at the parser's own answer: the tree the parser theorem hands back,
     and the line cut at [ref_nulcut t] *)
  Lemma ush_cmd_of_ref (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat)
      (s0 p : Z) (len : nat) (f : nat -> bv 8) (t : ushp_cmd) :
    ref_parsecmd len f = Some t ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 -> 0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    urun N h m pc avail -∗
    ushp_tree N s0 p t -∗
    ubytes γd s0 (S len) (ushp_zero_at (ref_nulcut t) (ushp_ext len f)) ==∗
    urun N h m pc avail ∗
    ush_cmd γd p (ushcmd_of_tree s0 (ushp_zero_at (ref_nulcut t) (ushp_ext len f)) t).
  Proof using .
    intros Href Hnn Hlen31 Hs0 Hs0hi.
    iIntros "Hrun Hnode Hline".
    iMod (ubytes_persist γd s0 (S len) _ with "Hline") as "#Hline".
    iApply (ush_cmd_of_ushp_tree h m pc avail s0 len _ t
              (ushp_cut_ok_of_ref len f t Hnn Href) Hlen31 Hs0 Hs0hi p
              with "Hrun Hnode Hline").
  Qed.

  (* ===================================================================== *)
  (* (C) THE CHILD: parse the line, then hand runcmd the tree.               *)
  (*                                                                        *)
  (*   0x9c0  c.mv a0,s1        the line                                    *)
  (*   0x9c2  jal  ra,parsecmd  -> the node, at the reference's answer      *)
  (*   0x9c6  jal  ra,runcmd    -> the continuation: the shape's arm        *)
  (*                                                                        *)
  (* The room is [ushp_room t] over what the arm needs; the arm gets the    *)
  (* runner's tree at [runcmd]'s entry, the line persisted at the cut, the  *)
  (* two lexer tables back, the allocator's end state and the lend back,   *)
  (* and the callee-saved file as it was at 0x9c0.                          *)
  (* ===================================================================== *)

  (* a write to a register that is not callee-saved keeps the callee-saved
     file *)
  Local Lemma ucallee_saved_upd (m : regfile) (r : mword 5) (v : mword 64) :
    ucallee_saved_idx r = false ->
    ucallee_saved m (<[Regidx r := v]> m).
  Proof using .
    intros Hr r' Hr'.
    rewrite (upd_ne m (Regidx r) (Regidx r') v); [ reflexivity | ].
    intro E. injection E as E. subst r'. rewrite Hr in Hr'. discriminate Hr'.
  Qed.

  Lemma wp_ref_child (UM UM' : iProp Σ)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (t : ushp_cmd)
      (n : nat) (Cr : iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ref_sym_scope len f ->
    ref_parsecmd len f = Some t ->
    ushp_cat t ->
    ushp_malloc_chain (ushp_nodes t) UM UM' ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    shk_code γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    (* the lend, and the law that turns it into the exit payload where the
       parser's NULL store kills the process *)
    □ (Cr -∗ ukn_pay N (-1)) -∗
    Cr -∗
    urun N h m (mword_of_int 0x9c0) (ushp_room t + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int p : mword 64) ⌝ -∗
       ⌜ ucallee_saved m m' ⌝ -∗
       ush_cmd γd p (ushcmd_of_tree s0 (ushp_zero_at (ref_nulcut t) (ushp_ext len f)) t) -∗
       ubytesq γd DfracDiscarded s0 (S len) (ushp_zero_at (ref_nulcut t) (ushp_ext len f)) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UM' -∗
       Cr -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (ushp_room t + (8 + (UkShDiag.ush_Dg + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hs1 Hscope Href Hcat Hchain Hs0 Hs64 Hs38.
    iIntros "#Hcode #Hpcode #Hpro Hline Hws Hsy HM #Hpxw Hcr Hrun Hcont".
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    iDestruct (ustr_len with "Hline") as %Hlen31.
    (* ---- 0x9c0  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x9c0) a0_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx))
              (ushp_room t + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_shk_9c0 with "Hcode"). }
    assert (E9c0 : add_vec_int (mword_of_int 0x9c0 : mword 64) 2
                   = mword_of_int 0x9c2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9c0. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m !!! Regidx s1_idx))]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int s0 : mword 64)).
    { rewrite /m1 (upd_eq m (Regidx a0_idx) _).
      rewrite Hs1. apply bv_eq. rewrite add_vec_unsigned.
      unfold bv_wrap. cbn [bv_unsigned]. rewrite Z.add_0_l.
      rewrite Z.mod_small; [ reflexivity | ].
      pose proof (bv_unsigned_in_range _ (mword_of_int s0 : mword 64)) as Hr.
      assert (Hm : bv_modulus (MachineWord.Z_idx 64) = 18446744073709551616%Z)
        by (vm_compute; reflexivity).
      rewrite Hm in Hr. exact Hr. }
    assert (Hcs1 : ucallee_saved m m1)
      by exact (ucallee_saved_upd m a0_idx _ ltac:(vm_compute; reflexivity)).
    (* ---- 0x9c2  jal ra,parsecmd ---- *)
    iApply (wp_uk_jal N h1 m1 (mword_of_int 0x9c2)
              (mword_of_int 2096812 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.parsecmd) (mword_of_int 0x9c6)
              (ushp_room t + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9c2 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx (mword_of_int 1 : mword 5)
                 := regval_into_reg (mword_of_int 0x9c6 : mword 64)]> m1).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int s0 : mword 64))
      by (rewrite /m2 (upd_ne m1 (Regidx (mword_of_int 1 : mword 5))
                         (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
          exact Ha0_1).
    assert (Hra_2 : ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))
                    = (mword_of_int 0x9c6 : mword 64))
      by (rewrite /m2 (upd_eq m1 (Regidx (mword_of_int 1 : mword 5)) _);
          apply bv_eq; vm_compute; reflexivity).
    assert (Hcs2 : ucallee_saved m m2)
      by exact (ucallee_saved_trans m m1 m2 Hcs1
                  (ucallee_saved_upd m1 (mword_of_int 1 : mword 5) _
                     ltac:(vm_compute; reflexivity))).
    (* ---- parsecmd: THE PARSER THEOREM ---- *)
    iApply (UkShParser.wp_ref_parser N h2 m2 dw dv s0 len f t UM UM'
              (8 + (UkShDiag.ush_Dg + n))
              Ha0_2 Hscope Href Hcat Hchain Hs0 Hs64
              with "Hpcode Hpro Hline Hws Hsy HM Hpxw Hcr Hrun").
    iIntros (p) "Hnode Hline %Hcut Hws Hsy".
    iIntros (h3 m3) "%Hcs3 %Ha0_3 HM' Hcr Hrun".
    rewrite Hra_2.
    (* ---- 0x9c6  jal ra,runcmd ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x9c6)
              (mword_of_int 2094792 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.runcmd) (mword_of_int 0x9ca)
              (ushp_room t + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9c6 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx (mword_of_int 1 : mword 5)
                 := regval_into_reg (mword_of_int 0x9ca : mword 64)]> m3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = (mword_of_int p : mword 64))
      by (rewrite /m4 (upd_ne m3 (Regidx (mword_of_int 1 : mword 5))
                         (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
          exact Ha0_3).
    assert (Hcs4 : ucallee_saved m m4)
      by exact (ucallee_saved_trans m m3 m4
                  (ucallee_saved_trans m m2 m3 Hcs2 Hcs3)
                  (ucallee_saved_upd m3 (mword_of_int 1 : mword 5) _
                     ltac:(vm_compute; reflexivity))).
    (* ---- THE SEAM: the node the parser built is the tree runcmd walks ---- *)
    iMod (ubytes_persist γd s0 (S len) _ with "Hline") as "#Hlineq".
    iMod (ush_cmd_of_ushp_tree h4 m4 (mword_of_int ShSyms.runcmd)
            (ushp_room t + (8 + (UkShDiag.ush_Dg + n))) s0 len _ t
            (ushp_cut_ok_of_ref len f t Hnn0 Href) Hlen31 Hs0 Hs38 p
            with "Hrun Hnode Hlineq") as "(Hrun & #Htree)".
    (* ---- runcmd: the arm's ---- *)
    iApply ("Hcont" $! h4 m4 p with "[%] [%] Htree Hlineq Hws Hsy HM' Hcr Hrun");
      [ exact Ha0_4 | exact Hcs4 ].
  Qed.

  (* ===================================================================== *)
  (* (C1) THE EXEC ARM: runcmd reaches [exec] and never returns             *)
  (* (UkShMain.wp_kshm_child's shape).                                      *)
  (* ===================================================================== *)
  Lemma wp_ref_child_exec (UM UM' : iProp Σ)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (szv : Z) (ld : list fdstate) (n : nat) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ref_sym_scope len f ->
    ref_parsecmd len f = Some (UshpExec toks) ->
    ushp_malloc_chain 1 UM UM' ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (* THE PAYLOAD IS FREE AT THIS RECORD: the exit is paid from nothing *)
    (⊢ ukn_pay N (-1)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    (* the exec deposit's supplier at THIS record's own payload *)
    uxsup_at (ukn_pay N) -∗
    (* ...and how a killer pays for a forked child *)
    □ (app_taint -∗ ukn_pay N (-1)) -∗
    shp_code γt -∗ shp_rodata γt -∗ ush_jtab γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd_any γcwd -∗
    UserChildren.uch_any γch -∗
    UM -∗
    (* the break, read off what the allocator left *)
    (UM' -∗ usz γs szv) -∗
    urun N h m (mword_of_int 0x9c0) (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hscope Href Hchain Hs0 Hs64 Hs38 Hpx.
    iIntros "#Hdp #Hcode #Hxs #Hkw #Hpcode #Hpro #Hjt Hline Hws Hsy Hstd Hcwd
             Hch HM Husz Hrun".
    iPoseProof Hpx as "Hpay".
    iAssert (□ (ukn_pay N (-1) -∗ ukn_pay N (-1)))%I as "#Hpxw";
      [ iIntros "!> $" | ].
    replace (60 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (ushp_room (UshpExec toks) + (8 + (UkShDiag.ush_Dg + n)))%nat
      by reflexivity.
    iApply (wp_ref_child UM UM' h m dw dv s0 len f (UshpExec toks) n
              (ukn_pay N (-1)) Hs1 Hscope Href I Hchain Hs0 Hs64 Hs38
              with "Hcode Hpcode Hpro Hline Hws Hsy HM Hpxw Hpay Hrun").
    iIntros (h' m' p) "%Ha0 %Hcs #Htree #Hlineq Hws Hsy HM' _ Hrun".
    iDestruct ("Husz" with "HM'") as "Hsz".
    replace (ushp_room (UshpExec toks) + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (6 * ush_ht (ushcmd_of_tree s0 (ushp_zero_at (ref_nulcut (UshpExec toks))
                                             (ushp_ext len f)) (UshpExec toks))
            + (2 + (UkShDiag.ush_Dg + (60 + n))))%nat
      by (cbn [ushcmd_of_tree ush_ht]; reflexivity).
    iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free
              (ushcmd_of_tree s0 _ (UshpExec toks))
              ltac:(cbn [ushcmd_of_tree ush_simple]; exact I)
              N h' m' p szv ld (60 + n) Hpx Ha0
              with "Hdp Hcode Hxs Hkw Hjt Htree Hsz Hstd Hcwd Hch Hrun").
  Qed.

  (* ===================================================================== *)
  (* (C2) THE REDIRECT ARM: close(1), open(file), and the sub-tree at        *)
  (* runcmd's entry, or the failed open at its diagnostic                   *)
  (* (UkShRedirSeam.wp_kshm_child_redir_g's shape).  The cut is a parameter *)
  (* [g] with its equation, so a statement at the redirect line's own       *)
  (* spelling of the cut is an instance.                                    *)
  (* ===================================================================== *)
  Lemma wp_ref_child_redir (UM UM' : iProp Σ)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (q e : nat) (g : nat -> bv 8)
      (ld : list fdstate) (st1 : fdstate) (n : nat)
      (H : iProp Σ) (K : fdtype -> iProp Σ) (Kf : iProp Σ)
      (Cr Cr' : iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ref_sym_scope len f ->
    ref_parsecmd len f = Some (UshpRedir (UshpExec toks) q e 1537 1) ->
    g = ushp_zero_at (ref_nulcut (UshpRedir (UshpExec toks) q e 1537 1)) (ushp_ext len f) ->
    ushp_malloc_chain 2 UM UM' ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UM -∗
    UkShRedir.ush_open_call_g N cwdv
      (UArg (s0 + Z.of_nat q) (e - q)%nat (fun j : nat => g (q + j)%nat)) 1537
      (<[1%nat := FdClosed]> ld) H K Kf -∗
    □ (Cr -∗ ukn_pay N (-1)) -∗
    (* THE LEND SPLITS AT THE CALL: whole across the parse (it pays the
       parser's exits), and then what the open is handed and the rest *)
    (Cr -∗ H ∗ Cr') -∗
    Cr -∗
    urun N h m (mword_of_int 0x9c0) (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    ((∀ (h' : CpuId) (m' : regfile) (p : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int p : mword 64) ⌝ -∗
       ush_cmd γd p (UExec (ush_args s0 g toks)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UM' -∗
       Cr' -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       mWP (Loop : expr riscv_lang))
     ∧
     (∀ (h' : CpuId) (m' : regfile),
        ⌜ UkShRun.ush_diag_at 0x10e m' ⌝ -∗
        UkShRun.ush_ptr γd (uint (m' !!! Regidx s1_idx) + 16)
          (ua_ptr (UArg (s0 + Z.of_nat q) (e - q)%nat (fun j : nat => g (q + j)%nat))) -∗
        UkShRun.ush_str γd
          (UArg (s0 + Z.of_nat q) (e - q)%nat (fun j : nat => g (q + j)%nat)) -∗
        UserFd.ustd γfd (<[1%nat := FdClosed]> ld) -∗
        UserCwd.ucwd γcwd cwdv -∗
        Kf -∗
        Cr' -∗
        urun N h' m' (mword_of_int 0x10e) (UkShDiag.ush_Dg + (70 + n)) -∗
        mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    intros Hs1 Hscope Href Hg Hchain Hs0 Hs64 Hs38 Hst1 Hne Hnp. subst g.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hstd Hcwd HM Hopen
             #Hpxw Hsplit Hcr Hrun Hk".
    replace (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (ushp_room (UshpRedir (UshpExec toks) q e 1537 1) + (8 + (UkShDiag.ush_Dg + n)))%nat
      by reflexivity.
    iApply (wp_ref_child UM UM' h m dw dv s0 len f
              (UshpRedir (UshpExec toks) q e 1537 1) n Cr
              Hs1 Hscope Href (conj I (conj eq_refl eq_refl)) Hchain Hs0 Hs64 Hs38
              with "Hcode Hpcode Hpro Hline Hws Hsy HM Hpxw Hcr Hrun").
    iIntros (h' m' p) "%Ha0 %Hcs #Htree #Hlineq Hws Hsy HM' Hcr Hrun".
    replace (ushp_room (UshpRedir (UshpExec toks) q e 1537 1) + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (UkShDiag.ush_Dg + (70 + n)))%nat by reflexivity.
    iDestruct ("Hsplit" with "Hcr") as "[HH Hcr]".
    iApply (UkShRedir.wp_kshr_redir_arm_g N
              (UExec (ush_args s0 _ toks))
              (UArg (s0 + Z.of_nat q) (e - q)%nat (fun j : nat => _ (q + j)%nat)) 1537
              h' m' p cwdv ld st1 (70 + n) H K Kf
              ltac:(unfold Z31; lia) Ha0 Hst1 Hne Hnp
              with "Hcode Hjt Htree Hstd Hcwd Hopen HH Hrun").
    iSplit.
    - iDestruct "Hk" as "[Hcont _]".
      iIntros (hf mf p' ty) "%Ha0f Hsub Hstd Hcwd HK Hrun".
      iApply ("Hcont" $! hf mf p' ty with "[%//] Hsub Hstd Hcwd HK HM' Hcr Hrun").
    - iDestruct "Hk" as "[_ Hfail]".
      iIntros (hf mf) "%Hat Hfp Hfs Hstd Hcwd HKf Hrun".
      iApply ("Hfail" $! hf mf with "[%//] Hfp Hfs Hstd Hcwd HKf Hcr Hrun").
  Qed.

  (* ===================================================================== *)
  (* (C3) THE PIPE ARM: the pipe, the two forks, the two waits             *)
  (* (UkShPipeRound.wp_kshm_child_pipe's shape).  The general room at a     *)
  (* pipe of two EXEC nodes is 66; the landed statement offers 68 and is    *)
  (* this at [n + 2].                                                       *)
  (* ===================================================================== *)
  Lemma wp_ref_child_pipe (UM UM' : iProp Σ)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (toksl toksr : list (nat * nat)) (g : nat -> bv 8)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr : iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ref_sym_scope len f ->
    ref_parsecmd len f = Some (UshpPipe (UshpExec toksl) (UshpExec toksr)) ->
    g = ushp_zero_at (ref_nulcut (UshpPipe (UshpExec toksl) (UshpExec toksr))) (ushp_ext len f) ->
    ushp_malloc_chain 3 UM UM' ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    (⊢ ukn_pay N (-1)) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM -∗
    Cr -∗
    □ (app_taint -∗ Qc (-1)) -∗
    (* the arm's own split, with the walk's leftovers ([UM'], [Cr]) free to
       ride into whichever of the three it likes *)
    (∀ γp : pipe_names, UM' -∗ Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ Rk γp)) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    urun N h m (mword_of_int 0x9c0) (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (* ---- THE LEFT CHILD: fd 1 is the pipe's WRITE end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (p : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int p : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') p (UExec (ush_args s0 g toksl)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE RIGHT CHILD: fd 0 is the pipe's READ end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (p : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int p : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') p (UExec (ush_args s0 g toksr)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE PARENT, at 0xea ---- *)
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       uwait_ans rw1 S2 S3 -∗
       uwait_ans rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hscope Href Hg Hchain Hs0 Hs64 Hs38 HQc Hpx Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1.
    subst g.
    (* the payload is free, so the parser's exit premise is free *)
    assert (HpxC : ⊢ □ (Cr -∗ ukn_pay N (-1))).
    { iIntros "!> _". iApply Hpx. }
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hsz Hstd Hcwd Hch
             HM Hcr #Hkw Hsplit Hpipe Hrun HcL HcR Hpar".
    iPoseProof HpxC as "#Hpxw".
    replace (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr))
            + (8 + (UkShDiag.ush_Dg + (2 + n))))%nat
      by (change (ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr))) with 66%nat; lia).
    iApply (wp_ref_child UM UM' h m dw dv s0 len f
              (UshpPipe (UshpExec toksl) (UshpExec toksr)) (2 + n) Cr
              Hs1 Hscope Href (conj I I) Hchain Hs0 Hs64 Hs38
              with "Hcode Hpcode Hpro Hline Hws Hsy HM Hpxw Hcr Hrun").
    iIntros (h' m' p) "%Ha0 %Hcs #Htree #Hlineq Hws Hsy HM' Hcr Hrun".
    replace (ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr))
             + (8 + (UkShDiag.ush_Dg + (2 + n))))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (68 + n))))%nat
      by (change (ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr))) with 66%nat; lia).
    iApply (UkShPipe.wp_kshr_pipe_arm Hpsok_free N
              (UExec (ush_args s0 _ toksl)) (UExec (ush_args s0 _ toksr))
              h' m' p szv cwdv ld st0 st1 Sc (68 + n)%nat
              R RcL RcR Rk Qc
              HQc Hpx Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1
              with "Hdp Hcode Hjt Htree Hsz Hstd Hcwd Hch Hkw
                    [Hsplit HM' Hcr] Hpipe Hrun HcL HcR Hpar").
    iIntros (γp) "HR". iApply ("Hsplit" $! γp with "HM' Hcr HR").
  Qed.

  (* ===================================================================== *)
  (* (A) THE ALLOCATOR CHAIN FROM A FRESH STATE.                            *)
  (*                                                                        *)
  (* [UkShMalloc.ushm_fresh sz] is the heap /init handed sh's child: [freep] *)
  (* holding zero, the sixteen bytes of [base], the break at [sz].  The     *)
  (* first call runs on an EMPTY free list, so it walks [sbrk] and [free]   *)
  (* and leaves the 64 KiB chunk [morecore] inserted minus its own twelve   *)
  (* units ([ushm_malloc_le_exec]: 4084 of 4096, the break at [sz + 65536]); *)
  (* every later call runs on THAT list and takes twelve more               *)
  (* ([ushm_malloc_le_one] at the parser's bound 168, which needs twelve    *)
  (* left).  So [k] calls chain for [1 <= k <= 341] -- and no line sh's     *)
  (* parser accepts has more than a hundred nodes.                          *)
  (* ===================================================================== *)
  Lemma ushm_chain_of_fresh (sz : Z) (k : nat) (R : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (1 <= k)%nat -> (k <= 341)%nat ->
    R = 4084 - 12 * (Z.of_nat k - 1) ->
    ushp_malloc_chain k (UkShMalloc.ushm_fresh N sz)
      (UkShMalloc.ushm_one_ge N (sz + 65536) R).
  Proof using Hpsok_free.
    intros Hszlo Hszal Hszok Hk1 Hk HR. subst R.
    assert (E12 : ((168 + 15) / 16 + 1)%Z = 12%Z) by (vm_compute; reflexivity).
    destruct k as [| k ]; [ lia | ].
    induction k as [| k IH ].
    - cbn [UkShRedirs.ushp_malloc_chain].
      exists (UkShMalloc.ushm_one_ge N (sz + 65536) 4084).
      split; [ exact (UkShMalloc.ushm_malloc_le_exec N Hpsok_free sz Hszlo Hszal Hszok) | ].
      f_equal; lia.
    - replace (S (S k)) with (S k + 1)%nat by lia.
      apply (UkShRedirs.ushp_malloc_chain_app N (S k) 1 _
               (UkShMalloc.ushm_one_ge N (sz + 65536) (4084 - 12 * (Z.of_nat (S k) - 1)))).
      + apply IH; lia.
      + apply UkShRedirs.ushp_malloc_chain_1.
        assert (E : (4084 - 12 * (Z.of_nat (S k + 1)%nat - 1))%Z
                    = (4084 - 12 * (Z.of_nat (S k) - 1) - ((168 + 15) / 16 + 1))%Z)
          by (rewrite E12; lia).
        rewrite E.
        exact (UkShMalloc.ushm_malloc_le_one N 168 (sz + 65536)
                 (4084 - 12 * (Z.of_nat (S k) - 1))
                 ltac:(lia) ltac:(lia) ltac:(rewrite E12; lia)).
  Qed.

End UkShSeam.
