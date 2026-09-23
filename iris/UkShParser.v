(* ===================================================================== *)
(* UkShParser.v -- THE TOP OF sh's PARSER AT THE REFERENCE PARSER, ONCE:   *)
(* parsepipe, parseline, nulterminate, parsecmd, and THE PARSER THEOREM    *)
(* (design/user-once.md SS2, worklist A2d).                                *)
(*                                                                        *)
(*   parsepipe    @0x682  cmd = parseexec(); if (peek(|)) { gettoken();    *)
(*                        cmd = pipecmd(cmd, parsepipe()); }               *)
(*   parseline    @0x6e2  cmd = parsepipe(); while (peek(&)) ...;          *)
(*                        if (peek(;)) ...; -- neither turns under the     *)
(*                        symbol scope                                     *)
(*   nulterminate @0x7ee  the jump table over the tree: EXEC zeroes each   *)
(*                        argument's end, REDIR recurses and zeroes the    *)
(*                        file name's end, PIPE recurses twice             *)
(*   parsecmd     @0x86e  strlen, parseline, the leftovers peek,           *)
(*                        nulterminate, return the node                    *)
(*                                                                        *)
(* These four used to be walked THREE times -- UkShParseCmd (the symbol-  *)
(* free line), UkShRedirCm / UkShRedirPc / UkShRedirNul (the '>' line) and *)
(* UkShPipeCm / UkShPipeParse (the '|' line, with UkShPipeRight feeding    *)
(* the recursion a re-based suffix; deleted at A2e) -- and the             *)
(* only genuine TURN above parseexec, parsepipe's, was walked once with   *)
(* the recursion fed the landed symbol-free walk on the line's suffix.    *)
(* Here each is stated once at the reference's answer, the turn is the    *)
(* induction hypothesis at the reference's cursor on the SAME line, and   *)
(* the landed statements above this file are corollaries in place.        *)
(*                                                                        *)
(* (0) THE ANSWER IS AN ADDRESSED TREE.  [ushp_atree s0 p t a] is the      *)
(*     tree [t] at [p] with every node's child pointers NAMED by [a :      *)
(*     ushp_ptr] and the bounds the constructors hand out kept ([p + 168]  *)
(*     at an exec node, [t + 40] inside a redir / pipe node); it closes    *)
(*     into the published [ushp_tree] by [ushp_atree_close] and it is what *)
(*     nulterminate takes and HANDS BACK UNCHANGED -- a walk that reads    *)
(*     the node fields and writes only the line cannot answer an           *)
(*     existential over the pointers.  [ushp_otree] is its existential    *)
(*     closure, the parse walks' answer.                                   *)
(* (1) THE ROOM IS A FUNCTION OF THE TREE.  [ushp_pex_room t] is           *)
(*     parseexec's stack, 40 words plus the redirect turn's eight exactly   *)
(*     when the answer is topped by a REDIR node (UkShArgs.wp_ref_parseexec *)
(*     at [16 + (24 + nn)] under [ref_has_redir t = true -> 8 <= nn]);      *)
(*     [ushp_pp_room t] is parsepipe's: its frame over parseexec's need, or *)
(*     at a pipe over the larger of the left command's and the recursion    *)
(*     on the right; [ushp_pl_room] parseline's frame over it; [ushp_room   *)
(*     t] parsecmd's: eight words and the larger of parseline's need and   *)
(*     nulterminate's recursion depth [4 * ushp_ht t].  The three landed    *)
(*     lines are its instances: 46 / 52 / 60 at an EXEC, 54 / 60 / 68 at   *)
(*     the REDIR over it (both exact), 52 / 58 / 66 at the PIPE of two      *)
(*     EXECs, where the landed pipe statements offer 54 / 60 / 68 and are   *)
(*     the instances at [2 + nn].                                           *)
(* (2) [wp_ref_pp_head]: parsepipe from its entry through the '|' peek --  *)
(*     the prologue, the parseexec (UkShArgs.wp_ref_parseexec, its open    *)
(*     answer closed to [ushp_otree] by [ushp_atree_of_redirs]) and the    *)
(*     peek (UkShGettoken.wp_ref_peek) -- shared by the miss and the turn. *)
(* (3) [wp_ref_parsepipe], by induction on the fuel driven by the          *)
(*     equation: the miss is the landed tail; the turn is the '|'          *)
(*     gettoken (UkShGettoken.wp_ref_gettoken at the reference's own       *)
(*     answer), the recursion (the induction hypothesis at cursor [s2] on  *)
(*     the SAME ustr -- no re-basing), pipecmd (UkShPipeCmd.               *)
(*     wp_kshp_pipecmd, its node LAST in the allocation chain, as the C    *)
(*     allocates it after the recursion returns).                          *)
(* (4) [wp_ref_parseline]: parsepipe and the two peeks, which MISS under   *)
(*     the scope (RefParseSym.ref_peek_scope_miss).                        *)
(* (5) [wp_ref_nul_head]: nulterminate from its entry through the jump     *)
(*     table, at any of the three walked type words; [wp_ref_nulterminate] *)
(*     by induction on the tree restricted to [ushp_walked] (LIST and BACK *)
(*     have no catalog row), the cut being [ushp_zero_at (ref_nulcut t)].  *)
(* (6) [wp_ref_parsecmd] / Theorem [wp_ref_parser]: strlen, parseline, the *)
(*     leftovers peek (the cursor IS at the end: the equation says so),    *)
(*     nulterminate; at [ref_parsecmd len f = Some t] and [ushp_cat t].    *)
(*                                                                        *)
(* TAINT: the allocator chain [ushp_malloc_chain (ushp_nodes t) UM UM'],  *)
(* a premise; nothing else.                                                *)
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
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShParseTok.
Require Import RefParse.
Require Import RefParseSym.
Require Import UkShGettoken.
Require Import UkShParseCmd.
Require Import UkShRedirCmd.
Require Import UkShRedirs.
Require Import UkShArgs.
Require Import UkShPipeNode.
Require Import UkShPipeCmd.

Require Import UexecSG.


(* ===================================================================== *)
(* (0a) THE POINTERS OF A TREE -- the child addresses, constructor by      *)
(* constructor, for the three walked shapes                                *)
(* ===================================================================== *)

Inductive ushp_ptr : Type :=
| UpExec
| UpRedir (pc : Z) (c : ushp_ptr)
| UpPipe (pl pr : Z) (l r : ushp_ptr).

(* ===================================================================== *)
(* (1a) THE ROOMS, pure                                                    *)
(* ===================================================================== *)

(* parseexec's stack: sixteen words of frame, twenty-four for the argument
   loop's calls, and the redirect turn's eight only when a redirect was
   consumed -- which is when the answer is topped by a REDIR node
   (RefParseSym.ref_has_redir).  This is UkShArgs.wp_ref_parseexec's
   [16 + (24 + nn)] with its guard [ref_has_redir t = true -> 8 <= nn]. *)
Definition ushp_pex_extra (t : ushp_cmd) : nat :=
  if ref_has_redir t then 8%nat else 0%nat.

Definition ushp_pex_room (t : ushp_cmd) : nat := (16 + (24 + ushp_pex_extra t))%nat.

Lemma ushp_pex_extra_guard (t : ushp_cmd) (k : nat) :
  ref_has_redir t = true -> (8 <= ushp_pex_extra t + k)%nat.
Proof using. intro H. unfold ushp_pex_extra. rewrite H. lia. Qed.

Lemma ushp_pex_room_ge (t : ushp_cmd) : (40 <= ushp_pex_room t)%nat.
Proof using. unfold ushp_pex_room. lia. Qed.

Lemma ushp_pex_room_has (t : ushp_cmd) :
  ref_has_redir t = true -> ushp_pex_room t = 48%nat.
Proof using. intro H. unfold ushp_pex_room, ushp_pex_extra. rewrite H. reflexivity. Qed.

(* parsepipe's stack: its six-word frame over parseexec's need at a tree
   with no pipe; at a pipe, over the larger of the left command's parseexec
   and the recursion on the right *)
Fixpoint ushp_pp_room (t : ushp_cmd) : nat :=
  match t with
  | UshpPipe l r => (6 + Nat.max (ushp_pex_room l) (ushp_pp_room r))%nat
  | _ => (6 + ushp_pex_room t)%nat
  end.

Lemma ushp_pp_room_ge (t : ushp_cmd) : (46 <= ushp_pp_room t)%nat.
Proof using.
  destruct t; cbn [ushp_pp_room];
    match goal with
    | |- context [ ushp_pex_room ?x ] => pose proof (ushp_pex_room_ge x)
    end; lia.
Qed.

(* parseexec's answer is never a pipe, so parsepipe's room at it is the
   frame over parseexec's need *)
Lemma ushp_pp_room_wrap (toks : list (nat * nat)) (rs : list rredir) :
  ushp_pp_room (ref_wrap (UshpExec toks) rs)
  = (6 + ushp_pex_room (ref_wrap (UshpExec toks) rs))%nat.
Proof using.
  destruct (ref_wrap_redir_or (UshpExec toks) rs) as [ E | (c' & q & e & mode & fd & E) ];
    rewrite E; reflexivity.
Qed.

(* parseline's: its own frame over parsepipe's *)
Definition ushp_pl_room (t : ushp_cmd) : nat := (6 + ushp_pp_room t)%nat.

(* parsecmd's: its own frame over the larger of parseline's need and
   nulterminate's recursion, four words per level of the tree *)
Definition ushp_room (t : ushp_cmd) : nat :=
  (8 + Nat.max (ushp_pl_room t) (4 * ushp_ht t))%nat.

(* ===================================================================== *)
(* (5a) THE CUT, pure: the fold that zeroes every index nulterminate      *)
(* visits.  [UkShParseCmd.ushp_nulfold] is its instance at an exec node.  *)
(* ===================================================================== *)

Definition ushp_zero_at (js : list nat) (g : nat -> bv 8) : nat -> bv 8 :=
  fold_left (fun (g' : nat -> bv 8) (j : nat) => UkShParseCmd.ushp_setb g' j ubyte0) js g.

Lemma ushp_zero_at_nil (g : nat -> bv 8) : ushp_zero_at [] g = g.
Proof using. reflexivity. Qed.

Lemma ushp_zero_at_app (l1 l2 : list nat) (g : nat -> bv 8) :
  ushp_zero_at (l1 ++ l2) g = ushp_zero_at l2 (ushp_zero_at l1 g).
Proof using. unfold ushp_zero_at. apply fold_left_app. Qed.

Lemma ushp_zero_at_snoc (l : list nat) (j : nat) (g : nat -> bv 8) :
  ushp_zero_at (l ++ [j]) g = UkShParseCmd.ushp_setb (ushp_zero_at l g) j ubyte0.
Proof using. rewrite ushp_zero_at_app. reflexivity. Qed.

Lemma ushp_nulfold_zero_at (toks : list (nat * nat)) (g : nat -> bv 8) :
  UkShParseCmd.ushp_nulfold toks g = ushp_zero_at (map snd toks) g.
Proof using.
  revert g. induction toks as [| tk r IH ]; intro g; [ reflexivity | ].
  cbn [UkShParseCmd.ushp_nulfold List.map]. rewrite IH. reflexivity.
Qed.

(* every index cut is zero afterwards, and a zero stays zero *)
Lemma ushp_zero_at_keep (js : list nat) (g : nat -> bv 8) (j : nat) :
  g j = ubyte0 -> ushp_zero_at js g j = ubyte0.
Proof using.
  revert g. induction js as [| k r IH ]; intros g Hg; [ exact Hg | ].
  cbn [ushp_zero_at fold_left]. apply IH. rewrite /UkShParseCmd.ushp_setb.
  destruct (Nat.eqb j k); [ reflexivity | exact Hg ].
Qed.

Lemma ushp_zero_at_hit (js : list nat) (g : nat -> bv 8) (j : nat) :
  j ∈ js -> ushp_zero_at js g j = ubyte0.
Proof using.
  revert g. induction js as [| k r IH ]; intros g Hin.
  - exfalso. exact (not_elem_of_nil j Hin).
  - cbn [ushp_zero_at fold_left].
    destruct (decide (j = k)) as [ -> | Hne ].
    + apply ushp_zero_at_keep. rewrite /UkShParseCmd.ushp_setb Nat.eqb_refl. reflexivity.
    + apply IH. apply elem_of_cons in Hin. destruct Hin as [ E | Hin ]; [ exact (False_ind _ (Hne E)) | exact Hin ].
Qed.


Section UkShParser.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).

  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_slot := (UkShParse.ushp_slot N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen N).
  Local Notation ushp_cell := (UkShParseTok.ushp_cell N).
  Local Notation wp_ref_gettoken := (UkShGettoken.wp_ref_gettoken N).
  Local Notation wp_ref_peek := (UkShGettoken.wp_ref_peek N).
  Local Notation ushp_setb := UkShParseCmd.ushp_setb.
  Local Notation ushp_nulfold := UkShParseCmd.ushp_nulfold.
  Local Notation ushp_ext := UkShParseCmd.ushp_ext.
  Local Notation ushp_bytes_upd := (UkShParseCmd.ushp_bytes_upd N).
  Local Notation ushp_slot_read := (UkShParseCmd.ushp_slot_read N).
  Local Notation ushp_ro_byte := (UkShParseCmd.ushp_ro_byte N).
  Local Notation ushp_jrow_exec := (UkShParseCmd.ushp_jrow_exec N).
  Local Notation wp_kshp_nul_loop := (UkShParseCmd.wp_kshp_nul_loop N).
  Local Notation wp_kshp_nul_fin := (UkShParseCmd.wp_kshp_nul_fin N).
  Local Notation ushp_ustr_bytes := (UkShParseCmd.ushp_ustr_bytes N).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_redir_close := (UkShRedirCmd.ushp_redir_close N).
  Local Notation ushp_malloc_chain := (UkShRedirs.ushp_malloc_chain N).
  Local Notation ushp_malloc_chain_split := (UkShRedirs.ushp_malloc_chain_split N).
  Local Notation ushp_redirs_at := (UkShRedirs.ushp_redirs_at N).
  Local Notation wp_ref_parseexec := (UkShArgs.wp_ref_parseexec N).
  Local Notation ushp_pipe_node := (UkShPipeNode.ushp_pipe_node N).
  Local Notation ushp_pipe_close := (UkShPipeNode.ushp_pipe_close N).
  Local Notation ushp_jrow_pipe := (UkShPipeNode.ushp_jrow_pipe N).
  Local Notation wp_kshp_pipecmd := (UkShPipeCmd.wp_kshp_pipecmd N).
(*ALIASES-END*)

  (* ===================================================================== *)
  (* (0) THE ADDRESSED TREE                                                 *)
  (* ===================================================================== *)

  Fixpoint ushp_atree (s0 p : Z) (t : ushp_cmd) (a : ushp_ptr) : iProp Σ :=
    match t with
    | UshpExec toks =>
        match a with
        | UpExec => (⌜ p + 168 < Z64 ⌝ ∗ ushp_exec_at s0 p toks)%I
        | _ => False%I
        end
    | UshpRedir c q e mode fd =>
        match a with
        | UpRedir pc ac =>
            (ushp_redir_node s0 p pc q e mode fd ∗ ushp_atree s0 pc c ac)%I
        | _ => False%I
        end
    | UshpPipe l r =>
        match a with
        | UpPipe pl pr al ar =>
            (ushp_pipe_node p pl pr ∗ ushp_atree s0 pl l al ∗ ushp_atree s0 pr r ar)%I
        | _ => False%I
        end
    | UshpList _ _ => False%I
    | UshpBack _ => False%I
    end.

  Definition ushp_otree (s0 p : Z) (t : ushp_cmd) : iProp Σ :=
    (∃ a : ushp_ptr, ushp_atree s0 p t a)%I.

  (* the one-way door to the published tree *)
  Lemma ushp_atree_close (s0 : Z) (t : ushp_cmd) :
    forall (p : Z) (a : ushp_ptr), ushp_atree s0 p t a -∗ ushp_tree s0 p t.
  Proof using .
    induction t as [ toks | c IH q e mode fd | l IHl r IHr | l _ r _ | c _ ];
      intros p a; destruct a as [| pc ac | pl pr al ar ]; cbn [ushp_atree];
      try (iIntros "%F"; exact (False_ind _ F)).
    - iIntros "(_ & H)". cbn [UkShParse.ushp_tree]. iExact "H".
    - iIntros "(Hn & Hc)". iDestruct (IH pc ac with "Hc") as "Hc".
      iApply (ushp_redir_close with "Hn Hc").
    - iIntros "(Hn & Hl & Hr)".
      iDestruct (IHl pl al with "Hl") as "Hl". iDestruct (IHr pr ar with "Hr") as "Hr".
      iApply (ushp_pipe_close with "Hn Hl Hr").
  Qed.

  Lemma ushp_otree_close (s0 p : Z) (t : ushp_cmd) :
    ushp_otree s0 p t -∗ ushp_tree s0 p t.
  Proof using .
    iIntros "(%a & H)". iApply (ushp_atree_close with "H").
  Qed.

  (* parseexec's open answer -- the exec node and the redirect chain around
     it -- is an addressed tree of the wrapped command *)
  Lemma ushp_atree_of_redirs (s0 root : Z) (rs : list rredir) :
    forall (cmd : Z) (c : ushp_cmd) (a : ushp_ptr),
      ushp_atree s0 cmd c a -∗ ushp_redirs_at s0 root cmd rs -∗
      ushp_otree s0 root (ref_wrap c rs).
  Proof using .
    induction rs as [| r rs IH ]; intros cmd c a; cbn [UkShRedirs.ushp_redirs_at].
    - iIntros "Hc %E". subst root. iExists a. iExact "Hc".
    - iIntros "Hc (%p1 & Hn & Hrest)". rewrite ref_wrap_cons.
      iApply (IH p1 _ (UpRedir cmd a) with "[Hn Hc] Hrest").
      cbn [ushp_atree]. iFrame "Hn Hc".
  Qed.

  (* ---- the three shapes, read back for the corollaries ----------------- *)
  Lemma ushp_otree_exec_inv (s0 p : Z) (toks : list (nat * nat)) :
    ushp_otree s0 p (UshpExec toks) -∗ ⌜ p + 168 < Z64 ⌝ ∗ ushp_exec_at s0 p toks.
  Proof using .
    iIntros "(%a & H)". destruct a as [| pc ac | pl pr al ar ]; cbn [ushp_atree];
      [ iExact "H" | iDestruct "H" as %[] | iDestruct "H" as %[] ].
  Qed.

  Lemma ushp_otree_redir_exec_inv (s0 p : Z) (toks : list (nat * nat)) (q e : nat)
      (mode fd : Z) :
    ushp_otree s0 p (UshpRedir (UshpExec toks) q e mode fd) -∗
    ∃ pe : Z, ⌜ pe + 168 < Z64 ⌝ ∗ ushp_redir_node s0 p pe q e mode fd ∗ ushp_exec_at s0 pe toks.
  Proof using .
    iIntros "(%a & H)". destruct a as [| pe ac | pl pr al ar ]; cbn [ushp_atree];
      [ iDestruct "H" as %[] | | iDestruct "H" as %[] ].
    destruct ac as [| pc' ac' | pl' pr' al' ar' ]; cbn [ushp_atree];
      [ | iDestruct "H" as "(_ & %F)"; exact (False_ind _ F)
        | iDestruct "H" as "(_ & %F)"; exact (False_ind _ F) ].
    iDestruct "H" as "(Hn & %Hpe & He)". iExists pe. iFrame "Hn He". iPureIntro. exact Hpe.
  Qed.

  Lemma ushp_otree_pipe_exec_inv (s0 p : Z) (toksl toksr : list (nat * nat)) :
    ushp_otree s0 p (UshpPipe (UshpExec toksl) (UshpExec toksr)) -∗
    ∃ pl pr : Z, ⌜ pl + 168 < Z64 ⌝ ∗ ⌜ pr + 168 < Z64 ⌝ ∗
      ushp_pipe_node p pl pr ∗ ushp_exec_at s0 pl toksl ∗ ushp_exec_at s0 pr toksr.
  Proof using .
    iIntros "(%a & H)". destruct a as [| pe ac | pl pr al ar ]; cbn [ushp_atree];
      [ iDestruct "H" as %[] | iDestruct "H" as %[] | ].
    destruct al as [| pc' ac' | pl' pr' al' ar' ]; cbn [ushp_atree];
      [ | iDestruct "H" as "(_ & %F & _)"; exact (False_ind _ F)
        | iDestruct "H" as "(_ & %F & _)"; exact (False_ind _ F) ].
    destruct ar as [| pc' ac' | pl' pr' al' ar' ]; cbn [ushp_atree];
      [ | iDestruct "H" as "(_ & _ & %F)"; exact (False_ind _ F)
        | iDestruct "H" as "(_ & _ & %F)"; exact (False_ind _ F) ].
    iDestruct "H" as "(Hn & (%Hpl & Hl) & (%Hpr & Hr))".
    iExists pl, pr. iFrame "Hn Hl Hr". iPureIntro. exact (conj Hpl Hpr).
  Qed.

  (* peek's tables at the top of the parser, as the reference's lists *)
  Lemma ushp_T_pipe_tl : [rb_bar] = ushp_lit ushp_T_pipe <$> seq 0%nat 1.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_back_tl : [rb_amp] = ushp_lit ushp_T_back <$> seq 0%nat 1.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_list_tl : [rb_semi] = ushp_lit ushp_T_list <$> seq 0%nat 1.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_none_tl : (@nil (bv 8)) = ushp_lit ushp_T_none <$> seq 0%nat 0.
  Proof using . reflexivity. Qed.

  (* ===================================================================== *)
  (* (2) parsepipe FROM ITS ENTRY THROUGH THE '|' PEEK                       *)
  (*                                                                        *)
  (*   0x682..0x690  the prologue (k = 6, no locals)                         *)
  (*   0x692..0x698  s2 := ps; s4 := ps; s1 := es; jal parseexec             *)
  (*   0x69c         s3 := the node                                          *)
  (*   0x69e..0x6aa  the pipe table, peek's arguments, jal peek              *)
  (*                                                                        *)
  (* ...and the continuation is at 0x6ae, the [c.bnez a0] that decides the   *)
  (* turn, with everything the two arms and the shared tail need: the       *)
  (* frame's words, the register file's facts, the sub-command's tree and   *)
  (* the cursor at the peek's answer.                                       *)
  (* ===================================================================== *)

  Lemma wp_ref_pp_head {Pex : iProp Σ} (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps s0 : Z) (len off n s s1 : nat) (f : nat -> bv 8) (w0 : mword 64)
      (t1 : ushp_cmd) (hit : bool) (UM UM1 : iProp Σ) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope len f ->
    ref_parseexec len f n off = Some (t1, s) ->
    ref_peek len f s [rb_bar] = (hit, s1) ->
    ushp_malloc_chain (ushp_nodes t1) UM UM1 ->
    (ref_has_redir t1 = true -> (8 <= nn)%nat) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe) (6 + (16 + (24 + nn))) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 8 * Z.of_nat 6 <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ uint (m !!! Regidx csp_rs1) < Z64 ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1
         = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 6)) ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int (if hit then 1 else 0) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
       ⌜ m' !!! Regidx s3_idx = mword_of_int p ⌝ -∗
       ⌜ m' !!! Regidx s4_idx = mword_of_int ps ⌝ -∗
       ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
           Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
           Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
           Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
           m' !!! Regidx q = m !!! Regidx q ⌝ -∗
       ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)],
          uword γd (uint (m !!! Regidx csp_rs1) - 8 * (Z.of_nat i + 1))
            (match i with
             | 0%nat => m !!! Regidx ra_idx
             | 1%nat => m !!! Regidx s0_idx
             | 2%nat => m !!! Regidx s1_idx
             | 3%nat => m !!! Regidx s2_idx
             | 4%nat => m !!! Regidx s3_idx
             | _ => m !!! Regidx s4_idx end)) -∗
       ustack γd (mword_of_int (uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat 6)) 0 -∗
       ushp_otree s0 p t1 -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat s1)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UM1 -∗
       Pex -∗
       urun N h' m' (mword_of_int 0x6ae) (16 + (24 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hoffle Hw0 Hscope Hex Hpk Hchain Hnn Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    assert (Hs : (s <= len)%nat)
      by exact (proj2 (ref_parseexec_bounded len f n off t1 s Hoffle Hex)).
    rewrite shpp_parsepipe.
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x682..0x690  the prologue ---- *)
    iApply (wp_kshp_frame_pro 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] 0x682
              (fun i : nat => match i with
                              | 0%nat => 0x684 | 1%nat => 0x686
                              | 2%nat => 0x688 | 3%nat => 0x68a
                              | 4%nat => 0x68c | 5%nat => 0x68e
                              | _ => 0x690 end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (16 + (24 + nn)) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_682 with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_684 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_686 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_688 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68e with "Hcode") | done ]. }
    { iApply (uis_shp_690 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (mA := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (HmA : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    mA !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (HspA : mA !!! Regidx csp_rs1 = spn).
    { rewrite (HmA csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x692  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv N h1 mA (mword_of_int 0x692) s2_idx a0_idx
              (mword_of_int ps) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_692 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> mA).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m2 !!! Regidx q = mA !!! Regidx q)
      by (intros q Hq; exact (upd_ne mA (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x694  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0x694) s4_idx a0_idx
              (mword_of_int ps) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_694 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x696  c.mv s1,a1 ---- *)
    iApply (wp_uk_cmv N h3 m3 (mword_of_int 0x696) s1_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (HmA a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_696 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x698  jal 590 <parseexec> ---- *)
    iApply (wp_uk_jal N h4 m4 (mword_of_int 0x698)
              (mword_of_int 2096888 : mword 21) ra_idx
              (mword_of_int 0x590) (mword_of_int 0x69c) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_698 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x69c : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret5 : ret_pc (m5 !!! Regidx ra_idx) = mword_of_int 0x69c).
    { rewrite (upd_eq m4 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x69c : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (HmA a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_5 : m5 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate))
              (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (HmA a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    rewrite <- shpp_parseexec.
    (* THE SUB-COMMAND: the general parseexec at the reference's answer, its
       open answer closed to the addressed tree *)
    iApply (wp_ref_parseexec h5 m5 dq dw dv ps s0 len off n s f w0 t1 UM UM1 nn
              Ha0_5 Ha1_5 Hoffle Hw0 Hscope Hex Hchain Hnn Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (p pe toks rs) "%Ht1 %Hpe Hexec Hrat Hcur Hstr Hws Hsy".
    iIntros (h6 m6) "%Hcs56 %Ha0_6 HM1 Hpay Hrun".
    rewrite Eret5.
    iDestruct (ushp_atree_of_redirs s0 p rs pe (UshpExec toks) UpExec
                 with "[Hexec] Hrat") as "Hot".
    { cbn [ushp_atree]. iFrame "Hexec". iPureIntro. exact Hpe. }
    rewrite <- Ht1.
    (* ---- 0x69c  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv N h6 m6 (mword_of_int 0x69c) s3_idx a0_idx
              (mword_of_int p) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_69c with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x69e/0x6a2  the pipe table ---- *)
    iApply (wp_uk_auipc N h7 m7 (mword_of_int 0x69e)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x169e) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_69e with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0x169e : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_8 : m8 !!! Regidx a2_idx = mword_of_int 0x169e)
      by exact (upd_eq m7 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x169e : mword 64))).
    iApply (wp_uk_addi N h8 m8 (mword_of_int 0x6a2)
              (mword_of_int 3218 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_pipe) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_8; unfold ushp_T_pipe;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6a2 with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_pipe : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x6a6/0x6a8  peek's two other arguments ---- *)
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate))
              (Hm8 s1_idx ltac:(vm_compute; discriminate))
              (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hcs56 s1_idx ltac:(vm_compute; reflexivity))
              (Hm5 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hcs56 s2_idx ltac:(vm_compute; reflexivity))
              (Hm5 s2_idx ltac:(vm_compute; discriminate))
              (Hm4 s2_idx ltac:(vm_compute; discriminate))
              (Hm3 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s2_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    iApply (wp_uk_cmv N h9 m9 (mword_of_int 0x6a6) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6a6 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h10 m10 (mword_of_int 0x6a8) a0_idx
              s2_idx (mword_of_int ps) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6a8 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x6aa  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h11 m11 (mword_of_int 0x6aa)
              (mword_of_int 2096542 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x6ae) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6aa with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x6ae : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x6ae).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x6ae : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_12 : m12 !!! Regidx a2_idx = mword_of_int ushp_T_pipe).
    { rewrite (Hm12 a2_idx ltac:(vm_compute; discriminate))
              (Hm11 a2_idx ltac:(vm_compute; discriminate))
              (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_pipe : mword 64))). }
    rewrite <- shpp_peek.
    (* THE '|' PEEK, at the reference's answer *)
    iApply (wp_ref_peek h12 m12 dq dw true DfracDiscarded ps s0
              ushp_T_pipe len s 1 f (ushp_lit ushp_T_pipe)
              (mword_of_int (s0 + Z.of_nat s)) (30 + nn) [rb_bar] hit s1
              Ha0_12 Ha1_12 Ha2_12 Hs eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_pipe; lia)
              ltac:(unfold ushp_T_pipe, Z64; lia) Hps0 Hps8 Hpssz
              ushp_T_pipe_tl Hpk
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_pipe 1 DfracDiscarded
                ushp_T_pipe_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h13 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12.
    (* ---- the register file the arms start from ---- *)
    assert (Hs1_13 : m13 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_9. }
    assert (Hs4_13 : m13 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hcs1213 s4_idx ltac:(vm_compute; reflexivity))
              (Hm12 s4_idx ltac:(vm_compute; discriminate))
              (Hm11 s4_idx ltac:(vm_compute; discriminate))
              (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hcs56 s4_idx ltac:(vm_compute; reflexivity))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m6 (Regidx s3_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              m13 !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3 Hq4.
      rewrite (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm7 q Hq3) (Hcs56 q Hq)
              (Hm5 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q Hq1) (Hm3 q Hq4) (Hm2 q Hq2) (HmA q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hsp13 : m13 !!! Regidx csp_rs1 = spn).
    { rewrite (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs56 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact HspA. }
    iApply ("Hcont" $! h13 m13 p
              with "[] [] [] [] [] [] [] [] [] Hsl Hloc Hot Hcur Hstr Hws Hsy HM1 Hpay Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro. exact Hhi.
    - iPureIntro. exact Hsp13.
    - iPureIntro. exact Ha0_13.
    - iPureIntro. exact Hs1_13.
    - iPureIntro. exact Hs3_13.
    - iPureIntro. exact Hs4_13.
    - iPureIntro. exact Hkeep.
  Qed.


  (* ===================================================================== *)
  (* (2b) parsepipe's TAIL, 0x6b0..0x6c0: a0 := s3, the epilogue             *)
  (* ===================================================================== *)

  Lemma wp_ref_pp_tail (h : CpuId) (m me : regfile) (root : Z) (nn : nat) :
    uint (m !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat 6 <= uint (m !!! Regidx csp_rs1) ->
    uint (m !!! Regidx csp_rs1) < Z64 ->
    me !!! Regidx csp_rs1 = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 6)) ->
    me !!! Regidx s3_idx = mword_of_int root ->
    (forall q : mword 5, ucallee_saved_idx q = true ->
       Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
       Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
       Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
       me !!! Regidx q = m !!! Regidx q) ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 5 : mword 6);
            (s0_idx, mword_of_int 4 : mword 6);
            (s1_idx, mword_of_int 3 : mword 6);
            (s2_idx, mword_of_int 2 : mword 6);
            (s3_idx, mword_of_int 1 : mword 6);
            (s4_idx, mword_of_int 0 : mword 6)],
       uword γd (uint (m !!! Regidx csp_rs1) - 8 * (Z.of_nat i + 1))
         (match i with
          | 0%nat => m !!! Regidx ra_idx
          | 1%nat => m !!! Regidx s0_idx
          | 2%nat => m !!! Regidx s1_idx
          | 3%nat => m !!! Regidx s2_idx
          | 4%nat => m !!! Regidx s3_idx
          | _ => m !!! Regidx s4_idx end)) -∗
    ustack γd (mword_of_int (uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat 6)) 0 -∗
    urun N h me (mword_of_int 0x6b0) (16 + (24 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int root ⌝ -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (6 + (16 + (24 + nn))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hal8 Hlo Hhi Hspe Hs3 Hkeep.
    iIntros "#Hcode Hsl Hloc Hrun Hcont".
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x6b0  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv N h me (mword_of_int 0x6b0) a0_idx
              s3_idx (mword_of_int root) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3; symmetry; exact (ushp_mv_val root))
              with "[] Hrun").
    { iApply (uis_shp_6b0 with "Hcode"). }
    iIntros (h1) "Hrun".
    set (mf := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int root : mword 64)]> me).
    assert (Hmf : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    mf !!! Regidx q = me !!! Regidx q)
      by (intros q Hq; exact (upd_ne me (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hspf : mf !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by (rewrite (Hmf csp_rs1 ltac:(vm_compute; discriminate)); exact Hspe).
    (* ---- 0x6b2..0x6c0  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x6b2 | 1%nat => 0x6b4
                              | 2%nat => 0x6b6 | 3%nat => 0x6b8
                              | 4%nat => 0x6ba | 5%nat => 0x6bc
                              | _ => 0x6be end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 6)) vals
              (16 + (24 + nn)) h1 mf
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspf
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_6b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6bc with "Hcode") | done ]. }
    { iApply (uis_shp_6be with "Hcode"). }
    { iApply (uis_shp_6c0 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" with "[] [] Hrun").
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] vals m mf sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        rewrite (Hmf q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6) eq_refl)
                 (Hmiss 5%nat s4_idx (mword_of_int 0 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq me (Regidx a0_idx)
                 (regval_into_reg (mword_of_int root : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  (* ===================================================================== *)
  (* (3) parsepipe, THE WHOLE FUNCTION, at the reference's answer            *)
  (*                                                                        *)
  (* By induction on the fuel: the outer call runs at [S n], the inner       *)
  (* parseexec and the recursion at [n], and the equation drives every       *)
  (* case.  Fuel 1 is vacuous -- parseexec at fuel 0 is [None] -- so the     *)
  (* recursion is always the hypothesis at fuel [S n], on the SAME line at   *)
  (* the cursor the '|' gettoken left.                                       *)
  (*                                                                        *)
  (*   0x6ae  c.bnez a0        -- the turn                                   *)
  (*   0x6c2..0x6c8            a3 := 0; a2 := 0; a1 := es; a0 := ps          *)
  (*   0x6ca  jal gettoken     -- consumes the '|'                            *)
  (*   0x6ce..0x6d2            a1 := es; a0 := ps; jal parsepipe             *)
  (*   0x6d6..0x6da            a1 := the right node; a0 := the left; jal     *)
  (*                           pipecmd                                       *)
  (*   0x6de  c.mv s3,a0 ; 0x6e0  c.j 6b0                                    *)
  (* ===================================================================== *)

  Lemma wp_ref_parsepipe {Pex : iProp Σ} (dq dw dv : dfrac) (ps s0 : Z)
      (len : nat) (f : nat -> bv 8) (n : nat) :
    forall (h : CpuId) (m : regfile) (off fin : nat) (w0 : mword 64)
           (t : ushp_cmd) (UM UM' : iProp Σ) (nn : nat),
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope len f ->
    ref_parsepipe len f (S n) off = Some (t, fin) ->
    ushp_malloc_chain (ushp_nodes t) UM UM' ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe) (ushp_pp_room t + nn) -∗
    (∀ root : Z,
       ushp_otree s0 root t -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int root ⌝ -∗
           UM' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (ushp_pp_room t + nn) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    induction n as [| n IH ];
      intros h m off fin w0 t UM UM' nn Ha0 Ha1 Hoffle Hw0 Hscope Href Hchain
             Hs0 Hs64 Hps0 Hps8 Hpssz.
    { (* fuel 1: parseexec at fuel 0 fails *)
      exfalso. rewrite ref_parsepipe_S in Href.
      assert (E0 : ref_parseexec len f 0 off = None).
      { unfold ref_parseexec.
        destruct (ref_peek len f off [rb_lpar]) as [[] s]; reflexivity. }
      rewrite E0 in Href. discriminate Href. }
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    (* ---- the reference's answer, taken apart ---- *)
    rewrite ref_parsepipe_S in Href.
    destruct (ref_parseexec len f (S n) off) as [[ t1 s ] | ] eqn:Hex;
      [ | discriminate Href ].
    destruct (ref_peek len f s [rb_bar]) as [ bar s1 ] eqn:Hpk.
    assert (Hs : (s <= len)%nat)
      by exact (proj2 (ref_parseexec_bounded len f (S n) off t1 s Hoffle Hex)).
    assert (Hs1 : s1 = ref_skip len f s)
      by (destruct bar; [ exact (proj1 (ref_peek_hit_inv _ _ _ _ _ Hpk))
                        | exact (ref_peek_miss_inv _ _ _ _ _ Hpk) ]).
    assert (Hs1le : (s1 <= len)%nat) by (rewrite Hs1; exact (ref_skip_le len f s Hs)).
    destruct bar.
    - (* ================= THE TURN ================= *)
      destruct (ref_gettoken len f s1) as [[[ gr gq ] ge ] s2 ] eqn:Eg.
      assert (Hs2le : (s2 <= len)%nat) by exact (ref_gettoken_fin_le len f s1 _ _ _ _ Hs1le Eg).
      destruct (ref_parsepipe len f (S n) s2) as [[ r s3 ] | ] eqn:Er;
        [ | discriminate Href ].
      injection Href as <- <-.
      (* the budget in the landed spelling, and the recursion's share of it *)
      pose proof (ushp_pp_room_ge r) as Hrge.
      pose proof (ushp_pex_room_ge t1) as Hlge.
      assert (Ebud : (ushp_pp_room (UshpPipe t1 r) + nn)%nat
                     = (6 + (16 + (24 + (Nat.max (ushp_pex_room t1) (ushp_pp_room r) - 40 + nn))))%nat)
        by (cbn [ushp_pp_room]; lia).
      set (nn' := (Nat.max (ushp_pex_room t1) (ushp_pp_room r) - 40 + nn)%nat) in *.
      (* the recursion's share: the right spine's room, the rest carried *)
      set (nnr := (Nat.max (ushp_pex_room t1) (ushp_pp_room r) - ushp_pp_room r + nn)%nat) in *.
      assert (Ebud2 : (16 + (24 + nn'))%nat = (ushp_pp_room r + nnr)%nat)
        by (unfold nn', nnr; lia).
      (* the left command's guard: a REDIR on top means its room is 48 *)
      assert (Hguard : ref_has_redir t1 = true -> (8 <= nn')%nat)
        by (intro H; pose proof (ushp_pex_room_has t1 H) as E; unfold nn'; lia).
      rewrite Ebud.
      (* the allocations: the left command's, the right's, then pipecmd's *)
      replace (ushp_nodes (UshpPipe t1 r)) with (ushp_nodes t1 + (ushp_nodes r + 1))%nat
        in Hchain by (cbn [ushp_nodes]; lia).
      destruct (ushp_malloc_chain_split (ushp_nodes t1) (ushp_nodes r + 1) UM UM' Hchain)
        as (UM1 & Hch1 & Hch23).
      destruct (ushp_malloc_chain_split (ushp_nodes r) 1 UM1 UM' Hch23)
        as (UM2 & Hch2 & Hch3).
      destruct Hch3 as (UM3 & Hmal23 & E3). cbn [UkShRedirs.ushp_malloc_chain] in E3.
      subst UM3.
      iApply (wp_ref_pp_head h m dq dw dv ps s0 len off (S n) s s1 f w0 t1 true UM UM1 nn'
                Ha0 Ha1 Hoffle Hw0 Hscope Hex Hpk Hch1 Hguard Hs0 Hs64 Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
      iIntros (h13 m13 pl) "%Hal8 %Hlo %Hhi %Hsp13 %Ha0_13 %Hs1_13 %Hs3_13 %Hs4_13 %Hkeep13
                            Hsl Hloc Hotl Hcur Hstr Hws Hsy HM1 Hpay Hrun".
      set (sp0 := m !!! Regidx csp_rs1) in *.
      (* ---- 0x6ae  c.bnez a0 -- TAKEN: there IS a pipe ---- *)
      iApply (wp_uk_cbnez N h13 m13 (mword_of_int 0x6ae)
                (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x6c2) (16 + (24 + nn'))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_13; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_6ae with "Hcode"). }
      iIntros (h14) "Hrun".
      (* ---- 0x6c2  c.li a3,0 ---- *)
      iApply (wp_uk_cli N h14 m13 (mword_of_int 0x6c2)
                (mword_of_int 0 : mword 6) a3_idx (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_6c2 with "Hcode"). }
      rewrite (ushp_pc_step 0x6c2 2). iIntros (h15) "Hrun".
      set (q1 := <[Regidx a3_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)]> m13).
      assert (Hq1 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                      q1 !!! Regidx r = m13 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne m13 (Regidx a3_idx) (Regidx r0) _ Hr)).
      assert (Ha3_q1 : q1 !!! Regidx a3_idx = mword_of_int 0).
      { rewrite (upd_eq m13 (Regidx a3_idx)
                   (regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
        apply bv_eq; vm_compute; reflexivity. }
      (* ---- 0x6c4  c.li a2,0 ---- *)
      iApply (wp_uk_cli N h15 q1 (mword_of_int 0x6c4)
                (mword_of_int 0 : mword 6) a2_idx (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_6c4 with "Hcode"). }
      rewrite (ushp_pc_step 0x6c4 2). iIntros (h16) "Hrun".
      set (q2 := <[Regidx a2_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)]> q1).
      assert (Hq2 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                      q2 !!! Regidx r = q1 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne q1 (Regidx a2_idx) (Regidx r0) _ Hr)).
      assert (Ha2_q2 : q2 !!! Regidx a2_idx = mword_of_int 0).
      { rewrite (upd_eq q1 (Regidx a2_idx)
                   (regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
        apply bv_eq; vm_compute; reflexivity. }
      (* ---- 0x6c6  c.mv a1,s1  --  es ---- *)
      iApply (wp_uk_cmv N h16 q2 (mword_of_int 0x6c6) a1_idx s1_idx
                (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hq2 s1_idx ltac:(vm_compute; discriminate))
                        (Hq1 s1_idx ltac:(vm_compute; discriminate)) Hs1_13;
                      symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_6c6 with "Hcode"). }
      rewrite (ushp_pc_step 0x6c6 2). iIntros (h17) "Hrun".
      set (q3 := <[Regidx a1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat len) : mword 64)]> q2).
      assert (Hq3 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                      q3 !!! Regidx r = q2 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne q2 (Regidx a1_idx) (Regidx r0) _ Hr)).
      (* ---- 0x6c8  c.mv a0,s4  --  &s ---- *)
      iApply (wp_uk_cmv N h17 q3 (mword_of_int 0x6c8) a0_idx s4_idx
                (mword_of_int ps) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hq3 s4_idx ltac:(vm_compute; discriminate))
                        (Hq2 s4_idx ltac:(vm_compute; discriminate))
                        (Hq1 s4_idx ltac:(vm_compute; discriminate)) Hs4_13;
                      symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_6c8 with "Hcode"). }
      rewrite (ushp_pc_step 0x6c8 2). iIntros (h18) "Hrun".
      set (q4 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int ps : mword 64)]> q3).
      assert (Hq4 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                      q4 !!! Regidx r = q3 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne q3 (Regidx a0_idx) (Regidx r0) _ Hr)).
      (* ---- 0x6ca  jal 310 <gettoken> -- consumes the '|' ---- *)
      iApply (wp_uk_jal N h18 q4 (mword_of_int 0x6ca)
                (mword_of_int 2096198 : mword 21) ra_idx
                (mword_of_int 0x310) (mword_of_int 0x6ce) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_6ca with "Hcode"). }
      iIntros (h19) "Hrun".
      set (q5 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x6ce : mword 64)]> q4).
      assert (Hq5 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                      q5 !!! Regidx r = q4 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne q4 (Regidx ra_idx) (Regidx r0) _ Hr)).
      assert (Eret_g : ret_pc (q5 !!! Regidx ra_idx) = mword_of_int 0x6ce);
        [ rewrite (upd_eq q4 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x6ce : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_q5 : q5 !!! Regidx a0_idx = mword_of_int ps).
      { rewrite (Hq5 a0_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq q3 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))). }
      assert (Ha1_q5 : q5 !!! Regidx a1_idx
                       = mword_of_int (s0 + Z.of_nat len)).
      { rewrite (Hq5 a1_idx ltac:(vm_compute; discriminate))
                (Hq4 a1_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq q2 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
      assert (Ha2_q5 : q5 !!! Regidx a2_idx = mword_of_int 0).
      { rewrite (Hq5 a2_idx ltac:(vm_compute; discriminate))
                (Hq4 a2_idx ltac:(vm_compute; discriminate))
                (Hq3 a2_idx ltac:(vm_compute; discriminate)). exact Ha2_q2. }
      assert (Ha3_q5 : q5 !!! Regidx a3_idx = mword_of_int 0).
      { rewrite (Hq5 a3_idx ltac:(vm_compute; discriminate))
                (Hq4 a3_idx ltac:(vm_compute; discriminate))
                (Hq3 a3_idx ltac:(vm_compute; discriminate))
                (Hq2 a3_idx ltac:(vm_compute; discriminate)). exact Ha3_q1. }
      rewrite <- shpp_gettoken.
      (* gettoken at the '|', at the reference's own answer; both
         out-parameters are NULL, which is [ushp_cell]'s left disjunct *)
      iApply (wp_ref_gettoken h19 q5 dq dw dv ps 0 0 s0 len s1 f
                (mword_of_int (s0 + Z.of_nat s1)) (mword_of_int 0) (mword_of_int 0)
                (30 + nn') gr gq ge s2
                Ha0_q5 Ha1_q5 Ha2_q5 Ha3_q5 Hs1le eq_refl Hscope Hs0 Hs64
                Hps0 Hps8 Hpssz Eg
                with "Hcode Hcur [] [] Hstr Hws Hsy Hrun").
      { iLeft. iPureIntro. reflexivity. }
      { iLeft. iPureIntro. reflexivity. }
      iIntros "Hcur _ _ Hstr Hws Hsy" (h20 g1) "%Hcsg %Ha0_g Hrun".
      rewrite Eret_g.
      (* ---- 0x6ce  c.mv a1,s1 ---- *)
      assert (Hs1_g1 : g1 !!! Regidx s1_idx
                       = mword_of_int (s0 + Z.of_nat len)).
      { rewrite (Hcsg s1_idx ltac:(vm_compute; reflexivity))
                (Hq5 s1_idx ltac:(vm_compute; discriminate))
                (Hq4 s1_idx ltac:(vm_compute; discriminate))
                (Hq3 s1_idx ltac:(vm_compute; discriminate))
                (Hq2 s1_idx ltac:(vm_compute; discriminate))
                (Hq1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_13. }
      assert (Hs4_g1 : g1 !!! Regidx s4_idx = mword_of_int ps).
      { rewrite (Hcsg s4_idx ltac:(vm_compute; reflexivity))
                (Hq5 s4_idx ltac:(vm_compute; discriminate))
                (Hq4 s4_idx ltac:(vm_compute; discriminate))
                (Hq3 s4_idx ltac:(vm_compute; discriminate))
                (Hq2 s4_idx ltac:(vm_compute; discriminate))
                (Hq1 s4_idx ltac:(vm_compute; discriminate)). exact Hs4_13. }
      iApply (wp_uk_cmv N h20 g1 (mword_of_int 0x6ce) a1_idx s1_idx
                (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1_g1; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_6ce with "Hcode"). }
      rewrite (ushp_pc_step 0x6ce 2). iIntros (h21) "Hrun".
      set (g2 := <[Regidx a1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat len) : mword 64)]> g1).
      assert (Hg2 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                      g2 !!! Regidx r = g1 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne g1 (Regidx a1_idx) (Regidx r0) _ Hr)).
      (* ---- 0x6d0  c.mv a0,s4 ---- *)
      iApply (wp_uk_cmv N h21 g2 (mword_of_int 0x6d0) a0_idx s4_idx
                (mword_of_int ps) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hg2 s4_idx ltac:(vm_compute; discriminate))
                        Hs4_g1; symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_6d0 with "Hcode"). }
      rewrite (ushp_pc_step 0x6d0 2). iIntros (h22) "Hrun".
      set (g3 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int ps : mword 64)]> g2).
      assert (Hg3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                      g3 !!! Regidx r = g2 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne g2 (Regidx a0_idx) (Regidx r0) _ Hr)).
      (* ---- 0x6d2  jal 682 <parsepipe> -- THE RECURSION ---- *)
      iApply (wp_uk_jal N h22 g3 (mword_of_int 0x6d2)
                (mword_of_int 2097072 : mword 21) ra_idx
                (mword_of_int 0x682) (mword_of_int 0x6d6) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_6d2 with "Hcode"). }
      iIntros (h23) "Hrun".
      set (g4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x6d6 : mword 64)]> g3).
      assert (Hg4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                      g4 !!! Regidx r = g3 !!! Regidx r)
        by (intros r0 Hr; exact (upd_ne g3 (Regidx ra_idx) (Regidx r0) _ Hr)).
      assert (Eret_r : ret_pc (g4 !!! Regidx ra_idx) = mword_of_int 0x6d6);
        [ rewrite (upd_eq g3 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x6d6 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_g4 : g4 !!! Regidx a0_idx = mword_of_int ps).
      { rewrite (Hg4 a0_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq g2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))). }
      assert (Ha1_g4 : g4 !!! Regidx a1_idx
                       = mword_of_int (s0 + Z.of_nat len)).
      { rewrite (Hg4 a1_idx ltac:(vm_compute; discriminate))
                (Hg3 a1_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq g1 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
      rewrite <- shpp_parsepipe.
      (* THE RECURSION: the induction hypothesis at the cursor the '|'
         gettoken left, on the same line *)
      iEval (rewrite Ebud2) in "Hrun".
      iApply (IH h23 g4 s2 s3 (mword_of_int (s0 + Z.of_nat s2)) r UM1 UM2 nnr
                Ha0_g4 Ha1_g4 Hs2le eq_refl Hscope Er Hch2 Hs0 Hs64 Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hsy HM1 Hpx Hpay Hrun").
      iIntros (pr) "Hotr Hcur Hstr Hws Hsy".
      iIntros (h24 r1) "%Hcsr %Ha0_r HM2 Hpay Hrun".
      iEval (rewrite <- Ebud2) in "Hrun".
      rewrite Eret_r.
      (* ---- 0x6d6  c.mv a1,a0  --  the RIGHT node ---- *)
      iApply (wp_uk_cmv N h24 r1 (mword_of_int 0x6d6) a1_idx a0_idx
                (mword_of_int pr) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_r; symmetry; exact (ushp_mv_val pr))
                with "[] Hrun").
      { iApply (uis_shp_6d6 with "Hcode"). }
      rewrite (ushp_pc_step 0x6d6 2). iIntros (h25) "Hrun".
      set (r2 := <[Regidx a1_idx
                   := regval_into_reg (mword_of_int pr : mword 64)]> r1).
      assert (Hr2 : forall r0 : mword 5, Regidx r0 <> Regidx a1_idx ->
                      r2 !!! Regidx r0 = r1 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne r1 (Regidx a1_idx) (Regidx r0) _ Hr)).
      (* ---- 0x6d8  c.mv a0,s3  --  the LEFT node ---- *)
      assert (Hs3_r1 : r1 !!! Regidx s3_idx = mword_of_int pl).
      { rewrite (Hcsr s3_idx ltac:(vm_compute; reflexivity))
                (Hg4 s3_idx ltac:(vm_compute; discriminate))
                (Hg3 s3_idx ltac:(vm_compute; discriminate))
                (Hg2 s3_idx ltac:(vm_compute; discriminate))
                (Hcsg s3_idx ltac:(vm_compute; reflexivity))
                (Hq5 s3_idx ltac:(vm_compute; discriminate))
                (Hq4 s3_idx ltac:(vm_compute; discriminate))
                (Hq3 s3_idx ltac:(vm_compute; discriminate))
                (Hq2 s3_idx ltac:(vm_compute; discriminate))
                (Hq1 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_13. }
      iApply (wp_uk_cmv N h25 r2 (mword_of_int 0x6d8) a0_idx s3_idx
                (mword_of_int pl) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hr2 s3_idx ltac:(vm_compute; discriminate))
                        Hs3_r1; symmetry; exact (ushp_mv_val pl))
                with "[] Hrun").
      { iApply (uis_shp_6d8 with "Hcode"). }
      rewrite (ushp_pc_step 0x6d8 2). iIntros (h26) "Hrun".
      set (r3 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int pl : mword 64)]> r2).
      assert (Hr3 : forall r0 : mword 5, Regidx r0 <> Regidx a0_idx ->
                      r3 !!! Regidx r0 = r2 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne r2 (Regidx a0_idx) (Regidx r0) _ Hr)).
      (* ---- 0x6da  jal 260 <pipecmd> ---- *)
      iApply (wp_uk_jal N h26 r3 (mword_of_int 0x6da)
                (mword_of_int 2096006 : mword 21) ra_idx
                (mword_of_int 0x260) (mword_of_int 0x6de) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_6da with "Hcode"). }
      iIntros (h27) "Hrun".
      set (r4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x6de : mword 64)]> r3).
      assert (Hr4 : forall r0 : mword 5, Regidx r0 <> Regidx ra_idx ->
                      r4 !!! Regidx r0 = r3 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne r3 (Regidx ra_idx) (Regidx r0) _ Hr)).
      assert (Eret_c : ret_pc (r4 !!! Regidx ra_idx) = mword_of_int 0x6de);
        [ rewrite (upd_eq r3 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x6de : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_r4 : r4 !!! Regidx a0_idx = mword_of_int pl).
      { rewrite (Hr4 a0_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq r2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int pl : mword 64))). }
      assert (Ha1_r4 : r4 !!! Regidx a1_idx = mword_of_int pr).
      { rewrite (Hr4 a1_idx ltac:(vm_compute; discriminate))
                (Hr3 a1_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq r1 (Regidx a1_idx)
                 (regval_into_reg (mword_of_int pr : mword 64))). }
      rewrite <- UkShParse.shpp_pipecmd.
      (* pipecmd: the two subtrees ride through in [Sub] *)
      iApply (wp_kshp_pipecmd UM2 UM' Hmal23 h27 r4 pl pr
                (ushp_otree s0 pl t1 ∗ ushp_otree s0 pr r)%I (24 + nn')
                Ha0_r4 Ha1_r4
                with "Hcode HM2 Hpx Hpay [Hotl Hotr] Hrun").
      { iSplitL "Hotl"; [ iExact "Hotl" | iExact "Hotr" ]. }
      iIntros (h28 q11 t) "%Hcsc %Ha0_c %Htb Hpnode [Hotl Hotr] HM3 Hpay Hrun".
      rewrite Eret_c.
      iDestruct "Hotl" as (al) "Hal". iDestruct "Hotr" as (ar) "Har".
      iAssert (ushp_otree s0 t (UshpPipe t1 r)) with "[Hpnode Hal Har]" as "Hot".
      { iExists (UpPipe pl pr al ar). cbn [ushp_atree]. iFrame "Hpnode Hal Har". }
      (* ---- 0x6de  c.mv s3,a0  --  the PIPE node becomes the answer ---- *)
      iApply (wp_uk_cmv N h28 q11 (mword_of_int 0x6de) s3_idx a0_idx
                (mword_of_int t) (16 + (24 + nn'))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_c; symmetry; exact (ushp_mv_val t))
                with "[] Hrun").
      { iApply (uis_shp_6de with "Hcode"). }
      rewrite (ushp_pc_step 0x6de 2). iIntros (h29) "Hrun".
      set (q12 := <[Regidx s3_idx
                    := regval_into_reg (mword_of_int t : mword 64)]> q11).
      assert (Hq12 : forall r0 : mword 5, Regidx r0 <> Regidx s3_idx ->
                       q12 !!! Regidx r0 = q11 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne q11 (Regidx s3_idx) (Regidx r0) _ Hr)).
      assert (Hs3_q12 : q12 !!! Regidx s3_idx = mword_of_int t)
        by exact (upd_eq q11 (Regidx s3_idx)
                    (regval_into_reg (mword_of_int t : mword 64))).
      (* ---- 0x6e0  c.j 6b0 -- into the tail ---- *)
      iApply (wp_uk_cj N h29 q12 (mword_of_int 0x6e0)
                (mword_of_int 2024 : mword 11) (mword_of_int 0x6b0)
                (16 + (24 + nn'))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_6e0 with "Hcode"). }
      iIntros (h30) "Hrun".
      (* the whole turn, as one preservation fact over the head's *)
      assert (Hkeep : forall r0 : mword 5, ucallee_saved_idx r0 = true ->
                Regidx r0 <> Regidx csp_rs1 -> Regidx r0 <> Regidx s0_idx ->
                Regidx r0 <> Regidx s1_idx -> Regidx r0 <> Regidx s2_idx ->
                Regidx r0 <> Regidx s3_idx -> Regidx r0 <> Regidx s4_idx ->
                q12 !!! Regidx r0 = m !!! Regidx r0).
      { intros r0 Hr Hsp Hx0 Hx1 Hx2 Hx3 Hx4.
        rewrite (Hq12 r0 Hx3)
                (Hcsc r0 Hr)
                (Hr4 r0 (ushp_cs_ne r0 ra_idx Hr ltac:(vm_compute; reflexivity)))
                (Hr3 r0 (ushp_cs_ne r0 a0_idx Hr ltac:(vm_compute; reflexivity)))
                (Hr2 r0 (ushp_cs_ne r0 a1_idx Hr ltac:(vm_compute; reflexivity)))
                (Hcsr r0 Hr)
                (Hg4 r0 (ushp_cs_ne r0 ra_idx Hr ltac:(vm_compute; reflexivity)))
                (Hg3 r0 (ushp_cs_ne r0 a0_idx Hr ltac:(vm_compute; reflexivity)))
                (Hg2 r0 (ushp_cs_ne r0 a1_idx Hr ltac:(vm_compute; reflexivity)))
                (Hcsg r0 Hr)
                (Hq5 r0 (ushp_cs_ne r0 ra_idx Hr ltac:(vm_compute; reflexivity)))
                (Hq4 r0 (ushp_cs_ne r0 a0_idx Hr ltac:(vm_compute; reflexivity)))
                (Hq3 r0 (ushp_cs_ne r0 a1_idx Hr ltac:(vm_compute; reflexivity)))
                (Hq2 r0 (ushp_cs_ne r0 a2_idx Hr ltac:(vm_compute; reflexivity)))
                (Hq1 r0 (ushp_cs_ne r0 a3_idx Hr ltac:(vm_compute; reflexivity))).
        exact (Hkeep13 r0 Hr Hsp Hx0 Hx1 Hx2 Hx3 Hx4). }
      assert (Hspe : q12 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6))).
      { rewrite (Hq12 csp_rs1 ltac:(vm_compute; discriminate))
                (Hcsc csp_rs1 ltac:(vm_compute; reflexivity))
                (Hr4 csp_rs1 ltac:(vm_compute; discriminate))
                (Hr3 csp_rs1 ltac:(vm_compute; discriminate))
                (Hr2 csp_rs1 ltac:(vm_compute; discriminate))
                (Hcsr csp_rs1 ltac:(vm_compute; reflexivity))
                (Hg4 csp_rs1 ltac:(vm_compute; discriminate))
                (Hg3 csp_rs1 ltac:(vm_compute; discriminate))
                (Hg2 csp_rs1 ltac:(vm_compute; discriminate))
                (Hcsg csp_rs1 ltac:(vm_compute; reflexivity))
                (Hq5 csp_rs1 ltac:(vm_compute; discriminate))
                (Hq4 csp_rs1 ltac:(vm_compute; discriminate))
                (Hq3 csp_rs1 ltac:(vm_compute; discriminate))
                (Hq2 csp_rs1 ltac:(vm_compute; discriminate))
                (Hq1 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp13. }
      iApply (wp_ref_pp_tail h30 m q12 t nn' Hal8 Hlo Hhi Hspe Hs3_q12 Hkeep
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf mf) "%Hcs %Ha0f Hrun".
      iApply ("Hcont" $! t with "Hot Hcur Hstr Hws Hsy [%//] [%//] HM3 Hpay Hrun").
    - (* ================= THE MISS ================= *)
      injection Href as <- <-.
      destruct (ref_parseexec_wrap_inv len f (S n) off t1 s Hex) as (toks & rs & Ht1).
      (* the room is the frame over parseexec's need: eight more words at a
         REDIR on top, none at an EXEC *)
      set (nn' := (ushp_pex_extra t1 + nn)%nat) in *.
      assert (Ebud : (ushp_pp_room t1 + nn)%nat = (6 + (16 + (24 + nn')))%nat)
        by (unfold nn'; rewrite Ht1 (ushp_pp_room_wrap toks rs); unfold ushp_pex_room; lia).
      rewrite Ebud.
      iApply (wp_ref_pp_head h m dq dw dv ps s0 len off (S n) s s1 f w0 t1 false UM UM' nn'
                Ha0 Ha1 Hoffle Hw0 Hscope Hex Hpk Hchain (ushp_pex_extra_guard t1 nn)
                Hs0 Hs64 Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
      iIntros (h13 m13 p) "%Hal8 %Hlo %Hhi %Hsp13 %Ha0_13 %Hs1_13 %Hs3_13 %Hs4_13 %Hkeep13
                           Hsl Hloc Hot Hcur Hstr Hws Hsy HM' Hpay Hrun".
      (* ---- 0x6ae  c.bnez a0 -- NOT taken: there is no pipe ---- *)
      iApply (wp_uk_cbnez N h13 m13 (mword_of_int 0x6ae)
                (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx false (mword_of_int 0x6c2) (16 + (24 + nn'))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_13; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_6ae with "Hcode"). }
      iIntros (h14) "Hrun".
      iApply (wp_ref_pp_tail h14 m m13 p nn' Hal8 Hlo Hhi Hsp13 Hs3_13 Hkeep13
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf mf) "%Hcs %Ha0f Hrun".
      iApply ("Hcont" $! p with "Hot Hcur Hstr Hws Hsy [%//] [%//] HM' Hpay Hrun").
  Qed.


  (* ===================================================================== *)
  (* (4) parseline, THE WHOLE FUNCTION, at the reference's answer            *)
  (*                                                                        *)
  (*   0x6e2..0x6f0  the prologue (k = 6, no locals)                         *)
  (*   0x6f2..0x6f6  s2 := ps; s3 := es; jal parsepipe                       *)
  (*   0x6fa         s1 := the node                                          *)
  (*   0x6fc..0x704  the ampersand table; c.j into the loop's guard          *)
  (*   0x71a..0x724  peek(&) -- MISSES under the scope                       *)
  (*   0x726..0x736  the semicolon table, peek(;) -- MISSES                  *)
  (*   0x738..0x748  a0 := s1, the epilogue                                  *)
  (* ===================================================================== *)

  Lemma wp_ref_parseline {Pex : iProp Σ} (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps s0 : Z) (len off n fin : nat) (f : nat -> bv 8) (w0 : mword 64)
      (t : ushp_cmd) (UM UM' : iProp Σ) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope len f ->
    ref_parseline len f (S n) off = Some (t, fin) ->
    ushp_malloc_chain (ushp_nodes t) UM UM' ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parseline) (ushp_pl_room t + nn) -∗
    (∀ root : Z,
       ushp_otree s0 root t -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int root ⌝ -∗
           UM' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (ushp_pl_room t + nn) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hoffle Hw0 Hscope Href Hchain Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    (* ---- the reference's answer: parsepipe's, and two peeks that miss ---- *)
    rewrite ref_parseline_S in Href.
    destruct (ref_parsepipe len f n off) as [[ t1 s ] | ] eqn:Hpp; [ | discriminate Href ].
    destruct n as [| n ]; [ cbn [ref_parsepipe] in Hpp; discriminate Hpp | ].
    rewrite (ref_backs_scope len f (S n) s t1 Hscope ltac:(lia)) in Href.
    set (s1 := ref_skip len f s) in *.
    rewrite (ref_peek_scope_miss len f s1 [rb_semi] Hscope ref_out_scope_semi) in Href.
    set (s2 := ref_skip len f s1) in *.
    injection Href as Et Efin. subst t1 fin.
    assert (Hs : (s <= len)%nat)
      by exact (proj2 (ref_parsepipe_bounded len f (S n) off t s Hoffle Hpp)).
    assert (Hs1 : (s1 <= len)%nat) by exact (ref_skip_le len f s Hs).
    assert (Hs2 : (s2 <= len)%nat) by exact (ref_skip_le len f s1 Hs1).
    pose proof (ref_peek_scope_miss len f s [rb_amp] Hscope ref_out_scope_amp) as Hpk1.
    pose proof (ref_peek_scope_miss len f s1 [rb_semi] Hscope ref_out_scope_semi) as Hpk2.
    fold s1 in Hpk1. fold s2 in Hpk2.
    (* the budget in the landed spelling *)
    pose proof (ushp_pp_room_ge t) as Hrge.
    set (nn' := (ushp_pp_room t - 46 + nn)%nat) in *.
    assert (Ebud : (ushp_pl_room t + nn)%nat = (6 + (6 + (16 + (24 + nn'))))%nat)
      by (unfold ushp_pl_room, nn'; lia).
    assert (Ebud2 : (6 + (16 + (24 + nn')))%nat = (ushp_pp_room t + nn)%nat)
      by (unfold nn'; lia).
    rewrite Ebud.
    rewrite shpp_parseline.
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x6e2..0x6f0  the prologue ---- *)
    iApply (wp_kshp_frame_pro 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] 0x6e2
              (fun i : nat => match i with
                              | 0%nat => 0x6e4 | 1%nat => 0x6e6
                              | 2%nat => 0x6e8 | 3%nat => 0x6ea
                              | 4%nat => 0x6ec | 5%nat => 0x6ee
                              | _ => 0x6f0 end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (6 + (16 + (24 + nn'))) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_6e2 with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_6e4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6e6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6e8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ea with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ec with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ee with "Hcode") | done ]. }
    { iApply (uis_shp_6f0 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (mA := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (HmA : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    mA !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (HspA : mA !!! Regidx csp_rs1 = spn).
    { rewrite (HmA csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x6f2  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv N h1 mA (mword_of_int 0x6f2) s2_idx a0_idx
              (mword_of_int ps) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6f2 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> mA).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m2 !!! Regidx q = mA !!! Regidx q)
      by (intros q Hq; exact (upd_ne mA (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x6f4  c.mv s3,a1 ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0x6f4) s3_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (HmA a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6f4 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx s3_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x6f6  jal 682 <parsepipe> ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x6f6)
              (mword_of_int 2097036 : mword 21) ra_idx
              (mword_of_int 0x682) (mword_of_int 0x6fa)
              (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6f6 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6fa : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret4 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x6fa).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x6fa : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (HmA a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_4 : m4 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (HmA a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    rewrite <- shpp_parsepipe.
    (* THE COMMAND: the general parsepipe *)
    iEval (rewrite Ebud2) in "Hrun".
    iApply (wp_ref_parsepipe dq dw dv ps s0 len f n h4 m4 off s w0 t UM UM' nn
              Ha0_4 Ha1_4 Hoffle Hw0 Hscope Hpp Hchain Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (p) "Hot Hcur Hstr Hws Hsy".
    iIntros (h5 m5) "%Hcs45 %Ha0_5 HM' Hpay Hrun".
    iEval (rewrite <- Ebud2) in "Hrun".
    rewrite Eret4.
    (* ---- 0x6fa  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h5 m5 (mword_of_int 0x6fa) s1_idx a0_idx
              (mword_of_int p) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_6fa with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x6fc/0x700  the ampersand table ---- *)
    iApply (wp_uk_auipc N h6 m6 (mword_of_int 0x6fc)
              (mword_of_int 1 : mword 20) s4_idx
              (mword_of_int 0x16fc) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6fc with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 0x16fc : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s4_idx) (Regidx q) _ Hq)).
    assert (Hs4_7 : m7 !!! Regidx s4_idx = mword_of_int 0x16fc)
      by exact (upd_eq m6 (Regidx s4_idx)
                  (regval_into_reg (mword_of_int 0x16fc : mword 64))).
    iApply (wp_uk_addi N h7 m7 (mword_of_int 0x700)
              (mword_of_int 3132 : mword 12) s4_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_7; unfold ushp_T_back;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_700 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx s4_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_back : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s4_idx) (Regidx q) _ Hq)).
    assert (Hs4_8 : m8 !!! Regidx s4_idx = mword_of_int ushp_T_back)
      by exact (upd_eq m7 (Regidx s4_idx)
                  (regval_into_reg (mword_of_int ushp_T_back : mword 64))).
    (* the two values the guards read, once *)
    assert (Hs2_8 : m8 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate))
              (Hcs45 s2_idx ltac:(vm_compute; reflexivity))
              (Hm4 s2_idx ltac:(vm_compute; discriminate))
              (Hm3 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s2_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs3_8 : m8 !!! Regidx s3_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hcs45 s3_idx ltac:(vm_compute; reflexivity))
              (Hm4 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s3_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    (* ---- 0x704  c.j 0x71a -- into the backgrounding loop's GUARD ---- *)
    iApply (wp_uk_cj N h8 m8 (mword_of_int 0x704)
              (mword_of_int 11 : mword 11) (mword_of_int 0x71a)
              (6 + (16 + (24 + nn')))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_704 with "Hcode"). }
    iIntros (h9) "Hrun".
    (* ---- 0x71a..0x71e  peek's three arguments ---- *)
    iApply (wp_uk_cmv N h9 m8 (mword_of_int 0x71a) a2_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_8; symmetry;
                    exact (ushp_mv_val ushp_T_back))
              with "[] Hrun").
    { iApply (uis_shp_71a with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_back : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a2_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h10 m9 (mword_of_int 0x71c) a1_idx s3_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm9 s3_idx ltac:(vm_compute; discriminate))
                      Hs3_8; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_71c with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h11 m10 (mword_of_int 0x71e) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      (Hm9 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_8; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_71e with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x720  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h12 m11 (mword_of_int 0x720)
              (mword_of_int 2096424 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x724)
              (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_720 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x724 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x724).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x724 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_12 : m12 !!! Regidx a2_idx = mword_of_int ushp_T_back).
    { rewrite (Hm12 a2_idx ltac:(vm_compute; discriminate))
              (Hm11 a2_idx ltac:(vm_compute; discriminate))
              (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_back : mword 64))). }
    rewrite <- shpp_peek.
    (* THE '&' PEEK: it misses *)
    iApply (wp_ref_peek h13 m12 dq dw true DfracDiscarded ps s0
              ushp_T_back len s 1 f (ushp_lit ushp_T_back)
              (mword_of_int (s0 + Z.of_nat s)) (36 + nn') [rb_amp] false s1
              Ha0_12 Ha1_12 Ha2_12 Hs eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_back; lia)
              ltac:(unfold ushp_T_back, Z64; lia) Hps0 Hps8 Hpssz
              ushp_T_back_tl Hpk1
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_back 1 DfracDiscarded
                ushp_T_back_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h14 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12.
    (* ---- 0x724  c.bnez a0 -- NOT taken: nothing is backgrounded ---- *)
    iApply (wp_uk_cbnez N h14 m13 (mword_of_int 0x724)
              (mword_of_int 241 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x706) (6 + (16 + (24 + nn')))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_724 with "Hcode"). }
    iIntros (h15) "Hrun".
    (* ---- 0x726/0x72a  the semicolon table ---- *)
    iApply (wp_uk_auipc N h15 m13 (mword_of_int 0x726)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x1726) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_726 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m14 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 0x1726 : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_14 : m14 !!! Regidx a2_idx = mword_of_int 0x1726)
      by exact (upd_eq m13 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x1726 : mword 64))).
    iApply (wp_uk_addi N h16 m14 (mword_of_int 0x72a)
              (mword_of_int 3098 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_list) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_14; unfold ushp_T_list;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_72a with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m15 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_list : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x72e/0x730  the other two arguments again ---- *)
    assert (Hs3_15 : m15 !!! Regidx s3_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm15 s3_idx ltac:(vm_compute; discriminate))
              (Hm14 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_8. }
    assert (Hs2_15 : m15 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm15 s2_idx ltac:(vm_compute; discriminate))
              (Hm14 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s2_idx ltac:(vm_compute; reflexivity))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_8. }
    iApply (wp_uk_cmv N h17 m15 (mword_of_int 0x72e) a1_idx
              s3_idx (mword_of_int (s0 + Z.of_nat len))
              (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_15; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_72e with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m16 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h18 m16 (mword_of_int 0x730) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm16 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_15; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_730 with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m17 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m16).
    assert (Hm17 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m17 !!! Regidx q = m16 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m16 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x732  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h19 m17 (mword_of_int 0x732)
              (mword_of_int 2096406 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x736)
              (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_732 with "Hcode"). }
    iIntros (h20) "Hrun".
    set (m18 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x736 : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret18 : ret_pc (m18 !!! Regidx ra_idx) = mword_of_int 0x736).
    { rewrite (upd_eq m17 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x736 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_18 : m18 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm18 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m16 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_18 : m18 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm18 a1_idx ltac:(vm_compute; discriminate))
              (Hm17 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m15 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_18 : m18 !!! Regidx a2_idx = mword_of_int ushp_T_list).
    { rewrite (Hm18 a2_idx ltac:(vm_compute; discriminate))
              (Hm17 a2_idx ltac:(vm_compute; discriminate))
              (Hm16 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m14 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_list : mword 64))). }
    (* THE ';' PEEK: it misses *)
    iApply (wp_ref_peek h20 m18 dq dw true DfracDiscarded ps s0
              ushp_T_list len s1 1 f (ushp_lit ushp_T_list)
              (mword_of_int (s0 + Z.of_nat s1)) (36 + nn') [rb_semi] false s2
              Ha0_18 Ha1_18 Ha2_18 Hs1 eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_list; lia)
              ltac:(unfold ushp_T_list, Z64; lia) Hps0 Hps8 Hpssz
              ushp_T_list_tl Hpk2
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_list 1 DfracDiscarded
                ushp_T_list_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h21 m19) "%Hcs1819 %Ha0_19 Hrun".
    rewrite Eret18.
    (* ---- 0x736  c.bnez a0 -- NOT taken: there is no list ---- *)
    iApply (wp_uk_cbnez N h21 m19 (mword_of_int 0x736)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x74a) (6 + (16 + (24 + nn')))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_19; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_736 with "Hcode"). }
    iIntros (h22) "Hrun".
    (* ---- 0x738  c.mv a0,s1 ---- *)
    assert (Hs1_19 : m19 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcs1819 s1_idx ltac:(vm_compute; reflexivity))
              (Hm18 s1_idx ltac:(vm_compute; discriminate))
              (Hm17 s1_idx ltac:(vm_compute; discriminate))
              (Hm16 s1_idx ltac:(vm_compute; discriminate))
              (Hm15 s1_idx ltac:(vm_compute; discriminate))
              (Hm14 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate))
              (Hm9 s1_idx ltac:(vm_compute; discriminate))
              (Hm8 s1_idx ltac:(vm_compute; discriminate))
              (Hm7 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s1_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iApply (wp_uk_cmv N h22 m19 (mword_of_int 0x738) a0_idx
              s1_idx (mword_of_int p) (6 + (16 + (24 + nn')))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_19; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_738 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m19).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m19 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m19 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3 Hq4.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1819 q Hq)
              (Hm18 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm17 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm16 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q Hq4) (Hm7 q Hq4) (Hm6 q Hq1) (Hcs45 q Hq)
              (Hm4 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm3 q Hq3) (Hm2 q Hq2) (HmA q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1819 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm18 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm17 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm16 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact HspA. }
    (* ---- 0x73a..0x748  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x73a | 1%nat => 0x73c
                              | 2%nat => 0x73e | 3%nat => 0x740
                              | 4%nat => 0x742 | 5%nat => 0x744
                              | _ => 0x746 end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 6)) vals
              (6 + (16 + (24 + nn'))) h23 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_73a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_73c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_73e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_740 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_742 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_744 with "Hcode") | done ]. }
    { iApply (uis_shp_746 with "Hcode"). }
    { iApply (uis_shp_748 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! p with "Hot Hcur Hstr Hws Hsy [] [] HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6) eq_refl)
                 (Hmiss 5%nat s4_idx (mword_of_int 0 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m19 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* (5) nulterminate FROM ITS ENTRY THROUGH THE JUMP TABLE                  *)
  (*                                                                        *)
  (*   0x7ee..0x7f8  c.addi sp,-32; the three spills; s0 := fp; s1 := a0    *)
  (*   0x7fa         c.beqz a0 -- NOT taken: the node is not null           *)
  (*   0x7fc..0x800  the type word, bltu a5,a4 -- NOT taken: in range       *)
  (*   0x804..0x812  the type word again, times four, plus the table's base  *)
  (*   0x814         c.lw a5,0(a5) -- THE TEXT-HALF LOAD of the row          *)
  (*   0x816..0x818  the arm's pc; c.jr a5                                   *)
  (*                                                                        *)
  (* ONE walk at the three type words the catalog carries, the row and the  *)
  (* arm it dispatches to being a function of the word ([ushp_nul_row]).    *)
  (* The continuation is at the arm's first instruction with the frame's    *)
  (* words (for [UkShParseCmd.wp_kshp_nul_fin]) and the register facts the  *)
  (* three arms read.                                                       *)
  (* ===================================================================== *)

  (* the jump table's three walked rows: type word, row address, row value,
     arm pc -- 0x13c0 plus the signed row IS the arm, checked by vm_compute
     where each is used *)
  Definition ushp_nul_row (ty row : Z) (rowv : mword 32) (arm : Z) : Prop :=
    (ty = 1 /\ row = 0x13c4 /\ rowv = mword_of_int 4294964330 /\ arm = 0x81a)
    \/ (ty = 2 /\ row = 0x13c8 /\ rowv = mword_of_int 4294964354 /\ arm = 0x832)
    \/ (ty = 3 /\ row = 0x13cc /\ rowv = mword_of_int 4294964378 /\ arm = 0x84a).

  Lemma ushp_nul_row_exec : ushp_nul_row 1 0x13c4 (mword_of_int 4294964330) 0x81a.
  Proof using . left. auto. Qed.
  Lemma ushp_nul_row_redir : ushp_nul_row 2 0x13c8 (mword_of_int 4294964354) 0x832.
  Proof using . right. left. auto. Qed.
  Lemma ushp_nul_row_pipe : ushp_nul_row 3 0x13cc (mword_of_int 4294964378) 0x84a.
  Proof using . right. right. auto. Qed.

  (* the REDIR row's four bytes, read off the image (from UkShRedirNul) *)
  Lemma ushp_jrow_redir :
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4,
      utext γt (0x13c8 + Z.of_nat j)
        (nth_byte (mword_of_int 4294964338 : mword 32) j).
  Proof using .
    iIntros "#H". rewrite !big_sepL_cons big_sepL_nil.
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 0%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 0%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 1%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 1%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 2%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 2%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 3%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 3%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | done ].
  Qed.

  (* the row of each walked type word, off the image *)
  Lemma ushp_jrow_of (ty row : Z) (rowv : mword 32) (arm : Z) :
    ushp_nul_row ty row rowv arm ->
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4, utext γt (row + Z.of_nat j) (nth_byte rowv j).
  Proof using .
    intros [ (_ & -> & -> & _) | [ (_ & -> & -> & _) | (_ & -> & -> & _) ] ]; iIntros "#Hro".
    - iApply (ushp_jrow_exec with "Hro").
    - iApply (ushp_jrow_redir with "Hro").
    - iApply (ushp_jrow_pipe with "Hro").
  Qed.

  Local Ltac nul_rows Hrow :=
    destruct Hrow as [ (-> & -> & -> & ->) | [ (-> & -> & -> & ->) | (-> & -> & -> & ->) ] ].

  Lemma wp_ref_nul_head (h : CpuId) (m : regfile) (p ty row : Z) (rowv : mword 32)
      (arm : Z) (nn : nat) :
    ushp_nul_row ty row rowv arm ->
    m !!! Regidx a0_idx = mword_of_int p ->
    0 < p -> p mod 8 = 0 -> p + 8 < Z64 ->
    shp_code γt -∗
    ([∗ list] j ∈ seq 0 4, utext γt (row + Z.of_nat j) (nth_byte rowv j)) -∗
    ubytes γd p 4 (nth_byte (mword_of_int ty : mword 32)) -∗
    urun N h m (mword_of_int ShSyms.nulterminate) (4 + nn) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 32 <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ uint (m !!! Regidx csp_rs1) < Z64 ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1
         = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 4)) ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int p ⌝ -∗
       ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
           Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
           Regidx q <> Regidx s1_idx ->
           m' !!! Regidx q = m !!! Regidx q ⌝ -∗
       ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)],
          uword γd (uint (m !!! Regidx csp_rs1) - 8 * (Z.of_nat i + 1))
            (match i with
             | 0%nat => m !!! Regidx ra_idx
             | 1%nat => m !!! Regidx s0_idx
             | _ => m !!! Regidx s1_idx end)) -∗
       ustack γd (mword_of_int (uint (m !!! Regidx csp_rs1) - 24)) 1 -∗
       ubytes γd p 4 (nth_byte (mword_of_int ty : mword 32)) -∗
       urun N h' m' (mword_of_int arm) nn -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hrow Ha0 Hp0 Hp8 Hpsz.
    iIntros "#Hcode #Hjrow Hty4 Hrun Hcont".
    assert (Hty : 1 <= ty <= 3) by (nul_rows Hrow; lia).
    rewrite shpp_nulterminate.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | _ => m !!! Regidx s1_idx end).
    (* ---- 0x7ee  c.addi sp,sp,-32 ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x7ee)
              (mword_of_int 32 : mword 6) 4 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7ee with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 4))).
    assert (Hspu : uint spn = uint sp0 - 32).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 24)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 1 [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    (* ---- 0x7f0..0x7f4  the three spills ---- *)
    iApply (wp_kshp_spill spn nn [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x7f0 | 1%nat => 0x7f2
                              | 2%nat => 0x7f4 | _ => 0x7f6 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| [| i ]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| i ]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_7f0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7f2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7f4 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x7f6  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_kshp_fp h2 m1 0x7f6 (mword_of_int 8 : mword 8) nn
              with "[] Hrun").
    { iApply (uis_shp_7f6 with "Hcode"). }
    iIntros (h3 v) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x7f8  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x7f8) s1_idx a0_idx
              (mword_of_int p) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_7f8 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Hs1_3 : m3 !!! Regidx s1_idx = mword_of_int p)
      by exact (upd_eq m2 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hsp3 : m3 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x7fa  c.beqz a0 -- NOT taken: the node is not null ---- *)
    iApply (wp_uk_cbeqz N h4 m3 (mword_of_int 0x7fa)
              (mword_of_int 34 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x83e) nn
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3;
                    assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ezr;
                    rewrite (moi_eq_vec p 0 ltac:(unfold Z64 in *; lia)
                               ltac:(unfold Z64; lia));
                    assert (Hnz : (p =? 0) = false)
                      by (apply Z.eqb_neq; lia);
                    rewrite Hnz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7fa with "Hcode"). }
    iIntros (h5) "Hrun".
    (* ---- the node's type word, read twice ---- *)
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    (* ---- 0x7fc  c.lw a4,0(a0) ---- *)
    iApply (wp_uk_clw N h5 m3 (mword_of_int 0x7fc)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx p
              (mword_of_int ty : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c4; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_7fc with "Hcode"). }
    iIntros "Hty4" (h6) "Hrun".
    set (m4 := <[Regidx a4_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int ty : mword 32)
                       : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_4 : m4 !!! Regidx a4_idx = (mword_of_int ty : mword 64)).
    { rewrite (upd_eq m3 (Regidx a4_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int ty : mword 32)
                     : mword 64))).
      nul_rows Hrow; apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x7fe  c.li a5,5 ---- *)
    iApply (wp_uk_cli N h6 m4 (mword_of_int 0x7fe)
              (mword_of_int 5 : mword 6) a5_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7fe with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m5 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 5 : mword 6)
                       : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_5 : m5 !!! Regidx a5_idx = (mword_of_int 5 : mword 64)).
    { rewrite (upd_eq m4 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 5 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int ty : mword 64)).
    { rewrite (Hm5 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_4. }
    (* ---- 0x800  bltu a5,a4 -- NOT taken: the type is in range ---- *)
    iApply (wp_uk_btype N h7 m5 (mword_of_int 0x800)
              (mword_of_int 62 : mword 13) a4_idx a5_idx BLTU false
              (mword_of_int 0x83e) nn
              ltac:(cbn [uv_btaken]; rewrite Ha5_5 Ha4_5;
                    rewrite (moi_lt_u 5 ty ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    symmetry; apply Z.ltb_ge; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_800 with "Hcode"). }
    iIntros (h8) "Hrun".
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_3. }
    (* ---- 0x804  lwu a5,0(a0) ---- *)
    iApply (wp_uk_lwu N h8 m5 (mword_of_int 0x804)
              (mword_of_int 0 : mword 12) a0_idx a5_idx p
              (mword_of_int ty : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_5 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_804 with "Hcode"). }
    iIntros "Hty4" (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (zero_extend' 64 (mword_of_int ty : mword 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int ty : mword 64)).
    { rewrite (upd_eq m5 (Regidx a5_idx)
                 (regval_into_reg
                    (zero_extend' 64 (mword_of_int ty : mword 32)
                     : mword 64))).
      nul_rows Hrow; apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x808  c.slli a5,a5,0x2 ---- *)
    iApply (wp_uk_cslli N h9 m6 (mword_of_int 0x808)
              (mword_of_int 2 : mword 6) a5_idx (mword_of_int (ty * 2 ^ 2)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_6 (moi_shl ty 2 ltac:(lia)); reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_808 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (ty * 2 ^ 2) : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_7 : m7 !!! Regidx a5_idx = (mword_of_int (ty * 2 ^ 2) : mword 64))
      by exact (upd_eq m6 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (ty * 2 ^ 2) : mword 64))).
    (* ---- 0x80a/0x80e  the jump table's base ---- *)
    iApply (wp_uk_auipc N h10 m7 (mword_of_int 0x80a)
              (mword_of_int 1 : mword 20) a4_idx
              (mword_of_int 0x180a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_80a with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x180a : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int 0x180a)
      by exact (upd_eq m7 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x180a : mword 64))).
    iApply (wp_uk_addi N h11 m8 (mword_of_int 0x80e)
              (mword_of_int 2998 : mword 12) a4_idx a4_idx
              (mword_of_int 0x13c0) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_8; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_80e with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x13c0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = mword_of_int 0x13c0)
      by exact (upd_eq m8 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x13c0 : mword 64))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = (mword_of_int (ty * 2 ^ 2) : mword 64)).
    { rewrite (Hm9 a5_idx ltac:(vm_compute; discriminate))
              (Hm8 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0x812  c.add a5,a5,a4 -- the row's address ---- *)
    iApply (wp_uk_cadd N h12 m9 (mword_of_int 0x812) a5_idx
              a4_idx (mword_of_int row) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_9 Ha4_9 moi_add; f_equal;
                    nul_rows Hrow; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_812 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int row : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_10 : m10 !!! Regidx a5_idx = mword_of_int row)
      by exact (upd_eq m9 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int row : mword 64))).
    (* ---- 0x814  c.lw a5,0(a5) -- THE TEXT-HALF LOAD ---- *)
    iApply (wp_uk_clw_text N h13 m10 (mword_of_int 0x814)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx row rowv nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_10 (uint_moi row ltac:(nul_rows Hrow; unfold Z64; lia));
                    nul_rows Hrow; vm_compute uoff_c4; lia)
              ltac:(nul_rows Hrow; vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hjrow Hrun").
    { iApply (uis_shp_814 with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg (sign_extend' 64 rowv : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha4_11 : m11 !!! Regidx a4_idx = mword_of_int 0x13c0).
    { rewrite (Hm11 a4_idx ltac:(vm_compute; discriminate))
              (Hm10 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_9. }
    (* ---- 0x816  c.add a5,a5,a4 -- the arm's pc ---- *)
    iApply (wp_uk_cadd N h14 m11 (mword_of_int 0x816) a5_idx
              a4_idx (mword_of_int arm) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_11
                      (upd_eq m10 (Regidx a5_idx)
                         (regval_into_reg (sign_extend' 64 rowv : mword 64)));
                    nul_rows Hrow; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_816 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int arm : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a5_idx) (Regidx q) _ Hq)).
    (* ---- 0x818  c.jr a5 -- the switch ---- *)
    iApply (wp_uk_cjr N h15 m12 (mword_of_int 0x818) a5_idx
              (mword_of_int arm) nn
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m11 (Regidx a5_idx)
                               (regval_into_reg
                                  (mword_of_int arm : mword 64)));
                    nul_rows Hrow; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_818 with "Hcode"). }
    iIntros (h16) "Hrun".
    (* ---- what the arm starts from ---- *)
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate))
              (Hm11 a0_idx ltac:(vm_compute; discriminate))
              (Hm10 a0_idx ltac:(vm_compute; discriminate))
              (Hm9 a0_idx ltac:(vm_compute; discriminate))
              (Hm8 a0_idx ltac:(vm_compute; discriminate))
              (Hm7 a0_idx ltac:(vm_compute; discriminate))
              (Hm6 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_5. }
    assert (Hkeep12 : forall q : mword 5, ucallee_saved_idx q = true ->
              m12 !!! Regidx q = m3 !!! Regidx q).
    { intros q Hq.
      rewrite (Hm12 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm7 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm5 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity))).
      reflexivity. }
    iApply ("Hcont" $! h16 m12 with "[] [] [] [] [] [] [] Hsl Hloc Hty4 Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro. lia.
    - iPureIntro. rewrite (Hkeep12 csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp3.
    - iPureIntro. exact Ha0_12.
    - iPureIntro. rewrite (Hkeep12 s1_idx ltac:(vm_compute; reflexivity)). exact Hs1_3.
    - iPureIntro. intros q Hq Hsp Hq0 Hq1.
      rewrite (Hkeep12 q Hq) (Hm3 q Hq1) (Hm2 q Hq0) (Hm1 q Hsp). reflexivity.
  Qed.


  (* ===================================================================== *)
  (* (5b) nulterminate, THE WHOLE FUNCTION, by induction on the tree         *)
  (*                                                                        *)
  (*   EXEC  0x81a..0x830  argv[0]; the loop (UkShParseCmd.wp_kshp_nul_loop) *)
  (*   REDIR 0x832..0x83a  a0 := rcmd->cmd; jal nulterminate;               *)
  (*                       *rcmd->efile = 0                                  *)
  (*   PIPE  0x84a..0x856  a0 := pcmd->left; jal; a0 := pcmd->right; jal    *)
  (*   ...and 0x83e..0x848, the common tail (UkShParseCmd.wp_kshp_nul_fin). *)
  (*                                                                        *)
  (* The tree comes back UNCHANGED, pointers and all ([ushp_atree]); the    *)
  (* line is cut at [ref_nulcut t].  LIST and BACK have no row in the       *)
  (* catalog: [ushp_walked t].  Room: four words per level of the tree.     *)
  (* ===================================================================== *)

  Lemma wp_ref_nulterminate (s0 : Z) (len : nat) (t : ushp_cmd) :
    forall (h : CpuId) (m : regfile) (p : Z) (a : ushp_ptr) (g : nat -> bv 8) (nn : nat),
    m !!! Regidx a0_idx = mword_of_int p ->
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    ushp_walked t -> ushp_bounded len t ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_atree s0 p t a -∗
    ubytes γd s0 (S len) g -∗
    urun N h m (mword_of_int ShSyms.nulterminate) (4 * ushp_ht t + nn) -∗
    (ushp_atree s0 p t a -∗
     ubytes γd s0 (S len) (ushp_zero_at (ref_nulcut t) g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 * ushp_ht t + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    induction t as [ toks | c IH q e mode fd | l IHl r IHr | l _ r _ | c _ ];
      intros h m p a g nn Ha0 Hs0 Hs64 Hwalk Hbnd;
      iIntros "#Hcode #Hro Hat Hline Hrun Hcont";
      [ | | | destruct Hwalk | destruct Hwalk ].
    - (* ======================= EXEC ======================= *)
      destruct a as [| pc ac | pl pr al ar ]; cbn [ushp_atree];
        [ | iDestruct "Hat" as %[] | iDestruct "Hat" as %[] ].
      iDestruct "Hat" as "(%Hpsz & Hnode)".
      destruct Hbnd as (Htlen & Hbf).
      assert (Hsnd : forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
                (fst tk <= len)%nat /\ (snd tk <= len)%nat)
        by (intros i tk Hi; exact (Forall_lookup_1 _ _ _ _ Hbf Hi)).
      iDestruct "Hnode" as "(%Hnl & %Hnp & %Hna & Hty & Hav & Hev)".
      iDestruct "Hty" as "[Hty4 Hpad]".
      set (sp0 := m !!! Regidx csp_rs1) in *.
      set (vals := fun i : nat =>
                     match i with
                     | 0%nat => m !!! Regidx ra_idx
                     | 1%nat => m !!! Regidx s0_idx
                     | _ => m !!! Regidx s1_idx end).
      set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
      iApply (wp_ref_nul_head h m p 1 0x13c4 (mword_of_int 4294964330) 0x81a nn
                ushp_nul_row_exec Ha0 Hnp Hna ltac:(unfold Z64 in *; lia)
                with "Hcode [] Hty4 Hrun").
      { iApply (ushp_jrow_exec with "Hro"). }
      iIntros (h16 m12) "%Hal8 %Hlo %Hhi %Hsp12 %Ha0_12 %Hs1_12 %Hkeep12 Hsl Hloc Hty4 Hrun".
      assert (Hsplu : uint spl = uint sp0 - 24)
        by (unfold spl; apply uint_moi; unfold sp0, Z64 in *; lia).
      (* ---- 0x81a  c.ld a5,8(a0) -- argv[0] ---- *)
      iDestruct (ushp_slot_read s0 (p + 8) toks fst 0%nat ltac:(lia)
                   with "Hav") as "[Hnx Havc]".
      destruct toks as [| tk rest ].
      + (* ======= NO ARGUMENTS: argv[0] is the cap ======================= *)
        assert (Eslot0 : ushp_slot s0 (p + 8) [] fst 0%nat
                         = uword γd (p + 8 + 8 * Z.of_nat 0)
                             (mword_of_int 0))
          by reflexivity.
        rewrite Eslot0.
        iApply (wp_uk_cld N h16 m12 (mword_of_int 0x81a)
                  (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                  (mword_of_int 7 : mword 3) a0_idx a5_idx
                  (p + 8 + 8 * Z.of_nat 0) (mword_of_int 0) nn
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0_12
                          (uint_moi p ltac:(unfold Z64 in *; lia));
                        vm_compute uoff_c8; lia)
                  ltac:(exact (ushp_slot_al8 p 1 0%nat Hna))
                  ltac:(vm_compute; discriminate)
                  with "[] Hnx Hrun").
        { iApply (uis_shp_81a with "Hcode"). }
        iIntros "Hnx" (h17) "Hrun".
        iDestruct ("Havc" with "Hnx") as "Hav".
        set (m13 := <[Regidx a5_idx
                      := regval_into_reg (mword_of_int 0 : mword 64)]> m12).
        assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                         m13 !!! Regidx q = m12 !!! Regidx q)
          by (intros q Hq; exact (upd_ne m12 (Regidx a5_idx) (Regidx q) _ Hq)).
        assert (Ha5_13 : m13 !!! Regidx a5_idx = (mword_of_int 0 : mword 64))
          by exact (upd_eq m12 (Regidx a5_idx)
                      (regval_into_reg (mword_of_int 0 : mword 64))).
        (* ---- 0x81c  c.beqz a5 -- TAKEN: nothing to nul-terminate ---- *)
        iApply (wp_uk_cbeqz N h17 m13 (mword_of_int 0x81c)
                  (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3)
                  a5_idx true (mword_of_int 0x83e) nn
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha5_13; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shp_81c with "Hcode"). }
        iIntros (h18) "Hrun".
        iApply (wp_kshp_nul_fin sp0 spl vals p nn h18 m13
                  Hal8 Hlo Hhi Hsplu
                  ltac:(rewrite (Hm13 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp12)
                  ltac:(rewrite (Hm13 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_12)
                  with "Hcode Hsl Hloc Hrun").
        iIntros (hf) "Hrun".
        iApply ("Hcont" with "[Hty4 Hpad Hav Hev] [Hline] [] [] Hrun").
        * cbn [ushp_atree]. iSplitR; [ iPureIntro; exact Hpsz | ].
          rewrite /ushp_exec_at /ushp_type_at.
          iSplitR; [ iPureIntro; exact Hnl | ].
          iSplitR; [ iPureIntro; exact Hnp | ].
          iSplitR; [ iPureIntro; exact Hna | ].
          iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                   iExact "Hpad" ] | ].
          iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
        * cbn [ref_nulcut ushp_zero_at fold_left]. iExact "Hline".
        * iPureIntro.
          apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
                 (s0_idx, mword_of_int 2 : mword 6);
                 (s1_idx, mword_of_int 1 : mword 6)] vals m
                   (<[Regidx a0_idx
                      := regval_into_reg (mword_of_int p : mword 64)]> m13)
                   sp0 eq_refl).
          { intros i r0 u Hi.
            destruct i as [| [| [| i ]]];
              cbn in Hi; try discriminate Hi;
              injection Hi as Hr Hu0; subst; reflexivity. }
          intros q Hq Hqsp Hmiss.
          rewrite (upd_ne m13 (Regidx a0_idx) (Regidx q) _
                     (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
                  (Hm13 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity))).
          exact (Hkeep12 q Hq Hqsp
                   (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6) eq_refl)
                   (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6) eq_refl)).
        * iPureIntro.
          rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
          apply ushp_spillback_eq.
          { intros _.
            exact (upd_eq m13 (Regidx a0_idx)
                     (regval_into_reg (mword_of_int p : mword 64))). }
          intros i r0 u Hi He.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
      + (* ======= AT LEAST ONE ARGUMENT: into the loop =================== *)
        assert (Eslot0 : ushp_slot s0 (p + 8) (tk :: rest) fst 0%nat
                         = uword γd (p + 8 + 8 * Z.of_nat 0)
                             (mword_of_int (s0 + Z.of_nat (fst tk))))
          by reflexivity.
        rewrite Eslot0.
        assert (Hfst0 : (fst tk <= len)%nat)
          by exact (proj1 (Hsnd 0%nat tk eq_refl)).
        iApply (wp_uk_cld N h16 m12 (mword_of_int 0x81a)
                  (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                  (mword_of_int 7 : mword 3) a0_idx a5_idx
                  (p + 8 + 8 * Z.of_nat 0)
                  (mword_of_int (s0 + Z.of_nat (fst tk))) nn
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0_12
                          (uint_moi p ltac:(unfold Z64 in *; lia));
                        vm_compute uoff_c8; lia)
                  ltac:(exact (ushp_slot_al8 p 1 0%nat Hna))
                  ltac:(vm_compute; discriminate)
                  with "[] Hnx Hrun").
        { iApply (uis_shp_81a with "Hcode"). }
        iIntros "Hnx" (h17) "Hrun".
        iDestruct ("Havc" with "Hnx") as "Hav".
        set (m13 := <[Regidx a5_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat (fst tk))
                            : mword 64)]> m12).
        assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                         m13 !!! Regidx q = m12 !!! Regidx q)
          by (intros q Hq; exact (upd_ne m12 (Regidx a5_idx) (Regidx q) _ Hq)).
        assert (Ha5_13 : m13 !!! Regidx a5_idx
                         = mword_of_int (s0 + Z.of_nat (fst tk)))
          by exact (upd_eq m12 (Regidx a5_idx)
                      (regval_into_reg
                         (mword_of_int (s0 + Z.of_nat (fst tk)) : mword 64))).
        (* ---- 0x81c  c.beqz a5 -- NOT taken ---- *)
        iApply (wp_uk_cbeqz N h17 m13 (mword_of_int 0x81c)
                  (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3)
                  a5_idx false (mword_of_int 0x83e) nn
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha5_13;
                        assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite Ezr;
                        rewrite (moi_eq_vec (s0 + Z.of_nat (fst tk)) 0
                                   ltac:(unfold Z64 in *; lia)
                                   ltac:(unfold Z64; lia));
                        assert (Hnz : (s0 + Z.of_nat (fst tk) =? 0) = false)
                          by (apply Z.eqb_neq; lia);
                        rewrite Hnz; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_shp_81c with "Hcode"). }
        iIntros (h18) "Hrun".
        (* ---- 0x81e  addi a5,a0,16 ---- *)
        assert (Ha0_13 : m13 !!! Regidx a0_idx = mword_of_int p).
        { rewrite (Hm13 a0_idx ltac:(vm_compute; discriminate)).
          exact Ha0_12. }
        iApply (wp_uk_addi N h18 m13 (mword_of_int 0x81e)
                  (mword_of_int 16 : mword 12) a0_idx a5_idx
                  (mword_of_int (p + 16)) nn
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha0_13;
                        assert (Ei : (sign_extend' 64
                                        (mword_of_int 16 : mword 12)
                                      : mword 64) = mword_of_int 16)
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite Ei; symmetry; apply moi_add)
                  with "[] Hrun").
        { iApply (uis_shp_81e with "Hcode"). }
        iIntros (h19) "Hrun".
        set (m14 := <[Regidx a5_idx
                      := regval_into_reg
                           (mword_of_int (p + 16) : mword 64)]> m13).
        assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                         m14 !!! Regidx q = m13 !!! Regidx q)
          by (intros q Hq; exact (upd_ne m13 (Regidx a5_idx) (Regidx q) _ Hq)).
        iApply (wp_kshp_nul_loop s0 p len nn rest (@nil (nat * nat)) tk
                  (tk :: rest) g h19 m14
                  Hs0 Hs64 Hnp Hna Hpsz eq_refl Htlen Hsnd
                  ltac:(assert (Ep16 : p + 16
                                       + 8 * Z.of_nat
                                               (length (@nil (nat * nat)))
                                       = p + 16)
                          by (cbn [length]; lia);
                        rewrite Ep16;
                        exact (upd_eq m13 (Regidx a5_idx)
                                 (regval_into_reg
                                    (mword_of_int (p + 16) : mword 64))))
                  with "Hcode [Hty4 Hpad Hav Hev] Hline Hrun").
        { rewrite /ushp_exec_at /ushp_type_at.
          iSplitR; [ iPureIntro; exact Hnl | ].
          iSplitR; [ iPureIntro; exact Hnp | ].
          iSplitR; [ iPureIntro; exact Hna | ].
          iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                   iExact "Hpad" ] | ].
          iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
        iIntros "Hnode Hline" (h20 mf) "%Hpresf Hrun".
        iApply (wp_kshp_nul_fin sp0 spl vals p nn h20 mf
                  Hal8 Hlo Hhi Hsplu
                  ltac:(rewrite (Hpresf csp_rs1
                                   ltac:(vm_compute; reflexivity))
                          (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
                          (Hm13 csp_rs1 ltac:(vm_compute; discriminate));
                        exact Hsp12)
                  ltac:(rewrite (Hpresf s1_idx
                                   ltac:(vm_compute; reflexivity))
                          (Hm14 s1_idx ltac:(vm_compute; discriminate))
                          (Hm13 s1_idx ltac:(vm_compute; discriminate));
                        exact Hs1_12)
                  with "Hcode Hsl Hloc Hrun").
        iIntros (hf) "Hrun".
        iApply ("Hcont" with "[Hnode] [Hline] [] [] Hrun").
        * cbn [ushp_atree]. iFrame "Hnode". iPureIntro. exact Hpsz.
        * cbn [ref_nulcut]. rewrite <- ushp_nulfold_zero_at. iExact "Hline".
        * iPureIntro.
          apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
                 (s0_idx, mword_of_int 2 : mword 6);
                 (s1_idx, mword_of_int 1 : mword 6)] vals m
                   (<[Regidx a0_idx
                      := regval_into_reg (mword_of_int p : mword 64)]> mf)
                   sp0 eq_refl).
          { intros i r0 u Hi.
            destruct i as [| [| [| i ]]];
              cbn in Hi; try discriminate Hi;
              injection Hi as Hr Hu0; subst; reflexivity. }
          intros q Hq Hqsp Hmiss.
          rewrite (upd_ne mf (Regidx a0_idx) (Regidx q) _
                     (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
                  (Hpresf q Hq)
                  (Hm14 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hm13 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity))).
          exact (Hkeep12 q Hq Hqsp
                   (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6) eq_refl)
                   (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6) eq_refl)).
        * iPureIntro.
          rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
          apply ushp_spillback_eq.
          { intros _.
            exact (upd_eq mf (Regidx a0_idx)
                     (regval_into_reg (mword_of_int p : mword 64))). }
          intros i r0 u Hi He.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
    - (* ======================= REDIR ======================= *)
      destruct a as [| pc ac | pl pr al ar ]; cbn [ushp_atree];
        [ iDestruct "Hat" as %[] | | iDestruct "Hat" as %[] ].
      iDestruct "Hat" as "[Hn Hsub]".
      cbn [ushp_walked] in Hwalk. destruct Hbnd as (Hbc & He).
      rewrite /ushp_redir_node.
      iDestruct "Hn" as "(%Hnp & %Hna & %Hnz & [Hty4 Hpad] & Hcmd & Hfile
                          & Hefile & Hmode & Hfd)".
      replace (4 * ushp_ht (UshpRedir c q e mode fd) + nn)%nat
        with (4 + (4 * ushp_ht c + nn))%nat by (cbn [ushp_ht]; lia).
      set (sp0 := m !!! Regidx csp_rs1) in *.
      set (vals := fun i : nat =>
                     match i with
                     | 0%nat => m !!! Regidx ra_idx
                     | 1%nat => m !!! Regidx s0_idx
                     | _ => m !!! Regidx s1_idx end).
      set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
      iApply (wp_ref_nul_head h m p 2 0x13c8 (mword_of_int 4294964354) 0x832
                (4 * ushp_ht c + nn) ushp_nul_row_redir Ha0 Hnp Hna ltac:(unfold Z64 in *; lia)
                with "Hcode [] Hty4 Hrun").
      { iApply (ushp_jrow_redir with "Hro"). }
      iIntros (h16 m12) "%Hal8 %Hlo %Hhi %Hsp12 %Ha0_12 %Hs1_12 %Hkeep12 Hsl Hloc Hty4 Hrun".
      assert (Hsplu : uint spl = uint sp0 - 24)
        by (unfold spl; apply uint_moi; unfold sp0, Z64 in *; lia).
      (* ---- 0x832  c.ld a0,8(a0) -- rcmd->cmd ---- *)
      iApply (wp_uk_cld N h16 m12 (mword_of_int 0x832)
                (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 2 : mword 3) a0_idx a0_idx
                (p + 8) (mword_of_int pc) (4 * ushp_ht c + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_12 (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Hna; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hcmd Hrun").
      { iApply (uis_shp_832 with "Hcode"). }
      iIntros "Hcmd" (h17) "Hrun".
      set (n1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int pc : mword 64)]> m12).
      assert (Hn1 : forall r0 : mword 5, Regidx r0 <> Regidx a0_idx ->
                      n1 !!! Regidx r0 = m12 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne m12 (Regidx a0_idx) (Regidx r0) _ Hr)).
      assert (Ha0_n1 : n1 !!! Regidx a0_idx = mword_of_int pc)
        by exact (upd_eq m12 (Regidx a0_idx)
                    (regval_into_reg (mword_of_int pc : mword 64))).
      (* ---- 0x834  jal ra,7ee <nulterminate> -- THE RECURSION ---- *)
      iApply (wp_uk_jal N h17 n1 (mword_of_int 0x834)
                (mword_of_int 2097082 : mword 21) ra_idx
                (mword_of_int 0x7ee) (mword_of_int 0x838) (4 * ushp_ht c + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_834 with "Hcode"). }
      iIntros (h18) "Hrun".
      set (n2 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x838 : mword 64)]> n1).
      assert (Hn2 : forall r0 : mword 5, Regidx r0 <> Regidx ra_idx ->
                      n2 !!! Regidx r0 = n1 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne n1 (Regidx ra_idx) (Regidx r0) _ Hr)).
      assert (Ha0_n2 : n2 !!! Regidx a0_idx = mword_of_int pc)
        by (rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_n1).
      assert (Eret2 : ret_pc (n2 !!! Regidx ra_idx) = mword_of_int 0x838);
        [ rewrite (upd_eq n1 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x838 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      rewrite <- shpp_nulterminate.
      iApply (IH h18 n2 pc ac g nn Ha0_n2 Hs0 Hs64 Hwalk Hbc
                with "Hcode Hro Hsub Hline Hrun").
      iIntros "Hsub Hline" (h19 mr) "%Hcsr %Ha0_r Hrun".
      rewrite Eret2.
      (* ---- 0x838  c.ld a5,24(s1) -- rcmd->efile ---- *)
      assert (Hs1_r : mr !!! Regidx s1_idx = mword_of_int p).
      { rewrite (Hcsr s1_idx ltac:(vm_compute; reflexivity))
                (Hn2 s1_idx ltac:(vm_compute; discriminate))
                (Hn1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_12. }
      iApply (wp_uk_cld N h19 mr (mword_of_int 0x838)
                (mword_of_int 3 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 7 : mword 3) s1_idx a5_idx
                (p + 24) (mword_of_int (s0 + Z.of_nat e)) (4 * ushp_ht c + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Hs1_r (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Hna; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hefile Hrun").
      { iApply (uis_shp_838 with "Hcode"). }
      iIntros "Hefile" (h20) "Hrun".
      set (n3 := <[Regidx a5_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat e) : mword 64)]> mr).
      assert (Hn3 : forall r0 : mword 5, Regidx r0 <> Regidx a5_idx ->
                      n3 !!! Regidx r0 = mr !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne mr (Regidx a5_idx) (Regidx r0) _ Hr)).
      assert (Ha5_n3 : n3 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat e))
        by exact (upd_eq mr (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat e) : mword 64))).
      (* ---- 0x83a  sb zero,0(a5) -- *rcmd->efile = 0 ---- *)
      iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
      iDestruct (ushp_bytes_upd s0 (S len) (ushp_zero_at (ref_nulcut c) g) e ubyte0
                   ltac:(lia) with "Hline") as "[Hb Hbc]".
      iApply (wp_uk_sb N h20 n3 (mword_of_int 0x83a)
                (mword_of_int 0 : mword 12) a5_idx x0_idx
                (s0 + Z.of_nat e) (ushp_zero_at (ref_nulcut c) g e) (4 * ushp_ht c + nn)
                ltac:(rewrite Ha5_n3
                        (uint_moi (s0 + Z.of_nat e)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                with "[] Hb Hrun").
      { iApply (uis_shp_83a with "Hcode"). }
      iIntros "Hb" (h21) "Hrun".
      rewrite Hx0.
      assert (Enb : nth_byte (zero_reg : mword 64) 0%nat = ubyte0)
        by (vm_compute; reflexivity).
      rewrite Enb.
      iDestruct ("Hbc" with "Hb") as "Hline".
      (* ---- 0x83e..0x848  the common tail ---- *)
      iApply (wp_kshp_nul_fin sp0 spl vals p (4 * ushp_ht c + nn) h21 n3
                Hal8 Hlo Hhi Hsplu
                ltac:(rewrite (Hn3 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hcsr csp_rs1 ltac:(vm_compute; reflexivity))
                        (Hn2 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hn1 csp_rs1 ltac:(vm_compute; discriminate));
                      exact Hsp12)
                ltac:(rewrite (Hn3 s1_idx ltac:(vm_compute; discriminate));
                      exact Hs1_r)
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with
               "[Hty4 Hpad Hcmd Hfile Hefile Hmode Hfd Hsub] [Hline] [] [] Hrun").
      + cbn [ushp_atree]. iFrame "Hsub". rewrite /ushp_redir_node.
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitR; [ iPureIntro; exact Hnz | ].
        iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                 iExact "Hpad" ] | ].
        iFrame "Hcmd Hfile Hefile Hmode Hfd".
      + cbn [ref_nulcut]. rewrite ushp_zero_at_snoc. iExact "Hline".
      + iPureIntro.
        apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
                 (s0_idx, mword_of_int 2 : mword 6);
                 (s1_idx, mword_of_int 1 : mword 6)] vals m
                 (<[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> n3)
                 sp0 eq_refl).
        * intros i r0 u Hi.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; reflexivity.
        * intros r0 Hr Hrsp Hmiss.
          rewrite (upd_ne n3 (Regidx a0_idx) (Regidx r0) _
                     (ushp_cs_ne r0 a0_idx Hr ltac:(vm_compute; reflexivity)))
                  (Hn3 r0 (ushp_cs_ne r0 a5_idx Hr
                            ltac:(vm_compute; reflexivity)))
                  (Hcsr r0 Hr)
                  (Hn2 r0 (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                            eq_refl))
                  (Hn1 r0 (ushp_cs_ne r0 a0_idx Hr
                            ltac:(vm_compute; reflexivity))).
          exact (Hkeep12 r0 Hr Hrsp
                   (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6) eq_refl)
                   (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6) eq_refl)).
      + iPureIntro.
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        apply ushp_spillback_eq.
        * intros _.
          exact (upd_eq n3 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))).
        * intros i r0 u Hi Heq.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; vm_compute in Heq; discriminate.
    - (* ======================= PIPE ======================= *)
      destruct a as [| pc ac | pl pr al ar ]; cbn [ushp_atree];
        [ iDestruct "Hat" as %[] | iDestruct "Hat" as %[] | ].
      iDestruct "Hat" as "(Hn & Hsubl & Hsubr)".
      destruct Hwalk as [ Hwl Hwr ]. destruct Hbnd as (Hbl & Hbr).
      rewrite /UkShPipeNode.ushp_pipe_node.
      iDestruct "Hn" as "(%Hnp & %Hna & %Hnz & [Hty4 Hpad] & Hleft & Hright)".
      set (mx := Nat.max (ushp_ht l) (ushp_ht r)).
      replace (4 * ushp_ht (UshpPipe l r) + nn)%nat
        with (4 + (4 * mx + nn))%nat by (unfold mx; cbn [ushp_ht]; lia).
      assert (Ebl : (4 * mx + nn)%nat = (4 * ushp_ht l + (4 * (mx - ushp_ht l) + nn))%nat)
        by (unfold mx; lia).
      assert (Ebr : (4 * mx + nn)%nat = (4 * ushp_ht r + (4 * (mx - ushp_ht r) + nn))%nat)
        by (unfold mx; lia).
      set (sp0 := m !!! Regidx csp_rs1) in *.
      set (vals := fun i : nat =>
                     match i with
                     | 0%nat => m !!! Regidx ra_idx
                     | 1%nat => m !!! Regidx s0_idx
                     | _ => m !!! Regidx s1_idx end).
      set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
      iApply (wp_ref_nul_head h m p 3 0x13cc (mword_of_int 4294964378) 0x84a
                (4 * mx + nn) ushp_nul_row_pipe Ha0 Hnp Hna ltac:(unfold Z64 in *; lia)
                with "Hcode [] Hty4 Hrun").
      { iApply (ushp_jrow_pipe with "Hro"). }
      iIntros (h16 m12) "%Hal8 %Hlo %Hhi %Hsp12 %Ha0_12 %Hs1_12 %Hkeep12 Hsl Hloc Hty4 Hrun".
      assert (Hsplu : uint spl = uint sp0 - 24)
        by (unfold spl; apply uint_moi; unfold sp0, Z64 in *; lia).
      (* ---- 0x84a  c.ld a0,8(a0) -- pcmd->left ---- *)
      iApply (wp_uk_cld N h16 m12 (mword_of_int 0x84a)
                (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 2 : mword 3) a0_idx a0_idx
                (p + 8) (mword_of_int pl) (4 * mx + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_12 (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Hna; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hleft Hrun").
      { iApply (uis_shp_84a with "Hcode"). }
      iIntros "Hleft" (h17) "Hrun".
      set (n1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int pl : mword 64)]> m12).
      assert (Hn1 : forall r0 : mword 5, Regidx r0 <> Regidx a0_idx ->
                      n1 !!! Regidx r0 = m12 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne m12 (Regidx a0_idx) (Regidx r0) _ Hr)).
      assert (Ha0_n1 : n1 !!! Regidx a0_idx = mword_of_int pl)
        by exact (upd_eq m12 (Regidx a0_idx)
                    (regval_into_reg (mword_of_int pl : mword 64))).
      (* ---- 0x84c  jal ra,7ee <nulterminate> -- THE LEFT RECURSION ---- *)
      iApply (wp_uk_jal N h17 n1 (mword_of_int 0x84c)
                (mword_of_int 2097058 : mword 21) ra_idx
                (mword_of_int 0x7ee) (mword_of_int 0x850) (4 * mx + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_84c with "Hcode"). }
      iIntros (h18) "Hrun".
      set (n2 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x850 : mword 64)]> n1).
      assert (Hn2 : forall r0 : mword 5, Regidx r0 <> Regidx ra_idx ->
                      n2 !!! Regidx r0 = n1 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne n1 (Regidx ra_idx) (Regidx r0) _ Hr)).
      assert (Ha0_n2 : n2 !!! Regidx a0_idx = mword_of_int pl)
        by (rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_n1).
      assert (Eret2 : ret_pc (n2 !!! Regidx ra_idx) = mword_of_int 0x850);
        [ rewrite (upd_eq n1 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x850 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      rewrite <- shpp_nulterminate.
      iEval (rewrite Ebl) in "Hrun".
      iApply (IHl h18 n2 pl al g (4 * (mx - ushp_ht l) + nn)%nat Ha0_n2 Hs0 Hs64 Hwl Hbl
                with "Hcode Hro Hsubl Hline Hrun").
      iIntros "Hsubl Hline" (h19 mr) "%Hcsr %Ha0_r Hrun".
      iEval (rewrite <- Ebl) in "Hrun".
      rewrite Eret2.
      (* ---- 0x850  c.ld a0,16(s1) -- pcmd->right ---- *)
      assert (Hs1_r : mr !!! Regidx s1_idx = mword_of_int p).
      { rewrite (Hcsr s1_idx ltac:(vm_compute; reflexivity))
                (Hn2 s1_idx ltac:(vm_compute; discriminate))
                (Hn1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_12. }
      iApply (wp_uk_cld N h19 mr (mword_of_int 0x850)
                (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 2 : mword 3) s1_idx a0_idx
                (p + 16) (mword_of_int pr) (4 * mx + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Hs1_r (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Hna; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hright Hrun").
      { iApply (uis_shp_850 with "Hcode"). }
      iIntros "Hright" (h20) "Hrun".
      set (n3 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int pr : mword 64)]> mr).
      assert (Hn3 : forall r0 : mword 5, Regidx r0 <> Regidx a0_idx ->
                      n3 !!! Regidx r0 = mr !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne mr (Regidx a0_idx) (Regidx r0) _ Hr)).
      assert (Ha0_n3 : n3 !!! Regidx a0_idx = mword_of_int pr)
        by exact (upd_eq mr (Regidx a0_idx)
                    (regval_into_reg (mword_of_int pr : mword 64))).
      (* ---- 0x852  jal ra,7ee <nulterminate> -- THE RIGHT RECURSION ---- *)
      iApply (wp_uk_jal N h20 n3 (mword_of_int 0x852)
                (mword_of_int 2097052 : mword 21) ra_idx
                (mword_of_int 0x7ee) (mword_of_int 0x856) (4 * mx + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_852 with "Hcode"). }
      iIntros (h21) "Hrun".
      set (n4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x856 : mword 64)]> n3).
      assert (Hn4 : forall r0 : mword 5, Regidx r0 <> Regidx ra_idx ->
                      n4 !!! Regidx r0 = n3 !!! Regidx r0)
        by (intros r0 Hr; exact (upd_ne n3 (Regidx ra_idx) (Regidx r0) _ Hr)).
      assert (Ha0_n4 : n4 !!! Regidx a0_idx = mword_of_int pr)
        by (rewrite (Hn4 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_n3).
      assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x856);
        [ rewrite (upd_eq n3 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x856 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      rewrite <- shpp_nulterminate.
      iEval (rewrite Ebr) in "Hrun".
      iApply (IHr h21 n4 pr ar (ushp_zero_at (ref_nulcut l) g) (4 * (mx - ushp_ht r) + nn)%nat
                Ha0_n4 Hs0 Hs64 Hwr Hbr
                with "Hcode Hro Hsubr Hline Hrun").
      iIntros "Hsubr Hline" (h22 mr2) "%Hcsr2 %Ha0_r2 Hrun".
      iEval (rewrite <- Ebr) in "Hrun".
      rewrite Eret4.
      (* ---- 0x856  c.j 83e -- into the common tail ---- *)
      iApply (wp_uk_cj N h22 mr2 (mword_of_int 0x856)
                (mword_of_int 2036 : mword 11) (mword_of_int 0x83e) (4 * mx + nn)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_856 with "Hcode"). }
      iIntros (h23) "Hrun".
      assert (Hs1_r2 : mr2 !!! Regidx s1_idx = mword_of_int p).
      { rewrite (Hcsr2 s1_idx ltac:(vm_compute; reflexivity))
                (Hn4 s1_idx ltac:(vm_compute; discriminate))
                (Hn3 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_r. }
      iApply (wp_kshp_nul_fin sp0 spl vals p (4 * mx + nn) h23 mr2
                Hal8 Hlo Hhi Hsplu
                ltac:(rewrite (Hcsr2 csp_rs1 ltac:(vm_compute; reflexivity))
                        (Hn4 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hn3 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hcsr csp_rs1 ltac:(vm_compute; reflexivity))
                        (Hn2 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hn1 csp_rs1 ltac:(vm_compute; discriminate));
                      exact Hsp12)
                Hs1_r2
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with
               "[Hty4 Hpad Hleft Hright Hsubl Hsubr] [Hline] [] [] Hrun").
      + cbn [ushp_atree]. iFrame "Hsubl Hsubr". rewrite /UkShPipeNode.ushp_pipe_node.
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitR; [ iPureIntro; exact Hnz | ].
        iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                 iExact "Hpad" ] | ].
        iFrame "Hleft Hright".
      + cbn [ref_nulcut]. rewrite ushp_zero_at_app. iExact "Hline".
      + iPureIntro.
        apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
                 (s0_idx, mword_of_int 2 : mword 6);
                 (s1_idx, mword_of_int 1 : mword 6)] vals m
                 (<[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> mr2)
                 sp0 eq_refl).
        * intros i r0 u Hi.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; reflexivity.
        * intros r0 Hr Hrsp Hmiss.
          rewrite (upd_ne mr2 (Regidx a0_idx) (Regidx r0) _
                     (ushp_cs_ne r0 a0_idx Hr ltac:(vm_compute; reflexivity)))
                  (Hcsr2 r0 Hr)
                  (Hn4 r0 (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                            eq_refl))
                  (Hn3 r0 (ushp_cs_ne r0 a0_idx Hr
                            ltac:(vm_compute; reflexivity)))
                  (Hcsr r0 Hr)
                  (Hn2 r0 (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                            eq_refl))
                  (Hn1 r0 (ushp_cs_ne r0 a0_idx Hr
                            ltac:(vm_compute; reflexivity))).
          exact (Hkeep12 r0 Hr Hrsp
                   (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6) eq_refl)
                   (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6) eq_refl)).
      + iPureIntro.
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        apply ushp_spillback_eq.
        * intros _.
          exact (upd_eq mr2 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))).
        * intros i r0 u Hi He.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* (6) parsecmd, THE WHOLE FUNCTION -- THE PARSER THEOREM                 *)
  (*                                                                        *)
  (*   0x86e..0x87a  the prologue (k = 8, three locals; the cursor cell is  *)
  (*                 [sp0 - 56])                                            *)
  (*   0x87c..0x88c  s = a0 into the cell; es := s + strlen(s); &s          *)
  (*   0x890..0x894  parseline(&s, es)                                       *)
  (*   0x898..0x8a6  s3 := the node; peek(&s, es, EMPTY)                     *)
  (*   0x8aa..0x8ae  the cursor read back; bne a2,s1 -- NOT taken: the       *)
  (*                 reference says the line was consumed                   *)
  (*   0x8b2..0x8b4  nulterminate(cmd)                                       *)
  (*   0x8b8..0x8c6  a0 := s3, the epilogue                                  *)
  (*                                                                        *)
  (* Stated at [ref_parsecmd len f = Some t] and [ushp_cat t]: the tree     *)
  (* comes back at [p] as an addressed tree, the line NUL-cut at            *)
  (* [ref_nulcut t], the allocations [ushp_nodes t] deep, room [ushp_room   *)
  (* t].  [wp_ref_parser] below closes the tree to [ushp_tree].              *)
  (* ===================================================================== *)

  Lemma wp_ref_parsecmd {Pex : iProp Σ} (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (t : ushp_cmd) (UM UM' : iProp Σ)
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ref_sym_scope len f ->
    ref_parsecmd len f = Some t ->
    ushp_cat t ->
    ushp_malloc_chain (ushp_nodes t) UM UM' ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd) (ushp_room t + nn) -∗
    (∀ p : Z,
       ushp_otree s0 p t -∗
       ubytes γd s0 (S len) (ushp_zero_at (ref_nulcut t) (ushp_ext len f)) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UM' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (ushp_room t + nn) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Hscope Href Hcat Hchain Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    (* ---- the reference's answer: parseline consumed the line ---- *)
    pose proof (ref_parsecmd_bounded len f t Href) as Hbnd.
    pose proof (ushp_cat_walked t Hcat) as Hwalk.
    unfold ref_parsecmd in Href.
    destruct (ref_parseline len f (ref_fuel len) 0%nat) as [[ t1 s ] | ] eqn:Hpl;
      [ | discriminate Href ].
    rewrite (ref_peek_scope_miss len f s [] Hscope ref_out_scope_nil) in Href.
    destruct (bool_decide (ref_skip len f s = len)) eqn:Es1; [ | discriminate Href ].
    apply bool_decide_eq_true_1 in Es1. injection Href as Et. subst t1.
    pose proof (ref_peek_scope_miss len f s [] Hscope ref_out_scope_nil) as Hpk.
    rewrite Es1 in Hpk.
    rewrite ref_fuel_SS in Hpl. set (n := S (4 * len + 6)%nat) in Hpl.
    assert (Hs : (s <= len)%nat)
      by exact (proj2 (ref_parseline_bounded len f (S n) 0%nat t s ltac:(lia) Hpl)).
    (* ---- the room in the landed spelling, and the two calls' shares ---- *)
    set (B := Nat.max (ushp_pl_room t) (4 * ushp_ht t)) in *.
    pose proof (ushp_pp_room_ge t) as Hrge.
    assert (HB1 : (ushp_pl_room t <= B)%nat) by (unfold B; lia).
    assert (HB2 : (4 * ushp_ht t <= B)%nat) by (unfold B; lia).
    assert (HB52 : (52 <= B)%nat) by (unfold B, ushp_pl_room in *; lia).
    set (nn' := (B - 52 + nn)%nat) in *.
    assert (Ebud : (ushp_room t + nn)%nat = (8 + (52 + nn'))%nat)
      by (unfold ushp_room, nn'; fold B; lia).
    assert (Ebud2 : (52 + nn')%nat = (ushp_pl_room t + (B - ushp_pl_room t + nn))%nat)
      by (unfold nn'; lia).
    assert (Ebud3 : (52 + nn')%nat = (4 * ushp_ht t + (B - 4 * ushp_ht t + nn))%nat)
      by (unfold nn'; lia).
    rewrite Ebud.
    rewrite shpp_parsecmd.
    iDestruct (ustr_len with "Hstr") as %Hlen31.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | _ => m !!! Regidx s3_idx end).
    (* ---- 0x86e  c.addi16sp sp,sp,-64 ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x86e)
              (mword_of_int 60 : mword 6) 8 (52 + nn')
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_86e with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 40) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 40)
      by (unfold spl; apply uint_moi; lia).
    set (sp3 := (mword_of_int (uint sp0 - 64) : mword 64)).
    assert (Hsp3u : uint sp3 = uint sp0 - 64)
      by (unfold sp3; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 3 [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    iDestruct (ushp_frame_split spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hloc") as "[Hlc Hbot]".
    rewrite !big_sepL_cons big_sepL_nil.
    iDestruct "Hlc" as "([%wl0 L0] & [%wcur Lcur] & [%wl2 L2] & _)".
    assert (E0 : uint sp0 - 40 - 8 * (Z.of_nat 0 + 1) = uint sp0 - 48)
      by lia.
    assert (E1 : uint sp0 - 40 - 8 * (Z.of_nat 1 + 1) = uint sp0 - 56)
      by lia.
    assert (E2 : uint sp0 - 40 - 8 * (Z.of_nat 2 + 1) = uint sp0 - 64)
      by lia.
    rewrite Hsplu E0 E1 E2.
    (* ---- 0x870..0x878  the five spills ---- *)
    iApply (wp_kshp_spill spn (52 + nn') [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x870 | 1%nat => 0x872
                              | 2%nat => 0x874 | 3%nat => 0x876
                              | 4%nat => 0x878 | _ => 0x87a end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_870 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_872 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_874 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_876 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_878 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x87a  c.addi4spn s0,sp,64 -- and its VALUE matters here ---- *)
    assert (Hup : add_vec_int spn (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 8) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    assert (Efp : add_vec spn
                    (sign_extend' 64
                       (caddi4spn_imm (mword_of_int 16 : mword 8))) = sp0).
    { assert (Ei : (sign_extend' 64
                      (caddi4spn_imm (mword_of_int 16 : mword 8)) : mword 64)
                   = mword_of_int (8 * Z.of_nat 8))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ei. exact Hup. }
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x87a)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              sp0 (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1; symmetry; exact Efp)
              with "[] Hrun").
    { iApply (uis_shp_87a with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hs0_2 : m2 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
      symmetry. exact (moi_of_uint sp0). }
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int s0).
    { rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x87c  sd a0,-56(s0) -- the cursor cell is initialised ---- *)
    assert (Hcur0 : 0 < uint sp0 - 56) by lia.
    assert (Hcur8 : (uint sp0 - 56) mod 8 = 0).
    { rewrite Zminus_mod Hal8. reflexivity. }
    assert (Hcurz : uint sp0 - 56 + 8 < Z64) by lia.
    iApply (wp_uk_sd N h3 m2 (mword_of_int 0x87c)
              (mword_of_int 4040 : mword 12) s0_idx a0_idx
              (uint sp0 - 56) wcur (52 + nn')
              ltac:(rewrite Hs0_2 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              with "[] Lcur Hrun").
    { iApply (uis_shp_87c with "Hcode"). }
    iIntros "Lcur" (h4) "Hrun".
    rewrite Ha0_2.
    (* ---- 0x880  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h4 m2 (mword_of_int 0x880) s1_idx a0_idx
              (mword_of_int s0) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2; symmetry; exact (ushp_mv_val s0))
              with "[] Hrun").
    { iApply (uis_shp_880 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int s0 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x882  jal a30 <strlen> ---- *)
    iApply (wp_uk_jal N h5 m3 (mword_of_int 0x882)
              (mword_of_int 430 : mword 21) ra_idx
              (mword_of_int 0xa30) (mword_of_int 0x886) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_882 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x886 : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret4 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x886).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x886 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int s0).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_2. }
    rewrite <- shpp_strlen.
    iApply (wp_kshp_strlen h6 m4 (DfracOwn 1) s0 len f (50 + nn')
              Ha0_4 ltac:(lia) ltac:(lia) with "Hcode Hstr Hrun").
    iIntros "Hstr" (h7 m5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    (* ---- 0x886/0x888  the 32-bit zero extension ---- *)
    assert (E32 : (2:Z) ^ 32 = 4294967296) by (vm_compute; reflexivity).
    iApply (wp_uk_cslli N h7 m5 (mword_of_int 0x886)
              (mword_of_int 32 : mword 6) a0_idx
              (mword_of_int (Z.of_nat len * 2 ^ 32)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry;
                    exact (moi_shl (Z.of_nat len) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_886 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m6 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat len * 2 ^ 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat len * 2 ^ 32))
      by exact (upd_eq m5 (Regidx a0_idx)
                  (regval_into_reg
                     (mword_of_int (Z.of_nat len * 2 ^ 32) : mword 64))).
    iApply (wp_uk_csrli N h8 m6 (mword_of_int 0x888)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 3) a0_idx
              (mword_of_int (Z.of_nat len)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6
                      (moi_shr (Z.of_nat len * 2 ^ 32) 32 ltac:(lia)
                         ltac:(rewrite E32; unfold Z64; lia));
                    f_equal; symmetry; apply Z.div_mul; lia)
              with "[] Hrun").
    { iApply (uis_shp_888 with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m7 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat len) : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_7 : m7 !!! Regidx a0_idx = mword_of_int (Z.of_nat len))
      by exact (upd_eq m6 (Regidx a0_idx)
                  (regval_into_reg
                     (mword_of_int (Z.of_nat len) : mword 64))).
    (* ---- 0x88a  c.add s1,s1,a0 -- es = s + len ---- *)
    assert (Hs1_7 : m7 !!! Regidx s1_idx = mword_of_int s0).
    { rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hm6 s1_idx ltac:(vm_compute; discriminate))
              (Hcs45 s1_idx ltac:(vm_compute; reflexivity))
              (Hm4 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s1_idx)
               (regval_into_reg (mword_of_int s0 : mword 64))). }
    iApply (wp_uk_cadd N h9 m7 (mword_of_int 0x88a) s1_idx
              a0_idx (mword_of_int (s0 + Z.of_nat len)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_7 Ha0_7; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_88a with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m8 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_8 : m8 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len))
      by exact (upd_eq m7 (Regidx s1_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat len) : mword 64))).
    (* ---- 0x88c  addi s2,s0,-56 -- &s ---- *)
    assert (Hs0_8 : m8 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm8 s0_idx ltac:(vm_compute; discriminate))
              (Hm7 s0_idx ltac:(vm_compute; discriminate))
              (Hm6 s0_idx ltac:(vm_compute; discriminate))
              (Hcs45 s0_idx ltac:(vm_compute; reflexivity))
              (Hm4 s0_idx ltac:(vm_compute; discriminate))
              (Hm3 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_2. }
    iApply (wp_uk_addi N h10 m8 (mword_of_int 0x88c)
              (mword_of_int 4040 : mword 12) s0_idx s2_idx
              (mword_of_int (uint sp0 - 56)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_8;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 4040 : mword 12)
                                  : mword 64) = mword_of_int (-56))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_88c with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m9 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (uint sp0 - 56) : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s2_idx) (Regidx q) _ Hq)).
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int (uint sp0 - 56))
      by exact (upd_eq m8 (Regidx s2_idx)
                  (regval_into_reg
                     (mword_of_int (uint sp0 - 56) : mword 64))).
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_8. }
    (* ---- 0x890/0x892  parseline(&s, es) ---- *)
    iApply (wp_uk_cmv N h11 m9 (mword_of_int 0x890) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_890 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h12 m10 (mword_of_int 0x892) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_892 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x894  jal 6e2 <parseline> ---- *)
    iApply (wp_uk_jal N h13 m11 (mword_of_int 0x894)
              (mword_of_int 2096718 : mword 21) ra_idx
              (mword_of_int 0x6e2) (mword_of_int 0x898) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_894 with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x898 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x898).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x898 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 56) : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    rewrite <- shpp_parseline.
    (* THE LINE: the general parseline at the reference's answer *)
    iEval (rewrite Ebud2) in "Hrun".
    iApply (wp_ref_parseline h14 m12 (DfracOwn 1) dw dv
              (uint sp0 - 56) s0 len 0%nat n s f (mword_of_int s0) t UM UM'
              (B - ushp_pl_room t + nn)%nat
              Ha0_12 Ha1_12 ltac:(lia)
              ltac:(f_equal; lia)
              Hscope Hpl Hchain ltac:(lia) ltac:(lia)
              Hcur0 Hcur8 Hcurz
              with "Hcode Hro Lcur Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (p) "Hot Lcur Hstr Hws Hsy".
    iIntros (h15 m13) "%Hcs1213 %Ha0_13 HM' Hpay Hrun".
    iEval (rewrite <- Ebud2) in "Hrun".
    rewrite Eret12.
    iDestruct "Hot" as (a) "Hat".
    (* ---- 0x898  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv N h15 m13 (mword_of_int 0x898) s3_idx
              a0_idx (mword_of_int p) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_13; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_898 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m14 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx s3_idx) (Regidx q) _ Hq)).
    assert (Hs3_14 : m14 !!! Regidx s3_idx = mword_of_int p)
      by exact (upd_eq m13 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hs1_14 : m14 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm14 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_9. }
    assert (Hs2_14 : m14 !!! Regidx s2_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm14 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s2_idx ltac:(vm_compute; reflexivity))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_9. }
    assert (Hs0_14 : m14 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm14 s0_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s0_idx ltac:(vm_compute; reflexivity))
              (Hm12 s0_idx ltac:(vm_compute; discriminate))
              (Hm11 s0_idx ltac:(vm_compute; discriminate))
              (Hm10 s0_idx ltac:(vm_compute; discriminate))
              (Hm9 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_8. }
    (* ---- 0x89a/0x89e  the EMPTY token table ---- *)
    iApply (wp_uk_auipc N h16 m14 (mword_of_int 0x89a)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x189a) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_89a with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m15 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 0x189a : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_15 : m15 !!! Regidx a2_idx = mword_of_int 0x189a)
      by exact (upd_eq m14 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x189a : mword 64))).
    iApply (wp_uk_addi N h17 m15 (mword_of_int 0x89e)
              (mword_of_int 2558 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_none) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_15; unfold ushp_T_none;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_89e with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m16 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_none : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x8a2/0x8a4  peek(&s, es, "") ---- *)
    iApply (wp_uk_cmv N h18 m16 (mword_of_int 0x8a2) a1_idx
              s1_idx (mword_of_int (s0 + Z.of_nat len)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm16 s1_idx ltac:(vm_compute; discriminate))
                      (Hm15 s1_idx ltac:(vm_compute; discriminate))
                      Hs1_14; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_8a2 with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m17 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m16).
    assert (Hm17 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m17 !!! Regidx q = m16 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m16 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h19 m17 (mword_of_int 0x8a4) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm17 s2_idx ltac:(vm_compute; discriminate))
                      (Hm16 s2_idx ltac:(vm_compute; discriminate))
                      (Hm15 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_14; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_8a4 with "Hcode"). }
    iIntros (h20) "Hrun".
    set (m18 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x8a6  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h20 m18 (mword_of_int 0x8a6)
              (mword_of_int 2096034 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x8aa) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_8a6 with "Hcode"). }
    iIntros (h21) "Hrun".
    set (m19 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8aa : mword 64)]> m18).
    assert (Hm19 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m19 !!! Regidx q = m18 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m18 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret19 : ret_pc (m19 !!! Regidx ra_idx) = mword_of_int 0x8aa).
    { rewrite (upd_eq m18 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x8aa : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_19 : m19 !!! Regidx a0_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm19 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m17 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 56) : mword 64))). }
    assert (Ha1_19 : m19 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm19 a1_idx ltac:(vm_compute; discriminate))
              (Hm18 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m16 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_19 : m19 !!! Regidx a2_idx = mword_of_int ushp_T_none).
    { rewrite (Hm19 a2_idx ltac:(vm_compute; discriminate))
              (Hm18 a2_idx ltac:(vm_compute; discriminate))
              (Hm17 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m15 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_none : mword 64))). }
    rewrite <- shpp_peek.
    (* THE LEFTOVERS PEEK, at the empty table: the cursor IS at the end *)
    iApply (wp_ref_peek h21 m19 (DfracOwn 1) dw true DfracDiscarded
              (uint sp0 - 56) s0 ushp_T_none len s 0 f
              (ushp_lit ushp_T_none)
              (mword_of_int (s0 + Z.of_nat s)) (42 + nn') [] false len
              Ha0_19 Ha1_19 Ha2_19 Hs eq_refl ltac:(lia) ltac:(lia)
              ltac:(unfold ushp_T_none; lia)
              ltac:(unfold ushp_T_none, Z64; lia) Hcur0 Hcur8 Hcurz
              ushp_T_none_tl Hpk
              with "Hcode Lcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_none 0 DfracDiscarded
                ushp_T_none_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Lcur Hstr Hws _" (h22 m20) "%Hcs1920 %Ha0_20 Hrun".
    rewrite Eret19.
    (* ---- 0x8aa  ld a2,-56(s0) -- the cursor, read back ---- *)
    assert (Hs0_19 : m19 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm19 s0_idx ltac:(vm_compute; discriminate))
              (Hm18 s0_idx ltac:(vm_compute; discriminate))
              (Hm17 s0_idx ltac:(vm_compute; discriminate))
              (Hm16 s0_idx ltac:(vm_compute; discriminate))
              (Hm15 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_14. }
    assert (Hs0_20 : m20 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hcs1920 s0_idx ltac:(vm_compute; reflexivity)).
      exact Hs0_19. }
    iApply (wp_uk_ld N h22 m20 (mword_of_int 0x8aa)
              (mword_of_int 4040 : mword 12) s0_idx a2_idx (DfracOwn 1)
              (uint sp0 - 56) (mword_of_int (s0 + Z.of_nat len)) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_20 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              ltac:(vm_compute; discriminate)
              with "[] Lcur Hrun").
    { iApply (uis_shp_8aa with "Hcode"). }
    iIntros "Lcur" (h23) "Hrun".
    set (m21 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m20).
    assert (Hm21 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m21 !!! Regidx q = m20 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m20 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_21 : m21 !!! Regidx a2_idx
                     = mword_of_int (s0 + Z.of_nat len))
      by exact (upd_eq m20 (Regidx a2_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat len) : mword 64))).
    assert (Hs1_21 : m21 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm21 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1920 s1_idx ltac:(vm_compute; reflexivity))
              (Hm19 s1_idx ltac:(vm_compute; discriminate))
              (Hm18 s1_idx ltac:(vm_compute; discriminate))
              (Hm17 s1_idx ltac:(vm_compute; discriminate))
              (Hm16 s1_idx ltac:(vm_compute; discriminate))
              (Hm15 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_14. }
    (* ---- 0x8ae  bne a2,s1 -- NOT taken: there are no leftovers ---- *)
    iApply (wp_uk_btype N h23 m21 (mword_of_int 0x8ae)
              (mword_of_int 26 : mword 13) s1_idx a2_idx BNE false
              (mword_of_int 0x8c8) (52 + nn')
              ltac:(cbn [uv_btaken]; rewrite Ha2_21 Hs1_21;
                    rewrite (moi_neq_vec (s0 + Z.of_nat len)
                               (s0 + Z.of_nat len)
                               ltac:(unfold Z64 in *; lia)
                               ltac:(unfold Z64 in *; lia));
                    rewrite Z.eqb_refl; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_8ae with "Hcode"). }
    iIntros (h24) "Hrun".
    (* ---- 0x8b2  c.mv a0,s3 ---- *)
    assert (Hs3_21 : m21 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hm21 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1920 s3_idx ltac:(vm_compute; reflexivity))
              (Hm19 s3_idx ltac:(vm_compute; discriminate))
              (Hm18 s3_idx ltac:(vm_compute; discriminate))
              (Hm17 s3_idx ltac:(vm_compute; discriminate))
              (Hm16 s3_idx ltac:(vm_compute; discriminate))
              (Hm15 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_14. }
    iApply (wp_uk_cmv N h24 m21 (mword_of_int 0x8b2) a0_idx
              s3_idx (mword_of_int p) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_21; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_8b2 with "Hcode"). }
    iIntros (h25) "Hrun".
    set (m22 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m21).
    assert (Hm22 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m22 !!! Regidx q = m21 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m21 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x8b4  jal 7ee <nulterminate> ---- *)
    iApply (wp_uk_jal N h25 m22 (mword_of_int 0x8b4)
              (mword_of_int 2096954 : mword 21) ra_idx
              (mword_of_int 0x7ee) (mword_of_int 0x8b8) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_8b4 with "Hcode"). }
    iIntros (h26) "Hrun".
    set (m23 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8b8 : mword 64)]> m22).
    assert (Hm23 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m23 !!! Regidx q = m22 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m22 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret23 : ret_pc (m23 !!! Regidx ra_idx) = mword_of_int 0x8b8).
    { rewrite (upd_eq m22 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x8b8 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_23 : m23 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm23 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m21 (Regidx a0_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iDestruct (ushp_ustr_bytes s0 len f with "Hstr") as "Hline".
    rewrite <- shpp_nulterminate.
    (* THE CUT: the general nulterminate over the addressed tree *)
    iEval (rewrite Ebud3) in "Hrun".
    iApply (wp_ref_nulterminate s0 len t h26 m23 p a (ushp_ext len f)
              (B - 4 * ushp_ht t + nn)%nat
              Ha0_23 ltac:(lia) ltac:(lia) Hwalk Hbnd
              with "Hcode Hro Hat Hline Hrun").
    iIntros "Hat Hline" (h27 m24) "%Hcs2324 %Ha0_24 Hrun".
    iEval (rewrite <- Ebud3) in "Hrun".
    rewrite Eret23.
    (* ---- 0x8b8  c.mv a0,s3 ---- *)
    assert (Hs3_24 : m24 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs2324 s3_idx ltac:(vm_compute; reflexivity))
              (Hm23 s3_idx ltac:(vm_compute; discriminate))
              (Hm22 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_21. }
    iApply (wp_uk_cmv N h27 m24 (mword_of_int 0x8b8) a0_idx
              s3_idx (mword_of_int p) (52 + nn')
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_24; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_8b8 with "Hcode"). }
    iIntros (h28) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m24).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m24 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m24 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* the whole body, as one preservation fact *)
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs2324 q Hq)
              (Hm23 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm22 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm21 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1920 q Hq)
              (Hm19 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm18 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm17 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm16 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q Hq3) (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q Hq2) (Hm8 q Hq1)
              (Hm7 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs45 q Hq)
              (Hm4 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm3 q Hq1) (Hm2 q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs2324 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm23 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm22 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm21 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1920 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm19 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm18 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm17 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm16 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x8ba..0x8c6  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 8 3 [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)] (mword_of_int 7 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x8ba | 1%nat => 0x8bc
                              | 2%nat => 0x8be | 3%nat => 0x8c0
                              | 4%nat => 0x8c2 | _ => 0x8c4 end)
              (mword_of_int 4 : mword 6) sp0 spl vals (52 + nn') h28 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) ltac:(lia)
              ltac:(cbn [length]; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl [L0 Lcur L2 Hbot] Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_8ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8c2 with "Hcode") | done ]. }
    { iApply (uis_shp_8c4 with "Hcode"). }
    { iApply (uis_shp_8c6 with "Hcode"). }
    { iApply (ushp_frame_join spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                (fun i : nat => match i with
                                | 0%nat => wl0
                                | 1%nat => mword_of_int (s0 + Z.of_nat len)
                                | _ => wl2 end)
                ltac:(cbn [length]; lia) with "[L0 Lcur L2] Hbot").
      rewrite !big_sepL_cons big_sepL_nil Hsplu E0 E1 E2.
      iSplitL "L0"; [ iExact "L0" | ].
      iSplitL "Lcur"; [ iExact "Lcur" | ].
      iSplitL "L2"; [ iExact "L2" | done ]. }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! p
              with "[Hat] Hline Hws Hsy [] [] HM' Hpay Hrun").
    { iExists a. iExact "Hat". }
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 6 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 5 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 3 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m24 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  (* ===================================================================== *)
  (* THE PARSER THEOREM.  Given a NUL-terminated command line at [s0] the   *)
  (* reference parses to [t] within the catalog's scope, sh's [parsecmd]     *)
  (* returns a node [p] with [ushp_tree s0 p t], the line NUL-cut at every   *)
  (* index of [ref_nulcut t], the allocator advanced [ushp_nodes t] calls,   *)
  (* the callee-saved file intact, at the return address.                    *)
  (*                                                                        *)
  (* AUDIT.  The allocator chain is a premise, nothing else reaches it: the  *)
  (* symbol table's bytes and the jump table's rows are read off the image.  *)
  (* ===================================================================== *)

  Theorem wp_ref_parser {Pex : iProp Σ} (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (t : ushp_cmd) (UM UM' : iProp Σ)
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ref_sym_scope len f ->
    ref_parsecmd len f = Some t ->
    ushp_cat t ->
    ushp_malloc_chain (ushp_nodes t) UM UM' ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd) (ushp_room t + nn) -∗
    (∀ p : Z,
       ushp_tree s0 p t -∗
       ubytes γd s0 (S len) (ushp_zero_at (ref_nulcut t) (ushp_ext len f)) -∗
       ⌜ forall j : nat, j ∈ ref_nulcut t ->
           ushp_zero_at (ref_nulcut t) (ushp_ext len f) j = ubyte0 ⌝ -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UM' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (ushp_room t + nn) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Hscope Href Hcat Hchain Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iApply (wp_ref_parsecmd h m dw dv s0 len f t UM UM' nn
              Ha0 Hscope Href Hcat Hchain Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (p) "Hot Hline Hws Hsy".
    iApply ("Hcont" $! p with "[Hot] Hline [] Hws Hsy").
    - iApply (ushp_otree_close with "Hot").
    - iPureIntro. intros j Hj. exact (ushp_zero_at_hit _ _ j Hj).
  Qed.


End UkShParser.
