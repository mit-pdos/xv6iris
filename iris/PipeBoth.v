(* ===================================================================== *)
(*  PipeBoth.v -- THE PIPELINE ROUND'S LEND: the block ledger, the       *)
(*  two-cursor credential family, its two byte steps, its entry and its  *)
(*  four exits, and the consumer's chain.                                *)
(*                                                                       *)
(*  Lane PIPE-2W (design app-pipe.md sections 4.3 / 4.3b, AMENDED by the *)
(*  coordinator on 2026-09-19 after SH-PIPE-ROUND-2's landed             *)
(*  [pipe_turn_one_writer]).  The pure half is [PipeBothPure.v].         *)
(*                                                                       *)
(*  WHY THE TWO-CURSOR LEASE IS THE ROUND'S LEND AND NOT THE [PBoth]     *)
(*  ARM'S.  [EchoOut.turn v P] is HALF a [mono_nat] authority, so there  *)
(*  is one console writer at a time; and sh's runcmd child forks TWICE   *)
(*  without knowing which of its children will write the round's block   *)
(*  (the left one at [PExecL], the right one at [PRan] or [PExecR], both *)
(*  at [PBoth]).  So the block credential can never be lent at the forks *)
(*  on any arm -- unless what is lent is a SHARED family with one cursor *)
(*  per child, which is what this file builds.  All four block shapes    *)
(*  come out of it: the LEFT child's console bytes are always a prefix   *)
(*  of [dg_execL], the RIGHT child's a prefix of ONE list [R] fixed at   *)
(*  its own first byte (the LINE at [PRan], [dg_execR] at [PExecR]), and *)
(*  the block written so far is [PipeBothPure.pend2 R sel].              *)
(*                                                                       *)
(*  WHAT TIES THE CLAIM TO THE FAMILY: A LEDGER OF THE BLOCK'S BYTES.    *)
(*  The round's alternative cannot be filed in [cs] at the block's first *)
(*  byte -- two writers decide the interleaving byte by byte and a       *)
(*  [mono_list] entry is immutable -- so while the block is in progress  *)
(*  the choice list is ONE SHORT and the claim reads the block off a     *)
(*  SECOND ledger instead: [blk_auth] / [blk_lb], a [mono_list] of the   *)
(*  bytes written so far.  The SPLIT ([sel], the two cursors) lives in   *)
(*  the family, not in the ledger, and that is not an accident:          *)
(*  [PipeBothPure.pend_both_not_inj] shows the block's BYTES do not      *)
(*  determine the split (the two diagnostics share their first five      *)
(*  bytes, so a six-byte block is the merge of [dg_execL]'s first six    *)
(*  AND of one left byte after [dg_execR]'s first five, and the next     *)
(*  LEFT byte differs), so a claim carrying only the bytes could not     *)
(*  decide which byte a writer at its own cursor may append -- while a   *)
(*  family carrying only the split could not be tied to the claim's own  *)
(*  [o_w].  BOTH are needed, and each covers what the other cannot.      *)
(*                                                                       *)
(*  WHERE THE LEDGER'S NAME LIVES (lanes PIPE-2W-2 / PIPE-2W-3).  The   *)
(*  claim and the two writers must MEAN THE SAME GHOST, so its gname     *)
(*  comes off the FIXED PART: [AppPipe.app_pipe]'s [app_fixed] is        *)
(*  [PipeOut.pipe_gn] -- echo's fixed part PAIRED with a gname of its    *)
(*  own, upstream's FILE application ([FileOut.file_gn]) verbatim -- and  *)
(*  the per-era record [PipeOut.pipe_era] carries the era's block ledger  *)
(*  [pe_blk] and the CURRENT ROUND's exclusive ghost [pe_cur].  A round's *)
(*  own ledger is minted when its block OPENS (a [mono_list] cannot be    *)
(*  reset) and its gname is pinned by [pe_cur] in two halves: the claim's *)
(*  non-taint arm holds one and the round's family the other, so a STALE  *)
(*  family from an earlier round cannot step ([PipeOut.cur_half_agree]),  *)
(*  and between rounds the claim holds the WHOLE ghost, which is what     *)
(*  makes the opening step exclusive ([PipeOut.cur_half_excl]).  So the   *)
(*  three claim-side steps are PROVED here ([pblk2_ecl_holds]), out of    *)
(*  [PipeOut.pecl_blk2_open] (the block's first byte, which mints the     *)
(*  round's ledger and splits the ghost), [_byte] (every further byte,    *)
(*  left or right) and [_file] (the prompt's first byte, which files the  *)
(*  round's code and rejoins the ghost).                                 *)
(*                                                                       *)
(*  THE LEDGER COSTS THE FUNCTOR LIST NOTHING: the bytes ride the era's  *)
(*  own echoed-list camera ([EchoOut.echoOutG]'s [eo_El]), so no class   *)
(*  and no functor row is added when the name arrives.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map
        invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeBothPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import PipeHooks.         (* S0 of [PipeLinksLine], moved *)
Require Import GenLinksLine.
Require Import RiscvPtsto.
Require Import WpUart.
(* as in PipeOut / PipeLinksLine: the Sail imports leave string_scope on
   top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S0  THE PURE BRIDGES                                                  *)
(*                                                                       *)
(*  [PipeBothPure.wr_blk2_p] and [PipeLinksLine.wr_blk_p] are the same    *)
(*  block shape read twice: the round's two writers', and the ordinary    *)
(*  block writer's.  They live in different files, so the bridge is here. *)
(* ===================================================================== *)

Lemma wr_blk2_p_blk (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) :
  wr_blk2_p ps cs I P R sel c1 c2 -> wr_blk_p ps cs I P.
Proof using.
  intros (Hne & Hr & Hq & _ & Hpin & HP & _). rewrite /wr_blk_p.
  pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
  split_and!; [exact Hpin | exact Hr | lia | exact HP].
Qed.

Lemma wr_blk_p_blk2 (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) :
  wr_blk_p ps cs I P -> pboth_line I ->
  wr_blk2_p ps cs I P R [] 0%nat 0%nat.
Proof using.
  intros Hw Hl. pose proof (wr_blk_nonnil_p ps cs I P Hw) as Hne.
  destruct Hw as (Hpin & Hr & Hn & HP). rewrite /wr_blk2_p.
  split_and!; try done; cbn [count_true length]; lia.
Qed.

(* THE ROUND'S CODE, and the block it owes.  [pblk2_code I R sel a] is
   what the FILER proves at the prompt: the round's alternative is [a],
   the line admits it, it does not reopen the prologue, and the block it
   owes is exactly what the two cursors wrote. *)
Definition pblk2_code (I : list (bv 8)) (R : list (bv 8))
    (sel : list bool) (a : nat) : Prop :=
  palt_ok (pline_at I) (palt_of a)
  /\ palt_panic (palt_of a) = false
  /\ palt_isforkS (palt_of a) = false
  /\ pcont (pline_at I) (palt_of a) = pend2 R sel ++ u_prompt.

Lemma pblk2_code_pab (I : list (bv 8)) (R : list (bv 8)) (sel : list bool)
    (a : nat) :
  pblk2_code I R sel a -> pab I a = pend2 R sel ++ u_prompt.
Proof using.
  intros (Hok & _ & Hfk & Hc). by rewrite (pab_is I a (conj Hok Hfk)).
Qed.

Lemma pblk2_code_papr (I : list (bv 8)) (R : list (bv 8)) (sel : list bool)
    (a : nat) :
  pblk2_code I R sel a -> papr I a.
Proof using. intros (Hok & Hpan & Hfk & _). by split_and!. Qed.

Lemma pblk2_code_len (I : list (bv 8)) (R : list (bv 8)) (sel : list bool)
    (a : nat) (c1 c2 : nat) :
  sel_wf2 R sel -> length sel = (c1 + c2)%nat ->
  pblk2_code I R sel a ->
  length (pab I a) = S (S (c1 + c2))%nat.
Proof using.
  intros Hwf Hlen Hc.
  assert (Hup : length u_prompt = 2%nat) by (by vm_compute).
  rewrite (pblk2_code_pab I R sel a Hc) length_app.
  rewrite (pend2_length R sel Hwf) Hlen Hup. lia.
Qed.

(* ---- THE FOUR CODES, each proved from the two cursors alone ---- *)

Lemma pblk2_code_ran (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = 0%nat ->
  length sel = length (wl_line (drop 1 ws)) ->
  pblk2_code I (wl_line (drop 1 ws)) sel (palt_code PRan).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code PRan) Hl.
  split_and!; [by apply palt_ok_LPipe_ran | exact palt_panic_ran
              | reflexivity |].
  rewrite (pcont_ran ws).
  by rewrite (pend2_right_only (wl_line (drop 1 ws)) sel Hc Hlen).
Qed.

Lemma pblk2_code_execL (I : list (bv 8)) (ws : list (list (bv 8)))
    (R : list (bv 8)) (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = length dg_execL -> length sel = length dg_execL ->
  pblk2_code I R sel (palt_code PExecL).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code PExecL) Hl.
  split_and!; [by apply palt_ok_LPipe_execL | exact palt_panic_execL
              | reflexivity |].
  rewrite (pcont_execL ws). by rewrite (pend2_left_only R sel Hc Hlen).
Qed.

Lemma pblk2_code_execR (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = 0%nat -> length sel = length dg_execR ->
  pblk2_code I dg_execR sel (palt_code PExecR).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code PExecR) Hl.
  split_and!; [by apply palt_ok_LPipe_execR | exact palt_panic_execR
              | reflexivity |].
  rewrite (pcont_execR ws).
  by rewrite (pend2_right_only dg_execR sel Hc Hlen).
Qed.

(* ...AND THE ONE PLACE A [PBoth] CODE IS EVER BUILT: out of the
   selector's length and its count of trues, both of which the two
   cursors carry. *)
Lemma pblk2_code_both (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = length dg_execL ->
  length sel = (length dg_execL + length dg_execR)%nat ->
  pblk2_code I dg_execR sel (palt_code (PBoth sel)).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code (PBoth sel)) Hl.
  destruct (pend2_both_full ws sel Hc Hlen) as [Hok Hcont].
  split_and!; [exact Hok | exact (palt_panic_both sel) | reflexivity
              | exact Hcont].
Qed.

(* THE WITNESS A BYTE IS WRITTEN AGAINST.  The claim reads an UNFILED
   block against some admissible alternative of the round's line whose
   continuation the block is a prefix of ([PipeOut.pblk_open]); mid-block
   the round's own code is not decided yet -- that is the whole point of
   the ledger -- so what a byte step spends is this existential.  The
   walk knows the round's FINAL code ([pblk2_code]) and every prefix of
   the block is covered by it, [pblk2_wit_mono]. *)
Definition pblk2_wit (I R : list (bv 8)) (sel : list bool) : Prop :=
  exists a : nat,
    palt_ok (pline_at I) (palt_of a)
    /\ palt_panic (palt_of a) = false
    /\ palt_isforkS (palt_of a) = false
    /\ pend2 R sel `prefix_of` pcont (pline_at I) (palt_of a).

Lemma pblk2_wit_of_code (I R : list (bv 8)) (sel : list bool) (a : nat) :
  pblk2_code I R sel a -> pblk2_wit I R sel.
Proof using.
  intros (Hok & Hpan & Hfk & Hc). exists a.
  split_and!; [exact Hok | exact Hpan | exact Hfk |].
  rewrite Hc. apply prefix_app_r. reflexivity.
Qed.

Lemma count_true_replicate_true (n : nat) :
  count_true (replicate n true) = n.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite replicate_S. cbn [count_true]. by rewrite IH.
Qed.

Lemma count_true_replicate_false (n : nat) :
  count_true (replicate n false) = 0%nat.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite replicate_S. cbn [count_true]. by rewrite IH.
Qed.

(* THE PADDED SELECTOR'S LENGTH, WITH THE TWO BOUNDS ABSTRACT.  [L] and
   [R] must be VARIABLES here: with [length dg_execL] in the goal,
   [rewrite !length_app] walks into [dg_execL = wl_line dg_exec] and
   splits it into the lengths of its words, while the hypotheses keep
   [length dg_execL] whole -- and then [lia] has two different atoms for
   one number and answers "Cannot find witness". *)
Lemma length_pad (sel : list bool) (L R : nat) :
  (count_true sel <= L)%nat -> (length sel - count_true sel <= R)%nat ->
  length (sel ++ replicate (L - count_true sel) true
              ++ replicate (R - (length sel - count_true sel)) false)
  = (L + R)%nat.
Proof using.
  intros H1 H2. pose proof (count_true_le sel) as Hcle.
  rewrite !length_app !length_replicate. lia.
Qed.

Lemma pblk2_wit_mono (I R : list (bv 8)) (sel sel' : list bool) :
  sel `prefix_of` sel' -> sel_wf2 R sel' ->
  pblk2_wit I R sel' -> pblk2_wit I R sel.
Proof using.
  intros Hp Hwf (a & Hok & Hpan & Hfk & Hpref). exists a.
  split_and!; [exact Hok | exact Hpan | exact Hfk |].
  etrans; [exact (pend2_prefix R sel sel' Hp Hwf) | exact Hpref].
Qed.

(* THE [PBoth] ROUND'S WITNESS, AT EVERY WELL-FORMED SELECTOR: pad the
   selector out with the left side's remaining bytes and then the right
   side's, and the round's own [PBoth] code covers what has been written
   so far.  This is what the CONCURRENT steps (S7) spend, where the
   selector lives under the invariant's existential and no single writer
   knows it. *)
Lemma pblk2_wit_both (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws -> sel_wf2 dg_execR sel ->
  pblk2_wit I dg_execR sel.
Proof using.
  intros Hl [H1 H2].
  pose proof (count_true_le sel) as Hcle.
  set (sel' := sel ++ replicate (length dg_execL - count_true sel) true
                   ++ replicate (length dg_execR
                                 - (length sel - count_true sel)) false).
  assert (Hc' : count_true sel' = length dg_execL).
  { rewrite /sel' !count_true_app count_true_replicate_true
      count_true_replicate_false. lia. }
  assert (Hlen' : length sel'
                  = (length dg_execL + length dg_execR)%nat).
  { exact (length_pad sel (length dg_execL) (length dg_execR) H1 H2). }
  apply (pblk2_wit_mono I dg_execR sel sel').
  - rewrite /sel'. by eexists.
  - rewrite /sel_wf2 Hc' Hlen'. lia.
  - exact (pblk2_wit_of_code I dg_execR sel' (palt_code (PBoth sel'))
             (pblk2_code_both I ws sel' Hl Hc' Hlen')).
Qed.

(* ===================================================================== *)
(*  S0b  THE TERMINAL ROUND'S WITNESS (lane PIPE-STAGE-3, design 4.3h)    *)
(*                                                                       *)
(*  [pblk2_wit]'s twin at a [PForkS] alternative.  The two are DISJOINT   *)
(*  by [palt_isforkS], which is what keeps the claim's [cs_nofork] and    *)
(*  [pab]'s guard out of the terminal round's way: a block written        *)
(*  against a [PForkS] witness is never filed and never reaches           *)
(*  [pblk_step].                                                          *)
(* ===================================================================== *)
Definition pblk2_wit_t (I R : list (bv 8)) (sel : list bool) : Prop :=
  exists a : nat,
    palt_ok (pline_at I) (palt_of a)
    /\ palt_panic (palt_of a) = false
    /\ palt_isforkS (palt_of a) = true
    /\ pend2 R sel `prefix_of` pcont (pline_at I) (palt_of a).

(* AT THE RIGHT SOURCE [alt_forkc] IT IS FREE, at EVERY well-formed
   selector: the round's own [PForkS sel] has that very merge as its
   continuation ([PipeDisc.pcont]'s [PForkS] arm, in the stage's
   convention), and the empty selector falls to the old constant
   ([sel_forkc], which [palt_ok] does admit where [] does not). *)
Lemma pblk2_wit_t_forkc (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws -> sel_wf2 alt_forkc sel ->
  pblk2_wit_t I alt_forkc sel.
Proof using.
  intros Hl [H1 H2]. rewrite /pblk2_wit_t Hl.
  destruct (decide (sel = [])) as [Hnil | Hne].
  - exists (palt_code (PForkS sel_forkc)).
    rewrite (palt_of_code (PForkS sel_forkc)).
    split_and!; [exact (palt_ok_forkS_old ws)
                | exact (palt_panic_forkS sel_forkc) | reflexivity |].
    rewrite Hnil (pend2_nil alt_forkc). apply prefix_nil.
  - exists (palt_code (PForkS sel)).
    rewrite (palt_of_code (PForkS sel)).
    split_and!; [rewrite /palt_ok; split_and!; assumption
                | exact (palt_panic_forkS sel) | reflexivity |].
    rewrite /pend2 /pcont. reflexivity.
Qed.

(* ---- THE PROMPT SITS INSIDE [alt_forkc] (design 4.3h): `fork\n' is the
       runcmd child's panic, `$ ' is sh's MAIN LOOP's prompt, written one
       process later at the SAME cursor. ---- *)
Lemma alt_forkc_dollar : alt_forkc !! 5%nat = Some (u_prompt !!! 0%nat).
Proof using. by vm_compute. Qed.

Lemma alt_forkc_cons : exists (b : bv 8) (bs : list (bv 8)),
  alt_forkc = b :: bs.
Proof using.
  destruct alt_forkc as [| b bs] eqn:Hac; [| by exists b, bs].
  exfalso. pose proof alt_forkc_dollar as Hd.
  rewrite Hac in Hd. cbn in Hd. discriminate Hd.
Qed.

Lemma alt_forkc_space : alt_forkc !! 6%nat = Some (u_prompt !!! 1%nat).
Proof using. by vm_compute. Qed.

(* ---- THE TEST'S SELECTOR: the whole of [alt_forkc] (the child's panic
       and the loop's prompt) and then the whole of the stray's
       diagnostic.  [true] is the STRAY (the landed convention). ---- *)
Definition sel_term : list bool :=
  replicate (length alt_forkc) false ++ replicate (length dg_execL) true.

Lemma palt_ok_sel_term (ws : list (list (bv 8))) :
  palt_ok (LPipe ws) (PForkS sel_term).
Proof using.
  rewrite /palt_ok /sel_term. split_and!.
  - intro Hq. apply (f_equal length) in Hq.
    rewrite length_app !length_replicate alt_forkc_len in Hq.
    cbn [length] in Hq. rewrite dg_execL_len in Hq. lia.
  - rewrite count_true_app count_true_replicate_false
            count_true_replicate_true. lia.
  - rewrite length_app !length_replicate count_true_app
            count_true_replicate_false count_true_replicate_true. lia.
Qed.

Lemma pcont_sel_term (ws : list (list (bv 8))) :
  pcont (LPipe ws) (PForkS sel_term) = alt_forkc ++ dg_execL.
Proof using. by vm_compute. Qed.

Section pipe_both.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation PT := (echo_taint γ).

  (* the record equation, as in [PipeLinks]: the port's claim IS the
     pipeline application's *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).

  Lemma pbchist_at0 (kk : nat) (hh : list mobs)
      (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = pecl g kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ================================================================= *)
  (*  S1  THE ROUND'S LEDGER lives at the CLAIM                         *)
  (*                                                                   *)
  (*  [PipeOut.rblk_auth] / [rblk_lb] at the gname minted when the      *)
  (*  block opens, and [PipeOut.cur_half] for the round it belongs to.  *)
  (*  Nothing is a parameter here any more: see the header.             *)
  (* ================================================================= *)

  (* ================================================================= *)
  (*  S2  THE TWO CURSORS                                               *)
  (*                                                                   *)
  (*  One per child, EXCLUSIVE, in halves: ONE IS LENT TO EACH CHILD AT *)
  (*  THE FORKS, which is what the round can do without knowing which   *)
  (*  child will write.                                                 *)
  (* ================================================================= *)

  Definition wcur (gc : gname) (q : Qp) (c : nat) : iProp Σ :=
    ghost_var gc q c.

  Global Instance wcur_timeless gc q c : Timeless (wcur gc q c).
  Proof using . rewrite /wcur. apply _. Qed.

  Lemma wcur_agree gc q1 q2 c1 c2 :
    wcur gc q1 c1 -∗ wcur gc q2 c2 -∗ ⌜c1 = c2⌝.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.

  Lemma wcur_update gc c1 c2 m :
    wcur gc (1/2) c1 -∗ wcur gc (1/2) c2 ==∗ wcur gc (1/2) m ∗ wcur gc (1/2) m.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iMod (ghost_var_update_halves m with "H1 H2") as "[$ $]".
  Qed.

  Lemma wcur_excl gc c1 c2 : wcur gc 1 c1 -∗ wcur gc 1 c2 -∗ False.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
  Qed.

  (* ================================================================= *)
  (*  S3  THE FAMILY                                                    *)
  (* ================================================================= *)

  (* WHAT TIES THE FAMILY TO THE CLAIM.  Before the block's first byte
     there is no round ledger yet and the claim owns the WHOLE
     current-round ghost; [sel = []] is exactly that state, and the first
     byte's step is what mints the ledger and splits the ghost.  After
     it, the family holds the writer's half AND the ledger's lower bound
     on the bytes written so far -- the half is what makes it the CURRENT
     round's family and not a stale one. *)
  (* ...AND THE TERMINAL FLAG (lane PIPE-STAGE-4, design SS4.3m).  The
     writer's half of the current-round ghost PINS it, so the claim and
     every party writing the round agree on whether it is a fork-failure
     round.  That is the discriminator [pecl_blk2_file] was missing: the
     filing step takes the half at [tm = false], which the claim's own
     half refutes at a terminal round -- and that is what makes the
     resolution FREEZABLE there. *)
  Definition pblk_led (k : nat) (I R : list (bv 8)) (sel : list bool)
      (tm : bool) : iProp Σ :=
    (⌜sel = []⌝ ∨ ∃ (w : pipe_era) (gb : gname),
        pera_pin g k w ∗ cur_half w (1/2) (nlines I - 1)%nat gb tm
        ∗ rblk_lb gb (pend2 R sel))%I.

  Global Instance pblk_led_timeless k I R sel tm :
    Timeless (pblk_led k I R sel tm).
  Proof using .
    rewrite /pblk_led.
    apply bi.or_timeless; [apply bi.pure_timeless |].
    apply bi.exist_timeless; intro w.
    apply bi.exist_timeless; intro gb.
    apply bi.sep_timeless; [apply pera_pin_timeless |].
    apply bi.sep_timeless;
      [apply cur_half_timeless | apply rblk_lb_timeless].
  Qed.

  Definition pwc_blk2 (k : nat) (v : era_pins) (I : list (bv 8))
      (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) (tm : bool)
    : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ ∗ ⌜wr_tail_p ps cs⌝
        ∗ turn v (P + c1 + c2)%nat ∗ ps_lb v ps ∗ cs_lb v cs
        ∗ pblk_led k I R sel tm ∗ inp_lb v I) ∨ PT)%I.

  (* NAME THE LEAVES, do not search: the tree carries 455 [Timeless]
     instances under transparent definitions and one [apply _] at this
     altitude tries nearly all of them ([PipeLinksLine]'s [tl_leaf]). *)
  Global Instance pwc_blk2_timeless k v I R sel c1 c2 tm :
    Timeless (pwc_blk2 k v I R sel c1 c2 tm).
  Proof using .
    rewrite /pwc_blk2.
    apply bi.or_timeless; [| apply echo_taint_timeless].
    apply bi.exist_timeless; intro ps.
    apply bi.exist_timeless; intro cs.
    apply bi.exist_timeless; intro P.
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply turn_timeless |].
    apply bi.sep_timeless; [apply ps_lb_timeless |].
    apply bi.sep_timeless; [apply cs_lb_timeless |].
    apply bi.sep_timeless; [apply pblk_led_timeless | apply inp_lb_timeless].
  Qed.

  Lemma pwc_blk2_taint k v I R sel c1 c2 tm :
    PT -∗ pwc_blk2 k v I R sel c1 c2 tm.
  Proof using . iIntros "HT". rewrite /pwc_blk2. by iRight. Qed.

  (* THE ENTRY: what sh's runcmd child holds for the round is the block
     credential at its first byte ([PipeLinksLine.pwc_lend], i.e.
     [lk_lcred]'s owed arm at an [LPipe] line); it IS the family at the
     empty selector, at ANY right-hand source. *)
  Lemma pwc_blk2_of_lend (k : nat) (v : era_pins) (I : list (bv 8))
      (R : list (bv 8)) (tm : bool) :
    pboth_line I ->
    pwc_lend g k v I -∗ pwc_blk2 k v I R [] 0%nat 0%nat tm.
  Proof using .
    intros Hl. iIntros "Hc". rewrite pwc_lend_view /pwc_blk2.
    iDestruct "Hc" as "[Hx | #HT]"; last by iRight.
    iDestruct "Hx" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P.
    rewrite !Nat.add_0_r. iFrame "Htn Hps Hcs HE".
    iSplitR;
      [iPureIntro; exact (wr_blk_p_blk2 ps cs I P R (proj1 Hw) Hl) |].
    iSplitR; [iPureIntro; exact (proj2 Hw) |].
    rewrite /pblk_led. by iLeft.
  Qed.

  (* ================================================================= *)
  (*  S4  WHAT THE CLAIM OWES: the three steps of the unfiled block      *)
  (*                                                                   *)
  (*  [PipeOut.pecl_step_write]'s twins at the claim's SECOND arm, in    *)
  (*  the same shape ([==∗] over [pecl], so they compose at any mask,    *)
  (*  which is what lets S7's concurrent step open an invariant around   *)
  (*  them).  These are what this lane leaves owed.                      *)
  (* ================================================================= *)

  Definition pblk2_ecl_L : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜dg_execL !! c1 = Some b⌝ -∗ ⌜Forall nodollar (pend2 R sel)⌝ -∗
        ⌜pblk2_wit I R (sel ++ [true])⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel false -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ pblk_led k I R (sel ++ [true]) false) ∨ PT))%I.

  Definition pblk2_ecl_R : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜R !! c2 = Some b⌝ -∗ ⌜Forall nodollar R⌝ -∗
        ⌜pblk2_wit I R (sel ++ [false])⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel false -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ pblk_led k I R (sel ++ [false]) false) ∨ PT))%I.

  (* ...AND THE FILING, at the prompt's own first byte: the only step
     that moves [cs], and the only place a round's code is built. *)
  Definition pblk2_ecl_file : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (a : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜pblk2_code I R sel a⌝ -∗ ⌜sel <> []⌝ -∗
        ⌜b = u_prompt !!! 0%nat⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel false -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat ∗ cs_lb v (cs ++ [a])) ∨ PT))%I.

  Definition pblk2_ecl : iProp Σ :=
    (pblk2_ecl_L ∗ pblk2_ecl_R ∗ pblk2_ecl_file)%I.

  Global Instance pblk2_ecl_L_persistent : Persistent pblk2_ecl_L.
  Proof using . rewrite /pblk2_ecl_L. apply _. Qed.
  (* The [R] halves name the [□] instance: under [apply _] the typeclass
     unifier takes 15 s (28 s for [pblk2_ecl_R_t]) to match it against the
     body, where a direct [apply] is instant. *)
  Global Instance pblk2_ecl_R_persistent : Persistent pblk2_ecl_R.
  Proof using . rewrite /pblk2_ecl_R. apply bi.intuitionistically_persistent. Qed.
  Global Instance pblk2_ecl_file_persistent : Persistent pblk2_ecl_file.
  Proof using . rewrite /pblk2_ecl_file. apply _. Qed.
  Global Instance pblk2_ecl_persistent : Persistent pblk2_ecl.
  Proof using .
    rewrite /pblk2_ecl.
    apply bi.sep_persistent; [apply pblk2_ecl_L_persistent |].
    apply bi.sep_persistent;
      [apply pblk2_ecl_R_persistent | apply pblk2_ecl_file_persistent].
  Qed.

  Lemma pblk2_ecl_l : pblk2_ecl -∗ pblk2_ecl_L.
  Proof using . by iIntros "($ & _ & _)". Qed.
  Lemma pblk2_ecl_r : pblk2_ecl -∗ pblk2_ecl_R.
  Proof using . by iIntros "(_ & $ & _)". Qed.
  Lemma pblk2_ecl_f : pblk2_ecl -∗ pblk2_ecl_file.
  Proof using . by iIntros "(_ & _ & $)". Qed.

  (* ----------------------------------------------------------------- *)
  (*  ...AND WHAT THE CLAIM PAYS: the three steps, at [PipeOut]'s own    *)
  (*  four.  The first byte of the block OPENS the round (mints its      *)
  (*  ledger, splits [pe_cur]); every further byte appends to that       *)
  (*  ledger under the writer's half; the prompt's first byte files the  *)
  (*  round's code and rejoins the ghost.                                *)
  (* ----------------------------------------------------------------- *)

  Lemma pblk2_ecl_L_holds : ⊢ pblk2_ecl_L.
  Proof using .
    rewrite /pblk2_ecl_L. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 b).
    iIntros "%Hw %Htl %Hb %HndR %Hwit #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (_ & Hstep).
    assert (Hnd : nodollar b)
      by exact (Forall_lookup_1 _ _ _ _ dg_execL_nodollar Hb).
    destruct Hwit as (a & Hok & Hpan & Hfk & Hpref).
    rewrite /pline_at in Hok, Hpan, Hpref. rewrite Hstep in Hpref.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - (* THE BLOCK'S FIRST BYTE: the round's ledger is minted here *)
      subst sel.
      assert (Hc10 : c1 = 0%nat) by (cbn [count_true] in Hcnt; lia).
      assert (Hc20 : c2 = 0%nat) by (cbn [length] in Hlen; lia).
      subst c1 c2.
      rewrite (pend2_nil R) in Hpref. cbn [app] in Hpref.
      assert (Hb0 : pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat))
                      (palt_of a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hle : (nlines I <= S (length cs))%nat) by lia.
      iMod (pecl_blk2_open g k v P a b ps cs I ho H Hne Hr Hle Hpp HP
              Hok Hpan Hfk Hb0 Hnd with "Hpin [Htn] Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      (* [replace P with ...] would rewrite P inside [Htn] too -- the
         Iris context is part of the Coq goal.  Convert the INDEX. *)
      { cbn [count_true]. rewrite ?Nat.add_0_r. iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
      iDestruct "Hx" as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & _ & _ & _)".
      iLeft. cbn [count_true]. rewrite ?Nat.add_0_r. iFrame "Htn".
      rewrite /pblk_led. iRight. iExists w, gb. iFrame "Hpera Hcur".
      rewrite Hstep (pend2_nil R). cbn [app]. iFrame "Hrlb".
    - (* A FURTHER BYTE: the round's own ledger, under the writer's half *)
      iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      iMod (pecl_blk2_byte g k v w gb P (nlines I - 1)%nat a b
              (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
              Hok Hpan Hfk Hpref HndR Hnd
              with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
          by (rewrite Hlb; lia). iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb') | #HT]"; [| by iRight].
      iLeft.
      replace (S (P + c1 + c2))%nat
        with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
      iFrame "Htn". rewrite /pblk_led. iRight. iExists w, gb.
      iFrame "Hpera Hcur". rewrite Hstep. iFrame "Hrlb'".
  Qed.

  Lemma pblk2_ecl_R_holds : ⊢ pblk2_ecl_R.
  Proof using .
    rewrite /pblk2_ecl_R. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 b).
    iIntros "%Hw %Htl %Hb %HndR %Hwit #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (_ & Hstep).
    assert (Hnd : nodollar b)
      by exact (Forall_lookup_1 _ _ _ _ HndR Hb).
    destruct Hwit as (a & Hok & Hpan & Hfk & Hpref).
    rewrite /pline_at in Hok, Hpan, Hpref. rewrite Hstep in Hpref.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - subst sel.
      assert (Hc10 : c1 = 0%nat) by (cbn [count_true] in Hcnt; lia).
      assert (Hc20 : c2 = 0%nat) by (cbn [length] in Hlen; lia).
      subst c1 c2.
      rewrite (pend2_nil R) in Hpref. cbn [app] in Hpref.
      assert (Hb0 : pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat))
                      (palt_of a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hle : (nlines I <= S (length cs))%nat) by lia.
      iMod (pecl_blk2_open g k v P a b ps cs I ho H Hne Hr Hle Hpp HP
              Hok Hpan Hfk Hb0 Hnd with "Hpin [Htn] Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { cbn [count_true]. rewrite ?Nat.add_0_r. iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
      iDestruct "Hx" as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & _ & _ & _)".
      iLeft. cbn [count_true]. rewrite ?Nat.add_0_r. iFrame "Htn".
      rewrite /pblk_led. iRight. iExists w, gb. iFrame "Hpera Hcur".
      rewrite Hstep (pend2_nil R). cbn [app]. iFrame "Hrlb".
    - iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      iMod (pecl_blk2_byte g k v w gb P (nlines I - 1)%nat a b
              (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
              Hok Hpan Hfk Hpref
              (pmerge_nodollar sel dg_execL R dg_execL_nodollar HndR) Hnd
              with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
          by (rewrite Hlb; lia). iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb') | #HT]"; [| by iRight].
      iLeft.
      replace (S (P + c1 + c2))%nat
        with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
      iFrame "Htn". rewrite /pblk_led. iRight. iExists w, gb.
      iFrame "Hpera Hcur". rewrite Hstep. iFrame "Hrlb'".
  Qed.

  Lemma pblk2_ecl_file_holds : ⊢ pblk2_ecl_file.
  Proof using .
    rewrite /pblk2_ecl_file. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 a b).
    iIntros "%Hw %Htl %Hcode %Hnn %Hbv #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    pose proof Hcode as (Hok & Hpan & Hfk & Hcont).
    rewrite /pline_at in Hok, Hpan, Hcont.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]"; [by destruct (Hnn Hnil) |].
    iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
    iMod (pecl_blk2_file g k v w gb P (nlines I - 1)%nat a b
            (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
            Hok Hpan Hfk Hcont Hbv
            with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
      as "(Hcl & Hret)".
    { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
        by (rewrite Hlb; lia). iExact "Htn". }
    iModIntro. iFrame "Hcl".
    iDestruct "Hret" as "[(Htn & _ & #Hcs' & _) | #HT]"; [| by iRight].
    iLeft.
    replace (S (P + c1 + c2))%nat
      with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
    iFrame "Htn Hcs'".
  Qed.

  (* ================================================================= *)
  (*  S4b  THE TERMINAL ROUND'S TWO BYTE OBLIGATIONS (PIPE-STAGE-3)     *)
  (*                                                                   *)
  (*  The twins of [pblk2_ecl_L] / [pblk2_ecl_R] at a [PForkS] witness. *)
  (*  TWO PREMISES COME OFF and NOTHING GOES ON: the `$'-freeness of the *)
  (*  block ([Forall nodollar]) and of the byte are exactly what the     *)
  (*  terminal arm of [PipeOut.pblk_open] does not ask for -- the prompt *)
  (*  sits INSIDE [alt_forkc], so the block carries a `$' by            *)
  (*  construction and D4, not `$'-freeness, is what refutes the next    *)
  (*  input ([PipeOut.pecl_step_echo]'s terminal case).  THERE IS NO     *)
  (*  TERMINAL FILING OBLIGATION: the round stays open for ever.        *)
  (* ================================================================= *)

  Definition pblk2_ecl_L_t : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (b : bv 8) (tmi : bool),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜dg_execL !! c1 = Some b⌝ -∗
        ⌜pblk2_wit_t I R (sel ++ [true])⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel tmi -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ pblk_led k I R (sel ++ [true]) true
              ∗ cs_frozen_at v (nlines I - 1)%nat) ∨ PT))%I.

  Definition pblk2_ecl_R_t : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (b : bv 8) (tmi : bool),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜R !! c2 = Some b⌝ -∗
        ⌜pblk2_wit_t I R (sel ++ [false])⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel tmi -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ pblk_led k I R (sel ++ [false]) true
              ∗ cs_frozen_at v (nlines I - 1)%nat) ∨ PT))%I.

  Definition pblk2_ecl_t : iProp Σ :=
    (pblk2_ecl_L_t ∗ pblk2_ecl_R_t)%I.

  Global Instance pblk2_ecl_L_t_persistent : Persistent pblk2_ecl_L_t.
  Proof using . rewrite /pblk2_ecl_L_t. apply _. Qed.
  Global Instance pblk2_ecl_R_t_persistent : Persistent pblk2_ecl_R_t.
  Proof using . rewrite /pblk2_ecl_R_t. apply bi.intuitionistically_persistent. Qed.
  Global Instance pblk2_ecl_t_persistent : Persistent pblk2_ecl_t.
  Proof using .
    rewrite /pblk2_ecl_t. apply bi.sep_persistent;
      [apply pblk2_ecl_L_t_persistent | apply pblk2_ecl_R_t_persistent].
  Qed.

  Lemma pblk2_ecl_t_l : pblk2_ecl_t -∗ pblk2_ecl_L_t.
  Proof using . by iIntros "($ & _)". Qed.
  Lemma pblk2_ecl_t_r : pblk2_ecl_t -∗ pblk2_ecl_R_t.
  Proof using . by iIntros "(_ & $)". Qed.

  Lemma pblk2_ecl_L_t_holds : ⊢ pblk2_ecl_L_t.
  Proof using .
    rewrite /pblk2_ecl_L_t. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 b tmi).
    iIntros "%Hw %Htl %Hb %Hwit #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (_ & Hstep).
    destruct Hwit as (a & Hok & Hpan & Hfk & Hpref).
    rewrite /pline_at in Hok, Hpan, Hpref. rewrite Hstep in Hpref.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - subst sel.
      assert (Hc10 : c1 = 0%nat) by (cbn [count_true] in Hcnt; lia).
      assert (Hc20 : c2 = 0%nat) by (cbn [length] in Hlen; lia).
      subst c1 c2.
      rewrite (pend2_nil R) in Hpref. cbn [app] in Hpref.
      assert (Hb0 : pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat))
                      (palt_of a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hle : (nlines I <= S (length cs))%nat) by lia.
      iMod (pecl_blk2_open_t g k v P a b ps cs I ho H Hne Hr Hle Hpp HP
              Hok Hpan Hfk Hb0 with "Hpin [Htn] Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { cbn [count_true]. rewrite ?Nat.add_0_r. iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
      iDestruct "Hx"
        as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & #Hfz & _ & _ & _)".
      iLeft. cbn [count_true]. rewrite ?Nat.add_0_r. iFrame "Htn Hfz".
      rewrite /pblk_led. iRight. iExists w, gb. iFrame "Hpera Hcur".
      rewrite Hstep (pend2_nil R). cbn [app]. iFrame "Hrlb".
    - iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      iMod (pecl_blk2_byte_t g k v w gb tmi P (nlines I - 1)%nat a b
              (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
              Hok Hpan Hfk Hpref
              with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
          by (rewrite Hlb; lia). iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb' & #Hfz) | #HT]";
        [| by iRight].
      iLeft.
      replace (S (P + c1 + c2))%nat
        with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
      iFrame "Htn Hfz". rewrite /pblk_led. iRight. iExists w, gb.
      iFrame "Hpera Hcur". rewrite Hstep. iFrame "Hrlb'".
  Qed.

  Lemma pblk2_ecl_R_t_holds : ⊢ pblk2_ecl_R_t.
  Proof using .
    rewrite /pblk2_ecl_R_t. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 b tmi).
    iIntros "%Hw %Htl %Hb %Hwit #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (_ & Hstep).
    destruct Hwit as (a & Hok & Hpan & Hfk & Hpref).
    rewrite /pline_at in Hok, Hpan, Hpref. rewrite Hstep in Hpref.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - subst sel.
      assert (Hc10 : c1 = 0%nat) by (cbn [count_true] in Hcnt; lia).
      assert (Hc20 : c2 = 0%nat) by (cbn [length] in Hlen; lia).
      subst c1 c2.
      rewrite (pend2_nil R) in Hpref. cbn [app] in Hpref.
      assert (Hb0 : pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat))
                      (palt_of a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hle : (nlines I <= S (length cs))%nat) by lia.
      iMod (pecl_blk2_open_t g k v P a b ps cs I ho H Hne Hr Hle Hpp HP
              Hok Hpan Hfk Hb0 with "Hpin [Htn] Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { cbn [count_true]. rewrite ?Nat.add_0_r. iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
      iDestruct "Hx"
        as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & #Hfz & _ & _ & _)".
      iLeft. cbn [count_true]. rewrite ?Nat.add_0_r. iFrame "Htn Hfz".
      rewrite /pblk_led. iRight. iExists w, gb. iFrame "Hpera Hcur".
      rewrite Hstep (pend2_nil R). cbn [app]. iFrame "Hrlb".
    - iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      iMod (pecl_blk2_byte_t g k v w gb tmi P (nlines I - 1)%nat a b
              (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
              Hok Hpan Hfk Hpref
              with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
          by (rewrite Hlb; lia). iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb' & #Hfz) | #HT]";
        [| by iRight].
      iLeft.
      replace (S (P + c1 + c2))%nat
        with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
      iFrame "Htn Hfz". rewrite /pblk_led. iRight. iExists w, gb.
      iFrame "Hpera Hcur". rewrite Hstep. iFrame "Hrlb'".
  Qed.

  Lemma pblk2_ecl_t_holds : ⊢ pblk2_ecl_t.
  Proof using .
    rewrite /pblk2_ecl_t.
    (* [iSplitL ""], not [iSplit]: on [∗] with an empty context [iSplit]
       goes through [FromAnd] and searches for a [Persistent] half through
       the unfolded [R] body -- the same 28 s (15 s below) as [apply _]. *)
    iSplitL ""; [iApply pblk2_ecl_L_t_holds | iApply pblk2_ecl_R_t_holds].
  Qed.

  (* THE LANE'S DEBT, PAID *)
  Lemma pblk2_ecl_holds : ⊢ pblk2_ecl.
  Proof using .
    rewrite /pblk2_ecl.
    iSplitL ""; [iApply pblk2_ecl_L_holds |].
    iSplitL ""; [iApply pblk2_ecl_R_holds | iApply pblk2_ecl_file_holds].
  Qed.

  (* ================================================================= *)
  (*  S5  THE TWO BYTE STEPS, at the family held LINEARLY               *)
  (*                                                                   *)
  (*  THE PREMISE IS THE TAINT LINK ALONE, not [PipeLinks.pipe_links].  *)
  (*  Introducing the six-component bundle with an intuitionistic intro *)
  (*  pattern sends the [Persistent] search into its wand chains and it *)
  (*  does not return in THIS file's cone -- durable-notes, the entry   *)
  (*  on a bundle of wands hanging the Persistent search; the same      *)
  (*  tactic is fine in [PipeLinksLine].  The taint link is             *)
  (*  [box]-headed with its own instance, so it answers at once, and it *)
  (*  is all these lemmas ever spend; a caller projects it with         *)
  (*  [PipeLinks.pipe_links_taint].                                     *)
  (* ================================================================= *)

  Lemma pblk2_step_L (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    dg_execL !! c1 = Some b ->
    Forall nodollar (pend2 R sel) ->
    pblk2_wit I R (sel ++ [true]) ->
    pblk2_ecl_L -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 false -∗
    (pwc_blk2 k v I R (sel ++ [true]) (S c1) c2 false -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hb HndR Hwit. iIntros "#HL #Ht #Hpin Hc HΦ".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_blk2_taint. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HL" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /pwc_blk2.
    iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
    replace (P + S c1 + c2)%nat with (S (P + c1 + c2))%nat by lia.
    iFrame "Htn". iPureIntro. by split.
  Qed.

  Lemma pblk2_step_R (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    R !! c2 = Some b ->
    Forall nodollar R ->
    pblk2_wit I R (sel ++ [false]) ->
    pblk2_ecl_R -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 false -∗
    (pwc_blk2 k v I R (sel ++ [false]) c1 (S c2) false -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hb HndR Hwit. iIntros "#HR #Ht #Hpin Hc HΦ".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_blk2_taint. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HR" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /pwc_blk2.
    iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
    replace (P + c1 + S c2)%nat with (S (P + c1 + c2))%nat by lia.
    iFrame "Htn". iPureIntro. by split.
  Qed.

  (* ================================================================= *)
  (*  S6  THE EXIT: the prompt's own first byte files the round's code   *)
  (*                                                                   *)
  (*  ONE lemma at FOUR instances ([pblk2_code_ran] / [_execL] /        *)
  (*  [_execR] / [_both]).  What comes out is the ordinary block        *)
  (*  credential one byte from its end -- exactly                       *)
  (*  [PipeLinksLine.pwc_blk_sp]'s argument -- so the round rejoins the *)
  (*  shared vocabulary at [pwc_sp_t] and sh's walk continues unchanged. *)
  (* ================================================================= *)

  Lemma pblk2_exit (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (a : nat) (b : bv 8) (Φ : iProp Σ) :
    pblk2_code I R sel a ->
    sel <> [] ->
    b = u_prompt !!! 0%nat ->
    pblk2_ecl_file -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 false -∗
    (pwc_sp_t g k v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hcode Hnn Hb. iIntros "#HF #Ht #Hpin Hc HΦ".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite pwc_sp_t_view. by iRight. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    pose proof Hw as (_ & _ & _ & _ & _ & _ & Hlen & _).
    assert (Hpapr : papr I a) by exact (pblk2_code_papr I R sel a Hcode).
    assert (Hab : length (pab I a) = S (S (c1 + c2))%nat)
      by exact (pblk2_code_len I R sel a c1 c2 Hwf Hlen Hcode).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HF" $! k v (default [] o) H I R ps cs P sel c1 c2 a b
            with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ".
    iDestruct "Hret" as "[[Htn #Hcs'] | #HT]";
      last by (rewrite pwc_sp_t_view; iRight).
    iApply (pwc_blk_sp g k v I a Hpapr).
    rewrite pwc_blk_view Hab. iLeft. iExists ps, cs, P.
    replace (S (S (c1 + c2)) - 1)%nat with (S (c1 + c2))%nat by lia.
    cbn [blkcs_p].
    replace (P + S (c1 + c2))%nat with (S (P + c1 + c2))%nat by lia.
    iFrame "Htn Hps HE Hcs'". iPureIntro.
    split; [exact (wr_blk2_p_blk ps cs I P R sel c1 c2 Hw) | exact Htl].
  Qed.

  (* ================================================================= *)
  (*  S7  (R2)  THE CONCURRENT FORM: the family in a RECOVERABLE        *)
  (*      invariant, one cursor half per child, and the right child's   *)
  (*      SOURCE settled by the right child                             *)
  (*                                                                   *)
  (*  Neither child can hold the family between its own bytes, so it    *)
  (*  lives in an invariant keyed by the cursors' gnames and each child *)
  (*  holds half of its own cursor; a step opens the invariant INSIDE   *)
  (*  the link's own fancy update.  That is why the claim's steps (S4)  *)
  (*  are BASIC updates, and why the namespace must be disjoint from    *)
  (*  the port's.                                                       *)
  (*                                                                   *)
  (*  THREE THINGS DESIGN 4.3f (R2) ASKS FOR, AND ONE IT LEFT OUT.      *)
  (*                                                                   *)
  (*  (i) RECOVERABLE.  An [inv] is never deallocated, so after the two *)
  (*  waits the round must be able to take the family back out.  The    *)
  (*  body gains a DONE arm -- and the arm's token is NOT a third ghost *)
  (*  [gD] as designed: it is the two cursors held WHOLE               *)
  (*  ([blk2_done]).  The design's [wcur gD 1 1] cannot be used,        *)
  (*  because the party that has to REFUTE the DONE arm most often is a *)
  (*  CHILD -- its byte step must rule out `the round already closed'   *)
  (*  -- and a child never holds [gD].  It does hold half of its own    *)
  (*  cursor, and a half beside a whole is [False]; so parking the two  *)
  (*  cursors whole is refutable by both children AND by the round      *)
  (*  (which holds both children's returned halves).  One ghost fewer   *)
  (*  and one law fewer than the ruling asks for.                       *)
  (*                                                                   *)
  (*  (ii) THE RIGHT CHILD'S SOURCE IS EXISTENTIAL, pinned by a         *)
  (*  one-shot the right child fires before its first byte ([rmode], a  *)
  (*  [wcur] of its own: 0 = not yet, 1 = the LINE (cat printing what   *)
  (*  it read, [PRan]), 2 = [dg_execR] (its exec failed)).  At          *)
  (*  [c2 = 0] the family does not read [R] at all                      *)
  (*  ([pwc_blk2_R_indep]), which is what makes the existential sound.  *)
  (*                                                                   *)
  (*  (iii) THE TWO CHILDREN'S PARTICIPATION IS EXCLUSIVE, AND DESIGN   *)
  (*  4.3f LEFT THAT OUT.  [pblk2_wit I R sel] -- the witness every     *)
  (*  byte step spends -- is FALSE at [R = L] and a selector carrying   *)
  (*  both a true and a false bit: [pend2 L sel] then begins with bytes *)
  (*  of [dg_execL] and continues with bytes of the LINE, and no        *)
  (*  alternative of an [LPipe] line has that continuation ([PExecL]'s  *)
  (*  is [dg_execL], [PRan]'s is the line, [PBoth sel']'s is the merge  *)
  (*  of [dg_execL] with [dg_execR]).  So `the left child printed' and  *)
  (*  `cat printed the line' are incompatible -- TRUE of the machine    *)
  (*  (the left child prints [dg_execL] only when its exec failed, and  *)
  (*  then nothing ever enters the pipe, so cat prints nothing) but a   *)
  (*  fact about the PROTOCOL, not about the console.  It enters here   *)
  (*  as two abstract witnesses and one premise: [XL] (`the left child  *)
  (*  kept echo's write permit'), [YR] (`a byte reached the reader'),   *)
  (*  and [box (XL -* YR ={Eex}=* False)].  This file stays protocol-free;    *)
  (*  the round supplies the pair out of [PipeProto].                   *)
  (* ================================================================= *)

  (* ---- R-INDEPENDENCE AT AN EMPTY RIGHT CURSOR ---- *)
  Lemma pend2_R_eq (R R' : list (bv 8)) (sel : list bool) (c1 : nat) :
    length sel = c1 -> count_true sel = c1 ->
    (c1 <= length dg_execL)%nat ->
    pend2 R sel = pend2 R' sel.
  Proof using .
    intros Hl Hc Hle. rewrite /pend2.
    rewrite (pmerge_all_true sel dg_execL R); [| lia | lia].
    rewrite (pmerge_all_true sel dg_execL R'); [| lia | lia].
    reflexivity.
  Qed.

  Lemma pblk2_wit_R_eq (I R R' : list (bv 8)) (sel : list bool) :
    pend2 R sel = pend2 R' sel ->
    pblk2_wit I R' sel -> pblk2_wit I R sel.
  Proof using .
    intros Heq (a & Hok & Hpan & Hfk & Hpref). exists a.
    split_and!; [exact Hok | exact Hpan | exact Hfk |]. by rewrite Heq.
  Qed.

  Lemma pwc_blk2_R_indep (k : nat) (v : era_pins) (I : list (bv 8))
      (R R' : list (bv 8)) (sel : list bool) (c1 : nat) (tm : bool) :
    pwc_blk2 k v I R sel c1 0%nat tm -∗ pwc_blk2 k v I R' sel c1 0%nat tm.
  Proof using .
    rewrite /pwc_blk2. iIntros "[Hx | #HT]"; last by iRight.
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt
                      & H1 & _).
    assert (Heq : pend2 R sel = pend2 R' sel).
    { apply (pend2_R_eq R R' sel c1); [lia | exact Hcnt | exact H1]. }
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
    iSplitR.
    { iPureIntro. rewrite /wr_blk2_p.
      split_and!; try assumption; lia. }
    iSplitR; [by iPureIntro |].
    rewrite /pblk_led. iDestruct "Hled" as "[%Hnil | Hled]"; [by iLeft |].
    iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
    iRight. iExists w, gb. iFrame "Hpera Hcur". by rewrite -Heq.
  Qed.

  (* ---- THE RIGHT CHILD'S MODE ---- *)
  (* THE THIRD SOURCE (lane PIPE-STAGE-3): mode [3] is the RUNCMD CHILD's
     own panic at a failed [fork1], whose bytes are [alt_forkc] --
     `fork\n' written by the child and then the prompt's `$ ' written by
     sh's MAIN LOOP one process later.  It is a mode and not a fourth
     cursor because the block's right half is ONE list read at ONE
     cursor; who holds that cursor changes at the child's exit. *)
  Definition rsrc (L : list (bv 8)) (n : nat) : list (bv 8) :=
    match n with
    | S O => L
    | S (S (S O)) => alt_forkc
    | _ => dg_execR
    end.

  (* THE FLAG THE CLAIM SEES (lane PIPE-STAGE-4, design SS4.3m).  A round
     is TERMINAL exactly when the runcmd child's own panic (mode 3) has
     put a byte on the wire.  Before that first byte the family does not
     read [R] at all ([pwc_blk2_R_indep]), so [c2 = 0] is not yet
     terminal -- and a stray writing at mode 3 before it goes through the
     LANDED (non-terminal) obligation, at the [PExecL] witness. *)
  Definition tmb (n c2 : nat) : bool :=
    match n, c2 with
    | 3%nat, S _ => true
    | _, _ => false
    end.

  Lemma tmb_true (n c2 : nat) : tmb n c2 = true -> n = 3%nat.
  Proof using .
    rewrite /tmb. destruct n as [| [| [| [| n]]]]; destruct c2; congruence.
  Qed.

  Lemma tmb_zero (n : nat) : tmb n 0%nat = false.
  Proof using . rewrite /tmb. by destruct n as [| [| [| [| n]]]]. Qed.

  (* ...AND THE MODE CARRIES IT, so [blk2_body] can hand the flag to
     [pwc_blk2] without naming the mode itself. *)
  Definition rmode (gM : gname) (L R : list (bv 8)) (c2 : nat)
      (tm : bool) (YR : iProp Σ) : iProp Σ :=
    (∃ n : nat, wcur gM (1/2) n ∗ ⌜tm = tmb n c2⌝
       ∗ (⌜n = 0%nat /\ c2 = 0%nat⌝
          ∨ (⌜n = 1%nat /\ R = L⌝ ∗ YR)
          ∨ ⌜n = 2%nat /\ R = dg_execR⌝
          ∨ ⌜n = 3%nat /\ R = alt_forkc⌝))%I.

  Global Instance rmode_timeless gM L R c2 tm YR :
    Timeless YR -> Timeless (rmode gM L R c2 tm YR).
  Proof using .
    intro. rewrite /rmode.
    apply bi.exist_timeless; intro n.
    apply bi.sep_timeless; [apply wcur_timeless |].
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.or_timeless; [apply bi.pure_timeless |].
    apply bi.or_timeless;
      [| apply bi.or_timeless; apply bi.pure_timeless].
    apply bi.sep_timeless; [apply bi.pure_timeless | assumption].
  Qed.

  Lemma rmode_src (gM : gname) (L R : list (bv 8)) (c2 n : nat)
      (tm : bool) (YR : iProp Σ) :
    n <> 0%nat ->
    wcur gM (1/2) n -∗ rmode gM L R c2 tm YR -∗ ⌜R = rsrc L n⌝.
  Proof using .
    intros Hn. iIntros "Hm Hr". rewrite /rmode.
    iDestruct "Hr" as (n') "(Hm' & _ & Harm)".
    iDestruct (wcur_agree with "Hm Hm'") as %<-.
    iDestruct "Harm" as "[%Ha | [[%Ha _] | [%Ha | %Ha]]]".
    - exfalso. apply Hn. exact (proj1 Ha).
    - iPureIntro. destruct Ha as [-> ->]. reflexivity.
    - iPureIntro. destruct Ha as [-> ->]. reflexivity.
    - iPureIntro. destruct Ha as [-> ->]. reflexivity.
  Qed.

  (* ---- THE DONE ARM: the two cursors, PARKED WHOLE ---- *)
  Definition blk2_done (gL gR : gname) : iProp Σ :=
    ((∃ x : nat, wcur gL 1 x) ∗ (∃ y : nat, wcur gR 1 y))%I.

  Global Instance blk2_done_timeless gL gR : Timeless (blk2_done gL gR).
  Proof using .
    rewrite /blk2_done.
    apply bi.sep_timeless;
      (apply bi.exist_timeless; intro; apply wcur_timeless).
  Qed.

  Lemma blk2_done_not_L (gL gR : gname) (c : nat) :
    wcur gL (1/2) c -∗ blk2_done gL gR -∗ False.
  Proof using .
    rewrite /blk2_done /wcur. iIntros "H1 [Hx _]".
    iDestruct "Hx" as (x) "H2".
    by iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
  Qed.

  Lemma blk2_done_not_R (gL gR : gname) (c : nat) :
    wcur gR (1/2) c -∗ blk2_done gL gR -∗ False.
  Proof using .
    rewrite /blk2_done /wcur. iIntros "H1 [_ Hy]".
    iDestruct "Hy" as (y) "H2".
    by iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
  Qed.

  (* ---- THE BODY, AND THE INVARIANT ---- *)
  Definition blk2_body (k : nat) (v : era_pins) (I L : list (bv 8))
      (gL gR gM : gname) (XL YR : iProp Σ) : iProp Σ :=
    ((∃ (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) (tm : bool),
        pwc_blk2 k v I R sel c1 c2 tm
        ∗ wcur gL (1/2) c1 ∗ wcur gR (1/2) c2
        ∗ (⌜c1 = 0%nat⌝ ∨ XL)
        ∗ rmode gM L R c2 tm YR)
     ∨ blk2_done gL gR)%I.

  Global Instance blk2_body_timeless k v I L gL gR gM XL YR :
    Timeless XL -> Timeless YR ->
    Timeless (blk2_body k v I L gL gR gM XL YR).
  Proof using .
    intros HX HY. rewrite /blk2_body.
    apply bi.or_timeless; [| apply blk2_done_timeless].
    apply bi.exist_timeless; intro R.
    apply bi.exist_timeless; intro sel.
    apply bi.exist_timeless; intro c1.
    apply bi.exist_timeless; intro c2.
    apply bi.exist_timeless; intro tm.
    apply bi.sep_timeless; [apply pwc_blk2_timeless |].
    apply bi.sep_timeless; [apply wcur_timeless |].
    apply bi.sep_timeless; [apply wcur_timeless |].
    apply bi.sep_timeless;
      [apply bi.or_timeless; [apply bi.pure_timeless | exact HX]
       | by apply rmode_timeless].
  Qed.

  Definition blk2_inv (N : namespace) (k : nat) (v : era_pins)
      (I L : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ) : iProp Σ :=
    inv N (blk2_body k v I L gL gR gM XL YR).

  Global Instance blk2_inv_persistent N k v I L gL gR gM XL YR :
    Persistent (blk2_inv N k v I L gL gR gM XL YR).
  Proof using . rewrite /blk2_inv. apply _. Qed.

  (* ---- THE ENTRY: the round's own lend, three ghosts minted ---- *)
  Lemma blk2_inv_alloc (E : coPset) (N : namespace) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (XL YR : iProp Σ) :
    pboth_line I ->
    pwc_lend g k v I ={E}=∗
    ∃ gL gR gM : gname,
      blk2_inv N k v I L gL gR gM XL YR
      ∗ wcur gL (1/2) 0%nat ∗ wcur gR (1/2) 0%nat ∗ wcur gM (1/2) 0%nat.
  Proof using .
    intros Hline. iIntros "Hlend".
    iMod (ghost_var_alloc (0%nat)) as (gL) "HL".
    iMod (ghost_var_alloc (0%nat)) as (gR) "HR".
    iMod (ghost_var_alloc (0%nat)) as (gM) "HM".
    iDestruct (ghost_var_split gL 0%nat (1/2) (1/2) with "[HL]")
      as "[HL1 HL2]"; [by rewrite Qp.half_half |].
    iDestruct (ghost_var_split gR 0%nat (1/2) (1/2) with "[HR]")
      as "[HR1 HR2]"; [by rewrite Qp.half_half |].
    iDestruct (ghost_var_split gM 0%nat (1/2) (1/2) with "[HM]")
      as "[HM1 HM2]"; [by rewrite Qp.half_half |].
    iDestruct (pwc_blk2_of_lend k v I dg_execR false Hline with "Hlend")
      as "Hf".
    iMod (inv_alloc N E (blk2_body k v I L gL gR gM XL YR)
            with "[Hf HL1 HR1 HM1]") as "#Hinv".
    { iNext. rewrite /blk2_body. iLeft.
      iExists dg_execR, [], 0%nat, 0%nat, false. rewrite /wcur.
      iFrame "Hf HL1 HR1".
      iSplitR; [by iLeft |]. rewrite /rmode. iExists 0%nat.
      rewrite /wcur. iFrame "HM1". iSplitR; [by iPureIntro |].
      iLeft. by iPureIntro. }
    iModIntro. iExists gL, gR, gM. rewrite /wcur.
    by iFrame "Hinv HL2 HR2 HM2".
  Qed.

  (* ---- THE RIGHT CHILD FIXES ITS SOURCE, BEFORE ITS FIRST BYTE ----
     No exclusion is spent here: the incompatibility of the two children
     is spent at the BYTE STEPS, where the invariant itself carries the
     [YR] this fire deposits. *)
  Lemma blk2_mode_fire (E : coPset) (N : namespace) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (n : nat) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ⊆ E ->
    n = 1%nat \/ n = 2%nat \/ n = 3%nat ->
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gM (1/2) 0%nat -∗ wcur gR (1/2) 0%nat -∗
    (⌜n = 1%nat⌝ -∗ YR) ={E}=∗
    wcur gM (1/2) n ∗ wcur gR (1/2) 0%nat.
  Proof using .
    intros HTX HTY HN Hn. iIntros "#Hinv HM HR HY".
    iMod (inv_acc E N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_R gL gR 0%nat with "HR Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1 c2 tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    (* the right cursor is the child's own, still at zero -- so the
       family does not read [R] and the mode's arm says nothing more *)
    iDestruct (wcur_agree with "HR HgR") as %<-.
    rewrite {1}/rmode. iDestruct "Hrm" as (n0) "(HgM & %Htmb & Harm)".
    iDestruct (wcur_agree with "HM HgM") as %<-.
    iClear "Harm".
    (* the flag is [false] at [c2 = 0] whatever the mode, so the fire --
       mode 3 included -- does not move it; the FIRST PANIC BYTE does *)
    rewrite Htmb tmb_zero.
    iMod (wcur_update gM 0%nat 0%nat n with "HM HgM") as "[HM HgM]".
    iDestruct (pwc_blk2_R_indep k v I R (rsrc L n) sel c1 false with "Hf")
      as "Hf".
    iMod ("Hclose" with "[Hf HgL HgR Hxl HgM HY]") as "_".
    { iNext. rewrite /blk2_body. iLeft.
      iExists (rsrc L n), sel, c1, 0%nat, false. iFrame "Hf HgL HgR Hxl".
      rewrite /rmode. iExists n. iFrame "HgM".
      iSplitR; [iPureIntro; by rewrite tmb_zero |].
      destruct Hn as [-> | [-> | ->]].
      - iRight. iLeft. iSplitR; [by iPureIntro |].
        iApply "HY". by iPureIntro.
      - iRight. iRight. iLeft. by iPureIntro.
      (* MODE FORK NEEDS NO EXCLUSION: the arm it installs carries no
         [YR] at all, because the runcmd child holds the right cursor
         itself -- it has not forked the right child. *)
      - iRight. iRight. iRight. by iPureIntro. }
    iModIntro. iFrame "HM HR".
  Qed.

  (* ---- THE LEFT CHILD'S BYTE ---- *)
  Lemma pblk2_cstep_L (N : namespace) (Eex : coPset) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c1 : nat) (b : bv 8) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    dg_execL !! c1 = Some b ->
    (forall sel : list bool,
       sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel) ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    □ (XL -∗ YR ={Eex}=∗ False) -∗
    pblk2_ecl_L -∗ pblk2_ecl_L_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I L gL gR gM XL YR -∗ wcur gL (1/2) c1 -∗
    (⌜c1 = 0%nat⌝ -∗ XL) -∗
    (wcur gL (1/2) (S c1) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros HTX HTY Hns HEx Hb Hwit Hwitt.
    iIntros "#Hex #HL #HLt #Ht #Hpin #Hinv HcL HXw HΦ".
    pose proof (lookup_lt_Some _ _ _ Hb) as HbL.
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_L gL gR c1 with "HcL Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1' c2 tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    iDestruct (wcur_agree with "HcL HgL") as %<-.
    (* ONE [XL] IN HAND, wherever it came from *)
    iAssert XL with "[Hxl HXw]" as "HXL".
    { iDestruct "Hxl" as "[%Hc0 | HX]";
        [iApply "HXw"; by iPureIntro | iExact "HX"]. }
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]"; last first.
    { (* the era is tainted: the claim answers any event out of its taint
         arm and the cursor moves on its own *)
      iMod (pecl_sup g k (default [] o) H (ConsLog.EvOut b) with "HT Hres")
        as "Hres".
      iMod (wcur_update gL c1 c1 (S c1) with "HcL HgL") as "[HcL HgL]".
      iMod ("Hclose" with "[HgL HgR HXL Hrm]") as "_".
      { iNext. rewrite /blk2_body. iLeft.
        iExists R, sel, (S c1), c2, tm. iFrame "HgL HgR Hrm".
        iSplitL ""; [by iApply pwc_blk2_taint |]. by iRight. }
      iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
      by iApply "HΦ". }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt
                      & Hc1L & Hc2R).
    (* THE SOURCE: the mode says which, and [R = L] is REFUTED here *)
    rewrite {1}/rmode. iDestruct "Hrm" as (n) "(HgM & %Htmb & Harm)".
    (* WHICH OBLIGATION: the round's TERMINAL FLAG, and not the witness,
       decides -- and the flag is [tmb n c2], so a stray writing at mode
       3 BEFORE the runcmd child's first panic byte ([c2 = 0]) still goes
       through the LANDED obligation, at the [PExecL] witness. *)
    iAssert (|={⊤ ∖ ↑uartN Uart0 ∖ ↑N}=>
               ⌜(tm = false /\ pblk2_wit I R (sel ++ [true])
                 /\ Forall nodollar (pend2 R sel))
                \/ (tm = true /\ pblk2_wit_t I R (sel ++ [true]))⌝
               ∗ rmode gM L R c2 tm YR ∗ XL)%I
      with "[Harm HgM HXL]" as ">(%Hwit1 & Hrm & HXL)".
    { iDestruct "Harm" as "[%Ha | [[%Ha HYR] | [%Ha | %Ha]]]".
      - (* the mode is UNSET: [c2 = 0], so the block so far is all-left
           and [R] is not read at all *)
        destruct Ha as [Hn0 Hc20]. subst c2.
        iModIntro. iFrame "HXL".
        iSplitR.
        { iPureIntro. left. split; [by rewrite Htmb tmb_zero |]. split.
          - apply (pblk2_wit_R_eq I R dg_execR (sel ++ [true])).
            + apply (pend2_R_eq R dg_execR (sel ++ [true]) (S c1));
                [ rewrite length_app; cbn [length]; lia
                | rewrite count_true_app; cbn [count_true]; lia
                | lia ].
            + apply Hwit. rewrite /sel_wf2 count_true_app length_app.
              cbn [count_true length]. lia.
          - rewrite /pend2 (pmerge_all_true sel dg_execL R); [| lia | lia].
            apply Forall_lookup. intros i x Hx.
            apply lookup_take_Some in Hx as [Hx _].
            exact (Forall_lookup_1 _ _ _ _ dg_execL_nodollar Hx). }
        rewrite /rmode. iExists n. iFrame "HgM".
        iSplitR; [by iPureIntro |]. iLeft. by iPureIntro.
      - (* [R = L]: cat is printing the line, so the left child never
           wrote -- and it is holding the very permit that says so *)
        iMod (fupd_mask_subseteq Eex) as "_"; [exact HEx |].
        iMod ("Hex" with "HXL HYR") as "[]".
      - destruct Ha as [Hn2 HR]. subst R.
        iModIntro. iFrame "HXL". iSplitR.
        { iPureIntro. left.
          split; [by rewrite Htmb Hn2 /tmb; destruct c2 |]. split.
          - apply Hwit. rewrite /sel_wf2 count_true_app length_app.
            cbn [count_true length]. lia.
          - rewrite /pend2. apply pmerge_nodollar;
              [exact dg_execL_nodollar | exact dg_execR_nodollar]. }
        rewrite /rmode. iExists n. iFrame "HgM".
        iSplitR; [by iPureIntro |]. iRight. iRight. iLeft.
        by iPureIntro.
      - (* MODE FORK (lane PIPE-STAGE-3): the stray is writing into the
           TERMINAL round's block.  Its witness is a [PForkS], and the
           block carries the prompt's `$' -- so no `$'-freeness is
           claimed here and none is needed: D4 refutes the next input.
           At [c2 = 0] the panic byte has NOT been written yet and the
           flag is still [false]: the landed obligation serves, at the
           very argument the unset-mode arm uses. *)
        destruct Ha as [Hn3 HR]. subst R.
        iModIntro. iFrame "HXL". iSplitR.
        { iPureIntro. destruct c2 as [| c2'].
          - left. split; [by rewrite Htmb tmb_zero |]. split.
            + apply (pblk2_wit_R_eq I alt_forkc dg_execR (sel ++ [true])).
              * apply (pend2_R_eq alt_forkc dg_execR (sel ++ [true]) (S c1));
                  [ rewrite length_app; cbn [length]; lia
                  | rewrite count_true_app; cbn [count_true]; lia
                  | lia ].
              * apply Hwit. rewrite /sel_wf2 count_true_app length_app.
                cbn [count_true length]. lia.
            + rewrite /pend2 (pmerge_all_true sel dg_execL alt_forkc);
                [| lia | lia].
              apply Forall_lookup. intros i x Hx.
              apply lookup_take_Some in Hx as [Hx _].
              exact (Forall_lookup_1 _ _ _ _ dg_execL_nodollar Hx).
          - right. split; [by rewrite Htmb Hn3 |]. apply Hwitt.
            rewrite /sel_wf2 count_true_app length_app.
            cbn [count_true length]. lia. }
        rewrite /rmode. iExists n. iFrame "HgM".
        iSplitR; [by iPureIntro |]. iRight. iRight. iRight.
        by iPureIntro. }
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    iAssert (|={⊤ ∖ ↑uartN Uart0 ∖ ↑N}=>
               pecl g k (default [] o)
                 (ConsLog.cons_step H (ConsLog.EvOut b))
               ∗ ((turn v (S (P + c1 + c2))%nat
                   ∗ pblk_led k I R (sel ++ [true]) tm) ∨ PT))%I
      with "[Htn Hled Hres]" as ">(Hres & Hret)".
    { destruct Hwit1 as [(Htmf & Hwa & Hndb) | (Htmt & Hwa)].
      - rewrite Htmf.
        iMod ("HL" $! k v (default [] o) H I R ps cs P sel c1 c2 b
                with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
          as "(Hres & Hret)".
        iModIntro. iFrame "Hres Hret".
      - rewrite Htmt.
        iMod ("HLt" $! k v (default [] o) H I R ps cs P sel c1 c2 b true
                with "[//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
          as "(Hres & Hret)".
        iModIntro. iFrame "Hres".
        iDestruct "Hret" as "[(Htn & Hled' & _) | #HT]"; [| by iRight].
        iLeft. iFrame "Htn Hled'". }
    iMod (wcur_update gL c1 c1 (S c1) with "HcL HgL") as "[HcL HgL]".
    iMod ("Hclose" with "[Hret HgL HgR HXL Hrm]") as "_".
    { iNext. rewrite /blk2_body. iLeft.
      iExists R, (sel ++ [true]), (S c1), c2, tm. iFrame "HgL HgR Hrm".
      iSplitL "Hret".
      - rewrite /pwc_blk2.
        iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
        iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
        replace (P + S c1 + c2)%nat with (S (P + c1 + c2))%nat by lia.
        iFrame "Htn". iPureIntro. by split.
      - by iRight. }
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  Lemma rmode_zero (gM : gname) (L R : list (bv 8)) (c2 : nat)
      (tm : bool) (YR : iProp Σ) :
    wcur gM (1/2) 0%nat -∗ rmode gM L R c2 tm YR -∗ ⌜c2 = 0%nat⌝.
  Proof using .
    iIntros "Hm Hr". rewrite /rmode.
    iDestruct "Hr" as (n') "(Hm' & _ & Harm)".
    iDestruct (wcur_agree with "Hm Hm'") as %<-.
    iDestruct "Harm" as "[%Ha | [[%Ha _] | [%Ha | %Ha]]]"; iPureIntro;
      first [ exact (proj2 Ha) | exfalso; discriminate (proj1 Ha) ].
  Qed.

  Lemma rmode_flag (gM : gname) (L R : list (bv 8)) (c2 n : nat)
      (tm : bool) (YR : iProp Σ) :
    wcur gM (1/2) n -∗ rmode gM L R c2 tm YR -∗ ⌜tm = tmb n c2⌝.
  Proof using .
    iIntros "Hm Hr". rewrite /rmode.
    iDestruct "Hr" as (n') "(Hm' & %Ht & _)".
    by iDestruct (wcur_agree with "Hm Hm'") as %<-.
  Qed.

  Lemma rmode_bump (gM : gname) (L R : list (bv 8)) (c2 c2' n : nat)
      (tm tm' : bool) (YR : iProp Σ) :
    n <> 0%nat -> tm' = tmb n c2' ->
    wcur gM (1/2) n -∗ rmode gM L R c2 tm YR -∗
    wcur gM (1/2) n ∗ rmode gM L R c2' tm' YR.
  Proof using .
    intros Hn Htm'. iIntros "Hm Hr". rewrite {1}/rmode.
    iDestruct "Hr" as (n') "(Hm' & _ & Harm)".
    iDestruct (wcur_agree with "Hm Hm'") as %<-.
    iFrame "Hm". rewrite /rmode. iExists n. iFrame "Hm'".
    iSplitR; [by iPureIntro |].
    iDestruct "Harm" as "[%Ha | [[%Ha HY] | [%Ha | %Ha]]]".
    - exfalso. apply Hn. exact (proj1 Ha).
    - iRight. iLeft. iFrame "HY". by iPureIntro.
    - iRight. iRight. iLeft. by iPureIntro.
    - iRight. iRight. iRight. by iPureIntro.
  Qed.

  Lemma rmode_one_YR (gM : gname) (L R : list (bv 8)) (c2 : nat)
      (tm : bool) (YR : iProp Σ) :
    wcur gM (1/2) 1%nat -∗ rmode gM L R c2 tm YR -∗ YR.
  Proof using .
    iIntros "Hm Hr". rewrite /rmode.
    iDestruct "Hr" as (n') "(Hm' & _ & Harm)".
    iDestruct (wcur_agree with "Hm Hm'") as %<-.
    iDestruct "Harm" as "[%Ha | [[%Ha HY] | [%Ha | %Ha]]]".
    - exfalso. destruct Ha as [Ha _]. discriminate Ha.
    - iExact "HY".
    - exfalso. destruct Ha as [Ha _]. discriminate Ha.
    - exfalso. destruct Ha as [Ha _]. discriminate Ha.
  Qed.

  (* ---- THE RIGHT CHILD'S BYTE, at its OWN source ---- *)
  Lemma pblk2_cstep_R (N : namespace) (Eex : coPset) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (n c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    n = 1%nat \/ n = 2%nat ->
    rsrc L n !! c2 = Some b ->
    Forall nodollar (rsrc L n) ->
    (forall sel : list bool,
       sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel) ->
    (forall sel : list bool,
       count_true sel = 0%nat -> (length sel <= length L)%nat ->
       pblk2_wit I L sel) ->
    □ (XL -∗ YR ={Eex}=∗ False) -∗
    pblk2_ecl_R -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gR (1/2) c2 -∗ wcur gM (1/2) n -∗
    (wcur gR (1/2) (S c2) -∗ wcur gM (1/2) n -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros HTX HTY Hns HEx Hn Hb HndR Hwit2 Hwit1.
    iIntros "#Hex #HR #Ht #Hpin #Hinv HcR HcM HΦ".
    pose proof (lookup_lt_Some _ _ _ Hb) as HbR.
    assert (Hn0 : n <> 0%nat) by (destruct Hn as [-> | ->]; lia).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_R gL gR c2 with "HcR Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1 c2' tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    iDestruct (wcur_agree with "HcR HgR") as %<-.
    iDestruct (rmode_src gM L R c2 n tm YR Hn0 with "HcM Hrm") as %HRn.
    subst R.
    (* AT MODES 1 AND 2 THE ROUND IS NOT TERMINAL, and the flag says so:
       [tmb n c2 = false] for every [n <> 3]. *)
    iDestruct (rmode_flag gM L (rsrc L n) c2 n tm YR with "HcM Hrm")
      as %Htmb.
    assert (Htmf : tm = false)
      by (rewrite Htmb; destruct Hn as [-> | ->]; by destruct c2).
    rewrite Htmf.
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]"; last first.
    { iMod (pecl_sup g k (default [] o) H (ConsLog.EvOut b) with "HT Hres")
        as "Hres".
      iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
      iDestruct (rmode_bump gM L (rsrc L n) c2 (S c2) n false false YR Hn0
                   ltac:(destruct Hn as [-> | ->]; reflexivity)
                   with "HcM Hrm") as "[HcM Hrm]".
      iMod ("Hclose" with "[HgL HgR Hxl Hrm]") as "_".
      { iNext. rewrite /blk2_body. iLeft.
        iExists (rsrc L n), sel, c1, (S c2), false. iFrame "HgL HgR Hxl Hrm".
        by iApply pwc_blk2_taint. }
      iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
      by iApply ("HΦ" with "HcR HcM"). }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt
                      & Hc1L & Hc2R).
    iAssert (|={⊤ ∖ ↑uartN Uart0 ∖ ↑N}=>
               ⌜pblk2_wit I (rsrc L n) (sel ++ [false])⌝
               ∗ (⌜c1 = 0%nat⌝ ∨ XL) ∗ wcur gM (1/2) n
               ∗ rmode gM L (rsrc L n) c2 false YR)%I
      with "[Hxl HcM Hrm]" as ">(%Hwit' & Hxl & HcM & Hrm)".
    { destruct Hn as [Hn1 | Hn2].
      - (* [n = 1]: cat is printing the LINE, so the left child never
           wrote -- and if it did, its permit meets the reader's byte *)
        subst n. cbn [rsrc] in Hb, HbR, Hc2R |- *.
        iDestruct "Hxl" as "[%Hc10 | HXL]"; last first.
        { iDestruct (rmode_one_YR gM L L c2 false YR with "HcM Hrm") as "HYR".
          iMod (fupd_mask_subseteq Eex) as "_"; [exact HEx |].
          iMod ("Hex" with "HXL HYR") as "[]". }
        iModIntro. iFrame "HcM Hrm". iSplitR; [| iLeft; by iPureIntro].
        iPureIntro. apply Hwit1.
        + rewrite count_true_app. cbn [count_true]. lia.
        + rewrite length_app. cbn [length]. lia.
      - subst n. cbn [rsrc] in Hb, HbR, Hc2R |- *.
        iModIntro. iFrame "Hxl HcM Hrm". iPureIntro. apply Hwit2.
        rewrite /sel_wf2 count_true_app length_app.
        cbn [count_true length]. lia. }
    destruct (wr_blk2_step_R ps cs I P (rsrc L n) sel c1 c2 b Hw Hb)
      as (Hw' & _).
    iMod ("HR" $! k v (default [] o) H I (rsrc L n) ps cs P sel c1 c2 b
            with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
    iDestruct (rmode_bump gM L (rsrc L n) c2 (S c2) n false false YR Hn0
                 ltac:(destruct Hn as [-> | ->]; reflexivity)
                 with "HcM Hrm") as "[HcM Hrm]".
    iMod ("Hclose" with "[Hret HgL HgR Hxl Hrm]") as "_".
    { iNext. rewrite /blk2_body. iLeft.
      iExists (rsrc L n), (sel ++ [false]), c1, (S c2), false.
      iFrame "HgL HgR Hxl Hrm". rewrite /pwc_blk2.
      iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
      iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
      replace (P + c1 + S c2)%nat with (S (P + c1 + c2))%nat by lia.
      iFrame "Htn". iPureIntro. by split. }
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    by iApply ("HΦ" with "HcR HcM").
  Qed.

  (* ---- THE RIGHT CURSOR AT MODE FORK (lane PIPE-STAGE-3) ----
     The runcmd child's own [fork1] panic (positions 0-4 of [alt_forkc],
     `fork\n'), and -- at the very same cursor, one process later --
     sh's MAIN LOOP's prompt (positions 5, 6, `$ ').  NO EXCLUSION IS
     SPENT: [rmode]'s arms are exclusive in [n], the mode half pins
     [n = 3], and the family's [R = L] branch (cat printing the line) is
     therefore UNREACHABLE here -- which is also why this step asks for
     neither [XL], nor [YR], nor a mask [Eex]. *)
  Lemma pblk2_cstep_R_t (N : namespace) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    alt_forkc !! c2 = Some b ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    pblk2_ecl_R_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gR (1/2) c2 -∗ wcur gM (1/2) 3%nat -∗
    (wcur gR (1/2) (S c2) -∗ wcur gM (1/2) 3%nat -∗
     (cs_frozen_at v (nlines I - 1)%nat ∨ PT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros HTX HTY Hns Hb Hwitt.
    iIntros "#HR #Ht #Hpin #Hinv HcR HcM HΦ".
    pose proof (lookup_lt_Some _ _ _ Hb) as HbR.
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_R gL gR c2 with "HcR Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1 c2' tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    iDestruct (wcur_agree with "HcR HgR") as %<-.
    iDestruct (rmode_src gM L R c2 3%nat tm YR ltac:(lia) with "HcM Hrm")
      as %HRn.
    cbn [rsrc] in HRn. subst R.
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]"; last first.
    { iMod (pecl_sup g k (default [] o) H (ConsLog.EvOut b) with "HT Hres")
        as "Hres".
      iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
      iDestruct (rmode_bump gM L alt_forkc c2 (S c2) 3%nat tm true YR
                   ltac:(lia) ltac:(reflexivity)
                   with "HcM Hrm") as "[HcM Hrm]".
      iMod ("Hclose" with "[HgL HgR Hxl Hrm]") as "_".
      { iNext. rewrite /blk2_body. iLeft.
        iExists alt_forkc, sel, c1, (S c2), true. iFrame "HgL HgR Hxl Hrm".
        by iApply pwc_blk2_taint. }
      iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
      iApply ("HΦ" with "HcR HcM"). by iRight. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt
                      & Hc1L & Hc2R).
    assert (Hwit' : pblk2_wit_t I alt_forkc (sel ++ [false])).
    { apply Hwitt. rewrite /sel_wf2 count_true_app length_app.
      cbn [count_true length]. lia. }
    destruct (wr_blk2_step_R ps cs I P alt_forkc sel c1 c2 b Hw Hb)
      as (Hw' & _).
    iMod ("HR" $! k v (default [] o) H I alt_forkc ps cs P sel c1 c2 b tm
            with "[//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
    iDestruct (rmode_bump gM L alt_forkc c2 (S c2) 3%nat tm true YR
                 ltac:(lia) ltac:(reflexivity)
                 with "HcM Hrm") as "[HcM Hrm]".
    (* THE FROZEN RESOLUTION comes out of the step and is PERSISTENT, so
       the writer keeps a copy while the family goes back in. *)
    iAssert (cs_frozen_at v (nlines I - 1)%nat ∨ PT)%I as "#Hfz".
    { iDestruct "Hret" as "[(_ & _ & #Hf) | #HT]"; [by iLeft | by iRight]. }
    iMod ("Hclose" with "[Hret HgL HgR Hxl Hrm]") as "_".
    { iNext. rewrite /blk2_body. iLeft.
      iExists alt_forkc, (sel ++ [false]), c1, (S c2), true.
      iFrame "HgL HgR Hxl Hrm". rewrite /pwc_blk2.
      iDestruct "Hret" as "[(Htn & Hled' & _) | #HT]"; [| by iRight].
      iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
      replace (P + c1 + S c2)%nat with (S (P + c1 + c2))%nat by lia.
      iFrame "Htn". iPureIntro. by split. }
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    by iApply ("HΦ" with "HcR HcM Hfz").
  Qed.

  (* ---- THE ROUND TAKES THE FAMILY BACK, AFTER BOTH WAITS ---- *)
  Lemma blk2_inv_close (E : coPset) (N : namespace) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c1 c2 : nat) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ⊆ E ->
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gL (1/2) c1 -∗ wcur gR (1/2) c2 ={E}=∗
    ∃ (R : list (bv 8)) (sel : list bool) (tm : bool),
      pwc_blk2 k v I R sel c1 c2 tm
      ∗ ⌜R = L \/ R = dg_execR \/ R = alt_forkc⌝
      ∗ ⌜tm = true -> R = alt_forkc⌝.
  Proof using .
    intros HTX HTY HN. iIntros "#Hinv HcL HcR".
    iMod (inv_acc E N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_L gL gR c1 with "HcL Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1' c2' tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    iDestruct (wcur_agree with "HcL HgL") as %<-.
    iDestruct (wcur_agree with "HcR HgR") as %<-.
    (* WHICH SOURCE: the mode's three arms, read as a disjunction.  At
       the UNSET mode the right cursor is still at zero and the family
       does not read [R] at all, so the round normalises it.  And the
       TERMINAL FLAG rides on the mode, so [tm = true] pins the source. *)
    iAssert (⌜(c2 = 0%nat \/ R = L \/ R = dg_execR \/ R = alt_forkc)
              /\ (tm = true -> R = alt_forkc)
              /\ (c2 = 0%nat -> tm = false)⌝)%I
      with "[Hrm]" as %(Hsrc & Htmt & Htm0).
    { rewrite /rmode. iDestruct "Hrm" as (n') "(_ & %Htmb & Harm)".
      assert (Htz : c2 = 0%nat -> tm = false)
        by (intros ->; by rewrite Htmb tmb_zero).
      iDestruct "Harm" as "[%Ha | [[%Ha _] | [%Ha | %Ha]]]"; iPureIntro;
        destruct Ha as [Hn HR]; subst n'; rewrite /tmb in Htmb.
      - split_and!;
          [by left | intro Hx; rewrite Hx in Htmb; discriminate | exact Htz].
      - split_and!; [by right; left
                    | intro Hx; rewrite Hx in Htmb; by destruct c2
                    | exact Htz].
      - split_and!; [by right; right; left
                    | intro Hx; rewrite Hx in Htmb; by destruct c2
                    | exact Htz].
      - split_and!; [by right; right; right | done | exact Htz]. }
    rewrite /wcur.
    iCombine "HcL HgL" as "HLf". iCombine "HcR HgR" as "HRf".
    rewrite ?Qp.half_half.
    iMod ("Hclose" with "[HLf HRf]") as "_".
    { iNext. rewrite /blk2_body. iRight. rewrite /blk2_done /wcur.
      iSplitL "HLf"; [iExists c1 | iExists c2]; by iFrame. }
    iModIntro. destruct Hsrc as [Hc20 | Hor].
    - subst c2. iExists dg_execR, sel, tm.
      iDestruct (pwc_blk2_R_indep k v I R dg_execR sel c1 tm with "Hf")
        as "Hf".
      iFrame "Hf". iPureIntro. split; [by right; left |].
      intro Hx. exfalso. rewrite (Htm0 eq_refl) in Hx. discriminate.
    - iExists R, sel, tm. iFrame "Hf". by iPureIntro.
  Qed.

  (* ...AND THE NON-TERMINAL FORM (lane PIPE-STAGE-4), which is what the
     round's EXIT needs: the boundary credential's third arm is at the
     flag [false], so the round has to show its round is not the runcmd
     child's own panic -- and the only thing that knows is the MODE.  The
     honest premise is therefore the right child's mode half, handed back
     at its exit; see the lane's Findings block. *)
  Lemma blk2_inv_close_nt (E : coPset) (N : namespace) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c1 c2 n : nat) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ⊆ E ->
    n <> 3%nat ->
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gL (1/2) c1 -∗ wcur gR (1/2) c2 -∗ wcur gM (1/2) n ={E}=∗
    ∃ (R : list (bv 8)) (sel : list bool),
      pwc_blk2 k v I R sel c1 c2 false
      ∗ ⌜R = L \/ R = dg_execR⌝ ∗ wcur gM (1/2) n.
  Proof using .
    intros HTX HTY HN Hn3. iIntros "#Hinv HcL HcR HcM".
    iMod (inv_acc E N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_L gL gR c1 with "HcL Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1' c2' tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    iDestruct (wcur_agree with "HcL HgL") as %<-.
    iDestruct (wcur_agree with "HcR HgR") as %<-.
    iDestruct (rmode_flag gM L R c2 n tm YR with "HcM Hrm") as %Htmb.
    assert (Htmf : tm = false)
      by (rewrite Htmb /tmb; destruct n as [| [| [| [| n]]]];
          try reflexivity; by destruct Hn3).
    iAssert ⌜c2 = 0%nat \/ R = L \/ R = dg_execR⌝%I as %Hsrc.
    { destruct (decide (n = 0%nat)) as [-> | Hnz].
      - iDestruct (rmode_zero gM L R c2 tm YR with "HcM Hrm") as %Hc20.
        iPureIntro. by left.
      - iDestruct (rmode_src gM L R c2 n tm YR Hnz with "HcM Hrm") as %HRn.
        iPureIntro. right. subst R.
        destruct n as [| [| [| [| n]]]];
          [ by destruct (Hnz eq_refl) | by left | by right
          | by destruct (Hn3 eq_refl) | by right ]. }
    rewrite Htmf. rewrite /wcur.
    iCombine "HcL HgL" as "HLf". iCombine "HcR HgR" as "HRf".
    rewrite ?Qp.half_half.
    iMod ("Hclose" with "[HLf HRf]") as "_".
    { iNext. rewrite /blk2_body. iRight. rewrite /blk2_done /wcur.
      iSplitL "HLf"; [iExists c1 | iExists c2]; by iFrame. }
    iModIntro. destruct Hsrc as [Hc20 | Hor].
    - subst c2. iExists dg_execR, sel.
      iDestruct (pwc_blk2_R_indep k v I R dg_execR sel c1 false with "Hf")
        as "Hf".
      iFrame "Hf HcM". iPureIntro. by right.
    - iExists R, sel. iFrame "Hf HcM". by iPureIntro.
  Qed.

  (* the chain composes -- [WpUart] names this lemma in a comment but
     does not state it *)
  Lemma pb_out_chain_app (i : uart_id) (k : nat) (bs1 bs2 : list (bv 8))
      (Φ : iProp Σ) :
    out_chain i k (bs1 ++ bs2) Φ = out_chain i k bs1 (out_chain i k bs2 Φ).
  Proof using .
    induction bs1 as [| b bs1 IH]; [reflexivity |].
    cbn [app out_chain]. by rewrite IH.
  Qed.

  (* ================================================================= *)
  (*  S8  THE CONSUMER'S CHAIN: a whole run of the two writers          *)
  (*                                                                   *)
  (*  From the family at any point, ANY interleaving [tail] of the two  *)
  (*  sides' remaining bytes is an [out_chain] -- the alternating run   *)
  (*  and the four one-sided runs are instances.                        *)
  (* ================================================================= *)

  Lemma pblk2_chain (k : nat) (v : era_pins) (I R : list (bv 8))
      (tail sel : list bool) (c1 c2 : nat) (Φ : iProp Σ) :
    (c1 + count_true tail <= length dg_execL)%nat ->
    (c2 + (length tail - count_true tail) <= length R)%nat ->
    (length sel = c1 + c2)%nat -> count_true sel = c1 ->
    Forall nodollar R -> pblk2_wit I R (sel ++ tail) ->
    pblk2_ecl_L -∗ pblk2_ecl_R -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 false -∗
    (pwc_blk2 k v I R (sel ++ tail) (c1 + count_true tail)%nat
       (c2 + (length tail - count_true tail))%nat false -∗ Φ) -∗
    out_chain Uart0 k (both_bytes2 R sel tail) Φ.
  Proof using Hcons.
    revert sel c1 c2 Φ.
    induction tail as [| [|] t IH];
      intros sel c1 c2 Φ H1 H2 Hlen Hcnt HndR Hwit;
      iIntros "#HL #HR #Ht #Hpin Hc HΦ".
    - (* nothing left to write: [sel ++ []] is not CONVERTIBLE to [sel],
         so the empty tail is closed on the continuation's own argument *)
      cbn [both_bytes2 out_chain].
      iApply "HΦ". cbn [count_true length].
      rewrite app_nil_r.
      replace (c1 + 0)%nat with c1 by lia.
      replace (c2 + (0 - 0))%nat with c2 by lia.
      iExact "Hc".
    - (* a LEFT byte, then the rest *)
      cbn [both_bytes2 count_true length] in H1, H2 |- *.
      pose proof (count_true_le t) as Hle.
      assert (Hlt : (c1 < length dg_execL)%nat) by lia.
      destruct (lookup_lt_is_Some_2 dg_execL c1 Hlt) as [b Hb].
      rewrite Hcnt (list_lookup_total_correct dg_execL c1 b Hb).
      cbn [out_chain].
      assert (Hwf' : sel_wf2 R (sel ++ true :: t)).
      { rewrite /sel_wf2 count_true_app length_app Hcnt Hlen.
        cbn [count_true length]. lia. }
      assert (HW1 : pblk2_wit I R (sel ++ [true])).
      { apply (pblk2_wit_mono I R (sel ++ [true]) (sel ++ true :: t));
          [exists t; by rewrite -app_assoc | exact Hwf' | exact Hwit]. }
      iApply (pblk2_step_L k v I R sel c1 c2 b _ Hb
               (pmerge_nodollar sel dg_execL R dg_execL_nodollar HndR) HW1
               with "HL Ht Hpin Hc").
      iIntros "Hc".
      (* the four premises are HOISTED, never spliced as [ltac:] into an
         application the proofmode still has evars in
         (claude-notes/optimization.md, "Inline [ltac:] in argument
         position": re-elaboration against unresolved evars can fail to
         terminate) *)
      assert (HA : (S c1 + count_true t <= length dg_execL)%nat) by lia.
      assert (HB : (c2 + (length t - count_true t) <= length R)%nat) by lia.
      assert (HC : length (sel ++ [true]) = (S c1 + c2)%nat)
        by (rewrite length_app Hlen; cbn [length]; lia).
      assert (HD : count_true (sel ++ [true]) = S c1)
        by (rewrite count_true_app Hcnt; cbn [count_true]; lia).
      assert (HE2 : pblk2_wit I R ((sel ++ [true]) ++ t))
        by (rewrite -app_assoc; exact Hwit).
      iApply (IH (sel ++ [true]) (S c1) c2 Φ HA HB HC HD HndR HE2
             with "HL HR Ht Hpin Hc [HΦ]").
      iIntros "Hc". iApply "HΦ". cbn [count_true length].
      replace (sel ++ true :: t) with ((sel ++ [true]) ++ t)
        by (by rewrite -app_assoc).
      replace (c1 + S (count_true t))%nat with (S c1 + count_true t)%nat
        by lia.
      replace (c2 + (S (length t) - S (count_true t)))%nat
        with (c2 + (length t - count_true t))%nat by lia.
      iExact "Hc".
    - (* a RIGHT byte, then the rest *)
      cbn [both_bytes2 count_true length] in H1, H2 |- *.
      pose proof (count_true_le t) as Hle.
      assert (Hlt : (c2 < length R)%nat) by lia.
      destruct (lookup_lt_is_Some_2 R c2 Hlt) as [b Hb].
      replace (length sel - count_true sel)%nat with c2 by lia.
      rewrite (list_lookup_total_correct R c2 b Hb).
      cbn [out_chain].
      assert (Hwf' : sel_wf2 R (sel ++ false :: t)).
      { rewrite /sel_wf2 count_true_app length_app Hcnt Hlen.
        cbn [count_true length]. lia. }
      assert (HW1 : pblk2_wit I R (sel ++ [false])).
      { apply (pblk2_wit_mono I R (sel ++ [false]) (sel ++ false :: t));
          [exists t; by rewrite -app_assoc | exact Hwf' | exact Hwit]. }
      iApply (pblk2_step_R k v I R sel c1 c2 b _ Hb HndR HW1
               with "HR Ht Hpin Hc").
      iIntros "Hc".
      assert (HA : (c1 + count_true t <= length dg_execL)%nat) by lia.
      assert (HB : (S c2 + (length t - count_true t) <= length R)%nat) by lia.
      assert (HC : length (sel ++ [false]) = (c1 + S c2)%nat)
        by (rewrite length_app Hlen; cbn [length]; lia).
      assert (HD : count_true (sel ++ [false]) = c1)
        by (rewrite count_true_app Hcnt; cbn [count_true]; lia).
      assert (HE2 : pblk2_wit I R ((sel ++ [false]) ++ t))
        by (rewrite -app_assoc; exact Hwit).
      iApply (IH (sel ++ [false]) c1 (S c2) Φ HA HB HC HD HndR HE2
             with "HL HR Ht Hpin Hc [HΦ]").
      iIntros "Hc". iApply "HΦ". cbn [count_true length].
      replace (sel ++ false :: t) with ((sel ++ [false]) ++ t)
        by (by rewrite -app_assoc).
      replace (c2 + (S (length t) - count_true t))%nat
        with (S c2 + (length t - count_true t))%nat by lia.
      iExact "Hc".
  Qed.

  (* ================================================================= *)
  (*  S9  THE ROUND'S LEND, END TO END                                  *)
  (*                                                                   *)
  (*  What lane SH-PIPE-ROUND-3 lends at the two forks and redeems      *)
  (*  after the two waits, on EVERY arm of the pipeline round: from the *)
  (*  round's owed block at an [LPipe] line ([pwc_lend], i.e.           *)
  (*  [lk_lcred]'s owed arm) and any interleaving of the two children's *)
  (*  bytes, the console shows exactly those bytes and the round ends   *)
  (*  at the shared prompt credential with its code filed.              *)
  (*                                                                   *)
  (*  This REPLACES the lane's original deliverable [pipe_both_law]:    *)
  (*  per the coordinator's amendment there is no [PBoth]-only law, and *)
  (*  the round lane states none.                                       *)
  (* ================================================================= *)

  Definition pipe_round_lend (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) : iProp Σ :=
    (∀ Φ : iProp Σ,
       pwc_lend g k v I -∗ (pwc_sp_t g k v I -∗ Φ) -∗
       out_chain Uart0 k (pend2 R sel ++ [u_prompt !!! 0%nat]) Φ)%I.

  Lemma pipe_round_lend_holds (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (a : nat) :
    pboth_line I ->
    (count_true sel <= length dg_execL)%nat ->
    (length sel - count_true sel <= length R)%nat ->
    Forall nodollar R ->
    sel <> [] ->
    pblk2_code I R sel a ->
    pblk2_ecl -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pipe_round_lend k v I R sel.
  Proof using Hcons.
    intros Hline H1 H2 HndR Hnn Hcode.
    iIntros "#Hecl #Ht #Hpin" (Φ) "Hlend HΦ".
    iDestruct (pblk2_ecl_l with "Hecl") as "#HL".
    iDestruct (pblk2_ecl_r with "Hecl") as "#HR".
    iDestruct (pblk2_ecl_f with "Hecl") as "#HF".
    iDestruct (pwc_blk2_of_lend k v I R false Hline with "Hlend") as "Hc".
    assert (Hb : pend2 R sel = both_bytes2 R [] sel).
    { rewrite -{1}(app_nil_l sel) (both_bytes2_app R [] sel);
        [by rewrite (pend2_nil R)
         | rewrite app_nil_l /sel_wf2; split; lia]. }
    rewrite Hb (pb_out_chain_app Uart0 k (both_bytes2 R [] sel)
                  [u_prompt !!! 0%nat] Φ).
    assert (HA : (0 + count_true sel <= length dg_execL)%nat) by lia.
    assert (HB : (0 + (length sel - count_true sel) <= length R)%nat) by lia.
    assert (HW : pblk2_wit I R ([] ++ sel))
      by (rewrite app_nil_l; exact (pblk2_wit_of_code I R sel a Hcode)).
    iApply (pblk2_chain k v I R sel [] 0%nat 0%nat _ HA HB eq_refl eq_refl
              HndR HW with "HL HR Ht Hpin Hc").
    iIntros "Hc". cbn [out_chain].
    rewrite app_nil_l !Nat.add_0_l.
    iApply (pblk2_exit k v I R sel (count_true sel)
              (length sel - count_true sel)%nat a (u_prompt !!! 0%nat) Φ
              Hcode Hnn eq_refl with "HF Ht Hpin Hc HΦ").
  Qed.

  (* ================================================================= *)
  (*  S10  (R1)  THE LOOP'S BOUNDARY CREDENTIAL, WIDENED                *)
  (*                                                                   *)
  (*  Lane SH-PIPE-ROUND-3 refuted the round's exit: [pblk2_exit] files *)
  (*  the round's code at the PROMPT'S FIRST BYTE, which sh's MAIN LOOP *)
  (*  writes one process after the runcmd child has exited, and         *)
  (*  [PipeLinksLine.pwc_line] -- the credential the child may hand     *)
  (*  back -- has no state carrying an unfiled block                    *)
  (*  ([UShPipeExit.pipe_blk2_not_line], [pipe_blk2_not_blk0]).         *)
  (*  Design section 4.3f (R1): give it one.                            *)
  (*                                                                   *)
  (*  THE EXIT IS THEREFORE A LINK AND NOT AN [Hcons] LEMMA.  The       *)
  (*  record field that consumes [lk_line] ([lk_prompt_dollar_line])    *)
  (*  takes no [Hcons], so the filing step has to arrive through        *)
  (*  [lk_links] -- which is why [PipeLinks.pipe_link_file] is the      *)
  (*  bundle's seventh leaf.                                            *)
  (* ================================================================= *)

  (* [pblk2_exit] at the LINK instead of the claim step: the same proof
     with [Hcons] moved into the bundle. *)
  Lemma pblk2_exit_lk (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (a : nat) (b : bv 8) (Φ : iProp Σ) :
    pblk2_code I R sel a ->
    sel <> [] ->
    b = u_prompt !!! 0%nat ->
    PipeLinks.pipe_link_file g -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 false -∗
    (pwc_sp_t g k v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using .
    intros Hcode Hnn Hb. iIntros "#HF #Ht #Hpin Hc HΦ".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite pwc_sp_t_view. by iRight. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & _).
    pose proof Hcode as (Hok & Hpan & Hfk & Hcont).
    rewrite /pline_at in Hok, Hpan, Hcont.
    assert (Hpapr : papr I a) by exact (pblk2_code_papr I R sel a Hcode).
    assert (Hab : length (pab I a) = S (S (c1 + c2))%nat)
      by exact (pblk2_code_len I R sel a c1 c2 Hwf Hlen Hcode).
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    rewrite /pblk_led. iDestruct "Hled" as "[%Hnil | Hled]";
      [by destruct (Hnn Hnil) |].
    iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
    iApply ("HF" $! k v w gb P (nlines I - 1)%nat a b (pend2 R sel)
              ps cs I Φ
              with "[//] [//] [//] [//] [//] [//] [//] [//] [//] [//] [//]
                    Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE [HΦ]").
    { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
        by (rewrite Hlb; lia). iExact "Htn". }
    iIntros "Hret". iApply "HΦ".
    iDestruct "Hret" as "[(Htn & _ & #Hcs' & _) | #HT]";
      last by (rewrite pwc_sp_t_view; iRight).
    iApply (pwc_blk_sp g k v I a Hpapr).
    rewrite pwc_blk_view Hab. iLeft. iExists ps, cs, P.
    replace (S (S (c1 + c2)) - 1)%nat with (S (c1 + c2))%nat by lia.
    cbn [blkcs_p].
    replace (P + S (c1 + c2))%nat with (S (P + length (pend2 R sel)))%nat
      by (rewrite Hlb; lia).
    iFrame "Htn Hps HE Hcs'". iPureIntro.
    split; [exact (wr_blk2_p_blk ps cs I P R sel c1 c2 Hw) | exact Htl].
  Qed.

  (* THE WIDENED CREDENTIAL.  [PipeLinksLine.pwc_line]'s two arms, and a
     THIRD: the round's block COMPLETE but not yet filed. *)
  (* THE PER-SHAPE LINE ARM ([GenLinksLine]'s [X] at the pipeline): the
     terminal round's block, written by two processes at the two cursors
     and not yet filed *)
  Definition pipe_X (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ (R : list (bv 8)) (sel : list bool) (c1 c2 a : nat),
       ⌜pblk2_code I R sel a⌝ ∗ ⌜sel <> []⌝
       ∗ pwc_blk2 k v I R sel c1 c2 false)%I.

  Global Instance pipe_X_timeless k v I : Timeless (pipe_X k v I).
  Proof using .
    rewrite /pipe_X.
    apply bi.exist_timeless; intro R.
    apply bi.exist_timeless; intro sel.
    apply bi.exist_timeless; intro c1.
    apply bi.exist_timeless; intro c2.
    apply bi.exist_timeless; intro a.
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply bi.pure_timeless | apply pwc_blk2_timeless].
  Qed.

  (* THE RECORD'S LINE CREDENTIAL, WIDENED (SH-PIPE-ROUND-4): the generic
     line at the pipeline's parameters with this arm -- an abbreviation,
     [pwc_line2 g] after the section -- and the pipeline's reading of it *)
  Local Notation pwc_line2 := (gwc_line pipe_lm (pipe_params g) pipe_X).
  Local Notation pwc_lpr2 := (gwc_lpr pipe_lm (pipe_params g) pipe_X).

  Lemma pwc_line2_view k v I :
    pwc_line2 k v I ⊣⊢
    (pwc_pro g k v I
     ∨ (∃ a : nat, ⌜papr I a⌝ ∗ pwc_post g k v I a)
     ∨ pipe_X k v I)%I.
  Proof using .
    rewrite /gwc_line. apply bi.equiv_entails; split.
    - iIntros "[H | [H | H]]"; [by iLeft | | by iRight; iRight].
      iDestruct "H" as (a) "[%Ha H]". destruct Ha as (H1 & H2 & H3).
      assert (Ha : papr I a) by exact (conj (H1 tt) (conj H2 H3)).
      iRight. iLeft. iExists a.
      iSplitR; [by iPureIntro |]. rewrite (pwc_post_gen g k v I a Ha). iExact "H".
    - iIntros "[H | [H | H]]"; [by iLeft | | by iRight; iRight].
      iDestruct "H" as (a) "[%Ha H]". iRight. iLeft. iExists a.
      iSplitR; [iPureIntro; destruct Ha as (H1 & H2 & H3);
                exact (conj (fun _ => H1) (conj H2 H3)) |].
      rewrite (pwc_post_gen g k v I a Ha). iExact "H".
  Qed.

  Lemma pwc_line2_timeless k v I : Timeless (pwc_line2 k v I).
  Proof using .
    apply (gwc_line_timeless pipe_lm (pipe_params g) pipe_X pipe_X_timeless).
  Qed.

  Lemma pwc_line2_of_line k v I : pwc_line g k v I -∗ pwc_line2 k v I.
  Proof using .
    rewrite /pwc_line pwc_line2_view. iIntros "[H | H]"; [by iLeft |].
    iRight. by iLeft.
  Qed.

  Lemma pwc_line2_taint k v I : PT -∗ pwc_line2 k v I.
  Proof using .
    iIntros "HT". iApply pwc_line2_of_line. by iApply pwc_line_taint.
  Qed.

  Lemma pwc_line2_of_pro k v I : pwc_pro g k v I -∗ pwc_line2 k v I.
  Proof using . rewrite pwc_line2_view. iIntros "H". by iLeft. Qed.

  Lemma pwc_line2_of_post k v I a :
    papr I a -> pwc_post g k v I a -∗ pwc_line2 k v I.
  Proof using .
    intros Ha. iIntros "H". iApply pwc_line2_of_line.
    iApply (pwc_line_of_post g k v I a Ha with "H").
  Qed.

  Lemma pwc_line2_of_blk0 k v I a :
    pwc_blk g k v I a 0%nat -∗ pwc_line2 k v I.
  Proof using .
    iIntros "H". iApply pwc_line2_of_line.
    iApply (pwc_line_of_blk0 g k v I a with "H").
  Qed.

  (* ...AND THE THIRD ARM'S OWN CONSTRUCTOR: what the round hands back. *)
  Lemma pwc_line2_of_blk2 k v I R sel c1 c2 a :
    pblk2_code I R sel a -> sel <> [] ->
    pwc_blk2 k v I R sel c1 c2 false -∗ pwc_line2 k v I.
  Proof using .
    intros Hcode Hnn. iIntros "H". rewrite pwc_line2_view. iRight. iRight.
    rewrite /pipe_X. iExists R, sel, c1, c2, a. by iFrame "H".
  Qed.

  (* THE PROMPT STEP AT THE THIRD ARM: the round's exit, which writes
     the same byte into the same [pwc_sp_t] as the one-writer arms --
     [GenLinksLine]'s [X_dollar], so the widened credential's prompt
     step is the generic [gprompt_dollar_line]. *)
  Lemma pipe_X_dollar (k : nat) (v : era_pins) (I : list (bv 8)) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ PipeLinks.pipe_links g -∗ pipe_X k v I -∗
    (pwc_sp_t g k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hx HΦ".
    iDestruct "Hx" as (R sel c1 c2 a) "(%Hcode & %Hnn & Hc)".
    iDestruct (PipeLinks.pipe_links_file with "Hlk") as "#HF".
    iDestruct (PipeLinks.pipe_links_taint with "Hlk") as "#Ht".
    iApply (pblk2_exit_lk k v I R sel c1 c2 a b Φ Hcode Hnn Hb
              with "HF Ht Hpin Hc HΦ").
  Qed.

  Lemma pprompt_dollar_line2 (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ PipeLinks.pipe_links g -∗ pwc_line2 k v I -∗
    (pwc_sp_t g k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    exact (gprompt_dollar_line pipe_lm (pipe_params g) pipe_X (pipe_links g)
             (pipe_links_persistent g) (pipe_links_gl g) pipe_X_dollar k v I b Φ).
  Qed.

  Lemma pwc_ban_done_line2 k v I :
    pwc_ban g k v I (length u_banner) -∗ pwc_line2 k v I.
  Proof using .
    apply (gwc_ban_done_line pipe_lm (pipe_params g) pipe_X).
  Qed.

  (* THE LOOP'S FAMILY AT THE WIDENED BOUNDARY: the generic [gwc_lpr]
     with [pwc_line2] at 0; the other three slots are the one-writer
     families, so the record's [lk_lpr_1]/[lk_lpr_2]/[lk_lpr_S3] stay
     [eq_refl]. *)
  Lemma pwc_lpr2_timeless k v I p : Timeless (pwc_lpr2 k v I p).
  Proof using .
    apply (gwc_lpr_timeless pipe_lm (pipe_params g) pipe_X pipe_X_timeless).
  Qed.

  (* ================================================================= *)
  (*  S11  THE TERMINAL ROUND, END TO END (lane PIPE-STAGE-3)           *)
  (*                                                                   *)
  (*  The two CHAINS at mode fork -- the right source [alt_forkc] (the  *)
  (*  runcmd child's `fork\n' and then, at the same cursor and one      *)
  (*  process later, sh's MAIN LOOP's `$ ') and the left source         *)
  (*  [dg_execL] (the STRAY: the first child, whose own [exec] failed   *)
  (*  and which nobody waits for) -- and the second shape of the        *)
  (*  round's boundary credential.                                     *)
  (* ================================================================= *)

  Lemma pblk2_cterm_chain (N : namespace) (k : nat) (v : era_pins)
      (I L : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ)
      (bs : list (bv 8)) (c2 : nat) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    drop c2 alt_forkc = bs ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    pblk2_ecl_R_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gR (1/2) c2 -∗ wcur gM (1/2) 3%nat -∗
    (wcur gR (1/2) (c2 + length bs)%nat -∗ wcur gM (1/2) 3%nat -∗ Φ) -∗
    out_chain Uart0 k bs Φ.
  Proof using Hcons.
    intros HTX HTY Hns. revert c2 Φ.
    induction bs as [| b bs IH]; intros c2 Φ Hdrop Hwitt;
      iIntros "#HR #Ht #Hpin #Hinv HcR HcM HΦ".
    - cbn [out_chain]. rewrite Nat.add_0_r.
      by iApply ("HΦ" with "HcR HcM").
    - assert (Hb : alt_forkc !! c2 = Some b).
      { rewrite -(Nat.add_0_r c2) -lookup_drop Hdrop. reflexivity. }
      assert (Hdrop' : drop (S c2) alt_forkc = bs).
      { rewrite -(Nat.add_1_r c2) -drop_drop Hdrop. reflexivity. }
      cbn [out_chain].
      iApply (pblk2_cstep_R_t N k v I L gL gR gM XL YR c2 b _
                HTX HTY Hns Hb Hwitt with "HR Ht Hpin Hinv HcR HcM").
      iIntros "HcR HcM _".
      iApply (IH (S c2) Φ Hdrop' Hwitt with "HR Ht Hpin Hinv HcR HcM [HΦ]").
      iIntros "HcR HcM". iApply ("HΦ" with "[HcR] HcM").
      replace (c2 + length (b :: bs))%nat with (S c2 + length bs)%nat
        by (cbn [length]; lia).
      iExact "HcR".
  Qed.

  (* A NON-EMPTY terminal chain HANDS THE FROZEN RESOLUTION OUT (lane
     PIPE-STAGE-4): its first byte is the round's terminal fire, and that
     is where [PipeOut.pecl] persists its resolution. *)
  Lemma pblk2_cterm_chain_fz (N : namespace) (k : nat) (v : era_pins)
      (I L : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ)
      (bs : list (bv 8)) (c2 : nat) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    drop c2 alt_forkc = bs ->
    bs <> [] ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    pblk2_ecl_R_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gR (1/2) c2 -∗ wcur gM (1/2) 3%nat -∗
    (wcur gR (1/2) (c2 + length bs)%nat -∗ wcur gM (1/2) 3%nat -∗
     (cs_frozen_at v (nlines I - 1)%nat ∨ PT) -∗ Φ) -∗
    out_chain Uart0 k bs Φ.
  Proof using Hcons.
    intros HTX HTY Hns Hdrop Hne Hwitt.
    destruct bs as [| b bs]; [by destruct (Hne eq_refl) |].
    iIntros "#HR #Ht #Hpin #Hinv HcR HcM HΦ".
    assert (Hb : alt_forkc !! c2 = Some b).
    { rewrite -(Nat.add_0_r c2) -lookup_drop Hdrop. reflexivity. }
    assert (Hdrop' : drop (S c2) alt_forkc = bs).
    { rewrite -(Nat.add_1_r c2) -drop_drop Hdrop. reflexivity. }
    cbn [out_chain].
    iApply (pblk2_cstep_R_t N k v I L gL gR gM XL YR c2 b _
              HTX HTY Hns Hb Hwitt with "HR Ht Hpin Hinv HcR HcM").
    iIntros "HcR HcM #Hfz".
    iApply (pblk2_cterm_chain N k v I L gL gR gM XL YR bs (S c2) Φ
              HTX HTY Hns Hdrop' Hwitt with "HR Ht Hpin Hinv HcR HcM [HΦ]").
    iIntros "HcR HcM". iApply ("HΦ" with "[HcR] HcM Hfz").
    replace (c2 + length (b :: bs))%nat with (S c2 + length bs)%nat
      by (cbn [length]; lia).
    iExact "HcR".
  Qed.

  Lemma pblk2_cstray_chain (N : namespace) (Eex : coPset) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (bs : list (bv 8)) (c1 : nat) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    drop c1 dg_execL = bs ->
    (forall sel : list bool,
       sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel) ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    □ (XL -∗ YR ={Eex}=∗ False) -∗
    pblk2_ecl_L -∗ pblk2_ecl_L_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I L gL gR gM XL YR -∗ wcur gL (1/2) c1 -∗
    (⌜c1 = 0%nat⌝ -∗ XL) -∗
    (wcur gL (1/2) (c1 + length bs)%nat -∗ Φ) -∗
    out_chain Uart0 k bs Φ.
  Proof using Hcons.
    intros HTX HTY Hns HEx. revert c1 Φ.
    induction bs as [| b bs IH]; intros c1 Φ Hdrop Hwit Hwitt;
      iIntros "#Hex #HL #HLt #Ht #Hpin #Hinv HcL HXw HΦ".
    - cbn [out_chain]. rewrite Nat.add_0_r. by iApply ("HΦ" with "HcL").
    - assert (Hb : dg_execL !! c1 = Some b).
      { rewrite -(Nat.add_0_r c1) -lookup_drop Hdrop. reflexivity. }
      assert (Hdrop' : drop (S c1) dg_execL = bs).
      { rewrite -(Nat.add_1_r c1) -drop_drop Hdrop. reflexivity. }
      cbn [out_chain].
      iApply (pblk2_cstep_L N Eex k v I L gL gR gM XL YR c1 b _
                HTX HTY Hns HEx Hb Hwit Hwitt
                with "Hex HL HLt Ht Hpin Hinv HcL HXw").
      iIntros "HcL".
      iApply (IH (S c1) Φ Hdrop' Hwit Hwitt
                with "Hex HL HLt Ht Hpin Hinv HcL [] [HΦ]").
      { iIntros "%Hq". discriminate Hq. }
      iIntros "HcL". iApply ("HΦ" with "[HcL]").
      replace (c1 + length (b :: bs))%nat with (S c1 + length bs)%nat
        by (cbn [length]; lia).
      iExact "HcL".
  Qed.

  (* ---- THE SECOND SHAPE OF THE ROUND'S BOUNDARY CREDENTIAL (design
     section 4.3h): what the runcmd child that PANICKED at [fork1] #2
     hands back when it exits.  It exits WITHOUT the family -- the stray
     is still holding [wcur gL (1/2)] and may write at any later time --
     so what it hands back is the family's INVARIANT, the right cursor at
     position 5 (the five bytes of `fork\n' it wrote itself) and the mode
     half at [3].  See the lane's Findings block for why this is NOT an
     arm of [pwc_line2]. ---- *)
  Definition pwc_fork_exit (N : namespace) (k : nat) (v : era_pins)
      (I L : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ)
      (c2 : nat) : iProp Σ :=
    (blk2_inv N k v I L gL gR gM XL YR
     ∗ wcur gR (1/2) c2 ∗ wcur gM (1/2) 3%nat
     ∗ (cs_frozen_at v (nlines I - 1)%nat ∨ PT))%I.

  (* ---- THE MAIN LOOP'S PROMPT AT THAT SHAPE: TWO RIGHT STEPS, at
     positions 5 and 6 of [alt_forkc], and NO FILING.  The round stays
     open for ever; D4 refutes the next input, so the credential only has
     to be consistent -- it is never spent. ---- *)
  Lemma pprompt_dollar_fork (N : namespace) (k : nat) (v : era_pins)
      (I L : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ)
      (b : bv 8) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    b = u_prompt !!! 0%nat ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    pblk2_ecl_R_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_fork_exit N k v I L gL gR gM XL YR 5%nat -∗
    (pwc_fork_exit N k v I L gL gR gM XL YR 6%nat -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros HTX HTY Hns Hb Hwitt. subst b.
    iIntros "#HR #Ht #Hpin (#Hinv & HcR & HcM & #Hfz0) HΦ".
    iApply (pblk2_cstep_R_t N k v I L gL gR gM XL YR 5%nat _ _
              HTX HTY Hns alt_forkc_dollar Hwitt
              with "HR Ht Hpin Hinv HcR HcM").
    iIntros "HcR HcM #Hfz". iApply "HΦ". rewrite /pwc_fork_exit.
    by iFrame "Hinv HcR HcM Hfz".
  Qed.

  Lemma pprompt_space_fork (N : namespace) (k : nat) (v : era_pins)
      (I L : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ)
      (b : bv 8) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    b = u_prompt !!! 1%nat ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    pblk2_ecl_R_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_fork_exit N k v I L gL gR gM XL YR 6%nat -∗
    (pwc_fork_exit N k v I L gL gR gM XL YR 7%nat -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros HTX HTY Hns Hb Hwitt. subst b.
    iIntros "#HR #Ht #Hpin (#Hinv & HcR & HcM & #Hfz0) HΦ".
    iApply (pblk2_cstep_R_t N k v I L gL gR gM XL YR 6%nat _ _
              HTX HTY Hns alt_forkc_space Hwitt
              with "HR Ht Hpin Hinv HcR HcM").
    iIntros "HcR HcM #Hfz". iApply "HΦ". rewrite /pwc_fork_exit.
    by iFrame "Hinv HcR HcM Hfz".
  Qed.

  (* ---- (ITEM 4) THE FIRST FORK'S PANIC: the same family at mode fork
     with the LEFT cursor never lent.  No stray exists, every byte of the
     block is a right byte, the selector is all-[false] and the block IS
     [alt_forkc] ([PipeDisc.pcont_forkS_old]).  This is the corollary the
     round (lane ROUND-5) uses at [fork1] #1. ---- *)
  Lemma pblk2_fork1_chain (N : namespace) (k : nat) (v : era_pins)
      (I L : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ)
      (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    (forall sel : list bool,
       sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel) ->
    pblk2_ecl_R_t -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I L gL gR gM XL YR -∗
    wcur gR (1/2) 0%nat -∗ wcur gM (1/2) 3%nat -∗
    (wcur gR (1/2) (length alt_forkc) -∗ wcur gM (1/2) 3%nat -∗
     (cs_frozen_at v (nlines I - 1)%nat ∨ PT) -∗ Φ) -∗
    out_chain Uart0 k alt_forkc Φ.
  Proof using Hcons.
    intros HTX HTY Hns Hwitt.
    assert (Hne : alt_forkc <> []).
    { destruct alt_forkc_cons as (b0 & bs0 & Hac). rewrite Hac. done. }
    assert (Hd0 : drop 0%nat alt_forkc = alt_forkc) by apply drop_0.
    iIntros "#HR #Ht #Hpin #Hinv HcR HcM HΦ".
    iApply (pblk2_cterm_chain_fz N k v I L gL gR gM XL YR alt_forkc 0%nat Φ
              HTX HTY Hns Hd0 Hne Hwitt
              with "HR Ht Hpin Hinv HcR HcM [HΦ]").
    iIntros "HcR HcM #Hfz". iApply ("HΦ" with "[HcR] HcM Hfz").
    rewrite Nat.add_0_l. iExact "HcR".
  Qed.

  (* ================================================================= *)
  (*  S12  THE READ AFTER A TERMINAL PROMPT REFUTES A LATER LINE, PURELY *)
  (*       (lane PIPE-STAGE-4; design SS4.3m, the fourth bullet)          *)
  (*                                                                   *)
  (*  This is route (gamma)'s lemma AT ITS TRUE SITE.  The read residue  *)
  (*  [PipeLinksLine.pwc_rres] at a line DELIVERED AFTER the terminal    *)
  (*  round carries [cs_lb v cs0] with                                   *)
  (*  [nlines (removelast (I ++ l ++ [wl_nl])) <= length cs0], i.e.      *)
  (*  [length cs0 >= nlines I]; the terminal writer carries the FROZEN   *)
  (*  resolution at length [nlines I - 1].  A lower bound of a frozen    *)
  (*  authority is a PREFIX of it, so the two cannot both hold -- and    *)
  (*  this is a PLAIN entailment, under no mask and with no claim in the *)
  (*  room, which is exactly what [UkSh.ush_wc_read]'s shape allows.     *)
  (*  (SH-PIPE-ROUND-5 parts 2-4 measured three routes to this leaf; the *)
  (*  reading the read site can hold had to be NON-MONOTONE, and this is *)
  (*  the only one there is.)                                           *)
  (* ================================================================= *)
  Lemma pterm_read_absurd (v : era_pins) (I l : list (bv 8)) :
    (1 <= nlines I)%nat ->
    cs_frozen_at v (nlines I - 1)%nat -∗
    pwc_rres v (I ++ l ++ [wl_nl]) -∗ False.
  Proof using .
    intros Hpos. iIntros "#Hfz Hres". rewrite /pwc_rres.
    iDestruct "Hres" as (ps0 cs0) "(%Hrd & _ & _ & #Hcs0)".
    destruct Hrd as (_ & _ & _ & Hle).
    assert (Hrl : removelast (I ++ l ++ [wl_nl]) = (I ++ l)%list).
    { rewrite app_assoc. apply epu_removelast_snoc. }
    rewrite Hrl in Hle.
    pose proof (nlines_app_le I l) as Hmono.
    iApply (cs_frozen_at_lb_absurd v (nlines I - 1)%nat cs0
              ltac:(lia) with "Hfz Hcs0").
  Qed.

  (* ...and at the shape the runcmd child's exit payload actually has *)
  Lemma pterm_fork_exit_read (N : namespace) (k : nat) (v : era_pins)
      (I L l : list (bv 8)) (gL gR gM : gname) (XL YR : iProp Σ)
      (c2 : nat) :
    (1 <= nlines I)%nat ->
    pwc_fork_exit N k v I L gL gR gM XL YR c2 -∗
    pwc_rres v (I ++ l ++ [wl_nl]) -∗ PT.
  Proof using .
    intros Hpos. iIntros "(_ & _ & _ & [#Hfz | #HT]) Hres"; [| iExact "HT"].
    iExFalso.
    iApply (pterm_read_absurd v I l Hpos with "Hfz Hres").
  Qed.

  (* ...AND THE ONE PREMISE IT ASKS FOR IS INSIDE THE SHAPE.  A terminal
     round HAS a line ([wr_blk2_p]'s [I <> []] and [rest_of I = []]), and
     the family's invariant is where that fact lives; the right cursor
     half refutes the DONE arm, so the shape can always read it back --
     at a fancy update, which is what [UkSh.ush_wc_read] is since
     SH-PIPE-ROUND-5 part 3. *)
  Lemma pwc_fork_exit_nlines (E : coPset) (N : namespace) (k : nat)
      (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c2 : nat) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ⊆ E ->
    pwc_fork_exit N k v I L gL gR gM XL YR c2 ={E}=∗
    pwc_fork_exit N k v I L gL gR gM XL YR c2
    ∗ (⌜(1 <= nlines I)%nat⌝ ∨ PT).
  Proof using .
    intros HTX HTY HN. iIntros "(#Hinv & HcR & HcM & #Hfz)".
    iMod (inv_acc E N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blk2_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blk2_done_not_R gL gR c2 with "HcR Hdone") as %[]. }
    iDestruct "Hfam" as (R sel c1 c2' tm) "(Hf & HgL & HgR & Hxl & Hrm)".
    iAssert (⌜(1 <= nlines I)%nat⌝ ∨ PT)%I as "#Hn".
    { rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]";
        [| by iRight].
      iDestruct "Hx" as (ps cs P) "(%Hw & _)".
      iLeft. iPureIntro.
      destruct Hw as (Hne & Hr & _).
      exact (nlines_pos_of_rest_nil I Hne Hr). }
    iMod ("Hclose" with "[Hf HgL HgR Hxl Hrm]") as "_".
    { iNext. rewrite /blk2_body. iLeft. iExists R, sel, c1, c2', tm.
      by iFrame "Hf HgL HgR Hxl Hrm". }
    iModIntro. iFrame "Hn". rewrite /pwc_fork_exit.
    by iFrame "Hinv HcR HcM Hfz".
  Qed.

  (* THE WHOLE OBLIGATION, at one fancy update: design SS4.3i's DIRTY
     CREDENTIAL, i.e. SH-PIPE-ROUND-5 part 2's [pterm_read_law] once the
     shape carries the frozen resolution. *)
  Lemma pterm_fork_exit_read_fupd (E : coPset) (N : namespace) (k : nat)
      (v : era_pins) (I L l : list (bv 8)) (gL gR gM : gname)
      (XL YR : iProp Σ) (c2 : nat) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ⊆ E ->
    pwc_fork_exit N k v I L gL gR gM XL YR c2 -∗
    pwc_rres v (I ++ l ++ [wl_nl]) ={E}=∗
    pwc_fork_exit N k v I L gL gR gM XL YR c2 ∗ PT.
  Proof using .
    intros HTX HTY HN. iIntros "Hfe #Hres".
    iMod (pwc_fork_exit_nlines E N k v I L gL gR gM XL YR c2 HTX HTY HN
            with "Hfe") as "[Hfe [%Hpos | #HT]]"; last by iFrame "Hfe HT".
    iAssert PT as "#HT".
    { iApply (pterm_fork_exit_read N k v I L l gL gR gM XL YR c2 Hpos
                with "Hfe Hres"). }
    iModIntro. by iFrame "Hfe HT".
  Qed.

  (* ---- (ITEM 5) THE TEST: [fork1] #2 fails; the runcmd child prints
     `fork\n' through the family and exits with the second shape; sh's
     main loop prints `$ '; the STRAY prints its whole diagnostic after
     that.  The claim admits every byte of
     [alt_forkc ++ dg_execL] and the pure reading of the merged block is
     [PForkS sel_term] ([pcont_sel_term], [palt_ok_sel_term]). ---- *)
  Lemma pterm_round_test (E : coPset) (N : namespace) (Eex : coPset)
      (k : nat) (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (XL YR : iProp Σ) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    (↑N : coPset) ⊆ E ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    pline_at I = LPipe ws ->
    (forall sel : list bool,
       sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel) ->
    □ (XL -∗ YR ={Eex}=∗ False) -∗
    pblk2_ecl_L -∗ pblk2_ecl_L_t -∗ pblk2_ecl_R_t -∗
    pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_lend g k v I -∗ XL -∗
    (∀ gL gR gM : gname,
       wcur gL (1/2) (length dg_execL) -∗
       wcur gR (1/2) (length alt_forkc) -∗ wcur gM (1/2) 3%nat -∗
       (cs_frozen_at v (nlines I - 1)%nat ∨ PT) -∗ Φ) ={E}=∗
      out_chain Uart0 k (alt_forkc ++ dg_execL) Φ.
  Proof using Hcons.
    intros HTX HTY Hns HNE HEx Hline Hwit.
    assert (Hbl : pboth_line I) by (exists ws; exact Hline).
    assert (Hwitt : forall sel : list bool,
               sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel).
    { intros sel Hs. exact (pblk2_wit_t_forkc I ws sel Hline Hs). }
    iIntros "#Hex #HL #HLt #HRt #Ht #Hpin Hlend HXL HΦ".
    iMod (blk2_inv_alloc E N k v I L XL YR Hbl with "Hlend")
      as (gL gR gM) "(#Hinv & HcL & HcR & HcM)".
    iMod (blk2_mode_fire E N k v I L gL gR gM XL YR 3%nat HTX HTY HNE
            ltac:(by right; right) with "Hinv HcM HcR []") as "[HcM HcR]".
    { iIntros "%Hq". discriminate Hq. }
    iModIntro.
    rewrite (pb_out_chain_app Uart0 k alt_forkc dg_execL Φ).
    iApply (pblk2_fork1_chain N k v I L gL gR gM XL YR _
              HTX HTY Hns Hwitt with "HRt Ht Hpin Hinv HcR HcM").
    iIntros "HcR HcM #Hfz".
    iApply (pblk2_cstray_chain N Eex k v I L gL gR gM XL YR dg_execL 0%nat Φ
              HTX HTY Hns HEx ltac:(reflexivity) Hwit Hwitt
              with "Hex HL HLt Ht Hpin Hinv HcL [HXL] [HΦ HcR HcM]").
    { by iIntros "_". }
    iIntros "HcL". iApply ("HΦ" $! gL gR gM with "[HcL] HcR HcM Hfz").
    rewrite Nat.add_0_l. iExact "HcL".
  Qed.

  (* ---- ...AND THE SAME TEST WITH THE READ AT ITS END (lane
     PIPE-STAGE-4): after the terminal round's whole wire has gone out
     through the CLAIM, what the round's writers hold REFUTES the read
     residue of ANY later delivered line -- purely, with no mask and no
     claim in the room.  This is the end-to-end anti-vacuity check for
     SS4.3m's fourth bullet: the credential the test starts from is
     [pwc_lend], the one sh's round lends, and every byte goes through
     [PipeOut.pecl]. ---- *)
  Lemma pterm_round_read_test (E : coPset) (N : namespace) (Eex : coPset)
      (k : nat) (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (XL YR : iProp Σ) (Φ : iProp Σ) :
    Timeless XL -> Timeless YR ->
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    (↑N : coPset) ⊆ E ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    pline_at I = LPipe ws ->
    (1 <= nlines I)%nat ->
    (forall sel : list bool,
       sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel) ->
    □ (XL -∗ YR ={Eex}=∗ False) -∗
    pblk2_ecl_L -∗ pblk2_ecl_L_t -∗ pblk2_ecl_R_t -∗
    pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_lend g k v I -∗ XL -∗
    (∀ gL gR gM : gname,
       wcur gL (1/2) (length dg_execL) -∗
       wcur gR (1/2) (length alt_forkc) -∗ wcur gM (1/2) 3%nat -∗
       (∀ l : list (bv 8), pwc_rres v (I ++ l ++ [wl_nl]) -∗ PT) -∗ Φ)
    ={E}=∗ out_chain Uart0 k (alt_forkc ++ dg_execL) Φ.
  Proof using Hcons.
    intros HTX HTY Hns HNE HEx Hline Hpos Hwit.
    iIntros "#Hex #HL #HLt #HRt #Ht #Hpin Hlend HXL HΦ".
    iMod (pterm_round_test E N Eex k v I L ws XL YR Φ
            HTX HTY Hns HNE HEx Hline Hwit
            with "Hex HL HLt HRt Ht Hpin Hlend HXL [HΦ]") as "$"; [| done].
    iIntros (gL gR gM) "HcL HcR HcM #Hfz".
    iApply ("HΦ" $! gL gR gM with "HcL HcR HcM").
    iIntros (l) "Hres".
    iDestruct "Hfz" as "[#Hf | #HT]"; [| iExact "HT"].
    iExFalso. iApply (pterm_read_absurd v I l Hpos with "Hf Hres").
  Qed.

End pipe_both.

(* the widened line credential and the loop's family at it, at the fixed
   part: abbreviations of the generic ones with the pipeline's arm *)
Notation pwc_line2 g := (gwc_line pipe_lm (pipe_params g) (pipe_X g)).
Notation pwc_lpr2 g := (gwc_lpr pipe_lm (pipe_params g) (pipe_X g)).
