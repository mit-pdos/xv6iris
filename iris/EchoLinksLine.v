(* ===================================================================== *)
(*  EchoLinksLine.v -- THE ERA'S WRITE CREDENTIAL ACROSS ONE TURN OF THE  *)
(*  SHELL'S COMMAND LOOP WHEN A CHILD RUNS, AND ACROSS THE SHELL'S OWN    *)
(*  FORK PANIC (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane          *)
(*  SH-LINE-CRED, the lemmas M3b core wires into the walk).               *)
(*                                                                       *)
(*  [EchoLinks] carries the credential from a line boundary through the   *)
(*  shell's prompt and the line's read: [ewc_owed] --'$'--> [ewc_sp]      *)
(*  --' '--> [ewc_open] --read--> [ewc_owed] at [I ++ l ++ [wl_nl]], the  *)
(*  era's input with the body just typed and its newline on the end.      *)
(*  What is missing is everything a CHILD does between that read and the  *)
(*  next prompt, and what the shell does when its fork fails:             *)
(*                                                                       *)
(*    [ewc_blk v I a i]   alternative [a] of the line's block chosen, [i] *)
(*                        of its bytes out ([i = 0]: nothing chosen yet;  *)
(*                        the first byte files the choice, exactly as     *)
(*                        echo's first byte does in [UEchoOut.ech]);      *)
(*    [ewc_post v I a]    the block written up to its last two bytes --   *)
(*                        the "$ " every line alternative but the panic   *)
(*                        ends in, which the SHELL writes after [wait];   *)
(*    [ewc_panic v I i]   [ewc_blk] at [a = 3]: "fork\n", the shell's own *)
(*                        panic line, whose end is the BANNER of a fresh  *)
(*                        prologue round ([EchoLinks.wr_ban] at [j = 0]). *)
(*                                                                       *)
(*  THE BLOCK IS THE LINE'S, NOT A CONSTANT: alternative [a] is           *)
(*  [EchoDisc.line_alts_of (last_ws I) !!! a], and at [a = 0] that is     *)
(*  what echo prints back -- the words of the input's LAST BODY, minus    *)
(*  the command name, and then the prompt.  Only alternatives 1, 2 and 3  *)
(*  are closed lists, which is why only their lengths are numbers.        *)
(*                                                                       *)
(*  ONE FAMILY, [ewc_blk], carries all three: the child's run, the exec   *)
(*  failure's diagnostic, and the panic are the same walk at different    *)
(*  [a].  The prompt after a child is then two steps at [ewc_post], and   *)
(*  the loop's boundary credential is WIDENED to [ewc_line]: the round's  *)
(*  open prologue ([wr_pro], round 0 and every restart) OR a line block   *)
(*  written up to its prompt ([ewc_post] at some [a < 3]; [a = 2] is the  *)
(*  child that recorded no choice, i.e. [ewc_owed]'s [wr_blk] arm         *)
(*  itself).  [ewc_lpr]/[ewc_lcred] are [EchoLinks.ewc_pr]/[ewc_cred] at  *)
(*  that widened boundary, so the shell's [Wc] can be instantiated here   *)
(*  and nothing in [UkSh] changes (review-m6a3.md, Finding 2).            *)
(*                                                                       *)
(*  THE ONE SHAPE [EchoLinks] GETS WRONG for these steps -- not missing,  *)
(*  loose: [wr_open]/[wr_blk] record only [pro_idx cs q < pro_rounds ps],  *)
(*  "the round this block is in has settled", which ADMITS a writer whose *)
(*  own lower bound [ps] has already resolved a round that has not        *)
(*  opened.  The shell's panic opens round [S (pro_idx cs (length cs))]   *)
(*  and [wr_ban] wants that round's resolution to be [replicate j 1] with *)
(*  [j = 0] -- i.e. EMPTY -- which the loose shape cannot give.  The      *)
(*  claim's own invariant ([EchoOut.ps_len_ok] (A): nothing is filed for  *)
(*  a round that has not opened) says it is empty; the credential's pure  *)
(*  shape has to say so too.  So every shape here carries [wr_tail]:      *)
(*                                                                       *)
(*    [wr_tail ps cs := pro_from (S (pro_idx cs (length cs))) ps = []]     *)
(*                                                                       *)
(*  ([wr_pro] already pins it: its [~ pro_done] arm settles the round     *)
(*  exactly at the choice byte, [wr_pro_tail]).  The tight shapes are     *)
(*  [wr_blk_t]/[wr_sp_t]/[wr_open_t]; the loose ones are implied          *)
(*  ([ewc_sp_t_sp], [ewc_open_t_open]) and never needed again.            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import EchoOut.
Require Import EchoLinks.
(* as in EchoDisc / EchoOutPure / EchoOut / EchoLinks: the Sail imports
   leave string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.


(* ===================================================================== *)
(*  S0  THE ALTERNATIVES' LENGTHS.  THREE OF THE FOUR ARE CONSTANTS and   *)
(*  are read by computation; the GOOD one is the line's own output and    *)
(*  its length is [EchoDisc.line_alts_of_0_length] -- the output's        *)
(*  length plus the prompt's two bytes, never a number.                   *)
(* ===================================================================== *)
(* the four alternatives' lengths and last two bytes are [EchoDisc]'s
   ([line_alts_len1] .. [line_alts_space]), pure facts moved there *)

(* a byte of [line_alts_of ws !!! a] exists only for a real alternative:
   out of range the list is the default [[]] *)
Lemma line_alts_lt (ws : list (list (bv 8))) (a i : nat) (b : bv 8) :
  line_alts_of ws !!! a !! i = Some b -> (a < 4)%nat.
Proof.
  intros Hb.
  destruct (decide (a < 4)%nat) as [? | Hge]; [done |].
  exfalso. pose proof (lookup_lt_Some _ _ _ Hb) as Hlt.
  rewrite list_lookup_total_alt
    (lookup_ge_None_2 (line_alts_of ws) a
       ltac:(rewrite line_alts_of_length; lia)) in Hlt.
  cbn in Hlt. lia.
Qed.

Lemma snoc_lookup_total (cs : list nat) (a : nat) :
  (cs ++ [a]) !!! length cs = a.
Proof.
  rewrite list_lookup_total_alt lookup_app_r; [| lia].
  by rewrite Nat.sub_diag.
Qed.


(* ===================================================================== *)
(*  S1  THE TIGHT SHAPES                                                  *)
(* ===================================================================== *)
(* THE ROUND THIS BLOCK IS IN IS THE LAST ONE RESOLVED: nothing of [ps]
   is filed beyond it.  [pro_idx cs (length cs)] is the round of the
   block that closes line [length cs] -- the block a [wr_blk] owes, and
   the block a [wr_open] has just written ([nlines I = length cs] there). *)
Definition wr_tail (ps cs : list nat) : Prop :=
  pro_from (S (pro_idx cs (length cs))) ps = [].

Definition wr_blk_t (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_blk ps cs I P /\ wr_tail ps cs.

Definition wr_sp_t (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_sp ps cs I P /\ wr_tail ps cs.

Definition wr_open_t (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_open ps cs I P /\ wr_tail ps cs.

(* the choice list of a block with [i] bytes out: the first byte files it *)
Definition blkcs (cs : list nat) (a i : nat) : list nat :=
  match i with O => cs | S _ => cs ++ [a] end.

(* ---- what [wr_blk] says about the input's parse ---- *)
Lemma wr_blk_lines (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk ps cs I P -> nlines I = S (length cs).
Proof. by intros (_ & _ & Hn & _). Qed.

Lemma wr_blk_started (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk ps cs I P -> nstarted I = S (length cs).
Proof.
  intros (_ & Hr & Hn & _). by rewrite (nstarted_rest_nil I Hr) Hn.
Qed.

(* ...and it is echo's own stage ([UEchoOut.echo_stage], spelled out) *)
Lemma wr_blk_t_stage (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_t ps cs I P ->
  rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before ps cs I)
  /\ pro_pin ps cs I
  /\ wr_tail ps cs.
Proof.
  intros [(Hpin & Hr & Hn & HP) Ht]. split_and!; assumption.
Qed.

(* ---- filing an alternative reads no block below the boundary ---- *)
Lemma wr_blk_pin_snoc (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk ps cs I P -> pro_pin ps (cs ++ [a]) I.
Proof.
  intros Hw. pose proof (wr_blk_started ps cs I P Hw) as Hst.
  destruct Hw as (Hpin & _).
  intros q Hq. rewrite (pro_idx_app_le cs [a] q ltac:(lia)). exact (Hpin q Hq).
Qed.

Lemma wr_blk_low (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk ps cs I P -> proc_before ps (cs ++ [a]) I = proc_before ps cs I.
Proof.
  intros Hw. pose proof Hw as (Hpin & Hr & Hn & HP). symmetry.
  apply (proc_before_cs_prefix ps ps cs (cs ++ [a]) I
           ltac:(reflexivity) ltac:(by eexists) Hpin).
  rewrite (nlines_removelast I Hr) Hn. lia.
Qed.

(* THE LINE THE BLOCK ANSWERS is the input's LAST BODY, which is what
   [last_ws] names -- so a block indexed by [length cs] and the parse's
   own [last_ws] are the same word list. *)
Lemma last_ws_of_blk (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk ps cs I P -> wl_words (bodies_of I !!! length cs) = last_ws I.
Proof.
  intros Hw. pose proof (wr_blk_lines ps cs I P Hw) as Hn.
  rewrite (last_ws_lta I). f_equal. f_equal. lia.
Qed.

(* ---- the block a [wr_blk] owes, once alternative [a] is filed ---- *)
Lemma wr_blk_pending (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk ps cs I P ->
  pending_at ps (cs ++ [a]) I = alt_cont ps (cs ++ [a]) (bodies_of I) (length cs).
Proof.
  intros Hw. pose proof (wr_blk_nonnil ps cs I P Hw) as Hne.
  destruct Hw as (_ & Hr & Hn & _).
  rewrite /pending_at decide_False; [| exact Hne].
  rewrite decide_True; [| exact Hr].
  replace (nlines I - 1)%nat with (length cs) by lia.
  reflexivity.
Qed.

Lemma wr_blk_alt (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk ps cs I P -> a <> 3%nat ->
  pending_at ps (cs ++ [a]) I = line_alts_of (last_ws I) !!! a.
Proof.
  intros Hw Ha.
  rewrite (wr_blk_pending ps cs I P a Hw) /alt_cont snoc_lookup_total
          (last_ws_of_blk ps cs I P Hw).
  case_decide as H3; [done |]. by rewrite app_nil_r.
Qed.

Lemma wr_blk_alt3 (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk ps cs I P ->
  pending_at ps (cs ++ [3%nat]) I
  = line_alts_of (last_ws I) !!! 3%nat
    ++ pro_of (pro_from (S (pro_idx cs (length cs))) ps).
Proof.
  intros Hw.
  rewrite (wr_blk_pending ps cs I P 3%nat Hw) /alt_cont snoc_lookup_total
          (last_ws_of_blk ps cs I P Hw).
  case_decide as H3; [| done].
  by rewrite (pro_idx_app_le cs [3%nat] (length cs) ltac:(lia)).
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR: byte [j] of the alternative
   is byte [P + j] of the stream, for EVERY alternative -- the panic's
   block goes on into the next round's prologue, but its first five bytes
   are the panic line all the same. *)
Lemma wr_blk_byte (ps cs : list nat) (I : list (bv 8)) (P a j : nat)
      (b : bv 8) :
  wr_blk ps cs I P -> line_alts_of (last_ws I) !!! a !! j = Some b ->
  proc_stream ps (cs ++ [a]) I !! (P + j)%nat = Some b.
Proof.
  intros Hw Hb. pose proof Hw as (_ & _ & _ & HP).
  rewrite /proc_stream (wr_blk_low ps cs I P a Hw) lookup_app_r; [| lia].
  replace (P + j - length (proc_before ps cs I))%nat with j by lia.
  destruct (decide (a = 3%nat)) as [-> | Ha].
  - rewrite (wr_blk_alt3 ps cs I P Hw) lookup_app_l; [exact Hb |].
    exact (lookup_lt_Some _ _ _ Hb).
  - by rewrite (wr_blk_alt ps cs I P a Hw Ha).
Qed.

(* ---- the round index does not move when a non-panic alternative is filed ---- *)
Lemma pro_idx_snoc_ne (cs : list nat) (a : nat) :
  a <> 3%nat -> pro_idx (cs ++ [a]) (S (length cs)) = pro_idx cs (length cs).
Proof.
  intros Ha. rewrite pro_idx_S snoc_lookup_total decide_False; [| exact Ha].
  rewrite (pro_idx_app_le cs [a] (length cs) ltac:(lia)). lia.
Qed.

Lemma pro_idx_snoc_3 (cs : list nat) :
  pro_idx (cs ++ [3%nat]) (S (length cs)) = S (pro_idx cs (length cs)).
Proof.
  rewrite pro_idx_S snoc_lookup_total
          (pro_idx_app_le cs [3%nat] (length cs) ltac:(lia)).
  first [ (case_decide as H3; [lia | exfalso; exact (H3 eq_refl)]) | lia ].
Qed.

Lemma wr_tail_snoc (ps cs : list nat) (a : nat) :
  a <> 3%nat -> wr_tail ps cs -> wr_tail ps (cs ++ [a]).
Proof.
  intros Ha Ht. rewrite /wr_tail length_app. cbn [length].
  rewrite Nat.add_1_r (pro_idx_snoc_ne cs a Ha). exact Ht.
Qed.

(* ===================================================================== *)
(*  S2  THE STEPS, PURE                                                   *)
(* ===================================================================== *)

(* (1) THE WHOLE BLOCK OF A NON-PANIC ALTERNATIVE, written: the cursor    *)
(*     lands on the stream's end and the round is settled -- [wr_open].   *)
Lemma wr_blk_open (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_t ps cs I P -> a <> 3%nat ->
  wr_open_t ps (cs ++ [a]) I (P + length (line_alts_of (last_ws I) !!! a))%nat.
Proof.
  intros [Hw Ht] Ha.
  pose proof (wr_blk_started ps cs I P Hw) as Hst.
  pose proof Hw as (Hpin & Hr & Hn & HP).
  split; [| exact (wr_tail_snoc ps cs a Ha Ht)].
  rewrite /wr_open. split_and!.
  - exact (wr_blk_pin_snoc ps cs I P a Hw).
  - exact Hr.
  - rewrite (length_app cs [a]) Hn. cbn [length]. lia.
  - rewrite Hn (pro_idx_snoc_ne cs a Ha). apply Hpin. lia.
  - rewrite /proc_stream (wr_blk_low ps cs I P a Hw)
            (wr_blk_alt ps cs I P a Hw Ha)
            (length_app (proc_before ps cs I)
               (line_alts_of (last_ws I) !!! a)) HP.
    reflexivity.
Qed.

(* (2) ...AND ONE BYTE SHORT OF IT, which is where the shell's ' ' goes:  *)
(*     [wr_sp] at the prompt's second byte.                               *)
Lemma wr_blk_sp (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_t ps cs I P -> (a < 3)%nat ->
  wr_sp_t ps (cs ++ [a]) I
    (P + (length (line_alts_of (last_ws I) !!! a) - 1))%nat.
Proof.
  intros Hw Ha. pose proof (line_alts_len_ge2 (last_ws I) a Ha) as Hlen.
  destruct (wr_blk_open ps cs I P a Hw ltac:(lia)) as [Hop Ht].
  split; [| exact Ht]. split.
  - replace (S (P + (length (line_alts_of (last_ws I) !!! a) - 1)))%nat
      with (P + length (line_alts_of (last_ws I) !!! a))%nat by lia.
    exact Hop.
  - exact (wr_blk_byte ps cs I P a _ _ (proj1 Hw)
             (line_alts_space (last_ws I) a Ha)).
Qed.

(* (3) THE SPACE AND THE READ, as [EchoLinks] has them, with the tail     *)
(*     riding along.                                                      *)
Lemma wr_sp_open_t (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_sp_t ps cs I P -> wr_open_t ps cs I (S P).
Proof. intros [Hs Ht]. split; [exact (wr_sp_open ps cs I P Hs) | exact Ht]. Qed.

Lemma wr_open_read_t (ps cs : list nat) (I : list (bv 8)) (P : nat)
      (l : list (bv 8)) :
  wr_open_t ps cs I P -> wl_nl ∉ l ->
  wr_blk_t ps cs (I ++ l ++ [wl_nl]) P.
Proof.
  intros [Ho Ht] Hl.
  split; [exact (wr_open_read ps cs I P l Ho Hl) | exact Ht].
Qed.

(* (4) THE ROUND'S CHOICE BYTE SETTLES ITS ROUND, so the writer's         *)
(*     resolution ends exactly there: [wr_pro]'s [~ pro_done] is the tail. *)
Lemma wr_pro_tail (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro ps cs I P -> wr_tail (ps ++ [0%nat]) cs.
Proof.
  intros (Hpin & Hr & Hn & Hopen & Hnd & HP).
  pose proof (pro_pin_idx_le ps cs I Hpin) as Hle.
  rewrite Hn in Hnd Hle.
  rewrite /wr_tail.
  replace (S (pro_idx cs (length cs))) with (pro_idx cs (length cs) + 1)%nat
    by lia.
  rewrite -(pro_from_add 1 (pro_idx cs (length cs)))
          (pro_from_snoc_le (pro_idx cs (length cs)) ps 0%nat Hle).
  cbn [pro_from]. exact (pro_tail_open_snoc _ 0%nat Hnd).
Qed.

Lemma wr_pro_dollar_t (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro ps cs I P -> wr_sp_t (ps ++ [0%nat]) cs I (S P).
Proof.
  intros Hw. split;
    [exact (wr_pro_dollar ps cs I P Hw) | exact (wr_pro_tail ps cs I P Hw)].
Qed.

(* (5) THE PANIC LINE OPENS A FRESH ROUND AT THE SAME INPUT: five bytes   *)
(*     in, the writer owes that round's BANNER -- [wr_ban] with no failed *)
(*     sub-round ([j = 0]) and the panic line as the block's prefix        *)
(*     ([wr_pre]).  This is where [wr_tail] is spent.                     *)
Lemma wr_blk_ban (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_t ps cs I P ->
  wr_ban ps (cs ++ [3%nat]) I
    (P + length (line_alts_of (last_ws I) !!! 3%nat))%nat.
Proof.
  intros [Hw Ht]. pose proof (wr_blk_nonnil ps cs I P Hw) as Hne.
  pose proof Hw as (Hpin & Hr & Hn & HP).
  rewrite /wr_ban. split_and!.
  - exact (wr_blk_pin_snoc ps cs I P 3%nat Hw).
  - exact Hr.
  - rewrite (length_app cs [3%nat]) Hn. cbn [length]. lia.
  - right. rewrite Hn.
    replace (S (length cs) - 1)%nat with (length cs) by lia.
    exact (snoc_lookup_total cs 3%nat).
  - exists 0%nat. split.
    + rewrite Hn pro_idx_snoc_3 pro_fail_0. exact Ht.
    + rewrite (wr_blk_low ps cs I P 3%nat Hw) -HP /wr_pre.
      rewrite decide_False; [| exact Hne].
      rewrite line_alts_of_3. lia.
Qed.


(* ===================================================================== *)
(*  S3  THE CREDENTIAL AS RESOURCES                                       *)
(* ===================================================================== *)
Section echo_links_line.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* THE BLOCK FAMILY: alternative [a] of the line's block chosen, [i] of
     its bytes out -- or the taint.  At [i = 0] nothing is chosen and the
     index [a] is not read ([ewc_blk_0]). *)
  Definition ewc_blk (v : era_pins) (I : list (bv 8)) (a i : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_blk_t ps cs I P⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v (blkcs cs a i) ∗ inp_lb v I) ∨ T)%I.

  (* ...the block written up to its prompt, which the shell writes after
     [wait] ([a < 3]; [a = 2] is the block-first '$' itself, nothing out) *)
  Definition ewc_post (v : era_pins) (I : list (bv 8)) (a : nat) : iProp Σ :=
    ewc_blk v I a (length (line_alts_of (last_ws I) !!! a) - 2)%nat.

  (* ...and the shell's own panic line, [i] of its five bytes out *)
  Definition ewc_panic (v : era_pins) (I : list (bv 8)) (i : nat) : iProp Σ :=
    ewc_blk v I 3%nat i.

  (* THE OPEN-PROLOGUE ARM of [EchoLinks.ewc_owed] on its own *)
  Definition ewc_pro (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_pro ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  Definition ewc_sp_t (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_sp_t ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  Definition ewc_open_t (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_open_t ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  (* THE LOOP'S BOUNDARY CREDENTIAL, WIDENED: the round's prologue is
     still open (sh's first prompt of a round: '$' files [ps ++ [0]]), or
     a line's block has been written up to its prompt by whoever took
     alternative [a] -- echo ([a = 0]), the exec-failed child ([a = 1]),
     or nobody ([a = 2], the child died at the null store and sh's '$'
     is the block's first byte). *)
  Definition ewc_line (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (ewc_pro v I ∨ (∃ a : nat, ⌜(a < 3)%nat⌝ ∗ ewc_post v I a))%I.

  (* ...indexed by the prompt bytes out, [EchoLinks.ewc_pr]'s twin *)
  (* ...AND A FOURTH INDEX (lane IO-LEAF, step 4): [3] is the line's
     BLOCK OWED with nothing chosen -- what the read of a line leaves and
     what the shell's fork LENDS its child ([ewc_blk] at [i = 0], the index
     [a] unread).  It is kept apart from [0] because [ewc_line] is a
     disjunction the fork cannot undo: a block-owed credential IS an
     [ewc_line] ([ewc_line_of_blk0]), the converse is false. *)
  Definition ewc_lpr (v : era_pins) (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => ewc_line v I
    | S O => ewc_sp_t v I
    | S (S O) => ewc_open_t v I
    | _ => ewc_blk v I 0%nat 0%nat
    end.

  (* ...with the era's pin beside it, [EchoLinks.ewc_cred]'s twin: the
     shape the shell's [Wc] is instantiated at *)
  Definition ewc_lcred (k : nat) (I : list (bv 8)) (p : nat) : iProp Σ :=
    (∃ v : era_pins, era_pin γ k v ∗ ewc_lpr v I p)%I.

  (* THE DISPATCH, NOT [apply _].  The tree's 455 [Timeless] instances sit
     under mostly transparent definitions, so the hint net cannot
     discriminate and one search at this altitude tries nearly all of
     them (3s a site here, 13s for this block).  Descend through the
     CONNECTIVES and name the leaf, syntactically -- the same dispatch as
     [FileLinksLine]'s, one tier down. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless T => assumption
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Timeless (era_pin _ _ _) => apply era_pin_timeless
    | |- _ => apply _
    end.

  Global Instance ewc_blk_timeless v I a i : Timeless (ewc_blk v I a i).
  Proof using Timeless0. rewrite /ewc_blk. tl_leaf. Qed.
  Global Instance ewc_post_timeless v I a : Timeless (ewc_post v I a).
  Proof using Timeless0. rewrite /ewc_post. apply ewc_blk_timeless. Qed.
  Global Instance ewc_panic_timeless v I i : Timeless (ewc_panic v I i).
  Proof using Timeless0. rewrite /ewc_panic. apply ewc_blk_timeless. Qed.
  Global Instance ewc_pro_timeless v I : Timeless (ewc_pro v I).
  Proof using Timeless0. rewrite /ewc_pro. tl_leaf. Qed.
  Global Instance ewc_sp_t_timeless v I : Timeless (ewc_sp_t v I).
  Proof using Timeless0. rewrite /ewc_sp_t. tl_leaf. Qed.
  Global Instance ewc_open_t_timeless v I : Timeless (ewc_open_t v I).
  Proof using Timeless0. rewrite /ewc_open_t. tl_leaf. Qed.
  Global Instance ewc_line_timeless v I : Timeless (ewc_line v I).
  Proof using Timeless0.
    rewrite /ewc_line.
    apply bi.or_timeless; [apply ewc_pro_timeless |].
    apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply ewc_post_timeless].
  Qed.
  Global Instance ewc_lpr_timeless v I p : Timeless (ewc_lpr v I p).
  Proof using Timeless0.
    rewrite /ewc_lpr. destruct p as [| [| [| p]]];
      [apply ewc_line_timeless | apply ewc_sp_t_timeless
      | apply ewc_open_t_timeless | apply ewc_blk_timeless].
  Qed.
  Global Instance ewc_lcred_timeless k I p : Timeless (ewc_lcred k I p).
  Proof using Timeless0.
    rewrite /ewc_lcred. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply era_pin_timeless | apply ewc_lpr_timeless].
  Qed.

  (* ---- the taint inhabits every shape ---- *)
  Lemma ewc_blk_taint v I a i : T -∗ ewc_blk v I a i.
  Proof using . iIntros "HT". rewrite /ewc_blk. by iRight. Qed.
  Lemma ewc_pro_taint v I : T -∗ ewc_pro v I.
  Proof using . iIntros "HT". rewrite /ewc_pro. by iRight. Qed.
  Lemma ewc_sp_t_taint v I : T -∗ ewc_sp_t v I.
  Proof using . iIntros "HT". rewrite /ewc_sp_t. by iRight. Qed.
  Lemma ewc_open_t_taint v I : T -∗ ewc_open_t v I.
  Proof using . iIntros "HT". rewrite /ewc_open_t. by iRight. Qed.
  Lemma ewc_line_taint v I : T -∗ ewc_line v I.
  Proof using . iIntros "HT". rewrite /ewc_line. iLeft. by iApply ewc_pro_taint. Qed.
  Lemma ewc_lpr_taint v I p : T -∗ ewc_lpr v I p.
  Proof using .
    iIntros "HT". rewrite /ewc_lpr. destruct p as [| [| [| p]]];
      [ by iApply ewc_line_taint | by iApply ewc_sp_t_taint
      | by iApply ewc_open_t_taint | by iApply ewc_blk_taint ].
  Qed.

  (* ---- the tight shapes imply [EchoLinks]'s loose ones ---- *)
  Lemma ewc_pro_owed v I : ewc_pro v I -∗ EchoLinks.ewc_owed T v I.
  Proof using Persistent0.
    rewrite /ewc_pro /EchoLinks.ewc_owed. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. by left.
  Qed.

  Lemma ewc_blk_owed v I a : ewc_blk v I a 0%nat -∗ EchoLinks.ewc_owed T v I.
  Proof using Persistent0.
    rewrite /ewc_blk /EchoLinks.ewc_owed. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    cbn [blkcs]. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro. right.
    exact (proj1 Hw).
  Qed.

  Lemma ewc_sp_t_sp v I : ewc_sp_t v I -∗ EchoLinks.ewc_sp T v I.
  Proof using Persistent0.
    rewrite /ewc_sp_t /EchoLinks.ewc_sp. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (proj1 Hw).
  Qed.

  Lemma ewc_open_t_open v I : ewc_open_t v I -∗ EchoLinks.ewc_open T v I.
  Proof using Persistent0.
    rewrite /ewc_open_t /EchoLinks.ewc_open. iIntros "[Hl | #HT]";
      last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (proj1 Hw).
  Qed.

  (* ---- the block family at [i = 0] reads no alternative ---- *)
  Lemma ewc_blk_0 v I a a' : ewc_blk v I a 0%nat -∗ ewc_blk v I a' 0%nat.
  Proof using . rewrite /ewc_blk. cbn [blkcs]. iIntros "H". iExact "H". Qed.

  (* ...and it is the [a = 2] arm of the widened boundary: the block-first
     '$' of a child that recorded no choice *)
  Lemma ewc_line_of_blk0 v I a : ewc_blk v I a 0%nat -∗ ewc_line v I.
  Proof using .
    iIntros "Hc". rewrite /ewc_line. iRight. iExists 2%nat.
    iSplitR; [iPureIntro; lia |].
    assert (H2 : (length (line_alts_of (last_ws I) !!! 2%nat) - 2)%nat = 0%nat)
      by (rewrite (line_alts_len2_ (last_ws I)); reflexivity).
    rewrite /ewc_post H2. iApply (ewc_blk_0 with "Hc").
  Qed.

  Lemma ewc_line_of_post v I a : (a < 3)%nat -> ewc_post v I a -∗ ewc_line v I.
  Proof using .
    intros Ha. iIntros "Hc". rewrite /ewc_line. iRight. iExists a.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  Lemma ewc_line_of_pro v I : ewc_pro v I -∗ ewc_line v I.
  Proof using . iIntros "Hc". rewrite /ewc_line. by iLeft. Qed.

  (* =================================================================== *)
  (*  S4  ONE BYTE OF THE BLOCK, THROUGH THE ERA'S LINKS                  *)
  (*                                                                     *)
  (*  The block-first byte FILES the alternative ([echo_link_blk]); every *)
  (*  byte after it is an ordinary byte of the block the choice fixed     *)
  (*  ([echo_link_w]).  No bound on [i] beyond the byte's existence: the  *)
  (*  credential does not know WHO writes a byte, only that it is next.   *)
  (* =================================================================== *)
  Lemma echo_blk_step (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    line_alts_of (last_ws I) !!! a !! i = Some b ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_blk v I a i -∗
    (ewc_blk v I a (S i) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_blk with "Hlk") as "#Hblk".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_blk. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    pose proof (proj1 Hw) as Hwb. pose proof Hwb as (Hpin & Hr & Hn & HP).
    pose proof (wr_blk_nonnil ps cs I P Hwb) as Hne.
    pose proof (line_alts_lt (last_ws I) a i b Hb) as Ha.
    destruct i as [| i'].
    - (* THE BLOCK-FIRST BYTE files the alternative *)
      cbn [blkcs]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v P a b ps cs I Φ
                with "[%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hne. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact HP. }
      { exact Ha. }
      { exact Hb. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs]. rewrite Nat.add_1_r.
      iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
    - (* every byte after it, at the choice list the first one extended *)
      cbn [blkcs].
      iApply ("Hw" $! k v (P + S i')%nat b ps (cs ++ [a]) I Φ
                with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { rewrite (length_app cs [a]) Hn. cbn [length]. lia. }
      { exact (wr_blk_pin_snoc ps cs I P a Hwb). }
      { exact (wr_blk_byte ps cs I P a (S i') b Hwb Hb). }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, P. cbn [blkcs].
      replace (P + S (S i'))%nat with (S (P + S i'))%nat by lia.
      iFrame "Htn' Hps' Hcs' HE'". by iPureIntro.
  Qed.

  (* the block written up to its prompt IS [ewc_post], by definition *)
  Lemma ewc_blk_done v I a :
    ewc_blk v I a (length (line_alts_of (last_ws I) !!! a) - 2)%nat -∗
    ewc_post v I a.
  Proof using . rewrite /ewc_post. iIntros "$". Qed.

  (* ...and one byte further it is the half-written prompt *)
  Lemma ewc_blk_sp v I a :
    (a < 3)%nat ->
    ewc_blk v I a (length (line_alts_of (last_ws I) !!! a) - 1)%nat -∗
    ewc_sp_t v I.
  Proof using Persistent0.
    intros Ha. rewrite /ewc_blk /ewc_sp_t. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    pose proof (line_alts_len_ge2 (last_ws I) a Ha) as Hlen.
    assert (Hbc : blkcs cs a (length (line_alts_of (last_ws I) !!! a) - 1)
                  = cs ++ [a]).
    { destruct (length (line_alts_of (last_ws I) !!! a) - 1)%nat as [| kk] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [a]),
      (P + (length (line_alts_of (last_ws I) !!! a) - 1))%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. exact (wr_blk_sp ps cs I P a Hw Ha).
  Qed.

  (* =================================================================== *)
  (*  S5  THE SHELL'S PROMPT AFTER A CHILD, AND AT THE WIDENED BOUNDARY   *)
  (* =================================================================== *)
  (* THE '$' AFTER A CHILD: an ordinary byte of the chosen block when the
     child wrote its share ([a = 0, 1]), the block-FIRST byte when it
     recorded no choice ([a = 2]) -- [echo_blk_step] at [i = length - 2]
     is both, and what it leaves is the half-written prompt. *)
  Lemma echo_prompt_dollar_post (k : nat) (v : era_pins) (I : list (bv 8))
      (a : nat) (b : bv 8) (Φ : iProp Σ) :
    (a < 3)%nat -> b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_post v I a -∗
    (ewc_sp_t v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Ha Hb. iIntros "#Hpin #Hlk Hc HΦ".
    pose proof (line_alts_len_ge2 (last_ws I) a Ha) as Hlen.
    assert (Hby : line_alts_of (last_ws I) !!! a
                    !! (length (line_alts_of (last_ws I) !!! a) - 2)%nat
                  = Some b)
      by (rewrite Hb; exact (line_alts_dollar (last_ws I) a Ha)).
    iApply (echo_blk_step k v I a
              (length (line_alts_of (last_ws I) !!! a) - 2)%nat b Φ Hby
              with "Hpin Hlk Hc [HΦ]").
    iIntros "Hc". iApply "HΦ".
    replace (S (length (line_alts_of (last_ws I) !!! a) - 2))%nat
      with (length (line_alts_of (last_ws I) !!! a) - 1)%nat by lia.
    iApply (ewc_blk_sp v I a Ha with "Hc").
  Qed.

  (* THE ' ' AFTER IT: [EchoLinks.echo_prompt_space], with the tail along *)
  Lemma echo_prompt_space_t (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_sp_t v I -∗
    (ewc_open_t v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_sp_t. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply ewc_open_t_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct Hw as [[Hop Hby] Ht].
    pose proof Hop as (Hpin & Hr & Hn & Hrd & HP).
    iApply ("Hw" $! k v P b ps cs I Φ
              with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { lia. }
    { exact Hpin. }
    { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /ewc_open_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    iPureIntro. exact (wr_sp_open_t ps cs I P (conj (conj Hop Hby) Ht)).
  Qed.

  (* THE '$' AT THE WIDENED BOUNDARY: the round's choice byte when the
     prologue is open ([echo_link_pro] at [a = 0], as in
     [EchoLinks.echo_prompt_dollar]'s first case), the byte after the
     child's share otherwise. *)
  Lemma echo_prompt_dollar_line (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_line v I -∗
    (ewc_sp_t v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    rewrite /ewc_line. iDestruct "Hc" as "[Hc | Hc]"; last first.
    { iDestruct "Hc" as (a) "[%Ha Hc]".
      iApply (echo_prompt_dollar_post k v I a b Φ Ha Hb
                with "Hpin Hlk Hc HΦ"). }
    iDestruct (echo_links_pro with "Hlk") as "#Hpro".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    rewrite /ewc_pro. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply ewc_sp_t_taint. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hhd : pro_alts !!! 0%nat !! 0%nat = Some b)
      by (rewrite wr_pro_alts_0 Hb; exact wr_prompt_head).
    pose proof (wr_pro_dollar_t ps cs I P Hw) as Hsp.
    destruct Hw as (Hpin & Hr & Hn & Hopen & Hnd & HP).
    iApply ("Hpro" $! k v P 0%nat b ps cs I Φ
              with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
    { exact Hr. }
    { exact Hopen. }
    { lia. }
    { exact Hpin. }
    { exact Hnd. }
    { exact HP. }
    { rewrite pro_alts_length. lia. }
    { exact Hhd. }
    iIntros "Hres". iApply "HΦ". rewrite /ewc_sp_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists (ps ++ [0%nat]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
    by iPureIntro.
  Qed.

  (* ...AS ONE STEP FAMILY over the prompt's two bytes, [UShOut.ushpr_step]'s
     twin at the widened boundary *)
  Lemma ewc_lpr_step (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
      (b : bv 8) (Φ : iProp Σ) :
    u_prompt !! p = Some b ->
    (p < 2)%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_lpr v I p -∗
    (ewc_lpr v I (S p) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb Hp. destruct p as [| [| p]]; [| | exfalso; lia].
    - assert (Hb0 : b = u_prompt !!! 0%nat).
      { rewrite wr_prompt_head in Hb. by injection Hb. }
      iIntros "#Hpin #Hlk Hc HΦ".
      iApply (echo_prompt_dollar_line k v I b Φ Hb0 with "Hpin Hlk Hc HΦ").
    - assert (Hb1 : b = u_prompt !!! 1%nat).
      { rewrite wr_prompt_tail in Hb. by injection Hb. }
      iIntros "#Hpin #Hlk Hc HΦ".
      iApply (echo_prompt_space_t k v I b Φ Hb1 with "Hpin Hlk Hc HΦ").
  Qed.

  (* =================================================================== *)
  (*  S6  THE READ, landing on the block family                           *)
  (* =================================================================== *)
  (* [EchoLinks.ewc_read]'s twin: the line just echoed owes its block and
     no alternative is chosen yet -- so this is [ewc_blk] at [i = 0] for
     EVERY [a]; the fork lends it and the child's first byte decides.
     The body [l] is whatever was typed, newline excluded. *)
  Lemma ewc_read_t (v : era_pins) (I : list (bv 8)) (a : nat)
      (l : list (bv 8)) :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ ewc_open_t v I -∗
    ewc_blk v (I ++ l ++ [wl_nl]) a 0%nat.
  Proof using Persistent0.
    intros Hl. iIntros "#HE' Hc". rewrite /ewc_open_t /ewc_blk.
    iDestruct "Hc" as "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. cbn [blkcs]. rewrite Nat.add_0_r.
    iFrame "Htn Hps Hcs HE'". iPureIntro.
    exact (wr_open_read_t ps cs I P l Hw Hl).
  Qed.

  (* ...and, at the loop's family, [UkSh.ush_wc_read]'s content: the read
     of a line leaves the BLOCK-OWED shape at the next boundary (index [3],
     step 4), not the widened one -- the fork needs to know the block is
     still owed. *)
  Lemma ewc_lpr_read (v : era_pins) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ ewc_lpr v I 2%nat -∗
    ewc_lpr v (I ++ l ++ [wl_nl]) 3%nat.
  Proof using Persistent0.
    intros Hl. iIntros "#HE' Hc". cbn [ewc_lpr].
    iApply (ewc_read_t v I 0%nat l Hl with "HE' Hc").
  Qed.

  Lemma ewc_lcred_read (k : nat) (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    era_pin γ k v -∗ inp_lb v (I ++ l ++ [wl_nl]) -∗
    ewc_lcred k I 2%nat -∗ ewc_lcred k (I ++ l ++ [wl_nl]) 3%nat.
  Proof using Persistent0.
    intros Hl. iIntros "#Hpin #HE' Hc". rewrite /ewc_lcred.
    iDestruct "Hc" as (v') "[#Hpin' Hc]".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iExists v. iFrame "Hpin". iApply (ewc_lpr_read v I l Hl with "HE' Hc").
  Qed.

  (* ...and the block-owed shape IS a boundary credential: nobody wrote,
     and the shell's '$' is the block's first byte ([ewc_post] at [a = 2]).
     This is what the [cd] arm and a fork that returned -1 re-enter the
     loop head with ([UkSh.ush_wc_blk_line]'s content). *)
  Lemma ewc_lpr_blk_line (v : era_pins) (I : list (bv 8)) :
    ewc_lpr v I 3%nat -∗ ewc_lpr v I 0%nat.
  Proof using . cbn [ewc_lpr]. iApply (ewc_line_of_blk0 v I 0%nat). Qed.

  Lemma ewc_lcred_blk_line (k : nat) (I : list (bv 8)) :
    ewc_lcred k I 3%nat -∗ ewc_lcred k I 0%nat.
  Proof using .
    rewrite /ewc_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". iApply (ewc_lpr_blk_line with "Hc").
  Qed.

  (* ...the taint inhabits the pinned family too, at any pin *)
  Lemma ewc_lcred_taint (k : nat) (I : list (bv 8)) (p : nat) (v : era_pins) :
    era_pin γ k v -∗ T -∗ ewc_lcred k I p.
  Proof using Persistent0.
    iIntros "#Hpin #HT". rewrite /ewc_lcred. iExists v. iFrame "Hpin".
    iApply (ewc_lpr_taint with "HT").
  Qed.

  (* ...the block written by echo ([a = 0]) is the loop's boundary
     credential: what sh's forked child hands back through its exit *)
  Lemma ewc_lcred_of_post (k : nat) (I : list (bv 8)) (v : era_pins) :
    era_pin γ k v -∗ ewc_post v I 0%nat -∗ ewc_lcred k I 0%nat.
  Proof using .
    iIntros "#Hpin Hc". rewrite /ewc_lcred. iExists v. iFrame "Hpin".
    cbn [ewc_lpr]. iApply (ewc_line_of_post v I 0%nat ltac:(lia) with "Hc").
  Qed.

  (* ...AT ANY ALTERNATIVE A CHILD CAN TAKE (lane IO-LEAF, M4b(2)): the
     exec-failed child's "exec %s failed" is [a = 1]. *)
  Lemma ewc_lcred_of_post_a (k : nat) (I : list (bv 8)) (a : nat)
      (v : era_pins) :
    (a < 3)%nat ->
    era_pin γ k v -∗ ewc_post v I a -∗ ewc_lcred k I 0%nat.
  Proof using .
    intros Ha. iIntros "#Hpin Hc". rewrite /ewc_lcred. iExists v.
    iFrame "Hpin". cbn [ewc_lpr]. iApply (ewc_line_of_post v I a Ha with "Hc").
  Qed.

  (* THE BLOCK OWED OPENS AT ANY ALTERNATIVE (M4b(2)): nothing has been
     written, so the block-first byte is still free to file whichever the
     writer takes ([ewc_blk_0]).  [ewc_lcred_blk_panic] below is [a = 3]. *)
  Lemma ewc_lcred_blk_open (k : nat) (I : list (bv 8)) (a : nat) :
    ewc_lcred k I 3%nat -∗
    ∃ v : era_pins, era_pin γ k v ∗ ewc_blk v I a 0%nat.
  Proof using .
    rewrite /ewc_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". cbn [ewc_lpr].
    iApply (ewc_blk_0 v I 0%nat a with "Hc").
  Qed.

  (* =================================================================== *)
  (*  S7  THE PANIC, and the banner it opens                              *)
  (* =================================================================== *)
  Lemma echo_panic_step (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    line_alts_of (last_ws I) !!! 3%nat !! i = Some b ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_panic v I i -∗
    (ewc_panic v I (S i) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. rewrite /ewc_panic. exact (echo_blk_step k v I 3%nat i b Φ Hb).
  Qed.

  (* THE FIVE BYTES OUT, THE NEXT ROUND'S BANNER IS OWED: what the shell
     hands back to /init through its exit payload, at the same input, and
     what pays the restart round's banner ([EchoLinks.echo_banner_step]
     from [ewc_ban _ _ 0]). *)
  Lemma ewc_panic_done (v : era_pins) (I : list (bv 8)) :
    ewc_panic v I (length (line_alts_of (last_ws I) !!! 3%nat)) -∗
    EchoLinks.ewc_ban T v I 0%nat.
  Proof using Persistent0.
    rewrite /ewc_panic /ewc_blk /EchoLinks.ewc_ban.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (Hbc : blkcs cs 3%nat (length (line_alts_of (last_ws I) !!! 3%nat))
                  = cs ++ [3%nat])
      by (rewrite (line_alts_len3 (last_ws I)); reflexivity).
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [3%nat]),
      (P + length (line_alts_of (last_ws I) !!! 3%nat))%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (wr_blk_ban ps cs I P Hw).
  Qed.

  (* =================================================================== *)
  (*  S8  THE ENTRY: /init's last banner byte lands on the widened        *)
  (*      boundary's open-prologue arm ([EchoLinks.ewc_ban_done]'s twin;  *)
  (*      that lemma's [ewc_owed] admits a loose [wr_blk] arm it never   *)
  (*      produces, which is why the entry must come through here).      *)
  (* =================================================================== *)
  Lemma ewc_ban_done_line (v : era_pins) (I : list (bv 8)) :
    EchoLinks.ewc_ban T v I (length u_banner) -∗ ewc_line v I.
  Proof using Persistent0.
    rewrite /EchoLinks.ewc_ban. iIntros "[Hl | #HT]";
      last by iApply ewc_line_taint.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18 in Hw. cbn [EchoLinks.wr_banp] in Hw.
    destruct Hw as (ps' & -> & Hw).
    iApply ewc_line_of_pro. rewrite /ewc_pro.
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro. exact (wr_ban_done ps' cs I P Hw).
  Qed.

  (* =================================================================== *)
  (*  S9  ECHO'S EXIT PAYLOAD IS [ewc_post] AT [a = 0]                    *)
  (*                                                                     *)
  (*  [UEchoOut.echq v ps0 cs0 I0 P] is [fun _ => ech ... L] with         *)
  (*  [L = length (wl_line (drop 1 ws))] -- the LINE echo printed back,   *)
  (*  its command name dropped -- and [ech ... L = (turn v (P + L) ∗      *)
  (*  ps_lb v ps0 ∗ cs_lb v (cs0 ++ [0]) ∗ inp_lb v I0) ∨ T] under        *)
  (*  [echo_stage ps0 cs0 I0 ws P] (the premises below).  It is not       *)
  (*  nameable here (it sits above the file system), so the conversion is *)
  (*  stated at its body.  [last_ws I0 = ws] is what ties echo's word     *)
  (*  list to the input's last body; [wr_tail] is what the child was LENT *)
  (*  ([ewc_blk _ _ _ 0]'s shape) and carries unchanged.                  *)
  (* =================================================================== *)
  Lemma ewc_post_of_ech (v : era_pins) (ps0 cs0 : list nat)
      (I0 : list (bv 8)) (ws : list (list (bv 8))) (P : nat) :
    rest_of I0 = [] ->
    nlines I0 = S (length cs0) ->
    last_ws I0 = ws ->
    P = length (proc_before ps0 cs0 I0) ->
    pro_pin ps0 cs0 I0 ->
    wr_tail ps0 cs0 ->
    ((turn v (P + length (wl_line (drop 1 ws)))%nat ∗ ps_lb v ps0
      ∗ cs_lb v (cs0 ++ [0%nat]) ∗ inp_lb v I0) ∨ T) -∗
    ewc_post v I0 0%nat.
  Proof using Persistent0.
    intros Hr Hn Hws HP Hpin Ht.
    assert (Hidx : (length (line_alts_of (last_ws I0) !!! 0%nat) - 2)%nat
                   = length (wl_line (drop 1 ws)))
      by (rewrite Hws (line_alts_of_0_length ws); lia).
    rewrite /ewc_post Hidx /ewc_blk.
    destruct (length (wl_line (drop 1 ws))) as [| m] eqn:Hm.
    { exfalso. pose proof (wl_line_pos (drop 1 ws)). lia. }
    iIntros "[(Htn & #Hps & #Hcs & #HE) | #HT]"; last by iRight.
    iLeft. iExists ps0, cs0, P. cbn [blkcs]. iFrame "Htn Hps Hcs HE".
    iPureIntro. split; [| exact Ht].
    rewrite /wr_blk. split_and!;
      [exact Hpin | exact Hr | exact Hn | exact HP].
  Qed.

  (* ...and the lend's other end: [ewc_blk _ _ _ 0] unfolds to the turn
     bundle at the stage echo's constructor asks for, plus [wr_blk_t_stage] *)
  Lemma ewc_blk_0_lend (v : era_pins) (I : list (bv 8)) (a : nat) :
    ewc_blk v I a 0%nat -∗
    (∃ ps cs P : _, ⌜wr_blk_t ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ T.
  Proof using Persistent0.
    rewrite /ewc_blk. cbn [blkcs]. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    rewrite Nat.add_0_r. iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
    by iPureIntro.
  Qed.

  (* ...and the LEND's other end, pinned: what sh's fork hands its child
     is the turn bundle at the stage echo's paid entry asks for
     ([UEchoOut.echo_uexec_slot_at], through [wr_blk_t_stage]) *)
  Lemma ewc_lcred_blk_lend (k : nat) (I : list (bv 8)) :
    ewc_lcred k I 3%nat -∗
    ∃ v : era_pins,
      era_pin γ k v
      ∗ ((∃ ps cs P : _, ⌜wr_blk_t ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
            ∗ cs_lb v cs ∗ inp_lb v I) ∨ T).
  Proof using Persistent0.
    rewrite /ewc_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". cbn [ewc_lpr].
    iApply (ewc_blk_0_lend v I 0%nat with "Hc").
  Qed.

  (* ...or the shell's own panic line's first byte ([a = 3]): the fork
     that failed pays "fork\n" from the block it was owed *)
  Lemma ewc_lcred_blk_panic (k : nat) (I : list (bv 8)) :
    ewc_lcred k I 3%nat -∗
    ∃ v : era_pins, era_pin γ k v ∗ ewc_panic v I 0%nat.
  Proof using .
    rewrite /ewc_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". cbn [ewc_lpr]. rewrite /ewc_panic.
    iApply (ewc_blk_0 v I 0%nat 3%nat with "Hc").
  Qed.

End echo_links_line.
