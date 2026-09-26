(* EchoOut.v -- E5's APPLICATION CLAIM, THE IRIS HALF (lane ECHO-OUT).

   Design of record: the coordinator's E5 DESIGN PAGE of 2026-09-15
   (scratchpad e5-design-page.md), section 2, which REPLACES the
   ledger-anchored shape of REVISIONS 4-8: CLAIM-RESIDENT STATE, NO LEDGER
   IN ANY LINK.

   WHY THE STATE IS IN THE CLAIM AND NOT IN THE LEDGER.  The two things
   that forced the ledger-anchored shape are both gone.  [App.Happ_boot]
   founds nothing any more (milestone E moved the founding to [App.Hpow],
   which is the ONE step per era that runs the ledger and may mint linear
   content), and [App.Happ_echo] is a CLOSED entailment with no observation
   handle, so a link fired inside the echo shift cannot reach the ledger at
   all.  So each era's authorities -- its cursor, its line choices, its
   echoed list and its delivered count -- live in the PORT'S CLAIM, and the
   ledger keeps only what is about the HISTORY: the taint counter, the era
   map (whose authority is spent at [echo_led_pow_cl] and nowhere else) and
   the phi conjunct.

   THE INDEX IS THE ERA NUMBER [k := S gen_id] (ambient [RiscvLang.GenId]),
   not a ghost name: [riscv_cons_res k ho H], every link at [k],
   [app_cons/app_boot A c k].  The kernel STAMPS every history it hands the
   application with [⌜obs_boots h = S gen_id⌝].  A link at [k] therefore
   knows [k = obs_boots h] purely, and no history is ever compared against
   the ledger's inside a link -- which is essential, because the observation
   AUTHORITY lives in the state interpretation.

   THE SHAPE (redesign R2/R3).  [ecl k ho H] is the TAINT (what the licence
   pays through) or the era's own arm, which holds the era's pin, its four
   authorities and the delivered count, together with [ecl_pure]'s account
   of the whole console history [H].

   THERE IS NO WINDOW COUNTER AND NO KERNEL-LENT TOKEN.  There were both,
   and here is why they are gone.  The echo's run used to be SPLIT -- the
   bytes went out through the output claim and the log entry was filed
   later through the input claim -- so [WpUart.cons_link] returned the input
   claim at exactly the log it was handed, [SpecConsoleintr.cons_echo_shift]
   was persistent, and the application's spec had to be total over
   interleavings cons.lock forbids but never states.  The kernel therefore
   LENT the application a per-era exclusive on the PLIC payload, and a
   [ghost_var nat] in QUARTERS made a second firing of one run meet five
   quarters.  Since the redesign the arm is a FIELD of the console history
   ([ConsLog.cons_hist]'s [ch_arm]) and every event steps it with the port
   invariant open, so a second open, a byte after the close and a second
   close are refuted by [ConsLog.cons_ev_ok] on the kernel's side and by the
   history's own shape on the application's.  The two descriptions the
   counter kept in step are ONE description.

   THE ERA'S FIRST WRITE needs no special step: [app_turn] (init's console
   credential, minted beside the claim at [echo_led_pow_cl] and carried to
   [App.Hinit_boot] by the kernel) is the era's cursor at zero, and at
   [P = 0] the paired claim's own [turn_auth] plus [pcount_zero] DERIVE
   [o_E so = [] /\ o_w so = []], hence [acc = []].  There is no founded arm
   to refute and no seed to spend.

   WHAT THE LINKS HAND THE PROGRAM (review S9).  A writer must prove
   [pending ps cs E !! length w = Some b] without holding any authority.  It
   gets a PERSISTENT lower bound of the era's line choices ([cs_lb]) and its
   cursor; [proc_stream_pcount] turns the two into the byte owed, because the
   process bytes of an era are one stream and the cursor is a position in it.
   [echo_write_link] and [echo_read_link] hand those back, which is what
   IO-LEAF and SH-LINE consume. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.     (* the parse: [rest_of], [nlines], [last_ws] --
                                 named directly here, and [Require Import] is
                                 not transitive for name visibility *)
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
(* ...and, for section 7, the kernel's own console contracts: the links the
   application's claims are wrapped onto, and the observation invariant the
   ledger lives in.  This file is BELOW [AppEcho] and ABOVE [WpUart], which
   is where the _CoqProject entry has always said the links belong. *)
Require Import RiscvPtsto.       (* [obsN], [obs_hist_lb_o],
                                    [riscv_cons_res], [riscvGS] *)
Require Import WpUart.           (* [out_link], [read_link], [cons_link],
                                    [cons_run], [chist_at], [uartN] *)
Require Import CtxIdDefs.           (* [CurCtx]: the echo obligation's context *)
Require Import SpecConsoleintr.  (* [cons_echo_shift], which is what
                                    [App.Happ_echo] asks of the
                                    application *)
(* as in EchoDisc / EchoOutPure: the Sail imports leave string_scope on top
   and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

(* ====================================================================== *)
(*  1.  THE TWO STAGES                                                     *)
(* ====================================================================== *)

(* E's HISTORIES ARE CYCLE SEGMENTS ([open_seg] of the history the byte was
   received at), not whole histories: [EchoOutPure]'s [E_index] counts with
   [ins], the discipline and [good_out] are per POWER CYCLE, and [acc]
   restarts at every era -- so instantiating [E_index] at whole histories is
   unsatisfiable from era 1 on.  Nothing in [EchoOutPure] moves: it is
   parametric in what E's first components are, and this file supplies
   segments ([EchoOutPure.open_seg_ends_in] is the one bridge). *)
Record ostage := MkO {
  o_ps : list nat;
  o_cs : list nat;
  o_E  : list (list mobs * bv 8);
  o_w  : list (bv 8);
}.
Definition ostage0 : ostage := MkO [] [] [] [].

(* ---- the two list moves the input's snoc laws are read through ---- *)

Lemma fmap_snd_snoc (E : list (list mobs * bv 8)) (x : list mobs * bv 8) :
  (snd <$> (E ++ [x])) = (snd <$> E) ++ [x.2].
Proof. by rewrite fmap_app. Qed.

Lemma epu_snoc_cases {A} (l : list A) : l = [] \/ exists u x, l = u ++ [x].
Proof.
  induction l as [| a l IH]; [by left |]. right.
  destruct IH as [-> | (u & x & ->)].
  - by exists [], a.
  - by exists (a :: u), x.
Qed.

Lemma epu_removelast_take {A} (l : list A) :
  removelast l = take (length l - 1)%nat l.
Proof.
  induction l as [| a l IH]; [done |].
  destruct l as [| b l']; [reflexivity |].
  change (removelast (a :: b :: l')) with (a :: removelast (b :: l')).
  rewrite IH.
  replace (length (a :: b :: l') - 1)%nat with (S (length (b :: l') - 1)%nat)
    by (cbn [length]; lia).
  reflexivity.
Qed.

Lemma epu_removelast_prefix {A} (l : list A) : removelast l `prefix_of` l.
Proof. rewrite epu_removelast_take. apply prefix_take. Qed.

Lemma epu_prefix_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> removelast l `prefix_of` removelast l'.
Proof.
  intros Hp. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Ht : take (length l - 1)%nat l = take (length l - 1)%nat l').
  { destruct Hp as [z ->]. rewrite (take_app_le l z (length l - 1)%nat); [done | lia]. }
  rewrite !epu_removelast_take Ht. apply prefix_take_le. lia.
Qed.

Lemma epu_prefix_of_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> l <> l' -> l `prefix_of` removelast l'.
Proof.
  intros Hp Hne. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Hlt : (length l < length l')%nat).
  { destruct (decide (length l = length l')) as [He | He]; [| lia].
    exfalso. exact (Hne (prefix_length_eq _ _ Hp ltac:(lia))). }
  assert (Hl : l = take (length l) l').
  { destruct Hp as [z ->]. by rewrite take_app_length. }
  rewrite epu_removelast_take {1}Hl. apply prefix_take_le. lia.
Qed.

(* A COMPLETED INPUT LOSES EXACTLY ITS LAST LINE when its last byte goes.
   This is the one arithmetic fact the length laws below need, and it
   replaces [div_succ_of_mod0]: where the divide-by-17 shape had to turn a
   quotient into its predecessor, the parse reads the cut's own snoc law. *)
Lemma nlines_removelast (I : list (bv 8)) :
  rest_of I = [] -> nlines (removelast I) = (nlines I - 1)%nat.
Proof.
  intros Hr. destruct (epu_snoc_cases I) as [-> | (u & x & ->)].
  - cbn [removelast]. rewrite nlines_nil. lia.
  - destruct (decide (x = wl_nl)) as [-> | Hx].
    + rewrite epu_removelast_snoc nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other u x Hx) in Hr.
      by destruct (app_eq_nil (rest_of u) [x] Hr) as [_ Hb].
Qed.

(* ...and an input that stops at a newline has started no further line *)
Lemma nstarted_rest_nil (I : list (bv 8)) :
  rest_of I = [] -> nstarted I = nlines I.
Proof.
  intros Hr. rewrite /nstarted Hr. case_decide as Hd;
    [lia | by destruct (Hd eq_refl)].
Qed.

(* ONE MORE BYTE STARTS AT MOST ONE MORE LINE, whichever byte it is: a
   newline completes the line it was typing and a body byte opens one. *)
Lemma nstarted_snoc (I : list (bv 8)) (b : bv 8) :
  nstarted (I ++ [b]) = S (nlines I).
Proof.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - apply nstarted_snoc_nl.
  - by apply nstarted_snoc_other.
Qed.

(* THE LINE A BLOCK ANSWERS is the LAST BODY of the input its echo closed,
   and that is the one the parser's [last_ws] names.  Unconditional: with
   no complete line both sides are the empty word list. *)
Lemma last_ws_lta (I : list (bv 8)) :
  last_ws I = wl_words (bodies_of I !!! (nlines I - 1)%nat).
Proof.
  rewrite /last_ws list_lookup_total_alt last_lookup /nlines Nat.sub_1_r.
  reflexivity.
Qed.

(* the OUTPUT claim's pure fact.

   THE STAGE IS READ THROUGH THE PARSER, NOT DIVIDED.  With a line per round
   there is no line length to divide by, so nothing here counts echoes: what
   the transcript turns on is the ERA'S INPUT [snd <$> o_E so] -- the bytes
   the console has echoed so far -- read by [LineWords]'s cut into its
   COMPLETE bodies ([nlines]) and the REST after the last newline
   ([rest_of]).  [pro_pin] is stated at that input, and [E_byte]'s
   positional law ("E's j-th byte is byte [j mod 17] of the line") is
   [E_disc], "the bytes of E parse" -- the only thing left of it once no
   position determines a byte.

   THE SAME-CYCLE FACTS LIVE HERE, AT THE CLAIM'S OWN WITNESS [ho], and not
   in the ledger (lane ECHO-OUT, section 7).  The reason is the ECHO: its
   links fire at the consputc STORES, which are later than the history the
   byte arrived at, so the ledger the shift opens is at a history the shift
   cannot name -- and no link may compare a history against the ledger's,
   because the observation AUTHORITY lives in the state interpretation.  At
   the claim's witness there is no such problem: the ECHO re-establishes the
   facts at its own [h] out of the INPUT claim's per-entry stamps, and the
   DRAIN lifts them to the run's history with [App.Htx]'s own premise
   [ho `prefix_of` h] plus the two era stamps ([EchoOutPure.
   open_seg_prefix_boots]).  The ledger is then HISTORY-FREE. *)
Definition eout_pure (k : nat) (ho : list mobs) (so : ostage)
    (acc : list (bv 8)) : Prop :=
  acc = D (o_ps so) (o_cs so) (o_E so) ++ o_w so
  /\ o_w so `prefix_of` pending (o_ps so) (o_cs so) (o_E so)
  /\ E_index (o_E so)
  /\ E_disc (o_E so)
  /\ Forall (fun a => (a < length pro_alts)%nat) (o_ps so)
  /\ pro_pin (o_ps so) (o_cs so) (snd <$> o_E so)
  /\ Forall (fun i => (i < 4)%nat) (o_cs so)
  /\ Forall (fun x => disc_seg x.1) (o_E so)
  /\ Forall (fun x => x.1 `prefix_of` open_seg ho) (o_E so)
  /\ (length (o_E so) <= length (ins (open_seg ho)))%nat
  /\ (o_E so = [] \/ obs_boots ho = k).

(* THE LEDGER'S LENGTH LAW FOR THE CHOICE LIST (REVISION 7(d)).  [cs] records
   one alternative per COMPLETED line, at index [q-1] for line [q], and it
   grows at the FIRST BYTE of that line's continuation -- which is the only
   moment at which the program knows which alternative it is taking.  So the
   list is one short exactly while the writer is standing at a block
   boundary with nothing of the block written ([o_w so = []] and the input
   ending at a newline, [rest_of _ = []]), and the prologue (block 0) grows
   it not at all -- which the nat subtraction below says for free. *)
Definition cs_len_ok (so : ostage) : Prop :=
  length (o_cs so)
  = (if decide (o_w so = [] /\ rest_of (snd <$> o_E so) = [])
     then (nlines (snd <$> o_E so) - 1)%nat
     else nlines (snd <$> o_E so)).

(* ---- the three moves of [cs_len_ok], as pure arithmetic ---- *)

(* [pending] is EMPTY mid-line, and at the head of the transcript while
   the boot round has no letter filed ([EchoDisc.pro_of_nil]); at every
   OTHER completed line the stage owes a whole line alternative, which is
   never empty. *)
Lemma pending_at_nonnil (ps cs : list nat) (I : list (bv 8)) :
  Forall (fun i => (i < 4)%nat) cs ->
  I <> [] -> rest_of I = [] ->
  pending_at ps cs I <> [].
Proof.
  intros HF Hne Hr. rewrite /pending_at.
  rewrite decide_False; [| exact Hne]. rewrite decide_True; [| exact Hr].
  rewrite /alt_cont. intros Hc. apply app_eq_nil in Hc as [Hc _].
  exact (line_alts_of_nonnil _ _ (cs_ok_of_Forall _ HF _) Hc).
Qed.

Lemma pending_nonnil (ps cs : list nat) (E : list (list mobs * bv 8)) :
  Forall (fun i => (i < 4)%nat) cs ->
  (snd <$> E) <> [] -> rest_of (snd <$> E) = [] ->
  pending ps cs E <> [].
Proof. rewrite /pending. apply pending_at_nonnil. Qed.

(* ...so an EMPTY [pending] at a completed line means the boot block, and
   there the choice list's two readings coincide (both are [0]) *)
Lemma pending_nil_inv (ps cs : list nat) (E : list (list mobs * bv 8)) :
  Forall (fun i => (i < 4)%nat) cs ->
  rest_of (snd <$> E) = [] ->
  pending ps cs E = [] -> (snd <$> E) = [].
Proof.
  intros HF Hr Hnil.
  destruct (decide ((snd <$> E) = [])) as [? | Hne]; [done | exfalso].
  exact (pending_nonnil ps cs E HF Hne Hr Hnil).
Qed.

Lemma cs_len_ok_inv (so : ostage) :
  cs_len_ok so ->
  ((o_w so = [] /\ rest_of (snd <$> o_E so) = [])
     /\ length (o_cs so) = (nlines (snd <$> o_E so) - 1)%nat)
  \/ (~ (o_w so = [] /\ rest_of (snd <$> o_E so) = [])
     /\ length (o_cs so) = nlines (snd <$> o_E so)).
Proof.
  rewrite /cs_len_ok. case_decide as Hb; intros Hc.
  - left. by split.
  - right. by split.
Qed.

Lemma cs_len_ok_intro (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) :
  ((w = [] /\ rest_of (snd <$> E) = []) ->
     length cs = (nlines (snd <$> E) - 1)%nat) ->
  (~ (w = [] /\ rest_of (snd <$> E) = []) ->
     length cs = nlines (snd <$> E)) ->
  cs_len_ok (MkO ps cs E w).
Proof.
  rewrite /cs_len_ok. cbn [o_ps o_cs o_E o_w]. intros H1 H2. case_decide as Hb.
  - by apply H1.
  - by apply H2.
Qed.

Lemma cs_len_ok_mid (so : ostage) :
  cs_len_ok so -> o_w so <> [] ->
  length (o_cs so) = nlines (snd <$> o_E so).
Proof.
  intros Hc Hw. destruct (cs_len_ok_inv so Hc) as [[[Hw' _] _] | [_ ?]];
    [done | done].
Qed.

(* THE ECHO does not move the choice list: it closes the block the writer
   has just finished, and the next block's alternative is chosen by the
   WRITE that starts it. *)
Lemma cs_len_ok_echo (so : ostage) (x : list mobs * bv 8) :
  Forall (fun i => (i < 4)%nat) (o_cs so) ->
  o_w so = pending (o_ps so) (o_cs so) (o_E so) ->
  cs_len_ok so ->
  cs_len_ok (MkO (o_ps so) (o_cs so) (o_E so ++ [x]) []).
Proof.
  intros HF Hw Hc.
  assert (Hq : length (o_cs so) = nlines (snd <$> o_E so)).
  { destruct (cs_len_ok_inv so Hc) as [[[Hw' Hm] Hq] | [_ Hq]]; [| exact Hq].
    (* an empty block at a completed line is the boot block with nothing
       typed: both readings of the list's length are zero there *)
    pose proof (pending_nil_inv (o_ps so) (o_cs so) (o_E so) HF Hm
                  ltac:(by rewrite -Hw)) as Hz.
    rewrite Hz in Hq |- *. rewrite nlines_nil in Hq |- *. lia. }
  apply cs_len_ok_intro; rewrite (fmap_snd_snoc (o_E so) x) Hq.
  - intros [_ Hm]. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
    + rewrite Hx nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other _ _ Hx) in Hm.
      by destruct (app_eq_nil (rest_of (snd <$> o_E so)) [x.2] Hm) as [_ Hb].
  - intros Hne. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
    + exfalso. apply Hne. split; [reflexivity |].
      rewrite Hx. apply rest_of_snoc_nl.
    + by rewrite (nlines_snoc_other _ _ Hx).
Qed.

(* A WRITE INSIDE A BLOCK does not move it either. *)
Lemma cs_len_ok_write (so : ostage) (b : bv 8) :
  cs_len_ok so ->
  (o_w so <> [] \/ rest_of (snd <$> o_E so) <> [] \/ (snd <$> o_E so) = []) ->
  cs_len_ok (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])).
Proof.
  intros Hc Hcase. apply cs_len_ok_intro.
  { intros [Hw _]. exfalso.
    by destruct (app_eq_nil (o_w so) [b] Hw) as [_ Hb]. }
  intros _. destruct (cs_len_ok_inv so Hc) as [[[Hw Hm] Hq] | [_ Hq]];
    [| exact Hq].
  destruct Hcase as [Hw' | [Hm' | Hn]]; [done | done |].
  rewrite Hq Hn nlines_nil. lia.
Qed.

(* ...and A WRITE AT A BLOCK'S FIRST BYTE grows it by exactly one
   (REVISION 7(d)). *)
Lemma cs_len_ok_blk (so : ostage) (a : nat) (b : bv 8) :
  rest_of (snd <$> o_E so) = [] ->
  (snd <$> o_E so) <> [] ->
  o_w so = [] ->
  cs_len_ok so ->
  cs_len_ok (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]).
Proof.
  intros Hr Hne Hw Hc.
  pose proof (nlines_pos_of_rest_nil (snd <$> o_E so) Hne Hr) as Hpos.
  destruct (cs_len_ok_inv so Hc) as [[_ Hq] | [Hne' _]]; last first.
  { exfalso. by apply Hne'. }
  apply cs_len_ok_intro.
  { intros [Hb _]. discriminate. }
  intros _. rewrite length_app. cbn [length]. rewrite Hq. lia.
Qed.

(* THE LEDGER'S LENGTH LAW FOR THE PROLOGUE RESOLUTION -- the TWIN of
   [cs_len_ok], and what makes the prologue's CHOICE readable off the
   cursor.  [cs_len_ok] pins how many LINE alternatives have been filed by
   the writer's position; this pins how much of the OPEN ROUND's resolution
   has been.  Without it a claim whose current round is already SETTLED --
   [pro_of] one alternative longer, so [pending_at] longer and the writer's
   [o_w] a proper prefix of it -- is a perfectly consistent state, and the
   prologue-choice write cannot tell it from the one it is actually in.

   THE ROUND A STAGE STANDS IN is [ps_round]: one per line that took
   alternative 3 (the shell's own fork panic), round 0 at the head of the
   transcript.  A block OPENS that round only at those two places
   ([ps_opens]); every other block owes no prologue at all, which is why the
   second conjunct is guarded -- unguarded it is simply false.

   THE TWO CONJUNCTS.
   (A) NOTHING IS FILED FOR A ROUND THAT HAS NOT OPENED: past the current
       round the resolution is empty.  This is what makes the block-first
       write that OPENS the next round (alternative 3) find it open.
   (B) EVERY ENTRY THE ROUND HAS IS ON THE WIRE: a prefix of the resolution
       that gives a SHORTER prologue than the stage's own was passed by the
       writer strictly.  Since an open prologue ends at a banner and filing
       an alternative appends at least its first byte
       ([EchoDisc.pro_of_open_snoc_lt]), this says exactly "the round is
       settled only once the writer has written past the block's banner",
       and it is what reconciles a writer's [~ pro_done] with the claim. *)
Definition ps_round (so : ostage) : nat :=
  pro_idx (o_cs so) (nlines (snd <$> o_E so)).

Definition ps_opens (so : ostage) : Prop :=
  (snd <$> o_E so) = []
  \/ (rest_of (snd <$> o_E so) = []
      /\ o_cs so !!! (nlines (snd <$> o_E so) - 1)%nat = 3%nat).

Definition ps_len_ok (so : ostage) : Prop :=
  pro_from (S (ps_round so)) (o_ps so) = []
  /\ (ps_opens so ->
      forall ps' : list nat, ps' `prefix_of` o_ps so ->
        pro_of (pro_from (ps_round so) ps')
          <> pro_of (pro_from (ps_round so) (o_ps so)) ->
        (length (pending_at ps' (o_cs so) (snd <$> o_E so))
         < length (o_w so))%nat).

(* the rounds a stage has NOT opened are empty in it, and stay empty as the
   index moves up -- the one consequence of (A) the three moves spend *)
Lemma ps_len_ok_empty_above (so : ostage) (R : nat) :
  ps_len_ok so -> (ps_round so <= R)%nat -> pro_from (S R) (o_ps so) = [].
Proof.
  intros [HA _] HR.
  replace (S R) with (S (ps_round so) + (R - ps_round so))%nat by lia.
  rewrite -pro_from_add HA. apply pro_from_nil.
Qed.

Lemma ps_len_ok_0 : ps_len_ok ostage0.
Proof.
  rewrite /ps_len_ok /ps_round /ostage0. cbn [o_ps o_cs o_E o_w]. split.
  - apply pro_from_nil.
  - intros _ ps' Hp Hne. exfalso. apply Hne.
    by rewrite (prefix_nil_inv ps' Hp).
Qed.

(* ---- the three moves, as [cs_len_ok_echo]/[_write]/[_blk] are ---- *)

(* A WRITE INSIDE THE BLOCK moves neither the round nor the resolution, and
   only lengthens what has been written. *)
Lemma ps_len_ok_write (so : ostage) (b : bv 8) :
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])).
Proof.
  intros [HA HB]. rewrite /ps_len_ok /ps_round /ps_opens in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *. split; [exact HA |].
  intros Ho ps' Hp Hne. rewrite (length_app (o_w so) [b]). cbn [length].
  pose proof (HB Ho ps' Hp Hne). lia.
Qed.

(* A WRITE AT A BLOCK'S FIRST BYTE may OPEN a round -- exactly when the
   alternative it files is 3 -- and (A) says that round is untouched. *)
Lemma ps_len_ok_blk (so : ostage) (a : nat) (b : bv 8) :
  rest_of (snd <$> o_E so) = [] ->
  (snd <$> o_E so) <> [] ->
  length (o_cs so) = (nlines (snd <$> o_E so) - 1)%nat ->
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]).
Proof.
  intros Hr Hne Hq Hok.
  pose proof (nlines_pos_of_rest_nil (snd <$> o_E so) Hne Hr) as Hpos.
  pose proof Hok as [HA HB].
  rewrite /ps_len_ok /ps_round /ps_opens in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *.
  assert (Hold : pro_idx (o_cs so) (nlines (snd <$> o_E so))
                 = pro_idx (o_cs so) (nlines (snd <$> o_E so) - 1)%nat).
  { replace (nlines (snd <$> o_E so))
      with (S (nlines (snd <$> o_E so) - 1))%nat at 1 by lia.
    apply pro_idx_Sne.
    rewrite list_lookup_total_alt
      (lookup_ge_None_2 (o_cs so) (nlines (snd <$> o_E so) - 1)%nat
         ltac:(lia)).
    by vm_compute. }
  assert (Hnew : (pro_idx (o_cs so) (nlines (snd <$> o_E so))
                  <= pro_idx (o_cs so ++ [a]) (nlines (snd <$> o_E so)))%nat).
  { rewrite Hold.
    replace (nlines (snd <$> o_E so))
      with (S (nlines (snd <$> o_E so) - 1))%nat at 2 by lia.
    rewrite pro_idx_S
      (pro_idx_app_le (o_cs so) [a] (nlines (snd <$> o_E so) - 1)%nat
         ltac:(lia)).
    lia. }
  split.
  - apply (ps_len_ok_empty_above so); [exact Hok |].
    rewrite /ps_round. exact Hnew.
  - intros Ho ps' Hp Hne2. exfalso.
    destruct Ho as [Hz | [_ H3]]; [by destruct (Hne Hz) |].
    assert (Ha3 : a = 3%nat).
    { rewrite list_lookup_total_alt lookup_app_r in H3; [| lia].
      rewrite Hq Nat.sub_diag in H3. by cbn in H3. }
    assert (Heq : pro_idx (o_cs so ++ [a]) (nlines (snd <$> o_E so))
                  = S (pro_idx (o_cs so) (nlines (snd <$> o_E so)))).
    { rewrite Hold
        -(pro_idx_app_le (o_cs so) [a] (nlines (snd <$> o_E so) - 1)%nat
            ltac:(lia)).
      replace (nlines (snd <$> o_E so))
        with (S (nlines (snd <$> o_E so) - 1))%nat at 1 by lia.
      apply pro_idx_S3. exact H3. }
    rewrite Heq in Hne2. apply Hne2.
    assert (Hnil : pro_from
                     (S (pro_idx (o_cs so) (nlines (snd <$> o_E so))))
                     (o_ps so) = []) by exact HA.
    assert (Hnil' : pro_from
                      (S (pro_idx (o_cs so) (nlines (snd <$> o_E so))))
                      ps' = []).
    { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
    by rewrite Hnil Hnil'.
Qed.

(* THE ECHO closes a line; when the line it closes took alternative 3 the
   round it opens is, again, one the resolution has not touched. *)
Lemma ps_len_ok_echo (so : ostage) (x : list mobs * bv 8) :
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so) (o_cs so) (o_E so ++ [x]) []).
Proof.
  intros Hok. pose proof Hok as [HA HB].
  rewrite /ps_len_ok /ps_round /ps_opens in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *.
  rewrite (fmap_snd_snoc (o_E so) x).
  assert (Hmono : (pro_idx (o_cs so) (nlines (snd <$> o_E so))
                   <= pro_idx (o_cs so)
                        (nlines ((snd <$> o_E so) ++ [x.2])))%nat)
    by (apply pro_idx_mono, nlines_app_le).
  split.
  - apply (ps_len_ok_empty_above so); [exact Hok |].
    rewrite /ps_round. exact Hmono.
  - intros Ho ps' Hp Hne. exfalso.
    destruct Ho as [Hz | [Hr H3]].
    { by destruct (app_eq_nil (snd <$> o_E so) [x.2] Hz) as [_ Hb]. }
    assert (Hx : x.2 = wl_nl).
    { destruct (decide (x.2 = wl_nl)) as [Hx | Hx]; [exact Hx | exfalso].
      rewrite (rest_of_snoc_other (snd <$> o_E so) x.2 Hx) in Hr.
      by destruct (app_eq_nil (rest_of (snd <$> o_E so)) [x.2] Hr) as [_ Hb]. }
    rewrite Hx (nlines_snoc_nl (snd <$> o_E so)) in H3.
    rewrite Hx (nlines_snoc_nl (snd <$> o_E so)) in Hne.
    replace (S (nlines (snd <$> o_E so)) - 1)%nat
      with (nlines (snd <$> o_E so)) in H3 by lia.
    assert (Heq : pro_idx (o_cs so) (S (nlines (snd <$> o_E so)))
                  = S (pro_idx (o_cs so) (nlines (snd <$> o_E so))))
      by (apply pro_idx_S3; exact H3).
    rewrite Heq in Hne. apply Hne.
    assert (Hnil : pro_from
                     (S (pro_idx (o_cs so) (nlines (snd <$> o_E so))))
                     (o_ps so) = []) by exact HA.
    assert (Hnil' : pro_from
                      (S (pro_idx (o_cs so) (nlines (snd <$> o_E so))))
                      ps' = []).
    { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
    by rewrite Hnil Hnil'.
Qed.

(* ...AND THE FOURTH MOVE, the one the prologue-choice write makes: filing
   the open round's alternative CLOSES it (nothing is left over, so (A)
   holds again) and puts its first byte on the wire (so (B) does). *)
Lemma ps_len_ok_pro (so : ostage) (a : nat) (b : bv 8) :
  (ps_round so <= pro_rounds (o_ps so))%nat ->
  ~ pro_done (pro_from (ps_round so) (o_ps so)) ->
  o_w so = pending (o_ps so) (o_cs so) (o_E so) ->
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so ++ [b])).
Proof.
  intros Hle Hnd Hw [HA HB].
  rewrite /ps_len_ok /ps_round /ps_opens in HA, HB, Hle, Hnd |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB, Hle, Hnd |- *. split.
  - replace (S (pro_idx (o_cs so) (nlines (snd <$> o_E so))))
      with (pro_idx (o_cs so) (nlines (snd <$> o_E so)) + 1)%nat by lia.
    rewrite -pro_from_add (pro_from_snoc_le _ (o_ps so) a Hle).
    cbn [pro_from]. by apply pro_tail_open_snoc.
  - intros Ho ps' Hp Hne. rewrite (length_app (o_w so) [b]). cbn [length].
    destruct (decide (length ps' <= length (o_ps so))%nat) as [Hlen | Hlen].
    + assert (Hp2 : ps' `prefix_of` o_ps so).
      { destruct (prefix_weak_total ps' (o_ps so) (o_ps so ++ [a]) Hp
                    ltac:(by eexists)) as [H | H]; [exact H |].
        rewrite (prefix_length_eq _ _ H ltac:(lia)). reflexivity. }
      pose proof (prefix_length _ _ (pending_at_ps_mono ps' (o_ps so)
                    (o_cs so) (snd <$> o_E so) Hp2)) as Hlp.
      rewrite -/(pending (o_ps so) (o_cs so) (o_E so)) -Hw in Hlp. lia.
    + rewrite (prefix_length_eq ps' (o_ps so ++ [a]) Hp) in Hne;
        last by (rewrite (length_app (o_ps so) [a]); cbn [length]; lia).
      by destruct (Hne eq_refl).
Qed.

(* E's entries, read off the log: the ECHOED ones with their histories
   projected to the cycle.  [EchoOutPure.echoed] keeps the raw histories --
   which is what [read_window_prefix] is stated over -- and this is its
   cycle-relative image, which is what the stage carries. *)
Definition seg_of (l : list (list mobs * bv 8)) : list (list mobs * bv 8) :=
  (fun x => (open_seg x.1, x.2)) <$> l.

Lemma seg_of_snd (l : list (list mobs * bv 8)) : snd <$> seg_of l = snd <$> l.
Proof.
  induction l as [| x l IH]; [done |].
  change (seg_of (x :: l)) with ((open_seg x.1, x.2) :: seg_of l).
  by rewrite !fmap_cons IH.
Qed.

Lemma seg_of_app (l1 l2 : list (list mobs * bv 8)) :
  seg_of (l1 ++ l2) = seg_of l1 ++ seg_of l2.
Proof. by rewrite /seg_of fmap_app. Qed.

Lemma seg_of_length (l : list (list mobs * bv 8)) : length (seg_of l) = length l.
Proof. by rewrite /seg_of length_fmap. Qed.

(* ====================================================================== *)
(*  1b.  THE ERA'S PROCESS-BYTE CURSOR (review S2)                         *)
(* ====================================================================== *)

(* THE ERA'S PROCESS BYTES AS ONE STREAM, READ OFF THE INPUT.  One
   [pending_at] block per byte the console has echoed, in order: the
   prologue at the empty input, a line's continuation at every input that
   has just completed a line, nothing in between.  [proc_before ps cs I] is
   what the stage owes STRICTLY BEFORE input [I], and [proc_stream ps cs I]
   is that plus the block owed AT [I].

   A [Fixpoint] from the LEFT with the input read so far as the accumulator,
   for [EchoOutPure.D_from]'s reason exactly: a recursion on the right does
   not reduce under [cbn] on an opaque tail.  The two recursions have the
   SAME SHAPE, which is what makes [pcount] literally an index into this
   list ([proc_stream_pcount]). *)
Fixpoint proc_before_from (ps cs : list nat) (pre I : list (bv 8))
  : list (bv 8) :=
  match I with
  | [] => []
  | b :: I' => pending_at ps cs pre ++ proc_before_from ps cs (pre ++ [b]) I'
  end.

Definition proc_before (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  proc_before_from ps cs [] I.

Definition proc_stream (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  proc_before ps cs I ++ pending_at ps cs I.

Lemma proc_before_nil ps cs : proc_before ps cs [] = [].
Proof. reflexivity. Qed.

Lemma proc_before_from_app ps cs pre I1 I2 :
  proc_before_from ps cs pre (I1 ++ I2)
  = proc_before_from ps cs pre I1 ++ proc_before_from ps cs (pre ++ I1) I2.
Proof.
  revert pre. induction I1 as [| b I1 IH]; intros pre.
  - cbn [proc_before_from app]. by rewrite app_nil_r.
  - cbn [app proc_before_from]. rewrite IH app_assoc.
    by rewrite epu_app_snoc.
Qed.

Lemma proc_before_app ps cs I k :
  proc_before ps cs (I ++ k)
  = proc_before ps cs I ++ proc_before_from ps cs I k.
Proof. rewrite /proc_before proc_before_from_app. by cbn [app]. Qed.

(* the stream through [I] is what the NEXT input's [proc_before] starts
   from -- the law the echo's cursor move is one line off *)
Lemma proc_before_snoc ps cs I b :
  proc_before ps cs (I ++ [b]) = proc_stream ps cs I.
Proof.
  rewrite proc_before_app /proc_stream. cbn [proc_before_from].
  by rewrite app_nil_r.
Qed.

Lemma proc_before_prefix ps cs I I' :
  I `prefix_of` I' -> proc_before ps cs I `prefix_of` proc_before ps cs I'.
Proof. intros [z ->]. rewrite proc_before_app. by eexists. Qed.

Lemma proc_stream_before ps cs I I' :
  I `prefix_of` I' -> I <> I' ->
  proc_stream ps cs I `prefix_of` proc_before ps cs I'.
Proof.
  intros [z Hz] Hne. destruct z as [| b z].
  { exfalso. apply Hne. by rewrite Hz app_nil_r. }
  rewrite Hz proc_before_app /proc_stream. cbn [proc_before_from].
  rewrite app_assoc. by eexists.
Qed.

Lemma proc_stream_mono ps cs I I' :
  I `prefix_of` I' -> proc_stream ps cs I `prefix_of` proc_stream ps cs I'.
Proof.
  intros Hp. destruct (decide (I = I')) as [-> | Hne]; [reflexivity |].
  etrans; [exact (proc_stream_before ps cs I I' Hp Hne) |].
  rewrite /proc_stream. by eexists.
Qed.

(* THE CURSOR: how many PROCESS bytes the transcript [D ps cs E ++ w]
   contains -- every block owed strictly before the era's input, plus what
   is written of the block owed at it.  DEFINITIONALLY an index into
   [proc_stream], which is why the two lookup laws below are one
   [lookup_app] each. *)
Definition pcount (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) : nat :=
  (length (proc_before ps cs (snd <$> E)) + length w)%nat.

(* A WRITE MOVES IT BY ONE *)
Lemma pcount_write ps cs E w b :
  pcount ps cs E (w ++ [b]) = S (pcount ps cs E w).
Proof. rewrite /pcount length_app /=. lia. Qed.

(* ...AND THE ECHO LEAVES IT ALONE, which is the whole point: the block the
   echo folds into [D] is exactly the [w] that was already counted. *)
Lemma pcount_echo ps cs E x w :
  w = pending ps cs E -> pcount ps cs (E ++ [x]) [] = pcount ps cs E w.
Proof.
  intros ->. rewrite /pcount (fmap_snd_snoc E x).
  rewrite (proc_before_snoc ps cs (snd <$> E) x.2) /proc_stream /pending.
  rewrite length_app. cbn [length]. lia.
Qed.

(* THE CURSOR IS AN INDEX INTO THE STREAM.  Forward: what the stage owes at
   [length w] is what the stream has at [pcount]. *)
Lemma proc_stream_pcount ps cs E w b :
  pending ps cs E !! length w = Some b ->
  proc_stream ps cs (snd <$> E) !! pcount ps cs E w = Some b.
Proof.
  intros Hb. rewrite /proc_stream /pcount lookup_app_r; [| lia].
  replace (length (proc_before ps cs (snd <$> E)) + length w
           - length (proc_before ps cs (snd <$> E)))%nat with (length w) by lia.
  exact Hb.
Qed.

(* ...and back, which is the direction a WRITER needs.  THE STRICTNESS
   PREMISE IS NOT DECORATION: at [length w = length (pending ps cs E)] the
   cursor indexes the FIRST byte of the NEXT block, which the stream has and
   the stage does not owe -- writing it would be writing past the
   continuation, before the echo that closes the line.  The program supplies
   it; see [write_stage_byte]. *)
Lemma proc_stream_pcount_inv ps cs E w I b :
  (snd <$> E) `prefix_of` I ->
  (length w < length (pending ps cs E))%nat ->
  proc_stream ps cs I !! pcount ps cs E w = Some b ->
  pending ps cs E !! length w = Some b.
Proof.
  intros HI Hlt Hl.
  destruct (lookup_lt_is_Some_2 (pending ps cs E) (length w) Hlt) as [b' Hb'].
  pose proof (proc_stream_pcount ps cs E w b' Hb') as Hfwd.
  assert (Heq : proc_stream ps cs I !! pcount ps cs E w = Some b')
    by (eapply prefix_lookup_Some;
        [exact Hfwd | by apply proc_stream_mono]).
  assert (Hbb : b = b') by congruence. by rewrite Hbb.
Qed.

(* a LOWER BOUND reads the same choice wherever it reaches *)
Lemma lookup_total_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> (i < length cs0)%nat -> cs !!! i = cs0 !!! i.
Proof.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

(* THE CHOICES ARE READ ONLY BELOW THE LAST COMPLETED LINE, so a lower bound
   of [cs] fixes the block a stage owes (review S9) -- and the PROLOGUE a
   "3" block re-enters is read only where [ps] has already settled it, which
   is what [pro_pin] says. *)
Lemma pending_at_cs_ext ps cs0 cs I :
  cs0 `prefix_of` cs -> (nlines I <= length cs0)%nat ->
  pending_at ps cs0 I = pending_at ps cs I.
Proof.
  intros Hp Hn. rewrite /pending_at.
  case_decide as H0; [done |].
  case_decide as Hr; [| done].
  pose proof (nlines_pos_of_rest_nil I H0 Hr) as Hpos.
  assert (Hlk : forall j, (j < nlines I)%nat -> cs0 !!! j = cs !!! j).
  { intros j Hj. symmetry. apply (lookup_total_prefix cs0 cs j Hp). lia. }
  rewrite /alt_cont (Hlk (nlines I - 1)%nat ltac:(lia)).
  by rewrite (pro_idx_ext cs0 cs (nlines I) Hlk (nlines I - 1)%nat ltac:(lia)).
Qed.

Lemma pending_at_cs_prefix ps0 ps cs0 cs I :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  (nlines I <= length cs0)%nat ->
  (pro_idx cs0 (nlines I) < pro_rounds ps0)%nat ->
  pending_at ps0 cs0 I = pending_at ps cs I.
Proof.
  intros Hps Hcs Hn Hr.
  rewrite (pending_at_ps_ext ps0 ps cs0 I Hps Hr). by apply pending_at_cs_ext.
Qed.

(* EVERY BLOCK STRICTLY BELOW A STAGE IS DETERMINED BY THE WRITER'S BOUNDS.
   "Strictly below" is what makes the two hypotheses affordable: a proper
   prefix of [I0] has at most [nlines (removelast I0)] complete lines
   (so [cs0] reaches it) and stands at a round [pro_pin] has settled. *)
Lemma pending_at_stage_ext ps0 ps cs0 cs I0 J :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  J `prefix_of` I0 -> J <> I0 ->
  pending_at ps0 cs0 J = pending_at ps cs J.
Proof.
  intros Hps Hcs Hpin Hn HJ Hne.
  assert (Hjl : (nlines J <= length cs0)%nat).
  { etrans; [| exact Hn].
    apply nlines_prefix, (epu_prefix_of_removelast J I0 HJ Hne). }
  apply (pending_at_cs_prefix ps0 ps cs0 cs J Hps Hcs Hjl).
  apply (pro_pin_at ps0 cs0 I0 (nlines J) Hpin).
  exact (nstarted_strict J I0 HJ Hne).
Qed.

Lemma proc_before_from_ext ps0 ps cs0 cs pre I :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ I -> J <> pre ++ I ->
     pending_at ps0 cs0 J = pending_at ps cs J) ->
  proc_before_from ps0 cs0 pre I = proc_before_from ps cs pre I.
Proof.
  revert pre. induction I as [| b I IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [b]) ++ I = pre ++ b :: I) by apply epu_app_snoc.
  assert (Hhere : pending_at ps0 cs0 pre = pending_at ps cs pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - apply (epu_app_cons_ne pre b I). }
  cbn [proc_before_from]. rewrite Hhere. f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma proc_before_ext ps0 ps cs0 cs I :
  (forall J, J `prefix_of` I -> J <> I ->
     pending_at ps0 cs0 J = pending_at ps cs J) ->
  proc_before ps0 cs0 I = proc_before ps cs I.
Proof.
  intros Hj. rewrite /proc_before. apply proc_before_from_ext.
  intros J _ H2 H3. rewrite app_nil_l in H2, H3. by apply Hj.
Qed.

(* the form the write lemmas spend: a writer's lower bounds determine the
   stream as far as it can index into it *)
Lemma proc_before_cs_prefix ps0 ps cs0 cs I0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  proc_before ps0 cs0 I0 = proc_before ps cs I0.
Proof.
  intros Hps Hcs Hpin Hn. apply proc_before_ext.
  intros J HJ Hne.
  exact (pending_at_stage_ext ps0 ps cs0 cs I0 J Hps Hcs Hpin Hn HJ Hne).
Qed.

Lemma pcount_cs_prefix ps0 ps cs0 cs E w :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 (snd <$> E) ->
  (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
  pcount ps0 cs0 E w = pcount ps cs E w.
Proof.
  intros Hps Hcs Hpin Hn. rewrite /pcount.
  by rewrite (proc_before_cs_prefix ps0 ps cs0 cs (snd <$> E) Hps Hcs Hpin Hn).
Qed.

(* ...AND THE ONE THE ORDINARY WRITE ACTUALLY HOLDS.  While the writer is
   inside the current block -- writing the banner of a restart's prologue,
   say -- that block's ROUND has not settled, so the stream through it is
   only a PREFIX of the claim's.  A prefix is all a byte lookup needs. *)
Lemma proc_stream_prefix ps0 ps cs0 cs I0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 I0 ->
  (nlines I0 <= length cs0)%nat ->
  proc_stream ps0 cs0 I0 `prefix_of` proc_stream ps cs I0.
Proof.
  intros Hps Hcs Hpin Hn.
  assert (Hb : proc_before ps0 cs0 I0 = proc_before ps cs I0).
  { apply (proc_before_cs_prefix ps0 ps cs0 cs I0 Hps Hcs Hpin).
    etrans; [apply nlines_prefix, epu_removelast_prefix | exact Hn]. }
  rewrite /proc_stream Hb. apply prefix_app.
  rewrite (pending_at_cs_ext ps0 cs0 cs I0 Hcs Hn).
  by apply pending_at_ps_mono.
Qed.

(* the same extension law for the TRANSCRIPT: [D] reads [pending_at] at the
   proper prefixes of the era's input only. *)
Lemma D_from_ext ps0 ps cs0 cs pre E :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
     J <> pre ++ (snd <$> E) -> pending_at ps0 cs0 J = pending_at ps cs J) ->
  D_from ps0 cs0 pre E = D_from ps cs pre E.
Proof.
  revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
    by (by rewrite fmap_cons epu_app_snoc).
  assert (Hhere : pending_at ps0 cs0 pre = pending_at ps cs pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
  cbn [D_from]. rewrite Hhere. do 2 f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma D_cs_prefix ps0 ps cs0 cs E :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 (snd <$> E) ->
  (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
  D ps0 cs0 E = D ps cs E.
Proof.
  intros Hps Hcs Hpin Hn. rewrite /D. apply D_from_ext.
  intros J _ H2 H3. rewrite app_nil_l in H2, H3.
  exact (pending_at_stage_ext ps0 ps cs0 cs (snd <$> E) J Hps Hcs Hpin Hn H2 H3).
Qed.

(* [w] stays a prefix once the byte it is owed is appended *)
Lemma prefix_snoc_lookup {A} (w l : list A) (b : A) :
  w `prefix_of` l -> l !! length w = Some b -> (w ++ [b]) `prefix_of` l.
Proof.
  intros [z ->] Hl. rewrite lookup_app_r in Hl; [| lia].
  rewrite Nat.sub_diag in Hl.
  destruct z as [| c z]; [discriminate |]. cbn in Hl. injection Hl as <-.
  exists z. by rewrite -app_assoc.
Qed.

(* THE WRITE'S WHOLE PURE ARGUMENT (the coordinator's ruling of 2026-09-14,
   at a line per round).  The writer names [cs0] (a lower bound of the era's
   choices), [I0] (a lower bound of the era's INPUT -- where the divide-by-17
   shape named a stage index [17 q]) and its cursor [P], and knows only that
   its byte is the [P]-th of the stream through [I0].  That ALONE pins the
   stage: if the era's input were strictly longer, the next line's first
   echo would have folded block [I0]'s WHOLE continuation into
   [proc_before], so the cursor could not still be indexing inside it; and
   at equality the index [P] lands strictly inside the continuation, which
   is the strictness premise [proc_stream_pcount_inv] asks for -- so the
   writer never has to supply it. *)
Lemma write_stage_byte (ps0 ps cs0 cs : list nat) (E : list (list mobs * bv 8))
      (w I0 : list (bv 8)) (P : nat) (b : bv 8) :
  ps0 `prefix_of` ps ->
  pro_pin ps0 cs0 I0 ->
  cs0 `prefix_of` cs ->
  (nlines I0 <= length cs0)%nat ->
  I0 `prefix_of` (snd <$> E) ->
  P = pcount ps cs E w ->
  proc_stream ps0 cs0 I0 !! P = Some b ->
  (snd <$> E) = I0 /\ pending ps cs E !! length w = Some b.
Proof.
  intros Hps Hpin Hcs Hn HI HP Hb.
  pose proof (prefix_lookup_Some _ _ _ _ Hb
                (proc_stream_prefix ps0 ps cs0 cs I0 Hps Hcs Hpin Hn)) as Hb'.
  clear Hb. rename Hb' into Hb.
  assert (Hlt : (P < length (proc_stream ps cs I0))%nat)
    by (by apply lookup_lt_Some in Hb).
  assert (HlenE : (snd <$> E) = I0).
  { destruct (decide ((snd <$> E) = I0)) as [? | Hne]; [done | exfalso].
    pose proof (proc_stream_before ps cs I0 (snd <$> E) HI
                  ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
    apply prefix_length in Hpre. rewrite HP /pcount in Hlt. lia. }
  split; [exact HlenE |].
  rewrite -HlenE in Hb, Hlt.
  assert (Hstrict : (length w < length (pending ps cs E))%nat).
  { rewrite /proc_stream length_app in Hlt.
    rewrite HP /pcount in Hlt. rewrite /pending. lia. }
  eapply (proc_stream_pcount_inv ps cs E w (snd <$> E) b);
    [reflexivity | exact Hstrict | by rewrite -HP].
Qed.

(* ====================================================================== *)
(*  1c.  THE BANNER OF AN ARBITRARY PROLOGUE ROUND                         *)
(* ====================================================================== *)

(* WHAT INIT'S RESTART LOOP PAYS THE WRITE LINK WITH.  Init prints the
   banner at the head of EVERY round: round 0 at boot, and one more each
   time the shell dies on its own [fork1] panic (line alternative 3) or its
   child fails to exec ([pro_alts !!! 1], which re-enters the SAME round).
   The banner is the LETTER [pro_alts !!! 3]: its first byte files it
   ([echo_write_link_pro] at [a = 3]) and the rest go through
   [echo_write_link], which asks for [proc_stream ps0 cs0 I !! P = Some b].
   This discharges that at an ARBITRARY round, off two facts the loop has:
   the block's SHAPE (its panic line, if any, and then this round's prologue
   -- [EchoOutPure.pending_at_round_pre] supplies it from the round-opening
   premise) and the round's resolution so far, which after [j] failed
   sub-rounds and the banner's first byte is [pro_fail j ++ [3]]
   ([EchoDisc.pro_fail]).  No [vm_compute]: [j] and the round index are
   variables. *)
Lemma proc_stream_round_banner (ps cs : list nat) (I : list (bv 8))
      (j i : nat) (pre : list (bv 8)) (b : bv 8) :
  pending_at ps cs I
  = pre ++ pro_of (pro_from (pro_idx cs (nlines I)) ps) ->
  pro_from (pro_idx cs (nlines I)) ps = pro_fail j ++ [3%nat] ->
  u_banner !! i = Some b ->
  proc_stream ps cs I
    !! (length (proc_before ps cs I) + length pre + pro_round * j + i)%nat
  = Some b.
Proof.
  intros Hshape Hopen Hb.
  rewrite /proc_stream Hshape Hopen.
  replace (length (proc_before ps cs I) + length pre + pro_round * j + i)%nat
    with (length (proc_before ps cs I) + (length pre + (pro_round * j + i)))%nat
    by lia.
  rewrite (lookup_app_shift (proc_before ps cs I)) (lookup_app_shift pre).
  by apply pro_of_fail_banner.
Qed.

(* ...and the same with the block's shape read off the round-opening premise
   itself, which is the form the loop applies.  The panic line is a
   CONSTANT ([EchoDisc.alt_panic]) -- the one thing a round-opening block
   owes that is not a function of what was typed. *)
Lemma proc_stream_round_banner_open (ps cs : list nat) (I : list (bv 8))
      (j i : nat) (b : bv 8) :
  rest_of I = [] ->
  (I = [] \/ cs !!! (nlines I - 1)%nat = 3%nat) ->
  pro_from (pro_idx cs (nlines I)) ps = pro_fail j ++ [3%nat] ->
  u_banner !! i = Some b ->
  proc_stream ps cs I
    !! (length (proc_before ps cs I)
        + length (if decide (I = []) then [] else alt_panic)
        + pro_round * j + i)%nat
  = Some b.
Proof.
  intros Hr Ho Hopen Hb.
  apply (proc_stream_round_banner ps cs I j i _ b);
    [by apply pending_at_round_pre | exact Hopen | exact Hb].
Qed.

(* ANTI-VACUITY.  The prologue-choice link's premises are SATISFIABLE AT
   ROUND 1 -- the round init opens after the shell's own [fork1] panic.  The
   era's input is ONE typed line ([EchoDisc.demo_ws1], "echo hi") whose
   continuation took alternative 3 ("fork\n"), the boot round settled with
   the banner and the prompt ([ps0 = [3; 0]]), and the writer stands at the
   round's first byte 25 process bytes into the era: 20 for [u_prologue] and
   5 for the panic line.  Both letters a round may open with are available
   there: init's banner ([a = 3]) and, if init's console is shut, the
   shell's bare prompt ([a = 0]).

   THE WIRE IS A LITERAL HERE ON PURPOSE -- this is a satisfiability
   witness, so it computes at one instance of the line and says nothing
   about the others. *)
Lemma pro_choice_round1_live :
  rest_of (wl_line demo_ws1) = []
  /\ (wl_line demo_ws1 = []
      \/ [3%nat] !!! (nlines (wl_line demo_ws1) - 1)%nat = 3%nat)
  /\ (nlines (wl_line demo_ws1) <= length [3%nat])%nat
  /\ pro_pin [3%nat; 0%nat] [3%nat] (wl_line demo_ws1)
  /\ ~ pro_done (pro_from (pro_idx [3%nat] (nlines (wl_line demo_ws1)))
                   [3%nat; 0%nat])
  /\ length (proc_stream [3%nat; 0%nat] [3%nat] (wl_line demo_ws1)) = 25%nat
  /\ (3 < length pro_alts)%nat
  /\ (exists b : bv 8, pro_alts !!! 3%nat !! 0%nat = Some b)
  /\ (exists b : bv 8, pro_alts !!! 0%nat !! 0%nat = Some b).
Proof.
  split_and!.
  - by vm_compute.
  - right. by vm_compute.
  - vm_compute (nlines (wl_line demo_ws1)). cbn [length]. lia.
  - intros q Hq. vm_compute (nstarted (wl_line demo_ws1)) in Hq.
    assert (q = 0%nat) by lia. subst q. by vm_compute.
  - assert (Hz : pro_from (pro_idx [3%nat] (nlines (wl_line demo_ws1)))
                   [3%nat; 0%nat] = []) by (by vm_compute).
    rewrite Hz. intros H. by apply Exists_nil in H.
  - by vm_compute.
  - rewrite pro_alts_length. lia.
  - destruct (pro_alts !!! 3%nat) as [| c t] eqn:Hz;
      [ vm_compute in Hz; discriminate | exists c; reflexivity ].
  - destruct (pro_alts !!! 0%nat) as [| c t] eqn:Hz;
      [ vm_compute in Hz; discriminate | exists c; reflexivity ].
Qed.

(* the log's own account of the era, plus the two index laws for the
   entries the log has echoed and the bound on the era's line choices that a
   READER hands on to a later block-first WRITE.

   IT WAS THE INPUT CLAIM'S PURE FACT, the same proposition in both of that
   claim's non-taint arms (the settled one and the chain-first window).
   What separated those was the window counter and nothing pure -- the entry
   the window owed was named by [ein_pend], which the echo handed to the
   append, never by the port's own claim -- which is what made the DROP arm
   ([cs = []], which does not move [echoed pops]) leave both exactly where
   they stood.  The merged claim has ONE arm (redesign R1) and this survives
   inside [ecl_pure].

   [E_index]/[E_disc] ARE HERE and not only in the output claim because
   SH-LINE reads the line off the READ's window and holds no output claim:
   [read_ret] exports them, together with the input the window reaches and
   its discipline. *)
Definition ein_pure (k : nat) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) (cs0 : list nat) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
  /\ dl `prefix_of` echoed pops
  /\ E_index (seg_of (echoed pops))
  /\ E_disc (seg_of (echoed pops))
  /\ (nlines (snd <$> echoed pops) <= S (length cs0))%nat
  (* (A1) EVERY LOG ENTRY IS ECHOED.  Under the discipline [consoleintr]
     never drops: the store arm sends its byte before it files the entry
     ([ConsLog.cons_ev_ok]'s [EvClose] clause), and the arms that file
     nothing are refuted at the OPEN, where the kernel says WHY a drop
     would have happened ([ConsLog.cons_drop_ok]) and the claim's
     delivered count says the ring cannot have been full.  This is what
     turns the log's LENGTH into the era's echoed count, which is how the
     claim knows -- with no per-byte wait on the wire -- that every input
     before the one being echoed has already been echoed. *)
  /\ Forall log_echoed pops.

(* WHAT THE INPUT CLAIM KNOWS OF THE WRITER'S STAGE at the input [I] its log
   has echoed (PROLOGUE-ALTS-3, the discipline lemma): the two choice lists
   it carries are bounded, every block strictly below [I] reads a settled
   round, and the line list reaches the last COMPLETED line -- which is
   [nlines (removelast I)], the parse's reading of what used to be
   [(m-1) div 17].  It is deposited by the echo off the output claim and
   handed to the reader by the read, beside a lower bound of the cursor at
   [length (proc_before ps0 cs0 I)] -- together they say "the writer has
   written every block the log's echoes answer". *)
Definition rd_stage (ps0 cs0 : list nat) (I : list (bv 8)) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps0
  /\ Forall (fun i => (i < 4)%nat) cs0
  /\ pro_pin ps0 cs0 I
  /\ (nlines (removelast I) <= length cs0)%nat.

Lemma rd_stage_0 : rd_stage [] [] [].
Proof.
  rewrite /rd_stage. split_and!; [constructor | constructor | |].
  - apply pro_pin_nil.
  - cbn [removelast]. rewrite nlines_nil. cbn [length]. lia.
Qed.

Lemma rd_stage_le (ps0 cs0 : list nat) (I I' : list (bv 8)) :
  I' `prefix_of` I -> rd_stage ps0 cs0 I -> rd_stage ps0 cs0 I'.
Proof.
  intros Hle (Hps & Hcs & Hpin & Hbnd). split_and!; [exact Hps | exact Hcs | |].
  - exact (pro_pin_prefix ps0 cs0 I' I Hle Hpin).
  - etrans; [| exact Hbnd].
    apply nlines_prefix, (epu_prefix_removelast I' I Hle).
Qed.

Lemma epu_lookup_nil_absurd {A} (j : nat) (x : A) :
  ([] : list A) !! j = Some x -> False.
Proof. intros Hx. apply lookup_lt_Some in Hx. cbn in Hx. lia. Qed.

Lemma eout_pure_0 k ho : eout_pure k ho ostage0 [].
Proof.
  rewrite /eout_pure /ostage0. cbn [o_ps o_cs o_E o_w]. split_and!.
  - rewrite D_nil. done.
  - rewrite pending_nil. apply prefix_nil.
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - exact disc_input_nil.
  - constructor.
  - exact (pro_pin_nil [] []).
  - constructor.
  - constructor.
  - constructor.
  - cbn [length]. lia.
  - by left.
Qed.

Lemma cs_len_ok_0 : cs_len_ok ostage0.
Proof.
  rewrite /ostage0. apply (cs_len_ok_intro [] [] []); intros _;
    cbn [length]; rewrite fmap_nil nlines_nil; lia.
Qed.

Lemma log_ok_nil : log_ok [].
Proof.
  split.
  - intros e He. by apply elem_of_nil in He.
  - intros i e1 e2 H1 H2. destruct (epu_lookup_nil_absurd i e1 H1).
Qed.

Lemma echoed_nil : echoed [] = [].
Proof. rewrite /echoed. by rewrite filter_nil. Qed.
Lemma ein_pure_0 k : ein_pure k [] [] [].
Proof.
  rewrite /ein_pure. split_and!.
  - exact log_ok_nil.
  - intros e He. by apply elem_of_nil in He.
  - intros e He. by apply elem_of_nil in He.
  - apply prefix_nil.
  - intros j x Hx. rewrite /seg_of echoed_nil fmap_nil in Hx.
    destruct (epu_lookup_nil_absurd j x Hx).
  - rewrite /E_disc /seg_of echoed_nil !fmap_nil. exact disc_input_nil.
  - rewrite echoed_nil fmap_nil nlines_nil. cbn [length]. lia.
  - constructor.
Qed.

(* ---- how the log's echoed slice moves at an append ---- *)
Lemma echoed_snoc_yes (pops : list log_entry) (e : log_entry) :
  log_echoed e ->
  echoed (pops ++ [e]) = echoed pops ++ [(le_hist e, le_byte e)].
Proof.
  intros He. induction pops as [| a l IH].
  - cbn [app]. rewrite /echoed (epu_filter_cons_T log_echoed e [] He).
    by rewrite filter_nil.
  - cbn [app]. rewrite /echoed in IH |- *.
    destruct (decide (log_echoed a)) as [Ha | Ha].
    + rewrite !(epu_filter_cons_T log_echoed a _ Ha) !fmap_cons.
      by rewrite IH.
    + rewrite !(epu_filter_cons_F log_echoed a _ Ha). by rewrite IH.
Qed.

Lemma echoed_snoc_no (pops : list log_entry) (e : log_entry) :
  ~ log_echoed e -> echoed (pops ++ [e]) = echoed pops.
Proof.
  intros He. induction pops as [| a l IH].
  - cbn [app]. rewrite /echoed (epu_filter_cons_F log_echoed e [] He).
    by rewrite filter_nil.
  - cbn [app]. rewrite /echoed in IH |- *.
    destruct (decide (log_echoed a)) as [Ha | Ha].
    + rewrite !(epu_filter_cons_T log_echoed a _ Ha) !fmap_cons.
      by rewrite IH.
    + rewrite !(epu_filter_cons_F log_echoed a _ Ha). by rewrite IH.
Qed.

(* WHAT (A1) BUYS: a log every entry of which is echoed IS its own echoed
   slice, so the log's LENGTH is the era's echoed count.  This is the step
   that replaces waiting for each byte's echo on the wire. *)
Lemma echoed_all_len (pops : list log_entry) :
  Forall log_echoed pops -> length (echoed pops) = length pops.
Proof.
  intro HF. induction pops as [| e pops IH] using rev_ind.
  - by rewrite echoed_nil.
  - apply Forall_app in HF as [HF1 HF2].
    rewrite Forall_singleton in HF2.
    rewrite (echoed_snoc_yes pops e HF2) !length_app. cbn [length].
    by rewrite (IH HF1).
Qed.

(* a dropped byte is not an echoed entry: [[]] is not [[echo_of c]] *)
Lemma log_echoed_nil_no (h : list mobs) (c : bv 8) :
  ~ log_echoed (h, c, []).
Proof. rewrite /log_echoed /le_echo /le_byte /=. discriminate. Qed.

Lemma log_echoed_echo (h : list mobs) (c : bv 8) :
  log_echoed (h, c, [echo_of c]).
Proof. by rewrite /log_echoed /le_echo /le_byte /=. Qed.

(* AN OUTPUT CLAIM AT [acc = []] STANDS AT THE START OF ITS ERA.  Nothing
   but the empty stage has an empty transcript: the first echo folds the
   whole PROLOGUE into [D], and the prologue is not empty. *)
Lemma eout_pure_nil_stage (k : nat) (ho : list mobs) (so : ostage) :
  eout_pure k ho so [] -> pcount (o_ps so) (o_cs so) (o_E so) (o_w so) = 0%nat.
Proof.
  intros (Hacc & _).
  assert (Hlen : (length (D (o_ps so) (o_cs so) (o_E so)) + length (o_w so))%nat = 0%nat)
    by (rewrite -length_app -Hacc; reflexivity).
  destruct (o_E so) as [| y E1] eqn:HE.
  - rewrite /pcount fmap_nil proc_before_nil. cbn [length]. lia.
  - exfalso.
    assert (Hup : (0 < length (D (o_ps so) (o_cs so) (y :: E1)))%nat).
    { change (D (o_ps so) (o_cs so) (y :: E1))
        with (pending_at (o_ps so) (o_cs so) []
              ++ [echo_of y.2] ++ D_from (o_ps so) (o_cs so) ([] ++ [y.2]) E1).
      rewrite !length_app. cbn [length]. lia. }
    lia.
Qed.

(* THE ECHO'S OWN ENTRY IS NOT IN THE LOG, and that is a PURE fact about the
   two histories: the arm's order premise ([ConsLog.arm_ok]'s fourth clause,
   which [WpUart.in_append] used to carry per byte) puts every logged
   history strictly below [h], the era stamps put the two in one cycle, and
   an [open_seg] can only grow when the history does.  This is what refutes
   the SETTLED arm at the append (an arm that says the entry has already
   been filed) and it is [open_seg_prefix_boots] with the strictness kept. *)
Lemma open_seg_hist_ext (h1 h2 : list mobs) :
  hist_ext h1 h2 -> obs_boots h1 = obs_boots h2 ->
  trace_shape h2 true -> hist_ext (open_seg h1) (open_seg h2).
Proof.
  intros [[k Hk] Hlt] Hb Hsh. subst h2.
  assert (Hk0 : obs_boots k = 0%nat)
    by (rewrite obs_boots_app in Hb; lia).
  rewrite /trace_shape foldl_app in Hsh.
  destruct (foldl obs_step (Some false) h1) as [st |] eqn:Hst; last first.
  { rewrite epu_foldl_obs_step_none in Hsh. discriminate. }
  destruct (epu_no_power_of_boots k st Hk0 Hsh) as [_ HF].
  rewrite (open_seg_io h1 k HF). split; [by eexists |].
  rewrite length_app. rewrite length_app in Hlt. lia.
Qed.

(* A PREFIX THAT STOPS SHORT OF THE LAST EVENT. *)
Lemma prefix_snoc_lt {A : Type} (l1 l2 : list A) (x : A) :
  l1 `prefix_of` (l2 ++ [x]) -> (length l1 <= length l2)%nat ->
  l1 `prefix_of` l2.
Proof.
  intros Hp Hlen.
  assert (Hl1 : l1 = take (length l1) l2).
  { rewrite -(take_app_le l2 [x] (length l1) Hlen).
    destruct Hp as [z Hz]. rewrite Hz. by rewrite take_app_length. }
  rewrite Hl1. apply prefix_take.
Qed.

(* ====================================================================== *)
(*  2.  THE GHOST NAMES AT THE FIXED PART                                  *)
(* ====================================================================== *)

(* [AppEcho.echo_fixed] becomes this record.  [eg_taint] is the landed
   counter and nothing about it moves; [eg_pin] is the ERA MAP, whose
   AUTHORITY is spent at exactly one place -- the ledger's power-on step,
   which allocates the era's ghosts and mints its pin.  No link touches it,
   which is what lets every link run without the ledger. *)
Record echo_gn := MkEchoGn {
  eg_taint : gname;   (* mono_nat: 0 while disciplined, 1 after -- LANDED *)
  eg_pin   : gname;   (* ghost_map nat era_pins: the era NUMBER's ghosts *)
}.

(* the ghosts of ONE era.  ALL FOUR LIVE IN THE CLAIMS (the design page's
   CLAIM-RESIDENT shape): the ledger holds none of them, and the pin below
   is the persistent name by which a claim, a writer and a reader mean the
   same era. *)
Record era_pins := MkPins {
  ep_go  : gname;   (* ghost_var nat: the era's PROCESS-BYTE CURSOR; the
                       output claim holds one half as [turn_auth], a writer
                       (init, through [app_turn]) the other *)
  ep_gcs : gname;   (* mono_list nat: the era's line choices; the output
                       claim holds the authority, everyone else a lower
                       bound *)
  ep_gps : gname;   (* mono_list nat: the era's PROLOGUE choices, in wire
                       order -- one per round of init's restart loop, the
                       first round at the boot and one more after every
                       line whose continuation was the shell's own fork
                       panic.  Same shape as [ep_gcs]: the output
                       claim holds the authority, a writer a lower bound *)
  ep_gE  : gname;   (* mono_list (list mobs * bv 8): the era's ECHOED LIST;
                       the output claim holds the authority, the input claim
                       a lower bound at the log's own slice *)
  ep_gdl : gname;   (* ghost_var nat: the DELIVERED COUNT, in two halves --
                       one in the input claim at [length dl], one in the
                       READER's hand.  A read hands its half over and gets
                       it back advanced, and the agreement inside the link
                       is what tells the reader WHERE in the era's input
                       its window fell: [read_link] hides the invariant's
                       [dl], and [ein_read_byte] cannot run without it. *)
  ep_gdll : gname;  (* mono_list (list mobs * bv 8): the DELIVERED LIST
                       itself.  The claim holds the authority at [ch_dl H]
                       and every writer a lower bound -- which is what
                       [inp_lb] is.  A program's bound is therefore a bound
                       on what the console has HANDED OVER, not on what it
                       has echoed, and that is the coupling the ring
                       argument spends: a block's first byte is written by
                       a process that has already CONSUMED the line it
                       answers, so the ring holds at most the line in
                       progress. *)
  ep_secc : gname;  (* mono_nat: THE ERA'S WILD FLAG (seccomp design 10.1):
                       0 while the era's console is disciplined, 1 once a
                       wild line's read made the era wild.  The union's
                       claim holds the whole authority; the era's wild
                       token is a lower bound at 1.  No other application
                       reads it. *)
}.

(* THE ERA MAP'S BOUND.  Every era the ledger has ever founded is at most
   the boot count of the ledger's own history, so the era a POWER-ON starts
   -- [S (obs_boots h)] -- is absent from the map and the insert is legal.
   This is the only thing in the ledger besides the taint counter and the
   phi conjunct that reads the history, and no LINK reads it. *)
Definition pin_dom {A : Type} (M : gmap nat A) (n : nat) : Prop :=
  forall k, is_Some (M !! k) -> (k <= n)%nat.

Lemma pin_dom_empty {A : Type} (n : nat) : pin_dom (∅ : gmap nat A) n.
Proof. intros k [x Hx]. by rewrite lookup_empty in Hx. Qed.

Lemma pin_dom_absent {A : Type} (M : gmap nat A) (n : nat) :
  pin_dom M n -> M !! (S n) = None.
Proof.
  intros Hd. destruct (M !! S n) as [x |] eqn:Hx; [| reflexivity].
  exfalso. specialize (Hd (S n) (ex_intro _ x Hx)). lia.
Qed.

Lemma pin_dom_insert {A : Type} (M : gmap nat A) (n : nat) (a : A) :
  pin_dom M n -> pin_dom (<[S n := a]> M) (S n).
Proof.
  intros Hd k Hk. destruct (decide (k = S n)) as [-> | Hne]; [lia |].
  rewrite lookup_insert_ne in Hk; [| lia]. specialize (Hd k Hk). lia.
Qed.

Class echoOutG (Σ : gFunctors) := EchoOutG {
  eo_mono_nat : mono_natG Σ;
  eo_turn     : ghost_varG Σ nat;
  eo_pin      : ghost_mapG Σ nat era_pins;
  eo_cs       : inG Σ (mono_listR (leibnizO nat));
  eo_El       : inG Σ (mono_listR (leibnizO (list mobs * bv 8)));
}.
#[global] Existing Instances eo_mono_nat eo_turn eo_pin eo_cs eo_El.

(* THE FUNCTOR BUNDLE, and the standard [subG] instance (lane ECHO-OUT part
   5).  [AppEcho] and everything above it takes [echoOutG Σ] as a section
   context; a CLOSED corollary that instantiates
   [App.xv6_app_adequacy] at a CONCRETE [Σ] discharges the class from its own
   bundle by this instance -- exactly as every other Iris library does.  The
   only closed corollaries in the tree today are the TRIVIAL application's
   ([SystemAdequacy.xv6_trace_adequacy] and its siblings, at [xv6Σ]), which
   never mention this class, so nothing in the tree needs [echoOutΣ] yet;
   it exists so that the echo's closed theorem can be stated without
   re-opening this file. *)
Definition echoOutΣ : gFunctors :=
  #[ mono_natΣ; ghost_varΣ nat; ghost_mapΣ nat era_pins;
     GFunctor (mono_listR (leibnizO nat));
     GFunctor (mono_listR (leibnizO (list mobs * bv 8))) ].

Global Instance subG_echoOutΣ {Σ} : subG echoOutΣ Σ -> echoOutG Σ.
Proof. solve_inG. Qed.

(* ====================================================================== *)
(*  THE ERA'S ECHOED LIST, READ OFF THE CONSOLE HISTORY (redesign lane R1) *)
(*                                                                        *)
(*  The redesign merges the output and input claims into ONE claim over    *)
(*  [LogEntryDefs.cons_hist].  The claim's [o_E] -- the era's echoed list -- is *)
(*  then not a free existential but a FUNCTION of the history, and that    *)
(*  function is what makes the window counter unnecessary.                 *)
(*                                                                        *)
(*  The input claim HAD two non-taint arms differing only in the counter:  *)
(*  SETTLED (the log and the era's list agree) and the chain-first WINDOW  *)
(*  (the echo's byte is on the wire, its log entry still owed, so the      *)
(*  era's list is ONE AHEAD).  The window arm held a HALF of [wcnt] so     *)
(*  that a second firing of the run met five quarters.  With the arm in    *)
(*  the history the two arms are ONE: [ch_E] counts the                    *)
(*  in-flight entry as soon as its byte is out, and                        *)
(*  [ch_E_close] below says the list DOES NOT MOVE when the entry is       *)
(*  filed -- the window closes by construction, with nothing to refute.    *)
(*                                                                        *)
(*  THE ARM'S CONDITION IS [take j cs = [echo_of c]], NOT                  *)
(*  [cs = [echo_of c]].  It has to be exactly [ConsLog.log_echoed]'s       *)
(*  condition on the entry [EvClose] will file, [(h, c, take j cs)], or    *)
(*  [ch_E_close] is false.  The two differ: a BACKSPACE input (c = 8) is   *)
(*  erased rather than echoed, so its [cs] is the three-byte               *)
(*  [consputc_bs] and [cs <> [echo_of c]] -- but [take 1 cs = [8]] IS      *)
(*  [[echo_of 8]], so the filed entry counts as echoed and the era's list  *)
(*  must already have counted it.  (Such an input breaks the console       *)
(*  discipline and so only ever reaches the claim's TAINT arm; [ch_E] is   *)
(*  a pure function and has to be right there anyway.)                     *)
(* ====================================================================== *)

Definition ch_arm_E (a : option LogEntryDefs.cons_arm) : list (list mobs * bv 8) :=
  match a with
  | Some (h, c, cs, j) =>
      if decide (take j cs = [echo_of c]) then [(open_seg h, c)] else []
  | None => []
  end.

Definition ch_E (H : LogEntryDefs.cons_hist) : list (list mobs * bv 8) :=
  seg_of (echoed (LogEntryDefs.ch_log H)) ++ ch_arm_E (LogEntryDefs.ch_arm H).

(* one filed entry, as the era's list sees it *)
Lemma seg_echoed_snoc (L : list log_entry) (e : log_entry) :
  seg_of (echoed (L ++ [e]))
  = seg_of (echoed L)
    ++ (if decide (log_echoed e) then [(open_seg (le_hist e), le_byte e)] else []).
Proof.
  destruct (decide (log_echoed e)) as [He | He].
  - by rewrite (echoed_snoc_yes L e He) seg_of_app.
  - by rewrite (echoed_snoc_no L e He) app_nil_r.
Qed.

Lemma ch_E_out (H : LogEntryDefs.cons_hist) (b : bv 8) :
  ch_E (ConsLog.cons_step H (ConsLog.EvOut b)) = ch_E H.
Proof. reflexivity. Qed.

Lemma ch_E_read (H : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
  ch_E (ConsLog.cons_step H (ConsLog.EvRead ws)) = ch_E H.
Proof. reflexivity. Qed.

(* the arm opens with nothing sent, so it counts nothing yet *)
Lemma ch_arm_E_open (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
  ch_arm_E (Some (h, c, cs, 0%nat)) = [].
Proof.
  cbn [ch_arm_E]. case_decide as Hk; [exfalso; discriminate Hk | reflexivity].
Qed.

Lemma ch_E_open (H : LogEntryDefs.cons_hist) (h : list mobs) (c : bv 8)
    (cs : list (bv 8)) :
  LogEntryDefs.ch_arm H = None ->
  ch_E (ConsLog.cons_step H (ConsLog.EvOpen h c cs)) = ch_E H.
Proof.
  intros Hn. unfold ch_E, ConsLog.cons_step. rewrite Hn.
  cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
  rewrite ch_arm_E_open. cbn [ch_arm_E]. by rewrite !app_nil_r.
Qed.

(* THE ONE THAT MATTERS: filing the entry does not move the era's list.
   This is the settled/window merge -- there is no second arm and no
   counter, because the two descriptions are equal. *)
Lemma ch_E_close (H : LogEntryDefs.cons_hist) :
  ch_E (ConsLog.cons_step H ConsLog.EvClose) = ch_E H.
Proof.
  rewrite /ch_E /ConsLog.cons_step.
  destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha; [| by rewrite Ha].
  cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
  rewrite seg_echoed_snoc app_nil_r. done.
Qed.

(* the byte going out is the only event that moves the list *)
Lemma ch_E_byte (H : LogEntryDefs.cons_hist) (b : bv 8)
    (h : list mobs) (c : bv 8) (cs : list (bv 8)) (j : nat) :
  LogEntryDefs.ch_arm H = Some (h, c, cs, j) ->
  ch_E (ConsLog.cons_step H (ConsLog.EvByte b))
  = seg_of (echoed (LogEntryDefs.ch_log H)) ++ ch_arm_E (Some (h, c, cs, S j)).
Proof. intros Ha. rewrite /ch_E /ConsLog.cons_step. by rewrite Ha. Qed.

(* ...and for the ordinary echo of one byte it grows by exactly that entry *)
Lemma ch_E_byte_echo (H : LogEntryDefs.cons_hist) (b : bv 8)
    (h : list mobs) (c : bv 8) :
  LogEntryDefs.ch_arm H = Some (h, c, [echo_of c], 0%nat) ->
  ch_E (ConsLog.cons_step H (ConsLog.EvByte b))
  = ch_E H ++ [(open_seg h, c)].
Proof.
  intros Ha. rewrite (ch_E_byte H b h c [echo_of c] 0%nat Ha).
  unfold ch_E. rewrite Ha ch_arm_E_open app_nil_r.
  cbn [ch_arm_E]. case_decide as Hk; [reflexivity |].
  exfalso. apply Hk. reflexivity.
Qed.

(* ---- the settled state: once the arm closes, the log's echoed count IS
   the era's list length.  This is what lets the READER's stage fact
   ([rd_stage] at the log's echo count) be read off the WRITER's
   ([eout_pure]'s [pro_pin] at [length (o_E so)]) -- today those are two
   facts in two claims, kept in step by the window counter. ---- *)
Lemma ch_E_close_len (H : LogEntryDefs.cons_hist) :
  length (echoed (LogEntryDefs.ch_log (ConsLog.cons_step H ConsLog.EvClose)))
  = length (ch_E H).
Proof.
  rewrite -(ch_E_close H) /ch_E.
  destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha.
  - rewrite /ConsLog.cons_step Ha /=. by rewrite app_nil_r seg_of_length.
  - rewrite /ConsLog.cons_step Ha /=. rewrite Ha /=.
    by rewrite app_nil_r seg_of_length.
Qed.

Lemma ch_dl_byte (H : LogEntryDefs.cons_hist) (b : bv 8) :
  LogEntryDefs.ch_dl (ConsLog.cons_step H (ConsLog.EvByte b)) = LogEntryDefs.ch_dl H.
Proof.
  rewrite /ConsLog.cons_step.
  by destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |].
Qed.

Lemma ch_dl_close (H : LogEntryDefs.cons_hist) :
  LogEntryDefs.ch_dl (ConsLog.cons_step H ConsLog.EvClose) = LogEntryDefs.ch_dl H.
Proof.
  rewrite /ConsLog.cons_step.
  by destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |].
Qed.

(* ---- the era facts the in-flight arm carries.  They are what the entry
   [EvClose] files needs in order to join [ein_pure]'s per-entry clauses,
   and they are the application's business, not [ConsLog]'s: that file
   knows nothing of the discipline or of era numbers. ---- *)
(* WHAT THE CLAIM REMEMBERS ABOUT AN OPEN ARM (redesign R2).

   The three facts are the shift's own premises, recorded at [EvOpen] and
   read back at EVERY byte of the arm.  They have to be recorded, because a
   byte link fires at a history the application did not see opened: an
   unrelated writer's [EvOut] may have moved the console history in
   between, and all the link itself hands over is [ConsLog.cons_ev_ok] and
   [ConsLog.cons_hist_ok].  [ConsLog.arm_ok] carries the order and wire
   facts; these three are the ledger's own and live here. *)
Definition ch_arm_era (k : nat) (ho : list mobs)
    (H : LogEntryDefs.cons_hist) : Prop :=
  match LogEntryDefs.ch_arm H with
  | Some (h, c, cs, j) =>
      disc_seg (open_seg h) /\ obs_boots h = k
      /\ disc h /\ trace_shape h true
      (* ...AND THE ARM'S HISTORY IS THE CLAIM'S OWN WITNESS.  This is what
         lets a byte link keep the witness where it found it: the claim
         cannot name [obs_hist_lb] (it lives below [riscvGS]), so the only
         bound it may return is the one the link handed it. *)
      /\ h = ho
      (* THE ARM ECHOES ITS BYTE, recorded at the open out of
         [ConsLog.cons_echo] with the drop and the erase arms refuted.  It
         is what (A1) needs at the close: with [ConsLog.cons_ev_ok]'s
         [EvClose] clause the byte has gone out, so the entry filed is
         [(h, c, [echo_of c])] and the log stays all-echoed. *)
      /\ cs = [echo_of c]
      (* ...AND THIS BYTE'S INPUT NUMBER (K1), read off the kernel's FIFO
         discipline at the open and carried to every byte of the arm.  The
         log is COMPLETE below this input: the receive FIFO is drained in
         arrival order and each popped byte's arm closes before the next
         pop, so the entry this arm will file is input number
         [length (ch_log H) + 1].  Nothing moves the log while an arm is
         open, which is why the fact recorded at the open is still true
         here. *)
      /\ (length (LogEntryDefs.ch_log H) + 1)%nat = length (ins (open_seg h))
  | None => True
  end.

(* THE CLAIM'S DELIVERED-COUNT LAW (A2).  Every COMPLETED line whose block
   has begun has been consumed by the reader.  The count is by BYTES, over
   the parse, because no line has a fixed length: [lines_bytes Eb n] is the
   first [n] complete lines of the era's input with their newlines.

   WHICH LINES' BLOCKS HAVE BEGUN.  All of them, except at the one moment
   the writer is standing at a block boundary with nothing of the block
   written -- the same moment [cs_len_ok] is one short, and for the same
   reason: the block that answers the last line has not started.

   WHERE IT COMES FROM.  A block's first byte is written against the
   writer's own [inp_lb], which is a lower bound on what the console has
   DELIVERED; so at that write the delivered list already reaches the whole
   line the block answers.  WHAT IT IS FOR: the ring.  At a drop the kernel
   says 128 echoed entries are undelivered ([ConsLog.cons_drop_ok]); this
   says those 128 bytes lie inside ONE line, and a line is under
   [EchoDisc.line_max]. *)
Definition dl_ok (so : ostage) (dl : list (list mobs * bv 8)) : Prop :=
  (lines_bytes (snd <$> o_E so)
     (if decide (rest_of (snd <$> o_E so) = [] /\ o_w so = [])
      then (nlines (snd <$> o_E so) - 1)%nat
      else nlines (snd <$> o_E so))
   <= length dl)%nat.

(* an era with no input owes nothing at any count *)
Lemma lines_bytes_nil (n : nat) : lines_bytes [] n = 0%nat.
Proof. by rewrite /lines_bytes bodies_of_nil take_nil wl_join_nil. Qed.

Lemma dl_ok_0 : dl_ok ostage0 [].
Proof.
  rewrite /dl_ok /ostage0. cbn [o_E o_w]. rewrite fmap_nil.
  rewrite lines_bytes_nil. lia.
Qed.

(* the delivered list only grows *)
Lemma dl_ok_mono (so : ostage) (dl dl' : list (list mobs * bv 8)) :
  (length dl <= length dl')%nat -> dl_ok so dl -> dl_ok so dl'.
Proof. rewrite /dl_ok. lia. Qed.

(* ---- (A2)'s three moves ---- *)

(* A PROCESS BYTE puts the writer inside a block, so the clause is at the
   whole line count.  That is no new obligation except at a boundary the
   writer had not left yet -- and the three cases here are exactly the ones
   [cs_len_ok_write]'s side condition already names: mid-block, mid-line,
   or an era with no input at all. *)
Lemma dl_ok_out (so so' : ostage) (dl : list (list mobs * bv 8)) :
  o_E so' = o_E so -> o_w so' <> [] ->
  (o_w so <> [] \/ rest_of (snd <$> o_E so) <> [] \/ (snd <$> o_E so) = []) ->
  dl_ok so dl -> dl_ok so' dl.
Proof.
  intros HE Hw Hcase Hdl. rewrite /dl_ok in Hdl |- *. rewrite HE.
  rewrite decide_False; last first.
  { intros [_ Hq]. by apply Hw. }
  destruct Hcase as [Hc | [Hc | Hc]].
  - rewrite decide_False in Hdl; [exact Hdl | by intros [_ Hq]].
  - rewrite decide_False in Hdl; [exact Hdl | by intros [Hq _]].
  - rewrite Hc lines_bytes_nil. lia.
Qed.

(* ...AND AT A BLOCK'S FIRST BYTE the clause is paid by the writer's own
   [inp_lb]: the bound it writes against is a lower bound on the DELIVERED
   input, and it is the whole era's input, so the reader has taken every
   byte of the line this block answers. *)
Lemma dl_ok_out_full (so so' : ostage) (dl : list (list mobs * bv 8)) :
  o_E so' = o_E so -> o_w so' <> [] ->
  rest_of (snd <$> o_E so) = [] ->
  (length (snd <$> o_E so) <= length dl)%nat ->
  dl_ok so' dl.
Proof.
  intros HE Hw Hr Hlen. rewrite /dl_ok HE.
  rewrite decide_False; last first.
  { intros [_ Hq]. by apply Hw. }
  pose proof (lines_bytes_rest (snd <$> o_E so)) as Hsum.
  rewrite Hr in Hsum. cbn [length] in Hsum. lia.
Qed.

(* THE ECHO leaves the writer owing a whole block, so the clause drops back
   to the completed lines below the one just closed -- which is where it
   already was.  The one case that is not a frame is the era's very first
   echo, and there the stage owes [pending] and the input is empty. *)
Lemma dl_ok_echo (so : ostage) (x : list mobs * bv 8)
    (dl : list (list mobs * bv 8)) :
  Forall (fun i => (i < 4)%nat) (o_cs so) ->
  o_w so = pending (o_ps so) (o_cs so) (o_E so) ->
  dl_ok so dl ->
  dl_ok (MkO (o_ps so) (o_cs so) (o_E so ++ [x]) []) dl.
Proof.
  intros Hcsb Hweq Hdl. rewrite /dl_ok in Hdl |- *.
  cbn [o_ps o_cs o_E o_w]. rewrite (fmap_snd_snoc (o_E so) x).
  destruct (decide (rest_of (snd <$> o_E so) = [] /\ o_w so = []))
    as [[Hr0 Hw0] | Hne].
  - (* the era has no input yet: nothing below the first line is owed *)
    assert (HEnil : (snd <$> o_E so) = []).
    { destruct (decide ((snd <$> o_E so) = [])) as [? | Hq]; [done | exfalso].
      apply (pending_at_nonnil (o_ps so) (o_cs so) (snd <$> o_E so)
               Hcsb Hq Hr0).
      rewrite -/(pending (o_ps so) (o_cs so) (o_E so)) -Hweq. exact Hw0. }
    rewrite HEnil. case_decide as Hc2.
    + (* the byte is the newline, and it closes the era's FIRST line, so
         the count below it is zero *)
      destruct Hc2 as [Hr2 _].
      assert (Hn2 : nlines ([] ++ [x.2]) = 1%nat).
      { destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
        - by rewrite Hx nlines_snoc_nl nlines_nil.
        - exfalso. rewrite (rest_of_snoc_other [] x.2 Hx) rest_of_nil in Hr2.
          discriminate Hr2. }
      rewrite Hn2. replace (1 - 1)%nat with 0%nat by lia.
      rewrite lines_bytes_0. lia.
    + (* ...or it opens one, and no line is complete *)
      assert (Hn2 : nlines ([] ++ [x.2]) = 0%nat).
      { destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
        - exfalso. apply Hc2. split; [| reflexivity].
          rewrite Hx. apply rest_of_snoc_nl.
        - by rewrite (nlines_snoc_other [] x.2 Hx) nlines_nil. }
      rewrite Hn2 lines_bytes_0. lia.
  - (* everywhere else the count does not move: a newline closes the line
       the clause was already at, and a body byte opens none.  [Hdl] is
       already at the whole line count -- the case split above put it
       there. *)
    destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
    + rewrite Hx. case_decide as Hc2; last first.
      { exfalso. apply Hc2. split; [apply rest_of_snoc_nl | reflexivity]. }
      rewrite nlines_snoc_nl.
      replace (S (nlines (snd <$> o_E so)) - 1)%nat
        with (nlines (snd <$> o_E so)) by lia.
      by rewrite (lines_bytes_snoc_nl _ _ (Nat.le_refl _)).
    + case_decide as Hc2.
      { exfalso. destruct Hc2 as [Hq _].
        rewrite (rest_of_snoc_other _ x.2 Hx) in Hq.
        destruct (app_eq_nil _ _ Hq) as [_ Hq2]. discriminate Hq2. }
      rewrite (nlines_snoc_other _ x.2 Hx).
      by rewrite (lines_bytes_snoc_other _ x.2 _ Hx).
Qed.

(* ---- THE MERGED CLAIM'S PURE CONTENT.  Today's [eout_pure] and
   [ein_pure] over ONE stage and ONE history, plus the tie that makes the
   window counter unnecessary: the era's echoed list IS [ch_E] of the
   history.  [ein_pure]'s choice list is the stage's own [o_cs], where
   today it is an existential [cs0] the input claim carries a lower bound
   for. ---- *)
Definition ecl_pure (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) : Prop :=
  eout_pure k ho so (LogEntryDefs.ch_acc H)
  /\ cs_len_ok so
  /\ ps_len_ok so
  /\ ein_pure k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (o_cs so)
  /\ ch_arm_era k ho H
  /\ o_E so = ch_E H
  /\ dl_ok so (LogEntryDefs.ch_dl H).

(* the two events that touch neither the log nor the arm leave every
   clause but [eout_pure]'s and [ein_pure]'s own arguments alone *)
Lemma ecl_pure_arm (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) :
  ecl_pure k ho so H -> ch_arm_era k ho H.
Proof. by intros (_ & _ & _ & _ & Hera & _ & _). Qed.

Lemma ecl_pure_E (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) :
  ecl_pure k ho so H -> o_E so = ch_E H.
Proof. by intros (_ & _ & _ & _ & _ & HE & _). Qed.

(* THE DELIVERED BYTES ARE INSIDE THE ERA'S INPUT.  The log's echoed slice
   IS the era's list up to the arm in flight, and the read never hands out
   more than the log has echoed -- so a lower bound on the DELIVERED input
   is a lower bound on the era's, which is what every write step reads
   [inp_lb] against. *)
Lemma ecl_pure_dl_E (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) :
  ecl_pure k ho so H ->
  (snd <$> LogEntryDefs.ch_dl H) `prefix_of` (snd <$> o_E so).
Proof.
  intros Hall. destruct Hall as (_ & _ & _ & Hin & _ & HE & _).
  destruct Hin as (_ & _ & _ & Hdlp & _).
  rewrite HE /ch_E.
  etrans; [exact (epu_fmap_prefix snd _ _ Hdlp) |].
  rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log H))).
  apply epu_fmap_prefix. by apply prefix_app_r.
Qed.

(* THE READER'S STAGE FACT, off the claim's own pure part.  It used to be a
   STORED field of the input claim's two arms, carried there because the
   reader and the writer read two different resources; with one claim it is
   a CONSEQUENCE of [eout_pure]'s pin and [cs_len_ok]'s length law, so
   nothing has to keep the two in step. *)
Lemma ecl_pure_rd_stage (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) :
  ecl_pure k ho so H -> rd_stage (o_ps so) (o_cs so) (snd <$> o_E so).
Proof.
  intros (Hout & Hcsl & _ & _ & _ & _).
  destruct Hout as (_ & _ & _ & _ & Hpsb & Hpin & Hcsb & _).
  rewrite /rd_stage. split_and!;
    [exact Hpsb | exact Hcsb | exact Hpin |].
  rewrite Hcsl. case_decide as Hd.
  - (* AT A COMPLETED LINE the list is one short, and so is the count of
       lines the input has once its last byte -- the newline -- is dropped *)
    destruct Hd as [_ Hr]. rewrite (nlines_removelast _ Hr). lia.
  - apply nlines_prefix, epu_removelast_prefix.
Qed.

(* ---- FILING THE ENTRY PRESERVES THE CLAIM, WITH THE STAGE UNCHANGED.
   This is what the settled/window split costs today and what the merge
   buys: there is no arm to choose, no counter to agree with, and the
   writer's [pro_pin] at [length (o_E so)] IS the reader's stage fact at
   the log's new echo count, because [ch_E_close_len] makes the two
   lengths equal. ---- *)
Lemma ecl_pure_close (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) :
  ConsLog.cons_hist_ok H ->
  ConsLog.cons_ev_ok H ConsLog.EvClose ->
  ecl_pure k ho so H ->
  ecl_pure k ho so (ConsLog.cons_step H ConsLog.EvClose).
Proof.
  intros Hok Hev Hecl.
  pose proof (ch_E_close H) as Hclose.
  pose proof (ch_E_close_len H) as Hlen.
  pose proof (ConsLog.cons_hist_ok_step H ConsLog.EvClose Hok Hev) as Hok'.
  unfold ConsLog.cons_hist_ok in Hok'. destruct Hok' as [Hlog' _].
  destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha; cycle 1.
  { rewrite /ConsLog.cons_step Ha. exact Hecl. }
  destruct Hecl as (Hout & Hcs & Hps & Hin & Hera & HE & Hdlok).
  destruct Hin as (_ & Hdsc & Hbts & Hdl & _ & _ & _ & Hall).
  rewrite /ch_arm_era Ha in Hera.
  destruct Hera as (Hdseg & Hboots & _ & _ & _ & Hcsa & _).
  (* (A1) AT THE CLOSE: the arm's echo IS the byte ([ch_arm_era], recorded
     at the open) and the kernel says a store arm sends its byte before it
     closes (K3), so the entry filed is echoed. *)
  destruct Hev as (a & Ha2 & _ & HK3). rewrite Ha in Ha2.
  injection Ha2 as <-.
  cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_byte LogEntryDefs.ca_sent
       le_echo le_byte fst snd] in HK3.
  assert (Hj : j = 1%nat) by (apply HK3; exact Hcsa).
  assert (Hech : log_echoed (h, c, take j cs)).
  { rewrite Hcsa Hj. cbn [take]. exact (log_echoed_echo h c). }
  destruct Hout as (Hacc & Hw & HEi & HEb & Hpsf & Hpin & Hcsf & Hdse & Hpre & Hle & Hbo).
  rewrite /ConsLog.cons_step Ha in Hlog' Hlen |- *.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl LogEntryDefs.ch_arm] in Hlog', Hlen |- *.
  (* the era's list has not moved, so the new log's echoed slice IS [o_E so] *)
  assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H ++ [(h, c, take j cs)]))
                 = o_E so).
  { rewrite HE -Hclose /ch_E /ConsLog.cons_step Ha.
    cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E]. by rewrite app_nil_r. }
  split_and!.
  - (* eout_pure: the accepted bytes did not move *)
    by split_and!.
  - exact Hcs.
  - exact Hps.
  - (* ein_pure at the new log *)
    split_and!.
    + exact Hlog'.
    + intros e He. apply elem_of_app in He as [He | He].
      * exact (Hdsc e He).
      * apply elem_of_list_singleton in He as ->.
        cbn [le_hist fst snd]. exact Hdseg.
    + intros e He. apply elem_of_app in He as [He | He].
      * exact (Hbts e He).
      * apply elem_of_list_singleton in He as ->.
        cbn [le_hist fst snd]. exact Hboots.
    + (* the delivered prefix survives: the log's echoed slice only grows *)
      rewrite (echoed_snoc_yes _ _ Hech).
      by apply (prefix_app_r _ _ [(le_hist (h, c, take j cs),
                                   le_byte (h, c, take j cs))]).
    + by rewrite Hseg.
    + by rewrite Hseg.
    + (* the reader's line count, off the writer's own [cs_len_ok] *)
      rewrite -(seg_of_snd (echoed _)) Hseg.
      rewrite /cs_len_ok in Hcs.
      destruct (decide (o_w so = [] /\ rest_of (snd <$> o_E so) = [])); lia.
    + (* (A1): the entry filed is echoed *)
      apply Forall_app. split; [exact Hall | by rewrite Forall_singleton].
  - exact I.
  - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
    rewrite app_nil_r. by rewrite Hseg.
  - exact Hdlok.
Qed.

(* ---- THE OTHER FOUR EVENTS.  Three of them are FRAME lemmas: the output
   side's own step ([eout_pure] at the new accepted bytes, with [cs_len_ok]
   and [ps_len_ok]) is what today's [eout_step_write]/[_blk]/[_pro] and
   [eout_step_echo] already prove, and these say the INPUT-side clauses come
   along for free -- which is the whole point of merging the claims.  Only
   [EvOpen] needs anything new, and what it needs is the two era facts the
   arm will owe the entry it files. ---- *)

Lemma ecl_pure_out (k : nat) (ho : list mobs) (so so' : ostage)
    (H : LogEntryDefs.cons_hist) (b : bv 8) :
  (length (o_cs so) <= length (o_cs so'))%nat -> o_E so' = o_E so ->
  eout_pure k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
  cs_len_ok so' -> ps_len_ok so' ->
  (* (A2) at the NEW stage.  The delivered list does not move at a process
     byte, but the stage does: a byte written into a block puts [o_w so']
     past the empty list, so the clause is at the whole line count where it
     was one short.  That is what the writer's own [inp_lb] pays for. *)
  dl_ok so' (LogEntryDefs.ch_dl H) ->
  ecl_pure k ho so H ->
  ecl_pure k ho so' (ConsLog.cons_step H (ConsLog.EvOut b)).
Proof.
  intros Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
  rewrite /ecl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera | | exact Hdlok'].
  - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                | exact HEi | exact HEb | lia | exact Hall].
  - by rewrite HE' HE /ch_E.
Qed.

Lemma ecl_pure_read (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
  (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
  ecl_pure k ho so H ->
  ecl_pure k ho so (ConsLog.cons_step H (ConsLog.EvRead ws)).
Proof.
  intros Hpre (Hout & Hc & Hp & Hin & Hera & HE & Hdlok).
  destruct Hin as (Hlog & Hdsc & Hbts & _ & HEi & HEb & Hcnt & Hall).
  rewrite /ecl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera
              | by rewrite HE /ch_E |].
  - by split_and!.
  - (* (A2) IS MONOTONE IN THE DELIVERED LIST: the stage did not move and
       the read only appends *)
    apply (dl_ok_mono so (LogEntryDefs.ch_dl H)); [| exact Hdlok].
    rewrite length_app. lia.
Qed.

(* MOVING THE WITNESS.  [eout_pure]'s three [ho]-dependent clauses -- every
   filed segment is a prefix of the witness's open segment, the era's list
   fits inside its input count, and the era stamp -- transfer to a LATER
   history, and the transfer is exactly the log's own order fact: every
   logged history is below [h], every logged history is stamped at this
   era, so [ObsTrace.open_seg_prefix_boots] puts each filed segment inside
   [open_seg h].  It is what the echo's byte step derives inline today;
   named here because the ARM'S OPEN is where it is spent now. *)
Lemma eout_pure_move (k : nat) (ho h : list mobs) (so : ostage)
    (acc : list (bv 8)) (L : list log_entry) (dl : list (list mobs * bv 8)) :
  trace_shape h true ->
  obs_boots h = k ->
  (forall e, e ∈ L -> hist_ext (le_hist e) h) ->
  ein_pure k L dl (o_cs so) ->
  seg_of (echoed L) = o_E so ->
  (length (o_E so) <= length (ins (open_seg h)))%nat ->
  eout_pure k ho so acc -> eout_pure k h so acc.
Proof.
  intros Hsh Hk Hord Hin Hseg Hle
    (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb & Hdsc & _ & _ & _).
  destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi & _).
  split_and!; [exact Hacc | exact Hwpre | exact Hidx | exact Hbyte
              | exact Hpsb | exact Hpin | exact Hcsb | exact Hdsc
              | | exact Hle |].
  - rewrite -Hseg. apply Forall_lookup_2. intros j x Hx.
    rewrite /seg_of list_lookup_fmap in Hx.
    destruct (echoed L !! j) as [y |] eqn:Hy; [| discriminate].
    cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [fst].
    assert (Hyin : y ∈ echoed L) by (by eapply elem_of_list_lookup_2).
    destruct (echoed_elem_inv L y Hyin) as (e & He & _ & Hye).
    apply open_seg_prefix_boots.
    + rewrite -Hye. cbn [fst]. by destruct (Hord e He) as [Hpre _].
    + rewrite -Hye. cbn [fst]. rewrite (Hstamp e He). by rewrite Hk.
    + exact Hsh.
  - right. exact Hk.
Qed.

(* THE ARM OPENS: the witness moves to the byte's own history, and from
   here on the claim owes the entry the arm will file its era facts.

   THIS IS WHERE THE DROP IS REFUTED.  [consoleintr] may echo nothing, and
   with D2 gone the wire no longer says it did not: the kernel says WHY a
   drop would have happened ([ConsLog.cons_drop_ok], four arms), and the
   claim refutes each.  A NUL, a ^P and an erase are not bytes a
   disciplined user types ([EchoDisc.disc_input_byte_val],
   [EchoOutPure.disc_seg_no_erase]); a FULL RING would mean 128 echoed
   inputs the reader has not consumed, and (A2) puts every completed line
   whose block has begun inside the delivered list, so those 128 bytes
   would have to fit in ONE line ([EchoOutPure.drop_refuted]).  What comes
   out is [cs = [echo_of c]], recorded in [ch_arm_era] and spent at the
   close to keep (A1). *)
Lemma ecl_pure_open (k : nat) (ho : list mobs) (so : ostage)
    (H : LogEntryDefs.cons_hist) (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
  ConsLog.cons_hist_ok H ->
  ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
  disc_seg (open_seg h) -> obs_boots h = k ->
  disc h -> trace_shape h true ->
  ecl_pure k ho so H ->
  ecl_pure k h so (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
Proof.
  intros Hok Hev Hd Hb Hdh Hsh (Hout & Hc & Hp & Hin & _ & HE & Hdlok).
  pose proof Hev as (Hn & Hends & Hecho & Hord & Hwire & HK1f & HK2).
  pose proof (ch_E_open H h c cs Hn) as Hopen.
  (* (K1) ALLOWS FOR UARTINIT'S RECEIVE FLUSH, and the discipline refutes
     it: a disciplined user types nothing before the first prompt, so the
     output-free window the flush could have eaten holds no input
     ([EchoOutPure.flush_lost_zero]).  What is left is the plain count. *)
  assert (HK1 : (length (LogEntryDefs.ch_log H) + 1)%nat
                = length (ins (open_seg h))).
  { destruct HK1f as (f & Hfl & Hcnt).
    rewrite (flush_lost_zero h f Hsh Hdh Hfl) Nat.add_0_r in Hcnt.
    by rewrite -ins_obs_ins in Hcnt. }
  pose proof (open_seg_ends_in h c Hends) as Hends'.
  (* the era's list IS the log's echoed slice while no arm is open *)
  assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H)) = o_E so).
  { rewrite HE /ch_E Hn. cbn [ch_arm_E]. by rewrite app_nil_r. }
  (* (K1) + (A1): the era has echoed every input of the segment but this
     one -- the kernel's FIFO discipline, not a fact about the wire *)
  assert (Hall : Forall log_echoed (LogEntryDefs.ch_log H))
    by (by destruct Hin as (_ & _ & _ & _ & _ & _ & _ & Hq)).
  assert (Hcnt : length (o_E so)
                 = (length (ins (open_seg h)) - 1)%nat).
  { rewrite -Hseg seg_of_length (echoed_all_len _ Hall). lia. }
  assert (Hle : (length (o_E so) <= length (ins (open_seg h)))%nat) by lia.
  pose proof (eout_pure_move k ho h so (LogEntryDefs.ch_acc H)
                (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H)
                Hsh Hb Hord Hin Hseg Hle Hout) as Hout'.
  (* THE ERA'S INPUT IS THE SEGMENT'S, MINUS THE BYTE BEING TYPED *)
  assert (Hpl : forall j x, o_E so !! j = Some x -> x.1 `prefix_of` open_seg h).
  { destruct Hout' as (_ & _ & _ & _ & _ & _ & _ & _ & Hpre1 & _).
    intros j x Hx. exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx). }
  assert (Hidx : E_index (o_E so)) by (by destruct Hout as (_ & _ & Hq & _)).
  assert (Hbytes : (snd <$> o_E so)
                   = take (length (LogEntryDefs.ch_log H)) (ins (open_seg h))).
  { rewrite (E_bytes_of_hist (o_E so) (open_seg h) Hidx Hpl Hle).
    by replace (length (o_E so)) with (length (LogEntryDefs.ch_log H)) by lia. }
  (* the byte typed is a byte the discipline allows *)
  assert (Hcin : c ∈ ins (open_seg h)).
  { destruct Hends' as [h0 Hh0]. rewrite Hh0 ins_app ins_in.
    apply elem_of_app. right. apply elem_of_list_here. }
  pose proof (disc_drop_byte _ c Hd Hcin) as (_ & _ & Hner).
  (* THE ARM ECHOES ITS BYTE: the drop and the erase arms are refuted *)
  assert (Hcs : cs = [echo_of c]).
  { destruct Hecho as [Hnil | [Hech | [Herase _]]]; [| exact Hech |];
      last first.
    { exfalso. rewrite Hner in Herase. discriminate. }
    exfalso.
    exact (cons_drop_refuted h c (LogEntryDefs.ch_log H)
             (LogEntryDefs.ch_dl H) (snd <$> o_E so) (o_w so)
             HK1 Hall Hdlok Hbytes Hd Hcin (HK2 Hnil)). }
  rewrite /ecl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl LogEntryDefs.ch_arm].
  split_and!; [exact Hout' | exact Hc | exact Hp | exact Hin | | | exact Hdlok].
  - rewrite /ch_arm_era. cbn [LogEntryDefs.ch_arm LogEntryDefs.ch_log].
    split_and!; [exact Hd | exact Hb | exact Hdh | exact Hsh | reflexivity
                | exact Hcs | exact HK1].
  - rewrite HE -Hopen /ConsLog.cons_step /ch_E.
    by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
Qed.

(* the echoed byte goes out: the era's list grows by exactly that entry,
   which is what the output side's own step already says *)
Lemma ecl_pure_byte (k : nat) (ho ho' : list mobs) (so so' : ostage)
    (H : LogEntryDefs.cons_hist) (b : bv 8) (h : list mobs) (c : bv 8) :
  LogEntryDefs.ch_arm H = Some (h, c, [echo_of c], 0%nat) ->
  (* THE WITNESS DOES NOT MOVE: it is the arm's own history already, by
     [ch_arm_era]'s tie, so the byte step names the same one. *)
  ho' = h ->
  (length (o_cs so) <= length (o_cs so'))%nat ->
  o_E so' = o_E so ++ [(open_seg h, c)] ->
  eout_pure k ho' so' (LogEntryDefs.ch_acc H ++ [b]) ->
  cs_len_ok so' -> ps_len_ok so' ->
  dl_ok so' (LogEntryDefs.ch_dl H) ->
  ecl_pure k ho so H ->
  (* THE WITNESS MOVES: the echo re-establishes the claim's facts at the
     byte's OWN history, which is what today's step does too. *)
  ecl_pure k ho' so' (ConsLog.cons_step H (ConsLog.EvByte b)).
Proof.
  intros Ha Hw Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
  pose proof (ch_E_byte_echo H b h c Ha) as Hgrow.
  rewrite /ecl_pure /ConsLog.cons_step Ha.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp
              | split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                            | exact HEi | exact HEb | lia | exact Hall]
              | | | exact Hdlok'].
  - rewrite /ch_arm_era Ha in Hera. rewrite /ch_arm_era.
    cbn [LogEntryDefs.ch_arm LogEntryDefs.ch_log].
    destruct Hera as (Hds & Hb & Hd & Hshh & _ & Hcsa & Hk1). by split_and!.
  - rewrite HE' HE -Hgrow /ConsLog.cons_step Ha.
    by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
Qed.

Section echo_out.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  (* THE TAINT, ABSTRACTLY.  [AppEcho.echo_taint] is [mono_nat_lb_own
     (eg_taint γ) 1]; this file takes it as a parameter so that it sits
     BELOW [AppEcho] and the two claims can be read without the era-0 pin
     cone. *)
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.


  (* ---- the era's ghosts, keyed by the ERA NUMBER ---- *)

  (* PERSISTENT: era [k]'s ghosts.  Keyed by the era NUMBER, so a claim at
     [k] and a writer agree on which ghosts they mean by function
     application, and no injectivity obligation arises anywhere. *)
  Definition era_pin (k : nat) (v : era_pins) : iProp Σ :=
    ghost_map_elem (eg_pin γ) k DfracDiscarded v.

  Global Instance era_pin_persistent k v : Persistent (era_pin k v).
  Proof using . rewrite /era_pin. apply _. Qed.
  Global Instance era_pin_timeless k v : Timeless (era_pin k v).
  Proof using . rewrite /era_pin. apply _. Qed.

  Lemma era_pin_agree k v v' : era_pin k v -∗ era_pin k v' -∗ ⌜v = v'⌝.
  Proof using .
    rewrite /era_pin. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. exact Heq.
  Qed.

  (* THE CURSOR: the era's process-byte count, in two halves of a MONOTONE
     counter.  The OUTPUT CLAIM holds one ([turn_auth], always at the
     stage's own [pcount]); the other travels in the programs' payloads
     (init's [app_turn], then fork [Rc], exit/wait [Q]).  THE ECHO NEVER
     TOUCHES IT ([pcount_echo]).  A monotone counter and not a ghost
     variable, so that the claim can PUBLISH a persistent lower bound of it
     ([turn_lb]) -- the echo deposits one into the input claim, the read
     hands it to the reader, and a holder of the writer's half compares
     ([turn_lb_le]) without opening any claim.  That comparison is what
     refutes an untainted read at a prompt the writer has not written
     ([EchoLinks.ewc_owed_read_refute]). *)
  Definition turn (v : era_pins) (P : nat) : iProp Σ :=
    mono_nat_auth_own (ep_go v) (1/2) P.
  Definition turn_auth (v : era_pins) (P : nat) : iProp Σ :=
    mono_nat_auth_own (ep_go v) (1/2) P.
  Definition turn_lb (v : era_pins) (m : nat) : iProp Σ :=
    mono_nat_lb_own (ep_go v) m.

  Global Instance turn_timeless v P : Timeless (turn v P).
  Proof using . rewrite /turn. apply _. Qed.
  Global Instance turn_auth_timeless v P : Timeless (turn_auth v P).
  Proof using . rewrite /turn_auth. apply _. Qed.
  Global Instance turn_lb_timeless v m : Timeless (turn_lb v m).
  Proof using . rewrite /turn_lb. apply _. Qed.
  Global Instance turn_lb_persistent v m : Persistent (turn_lb v m).
  Proof using . rewrite /turn_lb. apply _. Qed.

  Lemma turn_agree v P P' : turn v P -∗ turn_auth v P' -∗ ⌜P = P'⌝.
  Proof using .
    rewrite /turn /turn_auth. iIntros "H1 H2".
    iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[_ Heq].
    iPureIntro. exact Heq.
  Qed.

  (* the cursor only advances *)
  Lemma turn_update v P P' P'' :
    (P <= P'')%nat ->
    turn v P -∗ turn_auth v P' ==∗ turn v P'' ∗ turn_auth v P''.
  Proof using .
    intros Hle. rewrite /turn /turn_auth. iIntros "H1 H2".
    iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[_ <-].
    iAssert (mono_nat_auth_own (ep_go v) 1 P) with "[H1 H2]" as "H".
    { iEval (rewrite -Qp.half_half). iSplitL "H1"; [iExact "H1" | iExact "H2"]. }
    iMod (mono_nat_own_update P'' with "H") as "[H _]"; [exact Hle |].
    iModIntro. iEval (rewrite -Qp.half_half) in "H". iDestruct "H" as "[H1 H2]".
    iFrame "H1 H2".
  Qed.

  Lemma turn_lb_get v P : turn_auth v P -∗ turn_lb v P.
  Proof using . rewrite /turn_auth /turn_lb. iApply mono_nat_lb_own_get. Qed.

  Lemma turn_lb_le v P m : turn v P -∗ turn_lb v m -∗ ⌜(m <= P)%nat⌝.
  Proof using .
    rewrite /turn /turn_lb. iIntros "H1 H2".
    iDestruct (mono_nat_lb_own_valid with "H1 H2") as %[_ Hle].
    iPureIntro. exact Hle.
  Qed.

  Lemma turn_lb_weaken v m m' : (m' <= m)%nat -> turn_lb v m -∗ turn_lb v m'.
  Proof using . intros Hle. rewrite /turn_lb. by iApply mono_nat_lb_own_le. Qed.

  (* THE LINE CHOICES, as a monotone list: the output claim holds the
     authority, a writer holds a persistent lower bound (review S9). *)
  Definition cs_auth (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gcs v) (●ML (l : list (leibnizO nat))).
  Definition cs_lb (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gcs v) (◯ML (l : list (leibnizO nat))).

  Global Instance cs_lb_persistent v l : Persistent (cs_lb v l).
  Proof using . rewrite /cs_lb. apply _. Qed.
  Global Instance cs_lb_timeless v l : Timeless (cs_lb v l).
  Proof using . rewrite /cs_lb. apply _. Qed.
  Global Instance cs_auth_timeless v l : Timeless (cs_auth v l).
  Proof using . rewrite /cs_auth. apply _. Qed.

  Lemma cs_lb_get v l : cs_auth v l -∗ cs_auth v l ∗ cs_lb v l.
  Proof using .
    rewrite /cs_auth /cs_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (l : list (leibnizO nat))) with "H")
      as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma cs_auth_grow v l a :
    cs_auth v l ==∗ cs_auth v (l ++ [a]) ∗ cs_lb v (l ++ [a]).
  Proof using .
    rewrite /cs_auth /cs_lb. iIntros "H".
    iMod (own_update _ _ (●ML ((l ++ [a]) : list (leibnizO nat)))
            with "H") as "H".
    { apply mono_list_update. by eexists. }
    iModIntro. iDestruct (own_mono _ _ (◯ML ((l ++ [a]) : list (leibnizO nat)))
                            with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma cs_lb_prefix v l l' : cs_auth v l -∗ cs_lb v l' -∗ ⌜l' `prefix_of` l⌝.
  Proof using .
    rewrite /cs_auth /cs_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  (* THE PROLOGUE CHOICES, the same monotone list one round later: the
     output claim holds the authority, a writer a persistent lower bound.
     A writer's bound is worth a PREFIX of the stream and not an equality
     while the round it is standing in has not settled ([pro_pin],
     [proc_stream_prefix]) -- which is exactly the difference between the
     banner and the byte that chooses. *)
  Definition ps_auth (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gps v) (●ML (l : list (leibnizO nat))).
  Definition ps_lb (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gps v) (◯ML (l : list (leibnizO nat))).

  Global Instance ps_lb_persistent v l : Persistent (ps_lb v l).
  Proof using . rewrite /ps_lb. apply _. Qed.
  Global Instance ps_lb_timeless v l : Timeless (ps_lb v l).
  Proof using . rewrite /ps_lb. apply _. Qed.
  Global Instance ps_auth_timeless v l : Timeless (ps_auth v l).
  Proof using . rewrite /ps_auth. apply _. Qed.

  Lemma ps_lb_get v l : ps_auth v l -∗ ps_auth v l ∗ ps_lb v l.
  Proof using .
    rewrite /ps_auth /ps_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (l : list (leibnizO nat))) with "H")
      as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma ps_auth_grow v l a :
    ps_auth v l ==∗ ps_auth v (l ++ [a]) ∗ ps_lb v (l ++ [a]).
  Proof using .
    rewrite /ps_auth /ps_lb. iIntros "H".
    iMod (own_update _ _ (●ML ((l ++ [a]) : list (leibnizO nat)))
            with "H") as "H".
    { apply mono_list_update. by eexists. }
    iModIntro. iDestruct (own_mono _ _ (◯ML ((l ++ [a]) : list (leibnizO nat)))
                            with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma ps_lb_prefix v l l' : ps_auth v l -∗ ps_lb v l' -∗ ⌜l' `prefix_of` l⌝.
  Proof using .
    rewrite /ps_auth /ps_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  (* THE ERA'S ECHOED LIST, as a monotone list of ENTRIES (and no longer a
     mono_nat of its length).  The OUTPUT claim holds the authority; the
     INPUT claim holds a lower bound AT THE LOG'S OWN SLICE
     ([seg_of (echoed pops)]), and that bound -- read against the authority
     at the echo, and against the append's own carried bound at the append
     -- is what ties the log to the era's stage now that no ledger sees
     both.  A writer's [inp_lb] is the BYTES of one. *)
  Definition Elist_auth (v : era_pins) (E : list (list mobs * bv 8)) : iProp Σ :=
    own (ep_gE v) (●ML (E : list (leibnizO (list mobs * bv 8)))).
  Definition Elist_lb (v : era_pins) (E : list (list mobs * bv 8)) : iProp Σ :=
    own (ep_gE v) (◯ML (E : list (leibnizO (list mobs * bv 8)))).

  Global Instance Elist_lb_persistent v E : Persistent (Elist_lb v E).
  Proof using . rewrite /Elist_lb. apply _. Qed.
  Global Instance Elist_lb_timeless v E : Timeless (Elist_lb v E).
  Proof using . rewrite /Elist_lb. apply _. Qed.
  Global Instance Elist_auth_timeless v E : Timeless (Elist_auth v E).
  Proof using . rewrite /Elist_auth. apply _. Qed.

  Lemma Elist_lb_get v E : Elist_auth v E -∗ Elist_auth v E ∗ Elist_lb v E.
  Proof using .
    rewrite /Elist_auth /Elist_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (E : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma Elist_auth_grow v E x :
    Elist_auth v E ==∗ Elist_auth v (E ++ [x]) ∗ Elist_lb v (E ++ [x]).
  Proof using .
    rewrite /Elist_auth /Elist_lb. iIntros "H".
    iMod (own_update _ _
            (●ML ((E ++ [x]) : list (leibnizO (list mobs * bv 8))))
            with "H") as "H".
    { apply mono_list_update. by eexists. }
    iModIntro.
    iDestruct (own_mono _ _
                 (◯ML ((E ++ [x]) : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma Elist_prefix v E E' :
    Elist_auth v E -∗ Elist_lb v E' -∗ ⌜E' `prefix_of` E⌝.
  Proof using .
    rewrite /Elist_auth /Elist_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  (* TWO LOWER BOUNDS OF ONE ERA'S LIST ARE COMPARABLE, and that -- with the
     two lengths, which the window counter supplies -- is the whole of the
     append's tie to its own echo. *)
  Lemma Elist_lb_cmp v E1 E2 :
    Elist_lb v E1 -∗ Elist_lb v E2 -∗
      ⌜E1 `prefix_of` E2 \/ E2 `prefix_of` E1⌝.
  Proof using .
    rewrite /Elist_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply mono_list_lb_op_valid_L in Hv.
  Qed.

  (* ...and the same for the two choice lists: what lets a holder of the
     writer's bounds line them up with the bounds a read hands out *)
  Lemma cs_lb_cmp v l1 l2 :
    cs_lb v l1 -∗ cs_lb v l2 -∗ ⌜l1 `prefix_of` l2 \/ l2 `prefix_of` l1⌝.
  Proof using .
    rewrite /cs_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply mono_list_lb_op_valid_L in Hv.
  Qed.

  Lemma ps_lb_cmp v l1 l2 :
    ps_lb v l1 -∗ ps_lb v l2 -∗ ⌜l1 `prefix_of` l2 \/ l2 `prefix_of` l1⌝.
  Proof using .
    rewrite /ps_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply mono_list_lb_op_valid_L in Hv.
  Qed.

  Lemma Elist_lb_weaken v E E' :
    E' `prefix_of` E -> Elist_lb v E -∗ Elist_lb v E'.
  Proof using .
    intros Hp. rewrite /Elist_lb. iApply own_mono.
    apply mono_list_lb_mono. exact Hp.
  Qed.

  (* ---- THE ERA'S DELIVERED LIST, the authority [inp_lb] is a bound of.
         Same algebra as the echoed list one entry above; what differs is
         WHO moves it -- the READ does, and nothing else. ---- *)
  Definition dl_list_auth (v : era_pins) (D : list (list mobs * bv 8))
    : iProp Σ := own (ep_gdll v) (●ML (D : list (leibnizO (list mobs * bv 8)))).
  Definition dl_list_lb (v : era_pins) (D : list (list mobs * bv 8))
    : iProp Σ := own (ep_gdll v) (◯ML (D : list (leibnizO (list mobs * bv 8)))).

  Global Instance dl_list_lb_persistent v D : Persistent (dl_list_lb v D).
  Proof using . rewrite /dl_list_lb. apply _. Qed.
  Global Instance dl_list_lb_timeless v D : Timeless (dl_list_lb v D).
  Proof using . rewrite /dl_list_lb. apply _. Qed.
  Global Instance dl_list_auth_timeless v D : Timeless (dl_list_auth v D).
  Proof using . rewrite /dl_list_auth. apply _. Qed.

  Lemma dl_list_lb_get v D : dl_list_auth v D -∗ dl_list_auth v D ∗ dl_list_lb v D.
  Proof using .
    rewrite /dl_list_auth /dl_list_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (D : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma dl_list_auth_grow v D ws :
    dl_list_auth v D ==∗ dl_list_auth v (D ++ ws) ∗ dl_list_lb v (D ++ ws).
  Proof using .
    rewrite /dl_list_auth /dl_list_lb. iIntros "H".
    iMod (own_update _ _
            (●ML ((D ++ ws) : list (leibnizO (list mobs * bv 8))))
            with "H") as "H".
    { apply mono_list_update. by eexists. }
    iModIntro.
    iDestruct (own_mono _ _
                 (◯ML ((D ++ ws) : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma dl_list_prefix v D D' :
    dl_list_auth v D -∗ dl_list_lb v D' -∗ ⌜D' `prefix_of` D⌝.
  Proof using .
    rewrite /dl_list_auth /dl_list_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  Lemma dl_list_lb_cmp v D1 D2 :
    dl_list_lb v D1 -∗ dl_list_lb v D2 -∗
      ⌜D1 `prefix_of` D2 \/ D2 `prefix_of` D1⌝.
  Proof using .
    rewrite /dl_list_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply mono_list_lb_op_valid_L in Hv.
  Qed.

  Lemma dl_list_lb_weaken v D D' :
    D' `prefix_of` D -> dl_list_lb v D -∗ dl_list_lb v D'.
  Proof using .
    intros Hp. rewrite /dl_list_lb. iApply own_mono.
    apply mono_list_lb_mono. exact Hp.
  Qed.

  (* THE WRITER'S BOUND is a lower bound of the era's DELIVERED input, which
     is what a program can name: it knows the bytes a read handed it, never
     the entries they were filed as, and never the ones the console has
     echoed but not yet given up.

     IT BOUNDS THE DELIVERED LIST AND NOT THE ECHOED ONE, and that is the
     whole of (A3).  A block's first byte is written against this bound, so
     the step that files it KNOWS the reader has consumed the line the block
     answers -- which is what (A2) records and what the ring argument
     spends.  Every mint is still at a delivered prefix ([eturn] at the
     empty era, [ecl_step_read] at the window's far end), so no program
     proof sees the change: [inp_lb_prefix], [inp_lb_cmp] and [inp_lb_agree]
     are what a holder of two of them uses, and they are unchanged.

     Two lower bounds of one era's list are comparable ([dl_list_lb_cmp]),
     so the existentially quantified [D] inside is harmless. *)
  Definition inp_lb (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ D : list (list mobs * bv 8), dl_list_lb v D ∗ ⌜(snd <$> D) = I⌝)%I.

  Global Instance inp_lb_persistent v I : Persistent (inp_lb v I).
  Proof using . rewrite /inp_lb. apply _. Qed.
  Global Instance inp_lb_timeless v I : Timeless (inp_lb v I).
  Proof using . rewrite /inp_lb. apply _. Qed.

  Lemma inp_lb_of_dl_lb v D I :
    I `prefix_of` (snd <$> D) -> dl_list_lb v D -∗ inp_lb v I.
  Proof using .
    intros HI. iIntros "H".
    iDestruct (dl_list_lb_weaken v D (take (length I) D) (prefix_take D _)
                 with "H") as "H'".
    iExists (take (length I) D). iFrame "H'". iPureIntro.
    rewrite fmap_take. destruct HI as [z Hz]. rewrite Hz.
    by rewrite take_app_length.
  Qed.

  (* THE LAW THE WRITE SPENDS: the lower bound never runs past what the
     console has actually delivered.  The claim's own pure part
     ([ecl_pure_dl_E]) carries it the rest of the way, to the era's input. *)
  Lemma inp_lb_le v D I :
    dl_list_auth v D -∗ inp_lb v I -∗ ⌜I `prefix_of` (snd <$> D)⌝.
  Proof using .
    iIntros "Ha Hl". iDestruct "Hl" as (D') "[Hl %Heq]".
    iDestruct (dl_list_prefix with "Ha Hl") as %Hp.
    iPureIntro. rewrite -Heq. by apply epu_fmap_prefix.
  Qed.

  Lemma inp_lb_prefix v I I' :
    I' `prefix_of` I -> inp_lb v I -∗ inp_lb v I'.
  Proof using .
    intros HI. iIntros "Hl". iDestruct "Hl" as (D) "[Hl %Heq]".
    iApply (inp_lb_of_dl_lb v D I' with "Hl"). by rewrite Heq.
  Qed.

  Lemma inp_lb_cmp v I1 I2 :
    inp_lb v I1 -∗ inp_lb v I2 -∗
      ⌜I1 `prefix_of` I2 \/ I2 `prefix_of` I1⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (D1) "[H1 %Heq1]". iDestruct "H2" as (D2) "[H2 %Heq2]".
    iDestruct (dl_list_lb_cmp with "H1 H2") as %[Hp | Hp]; iPureIntro.
    - left. rewrite -Heq1 -Heq2. by apply epu_fmap_prefix.
    - right. rewrite -Heq1 -Heq2. by apply epu_fmap_prefix.
  Qed.

  Lemma inp_lb_agree v I1 I2 :
    length I1 = length I2 -> inp_lb v I1 -∗ inp_lb v I2 -∗ ⌜I1 = I2⌝.
  Proof using .
    intros Hlen. iIntros "H1 H2".
    iDestruct (inp_lb_cmp with "H1 H2") as %[Hp | Hp]; iPureIntro.
    - by apply prefix_length_eq; [| lia].
    - symmetry. by apply prefix_length_eq; [| lia].
  Qed.

  (* THE DELIVERED COUNT, in two halves: the input claim's and the
     reader's. *)
  Definition dl_cnt (v : era_pins) (q : Qp) (n : nat) : iProp Σ :=
    ghost_var (ep_gdl v) q n.

  Global Instance dl_cnt_timeless v q n : Timeless (dl_cnt v q n).
  Proof using . rewrite /dl_cnt. apply _. Qed.

  Lemma dl_cnt_agree v q1 q2 n1 n2 :
    dl_cnt v q1 n1 -∗ dl_cnt v q2 n2 -∗ ⌜n1 = n2⌝.
  Proof using .
    rewrite /dl_cnt. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. iPureIntro. exact Heq.
  Qed.

  Lemma dl_cnt_update v n1 n2 m :
    dl_cnt v (1/2) n1 -∗ dl_cnt v (1/2) n2 ==∗
      dl_cnt v (1/2) m ∗ dl_cnt v (1/2) m.
  Proof using .
    rewrite /dl_cnt. iIntros "H1 H2".
    by iMod (ghost_var_update_halves m with "H1 H2") as "[$ $]".
  Qed.

  (* THE CREDENTIAL INIT IS HANDED AT ITS ERA'S FIRST INSTRUCTION: the
     cursor at zero, the delivered count's other half, and the three
     lower bounds at the empty era. *)
  Definition eturn (k : nat) : iProp Σ :=
    (∃ v : era_pins,
       era_pin k v ∗ turn v 0%nat ∗ dl_cnt v (1/2) 0%nat
       ∗ cs_lb v [] ∗ ps_lb v [] ∗ inp_lb v [])%I.

  (* ====================================================================== *)
  (*  THE MERGED CLAIM (redesign lane R1) -- THE application's claim since  *)
  (*  R2; [eout] and [ein] are gone.                                        *)
  (*                                                                        *)
  (*  [eout] and [ein] AT ONCE, over ONE stage and ONE console history,     *)
  (*  with NO WINDOW COUNTER.  The two arms [ein] needed -- settled, and    *)
  (*  the chain-first window where the era's list is one ahead of the log   *)
  (*  -- are one arm here, because [ch_E] counts the in-flight entry as     *)
  (*  soon as its byte is out and [ch_E_close] says filing the entry does   *)
  (*  not move the list.  There was nothing left for [wcnt] to refute, and  *)
  (*  the lower bounds [ein] carried ([Elist_lb], [cs_lb], [ps_lb],         *)
  (*  [turn_lb]) went too: one claim holds the AUTHORITIES.                 *)
  (* ====================================================================== *)
  Definition ecl (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) : iProp Σ :=
    ( T
    ∨ ∃ (v : era_pins) (so : ostage),
        era_pin k v
        ∗ turn_auth v (pcount (o_ps so) (o_cs so) (o_E so) (o_w so))
        ∗ cs_auth v (o_cs so)
        ∗ ps_auth v (o_ps so)
        ∗ Elist_auth v (o_E so)
        ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
        (* ...AND THE DELIVERED LIST ITSELF (A3), beside its count.  The
           count is what a reader agrees with to place its window; the list
           is what a WRITER's [inp_lb] is a bound of. *)
        ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
        ∗ ⌜ecl_pure k ho so H⌝)%I.

  Global Instance ecl_timeless k ho H : Timeless (ecl k ho H).
  Proof using Timeless0. rewrite /ecl. apply _. Qed.

  (* ---- FILING THE LOG ENTRY NEEDS NO GHOST UPDATE AT ALL.

     This is the sharpest statement of what the merge bought.  The same move
     used to be a view shift: it picked between [ein]'s settled and window
     arms, re-split [wcnt], and handed the lent token back.  Here the stage, all
     four authorities and the delivered count are untouched -- only the pure
     side moves, by [ecl_pure_close] -- so the step is an ENTAILMENT, with
     no [==*], no invariant to open and no resource to find. ---- *)
  Lemma ecl_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    ecl k ho H -∗ ecl k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. rewrite /ecl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v so) "(Hpin & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, so. iFrame "Hpin Htn Hcs Hps HE".
    rewrite ch_dl_close. iFrame "Hdl Hdll". iPureIntro.
    by apply (ecl_pure_close k ho so H Hok Hev Hpure).
  Qed.

  (* ---- ...and neither does opening one -- but the OPEN is where the
     drop arm is refuted, so it now takes the kernel's own account of the
     event ([ConsLog.cons_ev_ok], which [WpUart.cons_link] hands over
     anyway) and reads [cons_drop_ok] against the claim's (A2). ---- *)
  Lemma ecl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    disc_seg (open_seg h) -> obs_boots h = k ->
    disc h -> trace_shape h true ->
    ecl k ho H -∗ ecl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh. rewrite /ecl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v so) "(Hpin & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, so. iFrame "Hpin Htn Hcs Hps HE".
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl]. iFrame "Hdl Hdll".
    iPureIntro.
    by apply (ecl_pure_open k ho so H h c cs Hok Hev Hd Hb Hdh Hsh Hpure).
  Qed.

  (* THE TAG -- [App.app_tag A c], and [AppEcho.echo_tag γ] with the taint
     abstracted, which is what [Happ_echo]'s tag equation says.  It is what
     the kernel hands the shift about the history the byte arrived at: the
     machine is on, and either the console is still disciplined or the
     application has already been paid off. *)
  Definition etag (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜disc h⌝ ∨ T))%I.

  Global Instance etag_persistent h : Persistent (etag h).
  Proof using Persistent0. rewrite /etag. apply _. Qed.
  Global Instance etag_timeless h : Timeless (etag h).
  Proof using Timeless0. rewrite /etag. apply _. Qed.

  Global Instance eturn_timeless k : Timeless (eturn k).
  Proof using . rewrite /eturn. apply _. Qed.

  (* ---- THE LICENCES ([App.al_sup] / [al_sup]) ---- *)





  Definition pin_map (h : list mobs) : iProp Σ :=
    (∃ Mp : gmap nat era_pins,
       ghost_map_auth (eg_pin γ) 1 Mp ∗ ⌜pin_dom Mp (obs_boots h)⌝)%I.

  Global Instance pin_map_timeless h : Timeless (pin_map h).
  Proof using . rewrite /pin_map. apply _. Qed.

  (* an event that starts no era leaves the map exactly where it was *)
  Lemma pin_map_step (h : list mobs) (e : mobs) :
    obs_boots [e] = 0%nat -> pin_map h -∗ pin_map (h ++ [e]).
  Proof using .
    intros He. rewrite /pin_map obs_boots_app He Nat.add_0_r. by iIntros "$".
  Qed.

  (* ...and the POWER-ON mints the era's pin.  The insert is legal because
     the map's bound says every era ever founded is at most [obs_boots h],
     and this one is [S] of it. *)
  Lemma pin_map_on (h : list mobs) (v : era_pins) :
    pin_map h ==∗
      pin_map (h ++ [ObsPowerOn]) ∗ era_pin (S (obs_boots h)) v.
  Proof using .
    rewrite /pin_map /era_pin obs_boots_app. cbn [obs_boots].
    rewrite Nat.add_1_r.
    iIntros "H". iDestruct "H" as (Mp) "[Hm %Hd]".
    iMod (ghost_map_insert_persist (S (obs_boots h)) v
            (pin_dom_absent _ _ Hd) with "Hm") as "[Hm #Hpin]".
    iModIntro. iFrame "Hpin". iExists _. iFrame "Hm".
    iPureIntro. by apply pin_dom_insert.
  Qed.

  (* ---- THE ERA'S GHOSTS AT FULL OWNERSHIP, and their split into the
         port's claim and init's credential ---- *)
  Definition era_full (v : era_pins) : iProp Σ :=
    (mono_nat_auth_own (ep_go v) 1 0%nat ∗ cs_auth v [] ∗ ps_auth v []
     ∗ Elist_auth v [] ∗ ghost_var (ep_gdl v) 1 0%nat
     ∗ dl_list_auth v [] ∗ mono_nat_auth_own (ep_secc v) 1 0%nat)%I.

  Global Instance era_full_timeless v : Timeless (era_full v).
  Proof using . rewrite /era_full. apply _. Qed.

  Lemma era_full_alloc : ⊢ |==> ∃ v : era_pins, era_full v.
  Proof using .
    iMod (mono_nat_own_alloc 0%nat) as (go) "[Ht _]".
    iMod (own_alloc (●ML ([] : list (leibnizO nat)))) as (gcs) "Hcs";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO nat)))) as (gps) "Hps";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO (list mobs * bv 8)))))
      as (gE) "HE"; [apply mono_list_auth_valid |].
    iMod (ghost_var_alloc 0%nat) as (gdl) "Hdl".
    iMod (own_alloc (●ML ([] : list (leibnizO (list mobs * bv 8)))))
      as (gdll) "Hdll"; [apply mono_list_auth_valid |].
    iMod (mono_nat_own_alloc 0%nat) as (gsc) "[Hsc _]".
    iModIntro. iExists (MkPins go gcs gps gE gdl gdll gsc).
    rewrite /era_full /cs_auth /ps_auth /Elist_auth /dl_list_auth /=.
    iFrame "Ht Hcs Hps HE Hdl Hdll Hsc".
  Qed.

  Lemma pcount_nil (ps cs : list nat) : pcount ps cs [] [] = 0%nat.
  Proof using . reflexivity. Qed.

  Lemma seg_of_echoed_nil : seg_of (echoed []) = [].
  Proof using . by rewrite echoed_nil /seg_of fmap_nil. Qed.

  (* THE FOUNDING, as a resource split: the era's ghosts become the port's
     claim at the start of their era and init's console credential. *)
  Lemma era_full_split_cl (k : nat) (v : era_pins) :
    era_pin k v -∗ era_full v -∗
      ecl k [] (LogEntryDefs.MkCH [] [] [] None) ∗ eturn k.
  Proof using .
    iIntros "#Hpin (Ht & Hcs & Hps & HE & Hdl & Hdll & _)".
    iAssert (turn_lb v 0%nat) as "#Htlb0".
    { rewrite /turn_lb. iApply (mono_nat_lb_own_get with "Ht"). }
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct "Ht" as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (dl_list_lb_get with "Hdll") as "[Hdll #Hdllb]".
    iSplitL "Ht1 Hcs Hps HE Hdl1 Hdll".
    { rewrite /ecl. iRight. iExists v, ostage0.
      cbn [o_ps o_cs o_E o_w ostage0 length LogEntryDefs.ch_dl].
      rewrite pcount_nil.
      iFrame "Hpin Ht1 Hcs Hps HE Hdl1 Hdll". iPureIntro.
      rewrite /ecl_pure.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      split_and!.
      - exact (eout_pure_0 k []).
      - exact cs_len_ok_0.
      - exact ps_len_ok_0.
      - exact (ein_pure_0 k).
      - by rewrite /ch_arm_era.
      - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
        rewrite app_nil_r. by rewrite seg_of_echoed_nil.
      - exact dl_ok_0. }
    rewrite /eturn. iExists v. iFrame "Hpin Ht2 Hdl2 Hcslb Hpslb".
    iApply (inp_lb_of_dl_lb v [] []); [apply prefix_nil | iExact "Hdllb"].
  Qed.

  (* ...and THE WHOLE LEDGER, which is what [AppEcho.echo_R] becomes. *)
  Definition echo_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γ) 1 (if decide (disc h) then 0%nat else 1%nat)
     ∗ pin_map h
     ∗ (⌜Forall good_out (cycles_of h)⌝ ∨ T))%I.

  Global Instance echo_led_timeless h : Timeless (echo_led h).
  Proof. rewrite /echo_led. apply _. Qed.

  (* WHAT THE BIRTH STEP YIELDS, i.e. what [AppEcho.echo_cl] becomes:
     [AppEcho.echo_birth] is two [own_alloc]s and this. *)
  Lemma echo_led_init :
    mono_nat_auth_own (eg_taint γ) 1 0%nat -∗
    ghost_map_auth (eg_pin γ) 1 (∅ : gmap nat era_pins) -∗
    echo_led [].
  Proof using .
    iIntros "Ht Hm". rewrite /echo_led /pin_map.
    rewrite decide_True; [| exact disc_nil].
    iFrame "Ht".
    iSplitL "Hm".
    { iExists ∅. iFrame "Hm". iPureIntro. apply pin_dom_empty. }
    iLeft. iPureIntro. rewrite /cycles_of /cycles_rev /=. constructor.
  Qed.
  (* ====================================================================== *)
  (*  5.  THE LEDGER'S STEPS                                                *)
  (* ====================================================================== *)

  (* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE cannot falsify a cycle
     that was good: the wire is unchanged and [sess] only grows with the
     input. *)
  Lemma good_out_step (seg : list mobs) (e : mobs) :
    obs_wire Uart0 [e] = [] -> good_out seg -> good_out (seg ++ [e]).
  Proof using .
    intros He Hg. rewrite /good_out obs_wire_app He app_nil_r.
    apply (expected_rel_ins_prefix (ins seg)); [| exact Hg].
    rewrite ins_app. by apply prefix_app_r.
  Qed.

  Lemma obs_wire_in (i : uart_id) (b : bv 8) : obs_wire Uart0 [ObsUartIn i b] = [].
  Proof using . by destruct i. Qed.

  Lemma obs_wire_out_other (i : uart_id) (b : bv 8) :
    i <> Uart0 -> obs_wire Uart0 [ObsUartOut i b] = [].
  Proof using . intros Hi. destruct i; [by destruct Hi | done]. Qed.

  Lemma io_singleton (e : mobs) :
    is_io e = true -> Forall (fun x => is_io x = true) [e].
  Proof using . intros He. constructor; [exact He | constructor]. Qed.

  (* THE MACHINE IS OFF AFTER A PowerOff, which is what makes [era_live]'s
     guarded conjunct vacuous there. *)
  Lemma trace_shape_off (h : list mobs) :
    trace_shape (h ++ [ObsPowerOff]) true -> False.
  Proof using .
    rewrite /trace_shape foldl_app.
    destruct (foldl obs_step (Some false) h) as [[|] |]; by cbn.
  Qed.

  Lemma phi_step_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
    Forall good_out (cycles_of h) -> Forall good_out (cycles_of (h ++ [e])).
  Proof using .
    intros Hsh Hio Hw HF.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs Hlast].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton in Hlast. rewrite Forall_singleton.
    apply good_out_step; [exact Hw | exact Hlast].
  Qed.

  Lemma phi_step_cons (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true ->
    good_out (open_seg h ++ [e]) ->
    Forall good_out (cycles_of h) -> Forall good_out (cycles_of (h ++ [e])).
  Proof using .
    intros Hsh Hio Hgo HF.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs _].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton. exact Hgo.
  Qed.

  (* THE POWER STEP -- AND THE FOUNDING OF THE ERA'S CLAIMS, ITS CURSOR AND
     ITS TOKEN (design page, section 2).  This is [App.Hpow]'s shape exactly:
     the on-arm allocates the era's four ghosts, mints its pin in the era map
     and splits the ghosts into the two port claims, init's console
     credential and the kernel's window token, at the era number
     [S (obs_boots h)] -- which [ObsTrace.obs_boots_app] makes the boot count
     of the POST-event history, i.e. the number the kernel's own stamp reads
     at every history of the new era.

     THIS IS THE ONLY STEP THAT TOUCHES THE ERA MAP'S AUTHORITY, which is
     what lets every link run without the ledger. *)
  Lemma echo_led_pow_cl (h : list mobs) (on : bool) :
    echo_led h ==∗
      echo_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else ecl (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)
              ∗ eturn (S (obs_boots h))).
  Proof using .
    iIntros "(Ht & Hpm & Hphi)". rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_power h on)).
    destruct on.
    - iDestruct (pin_map_step h ObsPowerOff eq_refl with "Hpm") as "Hpm".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm".
      rewrite cycles_of_off. iExact "Hphi".
    - iMod era_full_alloc as (v) "Hfull".
      iMod (pin_map_on h v with "Hpm") as "[Hpm #Hpin]".
      iDestruct (era_full_split_cl (S (obs_boots h)) v with "Hpin Hfull")
        as "(Hcl & Hturn)".
      iModIntro. iSplitR "Hcl Hturn".
      + iFrame "Ht Hpm".
        rewrite cycles_of_on.
        iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
        iLeft. iPureIntro. apply Forall_app. split; [exact Hg |].
        apply Forall_singleton. exact good_out_nil.
      + iFrame "Hcl Hturn".
  Qed.

  (* THE SUPPLY'S LAW AT THE MERGED CLAIM: a tainted era answers any event
     out of its taint arm, which is the whole of [App.al_sup]. *)
  Lemma ecl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    T -∗ ecl k ho H ==∗ ecl k ho (ConsLog.cons_step H ev).
  Proof using Persistent0. iIntros "#HT _". iModIntro. rewrite /ecl. by iLeft. Qed.

  (* THE OUTPUT STEP.  The obligation is UNGUARDED: the drain hands over
     [good_out] of the extended segment or the taint, and a byte reaching
     the wire in an era that has already broken the discipline arrives on
     the taint arm. *)
  Lemma echo_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (T ∨ ⌜i = Uart0 -> good_out (open_seg h ++ [ObsUartOut i b])⌝) -∗
    echo_led h ==∗ echo_led (h ++ [ObsUartOut i b]).
  Proof using .
    intros Hsh. iIntros "Hgo (Hcnt & Hpm & Hphi)".
    iDestruct (pin_map_step h (ObsUartOut i b) eq_refl with "Hpm") as "Hpm".
    rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_out h i b Hsh)).
    iModIntro. iFrame "Hcnt Hpm".
    iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
    iDestruct "Hgo" as "[HT | %Hgo]"; [by iRight |].
    iLeft. iPureIntro. destruct i.
    - exact (phi_step_cons h (ObsUartOut Uart0 b) Hsh eq_refl
               (Hgo eq_refl) Hg).
    - exact (phi_step_io h (ObsUartOut Uart1 b) Hsh eq_refl
               (obs_wire_out_other Uart1 b ltac:(discriminate)) Hg).
  Qed.

  Lemma echo_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    echo_led h ==∗
      echo_led (h ++ [ObsUartIn i b])
      ∗ (⌜disc (h ++ [ObsUartIn i b])⌝ ∨ mono_nat_lb_own (eg_taint γ) 1).
  Proof using .
    intros Hsh. iIntros "(Hcnt & Hpm & Hphi)".
    iDestruct (pin_map_step h (ObsUartIn i b) eq_refl with "Hpm") as "Hpm".
    iAssert (⌜Forall good_out (cycles_of (h ++ [ObsUartIn i b]))⌝ ∨ T)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro.
      apply (phi_step_io h (ObsUartIn i b) Hsh eq_refl (obs_wire_in i b) Hg). }
    rewrite /echo_led.
    destruct (decide (disc (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; last first.
      { destruct i;
          [ exact (disc_in h b Hsh Hd')
          | exact (proj1 (disc_other h (ObsUartIn Uart1 b) eq_refl I Hsh) Hd') ]. }
      iModIntro. iFrame "Hcnt Hpm Hphi". iLeft. iPureIntro. exact Hd'.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (disc h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hphi". iRight. iExact "Hlb".
  Qed.

  (* PHI's read at the end of the run, in the OWNER's form: the guard is the
     WHOLE history's discipline.  Once the taint is set [disc] is false
     forever ([EchoDisc.disc_prefix]), so the ledger's disjunction is exactly
     this implication. *)
  Lemma echo_led_phi (h : list mobs) :
    (T -∗ mono_nat_lb_own (eg_taint γ) 1) -∗
    echo_led h -∗ ⌜disc h -> Forall good_out (cycles_of h)⌝.
  Proof using .
    iIntros "HTT (Hcnt & _ & [%Hg | HT'])".
    { iPureIntro. by intros _. }
    iDestruct ("HTT" with "HT'") as "Hlb".
    iDestruct (mono_nat_lb_own_valid with "Hcnt Hlb") as %[_ Hle].
    iPureIntro. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.

  (* ====================================================================== *)
  (*  6.  THE STEPS THE LINKS SPEND                                         *)
  (* ====================================================================== *)

  (* NO STEP TAKES THE LEDGER.  Every authority an era has is in its claims,
     so a link opens the port invariant and nothing else -- which is what
     makes [App.Happ_echo] a CLOSED entailment (design page, F1). *)

  (* THE ECHO'S STEP.  It closes the line the writer has just finished and
     files the byte in the era's echoed list, which is where the era's INPUT
     grows.  Three pure facts carry it, and they are about BYTES rather than
     positions:

       - [EchoOutPure.sess_prefix_det] identifies the discipline's witness
         for the segment below this input with the claim's own transcript --
         the wire says what was typed -- and hands back that the round the
         closing line reads is SETTLED, which is what [pro_pin] needs at the
         input's new last line.  The witness is at the COMPLETED prefix
         ([LineWords.done_of]), because that is where the relaxed discipline
         pins the wire;
       - [EchoOutPure.next_input_of_complete] says the process output owed
         at this stage is complete.  At a line's first byte that is the pin
         again; mid-line the stage owes nothing, so there is nothing to say;
       - [EchoOutPure.E_disc_of_hist] says the era's bytes PARSE, off the
         segment's own discipline and the per-entry index law.  It replaces
         the positional reading ("E's j-th byte is byte [j mod 17] of the
         line"), which at a line per round says nothing.

     THE INPUT NUMBER IS THE KERNEL'S, NOT THE WIRE'S.  That the era has
     echoed EVERY input before this one is (K1) -- the receive FIFO is
     drained in arrival order -- plus (A1) -- every log entry is echoed.
     The premise below is the two of them at this arm; [ecl_step_byte] reads
     it out of [ch_arm_era], where the open recorded it. *)

  Lemma ecl_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    (length (LogEntryDefs.ch_log CH) + 1)%nat = length (ins (open_seg h)) ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
    ecl k ho CH ==∗
      ecl k h (ConsLog.cons_step CH (ConsLog.EvByte (echo_of c))).
  Proof using Persistent0.
    intros Hdisc Hsh Hk Hends Hwire Hord HK1 Harm. subst k.
    iIntros "Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. rewrite /ecl. by iLeft. }
    iDestruct "Hp" as (v so) "(#Hpin & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    pose proof Hcsb' as Hcsb.
    destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi
                     & Halle).
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log CH)) = o_E so).
    { rewrite HEtie /ch_E Harm ch_arm_E_open app_nil_r. reflexivity. }
    (* the byte's own facts, as in the landed proof *)
    pose proof (disc_seg'_open_seg h Hsh Hdisc) as Hd'.
    pose proof (disc_seg'_proj _ Hd') as Hdseg.
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    destruct (disc_seg'_pt_last (open_seg h) c Hd' Hends')
      as (ps' & cs' & Hok' & Hcs'b & Hlow').
    assert (Hprefixes : Forall (fun x => x.1 `prefix_of` open_seg h) (o_E so)).
    { rewrite -Hseg.
      apply Forall_lookup_2. intros j x Hx.
      rewrite /seg_of list_lookup_fmap in Hx.
      destruct (echoed (LogEntryDefs.ch_log CH) !! j) as [y |] eqn:Hy;
        [| discriminate].
      cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [fst].
      assert (Hyin : y ∈ echoed (LogEntryDefs.ch_log CH))
        by (by eapply elem_of_list_lookup_2).
      destruct (echoed_elem_inv (LogEntryDefs.ch_log CH) y Hyin)
        as (e & He & _ & Hye).
      apply open_seg_prefix_boots.
      - rewrite -Hye. cbn [fst]. by destruct (Hord e He) as [Hpre _].
      - rewrite -Hye. cbn [fst]. exact (Hstamp e He).
      - exact Hsh. }
    assert (Hpl : forall j x, o_E so !! j = Some x ->
                    x.1 `prefix_of` open_seg h)
      by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hprefixes Hx)).
    (* THE ERA'S INPUT IS THE SEGMENT'S, MINUS THE BYTE BEING TYPED.  (K1)
       and (A1) together: the log is complete below this input, and every
       entry of it is echoed. *)
    assert (Hoi : length (o_E so) = length (echoed (LogEntryDefs.ch_log CH)))
      by (by rewrite -Hseg seg_of_length).
    assert (Hcnt : length (o_E so) = (length (ins (open_seg h)) - 1)%nat)
      by (rewrite Hoi (echoed_all_len _ Halle); lia).
    assert (Hbytes : (snd <$> o_E so)
                     = take (length (o_E so)) (ins (open_seg h)))
      by (apply (E_bytes_of_hist (o_E so) (open_seg h) Hidx Hpl); lia).
    assert (Hnew' : forall x, x ∈ o_E so -> hist_ext x.1 (open_seg h)).
    { intros x Hx. apply elem_of_list_lookup in Hx as [jj Hj].
      destruct (Hidx jj x Hj) as [Hxe Hxlen].
      pose proof (Forall_lookup_1 _ _ _ _ Hprefixes Hj) as Hpx.
      apply lookup_lt_Some in Hj.
      split; [exact Hpx |].
      destruct Hpx as [z Hz]. destruct z as [| aa z'].
      - exfalso. rewrite app_nil_r in Hz. rewrite -Hz in Hxlen. lia.
      - rewrite Hz length_app /=. lia. }
    assert (Hup : obs_wire Uart0 (open_seg h)
                  `prefix_of` (D (o_ps so) (o_cs so) (o_E so) ++ o_w so))
      by (rewrite -Hacc; exact Hwire).
    (* THE WITNESS BELOW THE LAST INPUT IS THE CLAIM'S OWN TRANSCRIPT, and
       the round the closing line reads is settled -- by BYTES, not by an
       index ([EchoOutPure.sess_prefix_det]).  The discipline's bound is at
       the COMPLETE LINES of that input ([LineWords.done_of]), which is a
       PREFIX of the claim's; [pro_ok] does not notice, because the
       truncation drops no line ([LineWords.nlines_done]). *)
    assert (Hdi1 : disc_input (done_of (removelast (ins (open_seg h))))).
    { apply (disc_input_prefix _ (ins (open_seg h))); [| exact Hdseg].
      etrans; [apply done_of_prefix | apply epu_removelast_prefix]. }
    assert (Hok2 : pro_ok ps' cs'
                     (nlines (done_of (removelast (ins (open_seg h))))))
      by (rewrite nlines_done; exact Hok').
    assert (Hbelow : sess ps' cs' (done_of (removelast (ins (open_seg h))))
                     `prefix_of` sess (o_ps so) (o_cs so) (snd <$> o_E so)).
    { etrans; [exact Hlow' |]. etrans; [exact Hup |].
      by apply D_stage_prefix. }
    destruct (sess_prefix_det (o_ps so) ps' (o_cs so) cs'
                (done_of (removelast (ins (open_seg h)))) (snd <$> o_E so)
                Hpsb Hok2 Hcsb' Hcs'b Hpin Hbyte Hdi1 Hbelow)
      as (_ & Hokso & Heq).
    assert (Hlow : sess (o_ps so) (o_cs so)
                     (done_of (removelast (ins (open_seg h))))
                   `prefix_of` obs_wire Uart0 (open_seg h)).
    { rewrite -Heq. exact Hlow'. }
    pose proof (next_input_of_complete (o_ps so) (o_cs so) (o_E so) (o_w so)
                  (obs_wire Uart0 (open_seg h)) (open_seg h) c
                  (length (ins (open_seg h)))
                  Hbyte Hidx Hnew' Hends' eq_refl ltac:(lia) Hwpre
                  ltac:(rewrite -epu_removelast_take; exact Hlow) Hup)
      as Hweq.
    (* ...so the segment's input MINUS the byte just typed IS the era's *)
    assert (HI : removelast (ins (open_seg h)) = (snd <$> o_E so)).
    { rewrite Hbytes epu_removelast_take.
      replace (length (ins (open_seg h)) - 1)%nat with (length (o_E so))
        by lia.
      reflexivity. }
    assert (Hrnd : (pro_idx (o_cs so) (nlines (snd <$> o_E so))
                    < pro_rounds (o_ps so))%nat).
    { destruct Hokso as [_ Hokso].
      rewrite nlines_done HI in Hokso. exact Hokso. }
    (* the two laws at the new entry, which the claim carries on *)
    assert (Hidx2 : E_index (o_E so ++ [(open_seg h, c)])).
    { intros jj y Hy.
      destruct (decide (jj < length (o_E so))%nat) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. by apply Hidx. }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (o_E so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [fst snd]. split; [exact Hends' | lia]. }
    assert (Hpl2 : forall j x, (o_E so ++ [(open_seg h, c)]) !! j = Some x ->
                     x.1 `prefix_of` open_seg h).
    { intros jj y Hy.
      destruct (decide (jj < length (o_E so))%nat) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. exact (Hpl jj y Hy). }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (o_E so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [fst]. reflexivity. }
    assert (Hdisc2 : E_disc (o_E so ++ [(open_seg h, c)]))
      by exact (E_disc_of_hist _ (open_seg h) Hidx2 Hpl2 Hdseg).
    pose proof (cs_len_ok_echo so (open_seg h, c) Hcsb Hweq Hcsl) as Hcsl2.
    (* the pin survives the input's growth: every line strictly below is
       [Hpin]'s, and the one this echo closes is the round just settled *)
    assert (Hpin2 : pro_pin (o_ps so) (o_cs so) ((snd <$> o_E so) ++ [c])).
    { intros q Hq. rewrite nstarted_snoc in Hq.
      destruct (decide (q < nstarted (snd <$> o_E so))%nat) as [Hq2 | Hq2];
        [by apply Hpin |].
      assert (Hqe : q = nlines (snd <$> o_E so)).
      { pose proof (nlines_le_nstarted (snd <$> o_E so)). lia. }
      subst q. exact Hrnd. }
    iMod (Elist_auth_grow v (o_E so) (open_seg h, c) with "HE")
      as "[HE #HElb2]".
    iModIntro. rewrite /ecl. iRight.
      iExists v, (MkO (o_ps so) (o_cs so) (o_E so ++ [(open_seg h, c)]) []).
      cbn [o_ps o_cs o_E o_w].
      rewrite (pcount_echo (o_ps so) (o_cs so) (o_E so) (open_seg h, c)
                 (o_w so) Hweq).
      rewrite ch_dl_byte.
      iFrame "Hpin Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (ecl_pure_byte (obs_boots h) ho h so
               (MkO (o_ps so) (o_cs so) (o_E so ++ [(open_seg h, c)]) [])
               CH (echo_of c) h c Harm eq_refl);
        [cbn [o_cs]; lia | reflexivity | | | | | exact Hall0].
      - rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        + rewrite Hacc Hweq (D_app (o_ps so) (o_cs so) (o_E so) (open_seg h, c)).
          cbn [snd]. by rewrite app_nil_r app_assoc.
        + apply prefix_nil.
        + exact Hidx2.
        + exact Hdisc2.
        + exact Hpsb.
        + rewrite (fmap_snd_snoc (o_E so) (open_seg h, c)). cbn [snd].
          exact Hpin2.
        + exact Hcsb'.
        + rewrite Forall_app. split; [exact Hdsc |].
          rewrite Forall_singleton. cbn. exact Hdseg.
        + rewrite Forall_app. split; [exact Hprefixes |].
          rewrite Forall_singleton. cbn [fst]. reflexivity.
        + rewrite length_app. cbn [length]. lia.
        + by right.
      - exact Hcsl2.
      - exact (ps_len_ok_echo so (open_seg h, c) Hpsl).
      - (* (A2): the echo leaves the writer owing a whole block again *)
        exact (dl_ok_echo so (open_seg h, c) (LogEntryDefs.ch_dl CH)
                 Hcsb Hweq Hdlok).
  Qed.

  Lemma ecl_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    pro_pin ps0 cs0 I0 ->
    proc_stream ps0 cs0 I0 !! P = Some b ->
    era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    ecl k ho H ==∗
      ecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using Persistent0.
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /ecl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so) "(#Hpin2 & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
    { etrans; [exact HI0dl | exact (ecl_pure_dl_E k ho so H Hall0)]. }
    destruct (write_stage_byte ps0 (o_ps so) cs0 (o_cs so) (o_E so) (o_w so)
                I0 P b Hpsp Hpin0 Hcsp Hn HI0 HP Hb) as [HlenE Hnext].
    assert (Hcase : o_w so <> []
                    \/ rest_of (snd <$> o_E so) <> []
                    \/ (snd <$> o_E so) = []).
    { destruct (decide (o_w so = [])) as [Hw | Hw]; [| by left].
      destruct (decide (rest_of (snd <$> o_E so) = [])) as [Hm | Hm];
        [| by right; left].
      right; right.
      destruct (cs_len_ok_inv so Hcsl) as [[_ Hq] | [Hne _]]; last first.
      { exfalso. by apply Hne. }
      destruct (decide ((snd <$> o_E so) = [])) as [Hz | Hz]; [exact Hz |].
      exfalso.
      pose proof (prefix_length _ _ Hcsp) as Hlen0.
      pose proof (nlines_pos_of_rest_nil (snd <$> o_E so) Hz Hm) as Hpos.
      rewrite -HlenE in Hn. lia. }
    iMod (turn_update v P (pcount (o_ps so) (o_cs so) (o_E so) (o_w so)) (S P)
            ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iModIntro. iSplitR "Ht".
    - rewrite /ecl. iRight.
      iExists v, (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])).
      cbn [o_ps o_cs o_E o_w]. rewrite pcount_write -HP.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (ecl_pure_out k ho so
               (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])) H b);
        [cbn [o_cs]; lia | reflexivity | | | | | exact Hall0].
      + rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        * by rewrite Hacc app_assoc.
        * by apply prefix_snoc_lookup.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + exact (cs_len_ok_write so b Hcsl Hcase).
      + exact (ps_len_ok_write so b Hpsl).
      + (* (A2): the writer is now inside a block *)
        apply (dl_ok_out so (MkO (o_ps so) (o_cs so) (o_E so)
                               (o_w so ++ [b])));
          [reflexivity | cbn [o_w] | exact Hcase | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. iFrame "Ht Hpslb Hcslb Hilb".
  Qed.

  Lemma ecl_step_write_blk (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin ps0 cs0 I0 ->
    P = length (proc_before ps0 cs0 I0) ->
    (a < 4)%nat ->
    line_alts_of (last_ws I0) !!! a !! 0%nat = Some b ->
    era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    ecl k ho H ==∗
      ecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0)
         ∨ T).
  Proof.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hhead.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /ecl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so) "(#Hpin2 & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    pose proof Hcsb' as Hcsb.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
    { etrans; [exact HI0dl | exact (ecl_pure_dl_E k ho so H Hall0)]. }
    (* what the stage owes strictly below [I0] is the same under the
       writer's bounds *)
    assert (Hstream : proc_before ps0 cs0 I0
                      = proc_before (o_ps so) (o_cs so) I0).
    { apply (proc_before_cs_prefix ps0 (o_ps so) cs0 (o_cs so) I0
               Hpsp Hcsp Hpin0). lia. }
    (* the era's input is exactly [I0]: a further echo would have folded
       this line's WHOLE continuation into the stream, past the cursor *)
    assert (HlenE : (snd <$> o_E so) = I0).
    { destruct (decide ((snd <$> o_E so) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (proc_stream_before (o_ps so) (o_cs so) I0 (snd <$> o_E so)
                    HI0 ltac:(intros Hq; apply Hne; symmetry; exact Hq))
        as Hpre.
      apply prefix_length in Hpre.
      rewrite /proc_stream length_app -Hstream in Hpre.
      assert (Hne1 : pending_at (o_ps so) (o_cs so) I0 <> [])
        by (exact (pending_at_nonnil (o_ps so) (o_cs so) I0 Hcsb Hne0 Hr0)).
      assert (Hlen1 : (1 <= length (pending_at (o_ps so) (o_cs so) I0))%nat).
      { destruct (pending_at (o_ps so) (o_cs so) I0); [done | cbn; lia]. }
      rewrite /pcount in HP. lia. }
    (* ...and the writer stands at the line's first byte *)
    assert (Hwnil : o_w so = []).
    { assert (Hz : length (o_w so) = 0%nat).
      { rewrite /pcount in HP. rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    (* the claim's list is one short, so the writer's bound IS the list *)
    destruct (cs_len_ok_inv so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hcs0 : cs0 = o_cs so).
    { pose proof (prefix_length _ _ Hcsp) as Hle.
      destruct Hcsp as [z Hz]. rewrite Hz.
      assert (Hzn : z = []).
      { apply nil_length_inv. rewrite Hz length_app in Hle |- *.
        rewrite Hz length_app in Hq. lia. }
      by rewrite Hzn app_nil_r. }
    (* the byte the stage owes at the line's first position: the line is the
       LAST BODY of the input, and its alternative is what the write files *)
    assert (Hidx0 : (o_cs so ++ [a]) !!! (nlines I0 - 1)%nat = a).
    { rewrite list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hq Nat.sub_diag. reflexivity. }
    assert (Hpend : pending (o_ps so) (o_cs so ++ [a]) (o_E so) !! 0%nat
                    = Some b).
    { rewrite /pending HlenE /pending_at.
      rewrite decide_False; [| exact Hne0]. rewrite decide_True; [| exact Hr0].
      rewrite /alt_cont Hidx0 -(last_ws_lta I0).
      rewrite lookup_app_l; [exact Hhead |].
      destruct (line_alts_of (last_ws I0) !!! a) as [| z zs] eqn:Hz;
        [ exfalso; exact (line_alts_of_nonnil _ a Halt Hz) | cbn; lia ]. }
    (* THE NEW CHOICE IS NOT READ BELOW THE CURRENT LINE: neither by the
       transcript nor by the cursor, and the PROLOGUE rounds do not move
       either ([pro_idx_app_le] at the lines the stage has passed). *)
    assert (Hpinq : pro_pin (o_ps so) (o_cs so ++ [a]) (snd <$> o_E so)).
    { intros qq Hqq. rewrite pro_idx_app_le; [by apply Hpin |].
      rewrite HlenE (nstarted_rest_nil I0 Hr0) in Hqq. rewrite Hq. lia. }
    assert (HD : D (o_ps so) (o_cs so ++ [a]) (o_E so)
                 = D (o_ps so) (o_cs so) (o_E so)).
    { symmetry. apply (D_cs_prefix (o_ps so) (o_ps so) (o_cs so)
                         (o_cs so ++ [a]) (o_E so));
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpceq : pcount (o_ps so) (o_cs so) (o_E so) [b]
                    = pcount (o_ps so) (o_cs so ++ [a]) (o_E so) [b]).
    { apply (pcount_cs_prefix (o_ps so) (o_ps so) (o_cs so) (o_cs so ++ [a])
               (o_E so) [b]); [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpc2 : pcount (o_ps so) (o_cs so ++ [a]) (o_E so) [b] = S P).
    { rewrite -Hpceq /pcount HlenE -Hstream. cbn [length]. lia. }
    iMod (turn_update v P (pcount (o_ps so) (o_cs so) (o_E so) (o_w so)) (S P)
            ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (cs_auth_grow v (o_cs so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /ecl. iRight.
      iExists v, (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]).
      cbn [o_ps o_cs o_E o_w]. rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (ecl_pure_out k ho so
               (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]) H b);
        [cbn [o_cs]; rewrite length_app; cbn [length]; lia
        | reflexivity | | | | | exact Hall0].
      + rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        * rewrite Hacc Hwnil app_nil_r HD. reflexivity.
        * apply (prefix_snoc_lookup [] _ b); [apply prefix_nil |].
          by rewrite -Hpend.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * rewrite Forall_app. split; [exact Hcsb' |].
          by rewrite Forall_singleton.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + apply (cs_len_ok_blk so a b);
          [by rewrite HlenE | by rewrite HlenE | exact Hwnil | exact Hcsl].
      + apply (ps_len_ok_blk so a b);
          [by rewrite HlenE | by rewrite HlenE | by rewrite HlenE | exact Hpsl].
      + (* (A2) AT A BLOCK'S FIRST BYTE, paid by the writer's own [inp_lb]:
           the bound it writes against is a lower bound on the DELIVERED
           input and it is the WHOLE era's input, so the reader has taken
           every byte of the line this block answers. *)
        apply (dl_ok_out_full so (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]));
          [reflexivity | cbn [o_w]; discriminate | by rewrite HlenE |].
        pose proof (prefix_length _ _ HI0dl) as Hlp.
        rewrite !length_fmap in Hlp. rewrite HlenE. lia.
    - iLeft. rewrite Hcs0. iFrame "Ht Hilb Hcslb2 Hpslb".
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE (REVISION 7(d)).  The choice of
     continuation is the PROGRAM's knowledge -- sh knows whether it is about
     to echo the words it just read or report an exec failure -- and the
     observer can read it back off the wire because the four alternatives
     of a line settle every comparison the transcript takes part in
     ([EchoDisc.line_alts_of_prefix_bytes]).  So the writer supplies the
     alternative's INDEX beside its first byte, and the step files it: the
     claim's list grows from [q-1] to [q] at the input's [q]-th completed
     line, and every later byte of the block goes through [ecl_step_write]
     against the lower bound this returns.  The PROLOGUE (before any line)
     is not a choice and grows nothing -- which is why [I0 <> []] is a
     premise there. *)
  Lemma ecl_step_write_pro (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) :
    rest_of I0 = [] ->
    (I0 = [] \/ cs0 !!! (nlines I0 - 1)%nat = 3%nat) ->
    (nlines I0 <= length cs0)%nat ->
    pro_pin ps0 cs0 I0 ->
    ~ pro_done (pro_from (pro_idx cs0 (nlines I0)) ps0) ->
    P = length (proc_stream ps0 cs0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    ecl k ho CH ==∗
      ecl k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0)
         ∨ T).
  Proof.
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    pose proof (nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /ecl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so) "(#Hpin2 & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    pose proof Hcsb' as Hcsb.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
    { etrans; [exact HI0dl | exact (ecl_pure_dl_E k ho so CH Hall0)]. }
    (* ---- the writer's own list is bounded, and its round index is the
           claim's ---- *)
    assert (Hpsb0 : Forall (fun x => (x < length pro_alts)%nat) ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2. by apply Forall_app in Hpsb2 as [? _]. }
    assert (Hidxeq : pro_idx (o_cs so) (nlines I0) = pro_idx cs0 (nlines I0)).
    { symmetry. apply (pro_idx_ext cs0 (o_cs so) (nlines I0)); [| lia].
      intros j Hj. symmetry.
      apply (lookup_total_prefix cs0 (o_cs so) j Hcsp). lia. }
    rewrite -Hidxeq in Hnd.
    assert (HopenC : I0 = [] \/ o_cs so !!! (nlines I0 - 1)%nat = 3%nat).
    { destruct (decide (I0 = [])) as [Hz | Hne0]; [by left | right].
      pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
      destruct Hopen as [Hz | H3]; [by destruct (Hne0 Hz) |].
      rewrite (lookup_total_prefix cs0 (o_cs so) _ Hcsp); [exact H3 | lia]. }
    (* ---- what the stage owes below and at [I0], under the writer's
           bounds ---- *)
    assert (Hstream : proc_before ps0 cs0 I0
                      = proc_before (o_ps so) (o_cs so) I0).
    { apply (proc_before_cs_prefix ps0 (o_ps so) cs0 (o_cs so) I0
               Hpsp Hcsp Hpin0). lia. }
    assert (Hpend0 : pending_at ps0 cs0 I0 = pending_at ps0 (o_cs so) I0)
      by (apply (pending_at_cs_ext ps0 cs0 (o_cs so) I0 Hcsp Hdiv)).
    assert (Hpmono : pending_at ps0 (o_cs so) I0
                     `prefix_of` pending_at (o_ps so) (o_cs so) I0)
      by (by apply pending_at_ps_mono).
    assert (HPval : P = (length (proc_before ps0 cs0 I0)
                         + length (pending_at ps0 cs0 I0))%nat).
    { rewrite HPeq /proc_stream.
      by rewrite (length_app (proc_before ps0 cs0 I0)
                    (pending_at ps0 cs0 I0)). }
    rewrite /pcount in HP.
    (* ---- the era's input IS [I0]: a further echo would have folded this
           block into the stream, and the round it read would be SETTLED,
           which the writer's own [~ pro_done] refutes ---- *)
    assert (HlenE : (snd <$> o_E so) = I0).
    { destruct (decide ((snd <$> o_E so) = I0)) as [? | Hne]; [done | exfalso].
      assert (Hnei : I0 <> (snd <$> o_E so))
        by (intros Hq; apply Hne; symmetry; exact Hq).
      pose proof (proc_stream_before (o_ps so) (o_cs so) I0 (snd <$> o_E so)
                    HI0 Hnei) as Hpre.
      apply prefix_length in Hpre.
      rewrite /proc_stream length_app -Hstream in Hpre.
      pose proof (prefix_length _ _ Hpmono) as Hlp. rewrite -Hpend0 in Hlp.
      assert (Hpe : pending_at ps0 (o_cs so) I0
                    = pending_at (o_ps so) (o_cs so) I0).
      { apply prefix_length_eq; [exact Hpmono | rewrite -Hpend0; lia]. }
      pose proof (pending_at_round_det ps0 (o_ps so) (o_cs so) I0
                    Hr0 HopenC Hpe) as Hpro.
      assert (Hdone : pro_done (pro_from (pro_idx (o_cs so) (nlines I0))
                        (o_ps so))).
      { apply pro_from_done.
        apply (pro_pin_at (o_ps so) (o_cs so) (snd <$> o_E so) (nlines I0)
                 Hpin).
        exact (nstarted_strict I0 (snd <$> o_E so) HI0 Hnei). }
      apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (pro_idx (o_cs so) (nlines I0)) ps0)
                  (pro_from (pro_idx (o_cs so) (nlines I0)) (o_ps so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hpro; reflexivity)) as [Hd _].
      exact Hd. }
    (* ---- so the writer stands at the END of the block's OPEN prologue ---- *)
    assert (Hlenw : length (o_w so) = length (pending_at ps0 cs0 I0)).
    { rewrite HlenE -Hstream in HP. lia. }
    assert (Hweq : o_w so = pending_at ps0 (o_cs so) I0).
    { assert (Hw1 : o_w so `prefix_of` pending_at (o_ps so) (o_cs so) I0)
        by (rewrite -HlenE; exact Hwpre).
      assert (Hlen2 : length (o_w so) = length (pending_at ps0 (o_cs so) I0))
        by (rewrite -Hpend0; exact Hlenw).
      destruct (prefix_weak_total (o_w so) (pending_at ps0 (o_cs so) I0)
                  (pending_at (o_ps so) (o_cs so) I0) Hw1 Hpmono) as [Hq | Hq].
      - apply prefix_length_eq; [exact Hq | lia].
      - symmetry. apply prefix_length_eq; [exact Hq | lia]. }
    assert (Hopens : ps_opens so).
    { rewrite /ps_opens HlenE.
      destruct HopenC as [Hz | H3]; [by left | right; by split]. }
    (* ---- the CLAIM'S round is the writer's, still open, and its
           resolution is the writer's list ---- *)
    pose proof Hpsl as [HpsA HpsB].
    assert (Hproeq : pro_of (pro_from (pro_idx (o_cs so) (nlines I0)) ps0)
                     = pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                         (o_ps so))).
    { destruct (decide (pro_of (pro_from (pro_idx (o_cs so) (nlines I0)) ps0)
                        = pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                            (o_ps so)))) as [Heq | Hne]; [exact Heq | exfalso].
      pose proof (HpsB Hopens ps0 Hpsp) as Hlt.
      rewrite /ps_round HlenE in Hlt.
      pose proof (Hlt Hne) as Hlt2. rewrite Hweq in Hlt2. lia. }
    assert (Hndps : ~ pro_done (pro_from (pro_idx (o_cs so) (nlines I0))
                      (o_ps so))).
    { intros Hdone. apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (pro_idx (o_cs so) (nlines I0)) ps0)
                  (pro_from (pro_idx (o_cs so) (nlines I0)) (o_ps so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hproeq; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hround0 : (pro_idx (o_cs so) (nlines I0) <= pro_rounds ps0)%nat).
    { rewrite Hidxeq. by apply (pro_pin_round_le ps0 cs0 I0 Hr0 Hopen Hpin0). }
    assert (Hpseq : o_ps so = ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2.
      assert (Hzb : Forall (fun x => (x < length pro_alts)%nat) z)
        by (by apply Forall_app in Hpsb2 as [_ ?]).
      pose proof Hproeq as Hpe2. rewrite Hz in Hpe2.
      rewrite (pro_from_app_le _ ps0 z Hround0) in Hpe2.
      assert (Hzn : z = []).
      { apply (pro_of_open_app_inj _ z Hnd Hzb). by rewrite -Hpe2. }
      rewrite Hz Hzn. by rewrite app_nil_r. }
    assert (HRle : (pro_idx (o_cs so) (nlines I0)
                    <= pro_rounds (o_ps so))%nat)
      by (rewrite Hpseq; exact Hround0).
    (* ---- the byte the block owes at the writer's position ---- *)
    assert (Hshape2 : pending_at (o_ps so ++ [a]) (o_cs so) I0
                      = (if decide (I0 = []) then [] else alt_panic)
                        ++ pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                             (o_ps so ++ [a])))
      by (apply pending_at_round_pre; [exact Hr0 | exact HopenC]).
    assert (Hshape : pending_at (o_ps so) (o_cs so) I0
                     = (if decide (I0 = []) then [] else alt_panic)
                       ++ pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                            (o_ps so)))
      by (apply pending_at_round_pre; [exact Hr0 | exact HopenC]).
    assert (Hpendb : pending_at (o_ps so ++ [a]) (o_cs so) I0
                       !! length (o_w so) = Some b).
    { pose proof (pro_of_snoc_head
                    (pro_from (pro_idx (o_cs so) (nlines I0)) (o_ps so)) a b
                    Hndps Hhead) as Hph.
      assert (Hpre3' :
        ((if decide (I0 = []) then [] else alt_panic)
         ++ (pro_of (pro_from (pro_idx (o_cs so) (nlines I0)) (o_ps so))
             ++ [b]))
        `prefix_of` pending_at (o_ps so ++ [a]) (o_cs so) I0).
      { rewrite Hshape2 (pro_from_snoc_le _ (o_ps so) a HRle).
        by apply prefix_app. }
      assert (Hwl : length (o_w so)
                    = (length (if decide (I0 = []) then [] else alt_panic)
                       + length (pro_of (pro_from (pro_idx (o_cs so)
                           (nlines I0)) (o_ps so))))%nat).
      { rewrite Hweq -Hpseq Hshape.
        by rewrite (length_app
                      (if decide (I0 = []) then [] else alt_panic)
                      (pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                         (o_ps so)))). }
      rewrite Hwl. eapply prefix_lookup_Some; [| exact Hpre3'].
      rewrite (lookup_app_shift
                 (if decide (I0 = []) then [] else alt_panic)).
      replace (length (pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                 (o_ps so))))
        with (length (pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                 (o_ps so))) + 0)%nat by lia.
      by rewrite (lookup_app_shift
                    (pro_of (pro_from (pro_idx (o_cs so) (nlines I0))
                       (o_ps so)))). }
    assert (Hcase : o_w so <> []
                    \/ rest_of (snd <$> o_E so) <> []
                    \/ (snd <$> o_E so) = []).
    { destruct (decide (I0 = [])) as [Hz | Hnz].
      { right; right. by rewrite HlenE. }
      left. rewrite Hweq -Hpseq.
      exact (pending_at_nonnil (o_ps so) (o_cs so) I0 Hcsb Hnz Hr0). }
    (* ---- the transcript and the cursor do not read the new entry ---- *)
    assert (HD : D (o_ps so ++ [a]) (o_cs so) (o_E so)
                 = D (o_ps so) (o_cs so) (o_E so)).
    { symmetry. apply (D_ps_ext (o_ps so) (o_ps so ++ [a]) (o_cs so) (o_E so));
        [by eexists | exact Hpin]. }
    assert (Hpceq : pcount (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])
                    = pcount (o_ps so ++ [a]) (o_cs so) (o_E so)
                        (o_w so ++ [b])).
    { apply (pcount_cs_prefix (o_ps so) (o_ps so ++ [a]) (o_cs so) (o_cs so)
               (o_E so) (o_w so ++ [b]));
        [by eexists | reflexivity | exact Hpin |].
      pose proof (prefix_length _ _ Hcsp) as Hle2.
      rewrite HlenE Hrl0. lia. }
    assert (Hpc2 : pcount (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so ++ [b])
                   = S P).
    { rewrite -Hpceq /pcount (length_app (o_w so) [b]). cbn [length]. lia. }
    iMod (turn_update v P (pcount (o_ps so) (o_cs so) (o_E so) (o_w so)) (S P)
            ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (o_ps so) a with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /ecl. iRight.
      iExists v, (MkO (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so ++ [b])).
      cbn [o_ps o_cs o_E o_w]. rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (ecl_pure_out k ho so
               (MkO (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so ++ [b]))
               CH b);
        [cbn [o_cs]; lia | reflexivity | | | | | exact Hall0].
      + rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        * rewrite Hacc HD. by rewrite app_assoc.
        * apply prefix_snoc_lookup.
          { etrans; [exact Hwpre |]. rewrite /pending.
            by apply pending_at_ps_mono; eexists. }
          { rewrite /pending HlenE. exact Hpendb. }
        * exact Hidx.
        * exact Hbyte.
        * rewrite Forall_app.
          split; [exact Hpsb | by rewrite Forall_singleton].
        * apply (pro_pin_mono (o_ps so) (o_ps so ++ [a]));
            [by eexists | exact Hpin].
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + apply (cs_len_ok_write
                 (MkO (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so)) b);
          [exact Hcsl | exact Hcase].
      + apply (ps_len_ok_pro so a b);
          [ rewrite /ps_round HlenE; exact HRle
          | rewrite /ps_round HlenE; exact Hndps
          | rewrite /pending HlenE Hweq; by rewrite -Hpseq
          | exact (conj HpsA HpsB) ].
      + (* (A2): the writer is now inside the block's prologue round *)
        apply (dl_ok_out so (MkO (o_ps so ++ [a]) (o_cs so) (o_E so)
                               (o_w so ++ [b])));
          [reflexivity | cbn [o_w] | exact Hcase | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. rewrite -Hpseq. iFrame "Ht Hpslb2 Hcslb Hilb".
  Qed.

  Lemma ein_read_pure (k : nat) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (cs0 : list nat) :
    read_ok pops dl ws -> ein_pure k pops dl cs0 ->
    (dl ++ ws) `prefix_of` echoed pops
    /\ ein_pure k pops (dl ++ ws) cs0
    /\ (nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat.
  Proof using .
    intros Hread (Hlog & Hdisc & Hstamp & Hdlp & Hidx & Hbyte & Hbnd & Hall).
    assert (Hnoer : forall e, e ∈ pops -> cons_erase (le_byte e) = false).
    { intros e He. eapply disc_seg_no_erase; [by apply Hdisc |].
      apply open_seg_ends_in. by apply (proj1 (proj1 Hlog e He)). }
    assert (Hpref : (dl ++ ws) `prefix_of` echoed pops)
      by (eapply read_window_prefix;
          [exact Hlog | exact Hread | exact Hnoer | exact Hdlp]).
    split; [exact Hpref |]. split.
    - rewrite /ein_pure. split_and!;
        [exact Hlog | exact Hdisc | exact Hstamp | exact Hpref | exact Hidx
         | exact Hbyte | exact Hbnd | exact Hall].
    - etrans; [| exact Hbnd]. apply nlines_prefix, epu_fmap_prefix, Hpref.
  Qed.

  (* ---- THE READ, ON THE MERGED CLAIM.  This step used to have TWO
     identical branches, one per arm of [ein], differing only in which
     counter share they put back; here there is one.  The pure work is
     unchanged -- [ein_read_pure] turns [ConsLog.read_ok] into the
     delivered-prefix fact the claim needs -- and it is exactly the premise
     [ecl_pure_read] takes.

     WHAT THE READER GETS BACK, BESIDE THE WINDOW: the ERA'S INPUT AT THE
     WINDOW'S FAR END, [snd <$> (dl ++ ws)], as a persistent lower bound and
     as a PURE [disc_input].  That is what SH-LINE reads the line off now:
     with one fixed line the reader named a POSITION in it
     ([echo_line !!! (n mod 17)]) and there is no such position any more;
     what is left is that the bytes it has been handed PARSE, so its own
     newline completes an admissible line
     ([EchoDisc.disc_input_snoc_nl]/[disc_input_last_ws]). ---- *)
  Lemma ecl_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    era_pin k v -∗ dl_cnt v (1/2) n -∗ ecl k ho CH ==∗
      ecl k ho (ConsLog.cons_step CH (ConsLog.EvRead ws))
      ∗ ((T ∗ dl_cnt v (1/2) n)
         ∨ dl_cnt v (1/2) (n + length ws)%nat
           ∗ ⌜length (LogEntryDefs.ch_dl CH) = n⌝
           ∗ ⌜(LogEntryDefs.ch_dl CH ++ ws)
              `prefix_of` echoed (LogEntryDefs.ch_log CH)⌝
           ∗ ⌜E_index (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ ⌜E_disc (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ inp_lb v (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
           ∗ ⌜disc_input (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ cs0 ps0 : list nat,
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ ⌜(nlines (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                      <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (proc_before ps0 cs0
                                 (snd <$> (LogEntryDefs.ch_dl CH ++ ws))))
                  ∗ ⌜rd_stage ps0 cs0
                       (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝)).
  Proof using Persistent0.
    intros Hread. iIntros "#Hpinr Hdlr Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /ecl; by iLeft |]. iLeft. by iFrame "Hdlr". }
    iDestruct "Hp" as (v2 so) "(#Hpin & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (era_pin_agree with "Hpin Hpinr") as %->.
    iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hin as Hin2.
    destruct Hin2 as (_ & _ & _ & _ & Hidx & Hbyte & _ & _).
    destruct (ein_read_pure k (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH)
                ws (o_cs so) Hread Hin) as (Hpref & Hp' & Hbnd').
    (* the window's far end is inside the era's INPUT, which is what makes
       every bound below nameable *)
    assert (HEpre : (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                    `prefix_of` (snd <$> o_E so)).
    { rewrite (ecl_pure_E k ho so CH Hall0) /ch_E.
      etrans; [exact (epu_fmap_prefix snd _ _ Hpref) |].
      rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log CH))).
      apply epu_fmap_prefix. by apply prefix_app_r. }
    assert (Hdi : disc_input (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    { apply (disc_input_prefix _ (snd <$> o_E so) HEpre).
      by destruct Hpure as (_ & _ & _ & Hd & _). }
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (turn_lb_get with "Hta") as "#Htlb".
    iMod (dl_cnt_update v (length (LogEntryDefs.ch_dl CH)) n (n + length ws)%nat
            with "Hdl Hdlr") as "[Hdl Hdlr]".
    (* (A3) THE DELIVERED LIST GROWS, and the bound minted from it is what
       the reader hands on to a writer.  This is the ONLY step that moves
       it. *)
    iMod (dl_list_auth_grow v (LogEntryDefs.ch_dl CH) ws with "Hdll")
      as "[Hdll #Hdllb]".
    iModIntro. iSplitL "Hta Hcs Hps HE Hdl Hdll".
    { rewrite /ecl. iRight. iExists v, so.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite length_app Hdleq. iFrame "Hpin Hta Hcs Hps HE Hdl Hdll".
      iPureIntro. exact (ecl_pure_read k ho so CH ws Hpref Hall0). }
    iRight. iFrame "Hdlr".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR.
    { iApply (inp_lb_of_dl_lb v (LogEntryDefs.ch_dl CH ++ ws) _
                (reflexivity _)). iExact "Hdllb". }
    iSplitR; [by iPureIntro |].
    iRight. iExists (o_cs so), (o_ps so). iFrame "Hcslb Hpslb".
    iSplitR; [by iPureIntro |].
    iSplitR.
    { iApply (turn_lb_weaken with "Htlb"). rewrite /pcount.
      etrans; [apply prefix_length, proc_before_prefix; exact HEpre | lia]. }
    iPureIntro.
    exact (rd_stage_le _ _ _ _ HEpre (ecl_pure_rd_stage k ho so CH Hall0)).
  Qed.

  (* THE PER-BYTE FORM sh's [gets] reads: one byte at a time, placed by the
     reader's own delivered count.  [read_ret]'s [⌜length dl = n⌝] is what
     makes [n] usable here at all -- the link hides the invariant's [dl].
     It says WHERE in the era's input the byte sits and no longer WHICH byte
     it is: the value is the reader's own business, and what makes the line
     admissible is [read_ret]'s [disc_input]. *)
  Lemma ein_read_byte (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (n : nat) (x : list mobs * bv 8) :
    (dl ++ ws) `prefix_of` echoed pops ->
    length dl = n ->
    ws !! 0%nat = Some x ->
    x.2 = (snd <$> (dl ++ ws)) !!! n.
  Proof using .
    intros Hp Hdl Hx.
    assert (Hlk : (dl ++ ws) !! n = Some x).
    { rewrite lookup_app_r; [| lia]. rewrite Hdl Nat.sub_diag. exact Hx. }
    rewrite list_lookup_total_alt list_lookup_fmap Hlk. reflexivity.
  Qed.

  (* (L) THE DRAIN ([App.Htx]).  The claim's own same-cycle facts are at its
     WITNESS [ho]; [App.Htx] supplies [ho `prefix_of` h] and the era stamp at
     [h], the claim carries the stamp at [ho], and
     [EchoOutPure.open_seg_prefix_boots] puts the two segments in one cycle.
     [EchoOutPure.good_out_of_stage] then turns the stage into [good_out]. *)
  (* ---- THE DRAIN, ON THE MERGED CLAIM.  [App.Htx] reads the trace
     property off the claim at the end of the run.  Today it needs a second
     witness because the output and input claims carry their own; here there
     is one claim and one witness, and the proof is the output side's
     verbatim -- the input-side clauses play no part in [good_out]. ---- *)
  (* WHAT THE CLAIM SAYS ABOUT AN OPEN ARM, read back out.  A byte link
     fires at a history the application did not see opened, so the ledger's
     own three facts about the arm -- its discipline, its era and the tie to
     the claim's witness -- have to come from the claim itself. *)
  Lemma ecl_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    ecl k ho CH -∗
      ecl k ho CH ∗ (T ∨ ⌜ch_arm_era k ho CH⌝).
  Proof using Persistent0.
    rewrite /ecl. iIntros "[#HT | Hp]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct "Hp" as (v so) "(#Hpin & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iSplitL.
    - iRight. iExists v, so. iFrame "Hpin Hta Hcs Hps HE Hdl Hdll". by iPureIntro.
    - iRight. iPureIntro. exact (ecl_pure_arm k ho so CH Hall).
  Qed.

  (* ==================================================================== *)
  (*  THE BYTE STEP, OFF WHAT THE LINK ACTUALLY HANDS OVER.                *)
  (*                                                                      *)
  (*  This is where the merge pays.  Today's echo link needs seven facts   *)
  (*  from its caller, because the byte and the entry move two resources   *)
  (*  at two witnesses and nothing inside either says which input is being *)
  (*  answered.  Here the arm IS the history's own field: the event's      *)
  (*  premise names it, [ConsLog.arm_ok] carries its order and wire facts, *)
  (*  and [ch_arm_era] carries the ledger's.  So the link takes NOTHING.   *)
  (* ==================================================================== *)
  Lemma ecl_step_byte (k : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    ecl k ho CH ==∗ ecl k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using Persistent0.
    intros Hok Hev. iIntros "Hcl".
    iDestruct (ecl_arm with "Hcl") as "[Hcl [#HT | %Hera]]".
    { iModIntro. rewrite /ecl. by iLeft. }
    pose proof Hev as Hev0.
    destruct Hev0 as (a & Ha & Hlk). destruct a as [[[ha ca] csa] ja].
    cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Hlk.
    rewrite /ch_arm_era Ha in Hera.
    destruct Hera as (Hdseg & Hbts & Hdisc & Hsh & Hw & Hcsa0 & HK1).
    subst ha.
    destruct Hok as [_ Harm]. rewrite Ha in Harm.
    cbn [from_option LogEntryDefs.ca_hist LogEntryDefs.ca_byte
         LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Harm.
    destruct Harm as (Hends & Hecho & _ & Hord & Hwire).
    (* UNDER THE DISCIPLINE THE ARM ECHOES EXACTLY ONE BYTE: the erase
       disjunct is guarded by [cons_erase], which a disciplined segment
       refutes, and the empty one has no byte at any index. *)
    assert (Hshape : csa = [echo_of ca] /\ ja = 0%nat /\ b = echo_of ca).
    { destruct Hecho as [Hnil | [Hech | [Herase _]]].
      - exfalso. rewrite Hnil in Hlk. by rewrite lookup_nil in Hlk.
      - rewrite Hech in Hlk.
        destruct ja as [| j']; cbn in Hlk; [| by rewrite lookup_nil in Hlk].
        injection Hlk as <-. by split_and!.
      - exfalso.
        pose proof (disc_seg_no_erase (open_seg ho) ca Hdseg
                      (open_seg_ends_in ho ca Hends)) as Hno.
        rewrite Hno in Herase. discriminate. }
    destruct Hshape as (Hcsa & Hja & Hb).
    subst b. rewrite Hcsa Hja in Ha.
    (* (K1) + (A1) at this arm, recorded at the open and read back here:
       the log is complete below the input being echoed. *)
    iApply (ecl_step_echo k ho ca ho CH Hdisc Hsh Hbts Hends Hwire Hord HK1 Ha
              with "Hcl").
  Qed.

  Lemma ecl_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    ecl k ho CH -∗ ecl k ho CH ∗ (T ∨ ⌜good_out seg⌝).
  Proof using Persistent0.
    intros Hsh Hk Hpre Hins Hwire. subst k. rewrite /ecl.
    iIntros "Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    - iSplitR; [iLeft; iExact "HT" | iLeft; iExact "HT"].
    - iDestruct "Hp" as (v so) "(#Hpin & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
      pose proof Hall as Hall2.
      destruct Hall2 as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie & Hdlok).
      destruct Hpure as (Hacc & Hwp & Hidx & Hbyte & Hpsb & Hpin & Hcs' & Hdsc
                         & Hpre1 & Hpre2 & Hpre3).
      iSplitL "Hta Hcs Hps HE Hdl Hdll".
      { iRight. iExists v, so. iFrame "Hpin Hta Hcs Hps HE Hdl Hdll". by iPureIntro. }
      iRight. iPureIntro.
      (* THE ERA'S INPUT IS A PREFIX OF THE SEGMENT'S, which is what
         [good_out_of_stage] reads the transcript against now -- a count of
         echoes says nothing once the lines differ in length. *)
      assert (Hbytes : (snd <$> o_E so) `prefix_of` ins seg).
      { destruct Hpre3 as [HEnil | Hbo].
        - rewrite HEnil fmap_nil. apply prefix_nil.
        - assert (Hpl : forall j x, o_E so !! j = Some x ->
                          x.1 `prefix_of` open_seg ho)
            by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx)).
          rewrite (E_bytes_of_hist (o_E so) (open_seg ho) Hidx Hpl Hpre2).
          etrans; [apply prefix_take |].
          rewrite Hins. apply ins_prefix_of, open_seg_prefix_boots;
            [exact Hpre | by rewrite Hbo | exact Hsh]. }
      apply (good_out_of_stage (o_ps so) (o_cs so) (o_E so) (o_w so) seg
               Hpsb Hcs' Hbyte Hpin Hwp).
      + rewrite -Hacc. exact Hwire.
      + exact Hbytes.
  Qed.


  (* ==================================================================== *)
  (*  7.  THE LINKS: the claims wrapped onto the kernel's own console      *)
  (*      contracts                                                       *)
  (*                                                                      *)
  (*  A link runs at [⊤ ∖ ↑uartN Uart0] -- the store's device node opens   *)
  (*  the port invariant and the ghost step runs inside it.  IT OPENS      *)
  (*  NOTHING ELSE: every authority the era has is in the claim the link   *)
  (*  is handed, so no link reaches the application's ledger and           *)
  (*  [App.Happ_echo] stays a CLOSED entailment.                           *)
  (* ==================================================================== *)
  Section echo_links.
    Context `{HRg : !riscvGS Σ}.

    (* the record equations, as section parameters: [App.Happ_echo] and
       [App.Hinit_boot] hand them over at the [boot_fixedGS] literal.  ONE
       claim equation since the redesign, where there were four. *)
    Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ecl).
    Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = etag).

    Lemma chist_at0 (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
      chist_at Uart0 kk hh HH = ecl kk hh HH.
    Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

    (* ---- the taint route: once the era is off the discipline every link
            of every run is free ---- *)
    Lemma cons_link_of_taint (k : nat) (ev : ConsLog.cons_ev) (Φ : iProp Σ) :
      T -∗ Φ -∗ cons_link Uart0 k ev Φ.
    Proof using Hcons Persistent0.
      iIntros "#HT HΦ" (o H) "#Hlb Hres _ _".
      iModIntro. iExists o.
      iSplitR; [iExact "Hlb" |].
      iSplitR "HΦ"; [| iExact "HΦ"].
      rewrite !chist_at0 /ecl. by iLeft.
    Qed.

    (* (W) THE WRITE LINK, INSIDE A BLOCK.  What IO-LEAF spends per byte: the
       era's pin, its cursor and the three persistent bounds -- the two
       choice lists and the era's INPUT [I0], which is what a program can
       name now that no stage index is meaningful -- plus the Coq-level fact
       that the byte is the [P]-th of the era's process stream through
       [I0].  What it gets back in [Φ] is the cursor advanced and the same
       three bounds -- or the taint, if the claim was already off the
       discipline when the byte went out.

       INIT'S FIRST BANNER BYTE IS THIS LINK at [P = 0], [I0 = []],
       [cs0 = []]: [app_turn] ([eturn]) is exactly its argument list.

       THE WITNESS IS NOT MOVED: a process byte answers no input, so the
       claim stays at the history it was read at. *)
    Lemma echo_write_link (k : nat) (v : era_pins) (P : nat) (b : bv 8)
        (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
      (nlines I0 <= length cs0)%nat ->
      pro_pin ps0 cs0 I0 ->
      proc_stream ps0 cs0 I0 !! P = Some b ->
      era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
      (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T) -∗ Φ) -∗
      out_link Uart0 k b Φ.
    Proof using Hcons Persistent0.
      intros Hn Hpin0 Hb.
      iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
      rewrite !chist_at0.
      iMod (ecl_step_write k v P b ps0 cs0 I0 (default [] o) H
              Hn Hpin0 Hb with "Hpin Ht Hpslb Hcslb Hilb Hres")
        as "(Hres & Hret)".
      iModIntro. iExists o. rewrite chist_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
    Qed.

    (* (W'') THE TAINT ROUTE.  Once the era is off the discipline every
       claim is free, so a link costs nothing: the program tower spends
       this when an earlier link of the same string handed back the taint
       instead of the cursor. *)
    Lemma echo_write_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
      T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ.
    Proof using Hcons Persistent0.
      iIntros "#HT HΦ" (o H) "#Hlb Hres".
      iModIntro. iExists o.
      iSplitR; [iExact "Hlb" |].
      iSplitR "HΦ"; [| by iApply "HΦ"].
      rewrite !chist_at0 /ecl. by iLeft.
    Qed.

    (* (W') THE WRITE LINK AT A BLOCK'S FIRST BYTE.  The alternative's INDEX
       is the program's own knowledge and the step files it, so the bound
       that comes back has grown by one.  The alternatives are the LAST
       LINE's ([EchoDisc.line_alts_of] at [last_ws I0]) -- which is where
       "whatever you type is echoed back" enters the link layer. *)
    Lemma echo_write_link_blk (k : nat) (v : era_pins) (P a : nat)
        (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
      I0 <> [] ->
      rest_of I0 = [] ->
      (nlines I0 <= S (length cs0))%nat ->
      pro_pin ps0 cs0 I0 ->
      P = length (proc_before ps0 cs0 I0) ->
      (a < 4)%nat ->
      line_alts_of (last_ws I0) !!! a !! 0%nat = Some b ->
      era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
      (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0)
        ∨ T) -∗ Φ) -∗
      out_link Uart0 k b Φ.
    Proof using Hcons Persistent0.
      intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hhead.
      iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
      rewrite !chist_at0.
      iMod (ecl_step_write_blk k v P a b ps0 cs0 I0 (default [] o) H
              Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite chist_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
    Qed.

    (* (W-pro) THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE.  Init's
       own knowledge of which of the four alternatives it is taking, filed
       into the claim; the bound that comes back has the entry in it, and
       the rest of the alternative goes out through [echo_write_link]
       against that bound.  At [I0 = []], [cs0 = []] this is exactly the
       era's FIRST choice, at [P = length (pro_of ps0)]. *)
    Lemma echo_write_link_pro (k : nat) (v : era_pins) (P a : nat)
        (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
      rest_of I0 = [] ->
      (I0 = [] \/ cs0 !!! (nlines I0 - 1)%nat = 3%nat) ->
      (nlines I0 <= length cs0)%nat ->
      pro_pin ps0 cs0 I0 ->
      ~ pro_done (pro_from (pro_idx cs0 (nlines I0)) ps0) ->
      P = length (proc_stream ps0 cs0 I0) ->
      (a < length pro_alts)%nat ->
      pro_alts !!! a !! 0%nat = Some b ->
      era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
      (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0)
        ∨ T) -∗ Φ) -∗
      out_link Uart0 k b Φ.
    Proof using Hcons Persistent0.
      intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
      iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
      rewrite !chist_at0.
      iMod (ecl_step_write_pro k v P a b ps0 cs0 I0 (default [] o) H
              Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite chist_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
    Qed.

    (* (R) THE READ LINK.  [ws] is the window the read CONSUMED and
       [ConsLog.read_ok] is the kernel's whole pure account of it -- which
       IS the [EvRead] event's own premise, so the reader hands over
       nothing the link did not already carry.  Beside the window it exports
       THE ERA'S INPUT AT THE WINDOW'S FAR END and its DISCIPLINE, which is
       what a reader spends where it used to read a position of the one
       fixed line. *)
    Definition read_ret (k : nat) (v : era_pins) (n : nat)
        (ws : list (list mobs * bv 8)) : iProp Σ :=
      ((T ∗ dl_cnt v (1/2) n)
       ∨ dl_cnt v (1/2) (n + length ws)%nat
         ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
             ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
             ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
             ∗ ⌜E_index (seg_of (echoed pops))⌝
             ∗ ⌜E_disc (seg_of (echoed pops))⌝
             ∗ inp_lb v (snd <$> (dl ++ ws))
             ∗ ⌜disc_input (snd <$> (dl ++ ws))⌝
             ∗ (⌜ws = []⌝
                ∨ ∃ cs0 ps0 : list nat,
                    cs_lb v cs0 ∗ ps_lb v ps0
                    ∗ ⌜(nlines (snd <$> (dl ++ ws))
                        <= S (length cs0))%nat⌝
                    ∗ turn_lb v (length (proc_before ps0 cs0
                                   (snd <$> (dl ++ ws))))
                    ∗ ⌜rd_stage ps0 cs0 (snd <$> (dl ++ ws))⌝))%I.

    Lemma echo_read_link (k : nat) (v : era_pins) (n : nat)
        (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
      era_pin k v -∗ dl_cnt v (1/2) n -∗ (read_ret k v n ws -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
    Proof using Hcons Persistent0.
      iIntros "#Hpin Hdlr HΦ" (o H) "#Hlb Hres _ %Hread".
      rewrite !chist_at0.
      iMod (ecl_step_read k v n (default [] o) H ws Hread
              with "Hpin Hdlr Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite chist_at0. iFrame "Hlb Hres".
      iApply "HΦ". rewrite /read_ret.
      iDestruct "Hret" as "[Ht | (Hdlr & %Hdl & %Hpref & %Hidx & %Hbyte
                                 & Hilb & %Hdi & Hrest)]"; [by iLeft |].
      iRight. iFrame "Hdlr".
      iExists (LogEntryDefs.ch_log H), (LogEntryDefs.ch_dl H).
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitL "Hilb"; [iExact "Hilb" |].
      iSplitR; [by iPureIntro |]. iExact "Hrest".
    Qed.

    (* ================================================================== *)
    (*  THE ECHO SHIFT ITSELF -- [App.Happ_echo], a CLOSED entailment.     *)
    (*                                                                    *)
    (*  THE TOTALITY TABLE IS GONE.  Under the split run it was the whole  *)
    (*  proof: the taint arms, the window arm's five quarters, the settled *)
    (*  arm's tie at the echo and its refutation at the append, and a DROP *)
    (*  arm at every early stop.  With one claim over one console history  *)
    (*  each of those is a step of the claim itself, discharged where the  *)
    (*  history moves -- so what is left here is the ARM'S OPEN and a      *)
    (*  run whose every link takes nothing.                                *)
    (* ================================================================== *)

    (* THE CLOSE: the entry is filed at exactly what went out, and the step
       is an ENTAILMENT -- no ghost of the era's moves ([ecl_close]). *)
    Lemma echo_close_link (k : nat) (Φ : iProp Σ) :
      Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
    Proof using Hcons.
      iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
      rewrite chist_at0.
      iDestruct (ecl_close k (default [] o) H Hok Hev with "Hres") as "Hres".
      iModIntro. iExists o. rewrite chist_at0. by iFrame "Hlb Hres HΦ".
    Qed.

    (* ...AND THE BYTE, which takes NOTHING: the arm is the history's own
       field, and everything the step needs is inside the claim and the
       event's premises ([ecl_step_byte]). *)
    Lemma echo_byte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
      Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
    Proof using Hcons Persistent0.
      iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
      rewrite chist_at0.
      iMod (ecl_step_byte k (default [] o) H b Hok Hev with "Hres") as "Hres".
      iModIntro. iExists o. rewrite chist_at0. by iFrame "Hlb Hres HΦ".
    Qed.

    (* ...so the WHOLE RUN is free, at every length and at either exit.
       This one lemma is the old file's four taint routes, two append arms
       and echo link together. *)
    Lemma echo_cons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
      Φ -∗ cons_run k cs Φ.
    Proof using Hcons Persistent0.
      iIntros "HΦ". iInduction cs as [| b cs] "IH" forall (Φ);
        cbn [cons_run].
      - by iApply echo_close_link.
      - iSplit.
        + by iApply echo_close_link.
        + iApply echo_byte_link. by iApply "IH".
    Qed.

    (* [App.Happ_echo]. *)
    Lemma echo_happ_echo :
      ⊢ ∀ (GEN : GenId) (XI : CurCtx),
          @SpecConsoleintr.cons_echo_shift Σ HRg GEN XI.
    Proof using Hcons Htag Persistent0.
      iIntros (GEN XI).
      rewrite /SpecConsoleintr.cons_echo_shift Htag.
      iIntros "!>" (h c cs Φ) "%Hends %Hk %Hcs #Htg #Hlbh HΦ".
      iDestruct "Htg" as "[%Hsh [%Hdisc | #HT]]"; last first.
      { (* THE TAINT ROUTE, at the open; every link of the run is free
           anyway *)
        iApply (cons_link_of_taint with "HT [HΦ]").
        by iApply echo_cons_run. }
      (* THE ARM OPENS.  The claim's witness moves to the byte's own
         history here, which is what lets every byte of the arm keep it --
         and the kernel's account of the event ([cons_link] hands over both
         [cons_hist_ok] and [cons_ev_ok]) is what refutes the drop arm. *)
      iIntros (o H) "#Hlb Hres %Hok %Hev".
      rewrite chist_at0.
      iDestruct (ecl_open (S gen_id) (default [] o) H h c cs Hok Hev
                   (disc_seg_open_seg h Hsh Hdisc) Hk Hdisc Hsh
                   with "Hres") as "Hres".
      iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
      rewrite chist_at0. iFrame "Hlbh Hres".
      by iApply echo_cons_run.
    Qed.

  End echo_links.

End echo_out.
