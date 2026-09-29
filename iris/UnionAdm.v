(* ===================================================================== *)
(*  UnionAdm.v -- WHAT A BOOT MAY SEE AFTER A SYNC: the line list, the    *)
(*  sync records and the admissible sets [uadm] (lane SY3-M; design:      *)
(*  claude-notes/design/sync.md sections 4-5).  PURE.                     *)
(*                                                                        *)
(*  THE LINE LIST ([ulines_of h]) is every complete line of every cycle,  *)
(*  in order, as the union parses it ([uline_of_u]) -- a [sync] line is   *)
(*  an entry like a redirect line.  The ledger's rx wand appends          *)
(*  [uline_of_u b] when the newline completing the body [b] arrives; the *)
(*  redirect lines the ledger keeps today are this list's projection      *)
(*  ([omap echof_ws], [ulines_of_echof]).  A line's POSITION in the list *)
(*  is its global round index: the round's index in its cycle plus the    *)
(*  number of lines of the earlier cycles.                                *)
(*                                                                        *)
(*  A SYNC RECORD [(p, S)] names what a completed sync fixed: [S] the     *)
(*  files at the sync (the running state, which the sync made durable),   *)
(*  [p] the position of the first line typed after the sync line (the    *)
(*  sync line's own position plus one).  The record [srec0 = (0, ∅)] is   *)
(*  "no sync yet": the mkfs image has no user file, and every line comes  *)
(*  after it.                                                             *)
(*                                                                        *)
(*  [uadm ls (p, S) s] -- the design's [Adm(ls, k)] at the k-th record -- *)
(*  says each file of [s] is either as it was at the sync (absent there,  *)
(*  absent here) or a chunk subset of a redirect line at its name typed   *)
(*  at a position >= [p].  At [srec0] it is the landed [fadm_boot] of the *)
(*  redirect lines ([uadm_srec0]).  It is a product over names, so it     *)
(*  forgets which files moved together -- an over-approximation, never a  *)
(*  hole.                                                                 *)
(*                                                                        *)
(*  THE STATE AT THE SYNC IS NOT A FUNCTION OF THE LINES.  After [echo a  *)
(*  > f; echo b > f; sync] the file is [b]'s run if the second redirect  *)
(*  ran, and [a]'s if its open failed -- which only the console shows.   *)
(*  So a record is read off the cycle's RESOLUTION ([usync_last]: the     *)
(*  last round of line [sync] resolved to /sync's run whose whole block   *)
(*  is on the wire -- the pad of an in-flight round never counts), and    *)
(*  the per-cycle claim [lm_good_sync] is [lm_good_out] with the record   *)
(*  its own resolution computes.  On the machine the record is minted by  *)
(*  the sync itself (it knows the running state), and the counter of      *)
(*  design section 4 numbers the records: the k-th fire's record is      *)
(*  [srec_le]-above the (k-1)-th, and [uadm_shrink] is what turns the    *)
(*  durable copy's record into the ledger's.                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import PipesLedPure.
Require Import PipesDisc.
Require Import FileState.
Require Import FileDisc.
Require Import UnionDisc.
Require Import UnionDiscDec.
From stdpp Require Import list.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

Local Notation U := ulmG.
Local Notation UB := (ulm_byte_laws adm_u_g adm_s_on).
Local Notation UK := ulmG_hooks.

(* ===================================================================== *)
(*  1.  THE LINE LIST                                                     *)
(* ===================================================================== *)

(* the complete lines of one input, as the union parses them *)
Definition ulines_in (I : list (bv 8)) : list uline := uline_of_u <$> bodies_of I.

Definition ulines_cyc (seg : list mobs) : list uline := ulines_in (ins seg).

(* every complete line of the whole history, cycle by cycle *)
Definition ulines_of (h : list mobs) : list uline := concat (ulines_cyc <$> cycles_of h).

(* ...and of the cycles STRICTLY BEFORE cycle [k] *)
Definition ulines_before (h : list mobs) (k : nat) : list uline :=
  concat (ulines_cyc <$> take k (cycles_of h)).

Lemma ulines_in_length I : length (ulines_in I) = nlines I.
Proof using. by rewrite /ulines_in length_fmap. Qed.

Lemma ulines_before_all h : ulines_before h (length (cycles_of h)) = ulines_of h.
Proof using. by rewrite /ulines_before take_ge. Qed.

Lemma ulines_in_app I k : ulines_in I `prefix_of` ulines_in (I ++ k).
Proof using.
  destruct (bodies_of_app I k) as [z Hz].
  rewrite /ulines_in Hz fmap_app. by eexists.
Qed.

Lemma ulines_cyc_app seg k : ulines_cyc seg `prefix_of` ulines_cyc (seg ++ k).
Proof using. rewrite /ulines_cyc ins_app. apply ulines_in_app. Qed.

Lemma ulines_of_snoc h e : ulines_of h `prefix_of` ulines_of (h ++ [e]).
Proof using.
  rewrite /ulines_of /cycles_of cycles_rev_app /=.
  destruct e as [i b | i b | |]; cbn [cyc_step].
  - destruct (cycles_rev h) as [| c cs].
    + rewrite /=. apply prefix_nil.
    + cbn [rev]. rewrite !fmap_app !concat_app /=.
      rewrite !app_nil_r. apply prefix_app, ulines_cyc_app.
  - destruct (cycles_rev h) as [| c cs].
    + rewrite /=. apply prefix_nil.
    + cbn [rev]. rewrite !fmap_app !concat_app /=.
      rewrite !app_nil_r. apply prefix_app, ulines_cyc_app.
  - cbn [rev]. rewrite fmap_app concat_app.
    apply prefix_app_r. reflexivity.
  - reflexivity.
Qed.

Lemma ulines_of_prefix h' h : h' `prefix_of` h -> ulines_of h' `prefix_of` ulines_of h.
Proof using.
  intros [k ->]. induction k as [| e k IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH | apply ulines_of_snoc].
Qed.

(* an event that completes no line leaves the list ([echof_lines_of_io]'s
   twin): console output, and the power steps *)
Lemma ulines_of_io (h : list mobs) (e : mobs) :
  trace_shape h true -> is_io e = true -> ins [e] = [] ->
  ulines_of (h ++ [e]) = ulines_of h.
Proof using.
  intros Hsh Hio Hin.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  rewrite /ulines_of H1 H2 !fmap_app !concat_app.
  f_equal. cbn [fmap list_fmap concat].
  rewrite /ulines_cyc ins_app Hin (app_nil_r (ins (open_seg h))).
  reflexivity.
Qed.

Lemma ulines_of_out (h : list mobs) (i : uart_id) (b : bv 8) :
  trace_shape h true -> ulines_of (h ++ [ObsUartOut i b]) = ulines_of h.
Proof using.
  intros Hsh. apply ulines_of_io; [exact Hsh | by destruct i | by destruct i].
Qed.

Lemma ulines_of_power (h : list mobs) (on : bool) :
  ulines_of (h ++ [if on then ObsPowerOff else ObsPowerOn]) = ulines_of h.
Proof using.
  rewrite /ulines_of. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on fmap_app concat_app.
    cbn [fmap list_fmap concat]. rewrite /ulines_cyc.
    rewrite (_ : ins [] = []); [| reflexivity].
    rewrite /ulines_in bodies_of_nil fmap_nil.
    by rewrite !app_nil_r.
Qed.

Lemma ulines_before_cut (h : list mobs) (cs : list (list mobs)) (o : list mobs) :
  cycles_of h = cs ++ [o] -> ulines_before h (length cs) = concat (ulines_cyc <$> cs).
Proof using. intros Hc. rewrite /ulines_before Hc take_app_length. reflexivity. Qed.

Lemma ulines_of_cut (h : list mobs) (cs : list (list mobs)) (o : list mobs) :
  cycles_of h = cs ++ [o] -> ins o = [] -> ulines_of h = concat (ulines_cyc <$> cs).
Proof using.
  intros Hc Ho. rewrite /ulines_of Hc fmap_app concat_app.
  cbn [fmap list_fmap concat]. rewrite /ulines_cyc Ho /ulines_in bodies_of_nil.
  by rewrite !app_nil_r.
Qed.

(* ---- THE REDIRECT LINES ARE THE LIST'S PROJECTION: the union's parser
        answers a redirect exactly where the file model's does ---- *)
Lemma echof_ws_uline_of_u b : echof_ws (uline_of_u b) = echof_ws (uline_of b).
Proof using.
  rewrite /uline_of_u /uline_of. destruct (parse_line b) as [l |]; [reflexivity |].
  cbn [default]. destruct (pl_parse b) as [[ws | p n] |]; cbn;
    try (destruct (secc_parse b); [reflexivity |]; destruct (sync_parse b); reflexivity).
Qed.

Lemma omap_concat {A B} (f : A -> option B) (L : list (list A)) :
  omap f (concat L) = concat ((fun l : list A => omap f l : list B) <$> L).
Proof using. induction L as [| l L IH]; [reflexivity |]. by rewrite /= omap_app IH. Qed.

Lemma ulines_in_echof I : omap echof_ws (ulines_in I) = echof_lines_in I.
Proof using.
  rewrite /ulines_in /echof_lines_in /lines_of.
  induction (bodies_of I) as [| b bs IH]; [reflexivity |].
  cbn [fmap list_fmap omap list_omap]. rewrite echof_ws_uline_of_u IH. reflexivity.
Qed.

Lemma ulines_cycs_echof (segs : list (list mobs)) :
  omap echof_ws (concat (ulines_cyc <$> segs)) = concat (echof_cyc <$> segs).
Proof using.
  rewrite omap_concat. f_equal. rewrite -list_fmap_compose. apply list_fmap_ext.
  intros _ seg _. exact (ulines_in_echof (ins seg)).
Qed.

Lemma ulines_of_echof h : omap echof_ws (ulines_of h) = echof_lines_of h.
Proof using. exact (ulines_cycs_echof _). Qed.

Lemma ulines_before_echof h k : omap echof_ws (ulines_before h k) = echof_lines_before h k.
Proof using. exact (ulines_cycs_echof _). Qed.

(* ===================================================================== *)
(*  2.  THE ADMISSIBLE SETS, AND THE SHRINK                               *)
(* ===================================================================== *)

(* a sync record: the position of the first line typed after the sync,
   and the files at the sync *)
Definition srec : Type := (nat * fstate)%type.

(* no sync yet: the mkfs image, before every line *)
Definition srec0 : srec := (0, ∅).

(* THE DESIGN'S [Adm(ls, k)] AT THE k-TH RECORD: every file as the sync
   left it, or a chunk subset of a redirect line at its name typed after
   the sync *)
Definition uadm (ls : list uline) (r : srec) (s : fstate) : Prop :=
  forall N, s !! N = r.2 !! N
            \/ exists ws sel, LEchoF ws N ∈ drop r.1 ls
                              /\ sel_ok (echo_chunks ws) sel
                              /\ s !! N = Some (subseq (echo_chunks ws) sel).

(* the state at the sync is admissible at its own record *)
Lemma uadm_self ls r : uadm ls r r.2.
Proof using. intros N. by left. Qed.

(* WITH NO SYNC, THE LANDED SET: [fadm_boot] of the redirect lines *)
Lemma uadm_srec0 ls s : uadm ls srec0 s <-> fadm_boot (omap echof_ws ls) s.
Proof using.
  split.
  - intros H N c Hc. destruct (H N) as [H0 | (ws & sel & Hin & Hsel & Hs)].
    + rewrite Hc lookup_empty in H0. discriminate H0.
    + rewrite Hc in Hs. injection Hs as ->. exists ws, sel.
      split_and!; [| exact Hsel | reflexivity].
      apply list_elem_of_omap. exists (LEchoF ws N). split; [exact Hin | reflexivity].
  - intros H N. destruct (s !! N) as [c |] eqn:Hc; [right | left; by rewrite lookup_empty].
    destruct (H N c Hc) as (ws & sel & Hin & Hsel & ->).
    apply list_elem_of_omap in Hin as (l & Hl & Hw).
    destruct l; try discriminate Hw. injection Hw as <- <-.
    exists ws0, sel. rewrite drop_0. by split_and!.
Qed.

(* MONOTONE IN THE LIST: a line typed later only adds states *)
Lemma uadm_mono ls ls' r s : ls `prefix_of` ls' -> uadm ls r s -> uadm ls' r s.
Proof using.
  intros [z ->] H N. destruct (H N) as [H0 | (ws & sel & Hin & Hsel & Hs)]; [by left |].
  right. exists ws, sel. split_and!; [| exact Hsel | exact Hs].
  destruct (decide (r.1 <= length ls)) as [Hle | Hgt].
  - rewrite drop_app_le; [| exact Hle]. apply elem_of_app. by left.
  - rewrite drop_ge in Hin; [| lia]. by apply elem_of_nil in Hin.
Qed.

(* ONE RECORD ABOVE ANOTHER: later in the list, and its state admissible
   at the earlier one *)
Definition srec_le (ls : list uline) (r r' : srec) : Prop :=
  r.1 <= r'.1 /\ uadm ls r r'.2.

(* THE SHRINK: the sets shrink as the records rise *)
Lemma uadm_shrink ls r r' s : srec_le ls r r' -> uadm ls r' s -> uadm ls r s.
Proof using.
  intros [Hp Hr] H N. destruct (H N) as [H0 | (ws & sel & Hin & Hsel & Hs)].
  - rewrite H0. exact (Hr N).
  - right. exists ws, sel. split_and!; [| exact Hsel | exact Hs].
    rewrite (_ : r'.1 = r.1 + (r'.1 - r.1)) in Hin; [| lia].
    rewrite -drop_drop in Hin.
    apply list_elem_of_lookup in Hin as [j Hj]. rewrite lookup_drop in Hj.
    apply list_elem_of_lookup. by eexists.
Qed.

Lemma srec_le_refl ls r : srec_le ls r r.
Proof using. split; [lia | apply uadm_self]. Qed.

Lemma srec_le_trans ls r r' r'' : srec_le ls r r' -> srec_le ls r' r'' -> srec_le ls r r''.
Proof using.
  intros [H1 H2] [H3 H4]. split; [lia |]. exact (uadm_shrink ls r r' _ (conj H1 H2) H4).
Qed.

Lemma srec_le_mono ls ls' r r' : ls `prefix_of` ls' -> srec_le ls r r' -> srec_le ls' r r'.
Proof using. intros Hp [H1 H2]. split; [exact H1 | exact (uadm_mono ls ls' r _ Hp H2)]. Qed.

(* every record is above [srec0] once its state is admissible there *)
Lemma srec_le_0 ls r : uadm ls srec0 r.2 -> srec_le ls srec0 r.
Proof using. intros H. split; [cbn; lia | exact H]. Qed.

(* THE SHRINK AT A COUNTER (design section 4's form): records numbered by
   the sync counter, each above the one before; then [Adm(ls, k') ⊆
   Adm(ls, k)] for [k <= k'] *)
Lemma uadm_shrink_chain ls (rec : nat -> srec) k k' s :
  (forall j, k <= j -> j < k' -> srec_le ls (rec j) (rec (S j))) ->
  k <= k' -> uadm ls (rec k') s -> uadm ls (rec k) s.
Proof using.
  intros Hch Hk. induction k' as [| k' IH]; intros H.
  - assert (k = 0) as -> by lia. exact H.
  - destruct (decide (k = S k')) as [-> | Hne]; [exact H |].
    apply IH; [intros j Hj1 Hj2; apply Hch; lia | lia |].
    exact (uadm_shrink ls (rec k') (rec (S k')) s (Hch k' ltac:(lia) ltac:(lia)) H).
Qed.

(* ---- THE RUNNING STATE STAYS INSIDE: a round of a line typed after the
        sync moves one file to a chunk subset of that line, and every
        other round moves nothing ---- *)
Lemma uadm_redir ls r s ws N sel :
  LEchoF ws N ∈ drop r.1 ls -> sel_ok (echo_chunks ws) sel ->
  uadm ls r s -> uadm ls r (<[N := subseq (echo_chunks ws) sel]> s).
Proof using.
  intros Hin Hsel H M. destruct (decide (M = N)) as [-> | Hne].
  - right. exists ws, sel. rewrite lookup_insert_eq. by split_and!.
  - rewrite lookup_insert_ne; [| done]. exact (H M).
Qed.

Lemma uadm_ustep ls r s (j : nat) (l : uline) (a : ualt) :
  ls !! j = Some l -> r.1 <= j -> uok adm_u_g s l a ->
  uadm ls r s -> uadm ls r (ustep s l a).
Proof using.
  intros Hj Hr Hok H.
  destruct a as [a | x | x | u]; cbn [ustep]; [| exact H | exact H | exact H].
  destruct l as [ws | ws N | N | p n | ws |]; cbn [fsm]; try exact H.
  assert (Hin : LEchoF ws N ∈ drop r.1 ls).
  { apply list_elem_of_lookup. exists (j - r.1). rewrite lookup_drop.
    by rewrite (_ : r.1 + (j - r.1) = j); [| lia]. }
  cbn [uok ralt_ok] in Hok.
  destruct a; try exact H; try contradiction.
  - exact (uadm_redir ls r s ws N sel Hin Hok H).
  - rewrite -(subseq_nil (echo_chunks ws)).
    exact (uadm_redir ls r s ws N [] Hin (sel_ok_nil _) H).
  - destruct (s !! N); [exact H |].
    rewrite -(subseq_nil (echo_chunks ws)).
    exact (uadm_redir ls r s ws N [] Hin (sel_ok_nil _) H).
Qed.

(* ===================================================================== *)
(*  3.  THE CYCLE'S SYNC RECORD, READ OFF ITS RESOLUTION                  *)
(* ===================================================================== *)

(* round [i] is a COMPLETED sync: its line is [sync], /sync ran, and the
   round's whole block -- through the prompt sh prints after /sync exits
   -- is on the wire [w].  The record's position is local: the lines of
   this cycle after round [i] start at [S i]. *)
Definition usync_at (ps cs : list nat) (s : fstate) (I w : list (bv 8)) (i : nat)
    : option srec :=
  if decide (uline_of_u (bodies_of I !!! i) = LSync
             /\ ualt_dec (cs !!! i) = UR RSyncRan
             /\ (pro_of ps ++ lm_seq U ps cs s (bodies_of I) (S i)) `prefix_of` w)
  then Some (S i, lm_upto U cs s (bodies_of I) i) else None.

Definition usyncs (ps cs : list nat) (s : fstate) (I w : list (bv 8)) : list srec :=
  omap (usync_at ps cs s I w) (seq 0 (nlines I)).

(* the cycle's LAST completed sync, at local position *)
Definition usync_last (ps cs : list nat) (s : fstate) (I w : list (bv 8)) : option srec :=
  last (usyncs ps cs s I w).

(* THE PER-CYCLE CLAIM: [lm_good_out] with its resolution's sync record *)
Definition lm_good_sync (s : fstate) (seg : list mobs) (o : option srec) : Prop :=
  exists ps cs : list nat,
    lm_pro_ok U ps cs (nlines (ins seg))
    /\ lm_alts_ok U s (ins seg) cs
    /\ obs_wire Uart0 seg `prefix_of` lm_sess U ps cs s (ins seg)
    /\ o = usync_last ps cs s (ins seg) (obs_wire Uart0 seg).

Lemma lm_good_sync_out s seg o : lm_good_sync s seg o -> lm_good_out U s seg.
Proof using. intros (ps & cs & H1 & H2 & H3 & _). exists ps, cs. by split_and!. Qed.

Lemma lm_good_sync_nil s : lm_good_sync s [] None.
Proof using.
  destruct (lm_good_out_nil U s) as (ps & cs & H1 & H2 & H3).
  exists ps, cs. split_and!; [exact H1 | exact H2 | exact H3 |].
  rewrite /usync_last /usyncs (_ : nlines (ins []) = 0); reflexivity.
Qed.

(* ---- the record is stable while the wire is: a longer input adds a
        round whose block is not on the wire ---- *)
Lemma cs_prefix_total (cs cs' : list nat) j :
  cs `prefix_of` cs' -> j < length cs -> cs' !!! j = cs !!! j.
Proof using.
  intros [z ->] Hj. rewrite !list_lookup_total_alt lookup_app_l; [reflexivity | exact Hj].
Qed.

Lemma usync_at_ext ps cs cs' s I I' w i :
  length cs = nlines I -> cs `prefix_of` cs' -> I `prefix_of` I' -> i < nlines I ->
  usync_at ps cs' s I' w i = usync_at ps cs s I w i.
Proof using.
  intros Hlen Hcc HII Hi.
  assert (Hbb : forall j, j < nlines I -> bodies_of I' !!! j = bodies_of I !!! j).
  { intros j Hj. destruct HII as [k ->]. destruct (bodies_of_app I k) as [z Hz].
    rewrite Hz. rewrite !list_lookup_total_alt lookup_app_l; [reflexivity |].
    exact Hj. }
  assert (Hc : forall j, j < S i -> cs' !!! j = cs !!! j)
    by (intros j Hj; apply cs_prefix_total; [exact Hcc | lia]).
  rewrite /usync_at (Hbb i Hi) (Hc i ltac:(lia)).
  rewrite (lm_seq_cs_ext U ps cs' cs s (bodies_of I') (S i) Hc).
  rewrite (lm_seq_bs_ext U ps cs s (bodies_of I') (bodies_of I) (S i)
             ltac:(intros j Hj; apply Hbb; lia)).
  rewrite (lm_upto_cs_ext U cs' cs s (bodies_of I') i ltac:(intros j Hj; apply Hc; lia)).
  rewrite (lm_upto_bs_ext U cs s (bodies_of I') (bodies_of I) i
             ltac:(intros j Hj; apply Hbb; lia)).
  reflexivity.
Qed.

(* the new round after a newline: its block ends past the old wire *)
Lemma usync_at_new ps cs cs' s I w :
  length cs = nlines I -> cs `prefix_of` cs' ->
  w `prefix_of` lm_sess U ps cs s I ->
  usync_at ps cs' s (I ++ [wl_nl]) w (nlines I) = None.
Proof using.
  intros Hlen Hcc Hw. rewrite /usync_at. case_decide as Hd; [exfalso | reflexivity].
  destruct Hd as (_ & _ & Hp).
  rewrite lm_seq_S bodies_of_snoc_nl in Hp.
  rewrite (lm_seq_cs_ext U ps cs' cs s _ (nlines I)
             ltac:(intros j Hj; apply cs_prefix_total; [exact Hcc | lia])) in Hp.
  rewrite (lm_seq_bs_ext U ps cs s (bodies_of I ++ [rest_of I]) (bodies_of I) (nlines I)
             ltac:(intros j Hj; rewrite !list_lookup_total_alt lookup_app_l;
                   [reflexivity | exact Hj])) in Hp.
  rewrite /lm_blk in Hp.
  rewrite (_ : (bodies_of I ++ [rest_of I]) !!! nlines I = rest_of I) in Hp;
    [| rewrite list_lookup_total_alt lookup_app_r; [| rewrite /nlines; lia];
       rewrite /nlines Nat.sub_diag; reflexivity].
  pose proof (prefix_length _ _ (PreOrder_Transitive _ _ _ Hp Hw)) as HL.
  rewrite /lm_sess !length_app in HL. cbn [length] in HL. lia.
Qed.

Lemma usyncs_ext ps cs cs' s I I' w :
  length cs = nlines I -> cs `prefix_of` cs' ->
  w `prefix_of` lm_sess U ps cs s I ->
  (I' = I \/ exists b, I' = I ++ [b]) ->
  usyncs ps cs' s I' w = usyncs ps cs s I w.
Proof using.
  intros Hlen Hcc Hw HI'.
  assert (HII : I `prefix_of` I')
    by (destruct HI' as [-> | (b & ->)]; [reflexivity | by eexists]).
  assert (Hseq : forall n, n <= nlines I ->
            omap (usync_at ps cs' s I' w) (seq 0 n) = omap (usync_at ps cs s I w) (seq 0 n)).
  { intros n Hn. induction n as [| n IH]; [reflexivity |].
    rewrite seq_S !omap_app IH; [| lia].
    cbn [omap list_omap]. rewrite (usync_at_ext ps cs cs' s I I' w n Hlen Hcc HII); [| lia].
    reflexivity. }
  rewrite /usyncs. destruct HI' as [-> | (b & ->)]; [exact (Hseq (nlines I) ltac:(lia)) |].
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite nlines_snoc_nl seq_S omap_app Hseq; [| lia].
    cbn [omap list_omap]. rewrite (usync_at_new ps cs cs' s I w Hlen Hcc Hw).
    by rewrite app_nil_r.
  - rewrite (nlines_snoc_other I b Hb). exact (Hseq (nlines I) ltac:(lia)).
Qed.

(* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE keeps the cycle good
   with the same record ([lm_good_out_step]'s resolution, padded) *)
Lemma lm_good_sync_step (s : fstate) (seg : list mobs) (e : mobs) (o : option srec) :
  obs_wire Uart0 [e] = [] -> lm_good_sync s seg o -> lm_good_sync s (seg ++ [e]) o.
Proof using.
  intros He (ps & cs & [Hpsb Hlt] & Hao & Hwire & ->).
  set (I := ins seg). set (I' := ins (seg ++ [e])).
  assert (HI' : I' = I \/ exists b, I' = I ++ [b]).
  { rewrite /I' /I ins_app.
    destruct e as [[] b | i b | |].
    - right. exists b. by rewrite ins_in.
    - left. rewrite (_ : ins [ObsUartIn Uart1 b] = []); [by rewrite app_nil_r | reflexivity].
    - left. rewrite (_ : ins [ObsUartOut i b] = []); [by rewrite app_nil_r | by destruct i].
    - left. rewrite (_ : ins [ObsPowerOn] = []); [by rewrite app_nil_r | reflexivity].
    - left. rewrite (_ : ins [ObsPowerOff] = []); [by rewrite app_nil_r | reflexivity]. }
  assert (HII : I `prefix_of` I')
    by (destruct HI' as [-> | (b & ->)]; [reflexivity | by eexists]).
  assert (Hlen : length cs = nlines I) by exact (lm_alts_ok_len U s _ _ Hao).
  assert (Hnl : (nlines I <= nlines I')%nat) by (by apply nlines_prefix).
  set (cs' := lm_alts_pad U UK I' cs).
  assert (Hcc : cs `prefix_of` cs') by apply lm_alts_pad_prefix.
  assert (Hw : obs_wire Uart0 (seg ++ [e]) = obs_wire Uart0 seg)
    by (rewrite obs_wire_app He app_nil_r; reflexivity).
  exists ps, cs'. split_and!.
  - split; [exact Hpsb |].
    rewrite /cs' (lm_alts_pad_pro_idx U UK UB I' cs (nlines I') ltac:(lia)).
    rewrite (lm_pro_idx_ge U UB cs (nlines I) (nlines I') ltac:(lia) Hnl).
    exact Hlt.
  - rewrite /cs'. apply lm_alts_pad_ok.
    apply (lm_alts_pre_mono U s I I'); [exact HII |].
    exact (lm_alts_pre_of_alts_ok U s _ _ Hao).
  - rewrite Hw. etrans; [exact Hwire |].
    assert (Hcut : lm_sess U ps cs s I = lm_sess U ps cs' s I).
    { apply lm_sess_cs_ext. intros j Hj. symmetry. apply cs_prefix_total; [exact Hcc | lia]. }
    rewrite Hcut. by apply lm_sess_mono.
  - rewrite Hw /usync_last.
    rewrite (usyncs_ext ps cs cs' s I I' (obs_wire Uart0 seg) Hlen Hcc Hwire HI').
    reflexivity.
Qed.

(* ===================================================================== *)
(*  4.  THE LAST RECORD OF THE EARLIER CYCLES                             *)
(* ===================================================================== *)

(* walk the cycles with their local records, carrying the line offset:
   the latest completed sync, at its GLOBAL position ([srec0] if none) *)
Fixpoint ulast_from (off : nat) (r : srec) (segs : list (list mobs))
    (os : list (option srec)) : srec :=
  match segs, os with
  | seg :: segs', o :: os' =>
      ulast_from (off + nlines (ins seg))
        (match o with Some r' => (off + r'.1, r'.2) | None => r end) segs' os'
  | _, _ => r
  end.

(* the record a boot at cycle [k] reads: the last completed sync of the
   cycles strictly before [k], given each cycle's own ([os]) *)
Definition ulast_before (h : list mobs) (os : list (option srec)) (k : nat) : srec :=
  ulast_from 0 srec0 (take k (cycles_of h)) os.

(* the walk reads one record per cycle it walks *)
Lemma ulast_from_take off r segs os :
  ulast_from off r segs os = ulast_from off r segs (take (length segs) os).
Proof using.
  revert off r os. induction segs as [| seg segs IH]; intros off r os.
  - by destruct os.
  - destruct os as [| o os]; [reflexivity |]. cbn [length take ulast_from].
    exact (IH _ _ os).
Qed.

Lemma ulast_before_ext h h' os os' k :
  take k (cycles_of h) = take k (cycles_of h') -> take k os = take k os' ->
  ulast_before h os k = ulast_before h' os' k.
Proof using.
  intros Hc Ho. rewrite /ulast_before Hc.
  rewrite (ulast_from_take 0 srec0 _ os) (ulast_from_take 0 srec0 _ os').
  assert (Hn : forall l : list (option srec),
             take (length (take k (cycles_of h'))) l
             = take (length (take k (cycles_of h'))) (take k l)).
  { intros l. rewrite take_take. f_equal. rewrite length_take. lia. }
  by rewrite Hn (Hn os') Ho.
Qed.

(* ===================================================================== *)
(*  5.  THE BRIDGE (lane SY3-A4, step 1): THE RECORD A COMPLETED SYNC     *)
(*      ROUND'S HOOK APPENDS IS THE MODEL'S                               *)
(*                                                                        *)
(*  The hook appends [(length ls', s)] with [ls'] sh's line lower bound   *)
(*  ending at the sync line ([FileLinksLine.flw I]: the era's base        *)
(*  followed by the round's input lines) and [s] the deed's state at      *)
(*  PEND.  The model records [(S i, lm_upto cs s0 bodies i)] at the sync  *)
(*  line's LOCAL index [i] ([usync_at]) and [ulast_before] offsets it by  *)
(*  the earlier cycles' lines.  Locally: the round's index is [nlines I - *)
(*  1], so [S i = nlines I], and /sync's alternative moves no file, so    *)
(*  the deed's PEND state is the model's state before the round.         *)
(*  Globally: the offset [ulast_from] adds IS the length of the earlier   *)
(*  cycles' lines ([ulast_before_snoc_some]), which is the era's base.   *)
(* ===================================================================== *)

(* AT A PADDED RESOLUTION the last completed sync is a FILED round's: the
   pad files each line's exec failure, which is never /sync's run *)
Lemma usync_last_pad (ps cs : list nat) (s : fstate) (I w : list (bv 8)) (r : srec) :
  usync_last ps (lm_alts_pad U UK I cs) s I w = Some r ->
  exists i, i < length cs /\ i < nlines I
            /\ usync_at ps (lm_alts_pad U UK I cs) s I w i = Some r.
Proof using.
  rewrite /usync_last /usyncs. intros Hl.
  apply last_Some_elem_of in Hl.
  apply list_elem_of_omap in Hl as (i & Hi & Hu). apply elem_of_seq in Hi.
  exists i. destruct (decide (i < length cs)) as [Hic | Hic]; [split_and!; [exact Hic | lia | exact Hu] |].
  exfalso. revert Hu. rewrite /usync_at. case_decide as Hd; [| discriminate].
  intros _. destruct Hd as (Hls & Ha & _).
  rewrite /lm_alts_pad list_lookup_total_alt lookup_app_r in Ha; [| lia].
  rewrite list_lookup_fmap lookup_drop in Ha.
  replace (length cs + (i - length cs)) with i in Ha by lia.
  rewrite list_lookup_total_alt in Hls.
  destruct (bodies_of I !! i) as [b |] eqn:Hb;
    [| apply lookup_ge_None in Hb; rewrite /nlines in Hi; lia].
  cbn in Hls, Ha. change (lm_of U b) with (uline_of_u b) in Ha.
  rewrite Hls in Ha. vm_compute in Ha. discriminate Ha.
Qed.

(* THE GLOBAL OFFSET: walking the cycles adds each cycle's line count, so
   a record of the cycle at index [n] is offset by the lines of the cycles
   before it *)
Lemma ulast_from_app (off : nat) (r : srec) (segs segs' : list (list mobs))
    (os os' : list (option srec)) :
  length os = length segs ->
  ulast_from off r (segs ++ segs') (os ++ os')
  = ulast_from (off + length (concat (ulines_cyc <$> segs)))
      (ulast_from off r segs os) segs' os'.
Proof using.
  revert off r os. induction segs as [| seg segs IH]; intros off r os Hl.
  - destruct os; [| discriminate Hl]. cbn. by rewrite Nat.add_0_r.
  - destruct os as [| o os]; [discriminate Hl |]. cbn [app ulast_from].
    rewrite (IH _ _ os ltac:(cbn in Hl; lia)). f_equal.
    cbn [fmap list_fmap concat]. rewrite length_app /ulines_cyc ulines_in_length. lia.
Qed.

Lemma ulines_before_length_take (h : list mobs) (n : nat) :
  length (ulines_before h n) = length (concat (ulines_cyc <$> take n (cycles_of h))).
Proof using. reflexivity. Qed.

(* the open cycle's record [Some r'], at its GLOBAL position *)
Lemma ulast_before_snoc_some (h : list mobs) (os : list (option srec)) (r' : srec) :
  length os < length (cycles_of h) ->
  ulast_before h (os ++ [Some r']) (S (length os))
  = (length (ulines_before h (length os)) + r'.1, r'.2).
Proof using.
  intros Hlt. rewrite /ulast_before.
  destruct (lookup_lt_is_Some_2 (cycles_of h) (length os) Hlt) as [seg Hseg].
  rewrite (take_S_r _ _ _ Hseg).
  rewrite (ulast_from_app 0 srec0 _ [seg] os [Some r']); [| rewrite length_take; lia].
  cbn [ulast_from]. rewrite ulines_before_length_take. reflexivity.
Qed.

(* ...and [None]: the earlier cycles' record stands *)
Lemma ulast_before_snoc_none (h : list mobs) (os : list (option srec)) :
  length os < length (cycles_of h) ->
  ulast_before h (os ++ [None]) (S (length os)) = ulast_before h os (length os).
Proof using.
  intros Hlt. rewrite /ulast_before.
  destruct (lookup_lt_is_Some_2 (cycles_of h) (length os) Hlt) as [seg Hseg].
  rewrite (take_S_r _ _ _ Hseg).
  rewrite (ulast_from_app 0 srec0 _ [seg] os [None]); [| rewrite length_take; lia].
  cbn [ulast_from]. reflexivity.
Qed.

(* THE BRIDGE, WHOLE: the hook's record over sh's line lower bound [base ++
   ulines_in I] (the era's base, which is the earlier cycles' lines) is the
   model's last completed sync once the open cycle's record is the round's *)
Lemma usync_bridge (h : list mobs) (os : list (option srec)) (base : list uline)
    (I : list (bv 8)) (c : fstate) :
  length os < length (cycles_of h) ->
  base = ulines_before h (length os) ->
  ulast_before h (os ++ [Some (nlines I, c)]) (S (length os))
  = (length (base ++ ulines_in I), c).
Proof using.
  intros Hlt ->. rewrite (ulast_before_snoc_some h os _ Hlt) length_app ulines_in_length.
  reflexivity.
Qed.
