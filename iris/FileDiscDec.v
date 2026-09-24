(* FileDiscDec.v -- [FileDisc.disc_f] IS DECIDABLE, so the file ledger's
   taint counter can be at [decide (disc_f h)].

   Design of record: claude-notes/design/app-file.md section 4.3a, ruling
   "Blocker 1"; lane FILE-DEC.  [EchoDisc.disc_seg'_dec] decides the echo
   discipline by a finite search over the prologue resolutions
   ([pro_cands], through [pro_canon]) and the per-line choices
   ([bounded_lists 4]).  Two things stop that search from porting verbatim:

   - THE CHOICES ARE NO LONGER BOUNDED BY 4.  A round's code decodes to a
     [FileDisc.ralt], and [RFRan sel] carries a chunk subset through a
     countable encoding, so the codes a line admits are not an initial
     segment of the naturals.  They ARE finite per line: [ralt_ok] pins
     [sel] to [FileState.sel_ok (echo_chunks ws)], i.e. to a strictly
     increasing list over [seq 0 (length (echo_chunks ws))], of which there
     are 2^n.  [sel_cands] enumerates those and [alts_cands] the codes.
     The enumerator lists only CANONICAL codes [ralt_enc a]; a witness is
     canonicalised to those by [cs_canon], which is sound because every
     consumer of [cs] -- [pro_idx_f], [fstate_upto], [alt_cont_f], [sessf],
     [pro_ok_f], [disc_pt_f], [alts_ok] -- reads it ONLY through
     [ralt_at = ralt_dec o (!!!)], and [ralt_dec (ralt_enc (ralt_dec c)) =
     ralt_dec c].
   - THE BOOT STATE RANGES OVER ALL BYTE LISTS.  [disc_f] is
     [exists s : fstate, fstate_ok s /\ disc_seg_f' s seg], and [s] is not bounded
     by anything syntactic.  [disc_seg_f'_canon] is the design's
     canonicalisation lemma: the witness may always be taken from
     [scands seg = None :: Some [] :: (Some <$> substrings (obs_wire Uart0
     seg))].  WHY.  [cont] reads the file state at ONE alternative,
     [RCRan], where it prints the content VERBATIM; and the state before a
     round is either the boot state itself or a value the boot state does
     not enter ([fstate_upto_vs_nil]: the chain at [s] and the chain at
     [Some []] agree from the first round that moves the file, and until
     then the first is [s] and the second is [Some []]).  So either some
     checked prefix's transcript prints the boot content -- and then it is
     a contiguous substring of that prefix's wire, hence of the segment's
     -- or every checked transcript is the one at [Some []] and that state
     serves.

   Nothing here is evaluated: the instance is a decision procedure for the
   ledger to case on, never a computation on a literal.  [FileDisc]'s own
   witnesses ([demo_f1] .. [demo_f_bad]) are proved by other means. *)
From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import Sorted.        (* [StronglySorted], [sel_ok]'s order *)
From stdpp Require Import list list_numbers countable bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire Uart0], [cycles_of] *)
Require Import LineWords.
Require Import EchoDisc.         (* [pro_cands], [pro_canon], [nlines_max] *)
Require Import FileDisc.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(* ====================================================================== *)
(*  0.  SMALL LIST FACTS                                                   *)
(* ====================================================================== *)

Lemma fdd_snoc_inv {A} (l : list A) : l = [] \/ (exists u x, l = u ++ [x]).
Proof using.
  induction l as [| a l IH]; [by left | right].
  destruct IH as [-> | (u & x & ->)].
  - by exists [], a.
  - by exists (a :: u), x.
Qed.

Lemma fdd_infix_cons {A} (x : A) (u v y : list A) :
  exists C D, u ++ x :: (v ++ y) = C ++ v ++ D.
Proof using. exists (u ++ [x]), y. by rewrite -!app_assoc. Qed.

(* ====================================================================== *)
(*  1.  THE CONTENT IS DECIDABLE                                           *)
(* ====================================================================== *)

(* [fcont_ok]'s second arm at a shape a decision procedure can read: the
   existential [exists v, bs = v ++ [wl_nl]] IS [last bs = Some wl_nl]. *)
Definition fcont_ok' (bs : list (bv 8)) : Prop :=
  Forall wl_body_byte bs
  \/ (last bs = Some wl_nl /\ Forall wl_body_byte (removelast bs)).

Global Instance fcont_ok'_dec bs : Decision (fcont_ok' bs).
Proof using. rewrite /fcont_ok'. apply _. Defined.

Lemma fcont_ok_iff bs : fcont_ok bs <-> fcont_ok' bs.
Proof using.
  rewrite /fcont_ok /fcont_ok'. split.
  - intros [HF | (v & HF & ->)]; [by left | right].
    rewrite last_snoc removelast_last. by split.
  - intros [HF | [Hl HF]]; [by left | right].
    destruct (fdd_snoc_inv bs) as [-> | (u & x & ->)]; [done |].
    rewrite last_snoc in Hl. rewrite removelast_last in HF.
    exists u. split; [exact HF | by injection Hl as ->].
Qed.

Global Instance fcont_ok_dec bs : Decision (fcont_ok bs).
Proof using.
  destruct (decide (fcont_ok' bs)) as [H | H].
  - left. by apply fcont_ok_iff.
  - right. intro Hc. apply H, fcont_ok_iff, Hc.
Defined.

Global Instance fstate_ok_dec s : Decision (fstate_ok s).
Proof using. destruct s as [bs |]; rewrite /fstate_ok; apply _. Defined.

(* ====================================================================== *)
(*  2.  THE CHUNK SUBSETS OF ONE LINE                                      *)
(* ====================================================================== *)

(* every strictly increasing list over [seq 0 n], built by appending the
   largest index last -- which is the only place it can go *)
Fixpoint sel_cands (n : nat) : list (list nat) :=
  match n with
  | 0%nat => [[]]
  | S n' => sel_cands n' ++ ((fun s => s ++ [n']) <$> sel_cands n')
  end.

Lemma StronglySorted_lt_snoc_inv (sel : list nat) (j : nat) :
  StronglySorted lt (sel ++ [j]) ->
  StronglySorted lt sel /\ Forall (fun i => i < j) sel.
Proof using.
  induction sel as [| a sel IH]; cbn [app]; intro H.
  { split; constructor. }
  apply StronglySorted_inv in H as [H Hf].
  destruct (IH H) as [Hs Hlt].
  apply Forall_app in Hf as [Ha Hj]. rewrite Forall_singleton in Hj.
  split.
  - constructor; [exact Hs | exact Ha].
  - constructor; [exact Hj | exact Hlt].
Qed.

Lemma fdd_Forall_lt_weaken (l : list nat) (m n : nat) :
  (m <= n)%nat -> Forall (fun j => j < m) l -> Forall (fun j => j < n) l.
Proof using.
  intros Hm HF. apply Forall_forall. intros x Hx.
  pose proof (proj1 (Forall_forall _ _) HF x Hx) as Hx'. cbn beta in Hx'. lia.
Qed.

Lemma elem_of_sel_cands (n : nat) (sel : list nat) :
  sel ∈ sel_cands n <-> StronglySorted lt sel /\ Forall (fun j => j < n) sel.
Proof using.
  revert sel. induction n as [| n IH]; intros sel; cbn [sel_cands].
  - rewrite elem_of_list_singleton. split.
    + intros ->. split; constructor.
    + intros [_ HF]. destruct sel as [| j sel]; [reflexivity |].
      exfalso. apply Forall_cons_1 in HF as [Hj _]. cbn beta in Hj. lia.
  - rewrite elem_of_app elem_of_list_fmap. split.
    + intros [Hin | (u & -> & Hu)].
      * apply IH in Hin as [Hs HF]. split; [exact Hs |].
        apply (fdd_Forall_lt_weaken sel n (S n) ltac:(lia) HF).
      * apply IH in Hu as [Hs HF]. split.
        { by apply StronglySorted_lt_snoc. }
        apply Forall_app. split.
        { apply (fdd_Forall_lt_weaken u n (S n) ltac:(lia) HF). }
        apply Forall_singleton. cbn beta. lia.
    + intros [Hs HF].
      destruct (fdd_snoc_inv sel) as [-> | (u & x & ->)].
      { left. apply IH. split; constructor. }
      apply StronglySorted_lt_snoc_inv in Hs as [Hsu Hlt].
      apply Forall_app in HF as [HFu HFx]. rewrite Forall_singleton in HFx.
      cbn beta in HFx.
      destruct (decide (x = n)) as [-> | Hne].
      * right. exists u. split; [reflexivity |]. apply IH. by split.
      * assert (Hxn : x < n) by lia.
        left. apply IH. split.
        { by apply StronglySorted_lt_snoc. }
        apply Forall_app. split.
        { apply (fdd_Forall_lt_weaken u x n ltac:(lia) Hlt). }
        apply Forall_singleton. cbn beta. lia.
Qed.

Lemma sel_ok_cands (cs : list (list (bv 8))) (sel : list nat) :
  sel_ok cs sel <-> sel ∈ sel_cands (length cs).
Proof using. rewrite elem_of_sel_cands. by rewrite /sel_ok. Qed.

(* ====================================================================== *)
(*  3.  THE CODES ONE LINE ADMITS                                          *)
(* ====================================================================== *)

Definition ralt_fix_cands (l : uline) : list ralt :=
  match l with
  | LEcho _ => [REcho 0%nat; REcho 1%nat; REcho 2%nat; REcho 3%nat]
  | LEchoF _ => [RFExec; RFOpenU; RFOpenM; RFSilent; RFFork]
  | LCat => [RCRan; RCNoOpen; RCExec; RCSilent; RCFork]
  (* the DEAD arm: [FileDisc.ralt_ok] gives [LPipe] exactly [LCat]'s five *)
  | LPipe _ _ => [RCRan; RCNoOpen; RCExec; RCSilent; RCFork]
  end.

Definition ralt_cands (l : uline) : list nat :=
  (ralt_enc <$> ralt_fix_cands l)
  ++ match l with
     | LEchoF ws =>
         (fun sel => ralt_enc (RFRan sel))
           <$> sel_cands (length (echo_chunks ws))
     | _ => []
     end.

Lemma ralt_fix_cands_ok l : Forall (ralt_ok l) (ralt_fix_cands l).
Proof using.
  destruct l as [ws | ws | | ws npc]; cbn [ralt_fix_cands].
  - repeat (constructor; [cbn [ralt_ok]; lia |]). constructor.
  - repeat (constructor; [exact I |]). constructor.
  - repeat (constructor; [exact I |]). constructor.
  - repeat (constructor; [exact I |]). constructor.
Qed.

Ltac fdd_elem :=
  solve [ repeat first [ apply elem_of_list_here | apply elem_of_list_further ] ].

Lemma elem_of_ralt_cands l c : c ∈ ralt_cands l -> ralt_ok l (ralt_dec c).
Proof using.
  rewrite /ralt_cands elem_of_app. intros [Hin | Hin].
  - apply elem_of_list_fmap in Hin as (a & -> & Ha).
    rewrite ralt_dec_enc.
    exact (proj1 (Forall_forall _ _) (ralt_fix_cands_ok l) a Ha).
  - destruct l as [ws | ws | | ws npc]; try (by apply elem_of_nil in Hin).
    apply elem_of_list_fmap in Hin as (sel & -> & Hsel).
    rewrite ralt_dec_enc. cbn [ralt_ok].
    by apply (sel_ok_cands (echo_chunks ws) sel).
Qed.

Lemma ralt_cands_canon l c :
  ralt_ok l (ralt_dec c) -> ralt_enc (ralt_dec c) ∈ ralt_cands l.
Proof using.
  intro H. rewrite /ralt_cands elem_of_app.
  destruct l as [ws | ws | | ws npc];
    destruct (ralt_dec c) as [k | sel | | | | | | | | | |];
    cbn [ralt_ok] in H; try done.
  - left. apply elem_of_list_fmap. exists (REcho k). split; [reflexivity |].
    cbn [ralt_fix_cands].
    assert (Hk : k = 0%nat \/ k = 1%nat \/ k = 2%nat \/ k = 3%nat) by lia.
    destruct Hk as [-> | [-> | [-> | ->]]]; fdd_elem.
  - right. apply elem_of_list_fmap. exists sel. split; [reflexivity |].
    by apply sel_ok_cands.
  - left. apply elem_of_list_fmap. exists RFExec. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RFOpenU. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RFOpenM. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RFSilent. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RFFork. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCRan. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCNoOpen. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCExec. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCSilent. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCFork. split; [reflexivity |]. fdd_elem.
  (* ...and the dead [LPipe] arm, which is [LCat]'s five verbatim *)
  - left. apply elem_of_list_fmap. exists RCRan. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCNoOpen. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCExec. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCSilent. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCFork. split; [reflexivity |]. fdd_elem.
Qed.

(* ---- the resolution lists, line by line ----------------------------- *)

Fixpoint alts_cands (ls : list uline) : list (list nat) :=
  match ls with
  | [] => [[]]
  | l :: ls' =>
      (fun p => fst p :: snd p)
        <$> List.list_prod (ralt_cands l) (alts_cands ls')
  end.

Lemma elem_of_alts_cands (ls : list uline) (cs : list nat) :
  cs ∈ alts_cands ls <-> Forall2 (fun l c => c ∈ ralt_cands l) ls cs.
Proof using.
  revert cs. induction ls as [| l ls IH]; intros cs; cbn [alts_cands].
  - rewrite elem_of_list_singleton. split.
    + intros ->. constructor.
    + intro H. by apply Forall2_nil_inv_l in H.
  - rewrite elem_of_list_fmap. split.
    + intros ([c cs'] & -> & Hp). cbn [fst snd].
      apply elem_of_list_In, in_prod_iff in Hp as [Hc Hcs].
      apply elem_of_list_In in Hc. apply elem_of_list_In, IH in Hcs.
      by constructor.
    + intro H. apply Forall2_cons_inv_l in H as (c & cs' & Hc & Hcs & ->).
      exists (c, cs'). split; [reflexivity |].
      apply elem_of_list_In, in_prod_iff. split.
      * by apply elem_of_list_In.
      * by apply elem_of_list_In, IH.
Qed.

Lemma alts_cands_alts_ok (I : list (bv 8)) (cs : list nat) :
  cs ∈ alts_cands (lines_of I) -> alts_ok I cs.
Proof using.
  rewrite elem_of_alts_cands /alts_ok. intro H.
  eapply Forall2_impl; [exact H |]. intros l c Hc. by apply elem_of_ralt_cands.
Qed.

(* ====================================================================== *)
(*  4.  THE CANONICAL RESOLUTION                                           *)
(* ====================================================================== *)

(* EVERY consumer of [cs] reads it through [ralt_at], so replacing each
   entry by the canonical code of its own decoding moves nothing. *)
Definition cs_canon (cs : list nat) : list nat :=
  (fun c => ralt_enc (ralt_dec c)) <$> cs.

Lemma fdd_lookup_total_fmap (f : nat -> nat) (l : list nat) (i : nat) :
  f 0%nat = 0%nat -> (f <$> l) !!! i = f (l !!! i).
Proof using.
  intro Hf. rewrite !list_lookup_total_alt list_lookup_fmap.
  destruct (l !! i) as [x |]; cbn; [reflexivity | by rewrite Hf].
Qed.

Lemma cs_canon_at cs i : ralt_at (cs_canon cs) i = ralt_at cs i.
Proof using.
  rewrite /ralt_at /cs_canon (fdd_lookup_total_fmap _ cs i); [| by vm_compute].
  by rewrite ralt_dec_enc.
Qed.

Lemma pro_idx_f_canon cs i : pro_idx_f (cs_canon cs) i = pro_idx_f cs i.
Proof using.
  induction i as [| i IH]; [reflexivity |].
  by rewrite !pro_idx_f_S IH cs_canon_at.
Qed.

Lemma fstate_upto_canon cs s bs i :
  fstate_upto (cs_canon cs) s bs i = fstate_upto cs s bs i.
Proof using.
  induction i as [| i IH]; [reflexivity |].
  cbn [fstate_upto]. by rewrite IH cs_canon_at.
Qed.

Lemma alt_cont_f_canon ps cs s bs i :
  alt_cont_f ps (cs_canon cs) s bs i = alt_cont_f ps cs s bs i.
Proof using.
  by rewrite /alt_cont_f fstate_upto_canon cs_canon_at pro_idx_f_canon.
Qed.

Lemma alt_seq_f_canon ps cs s bs q :
  alt_seq_f ps (cs_canon cs) s bs q = alt_seq_f ps cs s bs q.
Proof using.
  induction q as [| q IH]; [reflexivity |].
  by rewrite !alt_seq_f_S IH /alt_blk_f alt_cont_f_canon.
Qed.

Lemma sessf_canon ps cs s I : sessf ps (cs_canon cs) s I = sessf ps cs s I.
Proof using. by rewrite /sessf alt_seq_f_canon. Qed.

Lemma alts_ok_cs_canon (I : list (bv 8)) (cs : list nat) :
  alts_ok I cs -> cs_canon cs ∈ alts_cands (lines_of I).
Proof using.
  rewrite /alts_ok elem_of_alts_cands /cs_canon. intro H.
  apply Forall2_fmap_r. eapply Forall2_impl; [exact H |].
  intros l c Hc. by apply ralt_cands_canon.
Qed.

Lemma disc_pt_all_f_canon ps cs s seg :
  disc_pt_all_f ps cs s seg -> disc_pt_all_f ps (cs_canon cs) s seg.
Proof using.
  rewrite /disc_pt_all_f. intro H. eapply Forall_impl; [exact H |].
  intros p [H1 H2]. split.
  - by rewrite /pro_ok_f pro_idx_f_canon.
  - by rewrite /disc_pt_f sessf_canon.
Qed.

(* ====================================================================== *)
(*  5.  THE PROLOGUE BOUND, AT [pro_idx_f]                                 *)
(* ====================================================================== *)

Lemma alt_seq_f_pro_len ps cs s bs q r :
  (r <= pro_idx_f cs q)%nat ->
  (length (pro_of (pro_from r ps))
   <= length (pro_of ps) + length (alt_seq_f ps cs s bs q))%nat.
Proof using.
  revert r. induction q as [| q IH]; intros r Hr.
  - assert (r = 0%nat) by (cbn [pro_idx_f] in Hr; lia). subst r.
    cbn [pro_from]. lia.
  - rewrite alt_seq_f_S length_app.
    destruct (decide (r <= pro_idx_f cs q)%nat) as [Hle | Hgt].
    + pose proof (IH r Hle). lia.
    + assert (Hp : ralt_panic (ralt_at cs q) = true).
      { destruct (ralt_panic (ralt_at cs q)) eqn:E; [reflexivity |].
        exfalso. rewrite (pro_idx_f_Sn cs q E) in Hr. lia. }
      rewrite (pro_idx_f_Sp cs q Hp) in Hr.
      assert (Hre : r = S (pro_idx_f cs q)) by lia.
      rewrite /alt_blk_f /alt_cont_f Hp !length_app.
      cbn [length]. rewrite length_app Hre. lia.
Qed.

Lemma sessf_pro_len ps cs s I r :
  (r <= pro_idx_f cs (nlines I))%nat ->
  (length (pro_of (pro_from r ps)) <= length (sessf ps cs s I))%nat.
Proof using.
  intro Hr. rewrite /sessf !length_app.
  pose proof (alt_seq_f_pro_len ps cs s (bodies_of I) (nlines I) r Hr). lia.
Qed.

(* ====================================================================== *)
(*  6.  CONTIGUOUS SUBSTRINGS                                              *)
(* ====================================================================== *)

Definition infixed {A} (m l : list A) : Prop := exists u v, l = u ++ m ++ v.

Definition substrings {A} (l : list A) : list (list A) :=
  (fun p => take (snd p) (drop (fst p) l))
    <$> List.list_prod (List.seq 0 (S (length l))) (List.seq 0 (S (length l))).

Lemma infixed_here {A} (m C D : list A) : infixed m (C ++ m ++ D).
Proof using. by exists C, D. Qed.

Lemma infixed_app_ctx {A} (m X A1 B1 : list A) :
  infixed m X -> infixed m (A1 ++ X ++ B1).
Proof using.
  intros (u & v & ->). exists (A1 ++ u), (v ++ B1). by rewrite -!app_assoc.
Qed.

Lemma infixed_prefix {A} (m l l' : list A) :
  infixed m l -> l `prefix_of` l' -> infixed m l'.
Proof using.
  intros (u & v & ->) [k ->]. exists u, (v ++ k). by rewrite -!app_assoc.
Qed.

Lemma elem_of_substrings {A} (m l : list A) : infixed m l -> m ∈ substrings l.
Proof using.
  intros (u & v & ->). rewrite /substrings. apply elem_of_list_fmap.
  exists (length u, length m). split.
  - cbn [fst snd].
    by rewrite drop_app_length take_app_length.
  - apply elem_of_list_In, in_prod; apply in_seq; rewrite !length_app; lia.
Qed.

(* ====================================================================== *)
(*  7.  THE BOOT-STATE CANONICALISATION                                    *)
(* ====================================================================== *)

Definition scands (seg : list mobs) : list fstate :=
  None :: Some [] :: (Some <$> substrings (obs_wire Uart0 seg)).

(* THE STATE CHAIN AT [s] AGAINST THE ONE AT [Some []].  Until a round
   moves the file the two are their own boot states; from the first round
   that moves it they agree forever.  [RFOpenM] is the only arm that reads
   the state, and it keeps a present one and creates at an absent one --
   which is exactly why the disjunction is stated at [Some []] and not at
   an arbitrary second state. *)
Lemma fstate_upto_vs_nil cs s bs i :
  (fstate_upto cs s bs i = s /\ fstate_upto cs (Some []) bs i = Some [])
  \/ fstate_upto cs s bs i = fstate_upto cs (Some []) bs i.
Proof using.
  induction i as [| i IH]; [by left |].
  cbn [fstate_upto]. destruct IH as [[Hu Hv] | He]; [| by rewrite He; right].
  rewrite Hu Hv.
  destruct (uline_of (bs !!! i)) as [ws | ws | | ws npc]; [by left | | by left | by left].
  destruct (ralt_at cs i) as [k | sel | | | | | | | | | |];
    cbn [fsm]; try (by left); try (by right).
  destruct s as [b0 |]; [by left | by right].
Qed.

Lemma alt_cont_f_state ps cs s s' bs i :
  fstate_upto cs s bs i = fstate_upto cs s' bs i ->
  alt_cont_f ps cs s bs i = alt_cont_f ps cs s' bs i.
Proof using. intro H. by rewrite /alt_cont_f H. Qed.

Lemma cont_state_ne s s' l a : cont s l a <> cont s' l a -> a = RCRan.
Proof using. destruct a; intro H; try (exfalso; by apply H); reflexivity. Qed.

Lemma cont_rcran_some l b0 : cont (Some b0) l RCRan = b0 ++ u_prompt.
Proof using. reflexivity. Qed.

Lemma alt_cont_f_cat ps cs s bs i b0 :
  ralt_at cs i = RCRan -> fstate_upto cs s bs i = Some b0 ->
  exists D, alt_cont_f ps cs s bs i = b0 ++ D.
Proof using.
  intros Ha Hs. rewrite /alt_cont_f Hs Ha cont_rcran_some.
  eexists. by rewrite -app_assoc.
Qed.

Lemma alt_blk_f_infix ps cs s bs i b0 :
  ralt_at cs i = RCRan -> fstate_upto cs s bs i = Some b0 ->
  infixed b0 (alt_blk_f ps cs s bs i).
Proof using.
  intros Ha Hs.
  destruct (alt_cont_f_cat ps cs s bs i b0 Ha Hs) as (D & HD).
  rewrite /alt_blk_f HD.
  destruct (fdd_infix_cons wl_nl (bs !!! i) b0 D) as (C & E & HE).
  rewrite HE. apply infixed_here.
Qed.

Lemma alt_seq_f_split ps cs s bs q i :
  (i < q)%nat ->
  exists A B, alt_seq_f ps cs s bs q = A ++ alt_blk_f ps cs s bs i ++ B.
Proof using.
  induction q as [| q IH]; intro Hi; [lia |].
  rewrite alt_seq_f_S.
  destruct (decide (i = q)) as [-> | Hne].
  - exists (alt_seq_f ps cs s bs q), []. by rewrite app_nil_r.
  - destruct (IH ltac:(lia)) as (A & B & HE).
    exists A, (B ++ alt_blk_f ps cs s bs q). rewrite HE. by rewrite -!app_assoc.
Qed.

Lemma sessf_infix_blk ps cs s I i :
  (i < nlines I)%nat ->
  infixed (alt_blk_f ps cs s (bodies_of I) i) (sessf ps cs s I).
Proof using.
  intro Hi.
  destruct (alt_seq_f_split ps cs s (bodies_of I) (nlines I) i Hi)
    as (A & B & HE).
  rewrite /sessf HE. apply infixed_app_ctx, infixed_here.
Qed.

Lemma obs_wire_prefix (i : uart_id) (p seg : list mobs) :
  p `prefix_of` seg -> obs_wire i p `prefix_of` obs_wire i seg.
Proof using. intros [k ->]. rewrite obs_wire_app. by eexists. Qed.

Lemma alt_seq_f_cont_ext ps cs s s' bs q :
  (forall i, (i < q)%nat ->
     alt_cont_f ps cs s bs i = alt_cont_f ps cs s' bs i) ->
  alt_seq_f ps cs s bs q = alt_seq_f ps cs s' bs q.
Proof using.
  intro H. induction q as [| q IH]; [reflexivity |].
  rewrite !alt_seq_f_S IH; [| intros i Hi; apply H; lia].
  by rewrite /alt_blk_f (H q ltac:(lia)).
Qed.

(* the design's lemma: the boot-state witness may be taken from a finite
   list read off the segment's own wire *)
Lemma disc_seg_f'_canon (seg : list mobs) :
  (exists s, fstate_ok s /\ disc_seg_f' s seg)
  <-> (exists s, s ∈ scands seg /\ fstate_ok s /\ disc_seg_f' s seg).
Proof using.
  split; [| intros (s & _ & H); by exists s].
  intros (s & Hok & Hd).
  destruct s as [b0 |];
    [| exists None; split; [apply elem_of_list_here | by split]].
  destruct Hd as (Hseg & ps & cs & Hal & Hpt).
  destruct (decide (Exists (fun p =>
      Exists (fun i =>
        alt_cont_f ps cs (Some b0) (bodies_of (ins p)) i
        <> alt_cont_f ps cs (Some []) (bodies_of (ins p)) i)
        (List.seq 0 (nlines (ins p))))
      (in_pres seg))) as [HB | HB].
  - (* SOME checked transcript prints the boot content, so it is on the
       segment's wire *)
    apply Exists_exists in HB as (p & Hp & Hi).
    apply Exists_exists in Hi as (i & Hiin & Hne).
    apply elem_of_list_In, in_seq in Hiin.
    destruct (fstate_upto_vs_nil cs (Some b0) (bodies_of (ins p)) i)
      as [[Hu Hv] | He];
      [| by destruct (Hne (alt_cont_f_state ps cs _ _ _ i He))].
    assert (Ha : ralt_at cs i = RCRan).
    { apply (cont_state_ne (fstate_upto cs (Some b0) (bodies_of (ins p)) i)
                           (fstate_upto cs (Some []) (bodies_of (ins p)) i)
                           (uline_of (bodies_of (ins p) !!! i))).
      intro Hc. apply Hne. by rewrite /alt_cont_f Hc. }
    assert (Hinf : infixed b0 (obs_wire Uart0 seg)).
    { eapply infixed_prefix;
        [| exact (obs_wire_prefix Uart0 p seg
                    (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp))].
      eapply infixed_prefix; [| exact (proj2 (Hpt p Hp))].
      destruct (sessf_infix_blk ps cs (Some b0) (done_of (ins p)) i
                  ltac:(rewrite nlines_done; lia))
        as (A & B & HE).
      rewrite HE bodies_of_done. apply infixed_app_ctx.
      exact (alt_blk_f_infix ps cs (Some b0) (bodies_of (ins p)) i b0 Ha Hu). }
    exists (Some b0). split.
    { apply elem_of_list_further, elem_of_list_further, elem_of_list_fmap.
      exists b0. split; [reflexivity |]. by apply elem_of_substrings. }
    split; [exact Hok |]. split; [exact Hseg |]. by exists ps, cs.
  - (* NO checked transcript reads the boot state: the era is the one at
       [Some []] *)
    exists (Some []).
    split; [by apply elem_of_list_further, elem_of_list_here |].
    split; [by left |].
    split; [exact Hseg |]. exists ps, cs. split; [exact Hal |].
    intros p Hp. destruct (Hpt p Hp) as [Hpo Hpf]. split; [exact Hpo |].
    rewrite /disc_pt_f.
    assert (Heq : sessf ps cs (Some []) (done_of (ins p))
                  = sessf ps cs (Some b0) (done_of (ins p))).
    { rewrite /sessf bodies_of_done nlines_done. f_equal. f_equal.
      symmetry. apply (alt_seq_f_cont_ext ps cs (Some b0) (Some [])).
      intros i Hi. apply dec_stable. intro Hne. apply HB.
      apply Exists_exists. exists p. split; [exact Hp |].
      apply Exists_exists. exists i.
      split; [apply elem_of_list_In, in_seq; lia | exact Hne]. }
    rewrite Heq. exact Hpf.
Qed.

(* ====================================================================== *)
(*  8.  THE DECISION                                                       *)
(* ====================================================================== *)

(* [EchoDisc.disc_seg'_dec]'s search, at the three enumerators: the boot
   states off the wire, the resolutions off the lines, the prologues off
   [pro_canon].  NOTHING HERE IS MEANT TO RUN: the ledger cases on it. *)
Global Instance disc_seg_f'_ex_dec seg :
  Decision (exists s : fstate, fstate_ok s /\ disc_seg_f' s seg).
Proof using.
  destruct (decide (disc_seg_f seg)) as [Hd | Hd];
    [| right; intros (s & _ & Hs & _); by apply Hd].
  destruct (decide (Exists (fun s =>
      fstate_ok s /\
      Exists (fun cs =>
        Exists (fun ps => disc_pt_all_f ps cs s seg)
          (pro_cands (S (pro_idx_f cs (nlines_max (in_pres seg))))
                     (length seg)))
        (alts_cands (lines_of (ins seg))))
      (scands seg))) as [HE | HE].
  - left. apply Exists_exists in HE as (s & _ & Hok & HC).
    apply Exists_exists in HC as (cs & Hcs & HP).
    apply Exists_exists in HP as (ps & _ & Hall).
    exists s. split; [exact Hok |].
    eapply disc_seg_f'_intro; [exact Hd | | exact Hall].
    by apply alts_cands_alts_ok.
  - right. intro Hex. apply HE.
    apply disc_seg_f'_canon in Hex as (s & Hsin & Hok & Hd').
    apply Exists_exists. exists s. split; [exact Hsin |].
    split; [exact Hok |].
    destruct Hd' as (_ & ps & cs & Hal & Hall).
    apply Exists_exists. exists (cs_canon cs).
    split; [by apply alts_ok_cs_canon |].
    rewrite pro_idx_f_canon. apply Exists_exists.
    (* the deepest checked point bounds every round the transcript enters *)
    destruct (decide (in_pres seg = [])) as [Hz | Hz].
    { destruct (pro_cands_nonempty
                  (S (pro_idx_f cs (nlines_max (in_pres seg)))) (length seg))
        as [g Hg].
      exists g. split; [exact Hg |]. rewrite /disc_pt_all_f Hz. constructor. }
    destruct (nlines_max_mem (in_pres seg) Hz) as (pl & Hplin & Hpleq).
    destruct (Hall pl Hplin) as [[HFps Hltl] Hptl].
    assert (Hplp : pl `prefix_of` seg)
      by exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) pl Hplin).
    destruct (pro_canon (S (pro_idx_f cs (nlines_max (in_pres seg))))
                (length seg) ps HFps) as (ps0 & Hin0 & Hrd0 & Hag0).
    { intros r Hr. rewrite -Hpleq in Hr. split; [lia |].
      etrans; [apply (sessf_pro_len ps cs s (done_of (ins pl)) r);
               rewrite nlines_done; lia |].
      etrans; [apply prefix_length, Hptl |].
      etrans; [apply obs_wire_length |].
      exact (prefix_length _ _ Hplp). }
    exists ps0. split; [exact Hin0 |].
    apply disc_pt_all_f_canon.
    rewrite /disc_pt_all_f. apply Forall_forall. intros p Hp.
    destruct (Hall p Hp) as [[_ Hltp] Hptp].
    assert (Hidxle : (pro_idx_f cs (nlines (ins p))
                      <= pro_idx_f cs (nlines_max (in_pres seg)))%nat)
      by (apply pro_idx_f_mono, nlines_max_ge, Hp).
    assert (Hsame : sessf ps0 cs s (done_of (ins p))
                    = sessf ps cs s (done_of (ins p))).
    { apply sessf_ps_ext. intros r Hr. rewrite nlines_done in Hr.
      apply Hag0. lia. }
    split.
    + rewrite /pro_ok_f. split; [by eapply pro_cands_Forall | lia].
    + by rewrite /disc_pt_f Hsame.
Defined.

(* THE DELIVERABLE.  The file discipline is decidable, so
   [FileOut.file_led]'s taint counter reads [decide (disc_f h)] and
   [FileOut.v] takes no hypothesis. *)
(* OPAQUE ON PURPOSE, as [EchoDisc.disc_dec] is: the ledger's counter is
   [if decide (disc_f h) then 0 else 1] and every proof that touches it
   rewrites with a closure law.  A transparent instance would let
   [rewrite /file_led] iota-reduce the counter at a literal history and
   those rewrites would stop matching. *)
Global Instance disc_f_dec h : Decision (disc_f h).
Proof using. rewrite /disc_f. apply _. Qed.
