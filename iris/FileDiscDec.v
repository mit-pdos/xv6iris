(* FileDiscDec.v -- THE FILE MODEL'S FINITE ENUMERATORS, which the union
   discipline's decider ([UnionDecU]) searches over.

   Design of record: claude-notes/design/app-file.md section 4.3a (lane
   FILE-DEC).  A round's code decodes to a [FileDisc.ralt], and [RFRan sel]
   carries a chunk subset through a countable encoding, so the codes a line
   admits are not an initial segment of the naturals.  They ARE finite per
   line: [ralt_ok] pins [sel] to [FileState.sel_ok (echo_chunks ws)], a
   strictly increasing list over [seq 0 (length (echo_chunks ws))], of which
   there are 2^n.  [sel_cands] enumerates those and [ralt_cands] the codes;
   the enumerator lists only CANONICAL codes [ralt_enc a], and a witness is
   canonicalised to those because every consumer reads a code only through
   [ralt_dec].  The content and the state are decidable ([fcont_ok_dec],
   [fstate_ok_dec]).

   The file application's own decider over its one-name boot states went
   with that application; the union's boot-state search is [UnionDecU]'s. *)
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
Proof using. rewrite /fstate_ok. apply _. Defined.

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
  (* the echo application's four but its silent index 2 *)
  | LEcho _ => [REcho 0%nat; REcho 1%nat; REcho 3%nat; ROom]
  | LEchoF _ _ => [RFExec; RFOpenU; RFOpenM; RFFork; ROom]
  | LCat _ => [RCRan; RCNoOpen; RCExec; RCFork; ROom]
  (* the DEAD arm: [FileDisc.ralt_ok] gives [LPipe] exactly [LCat]'s five *)
  | LPipe _ _ => [RCRan; RCNoOpen; RCExec; RCFork; ROom]
  | LSecc _ => [RCFork; RSExec; ROom]
  end.

Definition ralt_cands (l : uline) : list nat :=
  (ralt_enc <$> ralt_fix_cands l)
  ++ match l with
     | LEchoF ws _ =>
         (fun sel => ralt_enc (RFRan sel))
           <$> sel_cands (length (echo_chunks ws))
     | _ => []
     end.

Lemma ralt_fix_cands_ok l : Forall (ralt_ok l) (ralt_fix_cands l).
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [ralt_fix_cands].
  - repeat (constructor; [cbn [ralt_ok]; first [exact I | split; lia] |]).
    constructor.
  - repeat (constructor; [exact I |]). constructor.
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
  - destruct l as [ws | ws N | N | ws npc | ws]; try (by apply elem_of_nil in Hin).
    apply elem_of_list_fmap in Hin as (sel & -> & Hsel).
    rewrite ralt_dec_enc. cbn [ralt_ok].
    by apply (sel_ok_cands (echo_chunks ws) sel).
Qed.

Lemma ralt_cands_canon l c :
  ralt_ok l (ralt_dec c) -> ralt_enc (ralt_dec c) ∈ ralt_cands l.
Proof using.
  intro H. rewrite /ralt_cands elem_of_app.
  destruct l as [ws | ws N | N | ws npc | ws];
    destruct (ralt_dec c) as [k | sel | | | | | | | | | |];
    cbn [ralt_ok] in H; try done.
  - left. apply elem_of_list_fmap. exists (REcho k). split; [reflexivity |].
    assert (Hk : k = 0%nat \/ k = 1%nat \/ k = 3%nat) by lia.
    cbn [ralt_fix_cands]. destruct Hk as [-> | [-> | ->]]; fdd_elem.
  - left. apply elem_of_list_fmap. exists ROom. split; [reflexivity |]. fdd_elem.
  - right. apply elem_of_list_fmap. exists sel. split; [reflexivity |].
    by apply sel_ok_cands.
  - left. apply elem_of_list_fmap. exists RFExec. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RFOpenU. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RFOpenM. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RFFork. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists ROom. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCRan. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCNoOpen. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCExec. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCFork. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists ROom. split; [reflexivity |]. fdd_elem.
  (* ...and the dead [LPipe] arm, which is [LCat]'s five verbatim *)
  - left. apply elem_of_list_fmap. exists RCRan. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCNoOpen. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCExec. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RCFork. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists ROom. split; [reflexivity |]. fdd_elem.
  (* ...and the [seccomp] line's three (the shell's own) *)
  - left. apply elem_of_list_fmap. exists RCFork. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists RSExec. split; [reflexivity |]. fdd_elem.
  - left. apply elem_of_list_fmap. exists ROom. split; [reflexivity |]. fdd_elem.
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
(*  7.  TWO FACTS THE UNION'S DECIDER READS                                *)
(*                                                                        *)
(*  The file application's own decider ([disc_f_dec], over the one-name   *)
(*  boot states) went with that application (union cut C9h, filenames.md  *)
(*  cut W1); the union decides its discipline in [UnionDecU].              *)
(* ====================================================================== *)

Lemma cont_state_ne s s' l a : cont s l a <> cont s' l a -> a = RCRan.
Proof using. destruct a; intro H; try (exfalso; by apply H); reflexivity. Qed.

Lemma obs_wire_prefix (i : uart_id) (p seg : list mobs) :
  p `prefix_of` seg -> obs_wire i p `prefix_of` obs_wire i seg.
Proof using. intros [k ->]. rewrite obs_wire_app. by eexists. Qed.
