(* ===================================================================== *)
(*  UnionAdmDemo.v -- THE BOOT RELATION AFTER A SYNC, run on transcripts  *)
(*  (lane SY3-M; design: claude-notes/design/sync.md section 5).  PURE.   *)
(*                                                                        *)
(*  Four two-cycle histories, each [power on; cycle 0; power off; power  *)
(*  on; cycle 1], the conclusion [UnionOutPure.union_phi_sync_body] read at *)
(*  them:                                                                 *)
(*    - POSITIVE: [echo a > a.txt; echo b > a.txt; sync; <cut>; cat      *)
(*      a.txt] printing [b] is admitted ([demo_sync_cut]);               *)
(*    - NEGATIVE: the same printing [a] is refuted at EVERY choice of    *)
(*      boot states and records ([demo_sync_cut_neg]) -- the sync's      *)
(*      record is pinned by cycle 0's own wire (the second redirect      *)
(*      printed the bare prompt, so it ran; /sync printed the bare       *)
(*      prompt, so it ran), and no redirect line follows it;             *)
(*    - THE NO-SYNC CONTROL: [echo a > a.txt; echo b > a.txt; <cut>; cat *)
(*      a.txt] printing [a] IS admitted ([demo_nosync_cut]): without a   *)
(*      completed sync the boot may show any line's run -- the model    *)
(*      cannot see that [echo b]'s writes were committed, since [write]  *)
(*      carries no receipt (sync design section 6);                      *)
(*    - THE PAD DOES NOT COUNT: [sync] typed, /sync resolved to its run, *)
(*      but its prompt NOT on the wire at the cut -- [cat a.txt] printing *)
(*      [a] is admitted ([demo_sync_inflight]).                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import gmap bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel LineModelLinks.
Require Import FileState FileClass FileDisc.
Require Import UnionDisc UnionDiscDec UnionAdm UnionOutPure.
From stdpp Require Import list ssreflect.
Local Open Scope nat_scope.

Local Notation U := ulmG.

(* ===================================================================== *)
(*  1.  THE TRANSCRIPTS                                                   *)
(* ===================================================================== *)
Definition c_b : list (bv 8) := sb "b" ++ nl1.

(* cycle 0: two redirects, then [sync], every prompt on the wire *)
Definition I_s0 : list (bv 8) := b_ea ++ nl1 ++ b_eb ++ nl1 ++ b_sync ++ nl1.
Definition seg_s0 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (b_ea ++ nl1) ++ demo_out u_prompt
  ++ demo_typed (b_eb ++ nl1) ++ demo_out u_prompt
  ++ demo_typed (b_sync ++ nl1) ++ demo_out u_prompt.

(* ...the same without the sync *)
Definition I_n0 : list (bv 8) := b_ea ++ nl1 ++ b_eb ++ nl1.
Definition seg_n0 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (b_ea ++ nl1) ++ demo_out u_prompt
  ++ demo_typed (b_eb ++ nl1) ++ demo_out u_prompt.

(* ...and with the sync typed but its prompt not yet out *)
Definition seg_f0 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (b_ea ++ nl1) ++ demo_out u_prompt
  ++ demo_typed (b_eb ++ nl1) ++ demo_out u_prompt
  ++ demo_typed (b_sync ++ nl1).

(* cycle 1: [cat a.txt] printing [c] *)
Definition I_c1 : list (bv 8) := b_ca ++ nl1.
Definition seg_c1 (c : list (bv 8)) : list mobs :=
  demo_out u_prologue ++ demo_typed (b_ca ++ nl1) ++ demo_out (c ++ u_prompt).

Definition h_cut (seg0 seg1 : list mobs) : list mobs :=
  [ObsPowerOn] ++ seg0 ++ [ObsPowerOff; ObsPowerOn] ++ seg1.

Definition h_sb : list mobs := h_cut seg_s0 (seg_c1 c_b).
Definition h_sa : list mobs := h_cut seg_s0 (seg_c1 c_a).
Definition h_na : list mobs := h_cut seg_n0 (seg_c1 c_a).
Definition h_fa : list mobs := h_cut seg_f0 (seg_c1 c_a).

Lemma cyc_sb : cycles_of h_sb = [seg_s0; seg_c1 c_b].
Proof using. vm_compute. reflexivity. Qed.
Lemma cyc_sa : cycles_of h_sa = [seg_s0; seg_c1 c_a].
Proof using. vm_compute. reflexivity. Qed.
Lemma cyc_na : cycles_of h_na = [seg_n0; seg_c1 c_a].
Proof using. vm_compute. reflexivity. Qed.
Lemma cyc_fa : cycles_of h_fa = [seg_f0; seg_c1 c_a].
Proof using. vm_compute. reflexivity. Qed.

Lemma s0_ins : ins seg_s0 = I_s0.
Proof using. vm_compute. reflexivity. Qed.
Lemma n0_ins : ins seg_n0 = I_n0.
Proof using. vm_compute. reflexivity. Qed.
Lemma f0_ins : ins seg_f0 = I_s0.
Proof using. vm_compute. reflexivity. Qed.
Lemma c1_ins c : ins (seg_c1 c) = I_c1.
Proof using.
  rewrite /seg_c1 !ins_app.
  rewrite (_ : ins (demo_out u_prologue) = []); [| vm_compute; reflexivity].
  rewrite (_ : ins (demo_out (c ++ u_prompt)) = []);
    [| rewrite /ins /demo_out; induction (c ++ u_prompt) as [| x l IH]; [reflexivity |];
       cbn; exact IH].
  rewrite app_nil_r app_nil_l. vm_compute. reflexivity.
Qed.

Lemma s0_bodies : bodies_of I_s0 = [b_ea; b_eb; b_sync].
Proof using. vm_compute. reflexivity. Qed.
Lemma s0_nlines : nlines I_s0 = 3.
Proof using. rewrite /nlines s0_bodies. reflexivity. Qed.
Lemma s0_line1 : uline_of_u (bodies_of I_s0 !!! 1) = LEchoF ws_b txt_a.
Proof using. rewrite s0_bodies. vm_compute. reflexivity. Qed.
Lemma s0_line2 : uline_of_u (bodies_of I_s0 !!! 2) = LSync.
Proof using. rewrite s0_bodies. vm_compute. reflexivity. Qed.
Lemma s0_b1 : bodies_of I_s0 !!! 1 = b_eb.
Proof using. rewrite s0_bodies. reflexivity. Qed.
Lemma s0_b2 : bodies_of I_s0 !!! 2 = b_sync.
Proof using. rewrite s0_bodies. reflexivity. Qed.
Lemma c1_bodies : bodies_of I_c1 = [b_ca].
Proof using. vm_compute. reflexivity. Qed.

(* the honest resolutions, at small codes (every redirect run prints the
   bare prompt whatever its selection) *)
Definition cs_s0 : list nat :=
  [ualt_code (UR (RFRan [])); ualt_code (UR (RFRan [])); ualt_code (UR RSyncRan)].
Definition cs_n0 : list nat := [ualt_code (UR (RFRan [])); ualt_code (UR (RFRan []))].
Definition cs_c1 : list nat := [ualt_code (UR RCRan)].

Local Ltac dec_yes := apply (bool_decide_unpack _); vm_compute; exact I.

Lemma disc_in (I : list (bv 8)) :
  bool_decide (Forall (ubody_ok adm_u_g adm_s_on) (bodies_of I) /\ Forall ubyte (rest_of I)
               /\ S (length (rest_of I)) < line_max) = true ->
  lm_disc_input U I.
Proof using. intros H. exact (bool_decide_eq_true_1 _ H). Qed.

(* ===================================================================== *)
(*  2.  THE POSITIVE DEMO: sync, cut, cat prints what the sync fixed      *)
(* ===================================================================== *)

(* [echo b > a.txt] ran whole: the one selection that writes [b\n] *)
Definition cs_s0b : list nat :=
  [ualt_code (UR (RFRan [])); ualt_code (UR (RFRan (sel_all (echo_chunks ws_b))));
   ualt_code (UR RSyncRan)].
Definition st_b : fstate := {[txt_a := c_b]}.

Lemma s0b_good : lm_good_sync ∅ seg_s0 (Some (3, st_b)).
Proof using.
  exists [3; 0], cs_s0b. rewrite s0_ins. split_and!.
  - rewrite /lm_pro_ok. dec_yes.
  - split; [rewrite s0_nlines; reflexivity |].
    intros i Hi. rewrite s0_nlines in Hi.
    destruct i as [| [| [| i]]]; [dec_yes | dec_yes | dec_yes | lia].
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - vm_cast_no_check (eq_refl (Some (3, st_b))).
Qed.

Definition st_a : fstate := {[txt_a := c_a]}.

(* [cat a.txt] prints the file whole *)
Lemma c1_good_b : lm_good_sync st_b (seg_c1 c_b) None.
Proof using.
  exists [3; 0], cs_c1. rewrite c1_ins. split_and!.
  - rewrite /lm_pro_ok. dec_yes.
  - split; [reflexivity |].
    intros i Hi. rewrite (_ : nlines I_c1 = 1) in Hi; [| reflexivity].
    destruct i as [| i]; [dec_yes | lia].
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - vm_compute. reflexivity.
Qed.

Lemma c1_good_a : lm_good_sync st_a (seg_c1 c_a) None.
Proof using.
  exists [3; 0], cs_c1. rewrite c1_ins. split_and!.
  - rewrite /lm_pro_ok. dec_yes.
  - split; [reflexivity |].
    intros i Hi. rewrite (_ : nlines I_c1 = 1) in Hi; [| reflexivity].
    destruct i as [| i]; [dec_yes | lia].
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - vm_compute. reflexivity.
Qed.

Theorem demo_sync_cut :
  union_phi_sync_body h_sb [(∅, Some (3, st_b)); (st_b, None)].
Proof using.
  rewrite /union_phi_sync_body.
  assert (Hr : ulast_before h_sb (snd <$> [(∅, Some (3, st_b)); (st_b, None)]) 1 = (3, st_b))
    by vm_cast_no_check (eq_refl (3, st_b)).
  split_and!.
  - by rewrite cyc_sb.
  - intros w Hw. injection Hw as <-. reflexivity.
  - intros k w Hw. destruct k as [| k]; [| discriminate Hw].
    injection Hw as <-. rewrite Hr. apply uadm_self.
  - rewrite cyc_sb. constructor; [exact s0b_good |].
    constructor; [exact c1_good_b | constructor].
Qed.

Corollary demo_sync_cut_phi : union_phi_sync h_sb.
Proof using.
  apply (union_phi_sync_of_body h_sb [(∅, Some (3, st_b)); (st_b, None)]).
  intros _. exact demo_sync_cut.
Qed.

(* ===================================================================== *)
(*  3.  THE NEGATIVE DEMO: sync, cut, cat prints [a] -- refuted           *)
(* ===================================================================== *)

(* the sync line's bare prompt is /sync's run *)
Lemma sy_run (s : fstate) (a : ualt) (X : list (bv 8)) :
  uok adm_u_g s LSync a ->
  ucont s LSync a ++ (if upanic a then X else []) = u_prompt -> a = UR RSyncRan.
Proof using.
  intros Hok H. destruct (demo_sync_only s a Hok) as [-> | [-> | [-> | ->]]];
    [reflexivity | ..]; exfalso; cbn [ucont cont upanic ralt_panic] in H;
    apply (f_equal length) in H;
    unfold alt_execsync, alt_oom in H;
    rewrite ?app_nil_r ?length_app ?lb_panic_len ?wl_line_length ?ll_prompt_len in H;
    simpl in H; lia.
Qed.

(* a round of a redirect or of [sync] never ends coverage *)
Lemma sy_noterm s l a :
  (exists ws N, l = LEchoF ws N) \/ l = LSync -> uok adm_u_g s l a -> uterm a = false.
Proof using.
  intros [(ws & N & ->) | ->]; destruct a; cbn [uok]; first [contradiction | reflexivity].
Qed.

Lemma sy_noterm_lm s b a :
  (exists ws N, uline_of_u b = LEchoF ws N) \/ uline_of_u b = LSync ->
  lm_ok U s (lm_of U b) a -> lm_term U a = false.
Proof using.
  intros Hl Hok. change (uok adm_u_g s (uline_of_u b) a) in Hok. change (uterm a = false).
  destruct Hl as [(ws & N & Hb) | Hb]; rewrite Hb in Hok;
    [exact (sy_noterm s _ a (or_introl (ex_intro _ ws (ex_intro _ N eq_refl))) Hok)
    | exact (sy_noterm s _ a (or_intror eq_refl) Hok)].
Qed.

(* CYCLE 0 PINS ITS RECORD: under any resolution below its wire, the
   last completed sync is round 2, at a state whose [a.txt] holds a run
   of [echo b] *)
Lemma s0_rec (o : option srec) :
  lm_good_sync ∅ seg_s0 o ->
  exists T sel, o = Some (3, T) /\ sel_ok (echo_chunks ws_b) sel
                /\ T !! txt_a = Some (subseq (echo_chunks ws_b) sel) /\ fstate_ok T.
Proof using.
  intros (ps & cs & Hok & Hcs & Hpre & ->).
  rewrite s0_ins in Hok Hcs Hpre |- *.
  assert (Hw : obs_wire Uart0 seg_s0 = lm_sess U [3; 0] cs_s0 ∅ I_s0)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hok0 : lm_alts_ok U ∅ I_s0 cs_s0).
  { split; [rewrite s0_nlines; reflexivity |].
    intros i Hi. rewrite s0_nlines in Hi.
    destruct i as [| [| [| i]]]; [dec_yes | dec_yes | dec_yes | lia]. }
  assert (Hpro0 : lm_pro_ok U [3; 0] cs_s0 (nlines I_s0)) by (rewrite /lm_pro_ok; dec_yes).
  assert (Hlines : forall i, i < 3 -> (exists ws N, uline_of_u (bodies_of I_s0 !!! i) = LEchoF ws N)
                                      \/ uline_of_u (bodies_of I_s0 !!! i) = LSync).
  { intros i Hi. rewrite s0_bodies.
    destruct i as [| [| [| i]]]; [left; do 2 eexists; vm_compute; reflexivity
                                  | left; do 2 eexists; vm_compute; reflexivity
                                  | right; vm_compute; reflexivity | lia]. }
  assert (Hd4 : forall i, i < nlines I_s0 -> lm_term U (lm_at U cs i) = true ->
                S i = nlines I_s0 /\ rest_of I_s0 = []).
  { intros i Hi Ht. exfalso. rewrite s0_nlines in Hi.
    pose proof (proj2 Hcs i ltac:(rewrite s0_nlines; lia)) as Hi'.
    rewrite (sy_noterm_lm _ _ _ (Hlines i Hi) Hi') in Ht. discriminate Ht. }
  assert (Hnm : forall i, i < nlines I_s0 ->
            (exists c, lm_ok U (lm_upto U cs_s0 ∅ (bodies_of I_s0) i)
                         (lm_of U (bodies_of I_s0 !!! i)) c /\ lm_term U c = true) ->
            ~ lm_merge U (lm_of U (bodies_of I_s0 !!! i))
                (lm_cont U (lm_upto U cs_s0 ∅ (bodies_of I_s0) i)
                   (lm_of U (bodies_of I_s0 !!! i)) (lm_at U cs_s0 i))).
  { intros i Hi (c & Hc & Ht). exfalso. rewrite s0_nlines in Hi.
    rewrite (sy_noterm_lm _ _ _ (Hlines i Hi) Hc) in Ht. discriminate Ht. }
  assert (HT : lm_sess U [3; 0] cs_s0 ∅ I_s0 `prefix_of` lm_sess U ps cs ∅ I_s0)
    by (rewrite -Hw; exact Hpre).
  destruct (lm_sess_prefix_det U ulmG_laws ps [3; 0] cs cs_s0 ∅ ∅ I_s0 I_s0
              (proj1 Hok) Hpro0 Hcs Hok0 (lm_pro_pin_of_ok U ps cs I_s0 Hok)
              (disc_in I_s0 ltac:(vm_compute; reflexivity))
              (disc_in I_s0 ltac:(vm_compute; reflexivity))
              fstate_ok_empty fstate_ok_empty Hd4 Hnm HT)
    as (_ & _ & Heq & Hcnt).
  (* round 1, [echo b > a.txt], printed the bare prompt: it RAN *)
  assert (Hok1 : uok adm_u_g (lm_upto U cs ∅ (bodies_of I_s0) 1) (LEchoF ws_b txt_a)
                   (lm_at U cs 1)).
  { pose proof (proj2 Hcs 1 ltac:(rewrite s0_nlines; lia)) as H.
    rewrite s0_b1 (ab_line1 : lm_of U b_eb = _) in H. exact H. }
  pose proof (Hcnt 1 ltac:(rewrite s0_nlines; lia)) as H1.
  rewrite (_ : lm_cont_at U [3; 0] cs_s0 ∅ (bodies_of I_s0) 1 = u_prompt) in H1;
    [| vm_compute; reflexivity].
  assert (Hc1 : lm_cont_at U ps cs ∅ (bodies_of I_s0) 1
                = ucont (lm_upto U cs ∅ (bodies_of I_s0) 1) (LEchoF ws_b txt_a) (lm_at U cs 1)
                  ++ (if upanic (lm_at U cs 1)
                      then pro_of (pro_from (S (lm_pro_idx U cs 1)) ps) else [])).
  { rewrite /lm_cont_at s0_b1. cbn [ulmG ulm lm_of lm_cont lm_panic]. rewrite ab_line1.
    reflexivity. }
  rewrite Hc1 in H1.
  destruct (ab_run _ _ _ _ _ Hok1 (eq_sym H1)) as (sel & Hr1 & Hsel).
  (* round 2, [sync], printed the bare prompt: /sync RAN *)
  assert (Hok2 : uok adm_u_g (lm_upto U cs ∅ (bodies_of I_s0) 2) LSync (lm_at U cs 2)).
  { pose proof (proj2 Hcs 2 ltac:(rewrite s0_nlines; lia)) as H.
    rewrite s0_b2 (proj1 demo_sync_parse : lm_of U b_sync = _) in H. exact H. }
  pose proof (Hcnt 2 ltac:(rewrite s0_nlines; lia)) as H2.
  rewrite (_ : lm_cont_at U [3; 0] cs_s0 ∅ (bodies_of I_s0) 2 = u_prompt) in H2;
    [| vm_compute; reflexivity].
  assert (Hc2 : lm_cont_at U ps cs ∅ (bodies_of I_s0) 2
                = ucont (lm_upto U cs ∅ (bodies_of I_s0) 2) LSync (lm_at U cs 2)
                  ++ (if upanic (lm_at U cs 2)
                      then pro_of (pro_from (S (lm_pro_idx U cs 2)) ps) else [])).
  { rewrite /lm_cont_at s0_b2. cbn [ulmG ulm lm_of lm_cont lm_panic].
    rewrite (proj1 demo_sync_parse).
    reflexivity. }
  rewrite Hc2 in H2.
  pose proof (sy_run _ _ _ Hok2 (eq_sym H2)) as Hr2.
  (* the state the sync found *)
  set (T := (lm_upto U cs ∅ (bodies_of I_s0) 2 : fstate)).
  assert (HT2 : T !! txt_a = Some (subseq (echo_chunks ws_b) sel)).
  { rewrite /T. change (lm_upto U cs ∅ (bodies_of I_s0) 2)
      with (lm_step U (lm_upto U cs ∅ (bodies_of I_s0) 1)
              (lm_of U (bodies_of I_s0 !!! 1)) (lm_at U cs 1)).
    rewrite Hr1 s0_b1. cbn [ulmG ulm lm_of lm_step ustep]. rewrite ab_line1. cbn [fsm].
    apply lookup_insert_eq. }
  assert (HTok : fstate_ok T).
  { apply (lm_upto_st_ok U ulmG_laws cs ∅ (bodies_of I_s0) 2 fstate_ok_empty).
    - intros i Hi. apply (lml_body_line ulmG_laws).
      apply (lm_disc_input_body U I_s0 i _ (disc_in I_s0 ltac:(vm_compute; reflexivity))).
      rewrite list_lookup_lookup_total_lt; [reflexivity | rewrite s0_bodies /=; lia].
    - intros i Hi. apply (proj2 Hcs i). rewrite s0_nlines. lia. }
  (* the sync's round is completed: its block is on the wire *)
  assert (Hat2 : usync_at ps cs ∅ I_s0 (obs_wire Uart0 seg_s0) 2 = Some (3, T)).
  { rewrite /usync_at decide_True; [reflexivity |].
    split_and!; [exact s0_line2 | exact Hr2 |].
    rewrite Hw Heq /lm_sess s0_nlines. rewrite app_assoc. by apply prefix_app_r. }
  exists T, sel. split_and!; [| exact Hsel | exact HT2 | exact HTok].
  rewrite /usync_last /usyncs s0_nlines.
  change (seq 0 3) with ([0; 1] ++ [2]).
  rewrite omap_app. cbn [omap list_omap]. rewrite Hat2 last_snoc. reflexivity.
Qed.

(* WHAT [cat a.txt] PRINTS at a state whose [a.txt] holds a run of [echo
   b]: never [a] *)
Lemma c1_neg (s : fstate) (sel : list nat) (o : option srec) :
  fstate_ok s -> sel_ok (echo_chunks ws_b) sel ->
  s !! txt_a = Some (subseq (echo_chunks ws_b) sel) ->
  ~ lm_good_sync s (seg_c1 c_a) o.
Proof using.
  intros Hs Hsel Hst (ps & cs & Hok & Hcs & Hpre & _).
  rewrite c1_ins in Hok Hcs Hpre.
  assert (Hw : obs_wire Uart0 (seg_c1 c_a)
               = lm_sess U [3; 0] [] ∅ b_ca ++ wl_nl :: (c_a ++ u_prompt))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HJ0 : nlines b_ca = 0) by (vm_compute; reflexivity).
  assert (HT : lm_sess U [3; 0] [] ∅ b_ca `prefix_of` lm_sess U ps cs s I_c1).
  { etrans; [| exact Hpre]. rewrite Hw. by eexists. }
  destruct (lm_sess_prefix_det U ulmG_laws ps [3; 0] cs [] s ∅ b_ca I_c1
              (proj1 Hok) ltac:(rewrite /lm_pro_ok; dec_yes) Hcs
              (lm_alts_ok_nil U ∅ b_ca HJ0) (lm_pro_pin_of_ok U ps cs I_c1 Hok)
              (disc_in I_c1 ltac:(vm_compute; reflexivity))
              (disc_in b_ca ltac:(vm_compute; reflexivity))
              Hs fstate_ok_empty
              ltac:(intros i Hi; rewrite HJ0 in Hi; lia)
              ltac:(intros i Hi; rewrite HJ0 in Hi; lia) HT)
    as (_ & _ & Heq & _).
  rewrite Hw Heq in Hpre.
  rewrite /I_c1 /nl1 (lm_sess_snoc_nl U ps cs s b_ca) in Hpre.
  apply wl_prefix_app_cancel in Hpre. apply prefix_cons_inv_2 in Hpre.
  rewrite (_ : bodies_of b_ca ++ [rest_of b_ca] = bodies_of (b_ca ++ [wl_nl])) in Hpre;
    [| vm_compute; reflexivity].
  rewrite HJ0 in Hpre.
  assert (Hg : (c_a ++ u_prompt) !! 0 = Some (Z_to_bv 8 97%Z)) by (vm_compute; reflexivity).
  pose proof (lb_prefix_lookup _ _ _ 0 Hpre Hg) as Hh.
  assert (Hok0 : uok adm_u_g s (LCat txt_a) (lm_at U cs 0)).
  { pose proof (proj2 Hcs 0 ltac:(rewrite (_ : nlines I_c1 = 1); [lia | reflexivity])) as H.
    cbn [lm_upto] in H. rewrite c1_bodies in H. change ([b_ca] !!! 0) with b_ca in H.
    cbn [ulmG ulm lm_of lm_ok] in H. rewrite ca_line in H. exact H. }
  assert (Hc0 : lm_cont_at U ps cs s (bodies_of (b_ca ++ [wl_nl])) 0
                = ucont s (LCat txt_a) (lm_at U cs 0)
                  ++ (if upanic (lm_at U cs 0)
                      then pro_of (pro_from (S (lm_pro_idx U cs 0)) ps) else [])).
  { rewrite /lm_cont_at. cbn [lm_upto].
    rewrite (_ : bodies_of (b_ca ++ [wl_nl]) = [b_ca]); [| vm_compute; reflexivity].
    change ([b_ca] !!! 0) with b_ca.
    cbn [ulmG ulm lm_of lm_cont lm_panic]. rewrite ca_line. reflexivity. }
  rewrite Hc0 in Hh.
  destruct (lm_at U cs 0) as [r | x | x | u]; cbn [uok] in Hok0; try contradiction.
  cbn [ucont upanic] in Hh.
  exact (ab_cat_head _ r sel _ _ Hok0 Hsel Hst Hh ltac:(vm_compute; reflexivity)).
Qed.

Theorem demo_sync_cut_neg : forall W, ~ union_phi_sync_body h_sa W.
Proof using.
  intros W (Hlen & H0 & Hadm & HF).
  rewrite cyc_sa in Hlen HF.
  destruct W as [| w0 [| w1 [| w2 W]]]; cbn [length] in Hlen; try discriminate Hlen.
  apply Forall2_cons_1 in HF as [Hg0 HF]. apply Forall2_cons_1 in HF as [Hg1 _].
  pose proof (H0 w0 eq_refl) as Hw0.
  pose proof (Hadm 0 w1 eq_refl) as Hb.
  rewrite Hw0 in Hg0.
  destruct (s0_rec _ Hg0) as (T & sel & Hr & Hsel & HT & HTok).
  assert (Hlast : ulast_before h_sa (snd <$> [w0; w1]) 1 = (3, T)).
  { rewrite /ulast_before cyc_sa. cbn [fmap list_fmap take ulast_from].
    rewrite Hr. reflexivity. }
  assert (Hdrop : drop 3 (ulines_before h_sa 1) = []).
  { rewrite /ulines_before cyc_sa. cbn [take fmap list_fmap concat].
    rewrite app_nil_r /ulines_cyc s0_ins /ulines_in s0_bodies. reflexivity. }
  rewrite Hlast in Hb.
  (* the boot state IS the state at the sync: no redirect line follows it *)
  assert (Heq : w1.1 = T).
  { apply map_eq. intros N. destruct (Hb N) as [H | (ws & sel' & Hin & _)]; [exact H |].
    cbn [fst] in Hin. rewrite Hdrop in Hin. by apply elem_of_nil in Hin. }
  apply (c1_neg w1.1 sel w1.2); [by rewrite Heq | exact Hsel | by rewrite Heq | exact Hg1].
Qed.

(* ===================================================================== *)
(*  4.  THE CONTROLS: no sync, and a sync whose prompt is not out         *)
(* ===================================================================== *)

Lemma n0_good : lm_good_sync ∅ seg_n0 None.
Proof using.
  exists [3; 0], cs_n0. rewrite n0_ins. split_and!.
  - rewrite /lm_pro_ok. dec_yes.
  - split; [vm_compute; reflexivity |].
    intros i Hi. rewrite (_ : nlines I_n0 = 2) in Hi; [| vm_compute; reflexivity].
    destruct i as [| [| i]]; [dec_yes | dec_yes | lia].
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - vm_compute. reflexivity.
Qed.

(* the first redirect's run is admissible at no sync *)
Lemma adm_a0 (h : list mobs) :
  LEchoF ws_a txt_a ∈ ulines_before h 1 -> uadm (ulines_before h 1) srec0 st_a.
Proof using.
  intros Hin N. destruct (decide (N = txt_a)) as [-> | Hne].
  - right. exists ws_a, (sel_all (echo_chunks ws_a)).
    split_and!; [by rewrite drop_0 | apply sel_all_ok |].
    rewrite /st_a lookup_singleton_eq. vm_compute. reflexivity.
  - left. rewrite /st_a lookup_singleton_ne; [| done]. by rewrite lookup_empty.
Qed.

Theorem demo_nosync_cut :
  union_phi_sync_body h_na [(∅, None); (st_a, None)].
Proof using.
  rewrite /union_phi_sync_body.
  split_and!.
  - by rewrite cyc_na.
  - intros w Hw. injection Hw as <-. reflexivity.
  - intros k w Hw. destruct k as [| k]; [| discriminate Hw].
    injection Hw as <-.
    rewrite (_ : ulast_before h_na _ 1 = srec0); [| vm_compute; reflexivity].
    apply adm_a0.
    rewrite (_ : ulines_before h_na 1 = [LEchoF ws_a txt_a; LEchoF ws_b txt_a]);
      [| vm_compute; reflexivity].
    apply list_elem_of_here.
  - rewrite cyc_na. constructor; [exact n0_good |].
    constructor; [exact c1_good_a | constructor].
Qed.

(* the sync line typed and resolved to /sync's run, its prompt not on the
   wire: no record, and the boot may show the first redirect's run *)
Lemma f0_good : lm_good_sync ∅ seg_f0 None.
Proof using.
  exists [3; 0], cs_s0. rewrite f0_ins. split_and!.
  - rewrite /lm_pro_ok. dec_yes.
  - split; [rewrite s0_nlines; reflexivity |].
    intros i Hi. rewrite s0_nlines in Hi.
    destruct i as [| [| [| i]]]; [dec_yes | dec_yes | dec_yes | lia].
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - vm_compute. reflexivity.
Qed.

Theorem demo_sync_inflight :
  union_phi_sync_body h_fa [(∅, None); (st_a, None)].
Proof using.
  rewrite /union_phi_sync_body.
  split_and!.
  - by rewrite cyc_fa.
  - intros w Hw. injection Hw as <-. reflexivity.
  - intros k w Hw. destruct k as [| k]; [| discriminate Hw].
    injection Hw as <-.
    rewrite (_ : ulast_before h_fa _ 1 = srec0); [| vm_compute; reflexivity].
    apply adm_a0.
    rewrite (_ : ulines_before h_fa 1 = [LEchoF ws_a txt_a; LEchoF ws_b txt_a; LSync]);
      [| vm_compute; reflexivity].
    apply list_elem_of_here.
  - rewrite cyc_fa. constructor; [exact f0_good |].
    constructor; [exact c1_good_a | constructor].
Qed.

(* ===================================================================== *)
(*  5.  THE NEGATIVE DEMO'S TRACE IS DISCIPLINED (sync SY3-A4): so the    *)
(*      top theorem's conclusion ([UnionOutPure.union_phi_sync]) speaks  *)
(*      of it, and refutes it ([UInitUnion.union_sync_cut_neg])          *)
(* ===================================================================== *)

(* a line with no terminal alternative: neither a pipeline nor [seccomp] *)
Definition uplain (l : uline) : Prop :=
  match l with LPipe _ _ | LSecc _ => False | _ => True end.

Lemma d4_plain (cs : list nat) (s : fstate) (I : list (bv 8)) :
  (forall i, i < nlines I -> uplain (uline_of_u (bodies_of I !!! i))) ->
  lm_d4 U cs s I.
Proof using.
  intros Hp i Hi (c & Hok & Ht). specialize (Hp i Hi). revert Hp Hok Ht.
  cbn [ulmG ulm lm_ok lm_of lm_term].
  destruct (uline_of_u (bodies_of I !!! i)); intros Hp; try contradiction;
    destruct c; cbn [uok uterm]; intros Hok Ht; try contradiction; discriminate.
Qed.

Local Instance demo_pro_ok_dec ps cs q : Decision (lm_pro_ok U ps cs q).
Proof. rewrite /lm_pro_ok. apply _. Defined.
Local Instance demo_disc_pt_dec ps cs (s : fstate) p : Decision (lm_disc_pt U ps cs s p).
Proof. rewrite /lm_disc_pt. apply _. Defined.

Lemma st_a_ok : fstate_ok st_a.
Proof using.
  rewrite /fstate_ok /st_a map_Forall_singleton. split; [dec_yes |].
  right. exists (sb "a"). split; [dec_yes | reflexivity].
Qed.

Lemma sa_disc : lm_disc U h_sa.
Proof using.
  rewrite /lm_disc cyc_sa. constructor; [| constructor; [| constructor]].
  - exists ∅. split; [exact fstate_ok_empty |].
    rewrite /lm_disc_seg' s0_ins.
    split; [apply disc_in; vm_compute; reflexivity |].
    exists [3; 0], cs_s0b. split_and!.
    + split; [rewrite s0_nlines; reflexivity |].
      intros i Hi. rewrite s0_nlines in Hi.
      destruct i as [| [| [| i]]]; [dec_yes | dec_yes | dec_yes | lia].
    + apply d4_plain. intros i Hi. rewrite s0_nlines in Hi.
      destruct i as [| [| [| i]]]; [vm_compute; exact I | vm_compute; exact I
                                   | vm_compute; exact I | lia].
    + apply Forall_forall. dec_yes.
  - exists st_a. split; [exact st_a_ok |].
    rewrite /lm_disc_seg' c1_ins.
    split; [apply disc_in; vm_compute; reflexivity |].
    exists [3; 0], cs_c1. split_and!.
    + split; [reflexivity |].
      intros i Hi. rewrite (_ : nlines I_c1 = 1) in Hi; [| reflexivity].
      destruct i as [| i]; [dec_yes | lia].
    + apply d4_plain. intros i Hi. rewrite (_ : nlines I_c1 = 1) in Hi; [| reflexivity].
      destruct i as [| i]; [vm_compute; exact I | lia].
    + apply Forall_forall. dec_yes.
Qed.
