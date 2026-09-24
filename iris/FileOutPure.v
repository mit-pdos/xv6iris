(* FileOutPure.v -- THE FILE APPLICATION'S PURE RESIDUE.

   The console claim's stage machine is [GenOutPure]'s and its pure
   history layer [GenOutHist]'s, at [FileDisc.file_lm] (app-both M3b: the
   file's claim IS [GenOut.gcl]).  What stays here is what is the FILE's own
   and read outside the claim:

   - the bytes of a disciplined input and the refutation of the control
     bytes ([disc_byte_ok_f]), section 1;
   - the discipline's closure laws at the whole history ([disc_f_out],
     [disc_f_in], [disc_f_power], [disc_f_other]), which the ledger's steps
     are stated at, section 1b;
   - the writer's stream in the file's words ([pending_at_f],
     [proc_before_f], [proc_stream_f] at an [option fstate] read through
     [f0_st]), which the link families and cat's round compute on, and the
     choice list's range ([alts_pre]) with its pad at the file's own default
     alternative ([alts_pad]), sections 2 and 6b;
   - the output claim's step at an event that writes nothing
     ([good_out_f_step]), and the conclusion's body with its four steps
     ([file_phi_body]), which the ledger spends, sections 9-13. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import FileDisc.
(* as in EchoDisc / EchoOutPure: a pure file does not inherit ssreflect's
   [rewrite] from the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* the history of an entry of E *)
Local Notation ehist := (@fst (list mobs) (bv 8)).

(* ====================================================================== *)
(*  1.  THE BYTES OF A DISCIPLINED FILE-APPLICATION INPUT                  *)
(* ====================================================================== *)

(* every byte of a disciplined input is a body byte, a '>' or the newline --
   [EchoDisc.disc_input_byte] with [fbody_byte] where [wl_body_byte] was *)
Lemma disc_input_f_byte (I : list (bv 8)) (b : bv 8) :
  disc_input_f I -> b ∈ I -> fbody_byte b \/ b = wl_nl.
Proof using.
  intros Hd Hin. pose proof Hd as (Hb & Hr & _).
  rewrite (wl_cut_join I) in Hin.
  apply elem_of_app in Hin as [Hin | Hin].
  - destruct (join_elem_of (bodies_of I) b Hin) as [-> | (l & Hl & Hbl)];
      [by right | left].
    apply elem_of_list_lookup in Hl as [k Hk].
    pose proof (fbody_ok_bytes l (disc_input_f_body I k l Hd Hk)) as Hfb.
    exact (proj1 (Forall_forall _ _) Hfb b Hbl).
  - left. exact (proj1 (Forall_forall _ _) Hr b Hin).
Qed.

Lemma wl_gt_val : bv_unsigned wl_gt = 62%Z.
Proof using. by vm_compute. Qed.

(* [EchoOutPure.echo_byte_ne] is [Local]; this is that step, which is what
   turns every refutation below into one [lia] against the byte reading *)
Local Lemma fop_byte_ne (c : bv 8) (z : Z) :
  bv_unsigned c <> z ->
  bv_unsigned (mword_of_int z : mword 8) = z ->
  eq_vec (c : mword 8) (mword_of_int z : mword 8) = false.
Proof using.
  intros Hne Hz. apply eq_vec_false_iff. intro Hq.
  apply (f_equal bv_unsigned) in Hq. rewrite Hz in Hq. exact (Hne Hq).
Qed.

Lemma disc_input_f_byte_val (I : list (bv 8)) (b : bv 8) :
  disc_input_f I -> b ∈ I ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z \/ bv_unsigned b = 62%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof using.
  intros Hd Hin. destruct (disc_input_f_byte I b Hd Hin) as [[[Ha | ->] | ->] | ->].
  - destruct Ha as [H | [H | H]];
      [ right; right; right; by left
      | right; right; right; right; by left
      | right; right; right; right; by right ].
  - right. left. exact wl_sp_val.
  - right. right. left. exact wl_gt_val.
  - left. exact wl_nl_val.
Qed.

(* A DISCIPLINED INPUT HOLDS NO '\r', NO ERASE BYTE AND NO ^D, exactly as
   [EchoOutPure.disc_byte_ok] says for the echo application: the third
   clause refutes the read path's SWALLOW arm and the second the gap
   clause's erase disjunct. *)
Lemma disc_byte_ok_f (I : list (bv 8)) (c : bv 8) :
  disc_input_f I -> c ∈ I ->
  c <> (mword_of_int 13 : mword 8) /\ cons_erase c = false
  /\ bv_unsigned c <> 4%Z.
Proof using.
  intros Hd Hc. pose proof (disc_input_f_byte_val I c Hd Hc) as Hv.
  split_and!.
  - intro Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
      [lia | by vm_compute].
  - rewrite /cons_erase.
    rewrite (fop_byte_ne c 21 ltac:(lia) ltac:(by vm_compute)).
    rewrite (fop_byte_ne c 8 ltac:(lia) ltac:(by vm_compute)).
    rewrite (fop_byte_ne c 127 ltac:(lia) ltac:(by vm_compute)).
    reflexivity.
  - lia.
Qed.

Lemma disc_seg_f_last_in (h : list mobs) (c : bv 8) :
  disc_seg_f h -> obs_ends_in Uart0 h c -> c ∈ ins h.
Proof using.
  intros _ [h0 ->]. rewrite ins_app ins_in.
  apply elem_of_app. right. apply elem_of_list_here.
Qed.

Lemma disc_seg_f_no_ctrl_d (h : list mobs) (c : bv 8) :
  disc_seg_f h -> obs_ends_in Uart0 h c -> bv_unsigned c <> 4%Z.
Proof using.
  intros Hd He.
  apply (disc_byte_ok_f (ins h) c Hd (disc_seg_f_last_in h c Hd He)).
Qed.

(* ====================================================================== *)
(*  1b.  THE DISCIPLINE'S CLOSURE LAWS                                     *)
(*                                                                        *)
(*  [FileDisc] landed [disc_input_f]'s full set and none of [disc_f]'s.    *)
(*  The ledger's power, output and input steps are stated at exactly       *)
(*  these, on [EchoDisc.disc_other]/[disc_out]/[disc_power]/[disc_in]'s    *)
(*  own statements.                                                        *)
(* ====================================================================== *)

(* the choice list restricted to the lines a PREFIX of the input has *)
Lemma lines_of_prefix (I I' : list (bv 8)) :
  I `prefix_of` I' -> lines_of I `prefix_of` lines_of I'.
Proof using.
  intros Hp. destruct (bodies_of_prefix I I' Hp) as [z Hz].
  rewrite /lines_of Hz fmap_app. by eexists.
Qed.

Lemma lines_of_length (I : list (bv 8)) : length (lines_of I) = nlines I.
Proof using. by rewrite /lines_of length_fmap. Qed.

Lemma alts_ok_take (I I' : list (bv 8)) (cs : list nat) :
  I' `prefix_of` I -> alts_ok I cs -> alts_ok I' (take (nlines I') cs).
Proof using.
  intros Hp Ha.
  pose proof (alts_ok_length I cs Ha) as Hlen.
  assert (Hle : (nlines I' <= nlines I)%nat) by (by apply nlines_prefix).
  assert (Hl' : lines_of I' = take (nlines I') (lines_of I)).
  { destruct (lines_of_prefix I' I Hp) as [z Hz].
    rewrite Hz take_app_length'; [reflexivity | by rewrite lines_of_length]. }
  rewrite /alts_ok Hl'. apply Forall2_take. exact Ha.
Qed.

Lemma disc_seg_f'_other (s : fstate) (seg : list mobs) (e : mobs) :
  not_cons_in e -> disc_seg_f' s (seg ++ [e]) <-> disc_seg_f' s seg.
Proof using.
  intro He.
  assert (Hi : in_pres (seg ++ [e]) = in_pres seg)
    by (by apply in_pres_snoc_other).
  assert (Hn : ins (seg ++ [e]) = ins seg)
    by (rewrite ins_app (ins_snoc_other e He) app_nil_r; reflexivity).
  rewrite /disc_seg_f' /disc_seg_f Hi Hn. done.
Qed.

Lemma disc_f_other (h : list mobs) (e : mobs) :
  is_io e = true -> not_cons_in e -> trace_shape h true ->
  disc_f (h ++ [e]) <-> disc_f h.
Proof using.
  intros Hio He Hsh.
  destruct (cycles_of_io h [e] Hsh) as (cs & Hc & Hc'); [by constructor |].
  rewrite /disc_f Hc Hc' !Forall_app !Forall_singleton.
  assert (Hiff : (exists s : fstate, fstate_ok s /\ disc_seg_f' s (open_seg h ++ [e]))
                 <-> (exists s : fstate, fstate_ok s /\ disc_seg_f' s (open_seg h))).
  { split; intros (s & Hs & Hd); exists s; split; [exact Hs | | exact Hs |];
      by apply (disc_seg_f'_other s (open_seg h) e He). }
  rewrite Hiff. done.
Qed.

Lemma disc_f_out (h : list mobs) (i : uart_id) (b : bv 8) :
  trace_shape h true -> disc_f (h ++ [ObsUartOut i b]) <-> disc_f h.
Proof using.
  intro Hsh. apply disc_f_other; [by destruct i | by destruct i | exact Hsh].
Qed.

Lemma disc_f_power (h : list mobs) (on : bool) :
  disc_f (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> disc_f h.
Proof using.
  rewrite /disc_f. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on Forall_app Forall_singleton.
    split; [by intros [? _] |].
    intros ?. split; [done |]. exists None. split; [exact I |].
    exact (disc_seg_f'_nil None).
Qed.

(* THE INPUT STEP.  [EchoDisc.disc_seg'_in]'s twin: dropping the last input
   byte drops at most one line, so the witness resolution is TRUNCATED --
   [FileDisc.sessf_take] then says the shorter transcript is the same
   bytes, and [alts_ok_take] that the truncation is still a resolution. *)
Lemma disc_seg_f'_in (s : fstate) (seg : list mobs) (b : bv 8) :
  disc_seg_f' s (seg ++ [ObsUartIn Uart0 b]) -> disc_seg_f' s seg.
Proof using.
  intros [Hd (ps & cs & Hl & Hall)].
  rewrite /disc_seg_f ins_app ins_in in Hd.
  rewrite ins_app ins_in in Hl.
  assert (Hpre : ins seg `prefix_of` (ins seg ++ [b])) by (by eexists).
  assert (Hle : (nlines (ins seg) <= nlines (ins seg ++ [b]))%nat)
    by (by apply nlines_prefix).
  split; [exact (disc_input_f_prefix _ _ Hpre Hd) |].
  exists ps, (take (nlines (ins seg)) cs).
  split; [exact (alts_ok_take _ _ cs Hpre Hl) |].
  intros p Hp.
  assert (Hpin : p ∈ in_pres (seg ++ [ObsUartIn Uart0 b])).
  { rewrite in_pres_in. apply elem_of_app. by left. }
  destruct (Hall p Hpin) as [[HF Hlt] Hpt].
  assert (Hplt : (nlines (ins p) <= nlines (ins seg))%nat).
  { apply nlines_prefix, ins_prefix.
    exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp). }
  split.
  - rewrite /pro_ok_f. split; [exact HF |].
    rewrite (pro_idx_f_ext (take (nlines (ins seg)) cs) cs (nlines (ins p)));
      [exact Hlt | | lia].
    intros j Hj. rewrite list_lookup_total_alt lookup_take; [| lia].
    by rewrite -list_lookup_total_alt.
  - rewrite /disc_pt_f (sessf_take ps cs s (done_of (ins p)) _
                          ltac:(rewrite nlines_done; exact Hplt)).
    exact Hpt.
Qed.

Lemma disc_f_in (h : list mobs) (b : bv 8) :
  trace_shape h true -> disc_f (h ++ [ObsUartIn Uart0 b]) -> disc_f h.
Proof using.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartIn Uart0 b] Hsh) as (cs & Hc & Hc');
    [by constructor |].
  rewrite /disc_f Hc Hc' !Forall_app !Forall_singleton.
  intros [Hall (s & Hs & Hseg)]. split; [exact Hall |].
  exists s. split; [exact Hs | exact (disc_seg_f'_in s _ _ Hseg)].
Qed.

(* the open cycle of a disciplined history keeps D3, and the whole per-cycle
   discipline with its boot state -- [EchoOutPure.disc_seg_open_seg] and
   [disc_seg'_open_seg]'s twins *)
Lemma disc_seg_f'_open_seg (h : list mobs) :
  trace_shape h true -> disc_f h ->
  exists s : fstate, fstate_ok s /\ disc_seg_f' s (open_seg h).
Proof using.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply elem_of_list_lookup in Hin as [i Hi].
  exact (Forall_lookup_1 _ _ _ _ Hd Hi).
Qed.

Lemma disc_seg_f_open_seg (h : list mobs) :
  trace_shape h true -> disc_f h -> disc_seg_f (open_seg h).
Proof using.
  intros Hsh Hd. destruct (disc_seg_f'_open_seg h Hsh Hd) as (s & _ & Hs & _).
  exact Hs.
Qed.

(* ====================================================================== *)
(*  2.  THE WRITER'S STREAM, IN THE FILE'S WORDS                         *)
(* ====================================================================== *)

(* the era's boot state, as the stage carries it: [None] until the era's
   first process byte files it.  Read as a state it is [FileDisc]'s absent
   file -- which is only ever read at the empty stage, where the claim's
   [GenOutPure.lm_out_pure] pins the stage's input and written bytes to be empty. *)
Definition f0_st (f0 : option fstate) : fstate := default None f0.

Lemma f0_st_some (s : fstate) : f0_st (Some s) = s.
Proof using. reflexivity. Qed.

Definition pending_at_f (ps cs : list nat) (f0 : option fstate)
    (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then pro_of ps
  else if decide (rest_of I = [])
       then alt_cont_f ps cs (f0_st f0) (bodies_of I) (nlines I - 1) else [].

(* the round pointer a block-opening stage stands at *)
Lemma pro_idx_f_nlines (cs : list nat) (I : list (bv 8)) :
  I <> [] -> rest_of I = [] ->
  ralt_panic (ralt_at cs (nlines I - 1)) = true ->
  S (pro_idx_f cs (nlines I - 1)) = pro_idx_f cs (nlines I).
Proof using.
  intros H0 Hm H3. pose proof (nlines_pos_of_rest_nil I H0 Hm) as Hq.
  replace (nlines I) with (S (nlines I - 1))%nat at 2 by lia.
  symmetry. by apply pro_idx_f_Sp.
Qed.

Lemma pending_at_f_ps_ext ps ps' cs f0 I :
  ps `prefix_of` ps' ->
  (pro_idx_f cs (nlines I) < pro_rounds ps)%nat ->
  pending_at_f ps cs f0 I = pending_at_f ps' cs f0 I.
Proof using.
  intros Hp Hr. rewrite /pending_at_f. case_decide as H0.
  { subst I. apply (pro_of_from_done_ext 0%nat); [exact Hp |].
    rewrite nlines_nil in Hr. cbn [pro_idx_f] in Hr. exact Hr. }
  case_decide as Hm; [| done].
  rewrite /alt_cont_f. f_equal.
  destruct (ralt_panic (ralt_at cs (nlines I - 1))) eqn:H3; [| done].
  rewrite (pro_idx_f_nlines cs I H0 Hm H3).
  by apply pro_of_from_done_ext.
Qed.

(* E's INDEX LAW is [EchoOutPure.E_index] verbatim (it names no discipline);
   its CONTENT LAW is D3 for the file application. *)
Definition E_disc_f (E : list (list mobs * bv 8)) : Prop :=
  disc_input_f (snd <$> E).

Lemma disc_input_f_rest_short I :
  disc_input_f I -> (S (length (rest_of I)) < line_max)%nat.
Proof using. by intros (_ & _ & H). Qed.

(* WHAT THE STAGE CARRIES.  [FileDisc.alts_ok] is a [Forall2] against ALL of
   [lines_of I] and so pins [length cs = nlines I]; the stage's list runs one
   short at a block boundary, so what it carries is this pointwise reading. *)
Definition alts_pre (I : list (bv 8)) (cs : list nat) : Prop :=
  forall (i : nat) (c : nat),
    cs !! i = Some c ->
    (i < nlines I)%nat
    /\ ralt_ok (uline_of (bodies_of I !!! i)) (ralt_dec c).

Lemma alts_pre_nil I : alts_pre I [].
Proof using. intros i c Hc. by rewrite lookup_nil in Hc. Qed.

Lemma alts_pre_le I cs : alts_pre I cs -> (length cs <= nlines I)%nat.
Proof using.
  intros H. destruct (decide (length cs = 0)%nat) as [Hz | Hz]; [lia |].
  destruct (lookup_lt_is_Some_2 cs (length cs - 1)%nat ltac:(lia)) as [c Hc].
  destruct (H _ c Hc) as [Hlt _]. lia.
Qed.

Lemma alts_pre_of_alts_ok I cs : alts_ok I cs -> alts_pre I cs.
Proof using.
  intros Ha i c Hc.
  destruct (Forall2_lookup_r _ _ _ _ _ Ha Hc) as (l & Hl & Hok).
  rewrite /lines_of list_lookup_fmap in Hl.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hl. injection Hl as <-.
  rewrite (list_lookup_total_correct _ _ _ Hb).
  split; [| exact Hok]. rewrite /nlines. by eapply lookup_lt_Some.
Qed.

(* the input GROWS and the entries keep their meaning: a completed line's
   body is the same body in every longer input *)
Lemma alts_pre_mono I I' cs :
  I `prefix_of` I' -> alts_pre I cs -> alts_pre I' cs.
Proof using.
  intros Hp H i c Hc. destruct (H i c Hc) as [Hi Hok].
  destruct (bodies_of_prefix I I' Hp) as [z Hz].
  split; [rewrite /nlines Hz length_app; rewrite /nlines in Hi; lia |].
  rewrite Hz list_lookup_total_alt lookup_app_l;
    [| rewrite /nlines in Hi; lia].
  by rewrite -list_lookup_total_alt.
Qed.

(* THE DEFAULT ALTERNATIVE: every line shape admits one, which is what makes
   a partial resolution paddable *)
Definition ralt_def (l : uline) : nat :=
  match l with
  | LEcho _ => 0%nat
  | LEchoF _ => ralt_enc RFExec
  | LCat => ralt_enc RCRan
  (* the DEAD arm: [LPipe] admits [LCat]'s five, so it defaults the same *)
  | LPipe _ _ => ralt_enc RCRan
  end.

Lemma ralt_def_ok (l : uline) : ralt_ok l (ralt_dec (ralt_def l)).
Proof using.
  destruct l as [ws | ws | | ws npc]; cbn [ralt_def].
  - rewrite (ralt_dec_lt4 0%nat ltac:(lia)). rewrite /ralt_ok. lia.
  - by rewrite ralt_dec_enc.
  - by rewrite ralt_dec_enc.
  - by rewrite ralt_dec_enc.
Qed.

Definition alts_pad (I : list (bv 8)) (cs : list nat) : list nat :=
  cs ++ (ralt_def <$> drop (length cs) (lines_of I)).

Lemma alts_pad_prefix I cs : cs `prefix_of` alts_pad I cs.
Proof using. rewrite /alts_pad. by eexists. Qed.

Lemma alts_pad_take I cs : take (length cs) (alts_pad I cs) = cs.
Proof using. rewrite /alts_pad. by rewrite take_app_length. Qed.

Lemma alts_pad_ok I cs :
  alts_pre I cs -> alts_ok I (alts_pad I cs).
Proof using.
  intros H. pose proof (alts_pre_le I cs H) as Hle.
  rewrite /alts_ok /alts_pad.
  rewrite -{1}(take_drop (length cs) (lines_of I)).
  apply Forall2_app.
  - apply Forall2_same_length_lookup_2.
    { rewrite length_take lines_of_length. lia. }
    intros i l c Hl Hc.
    apply lookup_take_Some in Hl as [Hl _].
    rewrite /lines_of list_lookup_fmap in Hl.
    destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
    cbn in Hl. injection Hl as <-.
    pose proof (proj2 (H i c Hc)) as Hok.
    by rewrite (list_lookup_total_correct _ _ _ Hb) in Hok.
  - apply Forall2_fmap_r. apply Forall_Forall2_diag.
    apply Forall_forall. intros l _. exact (ralt_def_ok l).
Qed.

(* ====================================================================== *)
(*  6b.  THE ERA'S PROCESS-BYTE CURSOR, AT THE FILE SESSION                *)
(*                                                                        *)
(*  [EchoOut]'s section 1b, moved down here because it is pure and because *)
(*  the claim file is long enough without it.                              *)
(* ====================================================================== *)

Fixpoint proc_before_from_f (ps cs : list nat) (f0 : option fstate)
    (pre I : list (bv 8)) : list (bv 8) :=
  match I with
  | [] => []
  | b :: I' => pending_at_f ps cs f0 pre
               ++ proc_before_from_f ps cs f0 (pre ++ [b]) I'
  end.

Definition proc_before_f (ps cs : list nat) (f0 : option fstate)
    (I : list (bv 8)) : list (bv 8) := proc_before_from_f ps cs f0 [] I.

Definition proc_stream_f (ps cs : list nat) (f0 : option fstate)
    (I : list (bv 8)) : list (bv 8) :=
  proc_before_f ps cs f0 I ++ pending_at_f ps cs f0 I.

Lemma proc_before_f_nil ps cs f0 : proc_before_f ps cs f0 [] = [].
Proof using. reflexivity. Qed.

Lemma fop_snoc_cases {A} (l : list A) : l = [] \/ exists u x, l = u ++ [x].
Proof using.
  induction l as [| a l IH]; [by left |]. right.
  destruct IH as [-> | (u & x & ->)].
  - by exists [], a.
  - by exists (a :: u), x.
Qed.

Lemma fop_removelast_take {A} (l : list A) :
  removelast l = take (length l - 1)%nat l.
Proof using.
  induction l as [| a l IH]; [done |].
  destruct l as [| b l']; [reflexivity |].
  change (removelast (a :: b :: l')) with (a :: removelast (b :: l')).
  rewrite IH.
  replace (length (a :: b :: l') - 1)%nat with (S (length (b :: l') - 1)%nat)
    by (cbn [length]; lia).
  reflexivity.
Qed.

Lemma fop_prefix_of_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> l <> l' -> l `prefix_of` removelast l'.
Proof using.
  intros Hp Hne. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Hlt : (length l < length l')%nat).
  { destruct (decide (length l = length l')) as [He | He]; [| lia].
    exfalso. exact (Hne (prefix_length_eq _ _ Hp ltac:(lia))). }
  assert (Hl : l = take (length l) l').
  { destruct Hp as [z ->]. by rewrite take_app_length. }
  rewrite fop_removelast_take {1}Hl. apply prefix_take_le. lia.
Qed.

Lemma fop_nlines_removelast (I : list (bv 8)) :
  rest_of I = [] -> nlines (removelast I) = (nlines I - 1)%nat.
Proof using.
  intros Hr. destruct (fop_snoc_cases I) as [-> | (u & x & ->)].
  - cbn [removelast]. rewrite nlines_nil. lia.
  - destruct (decide (x = wl_nl)) as [-> | Hx].
    + rewrite epu_removelast_snoc nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other u x Hx) in Hr.
      by destruct (app_eq_nil (rest_of u) [x] Hr) as [_ Hb].
Qed.

Lemma fop_nstarted_rest_nil (I : list (bv 8)) :
  rest_of I = [] -> nstarted I = nlines I.
Proof using.
  intros Hr. rewrite /nstarted Hr. case_decide as Hd;
    [lia | by destruct (Hd eq_refl)].
Qed.

Lemma fop_lta_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> (i < length cs0)%nat -> cs !!! i = cs0 !!! i.
Proof using.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma pending_at_f_cs_ext ps cs0 cs f0 I :
  cs0 `prefix_of` cs -> (nlines I <= length cs0)%nat ->
  pending_at_f ps cs0 f0 I = pending_at_f ps cs f0 I.
Proof using.
  intros Hp Hn. rewrite /pending_at_f.
  case_decide as H0; [done |].
  case_decide as Hr; [| done].
  pose proof (nlines_pos_of_rest_nil I H0 Hr) as Hpos.
  assert (Hlk : forall j, (j < nlines I)%nat -> cs0 !!! j = cs !!! j).
  { intros j Hj. symmetry. apply (fop_lta_prefix cs0 cs j Hp). lia. }
  rewrite /alt_cont_f /ralt_at (Hlk (nlines I - 1)%nat ltac:(lia)).
  rewrite (fstate_upto_ext cs0 cs (f0_st f0) (bodies_of I) (bodies_of I)
             (nlines I - 1)%nat ltac:(intros j Hj; apply Hlk; lia)
             ltac:(intros j Hj; reflexivity)).
  by rewrite (pro_idx_f_ext cs0 cs (nlines I) Hlk (nlines I - 1)%nat
                ltac:(lia)).
Qed.

Lemma pending_at_f_cs_prefix ps0 ps cs0 cs f0 I :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  (nlines I <= length cs0)%nat ->
  (pro_idx_f cs0 (nlines I) < pro_rounds ps0)%nat ->
  pending_at_f ps0 cs0 f0 I = pending_at_f ps cs f0 I.
Proof using.
  intros Hps Hcs Hn Hr.
  rewrite (pending_at_f_ps_ext ps0 ps cs0 f0 I Hps Hr).
  by apply pending_at_f_cs_ext.
Qed.

Lemma pending_at_f_stage_ext ps0 ps cs0 cs f0 I0 J :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_f ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  J `prefix_of` I0 -> J <> I0 ->
  pending_at_f ps0 cs0 f0 J = pending_at_f ps cs f0 J.
Proof using.
  intros Hps Hcs Hpin Hn HJ Hne.
  assert (Hjl : (nlines J <= length cs0)%nat).
  { etrans; [| exact Hn].
    apply nlines_prefix, (fop_prefix_of_removelast J I0 HJ Hne). }
  apply (pending_at_f_cs_prefix ps0 ps cs0 cs f0 J Hps Hcs Hjl).
  apply Hpin. exact (nstarted_strict J I0 HJ Hne).
Qed.

Lemma proc_before_from_f_ext ps0 ps cs0 cs f0 pre I :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ I -> J <> pre ++ I ->
     pending_at_f ps0 cs0 f0 J = pending_at_f ps cs f0 J) ->
  proc_before_from_f ps0 cs0 f0 pre I = proc_before_from_f ps cs f0 pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [b]) ++ I = pre ++ b :: I) by apply epu_app_snoc.
  assert (Hhere : pending_at_f ps0 cs0 f0 pre = pending_at_f ps cs f0 pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - apply (epu_app_cons_ne pre b I). }
  cbn [proc_before_from_f]. rewrite Hhere. f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma proc_before_f_ext ps0 ps cs0 cs f0 I :
  (forall J, J `prefix_of` I -> J <> I ->
     pending_at_f ps0 cs0 f0 J = pending_at_f ps cs f0 J) ->
  proc_before_f ps0 cs0 f0 I = proc_before_f ps cs f0 I.
Proof using.
  intros Hj. rewrite /proc_before_f. apply proc_before_from_f_ext.
  intros J _ H2 H3. rewrite app_nil_l in H2, H3. by apply Hj.
Qed.

Lemma proc_before_f_cs_prefix ps0 ps cs0 cs f0 I0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_f ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  proc_before_f ps0 cs0 f0 I0 = proc_before_f ps cs f0 I0.
Proof using.
  intros Hps Hcs Hpin Hn. apply proc_before_f_ext.
  intros J HJ Hne.
  exact (pending_at_f_stage_ext ps0 ps cs0 cs f0 I0 J Hps Hcs Hpin Hn HJ Hne).
Qed.

(* [sessf] is never empty once round 0 has settled *)
Lemma sessf_nonnil (ps cs : list nat) (s : fstate) (I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> pro_done ps ->
  sessf ps cs s I <> [].
Proof using.
  intros HF Hd H. rewrite /sessf in H.
  apply app_eq_nil in H as [H _].
  assert (Hne : ps <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos ps HF Hne) as Hpos. rewrite H in Hpos.
  cbn [length] in Hpos. lia.
Qed.

(* ====================================================================== *)
(*  9.  THE CHOICE LIST OUT OF RANGE, AND THE PAD'S ROUND POINTER         *)
(* ====================================================================== *)

(* out of range the choice list reads 0, which decodes to [REcho 0] -- an
   alternative whose output is never empty, whatever the line is *)
Lemma ralt_at_ge (cs : list nat) (i : nat) :
  (length cs <= i)%nat -> ralt_at cs i = REcho 0%nat.
Proof using.
  intro Hi.
  assert (Hz : cs !!! i = 0%nat).
  { rewrite list_lookup_total_alt (lookup_ge_None_2 cs i Hi). reflexivity. }
  rewrite /ralt_at Hz. apply ralt_dec_lt4. lia.
Qed.

Lemma ralt_panic_ge (cs : list nat) (i : nat) :
  (length cs <= i)%nat -> ralt_panic (ralt_at cs i) = false.
Proof using. intro Hi. rewrite (ralt_at_ge cs i Hi). by vm_compute. Qed.

(* NO ALTERNATIVE PRINTS NOTHING.  Every constant one carries at least the
   prompt or its own newline, [RCRan]'s content is closed by the prompt, and
   an [REcho k] is nonempty for [k < 4] -- which covers both an alternative
   a line ADMITS and the out-of-range reading. *)
Lemma cont_nonnil (s : fstate) (l : uline) (a : ralt) :
  ralt_ok l a \/ a = REcho 0%nat -> cont s l a <> [].
Proof using.
  intro Ha.
  assert (Hpr : u_prompt <> []).
  { pose proof u_prompt_pos as Hup.
    destruct u_prompt as [| z zs]; [cbn [length] in Hup; lia | done]. }
  assert (Hex : alt_execfail <> []) by (by vm_compute).
  assert (Hop : alt_openfail <> []) by (by vm_compute).
  assert (Hpa : alt_panic <> []) by (by vm_compute).
  assert (Hca : alt_catopen <> []) by (by vm_compute).
  assert (Hec : alt_execcat <> []) by (by vm_compute).
  destruct a as [k | sel | | | | | | | | | |]; rewrite /cont.
  - assert (Hk : (k < 4)%nat).
    { destruct Ha as [Ha | Heq]; [| injection Heq as <-; lia].
      destruct l as [ws | ws | | ws npc];
        [exact Ha | by destruct Ha | by destruct Ha | by destruct Ha]. }
    exact (line_alts_of_nonnil (uline_ws l) k Hk).
  - exact Hpr.
  - exact Hex.
  - exact Hop.
  - exact Hop.
  - exact Hpr.
  - exact Hpa.
  - destruct s as [bs |]; [| exact Hca].
    intro Hq. by destruct (app_eq_nil bs u_prompt Hq) as [_ Hb].
  - exact Hca.
  - exact Hec.
  - exact Hpr.
  - exact Hpa.
Qed.

(* ---- THE PADDING MOVES NO PROLOGUE ROUND.  [pro_idx_f] reads the choice
       list only through [ralt_panic], and neither the out-of-range reading
       ([REcho 0]) nor any default alternative panics -- so a stage's round
       index is the same at its own list and at the padded one. ---- *)
Lemma ralt_panic_def (l : uline) : ralt_panic (ralt_dec (ralt_def l)) = false.
Proof using.
  destruct l as [ws | ws | | ws npc]; cbn [ralt_def].
  - rewrite (ralt_dec_lt4 0%nat ltac:(lia)). by vm_compute.
  - rewrite ralt_dec_enc. by vm_compute.
  - rewrite ralt_dec_enc. by vm_compute.
  - rewrite ralt_dec_enc. by vm_compute.
Qed.

Lemma pro_idx_f_ext_panic (cs1 cs2 : list nat) (q : nat) :
  (forall j, (j < q)%nat ->
     ralt_panic (ralt_at cs1 j) = ralt_panic (ralt_at cs2 j)) ->
  forall j, (j <= q)%nat -> pro_idx_f cs1 j = pro_idx_f cs2 j.
Proof using.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_f_S IH; [| lia]. by rewrite (Hj j ltac:(lia)).
Qed.

Lemma alts_pad_panic (I : list (bv 8)) (cs : list nat) (j : nat) :
  (j < nlines I)%nat ->
  ralt_panic (ralt_at (alts_pad I cs) j) = ralt_panic (ralt_at cs j).
Proof using.
  intros Hj. destruct (decide (j < length cs)%nat) as [Hlt | Hge].
  - by rewrite /ralt_at (fop_lta_prefix cs (alts_pad I cs) j
                           (alts_pad_prefix I cs) Hlt).
  - rewrite (ralt_panic_ge cs j ltac:(lia)).
    destruct (decide (j < length (alts_pad I cs))%nat) as [Hlt2 | Hge2];
      last first.
    { by rewrite (ralt_panic_ge (alts_pad I cs) j ltac:(lia)). }
    (* inside the PAD: the entry is the line's default alternative *)
    assert (Hjl : (j < length (lines_of I))%nat)
      by (rewrite lines_of_length; lia).
    destruct (lookup_lt_is_Some_2 (lines_of I) j Hjl) as [l Hl].
    assert (Hlk : alts_pad I cs !!! j = ralt_def l).
    { rewrite /alts_pad list_lookup_total_alt lookup_app_r; [| lia].
      rewrite list_lookup_fmap lookup_drop.
      replace (length cs + (j - length cs))%nat with j by lia.
      by rewrite Hl. }
    rewrite /ralt_at Hlk. exact (ralt_panic_def _).
Qed.

Lemma alts_pad_pro_idx (I : list (bv 8)) (cs : list nat) (q : nat) :
  (q <= nlines I)%nat -> pro_idx_f (alts_pad I cs) q = pro_idx_f cs q.
Proof using.
  intro Hq. apply (pro_idx_f_ext_panic (alts_pad I cs) cs (nlines I));
    [| exact Hq].
  intros j Hj. exact (alts_pad_panic I cs j Hj).
Qed.

(* past the choice list's end the round pointer stops moving: every entry
   there reads [REcho 0], which does not panic *)
Lemma pro_idx_f_ge (cs : list nat) (q q' : nat) :
  (length cs <= q)%nat -> (q <= q')%nat -> pro_idx_f cs q' = pro_idx_f cs q.
Proof using.
  intros Hle Hq. induction q' as [| q' IH].
  - assert (Hz : q = 0%nat) by lia. by subst q.
  - destruct (decide (q = S q')) as [-> | Hne]; [reflexivity |].
    rewrite pro_idx_f_S (IH ltac:(lia)) (ralt_panic_ge cs q' ltac:(lia)). lia.
Qed.

(* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE cannot falsify a cycle
   that was good -- [EchoOut.good_out_step]'s twin.  It needs one more move
   than the echo one: the extended input may have one more COMPLETE LINE,
   and [FileDisc.alts_ok] demands an entry per line, so the resolution is
   padded.  The padding moves no prologue round ([alts_pad_pro_idx]) and
   changes no block the shorter input had ([alts_pad_take] through
   [FileDisc.sessf_take]), so the same [ps] still answers. *)
Lemma good_out_f_step (s : fstate) (seg : list mobs) (e : mobs) :
  obs_wire Uart0 [e] = [] -> good_out_f s seg -> good_out_f s (seg ++ [e]).
Proof using.
  intros He (ps & cs & [Hpsb Hlt] & Hao & Hwire).
  set (I := ins seg). set (I' := ins (seg ++ [e])).
  assert (HII : I `prefix_of` I') by (rewrite /I /I' ins_app; by eexists).
  assert (Hlen : length cs = nlines I) by exact (alts_ok_length _ _ Hao).
  assert (Hnl : (nlines I <= nlines I')%nat) by (by apply nlines_prefix).
  set (cs' := alts_pad I' cs).
  exists ps, cs'. split.
  { split; [exact Hpsb |].
    rewrite /cs' (alts_pad_pro_idx I' cs (nlines I') ltac:(lia)).
    (* the pad is read only past the shorter input's last line, and a
       default alternative never panics *)
    rewrite (pro_idx_f_ge cs (nlines I) (nlines I') ltac:(lia) Hnl).
    exact Hlt. }
  split.
  { rewrite /cs'. apply alts_pad_ok.
    apply (alts_pre_mono I I'); [exact HII | exact (alts_pre_of_alts_ok _ _ Hao)]. }
  rewrite /I' obs_wire_app He app_nil_r.
  etrans; [exact Hwire |].
  assert (Hcut : sessf ps cs s I = sessf ps cs' s I).
  { rewrite -{1}(alts_pad_take I' cs) -/cs'.
    apply sessf_take. lia. }
  rewrite Hcut. by apply sessf_mono.
Qed.

(* ====================================================================== *)
(*  12.  THE ERA'S FIRST DRAIN: AN UNDRAINED CYCLE HAS TYPED NOTHING       *)
(*                                                                        *)
(*  The ledger fixes an era's boot state at the era's FIRST DRAIN, and     *)
(*  what makes that the right moment is D2: the checked prefix before a    *)
(*  cycle's first input byte already owes the whole prologue, which is     *)
(*  NONEMPTY.  So a cycle whose console wire is still empty has no input   *)
(*  byte at all, hence no complete line, hence the ledger's line list at   *)
(*  that moment IS the list of lines typed in strictly EARLIER cycles --   *)
(*  which is the set [FileDisc.file_phi]'s third clause reads the boot     *)
(*  state against.                                                        *)
(* ====================================================================== *)

(* the prefix before a cycle's FIRST console input byte is itself input-free *)
Lemma in_pres_first (seg : list mobs) :
  ins seg <> [] -> exists p, p ∈ in_pres seg /\ ins p = [].
Proof using.
  induction seg as [| e seg IH]; [by intros Hne |].
  destruct e as [i b | i b | |]; cbn [in_pres].
  - destruct i.
    + intros _. exists []. split; [apply elem_of_cons; by left | done].
    + intros Hne. destruct (IH Hne) as (p & Hp & Hi).
      exists (ObsUartIn Uart1 b :: p). split; [| exact Hi].
      apply elem_of_list_fmap. by exists p.
  - intros Hne. destruct (IH Hne) as (p & Hp & Hi).
    exists (ObsUartOut i b :: p). split; [| exact Hi].
    apply elem_of_list_fmap. by exists p.
  - intros Hne. destruct (IH Hne) as (p & Hp & Hi).
    exists (ObsPowerOn :: p). split; [| exact Hi].
    apply elem_of_list_fmap. by exists p.
  - intros Hne. destruct (IH Hne) as (p & Hp & Hi).
    exists (ObsPowerOff :: p). split; [| exact Hi].
    apply elem_of_list_fmap. by exists p.
Qed.

(* THE PURE FACT.  Under the discipline, a cycle whose console wire is
   empty has received no console input. *)
Lemma disc_f_first_out (h : list mobs) :
  disc_f h -> trace_shape h true ->
  obs_wire Uart0 (open_seg h) = [] -> ins (open_seg h) = [].
Proof using.
  intros Hd Hsh Hw.
  destruct (decide (ins (open_seg h) = [])) as [? | Hne]; [done | exfalso].
  destruct (disc_seg_f'_open_seg h Hsh Hd) as (s & _ & _ & ps & cs & _ & Hall).
  destruct (in_pres_first (open_seg h) Hne) as (p & Hp & Hpi).
  destruct (Hall p Hp) as [[Hpsb Hlt] Hpt].
  rewrite /disc_pt_f Hpi done_of_nil in Hpt.
  assert (Hwp : obs_wire Uart0 p = []).
  { destruct (proj1 (Forall_forall _ _) (in_pres_prefix_all (open_seg h)) p Hp)
      as [z Hz].
    rewrite Hz obs_wire_app in Hw. by destruct (app_eq_nil _ _ Hw) as [Hz1 _]. }
  rewrite Hwp in Hpt.
  apply (sessf_nonnil ps cs s [] Hpsb).
  - apply (proj2 (pro_done_rounds ps)).
    rewrite Hpi nlines_nil in Hlt. cbn [pro_idx_f] in Hlt. lia.
  - exact (prefix_nil_inv _ Hpt).
Qed.

Lemma echof_lines_before_cut (h : list mobs) (cs : list (list mobs))
    (o : list mobs) :
  cycles_of h = cs ++ [o] ->
  echof_lines_before h (length cs) = concat (echof_cyc <$> cs).
Proof using.
  intros Hc. rewrite /echof_lines_before Hc take_app_length. reflexivity.
Qed.

Lemma echof_lines_of_cut (h : list mobs) (cs : list (list mobs))
    (o : list mobs) :
  cycles_of h = cs ++ [o] -> ins o = [] ->
  echof_lines_of h = concat (echof_cyc <$> cs).
Proof using.
  intros Hc Ho. rewrite /echof_lines_of Hc fmap_app concat_app.
  cbn [fmap list_fmap concat]. rewrite /echof_cyc Ho.
  rewrite /echof_lines_in /lines_of bodies_of_nil fmap_nil.
  by rewrite !app_nil_r.
Qed.

(* THE COROLLARY THE LEDGER SPENDS.  At the era's first drain the ledger's
   line list -- the lines of the WHOLE history -- is exactly the list of
   lines typed in the cycles strictly before the open one.  [n] is the open
   cycle's INDEX, which is one less than the number of cycles (and so one
   less than [obs_boots h]: the eras the per-era maps are keyed by are
   1-based, the cycles 0-based). *)
Lemma efl_of_first_out (h : list mobs) (e : mobs) (n : nat) :
  disc_f h -> trace_shape h true -> is_io e = true ->
  obs_wire Uart0 (open_seg h) = [] ->
  S n = length (cycles_of h) ->
  echof_lines_of h = echof_lines_before (h ++ [e]) n.
Proof using.
  intros Hd Hsh Hio Hw Hn.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hlen : length cs = n).
  { rewrite H1 length_app in Hn. cbn [length] in Hn. lia. }
  rewrite (echof_lines_of_cut h cs (open_seg h) H1
             (disc_f_first_out h Hd Hsh Hw)).
  rewrite -Hlen. symmetry.
  exact (echof_lines_before_cut (h ++ [e]) cs (open_seg h ++ [e]) H2).
Qed.

(* ====================================================================== *)
(*  13.  THE CONCLUSION'S BODY, AND ITS FOUR STEPS                         *)
(*                                                                        *)
(*  [FileDisc.file_phi]'s body at a given list of per-cycle boot states.   *)
(*  The ledger carries [exists s0s, disc_f h -> file_phi_body h s0s], so   *)
(*  [FileDisc.file_phi] follows VERBATIM.                                  *)
(* ====================================================================== *)

Definition file_phi_body (h : list mobs) (s0s : list fstate) : Prop :=
  length s0s = length (cycles_of h)
  /\ (forall s, s0s !! 0%nat = Some s -> s = None)
  /\ (forall k s, s0s !! S k = Some s ->
        fadm_boot (echof_lines_before h (S k)) s)
  /\ Forall2 good_out_f s0s (cycles_of h).

Lemma file_phi_of_body (h : list mobs) (s0s : list fstate) :
  (disc_f h -> file_phi_body h s0s) -> file_phi h.
Proof using.
  intros H Hd. destruct (H Hd) as (H1 & H2 & H3 & H4).
  by exists s0s.
Qed.

Lemma file_phi_body_nil : file_phi_body [] [].
Proof using.
  rewrite /file_phi_body (_ : cycles_of [] = []); [| reflexivity].
  split_and!.
  - reflexivity.
  - intros s Hs. discriminate.
  - intros k s Hs. discriminate.
  - constructor.
Qed.

(* an event that puts nothing on the console's wire *)
Lemma file_phi_body_step_io (h : list mobs) (e : mobs) (s0s : list fstate) :
  trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
  file_phi_body h s0s -> file_phi_body (h ++ [e]) s0s.
Proof using.
  intros Hsh Hio Hw (Hlen & H0 & Hadm & HF).
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  rewrite H1 in Hlen, HF. rewrite /file_phi_body H2.
  assert (Hcut : forall j, (j < length s0s)%nat ->
                   echof_lines_before (h ++ [e]) j = echof_lines_before h j).
  { intros j Hj. rewrite /echof_lines_before H1 H2.
    rewrite length_app in Hlen. cbn [length] in Hlen.
    rewrite !take_app_le; [reflexivity | lia | lia]. }
  split_and!.
  - rewrite Hlen !length_app. reflexivity.
  - exact H0.
  - intros k s Hs. rewrite (Hcut (S k) (lookup_lt_Some _ _ _ Hs)).
    exact (Hadm k s Hs).
  - apply Forall2_app_inv_r in HF as (u1 & u2 & Hu1 & Hu2 & ->).
    apply Forall2_app; [exact Hu1 |].
    apply Forall2_cons_inv_r in Hu2 as (y & u3 & Hy & Hu3 & ->).
    apply Forall2_nil_inv_r in Hu3 as ->.
    constructor; [| constructor].
    exact (good_out_f_step y (open_seg h) e Hw Hy).
Qed.

Lemma file_phi_body_off (h : list mobs) (s0s : list fstate) :
  file_phi_body h s0s -> file_phi_body (h ++ [ObsPowerOff]) s0s.
Proof using.
  rewrite /file_phi_body /echof_lines_before cycles_of_off. done.
Qed.

Lemma file_phi_body_on (h : list mobs) (s0s : list fstate) :
  file_phi_body h s0s -> file_phi_body (h ++ [ObsPowerOn]) (s0s ++ [None]).
Proof using.
  intros (Hlen & H0 & Hadm & HF). rewrite /file_phi_body cycles_of_on.
  assert (Hcut : forall j, (j <= length s0s)%nat ->
                   echof_lines_before (h ++ [ObsPowerOn]) j
                   = echof_lines_before h j).
  { intros j Hj. rewrite /echof_lines_before cycles_of_on.
    rewrite take_app_le; [reflexivity | lia]. }
  split_and!.
  - rewrite !length_app Hlen. reflexivity.
  - intros s Hs. destruct s0s as [| y s0s].
    + cbn in Hs. by injection Hs as <-.
    + rewrite -app_comm_cons in Hs. cbn in Hs. exact (H0 s Hs).
  - intros k s Hs.
    destruct (decide (S k < length s0s)%nat) as [Hk | Hk].
    + rewrite lookup_app_l in Hs; [| lia].
      rewrite (Hcut (S k) ltac:(lia)). exact (Hadm k s Hs).
    + rewrite lookup_app_r in Hs; [| lia].
      assert (Hje : S k = length s0s).
      { apply lookup_lt_Some in Hs. cbn [length] in Hs. lia. }
      rewrite Hje Nat.sub_diag in Hs. cbn in Hs.
      injection Hs as <-. by left.
  - apply Forall2_app; [exact HF |].
    constructor; [exact (good_out_f_nil None) | constructor].
Qed.

(* the admissibility the OPEN cycle's entry already carries: at cycle 0 it
   is the guarded first clause (the entry is [None], admissible anywhere),
   and at a later cycle it is the third clause, whose line set a console
   output does not move *)
Lemma file_phi_body_last_adm (h : list mobs) (e : mobs) (u1 : list fstate)
    (x : fstate) :
  trace_shape h true -> is_io e = true ->
  file_phi_body h (u1 ++ [x]) ->
  fadm_boot (echof_lines_before (h ++ [e]) (length u1)) x.
Proof using.
  intros Hsh Hio (Hlen & H0 & Hadm & _).
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1).
  { rewrite H1 !length_app in Hlen. cbn [length] in Hlen. lia. }
  assert (Hlk : (u1 ++ [x]) !! length u1 = Some x)
    by (rewrite lookup_app_r; [by rewrite Nat.sub_diag | lia]).
  destruct (length u1) as [| n] eqn:Hn.
  - rewrite (H0 x Hlk). by left.
  - assert (Hcut : echof_lines_before (h ++ [e]) (S n)
                   = echof_lines_before h (S n)).
    { rewrite /echof_lines_before H1 H2 !take_app_le; [reflexivity | lia | lia]. }
    rewrite Hcut. exact (Hadm n x Hlk).
Qed.

(* THE DRAIN'S STEP: the console's own output, at the era's boot state --
   which the ledger may REPLACE here, because this may be the era's first
   drain and the entry it replaces was provisional. *)
Lemma file_phi_body_out (h : list mobs) (b : bv 8) (u1 : list fstate)
    (x s0 : fstate) :
  trace_shape h true ->
  good_out_f s0 (open_seg h ++ [ObsUartOut Uart0 b]) ->
  fadm_boot (echof_lines_before (h ++ [ObsUartOut Uart0 b]) (length u1)) s0 ->
  file_phi_body h (u1 ++ [x]) ->
  file_phi_body (h ++ [ObsUartOut Uart0 b]) (u1 ++ [s0]).
Proof using.
  intros Hsh Hgo Hadm0 (Hlen & H0 & Hadm & HF).
  destruct (cycles_of_io h [ObsUartOut Uart0 b] Hsh
              (proj2 (Forall_singleton _ _) (eq_refl : is_io (ObsUartOut Uart0 b) = true))) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1).
  { rewrite H1 !length_app in Hlen. cbn [length] in Hlen. lia. }
  assert (Hcut : forall j, (j <= length u1)%nat ->
                   echof_lines_before (h ++ [ObsUartOut Uart0 b]) j
                   = echof_lines_before h j).
  { intros j Hj. rewrite /echof_lines_before H1 H2.
    rewrite !take_app_le; [reflexivity | lia | lia]. }
  rewrite /file_phi_body H2. split_and!.
  - rewrite !length_app. rewrite H1 !length_app in Hlen. exact Hlen.
  - intros s Hs. destruct u1 as [| y u1].
    + cbn in Hs. injection Hs as <-. cbn [length] in Hadm0.
      destruct Hadm0 as [Hz | (ws & sel & Hws & _)]; [exact Hz |].
      exfalso. revert Hws. rewrite /echof_lines_before take_0.
      cbn [fmap list_fmap concat]. apply not_elem_of_nil.
    + apply (H0 s). exact Hs.
  - intros k s Hs.
    destruct (decide (S k < length u1)%nat) as [Hk | Hk].
    + rewrite lookup_app_l in Hs; [| lia].
      rewrite (Hcut (S k) ltac:(lia)). apply (Hadm k s).
      rewrite lookup_app_l; [exact Hs | lia].
    + rewrite lookup_app_r in Hs; [| lia].
      assert (Hje : S k = length u1).
      { apply lookup_lt_Some in Hs. cbn [length] in Hs. lia. }
      rewrite Hje Nat.sub_diag in Hs. cbn in Hs.
      injection Hs as <-. rewrite Hje. exact Hadm0.
  - rewrite H1 in HF.
    destruct (Forall2_app_inv good_out_f u1 [x] cs [open_seg h] ltac:(lia) HF)
      as [Hv1 _].
    apply Forall2_app; [exact Hv1 |].
    constructor; [exact Hgo | constructor].
Qed.

(* a nonempty list is a snoc *)
Lemma fop_snoc_inv {A} (l : list A) : l <> [] -> exists l' a, l = l' ++ [a].
Proof using.
  intros Hne. induction l as [| x l IH] using rev_ind; [done |].
  by exists l, x.
Qed.

(* THE LEDGER'S DRAIN STEP, PURELY.  At the era's FIRST drain the entry
   being replaced is provisional, and the admissibility of the drain's own
   state comes from the deed's witness read against the WHOLE history's
   line list -- which, the cycle having typed nothing ([efl_of_first_out]),
   IS the list of lines typed in strictly earlier cycles.  At a LATER drain
   the state is the one the ledger already fixed, and its admissibility is
   in the body already. *)
Lemma file_phi_body_drain (h : list mobs) (b : bv 8) (s0s : list fstate)
    (s0 : fstate) :
  trace_shape h true -> disc_f h ->
  good_out_f s0 (open_seg h ++ [ObsUartOut Uart0 b]) ->
  fadm_boot (echof_lines_of h) s0 ->
  (obs_wire Uart0 (open_seg h) <> [] -> exists u1, s0s = u1 ++ [s0]) ->
  file_phi_body h s0s ->
  file_phi_body (h ++ [ObsUartOut Uart0 b]) (removelast s0s ++ [s0]).
Proof using.
  intros Hsh Hd Hgo Hadm Hlast Hb.
  destruct (cycles_of_io h [ObsUartOut Uart0 b] Hsh
              (proj2 (Forall_singleton _ _)
                 (eq_refl : is_io (ObsUartOut Uart0 b) = true)))
    as (cs & H1 & H2).
  assert (Hne : s0s <> []).
  { intros Hz. destruct Hb as (Hlen & _).
    rewrite Hz H1 length_app in Hlen. cbn [length] in Hlen. lia. }
  destruct (fop_snoc_inv s0s Hne) as (u1 & x & ->).
  rewrite (epu_removelast_snoc u1 x).
  apply (file_phi_body_out h b u1 x s0 Hsh Hgo); [| exact Hb].
  destruct (decide (obs_wire Uart0 (open_seg h) = [])) as [Hw | Hw].
  - (* the era's FIRST drain *)
    assert (Hlen : S (length u1) = length (cycles_of h)).
    { destruct Hb as (Hl & _). rewrite length_app in Hl. cbn [length] in Hl. lia. }
    rewrite -(efl_of_first_out h (ObsUartOut Uart0 b) (length u1)
                Hd Hsh eq_refl Hw Hlen).
    exact Hadm.
  - (* a LATER drain of the same era: the state is the one already fixed *)
    assert (Hx : x = s0).
    { destruct (Hlast Hw) as (u2 & Hu2).
      destruct (app_inj_2 u1 u2 [x] [s0] eq_refl Hu2) as [_ Hxx].
      by injection Hxx. }
    rewrite -Hx.
    exact (file_phi_body_last_adm h (ObsUartOut Uart0 b) u1 x Hsh eq_refl Hb).
Qed.
