(* ===================================================================== *)
(*  PipesLedPure.v -- THE LEDGER'S CLOSURE LAWS OF A LINE MODEL'S         *)
(*  DISCIPLINE AND CONCLUSION, once over the model (cut C8).             *)
(*                                                                       *)
(*  [PipeOutPure]'s [disc_p_other] / [disc_p_out] / [disc_p_power] /     *)
(*  [disc_p_in] and [PipeOut]'s [phi_step_io_p] / [phi_step_cons_p],      *)
(*  stated at [LineModel.lm_disc] and [LineModel.lm_good_out]: what a     *)
(*  ledger whose taint counter sits at [decide (lm_disc M h)] spends at   *)
(*  each event of the trace.  PURE.                                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
From stdpp Require Import list.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

Section lm_led.
  Context (M : lmodel) (B : lm_byte_laws M).

  (* ---- an event that is not a console input leaves the discipline ---- *)
  Lemma lm_disc_seg'_other (s : lm_st M) (seg : list mobs) (e : mobs) :
    not_cons_in e -> lm_disc_seg' M s (seg ++ [e]) <-> lm_disc_seg' M s seg.
  Proof using.
    intro He.
    assert (Hi : in_pres (seg ++ [e]) = in_pres seg)
      by (by apply in_pres_snoc_other).
    assert (Hn : ins (seg ++ [e]) = ins seg)
      by (rewrite ins_app (ins_snoc_other e He) app_nil_r; reflexivity).
    rewrite /lm_disc_seg' Hi Hn. done.
  Qed.

  Lemma lm_disc_other (h : list mobs) (e : mobs) :
    is_io e = true -> not_cons_in e -> trace_shape h true ->
    lm_disc M (h ++ [e]) <-> lm_disc M h.
  Proof using.
    intros Hio He Hsh.
    destruct (cycles_of_io h [e] Hsh) as (cs & Hc & Hc'); [by constructor |].
    rewrite /lm_disc Hc Hc' !Forall_app !Forall_singleton.
    split.
    - intros [H1 (s & Hs & Hd)]. split; [exact H1 |]. exists s.
      split; [exact Hs |]. exact (proj1 (lm_disc_seg'_other s _ _ He) Hd).
    - intros [H1 (s & Hs & Hd)]. split; [exact H1 |]. exists s.
      split; [exact Hs |]. exact (proj2 (lm_disc_seg'_other s _ _ He) Hd).
  Qed.

  Lemma lm_disc_out (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true -> lm_disc M (h ++ [ObsUartOut i b]) <-> lm_disc M h.
  Proof using.
    intro Hsh. apply lm_disc_other; [by destruct i | by destruct i | exact Hsh].
  Qed.

  (* ---- the empty cycle is disciplined, at any boot state ---- *)
  Lemma lm_disc_seg'_nil (s : lm_st M) : lm_disc_seg' M s [].
  Proof using.
    split.
    { split; [constructor |]. split; [constructor |]. vm_compute. lia. }
    exists [], []. split; [apply lm_alts_ok_nil; by vm_compute |].
    split.
    - intros i Hi. rewrite /nlines in Hi. cbn in Hi. lia.
    - intros p Hp. by apply elem_of_nil in Hp.
  Qed.

  Lemma lm_disc_nil : lm_disc M [].
  Proof using. rewrite /lm_disc /cycles_of /=. constructor. Qed.

  Lemma lm_disc_power (h : list mobs) (on : bool) :
    (exists s, lm_st_ok M s) ->
    lm_disc M (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> lm_disc M h.
  Proof using.
    intros [s0 Hs0]. rewrite /lm_disc. destruct on.
    - by rewrite cycles_of_off.
    - rewrite cycles_of_on Forall_app Forall_singleton.
      split; [by intros [? _] |].
      intros ?. split; [done |]. exists s0. split; [exact Hs0 | exact (lm_disc_seg'_nil s0)].
  Qed.

  (* ---- THE INPUT STEP: the discipline is prefix-closed ---- *)

  (* D4 at the truncated resolution of a strictly shorter input: vacuous
     below the last line, since D4 puts a coverage-ending round at the
     input's very end ([GenOut.lm_d4_nomerge_snoc], restated here pure) *)
  Lemma lm_d4_take_snoc (cs : list nat) (s : lm_st M) (I : list (bv 8)) (b : bv 8) :
    lm_d4 M cs s (I ++ [b]) -> lm_d4 M (take (nlines I) cs) s I.
  Proof using.
    intros Hd4 i Hi Hex Hm. exfalso.
    destruct (bodies_of_prefix I (I ++ [b]) ltac:(by eexists)) as [z Hz].
    assert (Hbod : forall j, j < nlines I ->
              bodies_of (I ++ [b]) !!! j = bodies_of I !!! j).
    { intros j Hj. rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite /nlines in Hj; lia]. }
    assert (Htk : forall j, j < nlines I -> take (nlines I) cs !!! j = cs !!! j).
    { intros j Hj. rewrite !list_lookup_total_alt lookup_take; [done | lia]. }
    assert (Hup : lm_upto M (take (nlines I) cs) s (bodies_of I) i
                  = lm_upto M cs s (bodies_of (I ++ [b])) i).
    { apply (lm_upto_ext M); [intros j Hj; apply Htk; lia |].
      intros j Hj. symmetry. apply Hbod. lia. }
    rewrite Hup /lm_at (Htk i Hi) -(Hbod i Hi) in Hm.
    rewrite Hup -(Hbod i Hi) in Hex.
    assert (Hle : nlines I <= nlines (I ++ [b])) by (apply nlines_prefix; by eexists).
    destruct (Hd4 i ltac:(lia) Hex Hm) as [Hn Hr].
    destruct (decide (b = wl_nl)) as [-> | Hne].
    - rewrite nlines_snoc_nl in Hn. lia.
    - rewrite (rest_of_snoc_other I b Hne) in Hr.
      apply app_eq_nil in Hr as [_ Hr]. discriminate.
  Qed.

  Lemma lm_alts_ok_take (s : lm_st M) (I I' : list (bv 8)) (cs : list nat) :
    I `prefix_of` I' -> lm_alts_ok M s I' cs -> lm_alts_ok M s I (take (nlines I) cs).
  Proof using. exact (lm_alts_ok_prefix M s I I' cs). Qed.

  Lemma lm_disc_seg'_in (s : lm_st M) (seg : list mobs) (b : bv 8) :
    lm_disc_seg' M s (seg ++ [ObsUartIn Uart0 b]) -> lm_disc_seg' M s seg.
  Proof using B.
    intros [Hd (ps & cs & Hl & Hd4 & Hall)].
    rewrite ins_app ins_in in Hd, Hl, Hd4.
    assert (Hpre : ins seg `prefix_of` (ins seg ++ [b])) by (by eexists).
    split; [exact (lm_disc_input_prefix M B _ _ Hpre Hd) |].
    set (n := nlines (ins seg)).
    assert (Htk : forall j, j < n -> take n cs !!! j = cs !!! j).
    { intros j Hj. rewrite !list_lookup_total_alt lookup_take; [done | lia]. }
    exists ps, (take n cs).
    split; [exact (lm_alts_ok_take s _ _ cs Hpre Hl) |].
    split; [exact (lm_d4_take_snoc cs s (ins seg) b Hd4) |].
    intros p Hp.
    assert (Hpin : p ∈ in_pres (seg ++ [ObsUartIn Uart0 b])).
    { rewrite in_pres_in. apply elem_of_app. by left. }
    destruct (Hall p Hpin) as [[HF Hlt] Hpt].
    assert (Hplt : nlines (ins p) <= n).
    { apply nlines_prefix, ins_prefix.
      exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp). }
    split.
    - split; [exact HF |].
      rewrite (lm_pro_idx_ext M (take n cs) cs n Htk (nlines (ins p)) Hplt).
      exact Hlt.
    - rewrite /lm_disc_pt.
      rewrite (lm_sess_cs_ext M ps (take n cs) cs s (done_of (ins p))
                 ltac:(rewrite nlines_done; intros j Hj; apply Htk; lia)).
      exact Hpt.
  Qed.

  Lemma lm_disc_in (h : list mobs) (b : bv 8) :
    trace_shape h true -> lm_disc M (h ++ [ObsUartIn Uart0 b]) -> lm_disc M h.
  Proof using B.
    intros Hsh.
    destruct (cycles_of_io h [ObsUartIn Uart0 b] Hsh) as (cs & Hc & Hc');
      [by constructor |].
    rewrite /lm_disc Hc Hc' !Forall_app !Forall_singleton.
    intros [Hall (s & Hs & Hseg)]. split; [exact Hall |].
    exists s. split; [exact Hs | exact (lm_disc_seg'_in s _ _ Hseg)].
  Qed.

  (* ---- THE CONCLUSION'S STEPS ---- *)
  Lemma lm_good_out_nil (s : lm_st M) : lm_good_out M s [].
  Proof using.
    exists [0%nat], []. split.
    { split.
      - apply Forall_singleton. rewrite pro_alts_length. lia.
      - vm_compute. lia. }
    split; [apply lm_alts_ok_nil; by vm_compute |].
    apply prefix_nil.
  Qed.

  Context (K : lm_hooks M).

  Lemma lm_phi_step_io (s : lm_st M) (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
    Forall (lm_good_out M s) (cycles_of h) ->
    Forall (lm_good_out M s) (cycles_of (h ++ [e])).
  Proof using B K.
    intros Hsh Hio Hw HF.
    destruct (cycles_of_io h [e] Hsh ltac:(constructor; [exact Hio | constructor])) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs Hlast].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton in Hlast. rewrite Forall_singleton.
    exact (lm_good_out_step M K B s _ e Hw Hlast).
  Qed.

  Lemma lm_phi_step_cons (s : lm_st M) (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true ->
    lm_good_out M s (open_seg h ++ [e]) ->
    Forall (lm_good_out M s) (cycles_of h) ->
    Forall (lm_good_out M s) (cycles_of (h ++ [e])).
  Proof using.
    intros Hsh Hio Hgo HF.
    destruct (cycles_of_io h [e] Hsh ltac:(constructor; [exact Hio | constructor])) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs _].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton. exact Hgo.
  Qed.

  Lemma lm_phi_step_power (s : lm_st M) (h : list mobs) (on : bool) :
    Forall (lm_good_out M s) (cycles_of h) ->
    Forall (lm_good_out M s) (cycles_of (h ++ [if on then ObsPowerOff else ObsPowerOn])).
  Proof using.
    intros HF. destruct on.
    - by rewrite cycles_of_off.
    - rewrite cycles_of_on. apply Forall_app. split; [exact HF |].
      apply Forall_singleton. exact (lm_good_out_nil s).
  Qed.
End lm_led.
