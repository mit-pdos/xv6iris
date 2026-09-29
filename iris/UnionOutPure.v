(* ===================================================================== *)
(*  UnionOutPure.v -- THE UNION LEDGER'S PURE CARRIER (cut C9e'; design:  *)
(*  claude-notes/design/union.md section 4).  PURE.                       *)
(*                                                                        *)
(*  [FileOutPure]'s conclusion body and its four steps, at the union      *)
(*  model [UnionDisc.ulmG]: the per-cycle boot states [s0s] of            *)
(*  [FileDisc.file_phi] (the first absent, each later one admissible      *)
(*  against the lines typed in strictly earlier cycles), with the output  *)
(*  claim [LineModel.lm_good_out ulmG] in place of [good_out_f] and the   *)
(*  antecedent the union's discipline [lm_disc ulmG].                     *)
(*                                                                        *)
(*  The one fact the era's FIRST drain reads -- a cycle whose console     *)
(*  wire is empty has received no console input -- is stated once over    *)
(*  any line model ([lm_disc_first_out]).                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import LineModel.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionAdm.
From stdpp Require Import list.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE FIRST DRAIN'S FACT, OVER ANY LINE MODEL                       *)
(* ===================================================================== *)
Section first_out.
  Context (M : lmodel).

  Lemma um_sess_nonnil (ps cs : list nat) (s : lm_st M) (I : list (bv 8)) :
    Forall (fun a => a < length pro_alts) ps -> pro_done ps ->
    lm_sess M ps cs s I <> [].
  Proof using.
    intros HF Hd H. rewrite /lm_sess in H.
    apply app_eq_nil in H as [H _].
    assert (Hne : ps <> []) by (intros ->; by apply Exists_nil in Hd).
    pose proof (pro_of_pos ps HF Hne) as Hpos. rewrite H in Hpos.
    cbn [length] in Hpos. lia.
  Qed.

  Lemma um_disc_open_seg (h : list mobs) :
    trace_shape h true -> lm_disc M h ->
    exists s : lm_st M, lm_st_ok M s /\ lm_disc_seg' M s (open_seg h).
  Proof using.
    intros Hsh Hd.
    destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
    assert (Hin : open_seg h ∈ cycles_of h)
      by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
    apply list_elem_of_lookup in Hin as [i Hi].
    exact (Forall_lookup_1 _ _ _ _ Hd Hi).
  Qed.

  (* under the discipline, a cycle whose console wire is empty has
     received no console input: D1 at the first input byte asks for the
     prologue, and there is no room for it *)
  Lemma lm_disc_first_out (h : list mobs) :
    lm_disc M h -> trace_shape h true ->
    obs_wire Uart0 (open_seg h) = [] -> ins (open_seg h) = [].
  Proof using.
    intros Hd Hsh Hw.
    destruct (decide (ins (open_seg h) = [])) as [? | Hne]; [done | exfalso].
    destruct (um_disc_open_seg h Hsh Hd) as (s & _ & _ & ps & cs & _ & _ & Hall).
    destruct (in_pres_first (open_seg h) Hne) as (p & Hp & Hpi).
    destruct (Hall p Hp) as [[Hpsb Hlt] Hpt].
    rewrite /lm_disc_pt Hpi done_of_nil in Hpt.
    assert (Hwp : obs_wire Uart0 p = []).
    { destruct (proj1 (Forall_forall _ _) (in_pres_prefix_all (open_seg h)) p Hp)
        as [z Hz].
      rewrite Hz obs_wire_app in Hw. by destruct (app_eq_nil _ _ Hw) as [Hz1 _]. }
    rewrite Hwp in Hpt.
    apply (um_sess_nonnil ps cs s [] Hpsb (proj2 (pro_done_rounds ps) ltac:(lia))).
    exact (prefix_nil_inv _ Hpt).
  Qed.
End first_out.

(* ===================================================================== *)
(*  2.  THE UNION'S STATE                                                 *)
(* ===================================================================== *)
Local Notation U := ulmG.
Local Notation UB := (ulm_byte_laws adm_u_g adm_s_on).
Local Notation UK := ulmG_hooks.

(* the union's empty state is well formed: the discipline survives a
   power step *)
Lemma union_st_ok : exists s, lm_st_ok U s.
Proof using. exists ∅. exact fstate_ok_empty. Qed.

(* ===================================================================== *)
(*  3.  THE CONCLUSION AFTER A SYNC (lane SY3-M; sync design section 5): *)
(*      the model's boot relation, which the ledger and the theorem      *)
(*      state (lane SY3-A4; the landed [union_phi], the file's boot      *)
(*      relation without records, is retired): the per-cycle record [o] *)
(*      is FORCED by the cycle's resolution ([UnionAdm.lm_good_sync]),   *)
(*      so the first drain after a completed sync meets [uadm] at that  *)
(*      record through the durability link.                              *)
(* ===================================================================== *)

(* THE CONCLUSION (union design section 4, sync design section 5):
   [FileDisc.file_phi] at the union, each cycle carrying its resolution's
   last completed sync ([UnionAdm.lm_good_sync]), each later boot state
   admissible AT THE LAST COMPLETED SYNC OF THE EARLIER CYCLES
   ([UnionAdm.uadm] at [ulast_before]; with no sync, the landed
   [fadm_boot], [UnionAdm.uadm_srec0]) *)
Definition union_phi_sync (h : list mobs) : Prop :=
  lm_disc U h ->
  exists W : list (fstate * option srec),
    length W = length (cycles_of h)
    /\ (forall w, W !! 0%nat = Some w -> w.1 = ∅)
    /\ (forall k w, W !! S k = Some w ->
          uadm (ulines_before h (S k)) (ulast_before h (snd <$> W) (S k)) w.1)
    /\ Forall2 (fun w seg => lm_good_sync w.1 seg w.2) W (cycles_of h).

Definition union_phi_sync_body (h : list mobs) (W : list (fstate * option srec)) : Prop :=
  length W = length (cycles_of h)
  /\ (forall w, W !! 0%nat = Some w -> w.1 = ∅)
  /\ (forall k w, W !! S k = Some w ->
        uadm (ulines_before h (S k)) (ulast_before h (snd <$> W) (S k)) w.1)
  /\ Forall2 (fun w seg => lm_good_sync w.1 seg w.2) W (cycles_of h).

Lemma union_phi_sync_of_body (h : list mobs) (W : list (fstate * option srec)) :
  (lm_disc U h -> union_phi_sync_body h W) -> union_phi_sync h.
Proof using.
  intros H Hd. destruct (H Hd) as (H1 & H2 & H3 & H4).
  by exists W.
Qed.

(* ...and the per-cycle output claim the top theorem used to state *)
Lemma union_phi_sync_body_good (h : list mobs) (W : list (fstate * option srec)) :
  union_phi_sync_body h W -> Forall2 (lm_good_out U) (fst <$> W) (cycles_of h).
Proof using.
  intros (_ & _ & _ & HF). apply Forall2_fmap_l.
  eapply Forall2_impl; [exact HF |]. intros w seg Hw. exact (lm_good_sync_out _ _ _ Hw).
Qed.

Lemma union_phi_sync_body_nil : union_phi_sync_body [] [].
Proof using.
  rewrite /union_phi_sync_body (_ : cycles_of [] = []); [| reflexivity].
  split_and!.
  - reflexivity.
  - intros s Hs. discriminate.
  - intros k s Hs. discriminate.
  - constructor.
Qed.


(* ...and the same of the whole line list the sync records index *)
Lemma ulines_of_first_out_u (h : list mobs) (e : mobs) (n : nat) :
  lm_disc U h -> trace_shape h true -> is_io e = true ->
  obs_wire Uart0 (open_seg h) = [] ->
  S n = length (cycles_of h) ->
  ulines_of h = ulines_before (h ++ [e]) n.
Proof using.
  intros Hd Hsh Hio Hw Hn.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hlen : length cs = n).
  { rewrite H1 length_app in Hn. cbn [length] in Hn. lia. }
  rewrite (ulines_of_cut h cs (open_seg h) H1 (lm_disc_first_out U h Hd Hsh Hw)).
  rewrite -Hlen. symmetry.
  exact (ulines_before_cut (h ++ [e]) cs (open_seg h ++ [e]) H2).
Qed.

(* the earlier cycles' records are the same after the open cycle's moves *)
Lemma take_snd_snoc (u : list (fstate * option srec)) (x : fstate * option srec) j :
  j <= length u -> take j (snd <$> (u ++ [x])) = take j (snd <$> u).
Proof using.
  intros Hj. rewrite fmap_app take_app_le; [reflexivity | by rewrite length_fmap].
Qed.

(* the earlier cycles are the same after a console event *)
Lemma take_cycles_io (h : list mobs) (e : mobs) (cs : list (list mobs)) j :
  cycles_of h = cs ++ [open_seg h] ->
  cycles_of (h ++ [e]) = cs ++ [open_seg h ++ [e]] ->
  j <= length cs -> take j (cycles_of (h ++ [e])) = take j (cycles_of h).
Proof using.
  intros H1 H2 Hj. rewrite H1 H2 !take_app_le; [reflexivity | lia | lia].
Qed.

(* an event that puts nothing on the console's wire *)
Lemma union_phi_sync_body_step_io (h : list mobs) (e : mobs) (W : list (fstate * option srec)) :
  trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
  union_phi_sync_body h W -> union_phi_sync_body (h ++ [e]) W.
Proof using.
  intros Hsh Hio Hw (Hlen & H0 & Hadm & HF).
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hcs : length W = S (length cs)).
  { rewrite Hlen H1 length_app. cbn [length]. lia. }
  rewrite H1 in HF. rewrite /union_phi_sync_body H2.
  split_and!.
  - rewrite Hcs length_app. cbn [length]. lia.
  - exact H0.
  - intros k w Hs.
    assert (Hk : S k <= length cs) by (apply lookup_lt_Some in Hs; lia).
    rewrite /ulines_before (take_cycles_io h e cs (S k) H1 H2 Hk).
    rewrite (ulast_before_ext (h ++ [e]) h (snd <$> W) (snd <$> W) (S k)
               (take_cycles_io h e cs (S k) H1 H2 Hk) eq_refl).
    exact (Hadm k w Hs).
  - apply Forall2_app_inv_r in HF as (u1 & u2 & Hu1 & Hu2 & ->).
    apply Forall2_app; [exact Hu1 |].
    apply Forall2_cons_inv_r in Hu2 as (y & u3 & Hy & Hu3 & ->).
    apply Forall2_nil_inv_r in Hu3 as ->.
    constructor; [| constructor].
    exact (lm_good_sync_step y.1 (open_seg h) e y.2 Hw Hy).
Qed.

Lemma union_phi_sync_body_off (h : list mobs) (W : list (fstate * option srec)) :
  union_phi_sync_body h W -> union_phi_sync_body (h ++ [ObsPowerOff]) W.
Proof using.
  rewrite /union_phi_sync_body /ulines_before /ulast_before cycles_of_off. done.
Qed.

(* the last completed sync of the cycles so far: its state is the new
   cycle's provisional boot state, admissible at its own record *)
Definition union_rec_now (h : list mobs) (W : list (fstate * option srec)) : srec :=
  ulast_before h (snd <$> W) (length W).

Lemma union_phi_sync_body_on (h : list mobs) (W : list (fstate * option srec)) :
  union_phi_sync_body h W ->
  union_phi_sync_body (h ++ [ObsPowerOn]) (W ++ [((union_rec_now h W).2, None)]).
Proof using.
  intros (Hlen & H0 & Hadm & HF). rewrite /union_phi_sync_body cycles_of_on.
  assert (Htk : forall j, j <= length W ->
                  take j (cycles_of h ++ [[]]) = take j (cycles_of h))
    by (intros j Hj; rewrite take_app_le; [reflexivity | lia]).
  assert (Hos : forall j, j <= length W ->
                  take j (snd <$> (W ++ [((union_rec_now h W).2, None)]))
                  = take j (snd <$> W))
    by (intros j Hj; rewrite fmap_app take_app_le; [reflexivity | rewrite length_fmap; lia]).
  assert (Hcut : forall j, j <= length W ->
                   ulines_before (h ++ [ObsPowerOn]) j = ulines_before h j
                   /\ ulast_before (h ++ [ObsPowerOn])
                        (snd <$> (W ++ [((union_rec_now h W).2, None)])) j
                      = ulast_before h (snd <$> W) j).
  { intros j Hj. rewrite /ulines_before cycles_of_on (Htk j Hj). split; [reflexivity |].
    apply ulast_before_ext; [by rewrite cycles_of_on (Htk j Hj) | exact (Hos j Hj)]. }
  split_and!.
  - rewrite !length_app Hlen. reflexivity.
  - intros w Hs. destruct W as [| y W].
    + cbn in Hs. injection Hs as <-. reflexivity.
    + rewrite -app_comm_cons in Hs. cbn in Hs. exact (H0 w Hs).
  - intros k w Hs.
    destruct (decide (S k < length W)) as [Hk | Hk].
    + rewrite lookup_app_l in Hs; [| lia].
      destruct (Hcut (S k) ltac:(lia)) as [-> ->]. exact (Hadm k w Hs).
    + rewrite lookup_app_r in Hs; [| lia].
      assert (Hje : S k = length W).
      { apply lookup_lt_Some in Hs. cbn [length] in Hs. lia. }
      rewrite Hje Nat.sub_diag in Hs. cbn in Hs. injection Hs as <-.
      destruct (Hcut (S k) ltac:(lia)) as [-> ->]. rewrite Hje. apply uadm_self.
  - apply Forall2_app; [exact HF |].
    constructor; [exact (lm_good_sync_nil _) | constructor].
Qed.

(* the one admissible boot state with no line before it *)
Lemma uadm_nil_srec0 (s : fstate) : uadm [] srec0 s -> s = ∅.
Proof using.
  intros H. apply map_empty. intros N.
  destruct (H N) as [H0 | (ws & sel & Hin & _)]; [exact H0 |].
  by apply elem_of_nil in Hin.
Qed.

Lemma ulast_before_0 h os : ulast_before h os 0 = srec0.
Proof using. reflexivity. Qed.

(* the admissibility the OPEN cycle's entry already carries *)
Lemma union_phi_sync_body_last_adm (h : list mobs) (e : mobs) (u1 : list (fstate * option srec))
    (x : fstate * option srec) :
  trace_shape h true -> is_io e = true ->
  union_phi_sync_body h (u1 ++ [x]) ->
  uadm (ulines_before (h ++ [e]) (length u1)) (ulast_before (h ++ [e]) (snd <$> u1) (length u1))
    x.1.
Proof using.
  intros Hsh Hio (Hlen & H0 & Hadm & _).
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1).
  { rewrite H1 !length_app in Hlen. cbn [length] in Hlen. lia. }
  assert (Hlk : (u1 ++ [x]) !! length u1 = Some x)
    by (rewrite lookup_app_r; [by rewrite Nat.sub_diag | lia]).
  destruct (length u1) as [| n] eqn:Hn.
  - rewrite (H0 x Hlk) ulast_before_0. intros N. left. reflexivity.
  - assert (Hk : S n <= length cs) by lia.
    rewrite /ulines_before (take_cycles_io h e cs (S n) H1 H2 Hk).
    rewrite (ulast_before_ext (h ++ [e]) h (snd <$> u1) (snd <$> (u1 ++ [x])) (S n)
               (take_cycles_io h e cs (S n) H1 H2 Hk)
               (eq_sym (take_snd_snoc u1 x (S n) ltac:(lia)))).
    exact (Hadm n x Hlk).
Qed.

(* THE DRAIN'S STEP, at the era's boot state, which the ledger may
   REPLACE here (the entry it replaces may be provisional), with the
   open cycle's record at the new output *)
Lemma union_phi_sync_body_out (h : list mobs) (b : bv 8) (u1 : list (fstate * option srec))
    (x : fstate * option srec) (s0 : fstate) (o : option srec) :
  trace_shape h true ->
  lm_good_sync s0 (open_seg h ++ [ObsUartOut Uart0 b]) o ->
  uadm (ulines_before (h ++ [ObsUartOut Uart0 b]) (length u1))
    (ulast_before (h ++ [ObsUartOut Uart0 b]) (snd <$> u1) (length u1)) s0 ->
  union_phi_sync_body h (u1 ++ [x]) ->
  union_phi_sync_body (h ++ [ObsUartOut Uart0 b]) (u1 ++ [(s0, o)]).
Proof using.
  intros Hsh Hgo Hadm0 (Hlen & H0 & Hadm & HF).
  destruct (cycles_of_io h [ObsUartOut Uart0 b] Hsh
              (proj2 (Forall_singleton _ _)
                 (eq_refl : is_io (ObsUartOut Uart0 b) = true))) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1).
  { rewrite H1 !length_app in Hlen. cbn [length] in Hlen. lia. }
  rewrite /union_phi_sync_body H2. split_and!.
  - rewrite !length_app. rewrite H1 !length_app in Hlen. exact Hlen.
  - intros w Hs. destruct u1 as [| y u1].
    + cbn in Hs. injection Hs as <-. cbn [length] in Hadm0.
      apply uadm_nil_srec0. revert Hadm0. rewrite ulast_before_0 /ulines_before take_0.
      cbn [fmap list_fmap concat]. done.
    + apply (H0 w). exact Hs.
  - intros k w Hs.
    destruct (decide (S k < length u1)) as [Hk | Hk].
    + rewrite lookup_app_l in Hs; [| lia].
      rewrite /ulines_before (take_cycles_io h _ cs (S k) H1 H2 ltac:(lia)).
      rewrite (ulast_before_ext _ h _ (snd <$> (u1 ++ [x])) (S k)
                 (take_cycles_io h _ cs (S k) H1 H2 ltac:(lia))
                 (eq_trans (take_snd_snoc u1 (s0, o) (S k) ltac:(lia))
                    (eq_sym (take_snd_snoc u1 x (S k) ltac:(lia))))).
      apply (Hadm k w). rewrite lookup_app_l; [exact Hs | lia].
    + rewrite lookup_app_r in Hs; [| lia].
      assert (Hje : S k = length u1).
      { apply lookup_lt_Some in Hs. cbn [length] in Hs. lia. }
      rewrite Hje Nat.sub_diag in Hs. cbn in Hs. injection Hs as <-.
      rewrite Hje.
      rewrite (ulast_before_ext _ _ _ (snd <$> u1) (length u1) eq_refl
                 (take_snd_snoc u1 (s0, o) (length u1) ltac:(lia))).
      exact Hadm0.
  - rewrite H1 in HF.
    destruct (Forall2_app_inv _ u1 [x] cs [open_seg h] (eq_sym Hcs) HF) as [Hv1 _].
    apply Forall2_app; [exact Hv1 |].
    constructor; [exact Hgo | constructor].
Qed.

(* THE LEDGER'S DRAIN STEP, PURELY: at the era's FIRST drain the state's
   admissibility comes from the witness read against the whole history's
   line list, which is then the earlier cycles' ([ulines_of_first_out_u]),
   at the last completed sync of the earlier cycles; at a LATER drain the
   state is the one already fixed.  The open cycle's record is the new
   output's ([o]). *)
Lemma union_phi_sync_body_drain (h : list mobs) (b : bv 8) (W : list (fstate * option srec))
    (s0 : fstate) (o : option srec) :
  trace_shape h true -> lm_disc U h ->
  lm_good_sync s0 (open_seg h ++ [ObsUartOut Uart0 b]) o ->
  uadm (ulines_of h) (ulast_before h (snd <$> W) (pred (length W))) s0 ->
  (obs_wire Uart0 (open_seg h) <> [] -> exists u1 o0, W = u1 ++ [(s0, o0)]) ->
  union_phi_sync_body h W ->
  union_phi_sync_body (h ++ [ObsUartOut Uart0 b]) (removelast W ++ [(s0, o)]).
Proof using.
  intros Hsh Hd Hgo Hadm Hlast Hb.
  destruct (cycles_of_io h [ObsUartOut Uart0 b] Hsh
              (proj2 (Forall_singleton _ _)
                 (eq_refl : is_io (ObsUartOut Uart0 b) = true)))
    as (cs & H1 & H2).
  assert (Hne : W <> []).
  { intros Hz. destruct Hb as (Hlen & _).
    rewrite Hz H1 length_app in Hlen. cbn [length] in Hlen. lia. }
  destruct (fop_snoc_inv W Hne) as (u1 & x & ->).
  rewrite (epu_removelast_snoc u1 x).
  apply (union_phi_sync_body_out h b u1 x s0 o Hsh Hgo); [| exact Hb].
  assert (Hlen : S (length u1) = length (cycles_of h)).
  { destruct Hb as (Hl & _). rewrite length_app in Hl. cbn [length] in Hl. lia. }
  assert (Hcs : length cs = length u1).
  { rewrite H1 length_app in Hlen. cbn [length] in Hlen. lia. }
  destruct (decide (obs_wire Uart0 (open_seg h) = [])) as [Hw | Hw].
  - rewrite -(ulines_of_first_out_u h (ObsUartOut Uart0 b) (length u1)
                Hd Hsh eq_refl Hw Hlen).
    rewrite (_ : pred (length (u1 ++ [x])) = length u1) in Hadm;
      [| rewrite length_app /=; lia].
    rewrite (ulast_before_ext _ h (snd <$> u1) (snd <$> (u1 ++ [x])) (length u1)
               (take_cycles_io h _ cs (length u1) H1 H2 ltac:(lia))
               (eq_sym (take_snd_snoc u1 x (length u1) ltac:(lia)))).
    exact Hadm.
  - assert (Hx : x.1 = s0).
    { destruct (Hlast Hw) as (u2 & o0 & Hu2).
      destruct (app_inj_2 u1 u2 [x] [(s0, o0)] eq_refl Hu2) as [_ Hxx].
      by injection Hxx as ->. }
    rewrite -Hx.
    exact (union_phi_sync_body_last_adm h (ObsUartOut Uart0 b) u1 x Hsh eq_refl Hb).
Qed.
