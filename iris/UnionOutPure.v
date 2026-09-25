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
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import PipesLedPure.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import UnionDisc.
Require Import UnionDiscDec.
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
    apply elem_of_list_lookup in Hin as [i Hi].
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
(*  2.  THE UNION'S CONCLUSION, AND ITS BODY                              *)
(* ===================================================================== *)
Local Notation U := ulmG.
Local Notation UB := (ulm_byte_laws adm_u_g).
Local Notation UK := ulmG_hooks.

(* THE CONCLUSION (design section 4): [FileDisc.file_phi] at the union *)
Definition union_phi (h : list mobs) : Prop :=
  lm_disc U h ->
  exists s0s : list fstate,
    length s0s = length (cycles_of h)
    /\ (forall s, s0s !! 0%nat = Some s -> s = ∅)
    /\ (forall k s, s0s !! S k = Some s ->
          fadm_boot (echof_lines_before h (S k)) s)
    /\ Forall2 (lm_good_out U) s0s (cycles_of h).

Definition union_phi_body (h : list mobs) (s0s : list fstate) : Prop :=
  length s0s = length (cycles_of h)
  /\ (forall s, s0s !! 0%nat = Some s -> s = ∅)
  /\ (forall k s, s0s !! S k = Some s ->
        fadm_boot (echof_lines_before h (S k)) s)
  /\ Forall2 (lm_good_out U) s0s (cycles_of h).

Lemma union_phi_of_body (h : list mobs) (s0s : list fstate) :
  (lm_disc U h -> union_phi_body h s0s) -> union_phi h.
Proof using.
  intros H Hd. destruct (H Hd) as (H1 & H2 & H3 & H4).
  by exists s0s.
Qed.

Lemma union_phi_body_nil : union_phi_body [] [].
Proof using.
  rewrite /union_phi_body (_ : cycles_of [] = []); [| reflexivity].
  split_and!.
  - reflexivity.
  - intros s Hs. discriminate.
  - intros k s Hs. discriminate.
  - constructor.
Qed.

(* the union's empty state is well formed: the discipline survives a
   power step *)
Lemma union_st_ok : exists s, lm_st_ok U s.
Proof using. exists ∅. exact fstate_ok_empty. Qed.

(* the era's first drain: the ledger's line list is the list of lines
   typed in the cycles strictly before the open one *)
Lemma efl_of_first_out_u (h : list mobs) (e : mobs) (n : nat) :
  lm_disc U h -> trace_shape h true -> is_io e = true ->
  obs_wire Uart0 (open_seg h) = [] ->
  S n = length (cycles_of h) ->
  echof_lines_of h = echof_lines_before (h ++ [e]) n.
Proof using.
  intros Hd Hsh Hio Hw Hn.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hlen : length cs = n).
  { rewrite H1 length_app in Hn. cbn [length] in Hn. lia. }
  rewrite (echof_lines_of_cut h cs (open_seg h) H1
             (lm_disc_first_out U h Hd Hsh Hw)).
  rewrite -Hlen. symmetry.
  exact (echof_lines_before_cut (h ++ [e]) cs (open_seg h ++ [e]) H2).
Qed.

(* an event that puts nothing on the console's wire *)
Lemma union_phi_body_step_io (h : list mobs) (e : mobs) (s0s : list fstate) :
  trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
  union_phi_body h s0s -> union_phi_body (h ++ [e]) s0s.
Proof using.
  intros Hsh Hio Hw (Hlen & H0 & Hadm & HF).
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  rewrite H1 in Hlen, HF. rewrite /union_phi_body H2.
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
    exact (lm_good_out_step U UK UB y (open_seg h) e Hw Hy).
Qed.

Lemma union_phi_body_off (h : list mobs) (s0s : list fstate) :
  union_phi_body h s0s -> union_phi_body (h ++ [ObsPowerOff]) s0s.
Proof using.
  rewrite /union_phi_body /echof_lines_before cycles_of_off. done.
Qed.

Lemma union_phi_body_on (h : list mobs) (s0s : list fstate) :
  union_phi_body h s0s -> union_phi_body (h ++ [ObsPowerOn]) (s0s ++ [∅]).
Proof using.
  intros (Hlen & H0 & Hadm & HF). rewrite /union_phi_body cycles_of_on.
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
      injection Hs as <-. apply fadm_boot_empty.
  - apply Forall2_app; [exact HF |].
    constructor; [exact (lm_good_out_nil U ∅) | constructor].
Qed.

(* the admissibility the OPEN cycle's entry already carries *)
Lemma union_phi_body_last_adm (h : list mobs) (e : mobs) (u1 : list fstate)
    (x : fstate) :
  trace_shape h true -> is_io e = true ->
  union_phi_body h (u1 ++ [x]) ->
  fadm_boot (echof_lines_before (h ++ [e]) (length u1)) x.
Proof using.
  intros Hsh Hio (Hlen & H0 & Hadm & _).
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1).
  { rewrite H1 !length_app in Hlen. cbn [length] in Hlen. lia. }
  assert (Hlk : (u1 ++ [x]) !! length u1 = Some x)
    by (rewrite lookup_app_r; [by rewrite Nat.sub_diag | lia]).
  destruct (length u1) as [| n] eqn:Hn.
  - rewrite (H0 x Hlk). apply fadm_boot_empty.
  - assert (Hcut : echof_lines_before (h ++ [e]) (S n)
                   = echof_lines_before h (S n)).
    { rewrite /echof_lines_before H1 H2 !take_app_le; [reflexivity | lia | lia]. }
    rewrite Hcut. exact (Hadm n x Hlk).
Qed.

(* THE DRAIN'S STEP, at the era's boot state, which the ledger may
   REPLACE here (the entry it replaces may be provisional) *)
Lemma union_phi_body_out (h : list mobs) (b : bv 8) (u1 : list fstate)
    (x s0 : fstate) :
  trace_shape h true ->
  lm_good_out U s0 (open_seg h ++ [ObsUartOut Uart0 b]) ->
  fadm_boot (echof_lines_before (h ++ [ObsUartOut Uart0 b]) (length u1)) s0 ->
  union_phi_body h (u1 ++ [x]) ->
  union_phi_body (h ++ [ObsUartOut Uart0 b]) (u1 ++ [s0]).
Proof using.
  intros Hsh Hgo Hadm0 (Hlen & H0 & Hadm & HF).
  destruct (cycles_of_io h [ObsUartOut Uart0 b] Hsh
              (proj2 (Forall_singleton _ _)
                 (eq_refl : is_io (ObsUartOut Uart0 b) = true))) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1).
  { rewrite H1 !length_app in Hlen. cbn [length] in Hlen. lia. }
  assert (Hcut : forall j, (j <= length u1)%nat ->
                   echof_lines_before (h ++ [ObsUartOut Uart0 b]) j
                   = echof_lines_before h j).
  { intros j Hj. rewrite /echof_lines_before H1 H2.
    rewrite !take_app_le; [reflexivity | lia | lia]. }
  rewrite /union_phi_body H2. split_and!.
  - rewrite !length_app. rewrite H1 !length_app in Hlen. exact Hlen.
  - intros s Hs. destruct u1 as [| y u1].
    + cbn in Hs. injection Hs as <-. cbn [length] in Hadm0.
      apply fadm_boot_nil. revert Hadm0. rewrite /echof_lines_before take_0.
      cbn [fmap list_fmap concat]. done.
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
    destruct (Forall2_app_inv (lm_good_out U) u1 [x] cs [open_seg h] (eq_sym Hcs) HF)
      as [Hv1 _].
    apply Forall2_app; [exact Hv1 |].
    constructor; [exact Hgo | constructor].
Qed.

(* THE LEDGER'S DRAIN STEP, PURELY: at the era's FIRST drain the state's
   admissibility comes from the deed's witness read against the whole
   history's line list, which is then the earlier cycles' ([efl_of_first_out_u]);
   at a LATER drain the state is the one already fixed *)
Lemma union_phi_body_drain (h : list mobs) (b : bv 8) (s0s : list fstate)
    (s0 : fstate) :
  trace_shape h true -> lm_disc U h ->
  lm_good_out U s0 (open_seg h ++ [ObsUartOut Uart0 b]) ->
  fadm_boot (echof_lines_of h) s0 ->
  (obs_wire Uart0 (open_seg h) <> [] -> exists u1, s0s = u1 ++ [s0]) ->
  union_phi_body h s0s ->
  union_phi_body (h ++ [ObsUartOut Uart0 b]) (removelast s0s ++ [s0]).
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
  apply (union_phi_body_out h b u1 x s0 Hsh Hgo); [| exact Hb].
  destruct (decide (obs_wire Uart0 (open_seg h) = [])) as [Hw | Hw].
  - assert (Hlen : S (length u1) = length (cycles_of h)).
    { destruct Hb as (Hl & _). rewrite length_app in Hl. cbn [length] in Hl. lia. }
    rewrite -(efl_of_first_out_u h (ObsUartOut Uart0 b) (length u1)
                Hd Hsh eq_refl Hw Hlen).
    exact Hadm.
  - assert (Hx : x = s0).
    { destruct (Hlast Hw) as (u2 & Hu2).
      destruct (app_inj_2 u1 u2 [x] [s0] eq_refl Hu2) as [_ Hxx].
      by injection Hxx. }
    rewrite -Hx.
    exact (union_phi_body_last_adm h (ObsUartOut Uart0 b) u1 x Hsh eq_refl Hb).
Qed.
