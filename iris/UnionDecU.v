(* ===================================================================== *)
(* UnionDecU.v -- THE UNION DISCIPLINE IS DECIDABLE (cut C9e-dec; design: *)
(* claude-notes/design/union.md, review item S2; filenames.md seam (a)).  *)
(* Pure.                                                                  *)
(*                                                                        *)
(*  [lm_disc_ulmG_dec : Decision (lm_disc ulmG h)], constructively, so    *)
(*  the union ledger's taint counter can sit at [decide (lm_disc ulmG h)] *)
(*  with no excluded-middle axiom.  Nothing here is meant to run.         *)
(*                                                                        *)
(*  AT EVERY FILTER STAGE LIST (grep-pipes.md cut G4).  The decider is   *)
(*  proved once for any admission [ud_disc_dec] (what it needs of one:    *)
(*  [ud_adm]) and instantiated at the union application's [adm_u_g]      *)
(*  (every stage [cat] or [grep w], cut G8): [lm_disc_ulmG_dec].          *)
(*                                                                        *)
(*  WHY IT IS NOT [FileDiscDec] + [PipesDecE] (review S2).  The state     *)
(*  feeds the range condition: at a [cat f | cat^n] line [uok] reads the  *)
(*  round's content through [line_blocks], so                            *)
(*   - the candidate codes of a round depend on the state that round     *)
(*     starts in, and the resolutions are a DEPENDENT product ([ualts_dep]:   *)
(*     each round's candidates at the state the earlier choices leave);  *)
(*   - the coverage-ending outputs ([umerge]) gain the cat producer's    *)
(*     three diagnostics ([cat_dg_open f], [cat_dg_write], [dg_execR]);  *)
(*     [umerge]'s [exists s] is taken at the state holding an empty [f]  *)
(*     ([umerge_spec]);                                                   *)
(*   - the BOOT STATE is no longer printed contiguously: a pipeline's    *)
(*     last cat prints a PREFIX of a file (the ruled corner B)           *)
(*     interleaved with the other stages' diagnostics.  So the boot      *)
(*     state is canonicalised by TRUNCATION ([blocks_trunc],             *)
(*     [terms_trunc]): a run at content [b0] stays a run, with the same  *)
(*     console streams, at any prefix of [b0] its printed content fits  *)
(*     in (at a grep too: each pipe's new content is related to its old  *)
(*     one, not a uniform cut of it, section 4) -- and the longest such  *)
(*     printed prefix is a SUBSEQUENCE of the segment's wire.  If [b0]   *)
(*     itself is not one, no checked round printed the file whole ([cat  *)
(*     N] alone does, contiguously), and the era is the one at the       *)
(*     longest printed prefix.  The one round the wire never checks (the *)
(*     last line, typed as the last input byte) is re-resolved to the    *)
(*     silent round, which ends no coverage.                              *)
(*                                                                        *)
(*  THE STATE IS A MAP OF FILES (filenames.md cut W1), and the            *)
(*  canonicalisation works ONE NAME AT A TIME through seam (a): a round  *)
(*  moves only its line's file ([ustep_local], [ustep_ins_cases]), and   *)
(*  admits and prints reading only that file ([uok_local],               *)
(*  [ucont_local]).  A file no line names is dropped ([disc_agree]); each *)
(*  named file's content is cut with every other file carried along      *)
(*  ([u_canon_name]); the candidates are the PRODUCT over the named       *)
(*  files of the wire's subsequences ([prod_maps], [scandsU]), a finite  *)
(*  list that is only ever decided.                                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel LineModelLinks.
Require Import ProgTree PipesPair PipesDisc PipesDiscDec PipesDecE.
Require PipeDisc.
Require Import FileState FileDisc FileDiscDec.
Require Import UnionDisc UnionDiscDec.
Require GrepFilt.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Local Notation fc0 := (files_of {[txt_a := []]}).

Ltac ud_elem :=
  solve [ repeat first [ apply elem_of_list_here | apply elem_of_list_further ] ].

(* ===================================================================== *)
(*  0.  LIST FACTS                                                        *)
(* ===================================================================== *)

Fixpoint ud_sublists {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: l' => (cons x <$> ud_sublists l') ++ ud_sublists l'
  end.

Lemma elem_of_ud_sublists {A} (m l : list A) : m `sublist_of` l -> m ∈ ud_sublists l.
Proof using.
  induction 1 as [| x l1 l2 _ IH | x l1 l2 _ IH]; cbn [ud_sublists].
  - apply elem_of_list_here.
  - apply elem_of_app. left. apply elem_of_list_fmap. by exists l1.
  - apply elem_of_app. right. exact IH.
Qed.

Lemma ud_infixed_sublist {A} (m l : list A) : infixed m l -> m `sublist_of` l.
Proof using. intros (u & v & ->). apply sublist_inserts_l, sublist_inserts_r. reflexivity. Qed.

Lemma ud_infixed_trans {A} (m l l' : list A) : infixed m l -> infixed l l' -> infixed m l'.
Proof using.
  intros (u & v & ->) (u' & v' & ->). exists (u' ++ u), (v ++ v'). by rewrite -!app_assoc.
Qed.

Lemma ud_infixed_mid {A} (P : list A) (x : A) (m B C : list A) :
  infixed m (P ++ x :: ((m ++ B) ++ C)).
Proof using. exists (P ++ [x]), (B ++ C). by rewrite -!app_assoc. Qed.

Lemma ud_prefix_take (k : nat) (D L : bytes) : D `prefix_of` L -> take k D `prefix_of` take k L.
Proof using. intros [z ->]. rewrite take_app. by apply prefix_app_r. Qed.

Lemma ud_prefix_take_ge (k : nat) (D L : bytes) :
  D `prefix_of` L -> length D <= k -> D `prefix_of` take k L.
Proof using.
  intros [z ->] Hk. rewrite take_app (take_ge D k Hk). by apply prefix_app_r.
Qed.

(* every stream of a merge is a subsequence of it *)
Lemma merge_all_sublist ss b : merge_all ss b -> forall x, x ∈ ss -> x `sublist_of` b.
Proof using.
  induction 1 as [ss HF | ss i x s b Hi Hm IH]; intros y Hy.
  - rewrite Forall_forall in HF. rewrite (HF y Hy). apply sublist_nil_l.
  - apply elem_of_list_lookup in Hy as [j Hj].
    destruct (decide (j = i)) as [-> | Hne].
    + rewrite Hi in Hj. injection Hj as <-. apply sublist_skip. apply IH.
      apply elem_of_list_lookup. exists i. apply list_lookup_insert.
      exact (lookup_lt_Some _ _ _ Hi).
    + apply sublist_cons. apply IH. apply elem_of_list_lookup. exists j.
      rewrite list_lookup_insert_ne; [exact Hj | lia].
Qed.

(* a content's prefix is a content *)
Lemma fcont_ok_prefix (P b : bytes) : P `prefix_of` b -> fcont_ok b -> fcont_ok P.
Proof using.
  intros [z ->] [HF | (v & HF & Hv)].
  - left. apply Forall_app in HF as [HF _]. exact HF.
  - destruct (fdd_snoc_inv z) as [-> | (z' & y & ->)].
    + right. exists v. rewrite app_nil_r in Hv. split; [exact HF | exact Hv].
    + left. rewrite app_assoc in Hv. apply app_inj_tail in Hv as [Hv _].
      rewrite -Hv in HF. apply Forall_app in HF as [HF _]. exact HF.
Qed.

(* ===================================================================== *)
(*  1.  THE COVERAGE-ENDING OUTPUTS, DECIDED                              *)
(*                                                                        *)
(*  A terminal run's console streams are diagnostics only, at every       *)
(*  content: the producer's ([ud_prod]: echo's exec failure or nothing; *)
(*  cat f's exec failure, nothing, its write error or its open failure), *)
(*  the middle stages' ([umidok]: a cat's exec failure, nothing or its    *)
(*  write error; a grep's exec failure or nothing -- a grep prints no     *)
(*  diagnostic of its own) and the failing node's [fork] line.  Each is   *)
(*  realisable at [Some []], where the file is present and empty -- so   *)
(*  [umerge]'s [exists s] is [s = Some []].                               *)
(*                                                                        *)
(*  THE ADMISSION IS A PARAMETER ([ud_adm]): which producers it admits    *)
(*  (echo, and cat at the model's file), whether it admits grep stages    *)
(*  ([gp]), and that it admits every chain of cats -- and, at [gp], of    *)
(*  cats and greps of one pattern [gpat] -- behind either producer, which *)
(*  is what realises every checked shape.                                  *)
(* ===================================================================== *)

Definition ud_prod (p : producer) : list bytes :=
  match p with
  | PrEcho _ => [PipeDisc.dg_execL; []]
  | PrCatF f => [PipeDisc.dg_execR; []; cat_dg_write; cat_dg_open f]
  end.

Lemma ud_prod_cons fc L p so : stage_out fc L (SProd p) so -> so_cons so ∈ ud_prod p.
Proof using.
  intros H. destruct p as [ws | f]; inversion H; subst; cbn [so_cons st_dg_exec ud_prod]; ud_elem.
Qed.

(* THE CLASS NAMES A WIRE CAN SHOW (cut W4).  A refused open's
   diagnostic [cat_dg_open g] names a class name [g], and a wire [u]
   shows at most a prefix of that diagnostic -- a sublist of [u], whose
   name part completes in the class by one of [FileClass.txt_sfx].  So
   the names worth trying at [u] are finitely many ([gcands u]); the list
   is only ever decided. *)
Definition gcands (u : bytes) : list bytes :=
  filter (fun g => uname g)
    (concat ((fun w => (fun z => w ++ z) <$> txt_sfx) <$> ud_sublists u)).

Lemma gcands_uname g u : g ∈ gcands u -> uname g.
Proof using. intros H. apply elem_of_list_filter in H as [H _]. exact H. Qed.

Lemma gcands_of w z u :
  w `sublist_of` u -> z ∈ txt_sfx -> uname (w ++ z) -> (w ++ z) ∈ gcands u.
Proof using.
  intros Hw Hz Hu. apply elem_of_list_filter. split; [exact Hu |].
  apply elem_of_list_In, in_concat. exists ((fun z => w ++ z) <$> txt_sfx). split.
  - apply elem_of_list_In, elem_of_list_fmap. exists w.
    split; [reflexivity | exact (elem_of_ud_sublists w u Hw)].
  - apply elem_of_list_In, elem_of_list_fmap. exists z. split; [reflexivity | exact Hz].
Qed.

Lemma txt_sfx_nil : drop 4 txt_ext ∈ txt_sfx.
Proof using. apply elem_of_list_here. Qed.

Lemma gcands_self g u : uname g -> g `sublist_of` u -> g ∈ gcands u.
Proof using.
  intros Hg Hs. pose proof (gcands_of g (drop 4 txt_ext) u Hs txt_sfx_nil) as H.
  change (drop 4 txt_ext) with (@nil (bv 8)) in H. rewrite app_nil_r in H. exact (H Hg).
Qed.

Definition hdr_open : bytes := sb "cat: cannot open "%string.

Lemma cat_dg_open_eq g : cat_dg_open g = hdr_open ++ g ++ [wl_nl].
Proof using. reflexivity. Qed.

Lemma ud_take_prefix (n : nat) (l : bytes) : take n l `prefix_of` l.
Proof using. exists (drop n l). by rewrite take_drop. Qed.

(* the part of a refused open's diagnostic a wire shows is the part of a
   diagnostic at a name [gcands] tries *)
Lemma open_trunc (g v u : bytes) :
  uname g -> v `prefix_of` cat_dg_open g -> v `sublist_of` u ->
  exists g', g' ∈ gcands u /\ v `prefix_of` cat_dg_open g'.
Proof using.
  intros Hg Hv Hvu. rewrite cat_dg_open_eq in Hv.
  assert (Hvt : v = take (length v) (hdr_open ++ g ++ [wl_nl])).
  { destruct Hv as [r Hr]. rewrite Hr take_app_length. reflexivity. }
  assert (Hlen : (length v <= length hdr_open + length g + 1)%nat).
  { destruct Hv as [r Hr]. apply (f_equal length) in Hr. rewrite !length_app in Hr.
    cbn [length] in Hr. lia. }
  rewrite take_app in Hvt.
  destruct (decide (length v <= length hdr_open)%nat) as [Hle | Hgt].
  - exists txt_a. split.
    + change txt_a with ([] ++ txt_a).
      apply gcands_of; [apply sublist_nil_l | | exact txt_a_name].
      do 5 apply elem_of_list_further. apply elem_of_list_here.
    + replace (length v - length hdr_open)%nat with 0%nat in Hvt by lia.
      rewrite take_0 app_nil_r in Hvt. rewrite cat_dg_open_eq Hvt.
      apply prefix_app_r. apply ud_take_prefix.
  - rewrite (take_ge hdr_open) in Hvt; [| lia].
    destruct (decide (length v - length hdr_open <= length g)%nat) as [Hin | Hout].
    + rewrite take_app in Hvt.
      replace (length v - length hdr_open - length g)%nat with 0%nat in Hvt by lia.
      rewrite take_0 app_nil_r in Hvt.
      set (w := take (length v - length hdr_open) g) in *.
      assert (Hwu : w `sublist_of` u).
      { etrans; [| exact Hvu]. rewrite Hvt. apply sublist_inserts_l. reflexivity. }
      destruct (txt_prefix_complete w g Hg (ud_take_prefix _ g)) as (z & Hz & Hwz).
      exists (w ++ z). split; [exact (gcands_of w z u Hwu Hz Hwz) |].
      rewrite cat_dg_open_eq Hvt. apply prefix_app. rewrite -app_assoc.
      apply prefix_app_r. reflexivity.
    + assert (Hvw : v = hdr_open ++ g ++ [wl_nl]).
      { rewrite Hvt take_ge; [reflexivity |]. rewrite length_app. cbn [length]. lia. }
      exists g. split.
      * apply gcands_self; [exact Hg |]. etrans; [| exact Hvu]. rewrite Hvw.
        apply sublist_inserts_l, sublist_inserts_r. reflexivity.
      * rewrite cat_dg_open_eq Hvw. reflexivity.
Qed.

(* A PREFIX OF A TERMINAL BLOCK READS EACH STREAM ONLY AS FAR AS IT SHOWS
   IT.  Either every stream was read whole, or the reading stopped short
   of the prompt at some stream-wise prefix, each shown on the wire --
   and then any streams those prefixes extend read the wire just as
   well. *)
Lemma pmt_trunc (W : list bytes) (pr s u : bytes) :
  pde_pmt W pr s u ->
  Forall (fun w => w `sublist_of` u) W
  \/ exists W0, Forall2 prefix W0 W /\ Forall (fun w => w `sublist_of` u) W0
                /\ pde_pmt W0 [] s u.
Proof using.
  induction 1 as [W pr s | W pr s i x t u Hi H IH | W pr s x u HF H IH | W pr s x u H IH].
  - right. exists ((fun _ => []) <$> W). split_and!.
    + apply Forall2_same_length_lookup. split; [by rewrite length_fmap |].
      intros j a b Ha Hb. rewrite list_lookup_fmap Hb in Ha. injection Ha as <-.
      apply prefix_nil.
    + apply Forall_fmap. apply Forall_forall. intros w _. apply sublist_nil_l.
    + constructor.
  - assert (Hlt : (i < length W)%nat) by exact (lookup_lt_Some _ _ _ Hi).
    destruct IH as [HF | (W0 & HP & HS & H0)].
    + left. apply Forall_lookup. intros j w Hj.
      destruct (decide (j = i)) as [-> | Hne].
      * rewrite Hi in Hj. injection Hj as <-. apply sublist_skip.
        exact (Forall_lookup_1 _ _ _ _ HF (list_lookup_insert W i t Hlt)).
      * apply sublist_cons. refine (Forall_lookup_1 _ _ j _ HF _).
        rewrite list_lookup_insert_ne; [exact Hj | lia].
    + right.
      pose proof (Forall2_length _ _ _ HP) as Hl0.
      rewrite length_insert in Hl0.
      apply Forall2_same_length_lookup in HP as [_ HP].
      assert (Hi0 : (i < length W0)%nat) by (rewrite Hl0; exact Hlt).
      destruct (lookup_lt_is_Some_2 W0 i Hi0) as [v Hv].
      assert (Hvt : v `prefix_of` t) by exact (HP i v t Hv (list_lookup_insert W i t Hlt)).
      exists (<[i := x :: v]> W0). split_and!.
      * apply Forall2_same_length_lookup. split; [by rewrite length_insert |].
        intros j a b Ha Hb. destruct (decide (j = i)) as [-> | Hne].
        -- rewrite list_lookup_insert in Ha; [| lia]. injection Ha as <-.
           rewrite Hi in Hb. injection Hb as <-. by apply prefix_cons.
        -- rewrite list_lookup_insert_ne in Ha; [| lia].
           apply (HP j a b Ha). rewrite list_lookup_insert_ne; [exact Hb | lia].
      * apply Forall_lookup. intros j a Ha. destruct (decide (j = i)) as [-> | Hne].
        -- rewrite list_lookup_insert in Ha; [| lia]. injection Ha as <-.
           apply sublist_skip. exact (Forall_lookup_1 _ _ _ _ HS Hv).
        -- rewrite list_lookup_insert_ne in Ha; [| lia].
           apply sublist_cons. exact (Forall_lookup_1 _ _ _ _ HS Ha).
      * apply (pmt_w _ [] s i x v u); [rewrite list_lookup_insert; [reflexivity | lia] |].
        rewrite list_insert_insert list_insert_id; [exact H0 | exact Hv].
  - left. eapply Forall_impl; [exact HF |]. intros w ->. apply sublist_nil_l.
  - destruct IH as [HF | (W0 & HP & HS & H0)].
    + left. eapply Forall_impl; [exact HF |]. intros w Hw. by apply sublist_cons.
    + right. exists W0. split_and!; [exact HP | | by apply pmt_s].
      eapply Forall_impl; [exact HS |]. intros w Hw. by apply sublist_cons.
Qed.

Lemma pmt_ext (W0 : list bytes) (s u : bytes) :
  pde_pmt W0 [] s u -> forall W pr, Forall2 prefix W0 W -> pde_pmt W pr s u.
Proof using.
  intros H. remember (@nil (bv 8)) as e eqn:He. revert He.
  induction H as [W0 e s | W0 e s i x t u Hi H IH | W0 e s x u HF H IH | W0 e s x u H IH];
    intros He W pr HP.
  - constructor.
  - destruct (Forall2_lookup_l _ _ _ i (x :: t) HP Hi) as (w & Hw & [r ->]).
    apply (pmt_w W pr s i x (t ++ r) u); [exact Hw |].
    apply IH; [exact He |]. apply Forall2_insert; [exact HP | by exists r].
  - discriminate He.
  - apply pmt_s. exact (IH He W pr HP).
Qed.

Lemma pmt_stray_trunc (W : list bytes) (pr s u : bytes) :
  pde_pmt W pr s u -> exists sp, sp `prefix_of` s /\ sp `sublist_of` u /\ pde_pmt W pr sp u.
Proof using.
  induction 1 as [W pr s | W pr s i x t u Hi H IH | W pr s x u HF H IH | W pr s x u H IH].
  - exists []. split_and!; [apply prefix_nil | apply sublist_nil_l | constructor].
  - destruct IH as (sp & Hp & Hs & H'). exists sp.
    split_and!; [exact Hp | by apply sublist_cons | exact (pmt_w _ _ _ i x t u Hi H')].
  - destruct IH as (sp & Hp & Hs & H'). exists sp.
    split_and!; [exact Hp | by apply sublist_cons | exact (pmt_p _ _ _ x u HF H')].
  - destruct IH as (sp & Hp & Hs & H'). exists (x :: sp).
    split_and!; [by apply prefix_cons | by apply sublist_skip | exact (pmt_s _ _ _ x u H')].
Qed.

(* the diagnostics of every producer the union admits, at a wire: the
   four fixed ones and a refused open at every name [gcands] tries *)
Definition prodU (u : bytes) : list bytes :=
  [[]; PipeDisc.dg_execL; PipeDisc.dg_execR; cat_dg_write] ++ (cat_dg_open <$> gcands u).

(* the nonempty middle streams: a cat's two, and with grep stages ([gp])
   a grep's exec failure *)
Definition umo (gp : bool) : list bytes := pde_mo ++ (if gp then [dg_execG] else []).

Definition umidok (gp : bool) (m : bytes) : Prop := m = [] \/ m ∈ umo gp.

(* THE CHECKER: [PipesDecE.pde_mergeb] with the cat producer's streams and
   the middle streams [umo gp] *)
Definition umergeb (gp : bool) (u : bytes) : bool :=
  existsb (fun pc => existsb (fun s => pde_chk (umo gp) [pc; dg_fork_b] true s u_prompt u)
                      ([] :: umo gp)) (prodU u)
  || existsb (fun s => pde_chk (umo gp) [dg_fork_b] false s u_prompt u) (prodU u).

Lemma umo_grep (gp : bool) m : m ∈ (if gp then [dg_execG] else []) -> gp = true /\ m = dg_execG.
Proof using.
  destruct gp; [intros Hm; split; [reflexivity | exact (proj1 (elem_of_list_singleton _ _) Hm)] |].
  intros Hm. by apply elem_of_nil in Hm.
Qed.

Lemma umergeb_prompt gp : umergeb gp u_prompt = false.
Proof using. destruct gp; vm_compute; reflexivity. Qed.

(* the state the coverage-ending outputs are realised at *)
Lemma fstate_ok_nil1 : fstate_ok {[txt_a := []]}.
Proof using.
  rewrite /fstate_ok map_Forall_singleton. split; [exact txt_a_name | left; constructor].
Qed.

(* WHAT THE DECIDER NEEDS OF AN ADMISSION *)
Record ud_adm (adm : pline' -> bool) (gp : bool) (gpat : bytes) : Prop := {
  uda_catf : forall g fs, adm (LPipes (PrCatF g) fs) = true -> uname g;
  uda_filt : forall p fs, adm (LPipes p fs) = true -> Forall (fun F => gp = true \/ F = FCat) fs;
  uda_real : forall p fs,
    p = PrEcho [] \/ (exists g, p = PrCatF g /\ uname g) ->
    Forall (fun F => F = FCat \/ (gp = true /\ F = FGrep gpat)) fs -> adm (LPipes p fs) = true
}.

Section umerge.
  Context (adm : pline' -> bool) (gp : bool) (gpat : bytes).
  Hypothesis Hadm : ud_adm adm gp gpat.

  Lemma ud_mid_cons fc L F so :
    stage_out fc L (SMid F) so -> gp = true \/ F = FCat -> umidok gp (so_cons so).
  Proof using.
    intros H HF. remember (SMid F) as st eqn:Hst. unfold umidok, umo, pde_mo.
    destruct H as [st0 | st0 | ws Hl | ws D Hl HD | f Hf | f D Hf HD | f | F' D HD | D HD
                  | w D W HD HW | F' D HD]; try discriminate Hst; cbn [so_cons].
    - subst st0. cbn [st_dg_exec]. right. apply elem_of_app. destruct F as [| w]; cbn [filt_dg_exec].
      + left. ud_elem.
      + destruct HF as [Hg | HF]; [| discriminate HF]. right. rewrite Hg. cbv iota. ud_elem.
    - by left.
    - by left.
    - right. apply elem_of_app. left. ud_elem.
    - by left.
  Qed.

  (* a terminal suffix of an admitted line: diagnostics only *)
  Lemma ud_sfx_shape fc L fs win wc W s :
    sfx_term fc L fs win wc W s -> Forall (fun F => gp = true \/ F = FCat) fs ->
    exists mids, W = mids ++ [dg_fork_b] /\ Forall (umidok gp) mids /\ umidok gp s.
  Proof using.
    induction 1 as [F F' fs win wc so Hso | F F' fs win wc so W s Hso Hp Hsfx IH]; intros Hc;
      apply Forall_cons in Hc as [HF Hc].
    - exists []. split_and!; [reflexivity | constructor | exact (ud_mid_cons _ _ _ _ Hso HF)].
    - destruct (IH Hc) as (mids & -> & HFm & Hs). exists (so_cons so :: mids).
      split_and!; [reflexivity | constructor; [exact (ud_mid_cons _ _ _ _ Hso HF) | exact HFm] | exact Hs].
  Qed.

  Lemma ud_lterm_shape fc p fs W s :
    adm (LPipes p fs) = true -> line_term fc (LPipes p fs) W s ->
    (W = [dg_fork_b] /\ s ∈ ud_prod p)
    \/ (exists pc mids, W = pc :: mids ++ [dg_fork_b] /\ pc ∈ ud_prod p
                        /\ Forall (umidok gp) mids /\ umidok gp s).
  Proof using Hadm.
    intros Ha H. remember (LPipes p fs) as l eqn:Hl.
    destruct H as [p' fs' so Hn Hso | p' fs' so W' s' Hso Ht]; injection Hl as -> ->.
    - left. split; [reflexivity | exact (ud_prod_cons _ _ _ _ Hso)].
    - right.
      destruct (ud_sfx_shape _ _ _ _ _ _ _ Ht (@uda_filt _ _ _ Hadm p fs Ha)) as (mids & -> & HF & Hs).
      exists (so_cons so), mids.
      split_and!; [reflexivity | exact (ud_prod_cons _ _ _ _ Hso) | exact HF | exact Hs].
  Qed.

  (* a producer's stream a wire shows is one of [prodU]'s, as far as the
     wire shows it: at the stray stream... *)
  Lemma ud_stray_U p fs x (W : list bytes) (pr u : bytes) :
    adm (LPipes p fs) = true -> x ∈ ud_prod p -> pde_pmt W pr x u ->
    exists x', x' ∈ prodU u /\ pde_pmt W pr x' u.
  Proof using Hadm.
    unfold prodU. destruct p as [ws | g]; cbn [ud_prod]; intros Ha Hx Hp;
      apply elem_of_list_In in Hx.
    - exists x. split; [| exact Hp]. apply elem_of_app. left.
      destruct Hx as [<- | [<- | []]]; ud_elem.
    - pose proof (@uda_catf _ _ _ Hadm g fs Ha) as Hg.
      destruct Hx as [<- | [<- | [<- | [<- | []]]]];
        [exists PipeDisc.dg_execR | exists [] | exists cat_dg_write | ];
        try (split; [apply elem_of_app; left; ud_elem | exact Hp]).
      destruct (pmt_stray_trunc _ _ _ _ Hp) as (sp & Hsp & Hsu & Hp').
      destruct (open_trunc g sp u Hg Hsp Hsu) as (g' & Hg' & Hsp').
      exists (cat_dg_open g'). split.
      + apply elem_of_app. right. apply elem_of_list_fmap. by exists g'.
      + exact (pde_pmt_stray _ _ _ _ _ Hp' Hsp').
  Qed.

  (* ...and at the head of the streams *)
  Lemma ud_head_U p fs pc (R : list bytes) (pr s u : bytes) :
    adm (LPipes p fs) = true -> pc ∈ ud_prod p -> pde_pmt (pc :: R) pr s u ->
    exists pc', pc' ∈ prodU u /\ pde_pmt (pc' :: R) pr s u.
  Proof using Hadm.
    unfold prodU. destruct p as [ws | g]; cbn [ud_prod]; intros Ha Hx Hp;
      apply elem_of_list_In in Hx.
    - exists pc. split; [| exact Hp]. apply elem_of_app. left.
      destruct Hx as [<- | [<- | []]]; ud_elem.
    - pose proof (@uda_catf _ _ _ Hadm g fs Ha) as Hg.
      destruct Hx as [<- | [<- | [<- | [<- | []]]]];
        [exists PipeDisc.dg_execR | exists [] | exists cat_dg_write | ];
        try (split; [apply elem_of_app; left; ud_elem | exact Hp]).
      destruct (pmt_trunc _ _ _ _ Hp) as [HF | (W0 & HP & HS & H0)].
      + exists (cat_dg_open g). split; [| exact Hp].
        apply elem_of_app. right. apply elem_of_list_fmap. exists g. split; [reflexivity |].
        apply gcands_self; [exact Hg |].
        apply Forall_cons_1 in HF as [HF _]. etrans; [| exact HF].
        rewrite cat_dg_open_eq. apply sublist_inserts_l, sublist_inserts_r. reflexivity.
      + destruct W0 as [| v R0]; [by apply Forall2_nil_cons_inv in HP |].
        apply Forall2_cons_1 in HP as [Hv HR].
        apply Forall_cons_1 in HS as [Hvu _].
        destruct (open_trunc g v u Hg Hv Hvu) as (g' & Hg' & Hv').
        exists (cat_dg_open g'). split.
        * apply elem_of_app. right. apply elem_of_list_fmap. by exists g'.
        * apply (pmt_ext (v :: R0) s u H0). by apply Forall2_cons.
  Qed.

  (* every middle stream is a stage's, at a cat or (at [gp]) a grep of [gpat] *)
  Lemma ud_mid_so fc L m :
    umidok gp m ->
    exists F so, (F = FCat \/ (gp = true /\ F = FGrep gpat))
                 /\ stage_out fc L (SMid F) so /\ so_cons so = m /\ rd_of so = RdGone.
  Proof using.
    unfold umidok, umo, pde_mo. intros [-> | Hm].
    - exists FCat, (MkSO [] (Some RdGone) (Some WrNone)).
      split_and!; [by left | apply (so_silent fc L (SMid FCat)) | reflexivity | reflexivity].
    - apply elem_of_app in Hm as [Hm | Hm].
      + apply elem_of_list_In in Hm. destruct Hm as [<- | [<- | []]].
        * exists FCat, (MkSO PipeDisc.dg_execR (Some RdGone) (Some WrNone)).
          split_and!; [by left | apply (so_exec fc L (SMid FCat)) | reflexivity | reflexivity].
        * exists FCat, (MkSO cat_dg_write (Some RdGone) (Some (WrHalt []))).
          split_and!; [by left | apply so_mid_halt, prefix_nil | reflexivity | reflexivity].
      + destruct (umo_grep gp m Hm) as [Hg ->].
        exists (FGrep gpat), (MkSO dg_execG (Some RdGone) (Some WrNone)).
        split_and!; [right; split; [exact Hg | reflexivity] | apply (so_exec fc L (SMid (FGrep gpat)))
                    | reflexivity | reflexivity].
  Qed.

  Lemma ud_sfx_build fc L (mids : list bytes) (s : bytes) :
    Forall (umidok gp) mids -> umidok gp s ->
    exists F1 fs, Forall (fun F => F = FCat \/ (gp = true /\ F = FGrep gpat)) (F1 :: fs)
                  /\ forall win wc, sfx_term fc L (F1 :: fs) win wc (mids ++ [dg_fork_b]) s.
  Proof using.
    intros HF Hs. induction HF as [| m mids Hm HF IH].
    - destruct (ud_mid_so fc L s Hs) as (F & so & HFo & Hso & Hc & _).
      exists F, [FCat]. split; [constructor; [exact HFo | constructor; [by left | constructor]] |].
      intros win wc. change ([] ++ [dg_fork_b]) with [dg_fork_b]. rewrite -Hc.
      apply stt_here. exact Hso.
    - destruct IH as (F1 & fs & Hfs & Ht).
      destruct (ud_mid_so fc L m Hm) as (F & so & HFo & Hso & Hc & Hr).
      exists F, (F1 :: fs). split; [constructor; [exact HFo | exact Hfs] |].
      intros win wc. change ((m :: mids) ++ [dg_fork_b]) with (m :: (mids ++ [dg_fork_b])).
      rewrite -Hc. eapply stt_next; [exact Hso | rewrite Hr; apply pde_pairB_gone | apply Ht].
  Qed.

  (* each producer stream is a producer's at [{[a.txt := []]}] *)
  Lemma ud_real u pc :
    pc ∈ prodU u ->
    exists p, (forall fs, Forall (fun F => F = FCat \/ (gp = true /\ F = FGrep gpat)) fs ->
                          adm (LPipes p fs) = true)
              /\ exists so, stage_out fc0 (prod_content fc0 p) (SProd p) so /\ so_cons so = pc.
  Proof using Hadm.
    unfold prodU. intros Hpc. apply elem_of_app in Hpc as [Hpc | Hpc].
    - apply elem_of_list_In in Hpc.
      assert (HE : forall fs, Forall (fun F => F = FCat \/ (gp = true /\ F = FGrep gpat)) fs ->
                              adm (LPipes (PrEcho []) fs) = true)
        by (intros fs Hfs; apply (@uda_real _ _ _ Hadm); [by left | exact Hfs]).
      assert (HC : forall fs, Forall (fun F => F = FCat \/ (gp = true /\ F = FGrep gpat)) fs ->
                              adm (LPipes (PrCatF txt_a) fs) = true)
        by (intros fs Hfs; apply (@uda_real _ _ _ Hadm);
            [right; exists txt_a; split; [reflexivity | exact txt_a_name] | exact Hfs]).
      destruct Hpc as [<- | [<- | [<- | [<- | []]]]].
      + exists (PrEcho []). split; [exact HE |]. eexists. split; [apply so_silent | reflexivity].
      + exists (PrEcho []). split; [exact HE |]. eexists. split; [apply so_exec | reflexivity].
      + exists (PrCatF txt_a). split; [exact HC |]. eexists. split; [apply so_exec | reflexivity].
      + exists (PrCatF txt_a). split; [exact HC |].
        exists (MkSO cat_dg_write None (Some (WrHalt []))).
        split; [| reflexivity].
        apply (so_catf_halt _ _ txt_a []); [| apply prefix_nil].
        cbn [prod_content]. rewrite /files_of lookup_singleton. reflexivity.
    - apply elem_of_list_fmap in Hpc as (g & -> & Hg).
      exists (PrCatF g). split.
      + intros fs Hfs. apply (@uda_real _ _ _ Hadm); [| exact Hfs].
        right. exists g. split; [reflexivity | exact (gcands_uname g u Hg)].
      + eexists. split; [apply so_catf_open | reflexivity].
  Qed.

  Lemma ud_merge_of_lt p fs W s u :
    adm (LPipes p fs) = true ->
    line_term fc0 (LPipes p fs) W s -> pde_pmt W u_prompt s u -> pl_merge fc0 adm u.
  Proof using.
    intros Ha Hlt Hp. destruct (pde_pmt_blk _ _ _ _ Hp) as (Wm & b & HW & Hb & Hu).
    exists (LPipes p fs), b. split; [exact Ha |]. split; [| exact Hu].
    split.
    - intros ->. pose proof (pde_merge_len _ _ Hb) as Hl. unfold pde_total in Hl.
      simpl in Hl. rewrite !length_app ll_prompt_len in Hl. simpl in Hl. lia.
    - exists b. split; [| reflexivity]. exists W, s, Wm, s.
      split; [exact Hlt |]. split; [exact HW |]. split; [reflexivity | exact Hb].
  Qed.

  (* at EVERY content function: the shape reads no content *)
  Lemma umergeb_complete fc u : pl_merge fc adm u -> umergeb gp u = true.
  Proof using Hadm.
    intros (l & b & Ha & [_ (b' & (W & s & Wm & sp & Hlt & HW & Hsp & Hb) & Hbb)] & Hu).
    pose proof (pde_pmt_stray _ _ _ _ _
                  (pde_blk_pmt W Wm u_prompt sp b' u HW Hb
                     ltac:(etrans; [exact Hu | exact Hbb])) Hsp) as Hp.
    destruct l as [ws | p fs]; [inversion Hlt |].
    unfold umergeb. apply orb_true_iff.
    destruct (ud_lterm_shape _ _ _ _ _ Ha Hlt) as [[-> Hs] | (pc & mids & -> & Hpc & HF & Hs)].
    - right. destruct (ud_stray_U p fs s _ _ _ Ha Hs Hp) as (s' & Hs' & Hp').
      apply existsb_exists. exists s'.
      split; [apply elem_of_list_In; exact Hs' |].
      apply (pde_chk_complete _ _ _ _ _ Hp' [dg_fork_b] [] false);
        [by rewrite app_nil_r | constructor].
    - left. destruct (ud_head_U p fs pc _ _ _ _ Ha Hpc Hp) as (pc' & Hpc' & Hp').
      apply existsb_exists. exists pc'.
      split; [apply elem_of_list_In; exact Hpc' |].
      apply existsb_exists. exists s. split.
      { apply elem_of_list_In. destruct Hs as [-> | Hs];
          [apply elem_of_list_here | apply elem_of_list_further; exact Hs]. }
      apply (pde_chk_complete _ _ _ _ _ Hp' [pc'; dg_fork_b] mids true); [| exact HF].
      simpl. apply perm_skip. rewrite Permutation_app_comm. reflexivity.
  Qed.

  Lemma umergeb_sound u : umergeb gp u = true -> pl_merge fc0 adm u.
  Proof using Hadm.
    intros Hc. unfold umergeb in Hc. apply orb_true_iff in Hc as [Hc | Hc].
    - apply existsb_exists in Hc as (pc & Hpin & Hc).
      apply existsb_exists in Hc as (s & Hsin & Hc).
      assert (Hs : umidok gp s).
      { apply elem_of_list_In in Hsin. apply elem_of_cons in Hsin as [-> | Hs]; [by left | by right]. }
      destruct (pde_chk_sound (umo gp) u [pc; dg_fork_b] true s u_prompt Hc) as (Mu & HF & Hp).
      assert (HFm : Forall (umidok gp) Mu)
        by (eapply Forall_impl; [exact HF |]; intros m [_ Hm]; by right).
      destruct (ud_real u pc (proj2 (elem_of_list_In _ _) Hpin)) as (p & Ha & so & Hso & Hc').
      destruct (ud_sfx_build fc0 (prod_content fc0 p) Mu s HFm Hs) as (F1 & fs & Hfs & Ht).
      apply (ud_merge_of_lt p (F1 :: fs) (pc :: Mu ++ [dg_fork_b]) s u (Ha _ Hfs)).
      + rewrite -Hc'. eapply lt_next; [exact Hso |]. apply Ht.
      + apply (pde_pmt_perm _ _ _ _ _ Hp). simpl. apply perm_skip.
        rewrite Permutation_app_comm. reflexivity.
    - apply existsb_exists in Hc as (s & Hsin & Hc).
      destruct (pde_chk_sound (umo gp) u [dg_fork_b] false s u_prompt Hc) as (Mu & HF & Hp).
      destruct Mu as [| m Mu]; [| apply Forall_cons in HF as [[Hf _] _]; discriminate Hf].
      destruct (ud_real u s (proj2 (elem_of_list_In _ _) Hsin)) as (p & Ha & so & Hso & Hc').
      apply (ud_merge_of_lt p [FCat] [dg_fork_b] s u
               (Ha [FCat] (proj2 (Forall_singleton _ _) (or_introl eq_refl))));
        [| by rewrite app_nil_r in Hp].
      rewrite -Hc'. apply lt_here; [discriminate | exact Hso].
  Qed.

  (* [umerge_p]'s [exists s] IS the state holding one empty class file *)
  Lemma umerge_spec u : umerge_p adm u <-> umergeb gp u = true.
  Proof using Hadm.
    split.
    - intros (s & _ & Hm). exact (umergeb_complete _ u Hm).
    - intros Hb. exists {[txt_a := []]}. split; [exact fstate_ok_nil1 |].
      exact (umergeb_sound u Hb).
  Qed.

  Lemma umerge_some_nil u : umerge_p adm u <-> pl_merge fc0 adm u.
  Proof using Hadm.
    split; [intros Hm; apply umergeb_sound, umerge_spec, Hm |].
    intros Hm. exists {[txt_a := []]}. split; [exact fstate_ok_nil1 | exact Hm].
  Qed.

  Lemma umerge_p_dec (u : bytes) : Decision (umerge_p adm u).
  Proof using Hadm.
    destruct (umergeb gp u) eqn:H; [left; by apply umerge_spec |].
    right. intros Hm. apply umerge_spec in Hm. congruence.
  Qed.

  (* at a line: [True] at a seccomp line, the pipeline's check elsewhere *)
  Lemma umerge_dec (l : uline) (u : bytes) : Decision (umerge adm l u).
  Proof using Hadm. destruct l; cbn [umerge]; [apply umerge_p_dec .. | left; exact I]. Qed.

  (* the silent round's continuation ends no coverage, at a line that is
     not a seccomp line *)
  Lemma umerge_prompt l : (forall ws, l <> LSecc ws) -> ~ umerge adm l u_prompt.
  Proof using Hadm.
    intros Hl H. destruct l as [ws | ws N | N | p n | ws]; [| | | | exact (Hl ws eq_refl)].
    all: cbn [umerge] in H; apply umerge_spec in H; rewrite umergeb_prompt in H; discriminate H.
  Qed.
End umerge.

(* ===================================================================== *)
(*  2.  THE COVERAGE-ENDING GUARD, DECIDED                                *)
(* ===================================================================== *)

Definition uterm_line (adm : pline' -> bool) (l : uline) : Prop :=
  match l with
  | LPipe p n => adm (LPipes p n) = true /\ n <> []
  | LSecc _ => True
  | _ => False
  end.

Global Instance uterm_line_dec adm l : Decision (uterm_line adm l).
Proof using. destruct l; cbn [uterm_line]; apply _. Defined.

(* a line admits a coverage-ending alternative -- at any state -- iff it
   is an admitted pipeline with a cat, or a seccomp line *)
Lemma utermex_iff adm s l :
  (exists c, uok adm s l c /\ uterm c = true) <-> uterm_line adm l.
Proof using.
  split.
  - intros (c & Hok & Ht). destruct l as [ws | ws N | N | p n | ws].
    1-3: destruct c as [r | x | x | u]; cbn [uok uterm] in Hok, Ht;
         first [discriminate Ht | contradiction].
    2: exact I.
    destruct (uok_pipe _ _ _ _ _ Hok) as (x & -> & Hx).
    rewrite upl_term in Ht. destruct x as [| b | b]; try discriminate Ht.
    destruct Hx as [Hsafe | [Ha (_ & b' & (W & t & Wm & sp & Hlt & _) & _)]].
    { exfalso. destruct Hsafe as [H | [H | H]]; discriminate H. }
    split; [exact Ha | exact (line_term_pos _ _ _ _ _ Hlt)].
  - destruct l as [ws | ws N | N | p n | ws]; cbn [uterm_line]; [intros [] | intros [] | intros [] | |].
    2: { intros _. exists (US [wl_nl]). split; [cbn [uok]; discriminate | reflexivity]. }
    intros [Ha Hn]. exists (upl p (PLTerm dg_fork_b)). split; [| rewrite upl_term; reflexivity].
    apply uok_upl. right. split; [exact Ha | exact (plterm_fork_ok _ p n Hn)].
Qed.

(* ===================================================================== *)
(*  3.  SEAM (a): THE FILE A LINE TOUCHES, AND NAME-LOCALITY              *)
(*                                                                        *)
(*  [FileDisc.line_file l]: the one file a round of [l] may create,       *)
(*  change or read -- [N] at a redirect and at [cat N], the producer's    *)
(*  file at a [cat g | ..] pipeline, none at an echo line or an echo      *)
(*  pipeline.  The canonicalisation below works ONE NAME AT A TIME         *)
(*  through the two locality lemmas: a round moves only its line's file   *)
(*  ([ustep_local], and [ustep_ins_cases] for the shape of that move),    *)
(*  and admits and prints reading only that file ([uok_local],            *)
(*  [ucont_local]).                                                       *)
(* ===================================================================== *)

(* LOCALITY 1: a round changes only its line's file *)
Lemma ustep_local s l a g :
  line_file l <> Some g -> files_of (ustep s l a) g = files_of s g.
Proof using.
  intros Hl. rewrite /files_of. destruct a as [r | x | x | u]; cbn [ustep];
    [| reflexivity | reflexivity | reflexivity].
  destruct l as [ws | ws N | N | p n | ws]; cbn [fsm];
    [reflexivity | | reflexivity | reflexivity | reflexivity].
  assert (HgN : N <> g) by (intros ->; exact (Hl eq_refl)).
  destruct r; try reflexivity; try (by rewrite lookup_insert_ne).
  destruct (s !! N); [reflexivity | by rewrite lookup_insert_ne].
Qed.

(* THE SHAPE OF A ROUND'S MOVE AT ONE NAME [N]: either the round commutes
   with setting [N] (it does not touch [N], or it only reads it present),
   or its result does not depend on what [N] held (it set [N]) *)
Lemma ustep_ins_cases l a N :
  (forall x t, ustep (<[N := x]> t) l a = <[N := x]> (ustep t l a))
  \/ (forall x x' t, ustep (<[N := x]> t) l a = ustep (<[N := x']> t) l a).
Proof using.
  destruct a as [r | y | y | u]; cbn [ustep];
    [| left; intros x t; reflexivity | left; intros x t; reflexivity | left; intros x t; reflexivity].
  destruct l as [ws | ws M | M | p n | ws]; cbn [fsm];
    [left; intros x t; reflexivity | | left; intros x t; reflexivity | left; intros x t; reflexivity
    | left; intros x t; reflexivity].
  destruct (decide (M = N)) as [-> | HMN].
  - destruct r; try (left; intros x t; reflexivity).
    + right. intros x x' t. by rewrite !insert_insert.
    + right. intros x x' t. by rewrite !insert_insert.
    + left. intros x t. rewrite lookup_insert.
      destruct (t !! N); [reflexivity |]. by rewrite insert_insert.
  - left. intros x t. destruct r; try reflexivity; try (by apply insert_commute).
    destruct (t !! M) as [v |] eqn:E.
    + rewrite lookup_insert_ne; [| congruence]. rewrite E. reflexivity.
    + rewrite lookup_insert_ne; [| congruence]. rewrite E. by apply insert_commute.
Qed.

(* the content function is read only at the producer's file *)
Lemma stage_out_at fc fc' g L st so :
  stage_out fc L st so -> (forall f, st = SProd (PrCatF f) -> f = g) -> fc g = fc' g ->
  stage_out fc' L st so.
Proof using.
  destruct 1 as [st | st | ws Hl | ws D Hl HD | f Hf | f D Hf HD | f | F D HD | D HD
                | w D W HD HW | F D HD];
    intros Hst Hg.
  - apply so_exec.
  - apply so_silent.
  - apply so_echo. exact Hl.
  - apply so_echo_halt; [exact Hl | exact HD].
  - rewrite (Hst f eq_refl) in Hf |- *. apply so_catf. by rewrite -Hg.
  - rewrite (Hst f eq_refl) in Hf |- *. apply so_catf_halt; [by rewrite -Hg | exact HD].
  - apply so_catf_open.
  - apply so_mid_f. exact HD.
  - apply so_mid_halt. exact HD.
  - apply so_grep_halt; [exact HD | exact HW].
  - apply so_last_f. exact HD.
Qed.

Lemma line_run_at fc fc' g n ss :
  fc g = fc' g -> line_run fc (LPipes (PrCatF g) n) ss -> line_run fc' (LPipes (PrCatF g) n) ss.
Proof using.
  intros Hg H. remember (LPipes (PrCatF g) n) as l eqn:Hl.
  destruct H as [ws | ws | ws | p n' Hn | p n' so ss' Hso Hr]; try discriminate Hl;
    injection Hl as -> ->.
  - apply lr_pipe_fail. exact Hn.
  - assert (Hc : prod_content fc (PrCatF g) = prod_content fc' (PrCatF g))
      by (cbn [prod_content]; by rewrite Hg).
    apply lr_node.
    + rewrite -Hc. apply (stage_out_at fc _ g); [exact Hso | by intros f [= ->] | exact Hg].
    + rewrite -Hc. exact (sfx_run_fc fc fc' _ _ _ _ _ Hr).
Qed.

Lemma line_term_at fc fc' g n W s :
  fc g = fc' g -> line_term fc (LPipes (PrCatF g) n) W s -> line_term fc' (LPipes (PrCatF g) n) W s.
Proof using.
  intros Hg H. remember (LPipes (PrCatF g) n) as l eqn:Hl.
  assert (Hc : prod_content fc (PrCatF g) = prod_content fc' (PrCatF g))
    by (cbn [prod_content]; by rewrite Hg).
  destruct H as [p n' so Hn Hso | p n' so W' s' Hso Ht]; injection Hl as -> ->.
  - apply lt_here; [exact Hn |].
    rewrite -Hc. apply (stage_out_at fc _ g); [exact Hso | by intros f [= ->] | exact Hg].
  - apply lt_next.
    + rewrite -Hc. apply (stage_out_at fc _ g); [exact Hso | by intros f [= ->] | exact Hg].
    + rewrite -Hc. exact (sfx_term_fc fc fc' _ _ _ _ _ _ Ht).
Qed.

Lemma plalt_ok_at fc fc' g n x :
  fc g = fc' g -> plalt_ok fc (LPipes (PrCatF g) n) x -> plalt_ok fc' (LPipes (PrCatF g) n) x.
Proof using.
  intros Hg. destruct x as [| b | b]; cbn [plalt_ok]; unfold line_blocks, line_term_blocks.
  - intros _. exact I.
  - intros (ss & Hr & Hm). exists ss. split; [exact (line_run_at fc fc' g n ss Hg Hr) | exact Hm].
  - intros [Hne (b' & (W & t & Wm & sp & Hlt & HWm & Hsp & Hm) & Hp)]. split; [exact Hne |].
    exists b'. split; [| exact Hp]. exists W, t, Wm, sp.
    split_and!; [exact (line_term_at fc fc' g n W t Hg Hlt) | exact HWm | exact Hsp | exact Hm].
Qed.

(* LOCALITY 2: a round admits ... *)
Lemma uok_local adm s s' l a :
  (forall g, line_file l = Some g -> files_of s g = files_of s' g) ->
  uok adm s l a -> uok adm s' l a.
Proof using.
  intros Hf Hok. destruct l as [ws | ws N | N | [ws | g] n | ws];
    [exact Hok | exact Hok | exact Hok | | | exact Hok].
  - exact (uok_echo_st adm s s' ws n a Hok).
  - destruct a as [r | x | x | u]; cbn [uok] in Hok |- *; try contradiction.
    destruct Hok as [Hs | [Ha Hb]]; [left; exact Hs | right; split; [exact Ha |]].
    exact (plalt_ok_at _ _ g n x (Hf g eq_refl) Hb).
Qed.

(* ... and prints reading only its line's file *)
Lemma ucont_local adm s s' l a :
  (forall g, line_file l = Some g -> files_of s g = files_of s' g) ->
  uok adm s l a -> ucont s l a = ucont s' l a.
Proof using.
  intros Hf Hok. destruct a as [r | x | x | u]; cbn [ucont]; [| reflexivity | reflexivity | reflexivity].
  destruct (decide (cont s l r = cont s' l r)) as [E | Hne]; [exact E |].
  pose proof (cont_state_ne _ _ _ _ Hne) as ->. exfalso.
  destruct l as [ws | ws N | N | p n | ws]; cbn [uok ralt_ok] in Hok; try contradiction.
  apply Hne. pose proof (Hf N eq_refl) as E. rewrite /files_of in E.
  cbn [cont lname line_file default]. by rewrite E.
Qed.

(* two states that agree on a line's file stay so after its round, at
   every name a round's file can be *)
Lemma ustep_agree (Ns : list (list (bv 8))) s s' l a :
  (forall N, N ∈ Ns -> s !! N = s' !! N) ->
  (forall g, line_file l = Some g -> g ∈ Ns) ->
  forall N, N ∈ Ns -> ustep s l a !! N = ustep s' l a !! N.
Proof using.
  intros Hag Hl N HN. destruct a as [r | x | x | u]; cbn [ustep];
    [| exact (Hag N HN) | exact (Hag N HN) | exact (Hag N HN)].
  destruct l as [ws | ws M | M | p n | ws]; cbn [fsm]; try exact (Hag N HN).
  pose proof (Hl M eq_refl) as HM.
  destruct r; try exact (Hag N HN);
    try (destruct (decide (M = N)) as [-> | HMN];
         [by rewrite !lookup_insert | rewrite !lookup_insert_ne; [exact (Hag N HN) | done | done]]).
  destruct (s' !! M) as [v |] eqn:E'; rewrite (Hag M HM) E'; [exact (Hag N HN) |].
  destruct (decide (M = N)) as [-> | HMN];
    [by rewrite !lookup_insert | rewrite !lookup_insert_ne; [exact (Hag N HN) | done | done]].
Qed.

(* ===================================================================== *)
(*  4.  THE TRUNCATION LEMMA                                              *)
(*                                                                        *)
(*  Every pipe of a [cat f] pipeline carries a prefix of [f]'s content    *)
(*  [L], and [L] is ONE LINE (the file state's shape), so what a filter  *)
(*  owes of a prefix is a prefix ([fapp_prefix]) and a grep passes the    *)
(*  whole line or nothing (the gate, [GrepFilt.grep_out_line]).           *)
(*                                                                        *)
(*  Cutting the content to a prefix [P] re-runs the pipeline with each    *)
(*  pipe's new content RELATED to its old one by [tr_rel P]: a prefix of  *)
(*  it, inside [P], and the old one itself when that already fits in      *)
(*  [P].  This is grep-pipes.md section 2's per-pipe truncation with the  *)
(*  lengths left implicit: a grep does not commute with a uniform cut,    *)
(*  but it keeps the relation -- by monotonicity and the gate, since its  *)
(*  old output is [] or the whole line, and the whole line fits in [P]    *)
(*  only when [P] is all of it; a halted writer's bytes reach no reader  *)
(*  exactly, so the new run writes none; and a reader behind a halted cat *)
(*  (the loose corner B) restarts at the first [|P|] bytes of what it     *)
(*  saw.  The console streams are unchanged provided the one stream that  *)
(*  PRINTS content -- the last stage's -- fits in [P] when it is a prefix *)
(*  of [L] ([fits]).  No stage is assumed a cat.                          *)
(* ===================================================================== *)

Definition tr_rel (P D' D : bytes) : Prop :=
  D' `prefix_of` D /\ D' `prefix_of` P /\ (D `prefix_of` P -> D' = D).

Definition tr_wrel (P : bytes) (w' w : wr_out) : Prop :=
  match w', w with
  | WrAll D', WrAll D => tr_rel P D' D
  | WrHalt _, WrHalt _ | WrNone, WrNone => True
  | _, _ => False
  end.

Definition tr_rrel (P : bytes) (r' r : rd_out) : Prop :=
  match r', r with
  | RdEof D', RdEof D => tr_rel P D' D
  | RdGone, RdGone => True
  | _, _ => False
  end.

Lemma tr_rrel_gone P r' : tr_rrel P r' RdGone -> r' = RdGone.
Proof using. destruct r'; cbn [tr_rrel]; [intros [] | reflexivity]. Qed.

Lemma tr_rrel_eof P r' D : tr_rrel P r' (RdEof D) -> exists D', r' = RdEof D' /\ tr_rel P D' D.
Proof using. destruct r' as [D' |]; cbn [tr_rrel]; [intros H; by exists D' | intros []]. Qed.

Lemma take_len_prefix (P L D : bytes) :
  P `prefix_of` L -> D `prefix_of` L -> take (length P) D `prefix_of` P.
Proof using.
  intros HP HD.
  assert (HPe : take (length P) L = P) by (destruct HP as [z ->]; by rewrite take_app_length).
  etrans; [exact (ud_prefix_take (length P) D L HD) |]. rewrite HPe. reflexivity.
Qed.

Lemma tr_rel_top (P L : bytes) : P `prefix_of` L -> tr_rel P P L.
Proof using.
  intros HP. unfold tr_rel. split; [exact HP |]. split; [reflexivity |].
  intros HL. exact (prefix_length_eq P L HP (prefix_length _ _ HL)).
Qed.

Lemma tr_rel_take (P L D : bytes) :
  P `prefix_of` L -> D `prefix_of` L -> tr_rel P (take (length P) D) D.
Proof using.
  intros HP HD. unfold tr_rel. split; [apply prefix_take |]. split; [exact (take_len_prefix P L D HP HD) |].
  intros HDP. apply take_ge. exact (prefix_length _ _ HDP).
Qed.

(* A FILTER KEEPS THE RELATION (the gate) *)
Lemma tr_rel_fapp (L P D' D : bytes) (F : filt) :
  GrepFilt.oneline L -> D `prefix_of` L -> tr_rel P D' D -> tr_rel P (fapp F D') (fapp F D).
Proof using.
  intros HL HD (H1 & H2 & H3). unfold tr_rel.
  destruct F as [| w]; cbn [fapp]; [exact (conj H1 (conj H2 H3)) |].
  assert (HD' : D' `prefix_of` L) by (etrans; [exact H1 | exact HD]).
  split; [exact (GrepFilt.grep_out_mono w D' D H1) |]. split.
  - destruct (GrepFilt.grep_out_line w L D' HL HD') as [-> | [-> ->]]; [apply prefix_nil | exact H2].
  - intros HP. destruct (GrepFilt.grep_out_line w L D HL HD) as [HE | [-> HE]].
    + pose proof (GrepFilt.grep_out_mono w D' D H1) as Hm. rewrite HE in Hm |- *.
      exact (prefix_nil_inv _ Hm).
    + rewrite HE in HP. rewrite (H3 HP). reflexivity.
Qed.

(* A PIPE KEEPS IT: the new reader of a related writer *)
Lemma pair_trunc (L P : bytes) wc w' w r :
  P `prefix_of` L -> tr_wrel P w' w -> pipe_pairB L wc w r ->
  exists r', tr_rrel P r' r /\ pipe_pairB P wc w' r'.
Proof using.
  intros HP Hw Hp. destruct r as [D |].
  2: { exists RdGone. split; [exact I | destruct w'; exact I]. }
  destruct w' as [D0' | D0' |], w as [D0 | D0 |]; cbn [tr_wrel] in Hw; try contradiction;
    cbn [pipe_pairB pipe_pair] in Hp.
  - subst D. exists (RdEof D0'). cbn [tr_rrel pipe_pairB pipe_pair]. split; [exact Hw | reflexivity].
  - destruct Hp as [Hwc HD]. exists (RdEof (take (length P) D)).
    split; [exact (tr_rel_take P L D HP HD) |]. cbn [pipe_pairB].
    split; [exact Hwc | exact (take_len_prefix P L D HP HD)].
  - subst D. exists (RdEof []). cbn [tr_rrel pipe_pairB pipe_pair]. unfold tr_rel.
    split_and!; [reflexivity | apply prefix_nil | intros _; reflexivity | reflexivity].
Qed.

(* THE STAGES.  The cat producer at the cut content ... *)
Lemma prod_trunc fc fc' L P f so :
  P `prefix_of` L -> (fc f = Some L -> fc' f = Some P) ->
  stage_out fc L (SProd (PrCatF f)) so ->
  exists so', stage_out fc' P (SProd (PrCatF f)) so' /\ so_cons so' = so_cons so
              /\ tr_wrel P (wr_of so') (wr_of so).
Proof using.
  intros HP Hfc H. remember (SProd (PrCatF f)) as st eqn:Hst.
  destruct H as [st0 | st0 | ws Hl | ws D Hl HD | g Hg | g D Hg HD | g | F D HD | D HD
                | w D W HD HW | F D HD]; try discriminate Hst.
  - subst st0. eexists. split_and!; [apply so_exec | reflexivity | exact I].
  - subst st0. eexists. split_and!; [apply so_silent | reflexivity | exact I].
  - injection Hst as ->. exists (MkSO [] None (Some (WrAll P))).
    split_and!; [apply so_catf; exact (Hfc Hg) | reflexivity | exact (tr_rel_top P L HP)].
  - injection Hst as ->. exists (MkSO cat_dg_write None (Some (WrHalt []))).
    split_and!; [apply so_catf_halt; [exact (Hfc Hg) | apply prefix_nil] | reflexivity | exact I].
  - eexists. split_and!; [apply so_catf_open | reflexivity | exact I].
Qed.

(* ... a middle filter, reading a related pipe ... *)
Lemma mid_trunc fc fc' L P F so r' :
  GrepFilt.oneline L -> P `prefix_of` L ->
  stage_out fc L (SMid F) so -> tr_rrel P r' (rd_of so) ->
  exists so', stage_out fc' P (SMid F) so' /\ so_cons so' = so_cons so /\ rd_of so' = r'
              /\ tr_wrel P (wr_of so') (wr_of so).
Proof using.
  intros HL HP H Hr. remember (SMid F) as st eqn:Hst.
  destruct H as [st0 | st0 | ws Hl | ws D Hl HD | g Hg | g D Hg HD | g | F' D HD | D HD
                | w D W HD HW | F' D HD]; try discriminate Hst.
  - subst st0. cbn [rd_of so_rd st_rd_dead] in Hr. rewrite (tr_rrel_gone _ _ Hr).
    eexists. split_and!; [apply so_exec | reflexivity | reflexivity | exact I].
  - subst st0. cbn [rd_of so_rd st_rd_dead] in Hr. rewrite (tr_rrel_gone _ _ Hr).
    eexists. split_and!; [apply so_silent | reflexivity | reflexivity | exact I].
  - cbn [rd_of so_rd] in Hr. destruct (tr_rrel_eof _ _ _ Hr) as (D' & -> & Htr).
    exists (MkSO [] (Some (RdEof D')) (Some (WrAll (fapp F' D')))).
    split_and!; [apply so_mid_f; exact (proj1 (proj2 Htr)) | reflexivity | reflexivity |].
    exact (tr_rel_fapp L P D' D F' HL HD Htr).
  - cbn [rd_of so_rd] in Hr. rewrite (tr_rrel_gone _ _ Hr).
    exists (MkSO cat_dg_write (Some RdGone) (Some (WrHalt []))).
    split_and!; [apply so_mid_halt, prefix_nil | reflexivity | reflexivity | exact I].
  - cbn [rd_of so_rd] in Hr. destruct (tr_rrel_eof _ _ _ Hr) as (D' & -> & Htr).
    exists (MkSO [] (Some (RdEof D')) (Some (WrHalt []))).
    split_and!; [apply so_grep_halt; [exact (proj1 (proj2 Htr)) | apply prefix_nil]
                | reflexivity | reflexivity | exact I].
Qed.

(* ... a middle filter nobody reads after (a terminal run's stray) ... *)
Lemma mid_trunc_any fc fc' L P F so :
  stage_out fc L (SMid F) so -> exists so', stage_out fc' P (SMid F) so' /\ so_cons so' = so_cons so.
Proof using.
  intros H. remember (SMid F) as st eqn:Hst.
  destruct H as [st0 | st0 | ws Hl | ws D Hl HD | g Hg | g D Hg HD | g | F' D HD | D HD
                | w D W HD HW | F' D HD]; try discriminate Hst.
  - eexists. split; [apply so_exec | reflexivity].
  - eexists. split; [apply so_silent | reflexivity].
  - exists (MkSO [] (Some (RdEof [])) (Some (WrAll (fapp F' [])))).
    split; [apply so_mid_f, prefix_nil | reflexivity].
  - exists (MkSO cat_dg_write (Some RdGone) (Some (WrHalt []))).
    split; [apply so_mid_halt, prefix_nil | reflexivity].
  - exists (MkSO [] (Some (RdEof [])) (Some (WrHalt []))).
    split; [apply so_grep_halt; apply prefix_nil | reflexivity].
Qed.

(* ... and the last filter, whose printed content fits *)
Lemma last_trunc fc fc' L P F so r' :
  GrepFilt.oneline L -> P `prefix_of` L ->
  stage_out fc L (SLast F) so -> tr_rrel P r' (rd_of so) ->
  (so_cons so `prefix_of` L -> so_cons so `prefix_of` P) ->
  exists so', stage_out fc' P (SLast F) so' /\ so_cons so' = so_cons so /\ rd_of so' = r'.
Proof using.
  intros HL HP H Hr Hfit. remember (SLast F) as st eqn:Hst.
  destruct H as [st0 | st0 | ws Hl | ws D Hl HD | g Hg | g D Hg HD | g | F' D HD | D HD
                | w D W HD HW | F' D HD]; try discriminate Hst.
  - subst st0. cbn [rd_of so_rd st_rd_dead] in Hr. rewrite (tr_rrel_gone _ _ Hr).
    eexists. split_and!; [apply so_exec | reflexivity | reflexivity].
  - subst st0. cbn [rd_of so_rd st_rd_dead] in Hr. rewrite (tr_rrel_gone _ _ Hr).
    eexists. split_and!; [apply so_silent | reflexivity | reflexivity].
  - cbn [rd_of so_rd] in Hr. destruct (tr_rrel_eof _ _ _ Hr) as (D' & -> & Htr).
    exists (MkSO (fapp F' D') (Some (RdEof D')) None).
    split_and!; [apply so_last_f; exact (proj1 (proj2 Htr)) | | reflexivity].
    cbn [so_cons] in Hfit |- *.
    exact (proj2 (proj2 (tr_rel_fapp L P D' D F' HL HD Htr)) (Hfit (fapp_prefix F' L D HL HD))).
Qed.

(* the last stage's printed content fits in [P], if it is a prefix of [L] *)
Definition fits (P L : bytes) (ss : list bytes) : Prop :=
  forall x, last ss = Some x -> x `prefix_of` L -> x `prefix_of` P.

Lemma fits_cons P L x ss : ss <> [] -> fits P L (x :: ss) -> fits P L ss.
Proof using.
  intros Hne H y Hy. apply H. destruct ss as [| z ss]; [done |]. rewrite last_cons_cons. exact Hy.
Qed.

Lemma sfx_run_ne fc L m w wc ss : sfx_run fc L m w wc ss -> ss <> [].
Proof using. destruct 1; discriminate. Qed.

Lemma sfx_trunc fc fc' L P fs w wc ss w' :
  GrepFilt.oneline L -> P `prefix_of` L ->
  sfx_run fc L fs w wc ss -> tr_wrel P w' w -> fits P L ss -> sfx_run fc' P fs w' wc ss.
Proof using.
  intros HL HP H. revert w'.
  induction H as [F win wc so Hso Hp | F F' fs win wc | F F' fs win wc so ss Hso Hp Hr IH];
    intros w' Hw Hf.
  - destruct (pair_trunc L P wc w' win (rd_of so) HP Hw Hp) as (r' & Hrr & Hp').
    destruct (last_trunc fc fc' L P F so r' HL HP Hso Hrr) as (so' & Hso' & Hc & Hrd).
    { intros Hx. apply (Hf (so_cons so)); [reflexivity | exact Hx]. }
    rewrite -Hc. apply sr_last; [exact Hso' | rewrite Hrd; exact Hp'].
  - apply sr_pipe_fail.
  - destruct (pair_trunc L P wc w' win (rd_of so) HP Hw Hp) as (r' & Hrr & Hp').
    destruct (mid_trunc fc fc' L P F so r' HL HP Hso Hrr) as (so' & Hso' & Hc & Hrd & Hw').
    rewrite -Hc. apply sr_node; [exact Hso' | rewrite Hrd; exact Hp' |].
    apply IH; [exact Hw' |]. exact (fits_cons _ _ _ _ (sfx_run_ne _ _ _ _ _ _ Hr) Hf).
Qed.

Lemma sfx_term_trunc fc fc' L P fs w wc W s w' :
  GrepFilt.oneline L -> P `prefix_of` L ->
  sfx_term fc L fs w wc W s -> tr_wrel P w' w -> sfx_term fc' P fs w' wc W s.
Proof using.
  intros HL HP H. revert w'.
  induction H as [F F' fs win wc so Hso | F F' fs win wc so W s Hso Hp Ht IH]; intros w' Hw.
  - destruct (mid_trunc_any fc fc' L P F so Hso) as (so' & Hso' & Hc).
    rewrite -Hc. apply stt_here. exact Hso'.
  - destruct (pair_trunc L P wc w' win (rd_of so) HP Hw Hp) as (r' & Hrr & Hp').
    destruct (mid_trunc fc fc' L P F so r' HL HP Hso Hrr) as (so' & Hso' & Hc & Hrd & Hw').
    rewrite -Hc. apply stt_next; [exact Hso' | rewrite Hrd; exact Hp' | exact (IH _ Hw')].
Qed.

(* the round's content function, cut to [P] at ONE name [N] whose content
   is [b0]; every other file is left as it is *)
Lemma files_trunc (c : fstate) (N : list (bv 8)) (b0 P : bytes) f :
  fstate_ok c -> c !! N = Some b0 -> P `prefix_of` b0 ->
  GrepFilt.oneline (prod_content (files_of c) (PrCatF f))
  /\ prod_content (files_of (<[N := P]> c)) (PrCatF f) `prefix_of` prod_content (files_of c) (PrCatF f)
  /\ (files_of c f = Some (prod_content (files_of c) (PrCatF f)) ->
      files_of (<[N := P]> c) f = Some (prod_content (files_of (<[N := P]> c)) (PrCatF f)))
  /\ (forall x, (x `prefix_of` b0 -> x `prefix_of` P) ->
                x `prefix_of` prod_content (files_of c) (PrCatF f) ->
                x `prefix_of` prod_content (files_of (<[N := P]> c)) (PrCatF f)).
Proof using.
  intros Hc HN HP. cbn [prod_content]. rewrite /files_of. cbv beta.
  destruct (decide (f = N)) as [-> | Hf].
  - rewrite lookup_insert HN. cbn [default].
    split_and!; [exact (fcont_ok_nl b0 (proj2 (Hc N b0 HN))) | exact HP | intros _; reflexivity
                | intros x Hx; exact Hx].
  - destruct (c !! f) as [cf |] eqn:Hcf;
      rewrite lookup_insert_ne; try congruence; rewrite Hcf; cbn [default].
    + split_and!; [exact (fcont_ok_nl cf (proj2 (Hc f cf Hcf))) | reflexivity | intros H; exact H
                  | intros x _ Hx; exact Hx].
    + split_and!; [unfold GrepFilt.oneline; left; apply not_elem_of_nil | reflexivity
                  | intros H; discriminate H | intros x _ Hx; exact Hx].
Qed.

Lemma line_run_trunc c N b0 P f fs ss :
  fstate_ok c -> c !! N = Some b0 -> P `prefix_of` b0 ->
  line_run (files_of c) (LPipes (PrCatF f) fs) ss ->
  (forall x, last ss = Some x -> x `prefix_of` b0 -> x `prefix_of` P) ->
  line_run (files_of (<[N := P]> c)) (LPipes (PrCatF f) fs) ss.
Proof using.
  intros Hc HN HP H Hx. destruct (files_trunc c N b0 P f Hc HN HP) as (HL & HLP & Hfc & Hfit).
  remember (LPipes (PrCatF f) fs) as l eqn:Hl.
  destruct H as [ws | ws | ws | p fs' Hn | p fs' so ss' Hso Hr]; try discriminate Hl;
    injection Hl as -> ->.
  - apply lr_pipe_fail. exact Hn.
  - destruct (prod_trunc _ (files_of (<[N := P]> c)) _ _ f so HLP Hfc Hso) as (so' & Hso' & Hcs & Hw).
    rewrite -Hcs. apply lr_node; [exact Hso' |].
    apply (sfx_trunc (files_of c) _ _ _ _ _ _ _ _ HL HLP Hr Hw).
    apply (fits_cons _ _ (so_cons so) ss'); [exact (sfx_run_ne _ _ _ _ _ _ Hr) |].
    intros x Hlx Hxl. apply (Hfit x); [exact (Hx x Hlx) | exact Hxl].
Qed.

Lemma line_term_trunc c N b0 P f fs W s :
  fstate_ok c -> c !! N = Some b0 -> P `prefix_of` b0 ->
  line_term (files_of c) (LPipes (PrCatF f) fs) W s ->
  line_term (files_of (<[N := P]> c)) (LPipes (PrCatF f) fs) W s.
Proof using.
  intros Hc HN HP H. destruct (files_trunc c N b0 P f Hc HN HP) as (HL & HLP & Hfc & _).
  remember (LPipes (PrCatF f) fs) as l eqn:Hl.
  destruct H as [p fs' so Hn Hso | p fs' so W' s' Hso Ht]; injection Hl as -> ->.
  - destruct (prod_trunc _ (files_of (<[N := P]> c)) _ _ f so HLP Hfc Hso) as (so' & Hso' & Hcs & _).
    rewrite -Hcs. apply lt_here; [exact Hn | exact Hso'].
  - destruct (prod_trunc _ (files_of (<[N := P]> c)) _ _ f so HLP Hfc Hso) as (so' & Hso' & Hcs & Hw).
    rewrite -Hcs. apply lt_next; [exact Hso' |].
    exact (sfx_term_trunc (files_of c) _ _ _ _ _ _ _ _ _ HL HLP Ht Hw).
Qed.

(* THE TRUNCATION LEMMA (review S2, at every filter stage list, at one
   name): a run at a state whose file [N] holds [b0], whose printed
   content, if a prefix of [b0], is a prefix of [P], stays a run -- with
   the SAME block -- at the state whose [N] holds [b0]'s prefix [P] *)
Theorem blocks_trunc c N b0 P f fs ss b :
  fstate_ok c -> c !! N = Some b0 -> P `prefix_of` b0 ->
  line_run (files_of c) (LPipes (PrCatF f) fs) ss -> merge_all ss b ->
  (forall x, last ss = Some x -> x `prefix_of` b0 -> x `prefix_of` P) ->
  line_blocks (files_of (<[N := P]> c)) (LPipes (PrCatF f) fs) b.
Proof using.
  intros Hc HN HP Hr Hm Hx. exists ss.
  split; [exact (line_run_trunc c N b0 P f fs ss Hc HN HP Hr Hx) | exact Hm].
Qed.

(* ...and a terminal block is one at every prefix *)
Theorem terms_trunc c N b0 P f fs b :
  fstate_ok c -> c !! N = Some b0 -> P `prefix_of` b0 ->
  plalt_ok (files_of c) (LPipes (PrCatF f) fs) (PLTerm b) ->
  plalt_ok (files_of (<[N := P]> c)) (LPipes (PrCatF f) fs) (PLTerm b).
Proof using.
  intros Hc HN HP [Hne (b' & (W & t & Wm & sp & Hlt & HWm & Hsp & Hm) & Hp)].
  split; [exact Hne |]. exists b'. split; [| exact Hp]. exists W, t, Wm, sp.
  split_and!; [exact (line_term_trunc c N b0 P f fs W t Hc HN HP Hlt) | exact HWm | exact Hsp | exact Hm].
Qed.

(* ===================================================================== *)
(*  5.  THE SEARCH SPACE: per-round candidates at the round's state       *)
(* ===================================================================== *)

Definition pl_cands (fc : bytes -> option bytes) (l : pline') : list plalt :=
  [PLPanic; PLRun []; PLRun (pl_exfb l)]
  ++ (PLRun <$> (line_runs fc l ≫= pde_merges))
  ++ (PLTerm <$>
        (line_terms fc l ≫= fun ws =>
           pde_merges ws.1 ≫= fun Wm =>
           prefixes ws.2 ≫= fun sp =>
           pde_merges [Wm ++ u_prompt; sp] ≫= prefixes)).

Lemma pl_cands_complete fc l x : plsafe l x \/ plalt_ok fc l x -> x ∈ pl_cands fc l.
Proof using.
  rewrite /pl_cands. intros [[-> | [-> | ->]] | Hok].
  - apply elem_of_app. left. apply elem_of_list_here.
  - apply elem_of_app. left. apply elem_of_list_further, elem_of_list_here.
  - apply elem_of_app. left. apply elem_of_list_further, elem_of_list_further, elem_of_list_here.
  - destruct x as [| b | b].
    + apply elem_of_app. left. apply elem_of_list_here.
    + destruct Hok as (ss & Hr & Hm).
      apply elem_of_app. right. apply elem_of_app. left.
      apply elem_of_list_fmap. exists b. split; [reflexivity |].
      apply elem_of_list_bind. exists ss.
      split; [by apply elem_of_pde_merges | by apply line_runs_spec].
    + destruct Hok as [_ (b' & (W & s & Wm & sp & Hlt & HW & Hsp & Hb) & Hbb)].
      apply elem_of_app. right. apply elem_of_app. right.
      apply elem_of_list_fmap. exists b. split; [reflexivity |].
      apply elem_of_list_bind. exists (W, s). split; [| by apply line_terms_spec].
      apply elem_of_list_bind. exists Wm. split; [| by apply elem_of_pde_merges].
      apply elem_of_list_bind. exists sp. split; [| by apply prefixes_spec].
      apply elem_of_list_bind. exists b'. split; [by apply prefixes_spec | by apply elem_of_pde_merges].
Qed.

Lemma ralt_cands_enc l r : ralt_ok l r -> ralt_enc r ∈ ralt_cands l.
Proof using.
  intros H. pose proof (ralt_cands_canon l (ralt_enc r)) as Hc. rewrite ralt_dec_enc in Hc.
  exact (Hc H).
Qed.

(* THE SECCOMP ROUND'S CANONICAL BYTES (seccomp design section 3): D4
   makes a seccomp line the input's last complete one with nothing typed
   after it, so no input point's [done_of] holds it and its continuation
   is read by no checked point -- one nonempty representative stands for
   every [US u] ([ucanon]).  [u_seg_at] re-resolves to it. *)
Definition us0 : list (bv 8) := [wl_nl].
Definition ucanon (a : ualt) : ualt := match a with US _ => US us0 | _ => a end.

Lemma uok_ucanon adm s l a : uok adm s l a -> uok adm s l (ucanon a).
Proof using.
  destruct a as [r | x | x | u]; cbn [ucanon]; try (intros H; exact H).
  intros H. destruct l as [| | | [|] |]; cbn [uok] in H |- *; first [contradiction | discriminate].
Qed.

(* the codes a line admits at a state: the file's canonical codes at a
   file line, the pipeline's candidates at the round's content at a
   pipeline, the shell's three and the canonical terminal arm at a
   seccomp line *)
Definition ucands (s : fstate) (l : uline) : list nat :=
  match l with
  | LPipe p n => (fun x => ualt_code (upl p x)) <$> pl_cands (files_of s) (LPipes p n)
  | LSecc _ => ((fun c => 4 * c) <$> ralt_cands l) ++ [ualt_code (US us0)]
  | _ => (fun c => 4 * c) <$> ralt_cands l
  end.

Lemma ucands_complete adm s l a : uok adm s l a -> ualt_code (ucanon a) ∈ ucands s l.
Proof using.
  intros H. destruct l as [ws | ws N | N | p n | ws].
  1-3: destruct a as [r | x | x | u]; cbn [uok] in H; try contradiction;
       cbn [ucands ucanon ualt_code]; apply elem_of_list_fmap; exists (ralt_enc r);
       split; [reflexivity | exact (ralt_cands_enc _ r H)].
  2: { destruct a as [r | x | x | u]; cbn [uok] in H; try contradiction;
       cbn [ucands ucanon ualt_code]; apply elem_of_app.
       - left. apply elem_of_list_fmap. exists (ralt_enc r).
         split; [reflexivity | exact (ralt_cands_enc _ r H)].
       - right. apply elem_of_list_here. }
  destruct (uok_pipe _ _ _ _ _ H) as (x & -> & Hx). cbn [ucands].
  rewrite (_ : ucanon (upl p x) = upl p x); [| by destruct p].
  apply elem_of_list_fmap. exists x. split; [reflexivity |].
  apply pl_cands_complete. destruct Hx as [Hs | [_ Hok]]; [left | right]; assumption.
Qed.

(* THE DEPENDENT PRODUCT: each round's candidates at the state the
   earlier choices leave *)
Fixpoint ualts_dep (s : fstate) (bs : list bytes) : list (list nat) :=
  match bs with
  | [] => [[]]
  | b :: bs' =>
      ucands s (uline_of_u b) ≫= fun c =>
        cons c <$> ualts_dep (ustep s (uline_of_u b) (ualt_dec c)) bs'
  end.

Lemma um_upto_cons (M : lmodel) c cs s b bs i :
  lm_upto M (c :: cs) s (b :: bs) (S i) = lm_upto M cs (lm_step M s (lm_of M b) (lm_dec M c)) bs i.
Proof using. symmetry. exact (lm_upto_drop M (c :: cs) s (b :: bs) 1 i). Qed.

Lemma ualts_dep_intro (adm : pline' -> bool) (adm_s : list (list (bv 8)) -> bool) s bs cs :
  length cs = length bs ->
  (forall i, i < length bs ->
             cs !!! i ∈ ucands (lm_upto (ulm adm adm_s) cs s bs i) (uline_of_u (bs !!! i))) ->
  cs ∈ ualts_dep s bs.
Proof using.
  revert s cs. induction bs as [| b bs IH]; intros s cs Hl H.
  - destruct cs; [apply elem_of_list_here | discriminate Hl].
  - destruct cs as [| c cs]; [discriminate Hl |]. cbn [ualts_dep].
    apply elem_of_list_bind. exists c. split.
    + apply elem_of_list_fmap. exists cs. split; [reflexivity |].
      apply IH; [cbn in Hl; lia |]. intros i Hi.
      pose proof (H (S i) ltac:(cbn; lia)) as Hc.
      rewrite um_upto_cons in Hc. exact Hc.
    + exact (H 0 ltac:(cbn; lia)).
Qed.

(* ===================================================================== *)
(*  6.  THE CHECKED BLOCKS ARE ON THE WIRE                                *)
(* ===================================================================== *)
Section wire.
  Context (M : lmodel).

  Lemma um_seq_split ps cs s bs q i :
    i < q -> exists A B, lm_seq M ps cs s bs q = A ++ lm_blk M ps cs s bs i ++ B.
  Proof using.
    induction q as [| q IH]; intros Hi; [lia |]. rewrite lm_seq_S.
    destruct (decide (i = q)) as [-> | Hne].
    - exists (lm_seq M ps cs s bs q), []. by rewrite app_nil_r.
    - destruct (IH ltac:(lia)) as (A & B & HE).
      exists A, (B ++ lm_blk M ps cs s bs q). rewrite HE. by rewrite -!app_assoc.
  Qed.

  (* the transcript read at two choice lists that agree below a bound *)
  Lemma um_pro_idx_at_ext cs1 cs2 q :
    (forall j, j < q -> lm_panic M (lm_at M cs1 j) = lm_panic M (lm_at M cs2 j)) ->
    lm_pro_idx M cs1 q = lm_pro_idx M cs2 q.
  Proof using.
    induction q as [| q IH]; intros H; [reflexivity |].
    rewrite !lm_pro_idx_S IH; [| intros j Hj; apply H; lia]. by rewrite (H q ltac:(lia)).
  Qed.

  Lemma um_upto_at_ext cs1 cs2 s bs q :
    (forall j, j < q -> forall st l,
        lm_step M st l (lm_at M cs1 j) = lm_step M st l (lm_at M cs2 j)) ->
    lm_upto M cs1 s bs q = lm_upto M cs2 s bs q.
  Proof using.
    induction q as [| q IH]; intros H; [reflexivity |].
    cbn [lm_upto]. rewrite IH; [| intros j Hj; apply H; lia]. apply H. lia.
  Qed.

  Lemma um_seq_at_ext ps cs1 cs2 s bs q :
    (forall j, j < q -> lm_at M cs1 j = lm_at M cs2 j) ->
    lm_seq M ps cs1 s bs q = lm_seq M ps cs2 s bs q.
  Proof using.
    intros H. induction q as [| q IH]; [reflexivity |].
    rewrite !lm_seq_S IH; [| intros j Hj; apply H; lia]. f_equal.
    rewrite /lm_blk /lm_cont_at (H q ltac:(lia)).
    rewrite (um_upto_at_ext cs1 cs2 s bs q);
      [| intros j Hj st l; rewrite (H j ltac:(lia)); reflexivity].
    rewrite (um_pro_idx_at_ext cs1 cs2 q); [reflexivity |].
    intros j Hj. by rewrite (H j ltac:(lia)).
  Qed.

  Lemma um_sess_at_ext ps cs1 cs2 s I :
    (forall j, j < nlines I -> lm_at M cs1 j = lm_at M cs2 j) ->
    lm_sess M ps cs1 s I = lm_sess M ps cs2 s I.
  Proof using. intros H. by rewrite /lm_sess (um_seq_at_ext ps cs1 cs2 s _ _ H). Qed.

  Lemma um_seq_cont_ext ps cs s1 s2 bs q :
    (forall i, i < q -> lm_cont_at M ps cs s1 bs i = lm_cont_at M ps cs s2 bs i) ->
    lm_seq M ps cs s1 bs q = lm_seq M ps cs s2 bs q.
  Proof using.
    intros H. induction q as [| q IH]; [reflexivity |].
    rewrite !lm_seq_S IH; [| intros i Hi; apply H; lia].
    by rewrite /lm_blk (H q ltac:(lia)).
  Qed.

  Lemma um_blk_bs_ext ps cs s bs1 bs2 i :
    (forall j, j <= i -> bs1 !!! j = bs2 !!! j) ->
    lm_blk M ps cs s bs1 i = lm_blk M ps cs s bs2 i.
  Proof using.
    intros H. rewrite /lm_blk /lm_cont_at (H i ltac:(lia)).
    by rewrite (lm_upto_bs_ext M cs s bs1 bs2 i ltac:(intros j Hj; apply H; lia)).
  Qed.

  Lemma um_pres_bodies seg p j :
    p ∈ in_pres seg -> j < nlines (ins p) ->
    bodies_of (ins p) !!! j = bodies_of (ins seg) !!! j.
  Proof using.
    intros Hp Hj.
    destruct (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp) as [z Hz].
    assert (Hpre : ins p `prefix_of` ins seg) by (rewrite Hz ins_app; by apply prefix_app_r).
    destruct (bodies_of_prefix _ _ Hpre) as [w Hw].
    rewrite Hw !list_lookup_total_alt lookup_app_l; [reflexivity | rewrite /nlines in Hj; lia].
  Qed.

  (* every block the wire checks is a contiguous piece of the wire *)
  Lemma um_blk_on_wire seg ps cs s i :
    (forall p, p ∈ in_pres seg -> lm_disc_pt M ps cs s p) ->
    i < nlines_max (in_pres seg) ->
    infixed (lm_blk M ps cs s (bodies_of (ins seg)) i) (obs_wire Uart0 seg).
  Proof using.
    intros Hpt Hi.
    destruct (decide (in_pres seg = [])) as [Hz | Hz]; [rewrite Hz in Hi; cbn in Hi; lia |].
    destruct (nlines_max_mem (in_pres seg) Hz) as (p & Hp & Hpe).
    rewrite -Hpe in Hi.
    assert (Hin : infixed (lm_blk M ps cs s (bodies_of (ins p)) i)
                          (lm_sess M ps cs s (done_of (ins p)))).
    { destruct (um_seq_split ps cs s (bodies_of (ins p)) (nlines (ins p)) i Hi) as (A & B & HE).
      rewrite /lm_sess bodies_of_done nlines_done HE.
      apply infixed_app_ctx, infixed_here. }
    rewrite -(um_blk_bs_ext ps cs s (bodies_of (ins p)) (bodies_of (ins seg)) i);
      [| intros j Hj; apply (um_pres_bodies seg p j Hp); lia].
    eapply infixed_prefix;
      [| exact (obs_wire_prefix Uart0 p seg
                  (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp))].
    eapply infixed_prefix; [exact Hin | exact (Hpt p Hp)].
  Qed.
End wire.

(* an input point holds strictly fewer inputs than the segment *)
Lemma um_pres_ins_lt seg p : p ∈ in_pres seg -> length (ins p) < length (ins seg).
Proof using.
  revert p. induction seg as [| e seg IH]; intros p Hp; [by apply elem_of_nil in Hp |].
  change (e :: seg) with ([e] ++ seg). rewrite ins_app length_app.
  destruct e as [[] c | [] c | |]; cbn [in_pres] in Hp.
  1: { rewrite ins_in. apply elem_of_cons in Hp as [-> | Hp]; [cbn; lia |].
       apply elem_of_list_fmap in Hp as (p' & -> & Hp').
       change (ObsUartIn Uart0 c :: p') with ([ObsUartIn Uart0 c] ++ p').
       rewrite ins_app ins_in length_app. pose proof (IH p' Hp'). cbn [length]. lia. }
  all: rewrite ins_snoc_other; [| exact I].
  all: apply elem_of_list_fmap in Hp as (p' & -> & Hp').
  all: match goal with |- length (ins (?e :: ?q)) < _ => change (e :: q) with ([e] ++ q) end.
  all: rewrite ins_app ins_snoc_other; [| exact I].
  all: cbn [length app]; exact (IH p' Hp').
Qed.

(* ...so at a segment whose input ends at a newline, no input point holds
   its last line complete *)
Lemma um_pres_nlines seg p :
  p ∈ in_pres seg -> rest_of (ins seg) = [] -> nlines (ins p) <= nlines (ins seg) - 1.
Proof using.
  intros Hp Hr. pose proof (um_pres_ins_lt seg p Hp) as Hlt.
  destruct (ins_prefix _ _ (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp)) as [z Hz].
  assert (Hz0 : z <> []) by (intros ->; rewrite app_nil_r in Hz; rewrite Hz in Hlt; lia).
  rewrite -(ll_nlines_removelast (ins seg) Hr). apply nlines_prefix.
  rewrite Hz removelast_app; [| exact Hz0]. by eexists.
Qed.

(* ===================================================================== *)
(*  7.  THE BOOT-STATE CANONICALISATION, ONE NAME AT A TIME               *)
(*                                                                        *)
(*  A disciplined era has a disciplined boot state among [scandsU seg]:   *)
(*  the maps over the files the era's lines name, each content a         *)
(*  subsequence of the wire ([prod_maps]).  Two steps, both through the   *)
(*  seam.  A file no line names is never read or moved, so it may be     *)
(*  dropped ([disc_agree]).  A named file's content may be cut to the     *)
(*  longest prefix of it the checked rounds printed, every other file     *)
(*  carried along unchanged ([u_canon_name]) -- and that is done one name *)
(*  at a time.                                                            *)
(* ===================================================================== *)

(* the files an era's complete lines name *)
Definition seg_names (seg : list mobs) : list (list (bv 8)) :=
  remove_dups (omap line_file (uline_of_u <$> bodies_of (ins seg))).

Lemma seg_names_line seg i g :
  i < nlines (ins seg) ->
  line_file (uline_of_u (bodies_of (ins seg) !!! i)) = Some g -> g ∈ seg_names seg.
Proof using.
  intros Hi Hg. rewrite /seg_names elem_of_remove_dups. apply elem_of_list_omap.
  exists (uline_of_u (bodies_of (ins seg) !!! i)). split; [| exact Hg].
  apply elem_of_list_fmap. exists (bodies_of (ins seg) !!! i). split; [reflexivity |].
  apply elem_of_list_lookup_total_2. exact Hi.
Qed.

(* THE PRODUCT BOOT-STATE CHOOSER: every map over the names [Ns] whose
   contents are drawn from [vs] -- a finite list, only ever decided *)
Fixpoint prod_maps (Ns : list (list (bv 8))) (vs : list bytes) : list fstate :=
  match Ns with
  | [] => [∅]
  | N :: Ns' =>
      prod_maps Ns' vs ++ (vs ≫= fun v => (fun m => <[N := v]> m) <$> prod_maps Ns' vs)
  end.

Lemma prod_maps_complete Ns vs (s : fstate) :
  NoDup Ns -> (forall N c, s !! N = Some c -> N ∈ Ns /\ c ∈ vs) -> s ∈ prod_maps Ns vs.
Proof using.
  revert s. induction Ns as [| N Ns IH]; intros s Hnd Hs; cbn [prod_maps].
  - assert (Hs0 : s = ∅).
    { apply map_empty. intros M. destruct (s !! M) as [c |] eqn:Hc; [| exact Hc].
      destruct (Hs M c Hc) as [HM _]. by apply elem_of_nil in HM. }
    rewrite Hs0. apply elem_of_list_here.
  - apply NoDup_cons in Hnd as [HN Hnd].
    apply elem_of_app. destruct (s !! N) as [c |] eqn:Hc.
    + right. apply elem_of_list_bind. exists c. split; [| exact (proj2 (Hs N c Hc))].
      apply elem_of_list_fmap. exists (delete N s). split; [by rewrite insert_delete |].
      apply IH; [exact Hnd |]. intros M c' HM.
      destruct (decide (M = N)) as [-> | HMN]; [by rewrite lookup_delete in HM |].
      rewrite lookup_delete_ne in HM; [| congruence].
      destruct (Hs M c' HM) as [HMin Hc']. split; [| exact Hc'].
      apply elem_of_cons in HMin as [-> | HMin]; [done | exact HMin].
    + left. apply IH; [exact Hnd |]. intros M c' HM.
      destruct (Hs M c' HM) as [HMin Hc']. split; [| exact Hc'].
      apply elem_of_cons in HMin as [-> | HMin]; [congruence | exact HMin].
Qed.

(* the boot states worth trying *)
Definition scandsU (seg : list mobs) : list fstate :=
  prod_maps (seg_names seg) (ud_sublists (obs_wire Uart0 seg)).

(* ...at an admission [ud_adm] describes, to the end of the file *)
Section canon.
  Context (adm : pline' -> bool) (adm_s : list (list (bv 8)) -> bool) (gp : bool) (gpat : bytes).
  Hypothesis Hadm : ud_adm adm gp gpat.
  Local Notation U := (ulm adm adm_s).

(* the terminal arm of a seccomp round is admitted only at a seccomp line,
   where every output is mergeable *)
Lemma um_secc_merge st l u c : uok adm st l (US u) -> umerge adm l c.
Proof using.
  intros H. destruct l as [ws | ws N | N | [ws | f] n | ws]; cbn [uok umerge] in H |- *;
    first [contradiction | exact I].
Qed.

(* the state a checked round starts in is a state *)
Lemma upto_fok seg (s : fstate) cs i :
  fstate_ok s -> lm_disc_input U (ins seg) -> lm_alts_ok U s (ins seg) cs ->
  i <= nlines (ins seg) -> fstate_ok (lm_upto U cs s (bodies_of (ins seg)) i).
Proof using.
  intros Hs Hin Halts Hi. apply (lm_upto_st_ok U (ulm_laws adm adm_s)); [exact Hs | |].
  - intros j Hj. apply (uline_of_u_ok adm adm_s).
    destruct (lookup_lt_is_Some_2 (bodies_of (ins seg)) j ltac:(rewrite /nlines in Hi; lia))
      as [b Hb].
    rewrite (list_lookup_total_correct _ _ _ Hb). exact (Forall_lookup_1 _ _ _ _ (proj1 Hin) Hb).
  - intros j Hj. apply (proj2 Halts). lia.
Qed.

(* ---- STEP ONE: the files no line names are dropped ---- *)

(* the chains at two boot states agreeing on the era's named files agree
   there at every round *)
Lemma upto_agree seg cs (s s' : fstate) i :
  (forall N, N ∈ seg_names seg -> s !! N = s' !! N) ->
  i <= nlines (ins seg) ->
  forall N, N ∈ seg_names seg ->
    (lm_upto U cs s (bodies_of (ins seg)) i : fstate) !! N = lm_upto U cs s' (bodies_of (ins seg)) i !! N.
Proof using.
  intros Hag. induction i as [| i IH]; intros Hi; [exact Hag |].
  cbn [lm_upto]. change (lm_step U) with ustep. change (lm_of U) with uline_of_u.
  apply (ustep_agree (seg_names seg)); [apply IH; lia |].
  intros g Hg. exact (seg_names_line seg i g ltac:(lia) Hg).
Qed.

Lemma disc_agree seg (s s' : fstate) :
  (forall N, N ∈ seg_names seg -> s !! N = s' !! N) ->
  lm_disc_seg' U s seg -> lm_disc_seg' U s' seg.
Proof using.
  intros Hag [Hin (ps & cs & Halts & Hd4 & Hall)].
  assert (Hf : forall i, i < nlines (ins seg) -> forall g,
             line_file (uline_of_u (bodies_of (ins seg) !!! i)) = Some g ->
             files_of (lm_upto U cs s (bodies_of (ins seg)) i) g
             = files_of (lm_upto U cs s' (bodies_of (ins seg)) i) g).
  { intros i Hi g Hg. apply (upto_agree seg cs s s' i Hag); [lia |].
    exact (seg_names_line seg i g Hi Hg). }
  assert (Hok : forall i, i < nlines (ins seg) ->
             lm_ok U (lm_upto U cs s (bodies_of (ins seg)) i)
               (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i))
    by exact (proj2 Halts).
  assert (Hcont : forall i, i < nlines (ins seg) ->
             lm_cont U (lm_upto U cs s' (bodies_of (ins seg)) i)
               (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i)
             = lm_cont U (lm_upto U cs s (bodies_of (ins seg)) i)
                 (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i)).
  { intros i Hi. symmetry. exact (ucont_local adm _ _ _ _ (Hf i Hi) (Hok i Hi)). }
  split; [exact Hin |]. exists ps, cs. split_and!.
  - split; [exact (proj1 Halts) |]. intros i Hi.
    exact (uok_local adm _ _ _ _ (Hf i Hi) (Hok i Hi)).
  - intros i Hi Hex Hm. apply (Hd4 i Hi).
    + destruct Hex as (c & Hc & Ht). exists c. split; [| exact Ht].
      apply (uok_local adm (lm_upto U cs s' (bodies_of (ins seg)) i)); [| exact Hc].
      intros g Hg. symmetry. exact (Hf i Hi g Hg).
    + rewrite -(Hcont i Hi). exact Hm.
  - intros p Hp. destruct (Hall p Hp) as [Hpo Hpt]. split; [exact Hpo |].
    assert (Hq : nlines (ins p) <= nlines (ins seg)).
    { apply nlines_prefix, ins_prefix.
      exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp). }
    assert (E : lm_seq U ps cs s' (bodies_of (ins p)) (nlines (ins p))
                = lm_seq U ps cs s (bodies_of (ins p)) (nlines (ins p))).
    { apply um_seq_cont_ext. intros i Hi. rewrite /lm_cont_at. f_equal.
      assert (Hbs : forall j, j <= i -> bodies_of (ins p) !!! j = bodies_of (ins seg) !!! j)
        by (intros j Hj; apply (um_pres_bodies seg p j Hp); lia).
      rewrite (lm_upto_bs_ext U cs s' (bodies_of (ins p)) (bodies_of (ins seg)) i);
        [| intros j Hj; apply Hbs; lia].
      rewrite (lm_upto_bs_ext U cs s (bodies_of (ins p)) (bodies_of (ins seg)) i);
        [| intros j Hj; apply Hbs; lia].
      rewrite (Hbs i ltac:(lia)). exact (Hcont i ltac:(lia)). }
    rewrite /lm_disc_pt /lm_sess bodies_of_done nlines_done E.
    rewrite /lm_disc_pt /lm_sess bodies_of_done nlines_done in Hpt. exact Hpt.
Qed.

(* ---- STEP TWO: one named file's content, cut ---- *)

(* THE PRISTINE PAIR AT ONE NAME: until a round sets [N], the chain at the
   cut boot state is the chain at [b0] with [N] cut to [P]; from the first
   round that sets [N] the two agree.  Read through the seam: a round
   either commutes with setting [N] or does not depend on it
   ([ustep_ins_cases]). *)
Lemma upto_pristine cs (s : fstate) N b0 P bs i :
  s !! N = Some b0 ->
  ((lm_upto U cs s bs i : fstate) !! N = Some b0
   /\ lm_upto U cs (<[N := P]> s) bs i = <[N := P]> (lm_upto U cs s bs i : fstate))
  \/ lm_upto U cs s bs i = lm_upto U cs (<[N := P]> s) bs i.
Proof using.
  intros Hs. induction i as [| i IH]; [left; split; [exact Hs | reflexivity] |].
  cbn [lm_upto]. destruct IH as [[H1 H2] | He]; [| right; by rewrite He].
  rewrite H2. change (lm_step U) with ustep. change (lm_of U) with uline_of_u.
  destruct (ustep_ins_cases (uline_of_u (bs !!! i)) (lm_at U cs i) N) as [Hc | Hi].
  - left. rewrite (Hc P (lm_upto U cs s bs i)). split; [| reflexivity].
    rewrite -(insert_id (lm_upto U cs s bs i : fstate) N b0 H1).
    rewrite (Hc b0 (lm_upto U cs s bs i)). apply lookup_insert.
  - right. rewrite -{1}(insert_id (lm_upto U cs s bs i : fstate) N b0 H1). apply Hi.
Qed.

(* a round printing differently at the two chains is [cat N] *)
Lemma ucont_pristine t N P l a :
  ucont t l a <> ucont (<[N := P]> t) l a -> a = UR RCRan /\ lname l = N.
Proof using.
  destruct a as [r | x | x | u]; cbn [ucont];
    [| intros H; exfalso; exact (H eq_refl) | intros H; exfalso; exact (H eq_refl)
     | intros H; exfalso; exact (H eq_refl)].
  intros H. pose proof (cont_state_ne _ _ l r H) as ->. split; [reflexivity |].
  destruct (decide (lname l = N)) as [E | E]; [exact E |]. exfalso. apply H.
  cbn [cont]. rewrite lookup_insert_ne; [reflexivity | congruence].
Qed.

(* WHAT A CHECKED ROUND AT A STATE [c] WHOSE [N] HOLDS [b0] NEEDS OF [P]:
   at a [cat g | ..] pipeline that printed [b], a run of [b] whose printed
   content, if it is a prefix of [b0], fits in [P] *)
Definition ud_good (c : fstate) (b0 P : bytes) (l : uline) (a : ualt) : Prop :=
  forall g n b, l = LPipe (PrCatF g) n -> a = UPC (PLRun b) ->
    adm (LPipes (PrCatF g) n) = true ->
    plalt_ok (files_of c) (LPipes (PrCatF g) n) (PLRun b) ->
    exists ss, line_run (files_of c) (LPipes (PrCatF g) n) ss /\ merge_all ss b
               /\ (forall x, last ss = Some x -> x `prefix_of` b0 -> x `prefix_of` P).

Lemma ud_good_mono c b0 P P' l a : P `prefix_of` P' -> ud_good c b0 P l a -> ud_good c b0 P' l a.
Proof using.
  intros HP H g n b Hl Ha Had Hok. destruct (H g n b Hl Ha Had Hok) as (ss & Hr & Hm & Hx).
  exists ss. split_and!; [exact Hr | exact Hm |]. intros x Hl' Hxb. etrans; [exact (Hx x Hl' Hxb) | exact HP].
Qed.

(* one more round: [P] grows to the round's printed content when that is
   a longer prefix of [b0] *)
Lemma ud_good_step c b0 P l a (Wr : bytes) :
  P `prefix_of` b0 -> P `sublist_of` Wr ->
  (forall b, a = UPC (PLRun b) -> b `sublist_of` Wr) ->
  exists P', P `prefix_of` P' /\ P' `prefix_of` b0 /\ P' `sublist_of` Wr /\ ud_good c b0 P' l a.
Proof using.
  intros HPb HPw Hbw.
  assert (Hkeep : ud_good c b0 P l a -> exists P', P `prefix_of` P' /\ P' `prefix_of` b0
                                           /\ P' `sublist_of` Wr /\ ud_good c b0 P' l a)
    by (intros Hg; exists P; split_and!; [reflexivity | exact HPb | exact HPw | exact Hg]).
  destruct l as [ws | ws N | N | [ws | g] n | ws];
    try (apply Hkeep; intros g' n' b' Hl; discriminate Hl).
  destruct a as [r | x | [| b | b] | u];
    try (apply Hkeep; intros g' n' b' _ Ha; discriminate Ha).
  destruct (decide (adm (LPipes (PrCatF g) n) = true
                    /\ plalt_ok (files_of c) (LPipes (PrCatF g) n) (PLRun b)))
    as [[Had (ss & Hr & Hm)] | Hno].
  2: { apply Hkeep. intros g' n' b' [= <- <-] [= <-] Had Hok. exfalso. apply Hno. by split. }
  assert (Hwit : forall P', (forall x, last ss = Some x -> x `prefix_of` b0 -> x `prefix_of` P') ->
                            ud_good c b0 P' (LPipe (PrCatF g) n) (UPC (PLRun b))).
  { intros P' Hx g' n' b' [= <- <-] [= <-] _ _. exists ss. split_and!; [exact Hr | exact Hm | exact Hx]. }
  destruct (last ss) as [x |] eqn:Hl.
  2: { exists P. split_and!; [reflexivity | exact HPb | exact HPw |].
       apply Hwit. intros x' Hx'. try rewrite Hl in Hx'. discriminate Hx'. }
  destruct (decide (x `prefix_of` b0)) as [Hxb | Hxb].
  2: { exists P. split_and!; [reflexivity | exact HPb | exact HPw |].
       apply Hwit. intros x' Hx' Hx'b. try rewrite Hl in Hx'. injection Hx' as <-.
       exfalso. exact (Hxb Hx'b). }
  destruct (prefix_weak_total P x b0 HPb Hxb) as [HPx | HxP].
  - exists x. split_and!; [exact HPx | exact Hxb | |].
    + etrans; [exact (merge_all_sublist ss b Hm x (last_Some_elem_of ss x Hl)) |].
      exact (Hbw b eq_refl).
    + apply Hwit. intros x' Hx' _. try rewrite Hl in Hx'. injection Hx' as <-. reflexivity.
  - exists P. split_and!; [reflexivity | exact HPb | exact HPw |].
    apply Hwit. intros x' Hx' _. try rewrite Hl in Hx'. injection Hx' as <-. exact HxP.
Qed.

(* ADMISSIBILITY AT THE CUT STATE, at a round whose [N] still holds [b0].
   Off [N]: locality.  On [N]: a redirect and [cat N] read no state to
   admit; a [cat N] pipeline's blocks truncate. *)
Lemma uok_trunc c N b0 P l a :
  fstate_ok c -> c !! N = Some b0 -> P `prefix_of` b0 -> ud_good c b0 P l a ->
  uok adm c l a -> uok adm (<[N := P]> c) l a.
Proof using.
  intros Hc HN HP Hg Hok.
  destruct (decide (line_file l = Some N)) as [Hf | Hf].
  2: { apply (uok_local _ c); [| exact Hok].
       intros g Hg'. rewrite /files_of lookup_insert_ne; [reflexivity |].
       intros ->. exact (Hf Hg'). }
  destruct l as [ws | ws M | M | [ws | g] n | ws]; cbn [line_file] in Hf; try discriminate Hf;
    [exact Hok | exact Hok |].
  injection Hf as ->.
  destruct (uok_pipe _ _ _ _ _ Hok) as (x & -> & Hx). apply uok_upl.
  destruct Hx as [Hs | [Ha Hb]]; [left; exact Hs | right; split; [exact Ha |]].
  destruct x as [| b | b].
  - exact I.
  - destruct (Hg N n b eq_refl eq_refl Ha Hb) as (ss & Hr & Hm & Hx).
    exact (blocks_trunc c N b0 P N n ss b Hc HN HP Hr Hm Hx).
  - exact (terms_trunc c N b0 P N n b Hc HN HP Hb).
Qed.

(* THE CANONICALISATION AT ONE NAME: a disciplined era whose boot file [N]
   holds [b0] is disciplined at the boot state whose [N] holds a prefix of
   [b0] that is a subsequence of the wire, every other file unchanged *)
Theorem u_canon_name seg (s : fstate) N b0 :
  fstate_ok s -> s !! N = Some b0 -> lm_disc_seg' U s seg ->
  exists P, P `prefix_of` b0 /\ P ∈ ud_sublists (obs_wire Uart0 seg)
            /\ lm_disc_seg' U (<[N := P]> s) seg.
Proof using Hadm.
  intros Hok HN Hd.
  destruct (decide (b0 ∈ ud_sublists (obs_wire Uart0 seg))) as [Hb | Hnb].
  { exists b0. split_and!; [reflexivity | exact Hb |]. by rewrite insert_id. }
  destruct Hd as (Hin & ps & cs & Halts & Hd4 & Hall).
  assert (Hpt : forall p, p ∈ in_pres seg -> lm_disc_pt U ps cs s p)
    by (intros p Hp; exact (proj2 (Hall p Hp))).
  assert (Hwire : forall i, i < nlines_max (in_pres seg) ->
            infixed (lm_blk U ps cs s (bodies_of (ins seg)) i) (obs_wire Uart0 seg))
    by (intros i Hi; exact (um_blk_on_wire U seg ps cs s i Hpt Hi)).
  assert (Hmax : nlines_max (in_pres seg) <= nlines (ins seg)).
  { destruct (decide (in_pres seg = [])) as [Hz | Hz]; [rewrite Hz; cbn; lia |].
    destruct (nlines_max_mem (in_pres seg) Hz) as (pl & Hplin & Hpleq). rewrite -Hpleq.
    apply nlines_prefix, ins_prefix.
    exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) pl Hplin). }
  (* a checked round still at [b0] never prints [N] whole *)
  assert (Hnran : forall i, i < nlines_max (in_pres seg) ->
            (lm_upto U cs s (bodies_of (ins seg)) i : fstate) !! N = Some b0 ->
            lm_at U cs i = UR RCRan -> lname (lm_of U (bodies_of (ins seg) !!! i)) = N -> False).
  { intros i Hi Hs Ha Hl. apply Hnb, elem_of_ud_sublists, ud_infixed_sublist.
    apply (ud_infixed_trans _ (lm_blk U ps cs s (bodies_of (ins seg)) i));
      [| exact (Hwire i Hi)].
    assert (Hc : lm_cont U (lm_upto U cs s (bodies_of (ins seg)) i)
                   (lm_of U (bodies_of (ins seg) !!! i)) (UR RCRan) = b0 ++ u_prompt).
    { change (lm_cont U) with ucont. cbn [ucont cont]. rewrite Hl Hs. reflexivity. }
    rewrite /lm_blk /lm_cont_at Ha Hc. apply ud_infixed_mid. }
  (* THE LONGEST PRINTED PREFIX *)
  assert (HP : exists P, P `prefix_of` b0 /\ P `sublist_of` obs_wire Uart0 seg
                 /\ forall i, i < nlines_max (in_pres seg) ->
                      (lm_upto U cs s (bodies_of (ins seg)) i : fstate) !! N = Some b0 ->
                      ud_good (lm_upto U cs s (bodies_of (ins seg)) i) b0 P
                        (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i)).
  { cut (forall js, exists P, P `prefix_of` b0 /\ P `sublist_of` obs_wire Uart0 seg
            /\ Forall (fun i => i < nlines_max (in_pres seg) ->
                               (lm_upto U cs s (bodies_of (ins seg)) i : fstate) !! N = Some b0 ->
                               ud_good (lm_upto U cs s (bodies_of (ins seg)) i) b0 P
                                 (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i))
                      js).
    { intros Hc. destruct (Hc (seq 0 (nlines_max (in_pres seg)))) as (P & H1 & H2 & H3).
      exists P. split_and!; [exact H1 | exact H2 |]. intros i Hi Hs.
      rewrite Forall_forall in H3. apply H3; [apply elem_of_seq; lia | exact Hi | exact Hs]. }
    intros js. induction js as [| i js IH].
    { exists []. split_and!; [apply prefix_nil | apply sublist_nil_l | constructor]. }
    destruct IH as (P & HPb & HPw & HF).
    destruct (decide (i < nlines_max (in_pres seg)
                      /\ (lm_upto U cs s (bodies_of (ins seg)) i : fstate) !! N = Some b0))
      as [[Hi Hs] | Hno].
    2: { exists P. split_and!; [exact HPb | exact HPw |]. constructor; [| exact HF].
         intros Hi Hs. exfalso. apply Hno. by split. }
    destruct (ud_good_step (lm_upto U cs s (bodies_of (ins seg)) i) b0 P
                (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i)
                (obs_wire Uart0 seg) HPb HPw) as (P' & HPP & HP'b & HP'w & Hg).
    { intros b Hab. apply ud_infixed_sublist.
      apply (ud_infixed_trans _ (lm_blk U ps cs s (bodies_of (ins seg)) i));
        [| exact (Hwire i Hi)].
      assert (Hc : forall s' l, lm_cont U s' l (UPC (PLRun b)) = b ++ u_prompt) by reflexivity.
      rewrite /lm_blk /lm_cont_at Hab Hc. apply ud_infixed_mid. }
    exists P'. split_and!; [exact HP'b | exact HP'w |]. constructor; [intros _ _; exact Hg |].
    eapply Forall_impl; [exact HF |]. intros j Hj HjN Hjs.
    exact (ud_good_mono _ b0 P P' _ _ HPP (Hj HjN Hjs)). }
  destruct HP as (P & HPb & HPw & HPg).
  (* the unchecked rounds re-resolved to the silent round *)
  pose (cs' := imap (fun j c => if decide (j < nlines_max (in_pres seg)) then c
                               else unoc (uline_of_u (bodies_of (ins seg) !!! j))) cs).
  assert (Hlen : length cs' = length cs) by apply length_imap.
  assert (Hlt : forall j, j < nlines_max (in_pres seg) -> cs' !!! j = cs !!! j).
  { intros j Hj. destruct (decide (j < length cs)) as [Hjl | Hjl].
    - unfold cs'. rewrite list_lookup_total_imap; [| exact Hjl]. cbv beta.
      by rewrite decide_True.
    - assert (E1 : cs' !! j = None) by (apply lookup_ge_None_2; rewrite Hlen; lia).
      assert (E2 : cs !! j = None) by (apply lookup_ge_None_2; lia).
      rewrite !list_lookup_total_alt E1 E2. reflexivity. }
  assert (Hat : forall j, j < nlines_max (in_pres seg) -> lm_at U cs' j = lm_at U cs j)
    by (intros j Hj; rewrite /lm_at (Hlt j Hj); reflexivity).
  assert (Hge : forall j, nlines_max (in_pres seg) <= j -> j < nlines (ins seg) ->
                lm_at U cs' j = ualt_dec (unoc (uline_of_u (bodies_of (ins seg) !!! j)))).
  { intros j Hj Hjl. unfold lm_at, cs'. rewrite list_lookup_total_imap; [| rewrite (proj1 Halts); exact Hjl].
    cbv beta. rewrite decide_False; [reflexivity | lia]. }
  assert (Hup : forall i, i <= nlines_max (in_pres seg) ->
            lm_upto U cs' (<[N := P]> s) (bodies_of (ins seg)) i
            = lm_upto U cs (<[N := P]> s) (bodies_of (ins seg)) i).
  { intros i Hi. apply lm_upto_cs_ext. intros j Hj. apply Hlt. lia. }
  (* the checked rounds print the same at the cut boot state *)
  assert (Hcont : forall i, i < nlines_max (in_pres seg) ->
            lm_cont U (lm_upto U cs (<[N := P]> s) (bodies_of (ins seg)) i)
              (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i)
            = lm_cont U (lm_upto U cs s (bodies_of (ins seg)) i)
                (lm_of U (bodies_of (ins seg) !!! i)) (lm_at U cs i)).
  { intros i Hi. destruct (upto_pristine cs s N b0 P (bodies_of (ins seg)) i HN) as [[H1 H2] | He];
      [| by rewrite He].
    rewrite H2.
    destruct (decide (ucont (<[N := P]> (lm_upto U cs s (bodies_of (ins seg)) i))
                        (uline_of_u (bodies_of (ins seg) !!! i)) (lm_at U cs i)
                      = ucont (lm_upto U cs s (bodies_of (ins seg)) i)
                          (uline_of_u (bodies_of (ins seg) !!! i)) (lm_at U cs i)))
      as [E | Hne]; [exact E |].
    exfalso.
    destruct (ucont_pristine (lm_upto U cs s (bodies_of (ins seg)) i) N P
                (uline_of_u (bodies_of (ins seg) !!! i)) (lm_at U cs i)) as [Ha Hl].
    { intros E. apply Hne. by symmetry. }
    exact (Hnran i Hi H1 Ha Hl). }
  exists P. split_and!; [exact HPb | exact (elem_of_ud_sublists _ _ HPw) |].
  split; [exact Hin |]. exists ps, cs'. split_and!.
  - (* the range condition *)
    split; [rewrite Hlen; exact (proj1 Halts) |]. intros i Hi.
    destruct (decide (i < nlines_max (in_pres seg))) as [HiN | HiN].
    + rewrite (Hup i ltac:(lia)) (Hat i HiN).
      pose proof (proj2 Halts i Hi) as Ho.
      destruct (upto_pristine cs s N b0 P (bodies_of (ins seg)) i HN) as [[H1 H2] | He].
      * rewrite H2.
        exact (uok_trunc _ N b0 P _ _ (upto_fok seg s cs i Hok Hin Halts ltac:(lia))
                 H1 HPb (HPg i HiN H1) Ho).
      * rewrite -He. exact Ho.
    + rewrite (Hge i ltac:(lia) Hi). exact (unoc_ok adm _ _).
  - (* D4 *)
    intros i Hi Hex Hm. destruct (decide (i < nlines_max (in_pres seg))) as [HiN | HiN].
    + rewrite (Hup i ltac:(lia)) in Hex Hm. rewrite (Hat i HiN) (Hcont i HiN) in Hm.
      apply (Hd4 i Hi); [| exact Hm].
      destruct Hex as (c & Hc & Ht). exact (lml_term_st (ulm_laws adm adm_s) _ _ _ Hc Ht _).
    + assert (Hsd : forall l : uline, (exists ws, l = LSecc ws) \/ (forall ws, l <> LSecc ws))
        by (intros [| | | | ws']; [right; intros; discriminate .. | left; by exists ws']).
      destruct (Hsd (lm_of U (bodies_of (ins seg) !!! i))) as [[ws Hws] | Hns].
      * (* an unchecked seccomp line: D4 at the original resolution, where
           the line's every output is mergeable *)
        destruct Hex as (c & Hc & Ht). apply (Hd4 i Hi).
        -- exact (lml_term_st (ulm_laws adm adm_s) _ _ _ Hc Ht _).
        -- rewrite Hws. exact I.
      * exfalso. rewrite (Hge i ltac:(lia) Hi) in Hm.
        apply (umerge_prompt adm gp gpat Hadm (uline_of_u (bodies_of (ins seg) !!! i)));
          [exact Hns |].
        rewrite -(unoc_cont (lm_upto U cs' (<[N := P]> s) (bodies_of (ins seg)) i)
                   (uline_of_u (bodies_of (ins seg) !!! i))).
        exact Hm.
  - (* the checked points *)
    intros p Hp. destruct (Hall p Hp) as [Hpo Hpt'].
    assert (Hq : nlines (ins p) <= nlines_max (in_pres seg)) by exact (nlines_max_ge _ _ Hp).
    split.
    + rewrite /lm_pro_ok (lm_pro_idx_ext U cs' cs (nlines_max (in_pres seg)) Hlt (nlines (ins p)) Hq).
      exact Hpo.
    + rewrite /lm_disc_pt (lm_sess_cs_ext U ps cs' cs (<[N := P]> s) (done_of (ins p)));
        [| intros j Hj; rewrite nlines_done in Hj; apply Hlt; lia].
      assert (E : lm_seq U ps cs (<[N := P]> s) (bodies_of (ins p)) (nlines (ins p))
                  = lm_seq U ps cs s (bodies_of (ins p)) (nlines (ins p))).
      { apply um_seq_cont_ext. intros i Hi. rewrite /lm_cont_at. f_equal.
        assert (Hbs : forall j, j <= i -> bodies_of (ins p) !!! j = bodies_of (ins seg) !!! j)
          by (intros j Hj; apply (um_pres_bodies seg p j Hp); lia).
        rewrite (lm_upto_bs_ext U cs (<[N := P]> s) (bodies_of (ins p)) (bodies_of (ins seg)) i);
          [| intros j Hj; apply Hbs; lia].
        rewrite (lm_upto_bs_ext U cs s (bodies_of (ins p)) (bodies_of (ins seg)) i);
          [| intros j Hj; apply Hbs; lia].
        rewrite (Hbs i ltac:(lia)). exact (Hcont i ltac:(lia)). }
      rewrite /lm_sess bodies_of_done nlines_done E.
      rewrite /lm_disc_pt /lm_sess bodies_of_done nlines_done in Hpt'. exact Hpt'.
Qed.

(* THE CANONICALISATION: a disciplined era has a disciplined boot state
   among [scandsU] -- the unnamed files dropped, then each named file's
   content cut, one name at a time *)
Theorem u_canon_s seg (s : fstate) :
  fstate_ok s -> lm_disc_seg' U s seg ->
  exists s', s' ∈ scandsU seg /\ fstate_ok s' /\ lm_disc_seg' U s' seg.
Proof using Hadm.
  intros Hok Hd.
  (* the files no line names are dropped *)
  assert (Hs1 : exists s1 : fstate,
            (forall N c, s1 !! N = Some c -> s !! N = Some c /\ N ∈ seg_names seg)
            /\ (forall N, N ∈ seg_names seg -> s !! N = s1 !! N)).
  { exists (filter (fun kv : list (bv 8) * list (bv 8) => kv.1 ∈ seg_names seg) s). split.
    - intros N c Hc. apply map_lookup_filter_Some in Hc as [Hc HN]. by split.
    - intros N HN. destruct (s !! N) as [c |] eqn:Hc.
      + symmetry. apply map_lookup_filter_Some_2; [exact Hc | exact HN].
      + symmetry. apply map_lookup_filter_None. by left. }
  destruct Hs1 as (s1 & H1 & H1ag).
  assert (Hok1 : fstate_ok s1) by (intros N c Hc; exact (Hok N c (proj1 (H1 N c Hc)))).
  assert (Hd1 : lm_disc_seg' U s1 seg) by exact (disc_agree seg s s1 H1ag Hd).
  (* each named file's content cut, one name at a time *)
  assert (Hcanon : forall (L : list (list (bv 8))) t,
            fstate_ok t -> lm_disc_seg' U t seg ->
            (forall N c, t !! N = Some c -> N ∈ seg_names seg) ->
            (forall N c, t !! N = Some c -> N ∉ L -> c ∈ ud_sublists (obs_wire Uart0 seg)) ->
            exists t', fstate_ok t' /\ lm_disc_seg' U t' seg
                       /\ forall N c, t' !! N = Some c ->
                                      N ∈ seg_names seg /\ c ∈ ud_sublists (obs_wire Uart0 seg)).
  { intros L. induction L as [| N L IH]; intros t Hot Hdt Hnm Hsub.
    - exists t. split_and!; [exact Hot | exact Hdt |]. intros N c Hc.
      split; [exact (Hnm N c Hc) | exact (Hsub N c Hc (not_elem_of_nil N))].
    - destruct (t !! N) as [b0 |] eqn:HtN.
      + destruct (u_canon_name seg t N b0 Hot HtN Hdt) as (P & HPb & HPs & HdP).
        apply (IH (<[N := P]> t)).
        * intros M c Hc. destruct (decide (M = N)) as [-> | HMN].
          { rewrite lookup_insert in Hc. injection Hc as <-.
            destruct (Hot N b0 HtN) as [Hu Hb0].
            split; [exact Hu | exact (fcont_ok_prefix P b0 HPb Hb0)]. }
          rewrite lookup_insert_ne in Hc; [| congruence]. exact (Hot M c Hc).
        * exact HdP.
        * intros M c Hc. destruct (decide (M = N)) as [-> | HMN]; [exact (Hnm N b0 HtN) |].
          rewrite lookup_insert_ne in Hc; [| congruence]. exact (Hnm M c Hc).
        * intros M c Hc HM. destruct (decide (M = N)) as [-> | HMN].
          { rewrite lookup_insert in Hc. injection Hc as <-. exact HPs. }
          rewrite lookup_insert_ne in Hc; [| congruence].
          apply (Hsub M c Hc). intros Hin. apply elem_of_cons in Hin as [Hin | Hin];
            [exact (HMN Hin) | exact (HM Hin)].
      + apply (IH t Hot Hdt Hnm). intros M c Hc HM. apply (Hsub M c Hc).
        intros Hin. apply elem_of_cons in Hin as [Hin | Hin]; [| exact (HM Hin)].
        subst M. rewrite HtN in Hc. discriminate Hc. }
  assert (Hsub1 : forall N c, s1 !! N = Some c -> N ∉ (map_to_list s1).*1 ->
                    c ∈ ud_sublists (obs_wire Uart0 seg)).
  { intros N c Hc HN. exfalso. apply HN. apply elem_of_list_fmap. exists (N, c).
    split; [reflexivity | by apply elem_of_map_to_list]. }
  destruct (Hcanon _ s1 Hok1 Hd1 (fun N c Hc => proj2 (H1 N c Hc)) Hsub1)
    as (s' & Hok' & Hd' & Hs').
  exists s'. split_and!; [| exact Hok' | exact Hd'].
  apply prod_maps_complete; [apply NoDup_remove_dups | exact Hs'].
Qed.

(* ===================================================================== *)
(*  8.  THE PIECES, DECIDED                                               *)
(* ===================================================================== *)

Local Instance u_ok_dec s l a : Decision (lm_ok U s l a) := uok_dec adm s l a.
Local Instance u_merge_dec l u : Decision (lm_merge U l u) := umerge_dec adm gp gpat Hadm l u.

Local Instance u_input_dec (I : list (bv 8)) : Decision (lm_disc_input U I).
Proof using. rewrite /lm_disc_input. cbn [ulm lm_body_ok lm_body_byte]. apply _. Qed.

Local Instance u_alts_dec s I cs : Decision (lm_alts_ok U s I cs).
Proof using.
  destruct (decide (length cs = nlines I
                    /\ Forall (fun i => lm_ok U (lm_upto U cs s (bodies_of I) i)
                                           (lm_of U (bodies_of I !!! i)) (lm_at U cs i))
                              (seq 0 (nlines I)))) as [[H1 H2] | H].
  - left. split; [exact H1 |]. intros i Hi. rewrite Forall_forall in H2.
    apply H2, elem_of_seq. lia.
  - right. intros [H1 H2]. apply H. split; [exact H1 |]. apply Forall_forall.
    intros i Hi. apply elem_of_seq in Hi. apply H2. lia.
Qed.

Local Instance u_termex_dec s l : Decision (exists c, lm_ok U s l c /\ lm_term U c = true).
Proof using.
  destruct (decide (uterm_line adm l)) as [H | H].
  - left. exact (proj2 (utermex_iff adm s l) H).
  - right. intros Hex. exact (H (proj1 (utermex_iff adm s l) Hex)).
Qed.

Local Instance u_d4_dec cs s I : Decision (lm_d4 U cs s I).
Proof using Hadm.
  destruct (decide (Forall (fun i =>
      (exists c, lm_ok U (lm_upto U cs s (bodies_of I) i) (lm_of U (bodies_of I !!! i)) c
                 /\ lm_term U c = true) ->
      lm_merge U (lm_of U (bodies_of I !!! i)) (lm_cont U (lm_upto U cs s (bodies_of I) i)
                    (lm_of U (bodies_of I !!! i)) (lm_at U cs i)) ->
      nlines I = S i /\ rest_of I = []) (seq 0 (nlines I)))) as [H | H].
  - left. intros i Hi Hex Hm. rewrite Forall_forall in H.
    apply (H i); [apply elem_of_seq; lia | exact Hex | exact Hm].
  - right. intros Hd. apply H. apply Forall_forall. intros i Hi. apply elem_of_seq in Hi.
    apply Hd. lia.
Qed.

Local Instance u_pro_ok_dec ps cs q : Decision (lm_pro_ok U ps cs q).
Proof using. rewrite /lm_pro_ok. apply _. Qed.

Local Instance u_pt_dec ps cs s p : Decision (lm_disc_pt U ps cs s p).
Proof using. rewrite /lm_disc_pt. apply _. Qed.

Definition u_phi (seg : list mobs) (s : fstate) (ps cs : list nat) : Prop :=
  lm_alts_ok U s (ins seg) cs /\ lm_d4 U cs s (ins seg)
  /\ Forall (fun p => lm_pro_ok U ps cs (nlines (ins p)) /\ lm_disc_pt U ps cs s p)
       (in_pres seg).

Local Instance u_phi_dec seg s ps cs : Decision (u_phi seg s ps cs).
Proof using Hadm. rewrite /u_phi. apply _. Qed.

Definition u_found (seg : list mobs) (s : fstate) : Prop :=
  Exists (fun cs => Exists (fun ps => u_phi seg s ps cs)
                      (pro_cands (S (lm_pro_idx U cs (nlines_max (in_pres seg)))) (length seg)))
    (ualts_dep s (bodies_of (ins seg))).

Local Instance u_found_dec seg s : Decision (u_found seg s).
Proof using Hadm. rewrite /u_found. apply _. Qed.

Definition u_rhs (seg : list mobs) : Prop :=
  lm_disc_input U (ins seg)
  /\ Exists (fun s => fstate_ok s /\ u_found seg s) (scandsU seg).

Local Instance u_rhs_dec seg : Decision (u_rhs seg).
Proof using Hadm. rewrite /u_rhs. apply _. Qed.

(* ===================================================================== *)
(*  9.  AT ONE BOOT STATE THE SEARCH IS COMPLETE                          *)
(*                                                                        *)
(*  [PipesDecE.pde_seg_iff] at a state: the choice list canonicalised    *)
(*  through [ualt_code o ualt_dec] into the dependent product, the       *)
(*  prologue onto [EchoDisc.pro_cands].                                  *)
(* ===================================================================== *)
Lemma u_seg_at seg s : lm_disc_seg' U s seg -> u_found seg s.
Proof using.
  intros [Hin (ps & cs & Halts & Hd4 & Hall)]. rewrite /u_found.
  (* the choice list canonicalised: every code through [ualt_code o
     ualt_dec], and the seccomp round's bytes to [us0] ([ucanon]) *)
  pose (cs0 := (fun c => ualt_code (ucanon (ualt_dec c))) <$> cs).
  assert (Hext : forall j, lm_at U cs0 j = ucanon (lm_at U cs j)).
  { intros j. rewrite /lm_at /cs0 !list_lookup_total_alt list_lookup_fmap.
    destruct (cs !! j) as [c |]; [exact (ualt_dec_code _) | reflexivity]. }
  assert (Hpan : forall j, lm_panic U (lm_at U cs0 j) = lm_panic U (lm_at U cs j))
    by (intros j; rewrite Hext; by destruct (lm_at U cs j)).
  assert (Hpi : forall q, lm_pro_idx U cs0 q = lm_pro_idx U cs q)
    by (intros q; apply um_pro_idx_at_ext; intros j _; exact (Hpan j)).
  assert (Hup : forall bs q, lm_upto U cs0 s bs q = lm_upto U cs s bs q).
  { intros bs q. apply um_upto_at_ext. intros j _ st l. rewrite Hext. by destruct (lm_at U cs j). }
  assert (Halts0 : lm_alts_ok U s (ins seg) cs0).
  { split; [rewrite /cs0 length_fmap; exact (proj1 Halts) |]. intros i Hi.
    rewrite Hup Hext. apply uok_ucanon. exact (proj2 Halts i Hi). }
  assert (Hprod : cs0 ∈ ualts_dep s (bodies_of (ins seg))).
  { apply (ualts_dep_intro adm adm_s); [rewrite /cs0 length_fmap; exact (proj1 Halts) |].
    intros i Hi. rewrite /cs0 list_lookup_total_fmap;
      [| rewrite (proj1 Halts); exact Hi].
    rewrite Hup.
    exact (ucands_complete adm _ _ _ (proj2 Halts i Hi)). }
  (* A SECCOMP ROUND IS NEVER CHECKED: D4 makes its line the input's last,
     typed as its last byte, so no input point holds it complete *)
  assert (Hnus : forall j u, lm_at U cs j = US u ->
                 forall p, p ∈ in_pres seg -> nlines (ins p) <= j).
  { intros j u Hu p Hp.
    assert (Hjl : j < length cs).
    { destruct (decide (j < length cs)) as [Hl | Hl]; [exact Hl | exfalso].
      rewrite /lm_at list_lookup_total_alt (lookup_ge_None_2 cs j ltac:(lia)) in Hu.
      change (lm_dec U (default inhabitant None)) with (ualt_dec 0) in Hu.
      rewrite ualt_dec_0 in Hu. discriminate Hu. }
    rewrite (proj1 Halts) in Hjl.
    pose proof (proj2 Halts j Hjl) as Hok. rewrite Hu in Hok.
    destruct (Hd4 j Hjl (ex_intro _ (US u) (conj Hok eq_refl))
                (um_secc_merge _ _ u _ Hok)) as [Hn Hr].
    pose proof (um_pres_nlines seg p Hp Hr) as Hle. lia. }
  assert (Hd40 : lm_d4 U cs0 s (ins seg)).
  { intros i Hi Hex Hm. rewrite Hup in Hex, Hm. apply (Hd4 i Hi Hex).
    revert Hm. rewrite Hext. destruct (lm_at U cs i) as [r | x | x | u] eqn:Ei;
      intros Hm; try exact Hm.
    pose proof (proj2 Halts i Hi) as Hok. rewrite Ei in Hok.
    exact (um_secc_merge _ _ u _ Hok). }
  assert (Hall0 : forall p, p ∈ in_pres seg ->
            lm_pro_ok U ps cs0 (nlines (ins p)) /\ lm_disc_pt U ps cs0 s p).
  { intros p Hp. destruct (Hall p Hp) as [[HF Hlt] Hpt].
    rewrite /lm_pro_ok /lm_disc_pt Hpi.
    rewrite (um_sess_at_ext U ps cs0 cs s (done_of (ins p))).
    - split; [split; [exact HF | exact Hlt] | exact Hpt].
    - intros j Hj. rewrite nlines_done in Hj. rewrite Hext.
      destruct (lm_at U cs j) as [r | x | x | u] eqn:Ej; try reflexivity.
      exfalso. pose proof (Hnus j u Ej p Hp). lia. }
  apply Exists_exists. exists cs0. split; [exact Hprod |]. apply Exists_exists.
  destruct (decide (in_pres seg = [])) as [Hz | Hz].
  { destruct (pro_cands_nonempty (S (lm_pro_idx U cs0 (nlines_max (in_pres seg))))
                (length seg)) as [g Hg].
    exists g. split; [exact Hg |]. split; [exact Halts0 |]. split; [exact Hd40 |].
    rewrite Hz. constructor. }
  destruct (nlines_max_mem (in_pres seg) Hz) as (pl & Hplin & Hpleq).
  destruct (Hall0 pl Hplin) as [[HFps Hltl] Hptl].
  assert (Hplp : pl `prefix_of` seg)
    by exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) pl Hplin).
  destruct (pro_canon (S (lm_pro_idx U cs0 (nlines_max (in_pres seg))))
              (length seg) ps HFps) as (ps0 & Hin0 & Hrd0 & Hag0).
  { intros r Hr. rewrite -Hpleq in Hr. split; [lia |].
    etrans; [apply (pde_sess_pro_len U ps cs0 s (done_of (ins pl)) r);
             rewrite nlines_done; lia |].
    etrans; [apply prefix_length, Hptl |].
    etrans; [apply obs_wire_length |].
    exact (prefix_length _ _ Hplp). }
  exists ps0. split; [exact Hin0 |]. split; [exact Halts0 |]. split; [exact Hd40 |].
  apply Forall_forall. intros p Hp. destruct (Hall0 p Hp) as [[_ Hltp] Hptp].
  assert (Hidxle : lm_pro_idx U cs0 (nlines (ins p))
                   <= lm_pro_idx U cs0 (nlines_max (in_pres seg)))
    by (apply (lm_pro_idx_mono U), nlines_max_ge, Hp).
  assert (Hsame : lm_sess U ps0 cs0 s (done_of (ins p)) = lm_sess U ps cs0 s (done_of (ins p))).
  { apply pde_sess_ps_ext. intros r Hr. rewrite nlines_done in Hr. apply Hag0. lia. }
  split.
  - split; [eapply pro_cands_Forall; exact Hin0 | lia].
  - rewrite /lm_disc_pt Hsame. exact Hptp.
Qed.

Local Instance u_seg_dec (seg : list mobs) :
  Decision (exists s : lm_st U, lm_st_ok U s /\ lm_disc_seg' U s seg).
Proof using Hadm.
  destruct (decide (u_rhs seg)) as [H | H].
  - left. destruct H as [Hin HE]. apply Exists_exists in HE as (s & _ & Hok & HE).
    rewrite /u_found in HE. apply Exists_exists in HE as (cs & _ & HE).
    apply Exists_exists in HE as (ps & _ & Halts & Hd4 & Hall).
    exists s. split; [exact Hok |]. split; [exact Hin |]. exists ps, cs.
    split_and!; [exact Halts | exact Hd4 |].
    intros p Hp. exact (proj1 (Forall_forall _ _) Hall p Hp).
  - right. intros (s & Hok & Hd). apply H.
    destruct (u_canon_s seg s Hok Hd) as (s' & Hs' & Hok' & Hd').
    split; [exact (proj1 Hd') |]. apply Exists_exists. exists s'.
    split; [exact Hs' |]. split; [exact Hok' | exact (u_seg_at seg s' Hd')].
Qed.

(* the decider at the admission, generic *)
Lemma ud_disc_dec (h : list mobs) : Decision (lm_disc U h).
Proof using Hadm. rewrite /lm_disc. apply _. Qed.
End canon.

(* ===================================================================== *)
(*  THE DELIVERABLE                                                       *)
(*                                                                        *)
(*  OPAQUE ON PURPOSE, as [FileDiscDec.disc_f_dec] and [PipesDecE.        *)
(*  lm_disc_pipesE_dec] are: the ledger's counter is [if decide (lm_disc *)
(*  ulmG h) then 0 else 1] and every proof that touches it rewrites with *)
(*  a closure law.                                                        *)
(*                                                                        *)
(*  AT THE UNION APPLICATION's ADMISSION [adm_u_g] (grep-pipes.md cut     *)
(*  G8): every echo pipeline and every [cat f | ..], each stage [cat] or *)
(*  [grep w] of an alphanumeric word.                                     *)
(* ===================================================================== *)
(* the pattern the realisations use: [a] *)
Definition ud_gpat : bytes := [Z_to_bv 8 97].

Lemma ud_gpat_word : wl_word ud_gpat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma adm_u_g_ok : ud_adm adm_u_g true ud_gpat.
Proof using.
  split.
  - intros g fs Ha. cbn [adm_u_g] in Ha. apply andb_true_iff in Ha as [Ha _].
    exact (bool_decide_eq_true_1 _ Ha).
  - intros p fs _. apply Forall_forall. intros F _. by left.
  - intros p fs Hp Hfs.
    assert (Hc : filts_okb fs = true).
    { apply filts_okb_true. apply Forall_forall. intros F HF.
      destruct (proj1 (Forall_forall _ _) Hfs F HF) as [-> | [_ ->]];
        [exact I | exact ud_gpat_word]. }
    destruct Hp as [-> | (g & -> & Hg)]; cbn [adm_u_g]; [exact Hc |].
    rewrite bool_decide_true; [exact Hc | exact Hg].
Qed.

Global Instance lm_disc_ulmG_dec (h : list mobs) : Decision (lm_disc ulmG h).
Proof using. exact (ud_disc_dec adm_u_g adm_s_on true ud_gpat adm_u_g_ok h). Qed.

(* ...AND AT THE SECCOMP KNOB ON ([UnionDiscDec.ulmS], seccomp design
   section 3): the decider is generic in the knob -- a seccomp round is
   canonicalised to [US us0] ([u_seg_at]), and an unchecked seccomp line
   keeps D4 at its original resolution ([u_canon_name]) -- so turning the
   knob on at the application is this instance at its [adm_s] *)
Global Instance lm_disc_ulmS_dec (h : list mobs) : Decision (lm_disc ulmS h).
Proof using. exact (ud_disc_dec adm_u_g adm_s_on true ud_gpat adm_u_g_ok h). Qed.

(* the widened admission is not empty of greps: [cat a.txt | grep a | cat] *)
Lemma adm_u_g_demo : adm_u_g (LPipes (PrCatF txt_a) [FGrep ud_gpat; FCat]) = true.
Proof using. vm_compute. reflexivity. Qed.
