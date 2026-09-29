(* ===================================================================== *)
(*  UnionOut.v -- THE UNION APPLICATION'S CONSOLE CLAIM, ITS TAG AND ITS  *)
(*  LEDGER (cut C9e'; design: claude-notes/design/union.md section 3,     *)
(*  'The claim', review item S7).                                         *)
(*                                                                        *)
(*  THE CLAIM is the N-writer claim [PipeOutN.peclV] at the union model   *)
(*  [UnionDisc.ulmG]:                                                     *)
(*                                                                        *)
(*    ucl := gcl ulmG ucparams ∅ uwa ∨ popenU                          *)
(*                                                                        *)
(*  - [ucparams]: the FILE's taint, era pin and writer's witness          *)
(*    ([FileOut.file_cparams]' fields) at the union's laws and hooks;     *)
(*  - [uwa]: the FILE's witness authority ([FileOut.f0wa] / [f0boot] /    *)
(*    the filing [f0wa_file]) with the PIPELINE's byte ledger as its      *)
(*    stream extension ([gext := PipeOut.pext]);                          *)
(*  - [popenU]: [PipeOutN.popenV]'s open round at the union, CARRYING the *)
(*    witness authority [gwa uwa k (gs_st so)] -- so the file's filed     *)
(*    ledger and the claim's copy of the boot witness survive an open     *)
(*    pipeline round (the review's requirement).                          *)
(*                                                                        *)
(*  S7: the family's credential [pwc_blkU] is [PipeOutN.pwc_blkV] at the  *)
(*  union, and carries the pure tie [lm_upto cs s0 (bodies_of I) (n-1) =  *)
(*  sR]: the state the family's [runN] is built at IS the state the       *)
(*  claim's [lm_blk_at] reads.                                            *)
(*                                                                        *)
(*  THE FIXED PART is [union_gn]: the file's ([FileOut.file_gn]) and the  *)
(*  pipeline byte ledger's era map; the pipeline stack runs at            *)
(*  [ugn_pipe] = [MkPipeGn (fgn_echo gf) ugn_pera].                        *)
(*                                                                        *)
(*  THE LEDGER is [FileOut.file_led]'s shape at the union discipline,     *)
(*  plus the byte ledger's map [PipeOut.pera_map]; its taint counter      *)
(*  cases on the landed decider [UnionDecU.lm_disc_ulmG_dec] -- no        *)
(*  classical axiom -- and its conclusion is [UnionOutPure.union_phi_sync]. *)
(* ===================================================================== *)
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
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.
Require Import AppEcho.
Require Import FileState.
Require Import FileDisc.
Require Import AppFile.
Require Import FileOut.
Require Import PipeOut.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeOutN.
Require Import PipesLedPure.
Require Import GenOutWild.
Require Import PipeOutW.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionDecU.          (* [lm_disc_ulmG_dec]: the ledger's counter *)
Require Import UnionView.
Require Import UnionOutPure.
Require Import UnionAdm.           (* [ulines_of]: the ledger's full line list *)
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  0.  THE FIXED PART                                                    *)
(* ===================================================================== *)
Record union_gn := MkUnionGn {
  ugn_file : file_gn;   (* the file application's: taint, era maps, lines,
                           and the sync part's run-long names
                           ([AppFile.file_fixed], sync SY3-A3bc) *)
  ugn_pera : gname;     (* ghost_map nat pipe_era: the era's BYTE LEDGER *)
}.

(* WHAT THE UNION'S BIRTH PROMISES OF THE MACHINE'S NAMES
   ([App.app_born]): the file application's fixed part keeps the started
   counter's *)
Definition union_born (_ _ _ : gname) (γst : gname) (ug : union_gn) : Prop :=
  ff_st (fgn_cl (ugn_file ug)) = γst.

(* the pipeline stack's fixed part: the file's echo half and the byte
   ledger's map *)
Definition ugn_pipe (ug : union_gn) : pipe_gn :=
  MkPipeGn (fgn_echo (ugn_file ug)) (ugn_pera ug).

Local Notation U := ulmG.
Local Notation UB := (ulm_byte_laws adm_u_g adm_s_on).

(* THE UNION'S WILD LINES: the [seccomp x] line (seccomp design 10) --
   any nonempty tail is its terminal alternative's continuation at every
   state, and its merge set is everything *)
Definition uwild (l : uline) : bool :=
  match l with LSecc _ => true | _ => false end.

Lemma uwild_wild (l : uline) : uwild l = true -> lm_wild U l.
Proof using.
  destruct l as [ws | ws N | N | p fs | ws |]; try discriminate. intros _. split.
  - intros s u Hu. exists (ualt_code (US u)).
    cbn [ulmG ulm lm_ok lm_term lm_cont lm_dec]. rewrite ualt_dec_code.
    split_and!; [exact Hu | reflexivity | reflexivity].
  - intros u. cbn [ulmG ulm lm_merge umerge]. exact I.
Qed.

(* a pipeline line is not wild *)
Lemma uwild_pv (l : uline) (lR : pline') :
  pv_line pview_unionU l = Some lR -> uwild l = false.
Proof using.
  intros Hl. destruct (uv_line_some l lR Hl) as (p & fs & -> & _). reflexivity.
Qed.

(* the sync line is neither wild nor a pipeline (sync SY3-A4) *)
Lemma uwild_nsync (l : uline) : uwild l = true -> l <> LSync.
Proof using. by intros Hw ->. Qed.

Lemma upv_nsync (l : uline) (lR : pline') : pv_line pview_unionU l = Some lR -> l <> LSync.
Proof using.
  intros Hl. destruct (uv_line_some l lR Hl) as (p & fs & -> & _). discriminate.
Qed.

(* ---- THE ERA'S BASE, PURELY (sync SY3-A3bc): the line list of a history
        is the lines of the cycles before the current one followed by the
        current cycle's own ---- *)
Definition ulast_cyc (h : list mobs) : list uline :=
  ulines_cyc (default [] (last (cycles_of h))).

Lemma trace_shape_boots (h : list mobs) (on : bool) :
  trace_shape h on -> on = true -> obs_boots h <> 0%nat.
Proof using.
  revert on. induction h as [| e h IH] using rev_ind; intros on Hs Hon.
  - rewrite /trace_shape /= in Hs. injection Hs as <-. discriminate Hon.
  - rewrite /trace_shape foldl_app /= in Hs.
    destruct (foldl obs_step (Some false) h) as [b |] eqn:Hf;
      [| destruct e; discriminate Hs].
    rewrite obs_boots_app.
    destruct e; destruct b; cbn in Hs; try discriminate Hs.
    all: injection Hs as <-; try discriminate Hon.
    all: cbn [obs_boots]; try (specialize (IH true Hf eq_refl)); lia.
Qed.

Lemma ulast_cyc_on (h : list mobs) : ulast_cyc (h ++ [ObsPowerOn]) = [].
Proof using.
  rewrite /ulast_cyc cycles_of_on last_snoc /=. reflexivity.
Qed.

Lemma ubase_on (h : list mobs) :
  ulines_of (h ++ [ObsPowerOn]) = ulines_of h ++ ulast_cyc (h ++ [ObsPowerOn]).
Proof using.
  rewrite ulast_cyc_on app_nil_r. exact (ulines_of_power h false).
Qed.

Lemma ubase_off (h : list mobs) (B : list uline) :
  ulines_of h = B ++ ulast_cyc h ->
  ulines_of (h ++ [ObsPowerOff]) = B ++ ulast_cyc (h ++ [ObsPowerOff]).
Proof using.
  intros H. rewrite (ulines_of_power h true) /ulast_cyc cycles_of_off. exact H.
Qed.

Lemma ulast_cyc_io (h : list mobs) :
  trace_shape h true -> ulast_cyc h = ulines_cyc (open_seg h).
Proof using.
  intros Hsh. destruct (cycles_of_io h [] Hsh (Forall_nil_2 _)) as (cs & H1 & _).
  rewrite /ulast_cyc H1 last_snoc. reflexivity.
Qed.

Lemma ubase_io (h : list mobs) (e : mobs) (B : list uline) :
  trace_shape h true -> is_io e = true ->
  ulines_of h = B ++ ulast_cyc h -> ulines_of (h ++ [e]) = B ++ ulast_cyc (h ++ [e]).
Proof using.
  intros Hsh Hio H.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hc : B = concat (ulines_cyc <$> cs)).
  { rewrite /ulines_of /ulast_cyc H1 last_snoc fmap_app concat_app /= app_nil_r in H.
    exact (eq_sym (app_inv_tail _ _ _ H)). }
  rewrite /ulines_of /ulast_cyc H2 last_snoc fmap_app concat_app /= app_nil_r Hc.
  reflexivity.
Qed.

(* ---- THE ERA'S BASE IS THE EARLIER CYCLES' LINES (sync SY3-A4, the
        bridge's offset): the base the era's record pins is what
        [UnionAdm.ulast_before] adds to the open cycle's local record ---- *)
Lemma ubase_before (h : list mobs) (B : list uline) :
  trace_shape h true -> ulines_of h = B ++ ulast_cyc h ->
  B = ulines_before h (pred (length (cycles_of h))).
Proof using.
  intros Hsh H. destruct (cycles_of_io h [] Hsh (Forall_nil_2 _)) as (cs & H1 & _).
  rewrite /ulines_of /ulast_cyc H1 last_snoc fmap_app concat_app /= app_nil_r in H.
  rewrite -(app_inv_tail _ _ _ H) H1 length_app /= Nat.add_1_r /=.
  symmetry. exact (ulines_before_cut h cs _ H1).
Qed.

(* THE BRIDGE AT THE ERA ([UnionAdm.usync_bridge]): with the open cycle's
   record the sync round's local [(nlines I, c)], the model's last
   completed sync is [(length (base ++ ulines_in I), c)] -- the record the
   hook appends over sh's line lower bound [base ++ ulines_in I] *)
Lemma usync_bridge_era (h : list mobs) (os : list (option srec)) (B : list uline)
    (I : list (bv 8)) (c : fstate) :
  trace_shape h true -> ulines_of h = B ++ ulast_cyc h ->
  S (length os) = length (cycles_of h) ->
  ulast_before h (os ++ [Some (nlines I, c)]) (S (length os)) = (length (B ++ ulines_in I), c).
Proof using.
  intros Hsh HB Hl. apply usync_bridge; [lia |].
  rewrite (ubase_before h B Hsh HB) -Hl. reflexivity.
Qed.

(* ---- THE FLOOR'S TWO RECORDS, PURELY (sync SY3-A4): the last completed
        sync of the cycles so far ([UnionOutPure.union_rec_now]), and of
        the cycles before the open one -- the era's boot record ---- *)
Definition union_rec_base (h : list mobs) (W : list (fstate * option srec)) : srec :=
  ulast_before h (snd <$> W) (pred (length W)).

(* the open cycle's own segment moves no record: only its line count,
   which no later cycle reads *)
Lemma ulast_from_last (off : nat) (r : srec) (segs : list (list mobs))
    (seg seg' : list mobs) (os : list (option srec)) :
  ulast_from off r (segs ++ [seg]) os = ulast_from off r (segs ++ [seg']) os.
Proof using.
  revert off r os. induction segs as [| s0 segs IH]; intros off r os.
  - destruct os as [| o os]; [reflexivity |]. cbn [app ulast_from].
    by destruct os.
  - destruct os as [| o os]; [reflexivity |]. cbn [app ulast_from]. apply IH.
Qed.

Lemma union_rec_now_io (h : list mobs) (e : mobs) (W : list (fstate * option srec)) :
  trace_shape h true -> is_io e = true -> length W = length (cycles_of h) ->
  union_rec_now (h ++ [e]) W = union_rec_now h W.
Proof using.
  intros Hsh Hio Hl.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  rewrite /union_rec_now /ulast_before H1 H2.
  rewrite H1 length_app in Hl. cbn [length] in Hl.
  rewrite !take_ge; [| rewrite length_app /=; lia | rewrite length_app /=; lia].
  apply ulast_from_last.
Qed.

Lemma union_rec_now_off (h : list mobs) (W : list (fstate * option srec)) :
  union_rec_now (h ++ [ObsPowerOff]) W = union_rec_now h W.
Proof using. by rewrite /union_rec_now /ulast_before cycles_of_off. Qed.

Lemma union_rec_now_on (h : list mobs) (W : list (fstate * option srec)) (s : fstate) :
  length W = length (cycles_of h) ->
  union_rec_now (h ++ [ObsPowerOn]) (W ++ [(s, None)]) = union_rec_now h W.
Proof using.
  intros Hl. rewrite /union_rec_now fmap_app length_app /= Nat.add_1_r.
  rewrite -(length_fmap snd W).
  rewrite (ulast_before_snoc_none (h ++ [ObsPowerOn]) (snd <$> W));
    [| rewrite cycles_of_on length_app length_fmap /=; lia].
  apply ulast_before_ext; [| reflexivity].
  rewrite cycles_of_on take_app_le; [reflexivity | rewrite length_fmap; lia].
Qed.

Lemma union_rec_base_on (h : list mobs) (W : list (fstate * option srec)) (s : fstate) :
  length W = length (cycles_of h) ->
  union_rec_base (h ++ [ObsPowerOn]) (W ++ [(s, None)]) = union_rec_now h W.
Proof using.
  intros Hl. rewrite /union_rec_base /union_rec_now length_app /= Nat.add_1_r /=.
  apply ulast_before_ext.
  - rewrite cycles_of_on take_app_le; [reflexivity | lia].
  - rewrite fmap_app take_app_le; [reflexivity | rewrite length_fmap; lia].
Qed.

Lemma union_rec_base_off (h : list mobs) (W : list (fstate * option srec)) :
  union_rec_base (h ++ [ObsPowerOff]) W = union_rec_base h W.
Proof using. by rewrite /union_rec_base /ulast_before cycles_of_off. Qed.

(* a console event, the open cycle's entry replaced (or kept) *)
Lemma union_rec_base_io (h : list mobs) (e : mobs) (u1 : list (fstate * option srec))
    (x y : fstate * option srec) :
  trace_shape h true -> is_io e = true -> S (length u1) = length (cycles_of h) ->
  union_rec_base (h ++ [e]) (u1 ++ [x]) = union_rec_base h (u1 ++ [y]).
Proof using.
  intros Hsh Hio Hl.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1) by (rewrite H1 length_app /= in Hl; lia).
  rewrite /union_rec_base !length_app /= Nat.add_1_r /=.
  apply ulast_before_ext.
  - exact (take_cycles_io h e cs (length u1) H1 H2 ltac:(lia)).
  - rewrite (take_snd_snoc u1 x (length u1)); [| lia].
    rewrite (take_snd_snoc u1 y (length u1)); [reflexivity | lia].
Qed.

Lemma union_W_snoc (h : list mobs) (W : list (fstate * option srec)) :
  trace_shape h true -> length W = length (cycles_of h) ->
  exists u1 y, W = u1 ++ [y] /\ S (length u1) = length (cycles_of h).
Proof using.
  intros Hsh Hl.
  destruct (cycles_of_io h [] Hsh (Forall_nil_2 _)) as (cs & H1 & _).
  assert (Hne : W <> []) by (intros ->; rewrite H1 length_app /= in Hl; lia).
  destruct (exists_last Hne) as (u1 & y & ->). exists u1, y. split; [reflexivity |].
  rewrite length_app /= in Hl. lia.
Qed.

Lemma cycles_len_io (h : list mobs) (e : mobs) :
  trace_shape h true -> is_io e = true ->
  length (cycles_of (h ++ [e])) = length (cycles_of h).
Proof using.
  intros Hsh Hio.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  by rewrite H1 H2 !length_app.
Qed.

Lemma union_rec_base_io' (h : list mobs) (e : mobs) (W : list (fstate * option srec)) :
  trace_shape h true -> is_io e = true -> length W = length (cycles_of h) ->
  union_rec_base (h ++ [e]) W = union_rec_base h W.
Proof using.
  intros Hsh Hio Hl. destruct (union_W_snoc h W Hsh Hl) as (u1 & y & -> & Hl1).
  exact (union_rec_base_io h e u1 y y Hsh Hio Hl1).
Qed.

(* THE DRAIN'S NEW RECORD: with no completed sync in the open cycle, the
   era's boot record; with the round's, the bridge's *)
Lemma union_rec_now_drain_none (h : list mobs) (e : mobs) (u1 : list (fstate * option srec))
    (y : fstate * option srec) (s : fstate) :
  trace_shape h true -> is_io e = true -> S (length u1) = length (cycles_of h) ->
  union_rec_now (h ++ [e]) (u1 ++ [(s, None)]) = union_rec_base h (u1 ++ [y]).
Proof using.
  intros Hsh Hio Hl.
  destruct (cycles_of_io h [e] Hsh (proj2 (Forall_singleton _ _) Hio)) as (cs & H1 & H2).
  assert (Hcs : length cs = length u1) by (rewrite H1 length_app /= in Hl; lia).
  rewrite /union_rec_now /union_rec_base !length_app /= Nat.add_1_r /= fmap_app.
  rewrite -(length_fmap snd u1).
  rewrite (ulast_before_snoc_none (h ++ [e]) (snd <$> u1));
    [| rewrite H2 length_app length_fmap /=; lia].
  rewrite length_fmap.
  apply ulast_before_ext.
  - exact (take_cycles_io h e cs (length u1) H1 H2 ltac:(lia)).
  - symmetry. apply take_snd_snoc. lia.
Qed.

Lemma union_rec_now_drain_some (h : list mobs) (u1 : list (fstate * option srec))
    (s : fstate) (B : list uline) (I : list (bv 8)) (c : fstate) :
  trace_shape h true -> ulines_of h = B ++ ulast_cyc h ->
  S (length u1) = length (cycles_of h) ->
  union_rec_now h (u1 ++ [(s, Some (nlines I, c))]) = (length (B ++ ulines_in I), c).
Proof using.
  intros Hsh HB Hl. rewrite /union_rec_now length_app /= Nat.add_1_r fmap_app.
  rewrite -(length_fmap snd u1).
  apply (usync_bridge_era h (snd <$> u1) B I c Hsh HB). by rewrite length_fmap.
Qed.

Section union_out.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation pg := (ugn_pipe ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).

  (* =================================================================== *)
  (*  1.  THE PARAMETERS AND THE CLAIM                                    *)
  (* =================================================================== *)

  (* the file's taint, pin and writer's witness, at the union's model *)
  Definition ucparams : gen_cparams U :=
    MkGCP U ulmG_laws ulmG_hooks UT _ _
      UPIN _ _ (era_pin_agree (fgn_echo gf)) (f0cw gf) _ _.

  (* THE ROUND'S PAYLOAD (sync SY3-A4, [GenOut.gpr]): nothing, except when
     the alternative filed is /sync's run at a [sync] line, where it is the
     completed sync's RECORD -- the choices before the round, the era's
     boot state and record, and a lower bound of the RUN-LONG sync history
     ending at [(position of the line + 1, the state before the round)] *)
  Definition upr (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat) : iProp Σ :=
    (⌜¬ (lm_line_at U I = LSync /\ ualt_dec a = UR RSyncRan)⌝ ∨ UT
     ∨ ∃ (cs : list nat) (s0 : fstate) (vf : file_era) (L : list srec),
         cs_lb v cs ∗ ⌜length cs = (nlines I - 1)%nat⌝ ∗ f0cw gf k s0
         ∗ file_era_pin gf k vf
         ∗ sl_lb (ff_hist (fgn_cl gf))
             (L ++ [(length (fe_base vf ++ ulines_in I),
                     lm_upto U cs s0 (bodies_of I) (nlines I - 1))]))%I.

  Global Instance upr_persistent k v I a : Persistent (upr k v I a).
  Proof using . rewrite /upr /file_taint /echo_taint. apply _. Qed.
  Global Instance upr_timeless k v I a : Timeless (upr k v I a).
  Proof using . rewrite /upr /file_taint /echo_taint. apply _. Qed.

  (* ...free at every other alternative *)
  Lemma upr_free (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat) :
    ualt_dec a <> UR RSyncRan -> ⊢ upr k v I a.
  Proof using . intros Ha. iLeft. iPureIntro. intros [_ H]. exact (Ha H). Qed.

  Lemma upr_free_line (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat) :
    lm_line_at U I <> LSync -> ⊢ upr k v I a.
  Proof using . intros Hl. iLeft. iPureIntro. intros [H _]. exact (Hl H). Qed.

  Lemma upr_0 (k : nat) (v : era_pins) (I : list (bv 8)) : ⊢ upr k v I 0.
  Proof using . apply upr_free. intros H. vm_compute in H. discriminate H. Qed.

  Lemma upr_pan (k : nat) (v : era_pins) (I : list (bv 8)) :
    ⊢ upr k v I (lmh_pan ulmG_hooks (lm_line_at U I)).
  Proof using .
    destruct (decide (lm_line_at U I = LSync)) as [Hl | Hl]; [| by apply upr_free_line].
    rewrite Hl. apply upr_free. intros H. vm_compute in H. discriminate H.
  Qed.

  Lemma upr_exf (k : nat) (v : era_pins) (I : list (bv 8)) :
    ⊢ upr k v I (lmh_exf ulmG_hooks (lm_line_at U I)).
  Proof using .
    destruct (decide (lm_line_at U I = LSync)) as [Hl | Hl]; [| by apply upr_free_line].
    rewrite Hl. apply upr_free. intros H. vm_compute in H. discriminate H.
  Qed.

  (* ...and it is free at the wild line and at a pipeline's *)
  Lemma upr_wild (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat) :
    uwild (lm_line_at U I) = true -> ⊢ upr k v I a.
  Proof using . intros Hw. apply upr_free_line. exact (uwild_nsync _ Hw). Qed.

  Lemma upr_pv (k : nat) (v : era_pins) (I : list (bv 8)) (lR : pline') (a : nat) :
    pv_line pview_unionU (lineV U I) = Some lR -> ⊢ upr k v I a.
  Proof using . intros Hl. apply upr_free_line. exact (upv_nsync _ _ Hl). Qed.

  (* the file's witness authority, the pipeline's byte ledger beside it *)
  Definition uwa : gen_wa U ucparams ∅ :=
    @MkGWA Σ _ U ucparams ∅ (f0wa gf) _ (f0wa_agree_d gf) (f0_typed gf) _
      (f0wa_W gf) (f0boot gf) (f0wa_file gf) True (fun _ => f0wa_agree gf)
      False (fun Hf => match Hf with end)
      (pext pg) _ (pext_grow pg)
      upr _ _.

  Lemma uwa_ext k l : gext uwa k l = pext pg k l.
  Proof using . reflexivity. Qed.

  (* THE OPEN ROUND: [popenV] at the union, carrying the witness
     authority [f0wa] of the stage's filed state *)
  Definition popenU (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    popenV pg U UPIN (f0wa gf) ∅ upr k ho H.

  (* THE CLAIM: three arms (seccomp design 10.3) -- the taint, the
     disciplined claim under the era's wild flag at 0, and the WILD arm *)
  Definition ucl : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ :=
    pwclV pg U ucparams ∅ uwa uwild.

  (* THE ERA'S WILD TOKEN (seccomp design 10.1) *)
  Definition usecc_tok (k : nat) : iProp Σ := secc_tok U ucparams k.

  Global Instance usecc_tok_persistent k : Persistent (usecc_tok k).
  Proof using . rewrite /usecc_tok. apply _. Qed.
  Global Instance usecc_tok_timeless k : Timeless (usecc_tok k).
  Proof using . rewrite /usecc_tok. apply _. Qed.

  (* ...at its own line *)
  Definition usecc_tok_at (k : nat) (I0 : list (bv 8)) : iProp Σ :=
    secc_tok_at U ucparams k I0.
  Global Instance usecc_tok_at_persistent k I0 : Persistent (usecc_tok_at k I0).
  Proof using . rewrite /usecc_tok_at. apply _. Qed.
  Global Instance usecc_tok_at_timeless k I0 : Timeless (usecc_tok_at k I0).
  Proof using . rewrite /usecc_tok_at. apply _. Qed.
  (* THE UNION'S READER-SIDE WILD CREDENTIAL ([AppUnionRec.union_ifc]'s
     [ai_rdwild]; seccomp design 10.12, lane S5b): the era's token at the
     [seccomp x] line it was minted at, and the reader's position at that
     line -- a lower bound every later reader's position, of whichever
     shell, is above *)
  Definition urdwild (k : nat) : iProp Σ :=
    (∃ (I0 : list (bv 8)) (v : era_pins),
       usecc_tok_at k I0 ∗ ⌜uwild (lm_line_at U I0) = true⌝
       ∗ UPIN k v ∗ rpos_lb v (length I0))%I.

  Global Instance urdwild_persistent k : Persistent (urdwild k).
  Proof using . rewrite /urdwild. apply _. Qed.
  Global Instance urdwild_timeless k : Timeless (urdwild k).
  Proof using . rewrite /urdwild. apply _. Qed.

  Lemma usecc_tok_of_at (k : nat) (I0 : list (bv 8)) : usecc_tok_at k I0 -∗ usecc_tok k.
  Proof using . exact (secc_tok_of_at U ucparams k I0). Qed.

  Lemma ucl_unfold (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ucl k ho H ⊣⊢ UT ∨ (∃ v, UPIN k v ∗ secc_flag v 0 ∗ peclV pg U ucparams ∅ uwa k ho H)
                  ∨ wildV U ucparams ∅ uwa uwild k ho H.
  Proof using . done. Qed.

  Global Instance ucl_timeless k ho H : Timeless (ucl k ho H).
  Proof using . rewrite /ucl. apply _. Qed.

  Lemma ucl_taint (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    UT -∗ ucl k ho H.
  Proof using . iIntros "#HT". iApply (pwclV_taint pg U ucparams ∅ uwa uwild k ho H with "HT"). Qed.

  (* THE LICENCES: the taint moves the claim by any event, the wild token
     by any process event *)
  Lemma ucl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    UT -∗ ucl k ho H ==∗ ucl k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT Hc". iApply (pwclV_sup pg U ucparams ∅ uwa uwild k ho H ev with "HT Hc"). Qed.

  Lemma ucl_wild_lic (k : nat) :
    usecc_tok k -∗
    □ ∀ (h : list mobs) (H : LogEntryDefs.cons_hist) (ev : ConsLog.cons_ev),
        ⌜(exists b, ev = ConsLog.EvOut b) \/ (exists ws, ev = ConsLog.EvRead ws)⌝ -∗
        ⌜ConsLog.cons_ev_ok H ev⌝ -∗
        ucl k h H ==∗ ucl k h (ConsLog.cons_step H ev).
  Proof using . exact (pwclV_wild_lic pg U ucparams UB ∅ uwa uwild k). Qed.

  (* =================================================================== *)
  (*  2.  THE FILE LINES' EVENTS: the generic claim's, the open round     *)
  (*      refuted                                                         *)
  (* =================================================================== *)

  (* (H) THE ERA'S HEAD WRITE, filing the boot state out of [f0boot] *)
  Lemma ucl_step_write_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : fstate) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    fstate_ok s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (f0boot gf k s0 ∨ UT) -∗
    ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hok Halt Hhead. iIntros "Hpin Ht Hps Hcs HE Hbt Hcl".
    iApply (pwclV_step_write_first pg U ucparams ∅ uwa uwild uwild_wild
              k v a b s0 ho H Hok Halt Hhead with "Hpin Ht Hps Hcs HE Hbt Hcl").
  Qed.

  (* (W) A BYTE INSIDE A BLOCK OR A PROLOGUE ROUND *)
  Lemma ucl_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    lm_proc_stream U ps0 cs0 s0 I0 !! P = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0cw gf k s0 -∗
    ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hn Hpin0 Hb. iIntros "Hpin Ht Hps Hcs HE HW Hcl".
    iApply (pwclV_step_write pg U ucparams ∅ uwa uwild uwild_wild
              k v P b ps0 cs0 s0 I0 ho H Hn Hpin0 Hb with "Hpin Ht Hps Hcs HE HW Hcl").
  Qed.

  (* (B) A BLOCK'S FIRST BYTE, filing the round's alternative, at a line
     that is not a [seccomp x] line (premise; seccomp design 10.10: no
     escape -- the shell's round there never presents a block-first byte) *)
  Lemma ucl_step_write_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    uwild (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) = false ->
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    P = length (lm_proc_before U ps0 cs0 s0 I0) ->
    lm_ok U (lm_upto U cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec U a) ->
    lm_term U (lm_dec U a) = false ->
    lm_cont U (lm_upto U cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec U a) !! 0%nat = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0cw gf k s0 -∗
    (* ...and the round's payload (sync SY3-A4) *)
    upr k v I0 a -∗
    ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
          ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hnw Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead.
    iIntros "Hpin Ht Hps Hcs HE HW HR Hcl".
    iApply (pwclV_step_write_blk pg U ucparams UB ∅ uwa uwild uwild_wild
              k v P a b ps0 cs0 s0 I0 ho H
              Hnw Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead
              with "Hpin Ht Hps Hcs HE HW HR Hcl").
  Qed.

  (* (P) A PROLOGUE ROUND'S CHOICE BYTE: the file's witness is STRICT (a
     filed lower bound pins the state), so no cursor premise *)
  Lemma ucl_step_write_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) :
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic U (lm_at U cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx U cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream U ps0 cs0 s0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0cw gf k s0 -∗
    ucl k ho CH ==∗
      ucl k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
          ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "Hpin Ht Hps Hcs HE HW Hcl".
    iApply (pwclV_step_write_pro pg U ucparams ∅ uwa uwild uwild_wild
              k v P a b ps0 cs0 s0 I0 ho CH
              (or_intror (or_introl I)) Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
              with "Hpin Ht Hps Hcs HE HW Hcl").
  Qed.

  (* THE DRAIN: the trace fact at the era's own boot state, that state's
     deed witness ([gwa_ty uwa = f0_typed]), the era pin and a lower bound
     of the state -- [FileOut.fdrain_ret] at the union model, from either
     arm of the claim *)
  Definition udrain_ret (k : nat) (seg : list mobs) : iProp Σ :=
    (UT
     ∨ ∃ (s0 : fstate) (vf : file_era) (o : option srec),
         ⌜lm_good_sync s0 seg o⌝ ∗ ⌜fstate_ok s0⌝ ∗ f0_typed gf s0
         ∗ file_era_pin gf k vf ∗ f0_lb gf vf s0
         (* ...AND THE CYCLE'S LAST COMPLETED SYNC (sync SY3-A4): none, or the
            round's record -- its position over the era's base and the state
            before it -- the last entry of a lower bound of the run-long
            history, read off the payload the round filed *)
         ∗ (⌜o = None⌝
            ∨ ∃ (J : list (bv 8)) (c : fstate) (L : list srec),
                ⌜o = Some (nlines J, c)⌝
                ∗ sl_lb (ff_hist (fgn_cl gf))
                    (L ++ [(length (fe_base vf ++ ulines_in J), c)])))%I.

  Lemma ucl_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    ucl k ho CH -∗ ucl k ho CH ∗ udrain_ret k seg.
  Proof using .
    intros Hsh Hk Hpre Hins Hwire Hne. iIntros "Hcl".
    iDestruct (pwclV_drain pg U ucparams UB ∅ uwa uwild uwild_wild upr_wild k h ho CH seg
                 Hsh Hk Hpre Hins Hwire Hne with "Hcl") as "[$ Hd]".
    rewrite /udrain_ret /gdrain_ret.
    iDestruct "Hd" as "[#HT | (%s0 & %csf & %ex & %v & %Is & %Hg & %Hok & #Hty & #Hw
                             & #Hpin & #Hcsf & %HIs & #Hitems)]"; [by iLeft |].
    iDestruct "Hw" as (vf) "[#Hfp #Hlb]".
    destruct Hg as (ps & Hpro & Halts & Hwr).
    set (csr := lm_alts_pad U ulmG_hooks (ins seg) (csf ++ ex)).
    assert (Hgs : lm_good_sync s0 seg
                    (usync_last ps csr s0 (ins seg) (obs_wire Uart0 seg))).
    { exists ps, csr. split_and!; [exact Hpro | exact Halts | exact Hwr | reflexivity]. }
    destruct (usync_last ps csr s0 (ins seg) (obs_wire Uart0 seg)) as [r |] eqn:Ho;
      last first.
    { iRight. iExists s0, vf, None. iFrame "Hty Hfp Hlb".
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. by iLeft. }
    destruct (usync_last_pad ps (csf ++ ex) s0 (ins seg) (obs_wire Uart0 seg) r Ho)
      as (i & Hi & Hin & Hat).
    destruct HIs as (Hex & HlIs & HFI).
    destruct (lookup_lt_is_Some_2 Is i ltac:(lia)) as [J HJ].
    iDestruct (big_sepL_lookup with "Hitems") as "(Hpr & _ & %HnJ)"; [exact HJ |].
    pose proof (Forall_lookup_1 _ _ _ _ HFI HJ) as HJp.
    rewrite /usync_at in Hat. case_decide as Hd; [| discriminate].
    injection Hat as <-. destruct Hd as (HlS & HaR & _).
    assert (Hcsi : forall j, j < length (csf ++ ex) -> csr !!! j = (csf ++ ex) !!! j).
    { intros j Hj. apply cs_prefix_total; [apply lm_alts_pad_prefix | exact Hj]. }
    assert (Hbod : forall j, j < S i -> bodies_of (ins seg) !!! j = bodies_of J !!! j).
    { destruct HJp as [z Hz]. rewrite Hz. destruct (bodies_of_app J z) as [y Hy].
      intros j Hj. rewrite Hy !list_lookup_total_alt lookup_app_l; [reflexivity |].
      unfold nlines in HnJ. lia. }
    iDestruct "Hpr" as "[%Hnot | [#HT | (%cs' & %s0' & %vf' & %L & #Hcs' & %Hlcs & #Hcw
                                        & #Hfp' & #Hsl)]]".
    { exfalso. apply Hnot. split.
      - rewrite /lm_line_at HnJ (_ : (S i - 1)%nat = i); [| lia].
        rewrite -(Hbod i ltac:(lia)). exact HlS.
      - rewrite -(Hcsi i Hi). exact HaR. }
    { by iLeft. }
    iDestruct (file_era_pin_agree with "Hfp Hfp'") as %<-.
    iDestruct "Hcw" as (vf'') "[#Hfp'' #Hlb'']".
    iDestruct (file_era_pin_agree with "Hfp Hfp''") as %<-.
    iDestruct (f0_lb_agree with "Hlb Hlb''") as %<-.
    iDestruct (cs_lb_cmp v csf cs' with "Hcsf Hcs'") as %Hcmp.
    assert (Hcs'e : cs' = take i (csf ++ ex)).
    { rewrite HnJ in Hlcs. cbn in Hlcs. rewrite Nat.sub_0_r in Hlcs.
      rewrite length_app in Hi.
      destruct Hcmp as [Hp | Hp].
      - pose proof (prefix_length _ _ Hp) as Hl.
        assert (Hc : cs' = csf) by (symmetry; apply (prefix_length_eq csf cs' Hp); lia).
        subst cs'. rewrite take_app_le; [| lia].
        rewrite take_ge; [reflexivity | lia].
      - destruct Hp as [z ->]. rewrite length_app in Hi.
        rewrite -app_assoc (take_app_le cs' (z ++ ex) i); [| lia].
        rewrite take_ge; [reflexivity | lia]. }
    assert (Hup : lm_upto U csr s0 (bodies_of (ins seg)) i
                  = lm_upto U cs' s0 (bodies_of J) (nlines J - 1)).
    { rewrite HnJ (_ : (S i - 1)%nat = i); [| lia].
      rewrite (lm_upto_bs_ext U csr s0 (bodies_of (ins seg)) (bodies_of J) i
                 ltac:(intros j Hj; apply Hbod; lia)).
      apply lm_upto_cs_ext. intros j Hj. rewrite Hcsi; [| lia].
      rewrite Hcs'e !list_lookup_total_alt lookup_take_lt; [reflexivity | exact Hj]. }
    iRight. iExists s0, vf, (Some (S i, lm_upto U csr s0 (bodies_of (ins seg)) i)).
    iFrame "Hty Hfp Hlb". iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iRight. iExists J, (lm_upto U csr s0 (bodies_of (ins seg)) i), L.
    iSplitR; [iPureIntro; by rewrite HnJ |].
    rewrite Hup. iExact "Hsl".
  Qed.

  (* THE READ: the generic receipt, and at a read that completes a wild
     line the era's wild token (the transition, seccomp design 10.4) *)
  Lemma ucl_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    UPIN k v -∗ dl_cnt v (1/2) n -∗ ucl k ho CH ==∗
      ucl k ho (ConsLog.cons_step CH (ConsLog.EvRead ws))
      ∗ rd_retW U ucparams uwild k v n CH ws.
  Proof using .
    intros Hread. iIntros "Hpin Hdl Hcl".
    iApply (pwclV_step_read pg U ucparams UB ∅ uwa uwild uwild_wild k v n ho CH ws Hread
              with "Hpin Hdl Hcl").
  Qed.

  (* THE KERNEL'S OWN EVENTS *)
  Lemma ucl_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    ucl k ho H -∗ ucl k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using . intros Hok Hev. exact (pwclV_close pg U ucparams ∅ uwa uwild k ho H Hok Hev). Qed.

  Lemma ucl_step_byte (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    ucl k ho CH ==∗ ucl k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using .
    intros Hok Hev. exact (pwclV_step_byte pg U ucparams UB ∅ uwa uwild k ho CH b Hok Hev).
  Qed.

  Lemma ucl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input U (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc U h -> trace_shape h true ->
    ucl k ho H -∗ ucl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh.
    exact (pwclV_open pg U ucparams UB ∅ uwa uwild uwild_wild k ho H h c cs
             Hok Hev Hd Hb Hdh Hsh).
  Qed.

  (* =================================================================== *)
  (*  3.  THE PIPELINE ROUNDS' EVENTS (C9c'), at the union                *)
  (* =================================================================== *)

  (* THE FAMILY'S CREDENTIAL at the round's state [sR] (S7: it carries
     the tie [lm_upto cs s0 (bodies_of I) (nlines I - 1) = sR]) *)
  Definition pwc_blkU (v : era_pins) (I : list (bv 8)) (sR : fstate) (k : nat)
      (pre : list (bv 8)) (tm : bool) : iProp Σ :=
    pwc_blkV pg U UPIN (f0cw gf) UT v I sR k pre tm.

  Definition ptkU (v : era_pins) (I : list (bv 8)) (k : nat) : iProp Σ :=
    ptkV UT v I k.

  Definition pwitU (I : list (bv 8)) (sR : fstate) (tm : bool) (pre : list (bv 8)) : Prop :=
    pwitV U I sR tm pre.

  Global Instance pwc_blkU_timeless v I sR k pre tm : Timeless (pwc_blkU v I sR k pre tm).
  Proof using . rewrite /pwc_blkU. apply pwc_blkV_timeless; apply _. Qed.

  Global Instance ptkU_persistent v I k : Persistent (ptkU v I k).
  Proof using . rewrite /ptkU /ptkV. apply _. Qed.

  (* the tie, read off the credential *)
  Lemma pwc_blkU_tie (v : era_pins) (I : list (bv 8)) (sR : fstate) (k : nat)
      (pre : list (bv 8)) (tm : bool) :
    pwc_blkU v I sR k pre tm -∗
    (∃ (ps cs : list nat) (s0 : fstate) (P : nat),
       ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
       ∗ f0cw gf k s0) ∨ UT.
  Proof using .
    rewrite /pwc_blkU /pwc_blkV. iIntros "[Hx | #HT]"; [| by iRight].
    iDestruct "Hx" as (ps cs s0 P) "(%Hw & _ & #HW & _)".
    iLeft. iExists ps, cs, s0, P. by iFrame "HW".
  Qed.

  (* THE ENTRY: a round writer's lend before the block's first byte *)
  Lemma pwc_blkU_entry (v : era_pins) (I : list (bv 8)) (k : nat)
      (ps cs : list nat) (s0 : fstate) (P : nat) :
    wr_blkV U ps cs s0 I P ->
    UPIN k v -∗ f0cw gf k s0 -∗ turn v P -∗ ps_lb v ps -∗ cs_lb v cs -∗ inp_lb v I -∗
    pwc_blkU v I (lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat) k [] false.
  Proof using .
    intros Hw. iIntros "Hpin HW Ht Hps Hcs HE".
    iApply (pwc_blkV_entry pg U UPIN (f0cw gf) UT v I k ps cs s0 P Hw
              with "Hpin HW Ht Hps Hcs HE").
  Qed.

  (* THE CLAIM PAYS THE FAMILY'S ONE OBLIGATION, at the round's state, at
     a line that is NOT WILD (a terminal family byte at the [seccomp x]
     line would be admissible there; the family's lines are pipelines) *)
  Theorem pblkU_ecl_holds (v : era_pins) (I : list (bv 8)) (sR : fstate) (lR : pline') :
    pv_line pview_unionU (lineV U I) = Some lR ->
    ⊢ eclN ucl (pwc_blkU v I sR) (ptkU v I) (pwitU I sR).
  Proof using .
    intros HlR. exact (pwclV_ecl_holds pg U ucparams ∅ uwa uwa_ext uwild uwild_wild
                         v I sR (uwild_pv _ _ HlR) (fun k a => upr_pv k v I lR a HlR)).
  Qed.

  (* THE MODEL'S BLOCKS ARE THE CLAIM'S NON-TERMINAL WITNESS, through the
     union's view, at a well-formed round state *)
  Lemma pipesU_HWIT (I : list (bv 8)) (sR : fstate) (lR : pline') :
    pv_line pview_unionU (lineV U I) = Some lR -> fstate_ok sR ->
    adm_u_g lR = true -> pl_ok lR ->
    forall pre bl, blkN (wids (lcats lR)) (runN (files_of sR) lR) bl ->
      pre `prefix_of` bl -> pwitU I sR false pre.
  Proof using .
    intros HlR Hok Ha Hl.
    exact (pipesV_HWIT U pview_unionU I sR lR HlR
             (pview_union_fc_ok adm_u_g adm_s_on sR Hok) Ha Hl).
  Qed.

  (* THE FILING at the credential: the prompt's first byte files the
     block the family handed back, as the view's [PLRun pre] *)
  Lemma pwc_blkU_file (v : era_pins) (I : list (bv 8)) (sR : fstate) (lR : pline')
      (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (pre : list (bv 8)) (b : bv 8) :
    pv_line pview_unionU (lineV U I) = Some lR -> adm_u_g lR = true ->
    line_blocks (files_of sR) lR pre -> pre <> [] -> b = u_prompt !!! 0%nat ->
    pwc_blkU v I sR k pre false -∗ ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
            ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
            ∗ f0cw gf k s0 ∗ turn v (S (P + length pre))%nat
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc pview_unionU lR (PLRun pre)]) ∗ inp_lb v I) ∨ UT).
  Proof using .
    intros HlR Ha Hbl Hne Hbv. iIntros "Hpw Hcl".
    iApply (pwclV_blk_file pg U ucparams UB ∅ uwa uwa_ext uwild pview_unionU v I sR lR
              k ho H pre b HlR Ha Hbl Hne Hbv with "Hpw Hcl").
  Qed.

  (* ...and the EMPTY block: no writer wrote, the prompt is the block's
     first byte, filed between rounds as the view's [PLRun []] *)
  Lemma pwc_blkU_file_empty (v : era_pins) (I : list (bv 8)) (sR : fstate) (lR : pline')
      (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) (b : bv 8) :
    pv_line pview_unionU (lineV U I) = Some lR ->
    b = u_prompt !!! 0%nat ->
    pwc_blkU v I sR k [] false -∗ ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
            ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
            ∗ f0cw gf k s0 ∗ turn v (S P)
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc pview_unionU lR (PLRun [])]) ∗ inp_lb v I) ∨ UT).
  Proof using .
    intros HlR Hbv. iIntros "Hpw Hcl".
    iApply (pwclV_blk_file_empty pg U ucparams UB ∅ uwa uwild uwild_wild pview_unionU
              v I sR lR k ho H b uwild_pv HlR Hbv (fun k a => upr_pv k v I lR a HlR)
              with "Hpw Hcl").
  Qed.

  (* =================================================================== *)
  (*  4.  THE TAG                                                         *)
  (* =================================================================== *)

  (* [FileOut.ftag] at the union's discipline: the trace's shape, the
     discipline or the taint, and a lower bound of the ledger's line list
     (EVERY complete line, [UnionAdm.ulines_of]; its redirect lines are
     the projection, [UnionAdm.ulines_of_echof]) -- which is how a typed
     line reaches the child's create step *)
  Definition utag (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜lm_disc U h⌝ ∨ UT)
     ∗ fl_lb (fgn_cl gf) (ulines_of h)
     (* ...AND THE ERA'S BASE (sync SY3-A3bc): the list is the era's pinned
        base followed by the cycle's own lines *)
     ∗ ∃ vf : file_era, file_era_pin gf (obs_boots h) vf
         ∗ ⌜ulines_of h = fe_base vf ++ ulast_cyc h⌝)%I.

  Global Instance utag_persistent h : Persistent (utag h).
  Proof using . rewrite /utag. apply _. Qed.
  Global Instance utag_timeless h : Timeless (utag h).
  Proof using . rewrite /utag. apply _. Qed.

  (* =================================================================== *)
  (*  5.  THE FOUNDING: the era's ghosts become the claim at the start of *)
  (*      its era and init's credential                                   *)
  (* =================================================================== *)
  Lemma union_era_split (k : nat) (v : era_pins) (vf : file_era) (w : pipe_era)
      (gb : gname) :
    UPIN k v -∗ file_era_pin gf k vf -∗ pera_pin pg k w -∗
    era_full v -∗ f0_auth vf [] -∗ f0f_auth vf [] -∗
    blk_auth w [] -∗ rblk_auth gb [] -∗ cur_half w 1 0%nat gb false -∗
      ucl k [] (LogEntryDefs.MkCH [] [] [] None) ∗ fturn gf k.
  Proof using .
    iIntros "#Hpin #Hfp #Hpera (Ht & Hcs & Hps & HE & Hdl & Hdll & Hsc & Hrp) Hf0 Hfla Hblk Hrb Hcur1".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct "Ht" as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (dl_list_lb_get with "Hdll") as "[Hdll #Hdllb]".
    iSplitL "Ht1 Hcs Hps HE Hdl1 Hdll Hfla Hblk Hrb Hcur1 Hsc".
    { rewrite /ucl. iApply (pwclV_mid pg U ucparams ∅ uwa uwild k [] (LogEntryDefs.MkCH [] [] [] None) v with "Hpin Hsc").
      rewrite /peclV /gcl. iLeft. iRight. iExists v, (gstage0 U).
      cbn [gs_ps gs_cs gs_E gs_w gs_st gstage0 LogEntryDefs.ch_dl length].
      iSplitR; [iExact "Hpin" |].
      iSplitL "Hfla".
      { iExists vf. iFrame "Hfp Hfla". cbn [f0_wit default].
        iSplit; [done | iApply (f0_typed_none gf)]. }
      iSplitL "Hblk Hcur1 Hrb".
      { rewrite uwa_ext /pext.
        iExists w, 0%nat, gb, [], false. iFrame "Hpera Hcur1 Hrb".
        rewrite (_ : lm_stream U ∅ _ = []); [iExact "Hblk" | reflexivity]. }
      rewrite (_ : lm_pcount U [] [] (gs_state U ∅ (gstage0 U)) [] [] = 0%nat);
        [| reflexivity].
      iFrame "Ht1 Hcs Hps HE Hdl1 Hdll".
      iSplitR; [iApply gstore_nil |].
      iPureIntro.
      rewrite /gcl_pure.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      split_and!.
      - exact (lm_out_pure_0 U ∅ k [] fstate_ok_empty).
      - exact (lm_cs_len_ok_0 U).
      - exact (lm_ps_len_ok_0 U ∅).
      - exact (gin_pure_0 U k).
      - by rewrite /garm_era.
      - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
        rewrite app_nil_r echoed_nil /seg_of fmap_nil. reflexivity.
      - exact (lm_dl_ok_0 U). }
    rewrite /fturn. iExists v, vf. iFrame "Hpin Hfp Ht2 Hdl2 Hcslb Hpslb Hf0 Hrp".
    iApply (inp_lb_of_dl_lb v [] []); [apply prefix_nil | iExact "Hdllb"].
  Qed.

  (* =================================================================== *)
  (*  6.  THE LEDGER                                                      *)
  (*                                                                      *)
  (*  [FileOut.file_led] at the union's discipline, with the pipeline     *)
  (*  byte ledger's era map beside the file's.  THE COUNTER CASES ON THE  *)
  (*  LANDED DECIDER [UnionDecU.lm_disc_ulmG_dec]: no hypothesis, no      *)
  (*  classical axiom.                                                    *)
  (* =================================================================== *)
  (* THE CONCLUSION'S RESOURCE (sync SY3-A4): each cycle's boot state
     and its last completed sync ([UnionOutPure.union_phi_sync_body]); the
     floor, a lower bound of the run-long history whose last record is the
     last completed sync so far; and the era's record, whose floor's last
     record is the era's boot record (the cycles before the open one) *)
  Definition union_phi_res (h : list mobs) : iProp Σ :=
    (∃ W : list (fstate * option srec),
       ⌜lm_disc U h -> union_phi_sync_body h W⌝ ∗ f0_pinned gf h (fst <$> W)
       ∗ (∃ F : list srec, sl_lb (ff_hist (fgn_cl gf)) F
            ∗ ⌜lm_disc U h -> slast F = union_rec_now h W⌝)
       ∗ (⌜obs_boots h = 0%nat⌝
          ∨ ∃ vf : file_era, file_era_pin gf (obs_boots h) vf
              ∗ sl_lb (ff_hist (fgn_cl gf)) (fe_floor vf)
              ∗ ⌜lm_disc U h -> slast (fe_floor vf) = union_rec_base h W⌝))%I.

  Global Instance union_phi_res_timeless h : Timeless (union_phi_res h).
  Proof using . rewrite /union_phi_res. apply _. Qed.

  (* THE SYNC REGISTRY'S AUTHORITY (sync SY3-A3bc): eras [0 .. obs_boots h]
     registered *)
  Definition union_reg (h : list mobs) : iProp Σ :=
    (∃ R : gmap nat gname, ghost_map_auth_frac (ff_reg (fgn_cl gf)) 1 R
       ∗ ⌜forall k : nat, k ∈ dom R <-> (k <= obs_boots h)%nat⌝)%I.

  (* THE FLOOR (sync SY3-A4, the owner's ruling): a lower bound of the
     RUN-LONG sync history, which the durable copy holds the authority of --
     no era, no registration.  The PowerOn pins it into the era's record
     ([fe_floor]) and never writes it.  The conclusion's resource carries
     its own ([union_phi_res]); this one rides the ledger's TAINT arm, so a
     tainted PowerOn still has a floor to pin *)
  Definition union_floor : iProp Σ :=
    (∃ F : list srec, sl_lb (ff_hist (fgn_cl gf)) F)%I.

  Global Instance union_floor_persistent : Persistent union_floor.
  Proof using . rewrite /union_floor. apply _. Qed.

  (* THE ERA'S BASE (sync SY3-A3bc, ruling (a)): the current era's record
     is pinned, and the line list is its base followed by the current
     cycle's lines *)
  Definition union_base (h : list mobs) : iProp Σ :=
    (⌜obs_boots h = 0%nat⌝
     ∨ ∃ vf : file_era, file_era_pin gf (obs_boots h) vf
         ∗ ⌜ulines_of h = fe_base vf ++ ulast_cyc h⌝)%I.

  Global Instance union_base_persistent h : Persistent (union_base h).
  Proof using . rewrite /union_base. apply _. Qed.

  Definition union_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own_frac (eg_taint (fgn_echo gf)) 1
       (if decide (lm_disc U h) then 0%nat else 1%nat)
     ∗ pin_map (fgn_echo gf) h
     ∗ f0_map gf h
     ∗ pera_map pg h
     ∗ fl_auth (fgn_cl gf) (ulines_of h)
     ∗ (union_phi_res h ∨ UT ∗ union_floor)
     ∗ union_reg h ∗ union_base h)%I.

  Global Instance union_led_timeless h : Timeless (union_led h).
  Proof using . rewrite /union_led. apply _. Qed.

  (* the birth's yield: the TRACE slot's part -- the registry at era 0 and
     the era-0 floor beside the file's and the byte ledger's *)
  Definition union_cl_all : iProp Σ :=
    (file_cl_all gf ∗ ghost_map_auth_frac (ugn_pera ug) 1 (∅ : gmap nat pipe_era)
     ∗ (∃ γ0 : gname, ghost_map_auth_frac (ff_reg (fgn_cl gf)) 1 {[0%nat := γ0]})
     ∗ sl_lb (ff_hist (fgn_cl gf)) [])%I.

  (* ...and the CRASH slot's part: what era 0's durable copy is founded
     from ([AppFile.file_init]) *)
  Definition union_cls : iProp Σ :=
    (∃ γ0 : gname, sync_reg (fgn_cl gf) 0 γ0 ∗ sl_auth γ0 (1/2) []
       ∗ sync_cm_auth (fgn_cl gf) 0 ∗ sl_auth (ff_hist (fgn_cl gf)) 1 []
       ∗ run_auth (fgn_cl gf) 0 ∗ fl_lb (fgn_cl gf) [])%I.

  Lemma union_led_init : union_cl_all -∗ union_led [].
  Proof using .
    rewrite /union_cl_all /file_cl_all /file_cl /echo_cl /union_led /pin_map
      /f0_map /pera_map.
    iIntros "([[[Ht Hm] Hfl] Hmf] & Hme & (%γ0 & Hreg) & #Hlb0)".
    rewrite decide_True; [| exact (lm_disc_nil U)].
    rewrite (_ : ulines_of [] = []); last first.
    { rewrite /ulines_of /cycles_of /cycles_rev /=. reflexivity. }
    iFrame "Ht Hfl".
    iSplitL "Hm"; [iExists ∅; iFrame "Hm"; iPureIntro; apply pin_dom_empty |].
    iSplitL "Hmf"; [iExists ∅; iFrame "Hmf"; iPureIntro; apply pin_dom_empty |].
    iSplitL "Hme"; [iExists ∅; iFrame "Hme"; iPureIntro; apply pin_dom_empty |].
    iSplitR.
    { iLeft. iExists []. iSplitR.
      { iPureIntro. intros _. exact union_phi_sync_body_nil. }
      iSplitR; [iApply f0_pinned_undrained; reflexivity |].
      iSplitR; [iExists []; iFrame "Hlb0"; iPureIntro; intros _; reflexivity |].
      iLeft. by iPureIntro. }
    iSplitL "Hreg".
    { iExists {[0%nat := γ0]}. iFrame "Hreg". iPureIntro. intros k.
      rewrite dom_singleton_L elem_of_singleton. cbn. lia. }
    iLeft. by iPureIntro.
  Qed.

  (* ---- THE ERA'S TURN IN ITS FOUR STAGES (sync SY3-A3bc, design 4.5
          "PowerOn"; [App.app_turn]/[app_turn']/[app_turn'']/[app_iturn]) ---- *)

  (* what the on-arm yields beside init's credential: the era's fresh sync
     list registered at the era, the era's record with its base and the copy
     list's authority, a lower bound at the base, and the floor *)
  Definition union_tn (k : nat) : iProp Σ :=
    (∃ (γ : gname) (vf : file_era),
        sync_reg (fgn_cl gf) k γ ∗ sl_auth γ 1 [] ∗ file_era_pin gf k vf
        ∗ fcp_auth vf [] ∗ fl_lb (fgn_cl gf) (fe_base vf)
        (* ...and the floor, as the era's record pins it (sync SY3-A4) *)
        ∗ sl_lb (ff_hist (fgn_cl gf)) (fe_floor vf))%I.

  Definition uturn (k : nat) : iProp Σ := (fturn gf k ∗ union_tn k)%I.

  (* what the transport hands back: the copy's line list pinned at the
     era's record, and the era's token pieces with a lower bound of the list
     for the floor *)
  Definition uturn' (k : nat) : iProp Σ :=
    (fturn gf k ∗ ∃ (vf : file_era) (ls : list fl_line),
       file_era_pin gf k vf ∗ fcp_pin vf ls ∗ fl_lb (fgn_cl gf) ls
       ∗ (UT ∨ ∃ (γ : gname) (Ls : list srec),
                 sync_reg (fgn_cl gf) k γ ∗ sl_auth γ (1/4) Ls ∗ sl_lb γ Ls
                 ∗ sync_cm_lb (fgn_cl gf) k))%I.

  (* after the return path: the copy's list certified INSIDE the era's base,
     and a lower bound at the base (sh's first line witness) *)
  Definition uturn'' (k : nat) : iProp Σ :=
    (fturn gf k ∗ ∃ (vf : file_era) (ls : list fl_line),
       file_era_pin gf k vf ∗ fcp_pin vf ls ∗ ⌜ls `prefix_of` fe_base vf⌝
       ∗ fl_lb (fgn_cl gf) (fe_base vf)
       ∗ (UT ∨ ∃ (γ : gname) (Ls : list srec),
                 sync_reg (fgn_cl gf) k γ ∗ sl_auth γ (1/4) Ls
                 ∗ sync_cm_lb (fgn_cl gf) k))%I.

  (* what /init is handed: the above less the token *)
  Definition uturn_i (k : nat) : iProp Σ :=
    (fturn gf k ∗ ∃ (vf : file_era) (ls : list fl_line),
       file_era_pin gf k vf ∗ fcp_pin vf ls ∗ ⌜ls `prefix_of` fe_base vf⌝
       ∗ fl_lb (fgn_cl gf) (fe_base vf))%I.

  Global Instance union_tn_timeless k : Timeless (union_tn k).
  Proof using . rewrite /union_tn. apply _. Qed.
  Global Instance uturn_timeless k : Timeless (uturn k).
  Proof using . rewrite /uturn. apply _. Qed.
  Global Instance uturn'_timeless k : Timeless (uturn' k).
  Proof using . rewrite /uturn'. apply _. Qed.
  Global Instance uturn''_timeless k : Timeless (uturn'' k).
  Proof using . rewrite /uturn''. apply _. Qed.
  Global Instance uturn_i_timeless k : Timeless (uturn_i k).
  Proof using . rewrite /uturn_i. apply _. Qed.

  (* THE POWER STEP: the on-arm allocates the era's three records (echo's,
     the file's boot state at the ledger's line list, the byte ledger) and
     the era's sync list (registered), mints the pins, and splits the ghosts
     into the era's claim and the turn *)
  Lemma union_led_pow (h : list mobs) (on : bool) :
    union_led h ==∗
      union_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else ucl (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)
              ∗ uturn (S (obs_boots h))).
  Proof using .
    iIntros "(Ht & Hpm & Hfm & Hme & Hfl & Hphi & Hreg & #Hbase)".
    rewrite /union_led.
    rewrite (decide_ext _ (lm_disc U h) 0%nat 1%nat
               (lm_disc_power U h on union_st_ok)).
    rewrite (_ : ulines_of (h ++ [if on then ObsPowerOff else ObsPowerOn])
                 = ulines_of h); [| exact (ulines_of_power h on)].
    destruct on.
    - assert (Hb : obs_boots (h ++ [ObsPowerOff]) = obs_boots h)
        by (rewrite obs_boots_app /=; lia).
      iDestruct (pin_map_step (fgn_echo gf) h ObsPowerOff eq_refl with "Hpm") as "Hpm".
      iDestruct (f0_map_step gf h ObsPowerOff eq_refl with "Hfm") as "Hfm".
      iDestruct (pera_map_step pg h ObsPowerOff eq_refl with "Hme") as "Hme".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm Hfm Hme Hfl".
      iSplitL "Hphi".
      { iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
        iLeft. iDestruct "Hphi" as (W) "(%Hbd & _ & (%F & #HF & %HFr) & #Hera)".
        iExists W. iSplitR.
        { iPureIntro. intros Hd.
          exact (union_phi_sync_body_off h W
                   (Hbd (proj1 (lm_disc_power U h true union_st_ok) Hd))). }
        iSplitR.
        { iApply f0_pinned_undrained.
          by rewrite (open_seg_power h ObsPowerOff eq_refl). }
        iSplitR.
        { iExists F. iFrame "HF". iPureIntro. intros Hd. rewrite union_rec_now_off.
          exact (HFr (proj1 (lm_disc_power U h true union_st_ok) Hd)). }
        rewrite Hb. iDestruct "Hera" as "[%H0 | (%vf & #Hp & #HflE & %Hr)]";
          [by iLeft | iRight].
        iExists vf. iFrame "Hp HflE". iPureIntro. intros Hd. rewrite union_rec_base_off.
        exact (Hr (proj1 (lm_disc_power U h true union_st_ok) Hd)). }
      iSplitL "Hreg".
      { iDestruct "Hreg" as (R) "[HR %HR]". iExists R. iFrame "HR". by rewrite Hb. }
      rewrite /union_base Hb. iDestruct "Hbase" as "[%H0 | (%vf & #Hp & %Hu)]";
        [by iLeft | iRight].
      iExists vf. iFrame "Hp". iPureIntro.
      exact (ubase_off h _ Hu).
    - assert (Hb : obs_boots (h ++ [ObsPowerOn]) = S (obs_boots h))
        by (rewrite obs_boots_app /=; lia).
      iMod era_full_alloc as (v) "Hfull".
      (* the floor the era's record pins: the conclusion's, or (tainted)
         the taint arm's *)
      iAssert (∃ F : list srec, sl_lb (ff_hist (fgn_cl gf)) F
                 ∗ ((∃ W : list (fstate * option srec),
                       ⌜lm_disc U h -> union_phi_sync_body h W⌝
                       ∗ ⌜lm_disc U h -> slast F = union_rec_now h W⌝) ∨ UT))%I
        with "[Hphi]" as (F) "[#HF Hphi]".
      { iDestruct "Hphi" as "[Hphi | #HT]".
        - iDestruct "Hphi" as (W) "(%Hbd & _ & (%F & #HF & %HFr) & _)".
          iExists F. iFrame "HF". iLeft. iExists W. by iSplit; iPureIntro.
        - iDestruct "HT" as "[#HT (%F & #HF)]". iExists F. iFrame "HF". by iRight. }
      iMod (f0_alloc (ulines_of h) F) as (vf) "(%Hbv & %Hfv & Hf0 & Hfla & Hcp)".
      iMod blk_alloc as (w gb) "(Hblk & Hrb & Hcur1)".
      iMod (pin_map_on (fgn_echo gf) h v with "Hpm") as "[Hpm #Hpin]".
      iMod (f0_map_on gf h vf with "Hfm") as "[Hfm #Hfp]".
      iMod (pera_map_on pg h w with "Hme") as "[Hme #Hpera]".
      iDestruct (union_era_split (S (obs_boots h)) v vf w gb
                   with "Hpin Hfp Hpera Hfull Hf0 Hfla Hblk Hrb Hcur1") as "(Hcl & Hturn)".
      (* the era's sync list, registered *)
      iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γ) "Hγ";
        [apply mono_list_auth_valid |].
      iDestruct "Hreg" as (R) "[HR %HR]".
      iMod (ghost_map_insert_persist (S (obs_boots h)) γ with "HR") as "[HR #Hel]".
      { apply not_elem_of_dom. intros Hin. apply HR in Hin. lia. }
      iDestruct (fl_auth_lb with "Hfl") as "[Hfl #Hlbb]".
      iModIntro. iSplitR "Hcl Hturn Hγ Hcp".
      + iFrame "Ht Hpm Hfm Hme Hfl".
        iSplitL "Hphi".
        { iDestruct "Hphi" as "[Hphi | #HT]";
            [| iRight; iFrame "HT"; iExists F; iExact "HF"].
          iLeft. iDestruct "Hphi" as (W) "[%Hbd %HFr]".
          iExists (W ++ [((union_rec_now h W).2, None)]). iSplitR.
          { iPureIntro. intros Hd.
            exact (union_phi_sync_body_on h W
                     (Hbd (proj1 (lm_disc_power U h false union_st_ok) Hd))). }
          iSplitR.
          { iApply f0_pinned_undrained.
            by rewrite (open_seg_power h ObsPowerOn eq_refl). }
          iSplitR.
          { iExists F. iFrame "HF". iPureIntro. intros Hd.
            pose proof (proj1 (lm_disc_power U h false union_st_ok) Hd) as Hd0.
            destruct (Hbd Hd0) as (Hlen & _).
            rewrite union_rec_now_on; [exact (HFr Hd0) | exact Hlen]. }
          iRight. iExists vf. rewrite Hb Hfv. iFrame "Hfp HF". iPureIntro. intros Hd.
          pose proof (proj1 (lm_disc_power U h false union_st_ok) Hd) as Hd0.
          destruct (Hbd Hd0) as (Hlen & _).
          rewrite union_rec_base_on; [exact (HFr Hd0) | exact Hlen]. }
        iSplitL "HR".
        { iExists (<[S (obs_boots h) := γ]> R). iFrame "HR". iPureIntro. intros k.
          rewrite dom_insert_L elem_of_union elem_of_singleton HR Hb. lia. }
        rewrite /union_base Hb. iRight. iExists vf. iFrame "Hfp". iPureIntro.
        rewrite Hbv. exact (ubase_on h).
      + iFrame "Hcl Hturn". rewrite /union_tn.
        iExists γ, vf. rewrite Hbv Hfv. iFrame "Hel Hfp Hcp Hlbb HF". iExact "Hγ".
  Qed.

  (* THE OUTPUT STEP, AND THE ERA'S FIRST DRAIN ([FileOut.file_led_tx] at
     the union): the drain hands the era's boot state, its deed witness, a
     lower bound pinned to the era's record, and the cycle's last completed
     sync with the history's lower bound ending at it (sync SY3-A4) -- the
     floor moves to it, or back to the era's own *)
  Lemma union_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (match i with
     | Uart0 => udrain_ret (obs_boots h) (open_seg h ++ [ObsUartOut Uart0 b])
     | _ => True
     end) -∗
    union_led h ==∗ union_led (h ++ [ObsUartOut i b]).
  Proof using .
    intros Hsh. iIntros "Hgo (Ht & Hpm & Hfm & Hme & Hfl & Hphi & Hreg & #Hbase)".
    assert (Hbo : obs_boots (h ++ [ObsUartOut i b]) = obs_boots h)
      by (rewrite obs_boots_app /=; lia).
    assert (Hsh' : trace_shape (h ++ [ObsUartOut i b]) true)
      by (eapply trace_shape_snoc; [exact Hsh | by destruct i]).
    iAssert (union_reg (h ++ [ObsUartOut i b]) ∗ union_base (h ++ [ObsUartOut i b]))%I
      with "[Hreg]" as "[Hreg #Hbase']".
    { iSplitL "Hreg".
      { iDestruct "Hreg" as (R) "[HR %HR]". iExists R. iFrame "HR". by rewrite Hbo. }
      rewrite /union_base Hbo. iDestruct "Hbase" as "[%H0 | (%vf & #Hp & %Hu)]";
        [by iLeft | iRight].
      iExists vf. iFrame "Hp". iPureIntro.
      exact (ubase_io h (ObsUartOut i b) _ Hsh ltac:(by destruct i) Hu). }
    iDestruct (pin_map_step (fgn_echo gf) h (ObsUartOut i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step gf h (ObsUartOut i b) eq_refl with "Hfm") as "Hfm".
    iDestruct (pera_map_step pg h (ObsUartOut i b) eq_refl with "Hme") as "Hme".
    rewrite /union_led.
    rewrite (decide_ext _ (lm_disc U h) 0%nat 1%nat (lm_disc_out U h i b Hsh)).
    rewrite (_ : ulines_of (h ++ [ObsUartOut i b]) = ulines_of h);
      [| exact (ulines_of_out h i b Hsh)].
    iFrame "Ht Hpm Hfm Hme Hreg Hbase'".
    iDestruct "Hphi" as "[Hphi | HT]"; last first.
    { iModIntro. iFrame "Hfl". by iRight. }
    iDestruct "Hphi" as (W) "(%Hb & #Hpin0 & (%F & #HF & %HFr) & #Hera)".
    assert (Hdh : lm_disc U (h ++ [ObsUartOut i b]) -> lm_disc U h)
      by exact (proj1 (lm_disc_out U h i b Hsh)).
    destruct i; last first.
    { iModIntro. iFrame "Hfl". iLeft. iExists W. iSplitR.
      { iPureIntro. intros Hd.
        apply (union_phi_sync_body_step_io h (ObsUartOut Uart1 b) W Hsh eq_refl
                 eq_refl), Hb, Hdh, Hd. }
      iSplitR.
      { iApply (f0_pinned_io gf h (ObsUartOut Uart1 b) (fst <$> W) eq_refl eq_refl
                  with "Hpin0"). }
      iSplitR.
      { iExists F. iFrame "HF". iPureIntro. intros Hd.
        destruct (Hb (Hdh Hd)) as (Hlen & _).
        rewrite union_rec_now_io; [exact (HFr (Hdh Hd)) | exact Hsh | reflexivity
                                   | exact Hlen]. }
      rewrite Hbo. iDestruct "Hera" as "[%H0 | (%vf & #Hp & #HflE & %Hr)]";
        [by iLeft | iRight].
      iExists vf. iFrame "Hp HflE". iPureIntro. intros Hd.
      destruct (Hb (Hdh Hd)) as (Hlen & _).
      rewrite union_rec_base_io'; [exact (Hr (Hdh Hd)) | exact Hsh | reflexivity
                                   | exact Hlen]. }
    rewrite /udrain_ret.
    iDestruct "Hgo" as "[#HT | Hgo]".
    { iModIntro. iFrame "Hfl". iRight. iFrame "HT". iExists F. iExact "HF". }
    iDestruct "Hgo" as (s0 vf o) "(%Hgo & _ & #Hty & #Hfp & #Hlb & Ho)".
    iDestruct "Hera" as "[%H0 | (%vfE & #HpE & #HflE & %HrE)]".
    { exfalso. exact (trace_shape_boots h true Hsh eq_refl H0). }
    iDestruct (file_era_pin_agree with "Hfp HpE") as %<-.
    iDestruct "Hbase'" as "[%H0' | (%vfB & #HpB & %HuB)]".
    { exfalso. exact (trace_shape_boots _ true Hsh' eq_refl H0'). }
    rewrite Hbo. iDestruct (file_era_pin_agree with "Hfp HpB") as %<-.
    (* THE ERA'S BOOT FACT: the boot state is admissible at the era's floor *)
    iDestruct (f0_bl_bt with "[]") as "[#HT | (%ls & #Hls & %Hadm0)]";
      [iApply (f0_lb_bl with "Hlb")
      | iModIntro; iFrame "Hfl"; iRight; iFrame "HT"; iExists F; iExact "HF" |].
    iDestruct (fl_lb_prefix with "Hfl Hls") as %Hlsp.
    pose proof (uadm_mono _ _ _ _ Hlsp Hadm0) as Hadm.
    iAssert (⌜obs_wire Uart0 (open_seg h) <> [] ->
               exists u1 o0, W = u1 ++ [(s0, o0)]⌝)%I as "%Hlast".
    { destruct (decide (obs_wire Uart0 (open_seg h) = [])) as [Hw | Hw].
      - iPureIntro. intro Hne. by destruct (Hne Hw).
      - iDestruct (f0_pinned_drained gf h (fst <$> W) vf s0 Hw with "Hfp Hlb Hpin0")
          as %(u1 & Hu1).
        iPureIntro. intros _.
        apply fmap_app_inv in Hu1 as (w1 & w2 & -> & Hw2 & ->).
        destruct w2 as [| [x o0] [| ? ?]]; try discriminate.
        injection Hw2 as <-. by exists w1, o0. }
    iAssert (sl_lb (ff_hist (fgn_cl gf)) (fe_floor vf)
             ∗ (⌜o = None⌝
                ∨ ∃ (J : list (bv 8)) (c : fstate) (L : list srec),
                    ⌜o = Some (nlines J, c)⌝
                    ∗ sl_lb (ff_hist (fgn_cl gf))
                        (L ++ [(length (fe_base vf ++ ulines_in J), c)])))%I
      with "[Ho]" as "[_ Ho]"; [by iFrame "HflE Ho" |].
    iModIntro. iFrame "Hfl". iLeft.
    iExists (removelast W ++ [(s0, o)]). iSplitR.
    { iPureIntro. intros Hd. pose proof (Hdh Hd) as Hd0.
      apply (union_phi_sync_body_drain h b W s0 o Hsh Hd0 Hgo); [| exact Hlast | exact (Hb Hd0)].
      pose proof (HrE Hd0) as HrE'. rewrite /union_rec_base in HrE'.
      rewrite -HrE'. exact Hadm. }
    iSplitR.
    { rewrite fmap_app /=.
      iApply (f0_pinned_drain gf h b (fst <$> removelast W) vf s0 with "Hfp Hlb"). }
    iSplitL "Ho".
    { iDestruct "Ho" as "[%Hon | (%J & %c & %L & %HoJ & #HL)]".
      - iExists (fe_floor vf). iFrame "HflE". iPureIntro. intros Hd.
        pose proof (Hdh Hd) as Hd0. destruct (Hb Hd0) as (Hlen & _). subst o.
        destruct (union_W_snoc h W Hsh Hlen) as (u1 & y & -> & Hl1).
        rewrite epu_removelast_snoc.
        rewrite (union_rec_now_drain_none h (ObsUartOut Uart0 b) u1 y s0 Hsh eq_refl Hl1).
        exact (HrE Hd0).
      - iExists (L ++ [(length (fe_base vf ++ ulines_in J), c)]). iFrame "HL".
        iPureIntro. intros Hd.
        pose proof (Hdh Hd) as Hd0. destruct (Hb Hd0) as (Hlen & _). subst o.
        destruct (union_W_snoc h W Hsh Hlen) as (u1 & y & -> & Hl1).
        rewrite epu_removelast_snoc slast_snoc.
        rewrite (union_rec_now_drain_some (h ++ [ObsUartOut Uart0 b]) u1 s0 (fe_base vf)
                   J c Hsh' HuB); [reflexivity |].
        rewrite (cycles_len_io h (ObsUartOut Uart0 b) Hsh eq_refl). exact Hl1. }
    rewrite Hbo. iRight. iExists vf. iFrame "Hfp HflE". iPureIntro. intros Hd.
    pose proof (Hdh Hd) as Hd0. destruct (Hb Hd0) as (Hlen & _).
    destruct (union_W_snoc h W Hsh Hlen) as (u1 & y & -> & Hl1).
    rewrite epu_removelast_snoc.
    rewrite (union_rec_base_io h (ObsUartOut Uart0 b) u1 (s0, o) y Hsh eq_refl Hl1).
    exact (HrE Hd0).
  Qed.

  (* THE INPUT STEP: the counter decides, and the byte's TAG is handed
     out, its line list's lower bound grown by what the input completed *)
  Lemma union_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    union_led h ==∗
      union_led (h ++ [ObsUartIn i b]) ∗ utag (h ++ [ObsUartIn i b]).
  Proof using .
    intros Hsh. iIntros "(Hcnt & Hpm & Hfm & Hme & Hfl & Hphi & Hreg & #Hbase)".
    assert (Hbo : obs_boots (h ++ [ObsUartIn i b]) = obs_boots h)
      by (rewrite obs_boots_app /=; lia).
    iAssert (union_reg (h ++ [ObsUartIn i b])
             ∗ ∃ vf : file_era, file_era_pin gf (obs_boots (h ++ [ObsUartIn i b])) vf
                 ∗ ⌜ulines_of (h ++ [ObsUartIn i b])
                    = fe_base vf ++ ulast_cyc (h ++ [ObsUartIn i b])⌝)%I
      with "[Hreg]" as "[Hreg #Hbase']".
    { iSplitL "Hreg".
      { iDestruct "Hreg" as (R) "[HR %HR]". iExists R. iFrame "HR". by rewrite Hbo. }
      rewrite Hbo. iDestruct "Hbase" as "[%H0 | (%vf & #Hp & %Hu)]".
      { exfalso. exact (trace_shape_boots h true Hsh eq_refl H0). }
      iExists vf. iFrame "Hp". iPureIntro.
      exact (ubase_io h (ObsUartIn i b) _ Hsh ltac:(by destruct i) Hu). }
    iDestruct (pin_map_step (fgn_echo gf) h (ObsUartIn i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step gf h (ObsUartIn i b) eq_refl with "Hfm") as "Hfm".
    iDestruct (pera_map_step pg h (ObsUartIn i b) eq_refl with "Hme") as "Hme".
    iMod (fl_auth_grow_pre gf (ulines_of h) (ulines_of (h ++ [ObsUartIn i b]))
            (ulines_of_snoc h (ObsUartIn i b)) with "Hfl")
      as "[Hfl #Hfllb]".
    assert (Hin : lm_disc U (h ++ [ObsUartIn i b]) -> lm_disc U h).
    { destruct i;
        [ exact (lm_disc_in U UB h b Hsh)
        | exact (proj1 (lm_disc_other U h (ObsUartIn Uart1 b) eq_refl I Hsh)) ]. }
    iAssert (union_phi_res (h ++ [ObsUartIn i b]) ∨ UT ∗ union_floor)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
      iLeft. iDestruct "Hphi" as (W) "(%Hb & #Hp & (%F & #HF & %HFr) & #Hera)".
      iExists W. iSplitR.
      { iPureIntro. intros Hd.
        apply (union_phi_sync_body_step_io h (ObsUartIn i b) W Hsh
                 ltac:(by destruct i) ltac:(by destruct i)), Hb.
        exact (Hin Hd). }
      iSplitR.
      { iApply (f0_pinned_io gf h (ObsUartIn i b) (fst <$> W) ltac:(by destruct i)
                  ltac:(by destruct i) with "Hp"). }
      iSplitR.
      { iExists F. iFrame "HF". iPureIntro. intros Hd.
        destruct (Hb (Hin Hd)) as (Hlen & _).
        rewrite union_rec_now_io; [exact (HFr (Hin Hd)) | exact Hsh | by destruct i
                                   | exact Hlen]. }
      rewrite Hbo. iDestruct "Hera" as "[%H0 | (%vf & #Hpv & #HflE & %Hr)]";
        [by iLeft | iRight].
      iExists vf. iFrame "Hpv HflE". iPureIntro. intros Hd.
      destruct (Hb (Hin Hd)) as (Hlen & _).
      rewrite union_rec_base_io'; [exact (Hr (Hin Hd)) | exact Hsh | by destruct i
                                   | exact Hlen]. }
    assert (Hsh' : trace_shape (h ++ [ObsUartIn i b]) true)
      by (eapply trace_shape_snoc; [exact Hsh | reflexivity]).
    rewrite /union_led /utag.
    destruct (decide (lm_disc U (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; [| exact (Hin Hd')].
      iModIntro. iFrame "Hcnt Hpm Hfm Hme Hfl Hphi Hfllb Hreg".
      iSplitR; [iRight; iExact "Hbase'" |].
      iSplitR; [by iPureIntro |]. iSplitR; [iLeft; by iPureIntro |].
      iExact "Hbase'".
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (lm_disc U h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hfm Hme Hfl Hphi Hfllb Hreg".
      iSplitR; [iRight; iExact "Hbase'" |].
      iSplitR; [by iPureIntro |]. iSplitR; [iRight; rewrite /file_taint /echo_taint;
        iExact "Hlb" |].
      iExact "Hbase'".
  Qed.

  (* THE CONCLUSION's read at the end of the run (sync SY3-A4: each cycle
     with its last completed sync, each later boot admissible at the last
     completed sync before it) *)
  Lemma union_led_phi (h : list mobs) :
    union_led h -∗ ⌜union_phi_sync h⌝.
  Proof using .
    iIntros "(Hcnt & _ & _ & _ & _ & [Hphi | [HT' _]] & _)".
    { iDestruct "Hphi" as (W) "[%Hb _]". iPureIntro.
      exact (union_phi_sync_of_body h W Hb). }
    rewrite /file_taint /echo_taint.
    iDestruct (mono_nat_auth_lb_own_valid with "Hcnt HT'") as %[_ Hle].
    iPureIntro. rewrite /union_phi_sync. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.
  (* THE RETURN PATH (sync SY3-A3bc, [App.al_back]): at the history the
     power-on left, the line list IS the era's base, so the copy's list the
     transport pinned is inside it (the authority against the lower bound);
     the floor moves to the new era's list *)
  Lemma union_led_back (h : list mobs) :
    union_led (h ++ [ObsPowerOn]) -∗ uturn' (S (obs_boots h)) ==∗
      union_led (h ++ [ObsPowerOn]) ∗ uturn'' (S (obs_boots h)).
  Proof using .
    assert (Hb : obs_boots (h ++ [ObsPowerOn]) = S (obs_boots h))
      by (rewrite obs_boots_app /=; lia).
    iIntros "(Ht & Hpm & Hfm & Hme & Hfl & Hphi & Hreg & #Hbase)".
    iIntros "(Hturn & %vf & %ls & #Hp & #Hcp & #Hls & Htk)".
    iDestruct "Hbase" as "[%H0 | (%vf' & #Hp' & %Hu)]"; [lia |].
    rewrite Hb. iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    rewrite ulast_cyc_on app_nil_r in Hu.
    iDestruct (fl_lb_prefix with "Hfl Hls") as %Hpre.
    iDestruct (fl_auth_lb with "Hfl") as "[Hfl #Hlbb]".
    rewrite Hu in Hpre. iEval (rewrite Hu) in "Hlbb".
    (* the floor is never written here (sync SY3-A4): the return path only
       certifies the copy's line list inside the era's base *)
    iAssert (UT ∨ ∃ (γ : gname) (Ls : list srec),
               sync_reg (fgn_cl gf) (S (obs_boots h)) γ ∗ sl_auth γ (1/4) Ls
               ∗ sync_cm_lb (fgn_cl gf) (S (obs_boots h)))%I
      with "[Htk]" as "Htk".
    { iDestruct "Htk" as "[#HT | (%γ & %Ls & #Hr & Hq & #Hl & #Hc)]"; [by iLeft |].
      iRight. iExists γ, Ls. iFrame "Hr Hq Hc". }
    iModIntro. iSplitR "Hturn Htk".
    { iFrame "Ht Hpm Hfm Hme Hfl Hphi Hreg". iRight. iExists vf.
      rewrite Hb. iFrame "Hp". iPureIntro. rewrite ulast_cyc_on app_nil_r. exact Hu. }
    iFrame "Hturn". iExists vf, ls. iFrame "Hp Hcp Hlbb Htk". by iPureIntro.
  Qed.

  (* THE FOUNDING (sync SY3-A3bc, [App.al_found]): the token out of the
     returned turn, the rest for /init *)
  Lemma union_found (k : nat) :
    uturn'' (S k) ⊢ |==> union_tk (fgn_cl gf) k ∗ uturn_i (S k).
  Proof using .
    iIntros "(Hturn & %vf & %ls & #Hp & #Hcp & %Hpre & #Hlbb & Htk)".
    iModIntro. iSplitL "Htk".
    { rewrite /union_tk. iDestruct "Htk" as "[#HT | (%γ & %Ls & Hr & Hq & Hc)]";
        [by iLeft | iRight]. iExists γ, Ls. iFrame "Hr Hq Hc". }
    iFrame "Hturn". iExists vf, ls. iFrame "Hp Hcp Hlbb". by iPureIntro.
  Qed.
End union_out.

(* ===================================================================== *)
(*  7.  THE BIRTH STEP: the file's, and the byte ledger's map beside it   *)
(* ===================================================================== *)
Section union_birth.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.

  (* the birth, handed the machine's started counter's name, which the
     file application's fixed part keeps; the SYNC PART's era 0: a list
     registered at 0, its half and the commit-era counter's authority to
     the crash slot (era 0's durable copy), the registry and the floor to
     the trace slot *)
  Lemma union_birth_all (γst : gname) :
    ⊢ |==> ∃ ug : union_gn, ⌜ff_st (fgn_cl (ugn_file ug)) = γst⌝
          ∗ union_cls ug ∗ union_cl_all ug.
  Proof using .
    iMod (file_birth_all γst) as (gf) "(%Hst & Hf & Hreg & Hcm & Hhi & Hra)".
    iMod (ghost_map_alloc_empty (K := nat) (V := pipe_era)) as (gm) "Hm".
    iMod (own_alloc (●ML ([] : list (leibnizO srec)))) as (γ0) "H0";
      [apply mono_list_auth_valid |].
    iMod (ghost_map_insert_persist 0%nat γ0 with "Hreg") as "[Hreg #Hel]";
      [apply lookup_empty |].
    iDestruct "Hf" as "[[He Hfl] Hme]".
    iDestruct (fl_auth_lb with "Hfl") as "[Hfl #Hlb]".
    iDestruct (sl_auth_split3_1 with "H0") as "(Hh & _ & _)".
    iDestruct (sl_lb_get with "Hhi") as "#Hhl".
    iModIntro. iExists (MkUnionGn gf gm). rewrite /union_cls /union_cl_all /=.
    iSplitR; [done |].
    iSplitL "Hh Hcm Hhi Hra".
    { iExists γ0. iFrame "Hel Hh Hlb Hhi Hra". iExact "Hcm". }
    iFrame "Hm". iSplitL "He Hfl Hme".
    { rewrite /file_cl_all /file_cl. iFrame "He Hfl Hme". }
    iSplitL "Hreg"; [iExists γ0; rewrite insert_empty; iFrame "Hreg" |].
    iExact "Hhl".
  Qed.
End union_birth.
