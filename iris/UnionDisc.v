(* ===================================================================== *)
(* UnionDisc.v -- THE UNION MODEL (cuts C9b, C9b2; design: claude-notes/ *)
(* design/union.md section 1, with the review amendments B2 and S3).     *)
(* Pure.                                                                  *)
(*                                                                        *)
(*  One line model [ulm adm] for every line shape the shell reads:        *)
(*  [echo ws], [echo ws > f], [cat f] (the file model's lines and          *)
(*  alternatives, [UR]) and [p | F1 | .. | Fn] for a producer [p] -- echo *)
(*  or [cat f] -- and filter stages [cat] or [grep w] (the N-stage        *)
(*  pipeline model's).  The state is the file's                           *)
(*  ([fstate]); a pipeline round reads it through [FileDisc.files_of] (so *)
(*  [cat f | cat] prints the round's content) and leaves it alone.        *)
(*                                                                        *)
(*  THE PIPELINE ALTERNATIVES ARE SPLIT BY PRODUCER (C9b2): [UPE] at an   *)
(*  echo pipeline, [UPC] at a [cat f] pipeline.  An echo pipeline's       *)
(*  admission reads no state ([uok_echo_st]: no stage of it is [cat f],   *)
(*  so the content function is never consulted), while a [cat f]          *)
(*  pipeline's does.  Splitting them is what lets an echo pipeline's      *)
(*  exec alternative [exec echo failed] be FREE ([lmh_free_ok] quantifies *)
(*  over every line, and at a [cat f] pipeline the same block is          *)
(*  admissible exactly when [f] holds it -- [UnionDiscDec.                *)
(*  demo_execL_state_dep]; under one constructor it could not be free).   *)
(*                                                                        *)
(*  THE CROSS CASES ARE [False] (amendment B2).  [FileDisc.ralt_ok]'s     *)
(*  dead [LPipe] arm admits [LCat]'s five alternatives, [RCRan] (f's     *)
(*  content) among them; reading it at a pipeline would admit the file's *)
(*  content as the output of [echo hi | cat].  So a pipeline line admits  *)
(*  no [UR] alternative but [UR ROom] (sh's node-0 child parses the line *)
(*  and may die of out-of-memory there, saying so; sync design section  *)
(*  2), a file line no pipeline one, an echo pipeline no [UPC] one and a *)
(*  [cat f] pipeline no [UPE] one.                                        *)
(*                                                                        *)
(*  THE ADMISSION [adm] IS A PARAMETER.  [adm_u_g] admits every echo      *)
(*  pipeline and every [cat g | ..] pipeline at a name [g] of the file    *)
(*  model's class ([FileDisc.uname], filenames.md), each filter stage     *)
(*  [cat] or [grep w] of one alphanumeric word (grep-pipes.md cut G8).    *)
(*  A name outside the class is not admitted (owner ruling: a class of   *)
(*  user files, never the image's binaries).                             *)
(*                                                                        *)
(*  THE LAWS hold at EVERY admission ([ulm_laws]): the pipeline half is   *)
(*  [PipesDisc.pipes_lm_laws_fc] at the round's content function, whose   *)
(*  only premise ([fc_ok]) is the file state's own shape                  *)
(*  ([fstate_ok]).  No [adm_ok] is needed and [adm_u_g] does not satisfy  *)
(*  it: [echo fork > f] then [cat f | cat] prints the panic line.         *)
(*                                                                        *)
(*  THE HOOKS (section 4) are proved here field by field; the record      *)
(*  [ulm_hooks : lm_hooks (ulm adm)] is assembled in [UnionDiscDec],      *)
(*  beside the decision of the range condition it needs.                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel LineModelLinks.
Require Import StringBytes ProgTree ProgTreePipes PipesPair PipesDisc.
Require PipeDisc.
Require Import PipesUline.
Require Import FileState FileDisc FileOutPure FileHooks.
From stdpp Require Import list.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE ALTERNATIVES                                                  *)
(* ===================================================================== *)

(* a file line's alternative, an echo pipeline's, a [cat f] pipeline's,
   or the TERMINAL arm of a [seccomp x] line (seccomp design section 3):
   [US u], with [u] the bytes the round put on the wire after the echo --
   ARBITRARY, since the masked binary keeps the console *)
Inductive ualt :=
  | UR (a : ralt)
  | UPE (a : plalt)
  | UPC (a : plalt)
  | US (u : list (bv 8)).

Global Instance ualt_eq_dec : EqDecision ualt.
Proof using. solve_decision. Defined.

(* THE CODE: the four injective codes interleaved mod 4.  Like
   [plalt_code] it is built, never computed. *)
Definition ualt_code (a : ualt) : nat :=
  match a with
  | UR r => 4 * ralt_enc r
  | UPE x => 4 * plalt_code x + 1
  | UPC x => 4 * plalt_code x + 2
  | US u => 4 * encode_nat u + 3
  end.

Definition ualt_dec (n : nat) : ualt :=
  if decide (n mod 4 = 0) then UR (ralt_dec (n / 4))
  else if decide (n mod 4 = 1) then UPE (plalt_of (n / 4))
  else if decide (n mod 4 = 2) then UPC (plalt_of (n / 4))
  else US (default [] (decode_nat (n / 4))).

Lemma div4 (n : nat) : n = 4 * (n / 4) + n mod 4 /\ n mod 4 < 4.
Proof using. split; [apply Nat.div_mod; lia | apply Nat.mod_upper_bound; lia]. Qed.

Lemma ualt_dec_R (k : nat) : ualt_dec (4 * k) = UR (ralt_dec k).
Proof using.
  unfold ualt_dec. destruct (div4 (4 * k)) as [H1 H2].
  assert (Hq : 4 * k / 4 = k) by lia.
  rewrite decide_True; [| lia]. rewrite Hq. reflexivity.
Qed.

Lemma ualt_dec_E (k : nat) : ualt_dec (4 * k + 1) = UPE (plalt_of k).
Proof using.
  unfold ualt_dec. destruct (div4 (4 * k + 1)) as [H1 H2].
  assert (Hq : (4 * k + 1) / 4 = k) by lia.
  rewrite decide_False; [| lia]. rewrite decide_True; [| lia]. rewrite Hq. reflexivity.
Qed.

Lemma ualt_dec_C (k : nat) : ualt_dec (4 * k + 2) = UPC (plalt_of k).
Proof using.
  unfold ualt_dec. destruct (div4 (4 * k + 2)) as [H1 H2].
  assert (Hq : (4 * k + 2) / 4 = k) by lia.
  rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
  rewrite decide_True; [| lia]. rewrite Hq. reflexivity.
Qed.

Lemma ualt_dec_S (k : nat) : ualt_dec (4 * k + 3) = US (default [] (decode_nat k)).
Proof using.
  unfold ualt_dec. destruct (div4 (4 * k + 3)) as [H1 H2].
  assert (Hq : (4 * k + 3) / 4 = k) by lia.
  rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
  rewrite decide_False; [| lia]. rewrite Hq. reflexivity.
Qed.

Lemma ualt_dec_0 : ualt_dec 0 = UR (ralt_dec 0).
Proof using. exact (ualt_dec_R 0). Qed.

Lemma ualt_dec_code (a : ualt) : ualt_dec (ualt_code a) = a.
Proof using.
  destruct a as [r | x | x | u]; cbn [ualt_code].
  - by rewrite ualt_dec_R, ralt_dec_enc.
  - by rewrite ualt_dec_E, plalt_of_code.
  - by rewrite ualt_dec_C, plalt_of_code.
  - by rewrite ualt_dec_S, decode_encode_nat.
Qed.

Lemma ualt_code_inj (a b : ualt) : ualt_code a = ualt_code b -> a = b.
Proof using. intros H. by rewrite <- (ualt_dec_code a), <- (ualt_dec_code b), H. Qed.

Definition upanic (a : ualt) : bool :=
  match a with UR r => ralt_panic r | UPE x | UPC x => plpanic x | US _ => false end.
(* the seccomp round ends the era's coverage (seccomp design section 2) *)
Definition uterm (a : ualt) : bool :=
  match a with UR _ => false | UPE x | UPC x => plterm x | US _ => true end.

(* the console continuation: the file's, at the round's state, or the
   pipeline's (which names its whole block), or the seccomp round's bytes *)
Definition ucont (s : fstate) (l : uline) (a : ualt) : list (bv 8) :=
  match a with UR r => cont s l r | UPE x | UPC x => plcont x | US u => u end.

(* the step: the file's; a pipeline leaves the files alone, and so does
   the seccomp round -- THE STATE DOES NOT MOVE, which is the design's
   section 1 claim, stated *)
Definition ustep (s : fstate) (l : uline) (a : ualt) : fstate :=
  match a with UR r => fsm s l r | UPE _ | UPC _ | US _ => s end.

(* THE RANGE CONDITION at the round's state.  At a pipeline whose
   producer matches the alternative's: the shell's own three ([plsafe])
   at every state, or an admitted line's run at the content [s] gives
   [f] (which an echo producer never reads, [uok_echo_st]).  Every cross
   case is [False] (amendment B2, and the producer split).  At a [seccomp]
   line: the shell's own three ([FileDisc.ralt_ok]'s arm) and the terminal
   arm at any NONEMPTY [u] -- nonempty because the hooks' writer law
   [lmh_cont_nonnil] reads every admitted continuation as nonempty (the
   pipeline's terminal blocks are nonempty for the same reason), and a
   claim is a prefix of the transcript, so a wire that shows nothing after
   the echo is still one of [US u]'s prefixes.  [US] anywhere else is
   [False].  At a pipeline the one file alternative is [ROom]: the shell
   parses the line in its first child ([runcmd(parsecmd(cmd))]), which may
   die of out-of-memory there and says so. *)
Definition uok (adm : pline' -> bool) (s : fstate) (l : uline) (a : ualt) : Prop :=
  match l with
  | LPipe p n =>
      match a, p with
      | UR r, _ => r = ROom
      | UPE x, PrEcho _ | UPC x, PrCatF _ =>
          plsafe (LPipes p n) x
          \/ (adm (LPipes p n) = true /\ plalt_ok (files_of s) (LPipes p n) x)
      | _, _ => False
      end
  | LSecc _ => match a with UR r => ralt_ok l r | US u => u <> [] | _ => False end
  | _ => match a with UR r => ralt_ok l r | _ => False end
  end.

(* the pipeline alternative a producer's line takes *)
Definition upl (p : producer) (x : plalt) : ualt :=
  match p with PrEcho _ => UPE x | PrCatF _ => UPC x end.

Lemma upl_cont s l p x : ucont s l (upl p x) = plcont x.
Proof using. by destruct p. Qed.
Lemma upl_panic p x : upanic (upl p x) = plpanic x.
Proof using. by destruct p. Qed.
Lemma upl_term p x : uterm (upl p x) = plterm x.
Proof using. by destruct p. Qed.

Lemma uok_upl adm s p n x :
  uok adm s (LPipe p n) (upl p x)
  <-> plsafe (LPipes p n) x
      \/ (adm (LPipes p n) = true /\ plalt_ok (files_of s) (LPipes p n) x).
Proof using. by destruct p. Qed.

(* every alternative a pipeline admits is the out-of-memory death or its
   producer's *)
Lemma uok_pipe adm s p n a :
  uok adm s (LPipe p n) a ->
  a = UR ROom
  \/ exists x, a = upl p x
               /\ (plsafe (LPipes p n) x
                   \/ (adm (LPipes p n) = true /\ plalt_ok (files_of s) (LPipes p n) x)).
Proof using.
  intros H. destruct a as [r | x | x | u], p as [ws | f]; cbn [uok] in H; try contradiction;
    first [left; by subst r | right; exists x; (split; [reflexivity | exact H])].
Qed.

(* ---- AN ECHO PIPELINE READS NO STATE ---- *)

(* a stage that is not [cat f] never consults the content function *)
Lemma stage_out_fc fc fc' L st so :
  stage_out fc L st so -> (forall f, st <> SProd (PrCatF f)) -> stage_out fc' L st so.
Proof using.
  destruct 1 as [st | st | ws Hl | ws D Hl HD | f Hf | f D Hf HD | f | F D HD | D HD
                | w D W HD HW | F D HD];
    intros Hst.
  - apply so_exec.
  - apply so_silent.
  - apply so_echo. exact Hl.
  - apply so_echo_halt; [exact Hl | exact HD].
  - exfalso. exact (Hst f eq_refl).
  - exfalso. exact (Hst f eq_refl).
  - apply so_catf_open.
  - apply so_mid_f. exact HD.
  - apply so_mid_halt. exact HD.
  - apply so_grep_halt; [exact HD | exact HW].
  - apply so_last_f. exact HD.
Qed.

Lemma sfx_run_fc fc fc' L fs w wc ss : sfx_run fc L fs w wc ss -> sfx_run fc' L fs w wc ss.
Proof using.
  induction 1 as [F win wc so Hso Hp | F F' fs win wc | F F' fs win wc so ss Hso Hp Hr IH].
  - apply sr_last; [| exact Hp].
    apply (stage_out_fc fc); [exact Hso | intros f Hf; discriminate Hf].
  - apply sr_pipe_fail.
  - apply sr_node; [| exact Hp | exact IH].
    apply (stage_out_fc fc); [exact Hso | intros f Hf; discriminate Hf].
Qed.

Lemma sfx_term_fc fc fc' L fs w wc W t :
  sfx_term fc L fs w wc W t -> sfx_term fc' L fs w wc W t.
Proof using.
  induction 1 as [F F' fs win wc so Hso | F F' fs win wc so W t Hso Hp Ht IH].
  - apply stt_here. apply (stage_out_fc fc); [exact Hso | intros f Hf; discriminate Hf].
  - apply stt_next; [| exact Hp | exact IH].
    apply (stage_out_fc fc); [exact Hso | intros f Hf; discriminate Hf].
Qed.

Lemma line_run_echo_fc fc fc' ws n ss :
  line_run fc (LPipes (PrEcho ws) n) ss -> line_run fc' (LPipes (PrEcho ws) n) ss.
Proof using.
  intros H. remember (LPipes (PrEcho ws) n) as l eqn:Hl.
  destruct H as [ws' | ws' | ws' | p n' Hn | p n' so ss' Hso Hr]; try discriminate Hl;
    injection Hl as -> ->.
  - apply lr_pipe_fail. exact Hn.
  - apply (lr_node fc' (PrEcho ws) n so ss').
    + apply (stage_out_fc fc); [exact Hso | intros f Hf; discriminate Hf].
    + exact (sfx_run_fc fc fc' _ _ _ _ _ Hr).
Qed.

Lemma line_term_echo_fc fc fc' ws n W t :
  line_term fc (LPipes (PrEcho ws) n) W t -> line_term fc' (LPipes (PrEcho ws) n) W t.
Proof using.
  intros H. remember (LPipes (PrEcho ws) n) as l eqn:Hl.
  destruct H as [p n' so Hn Hso | p n' so W' t' Hso Ht]; injection Hl as -> ->.
  - apply lt_here; [exact Hn |].
    apply (stage_out_fc fc); [exact Hso | intros f Hf; discriminate Hf].
  - apply (lt_next fc' (PrEcho ws) n so W' t').
    + apply (stage_out_fc fc); [exact Hso | intros f Hf; discriminate Hf].
    + exact (sfx_term_fc fc fc' _ _ _ _ _ _ Ht).
Qed.

Lemma plalt_ok_echo_fc fc fc' ws n x :
  plalt_ok fc (LPipes (PrEcho ws) n) x -> plalt_ok fc' (LPipes (PrEcho ws) n) x.
Proof using.
  destruct x as [| b | b]; cbn [plalt_ok]; unfold line_blocks, line_term_blocks.
  - intros _. exact I.
  - intros (ss & Hr & Hm). exists ss. split; [exact (line_run_echo_fc fc fc' ws n ss Hr) | exact Hm].
  - intros [Hne (b' & (W & t & Wm & sp & Hlt & HWm & Hsp & Hm) & Hp)]. split; [exact Hne |].
    exists b'. split; [| exact Hp]. exists W, t, Wm, sp.
    split_and!; [exact (line_term_echo_fc fc fc' ws n W t Hlt) | exact HWm | exact Hsp | exact Hm].
Qed.

(* THE ADMISSION OF AN ECHO PIPELINE IS STATE-INDEPENDENT *)
Lemma uok_echo_st adm s s' ws n a :
  uok adm s (LPipe (PrEcho ws) n) a -> uok adm s' (LPipe (PrEcho ws) n) a.
Proof using.
  intros H. destruct a as [r | x | x | u]; cbn [uok] in H |- *; try contradiction;
    [exact H |].
  destruct H as [Hsafe | [Ha Hb]]; [left; exact Hsafe |].
  right. split; [exact Ha | exact (plalt_ok_echo_fc _ _ ws n x Hb)].
Qed.

(* ===================================================================== *)
(*  2.  THE LINES: the file's parser, then the pipeline's, then the       *)
(*      seccomp line's                                                    *)
(* ===================================================================== *)

Definition uline_of_u (b : list (bv 8)) : uline :=
  match parse_line b with
  | Some l => l
  | None =>
      match pl_parse b with
      | Some (LPipes p n) => LPipe p n
      | _ => match secc_parse b with Some ws => LSecc ws | None => inhabitant end
      end
  end.

(* a body the admission lets through as a pipeline *)
Definition upipe_ok (adm : pline' -> bool) (b : list (bv 8)) : Prop :=
  match pl_parse b with Some (LPipes p n) => adm (LPipes p n) = true | _ => False end.

Global Instance upipe_ok_dec adm b : Decision (upipe_ok adm b).
Proof using. unfold upipe_ok. destruct (pl_parse b) as [[ws | p n] |]; apply _. Defined.

(* THE SECCOMP ADMISSION KNOB (seccomp design section 3): [adm_s] says
   which [seccomp x ..] lines the application admits, as [adm] does for
   pipelines.  A seccomp body is admitted exactly when its words are, so
   while the knob is off ([fun _ => false], [ulmG]) no disciplined input
   holds one -- which is what refutes the [LSecc] arm of every law cased
   on an admitted line. *)
Definition usecc_ok (adm_s : list (list (bv 8)) -> bool) (b : list (bv 8)) : Prop :=
  match secc_parse b with Some ws => adm_s ws = true | None => False end.

Global Instance usecc_ok_dec adm_s b : Decision (usecc_ok adm_s b).
Proof using. unfold usecc_ok. destruct (secc_parse b); apply _. Defined.

Definition ubody_ok (adm : pline' -> bool) (adm_s : list (list (bv 8)) -> bool)
    (b : list (bv 8)) : Prop :=
  fbody_ok b \/ upipe_ok adm b \/ usecc_ok adm_s b.

Global Instance ubody_ok_dec adm adm_s b : Decision (ubody_ok adm adm_s b).
Proof using. unfold ubody_ok. apply _. Defined.

(* the knob at a line: a seccomp line is well formed at the model only
   when admitted ([lml_body_line] ties the two admissions together) *)
Definition usecc_adm (adm_s : list (list (bv 8)) -> bool) (l : uline) : Prop :=
  match l with LSecc ws => adm_s ws = true | _ => True end.

Definition uline_okU (adm_s : list (list (bv 8)) -> bool) (l : uline) : Prop :=
  uline_ok l /\ usecc_adm adm_s l.

Global Instance usecc_adm_dec adm_s l : Decision (usecc_adm adm_s l).
Proof using. destruct l; unfold usecc_adm; apply _. Defined.

Global Instance uline_okU_dec adm_s l : Decision (uline_okU adm_s l).
Proof using. unfold uline_okU. apply _. Defined.

(* the partial line's alphabet: the file lines' ([fbody_byte], which has
   the dot a file name is typed through, cut W4) and the bar *)
Definition ubyte (b : bv 8) : Prop := fbody_byte b \/ b = fd_bar.

Global Instance ubyte_dec b : Decision (ubyte b).
Proof using. unfold ubyte. apply _. Defined.

(* the coverage-ending outputs AT A LINE: at a [seccomp] line EVERY byte
   string (the masked binary prints anything); elsewhere a prefix of an
   admitted pipeline's terminal block at SOME admissible state (terminal
   runs carry no content, so the state is immaterial) *)
Definition umerge_p (adm : pline' -> bool) (u : list (bv 8)) : Prop :=
  exists s, fstate_ok s /\ pl_merge (files_of s) adm u.

Definition umerge (adm : pline' -> bool) (l : uline) (u : list (bv 8)) : Prop :=
  match l with LSecc _ => True | _ => umerge_p adm u end.

(* ===================================================================== *)
(*  3.  THE MODEL AND ITS LAWS                                            *)
(* ===================================================================== *)

Definition ulm (adm : pline' -> bool) (adm_s : list (list (bv 8)) -> bool) : lmodel :=
  MkLM fstate uline uline_of_u ualt ualt_dec upanic ucont ustep (uok adm)
       (ubody_ok adm adm_s) ubyte (uline_okU adm_s) fstate_ok uterm (umerge adm).

(* THE ADMISSION THE UNION APPLICATION INSTANTIATES (grep-pipes.md cut
   G8): every echo pipeline and every [cat f | ..] at the model's file
   name, each filter stage [cat] or [grep w] of one alphanumeric word
   ([filt_ok]).  An echo line alone is the file's [LEcho], so [LEcho']
   is not admitted here. *)
Definition filts_okb (fs : list filt) : bool := forallb (fun F => bool_decide (filt_ok F)) fs.

Lemma filts_okb_true (fs : list filt) : filts_okb fs = true <-> Forall filt_ok fs.
Proof using.
  unfold filts_okb. rewrite forallb_forall, Forall_forall. split.
  - intros H F HF. apply (bool_decide_eq_true_1 _ (H F (proj1 (elem_of_list_In _ _) HF))).
  - intros H F HF. apply bool_decide_eq_true_2. apply H. exact (proj2 (elem_of_list_In _ _) HF).
Qed.

Definition adm_u_g (l : pline') : bool :=
  match l with
  | LEcho' _ => false
  | LPipes (PrEcho _) fs => filts_okb fs
  | LPipes (PrCatF g) fs => bool_decide (uname g) && filts_okb fs
  end.

(* THE SECCOMP KNOB (seccomp design section 3).  OFF admits no seccomp
   line; ON admits every [seccomp x] line with an argument (seccomp lane
   S4: sh's seccomp round is proved, so the union application runs ON) *)
Definition adm_s_off : list (list (bv 8)) -> bool := fun _ => false.
Definition adm_s_on (ws : list (list (bv 8))) : bool := bool_decide (ws <> []).

Definition ulmG : lmodel := ulm adm_u_g adm_s_on.

Lemma adm_u_g_echo (ws : list (list (bv 8))) (fs : list filt) :
  Forall filt_ok fs -> adm_u_g (LPipes (PrEcho ws) fs) = true.
Proof using. intros H. exact (proj2 (filts_okb_true fs) H). Qed.

Lemma adm_u_g_catf (g : list (bv 8)) (fs : list filt) :
  adm_u_g (LPipes (PrCatF g) fs) = true <-> uname g /\ Forall filt_ok fs.
Proof using.
  cbn [adm_u_g]. rewrite andb_true_iff, bool_decide_eq_true, filts_okb_true. reflexivity.
Qed.


(* an admitted pipeline's stages are admissible filters *)
Lemma adm_u_g_fs (p : producer) (fs : list filt) :
  adm_u_g (LPipes p fs) = true -> Forall filt_ok fs.
Proof using.
  destruct p as [ws | g]; [exact (proj1 (filts_okb_true fs)) |].
  intros Ha. exact (proj2 (proj1 (adm_u_g_catf g fs) Ha)).
Qed.

(* ---- the pieces ---- *)

(* the round's content function has a word line's shape *)
Lemma files_of_fc_ok (s : fstate) : fstate_ok s -> fc_ok (files_of s).
Proof using.
  intros Hs g c Hg. apply files_of_some in Hg. pose proof (proj2 (Hs g c Hg)) as Hc.
  split; [exact (fcont_ok_nodollar c Hc) | exact (fcont_ok_nl c Hc)].
Qed.

(* a pipeline's body is not a seccomp body: its first word is [echo] or
   [cat] ([uline_ws_head_secc]) *)
Lemma pl_parse_not_secc b l : pl_parse b = Some l -> secc_parse b = None.
Proof using.
  intros Hq. destruct (pl_parse_some b l Hq) as [Hok Hb].
  unfold secc_parse. rewrite decide_False; [reflexivity |].
  intros (_ & Hh & _).
  rewrite Hb, <- (uline_ws_of_pl_all l Hok) in Hh.
  destruct (uline_ws_head_secc (uline_of_pl l) (uline_ok_of_pl_all l Hok) Hh) as [ws Hws].
  destruct l; discriminate Hws.
Qed.

(* a seccomp body is read as its line *)
Lemma uline_of_u_secc_parse b ws : secc_parse b = Some ws -> uline_of_u b = LSecc ws.
Proof using.
  intros Hs. unfold uline_of_u.
  destruct (parse_line b) as [l |] eqn:Hp.
  { exfalso. rewrite (secc_parse_fbody b (ex_intro _ l Hp)) in Hs. discriminate Hs. }
  destruct (pl_parse b) as [[ws' | p n] |] eqn:Hq;
    [rewrite Hs; reflexivity | | rewrite Hs; reflexivity].
  exfalso. rewrite (pl_parse_not_secc b _ Hq) in Hs. discriminate Hs.
Qed.

Lemma uline_of_u_secc ws : secc_ok ws -> uline_of_u (line_body (LSecc ws)) = LSecc ws.
Proof using. intros Hok. exact (uline_of_u_secc_parse _ ws (secc_parse_body ws Hok)). Qed.

Lemma uline_of_u_ok (adm : pline' -> bool) (adm_s : list (list (bv 8)) -> bool)
    (b : list (bv 8)) :
  ubody_ok adm adm_s b -> uline_okU adm_s (uline_of_u b).
Proof using.
  intros Hb. unfold uline_of_u. destruct (parse_line b) as [l |] eqn:Hp.
  { split; [exact (parse_line_ok b l Hp) |].
    destruct l as [| | | | ws]; try exact I. exfalso. exact (parse_line_not_secc b ws Hp). }
  destruct Hb as [[l Hl] | [Hpipe | Hsecc]]; [rewrite Hp in Hl; discriminate Hl | |].
  - revert Hpipe. unfold upipe_ok.
    destruct (pl_parse b) as [[ws | p n] |] eqn:Hq; intros Hpipe; try contradiction.
    destruct (pl_parse_some b _ Hq) as [Hok _].
    split; [exact (uline_ok_of_pl_all (LPipes p n) Hok) | exact I].
  - revert Hsecc. unfold usecc_ok. destruct (secc_parse b) as [ws |] eqn:Hs; [| intros []].
    intros Ha. destruct (pl_parse b) as [[ws' | p n] |] eqn:Hq.
    + split; [exact (proj1 (secc_parse_some b ws Hs)) | exact Ha].
    + exfalso. rewrite (pl_parse_not_secc b _ Hq) in Hs. discriminate Hs.
    + split; [exact (proj1 (secc_parse_some b ws Hs)) | exact Ha].
Qed.

(* WITH THE KNOB OFF no admitted body is a seccomp line *)
Lemma uline_of_u_off (adm : pline' -> bool) (b : list (bv 8)) :
  ubody_ok adm adm_s_off b -> forall ws, uline_of_u b <> LSecc ws.
Proof using.
  intros Hb ws Hws. pose proof (uline_of_u_ok adm adm_s_off b Hb) as [_ Ha].
  rewrite Hws in Ha. discriminate Ha.
Qed.

(* a run proves its line has a stage *)
Lemma sfx_run_pos fc L fs w wc ss : sfx_run fc L fs w wc ss -> fs <> [].
Proof using. destruct 1; discriminate. Qed.

Lemma line_blocks_pos fc p fs b : line_blocks fc (LPipes p fs) b -> fs <> [].
Proof using.
  intros (ss & Hr & _). remember (LPipes p fs) as l eqn:Hl.
  destruct Hr as [ws | ws | ws | p' n' Hn | p' n' so ss' Hso Hsr]; try discriminate Hl;
    injection Hl as -> ->; [exact Hn | exact (sfx_run_pos _ _ _ _ _ _ Hsr)].
Qed.

Lemma sfx_term_pos fc L fs w wc W t : sfx_term fc L fs w wc W t -> fs <> [].
Proof using. destruct 1; discriminate. Qed.

Lemma line_term_pos fc p fs W t : line_term fc (LPipes p fs) W t -> fs <> [].
Proof using.
  intros H. remember (LPipes p fs) as l eqn:Hl.
  destruct H as [p' n' so Hn Hso | p' n' so W' t' Hso Hst];
    injection Hl as -> ->; [exact Hn | exact (sfx_term_pos _ _ _ _ _ _ _ Hst)].
Qed.

(* A TERMINAL ALTERNATIVE AT EVERY CONTENT: the fork of the node below
   the producer fails after the producer was forked, and the producer's
   exec fails -- [lt_here] and [so_exec], whatever [f] holds *)
Lemma plterm_fork_ok fc p n :
  n <> [] -> plalt_ok fc (LPipes p n) (PLTerm dg_fork_b).
Proof using.
  intros Hn. split.
  { intros H. apply (f_equal length) in H. unfold dg_fork_b in H.
    rewrite wl_line_length in H. cbn [length] in H. lia. }
  exists (dg_fork_b ++ u_prompt). split; [| by exists u_prompt].
  exists [dg_fork_b], (st_dg_exec (SProd p)), dg_fork_b, []. split_and!.
  - exact (lt_here fc p n (MkSO (st_dg_exec (SProd p)) (st_rd_dead (SProd p))
                             (st_wr_dead (SProd p))) Hn (so_exec _ _ _)).
  - apply merge_all_one. reflexivity.
  - apply prefix_nil.
  - exact (merge_all_nils (dg_fork_b ++ u_prompt) 1).
Qed.


(* the seccomp body's bytes and length, as a line's *)
Lemma secc_body_bytes b ws : secc_parse b = Some ws -> Forall fbody_byte b.
Proof using.
  intros Hs. destruct (secc_parse_some b ws Hs) as [Hok ->]. cbn [line_body].
  eapply Forall_impl; [exact (wl_body_bytes_fn _ (secc_ok_wf ws Hok)) |].
  exact fbody_byte_of_fn.
Qed.

Lemma secc_body_short b ws : secc_parse b = Some ws -> S (length b) < line_max.
Proof using.
  intros Hs. destruct (secc_parse_some b ws Hs) as [(_ & _ & _ & Hl) ->]. cbn [line_body].
  rewrite wl_line_length in Hl. lia.
Qed.

Section laws.
  Context (adm : pline' -> bool) (adm_s : list (list (bv 8)) -> bool).

  Lemma ulm_st_step s l a :
    fstate_ok s -> uline_ok l -> uok adm s l a -> fstate_ok (ustep s l a).
  Proof using.
    intros Hs Hl Ha. destruct a as [r | x | x | u]; cbn [ustep]; [| exact Hs | exact Hs | exact Hs].
    destruct l as [ws | ws N | N | p n | ws]; cbn [uok] in Ha;
      [exact (fstate_ok_fsm s _ r Hs Hl Ha) | exact (fstate_ok_fsm s _ r Hs Hl Ha)
      | exact (fstate_ok_fsm s _ r Hs Hl Ha) | exact Hs
      | exact (fstate_ok_fsm s _ r Hs Hl Ha)].
  Qed.

  Lemma ulm_cont_panic s l a : upanic a = true -> ucont s l a = alt_panic.
  Proof using.
    destruct a as [r | [| b | b] | [| b | b] | u]; cbn [upanic ucont]; intros H;
      [exact (cont_panic s l r H) | reflexivity | discriminate H | discriminate H
      | reflexivity | discriminate H | discriminate H | discriminate H].
  Qed.

  Lemma ulm_term_nopanic a : uterm a = true -> upanic a = false.
  Proof using.
    destruct a as [r | [| b | b] | [| b | b] | u]; cbn; intros H; first [discriminate H | reflexivity].
  Qed.

  Lemma ulm_term_merge s l a :
    fstate_ok s -> uok adm s l a -> uterm a = true -> umerge adm l (ucont s l a).
  Proof using.
    intros Hs Hok Ht. destruct l as [ws | ws N | N | p n | ws].
    1-3: destruct a as [r | x | x | u]; cbn [uok uterm] in Hok, Ht;
         first [discriminate Ht | contradiction].
    2: exact I.
    destruct (uok_pipe _ _ _ _ _ Hok) as [-> | (x & -> & Hx)]; [discriminate Ht |].
    rewrite upl_term in Ht. rewrite upl_cont.
    destruct x as [| b | b]; try discriminate Ht.
    destruct Hx as [Hsafe | [Ha Hb]].
    { exfalso. destruct Hsafe as [H | [H | H]]; discriminate H. }
    cbn [umerge]. exists s. split; [exact Hs |]. exists (LPipes p n), b.
    split_and!; [exact Ha | exact Hb |]. reflexivity.
  Qed.

  Lemma ulm_merge_prefix l u' u : u' `prefix_of` u -> umerge adm l u -> umerge adm l u'.
  Proof using.
    intros Hp Hm. destruct l as [ws | ws N | N | p n | ws]; [| | | | exact I].
    all: cbn [umerge] in Hm |- *; unfold umerge_p in Hm |- *.
    all: destruct Hm as (s & Hs & l & b & Ha & Hok & Hu); exists s; split; [exact Hs |].
    all: exists l, b; split_and!; [exact Ha | exact Hok | etrans; [exact Hp | exact Hu]].
  Qed.

  Lemma ulm_cont_shape s l a :
    fstate_ok s -> uline_okU adm_s l -> uok adm s l a -> upanic a = false -> uterm a = false ->
    exists u, ucont s l a = u ++ u_prompt
              /\ Forall nodollar u
              /\ (forall Y ps W,
                    Forall (fun x => x < length pro_alts) ps ->
                    lm_below_panic u Y ps W -> u = alt_panic).
  Proof using.
    intros Hs [Hl _] Hok Hp Ht. destruct l as [ws | ws N | N | p n | ws].
    (* a file alternative at a file line (or the shell's own three at a
       seccomp line): the file model's law *)
    1-3: destruct a as [r | x | x | u]; cbn [uok] in Hok; try contradiction;
         exact (lml_cont_shape file_lm_laws s _ r Hs Hl Hok Hp eq_refl).
    2: { destruct a as [r | x | x | u]; cbn [uok] in Hok; try contradiction;
           [exact (lml_cont_shape file_lm_laws s _ r Hs Hl Hok Hp eq_refl) | discriminate Ht]. }
    (* the out-of-memory death at a pipeline: the file model's law at its
       dead arm, which admits it; a pipeline alternative: the pipeline
       model's law at the round's content function *)
    destruct (uok_pipe _ _ _ _ _ Hok) as [-> | (x & -> & Hx)].
    { exact (lml_cont_shape file_lm_laws s _ ROom Hs Hl I Hp eq_refl). }
    rewrite upl_panic in Hp. rewrite upl_term in Ht. rewrite upl_cont.
    exact (lml_cont_shape (pipes_lm_laws_fc (files_of s) adm (files_of_fc_ok s Hs))
             tt (LPipes p n) x I (pl_ok_of_uline p n Hl) Hx Hp Ht).
  Qed.

  (* a terminal alternative at one state has one at every state: the
     producer's exec failure below a failed fork ([plterm_fork_ok]); at a
     seccomp line the terminal arm at one byte, whatever the state *)
  Lemma ulm_term_st s l c :
    uok adm s l c -> uterm c = true ->
    forall s', exists c', uok adm s' l c' /\ uterm c' = true.
  Proof using.
    intros Hok Ht s'. destruct l as [ws | ws N | N | p n | ws].
    1-3: destruct c as [r | x | x | u]; cbn [uok uterm] in Hok, Ht;
         first [discriminate Ht | contradiction].
    2: { exists (US [wl_nl]). split; [cbn [uok]; discriminate | reflexivity]. }
    destruct (uok_pipe _ _ _ _ _ Hok) as [-> | (x & -> & Hx)]; [discriminate Ht |].
    rewrite upl_term in Ht. destruct x as [| b | b]; try discriminate Ht.
    destruct Hx as [Hsafe | [Ha (_ & b' & (W & t & Wm & sp & Hlt & _) & _)]].
    { exfalso. destruct Hsafe as [H | [H | H]]; discriminate H. }
    exists (upl p (PLTerm dg_fork_b)). split; [| rewrite upl_term; reflexivity].
    apply uok_upl. right. split; [exact Ha |].
    exact (plterm_fork_ok _ p n (line_term_pos _ _ _ _ _ Hlt)).
  Qed.

  Theorem ulm_laws : lm_laws (ulm adm adm_s).
  Proof using.
    constructor; cbn [ulm lm_ok lm_cont lm_merge lm_panic lm_term lm_line_ok lm_body_ok
                      lm_of lm_st_ok lm_step].
    - exact (uline_of_u_ok adm adm_s).
    - intros s l a Hs Hl Ha. exact (ulm_st_step s l a Hs (proj1 Hl) Ha).
    - exact ulm_cont_panic.
    - exact ulm_term_nopanic.
    - exact ulm_term_merge.
    - exact ulm_merge_prefix.
    - exact ulm_cont_shape.
    - exact ulm_term_st.
  Qed.

  Theorem ulm_byte_laws : lm_byte_laws (ulm adm adm_s).
  Proof using.
    constructor; cbn [ulm lm_body_ok lm_body_byte lm_panic lm_dec].
    - intros b [Hb | [Hb | Hb]].
      + eapply Forall_impl; [exact (fbody_ok_bytes b Hb) |]. intros x Hx. by left.
      + revert Hb. unfold upipe_ok.
        destruct (pl_parse b) as [[ws | p n] |] eqn:Hq; intros Hb; try contradiction.
        destruct (pl_parse_some b _ Hq) as [Hok ->].
        eapply Forall_impl; [exact (pl_body_bytes _ Hok) |].
        intros x [[Hx | Hx] | Hx]; [left; left; exact Hx | right; exact Hx | left; right; right; exact Hx].
      + revert Hb. unfold usecc_ok. destruct (secc_parse b) as [ws |] eqn:Hs; [| intros []].
        intros _. eapply Forall_impl; [exact (secc_body_bytes b ws Hs) |]. intros x Hx. by left.
    - intros b [Hb | [Hb | Hb]]; [exact (fbody_ok_short b Hb) | |].
      + revert Hb. unfold upipe_ok.
        destruct (pl_parse b) as [[ws | p n] |] eqn:Hq; intros Hb; try contradiction.
        destruct (pl_parse_some b _ Hq) as [Hok ->]. exact (pl_body_short _ Hok).
      + revert Hb. unfold usecc_ok. destruct (secc_parse b) as [ws |] eqn:Hs; [| intros []].
        intros _. exact (secc_body_short b ws Hs).
    - intros b [Hb | ->].
      + exact (lmb_byte_printable file_lm_byte_laws b Hb).
      + assert (Hbar : bv_unsigned fd_bar = 124%Z) by (vm_compute; reflexivity).
        rewrite Hbar. lia.
    - rewrite ualt_dec_0. exact (lmb_dec0_nopanic file_lm_byte_laws).
  Qed.
End laws.

Corollary ulmG_laws : lm_laws ulmG.
Proof using. exact (ulm_laws adm_u_g adm_s_on). Qed.

(* ===================================================================== *)
(*  4.  THE HOOKS                                                         *)
(*                                                                        *)
(*  [lmh_free] is a function of the ALTERNATIVE alone and [lmh_free_ok]   *)
(*  quantifies over every line.  At [UR] the file's [fstate_free] is free *)
(*  (the file's range condition reads no state).  At [UPE] every non-     *)
(*  terminal alternative is free: an echo pipeline's admission reads no   *)
(*  state ([uok_echo_st]), and its continuation names its whole block --  *)
(*  so the exec alternative [exec echo failed] is free there.  At [UPC]   *)
(*  only the genuinely state-free ones are: the panic, the silent round   *)
(*  and [exec cat failed] -- the [cat f] producer's exec failure, one of *)
(*  the shell's own three ([plsafe]) at every content; any other [PLRun]  *)
(*  block is read at the round's content, and a [PLTerm] is never free.   *)
(* ===================================================================== *)

Definition ufree (a : ualt) : bool :=
  match a with
  | UR r => fstate_free r
  | UPE x => negb (plterm x)
  | UPC PLPanic => true
  | UPC (PLRun b) => bool_decide (b = [] \/ b = PipeDisc.dg_execR)
  | UPC (PLTerm _) => false
  (* the seccomp round is terminal, and a terminal arm is never free *)
  | US _ => false
  end.

Section hooks.
  Context (adm : pline' -> bool).

  Lemma ufree_cont s s' l a : ufree a = true -> ucont s l a = ucont s' l a.
  Proof using.
    destruct a as [r | x | x | u]; cbn [ufree ucont]; [exact (cont_state_free s s' l r) | | | discriminate];
      intros _; reflexivity.
  Qed.

  Lemma ufree_term a : ufree a = true -> uterm a = false.
  Proof using. destruct a as [r | [| b | b] | [| b | b] | u]; cbn; done. Qed.

  (* THE STATE-INDEPENDENCE of the free alternatives *)
  Lemma ufree_ok s s' l a : ufree a = true -> uok adm s l a -> uok adm s' l a.
  Proof using.
    intros Hfr Hok. destruct l as [ws | ws N | N | [ws | f] n | ws].
    1-3: destruct a as [r | x | x | u]; cbn [uok] in Hok |- *; first [exact Hok | contradiction].
    3: destruct a as [r | x | x | u]; cbn [uok] in Hok |- *;
         first [exact Hok | contradiction | discriminate Hfr].
    - (* an echo pipeline: its admission reads no state *)
      exact (uok_echo_st adm s s' ws n a Hok).
    - (* a [cat f] pipeline: only the state-free three *)
      destruct a as [r | x | x | u]; cbn [uok] in Hok |- *; try contradiction;
        [exact Hok |].
      destruct Hok as [Hsafe | [Ha Hb]]; [left; exact Hsafe |].
      destruct x as [| b | b]; cbn [ufree] in Hfr; [left; left; reflexivity | | discriminate Hfr].
      (* [exec cat failed] is the [cat f] producer's own exec diagnostic,
         one of the shell's three *)
      apply bool_decide_eq_true in Hfr as [-> | ->]; [left; right; left; reflexivity |].
      left. right. right. reflexivity.
  Qed.

  (* the shell's own three, per line: the file's at a file line (and at a
     seccomp line, [FileHooks]'s arm), the pipeline's ([plsafe]) at a
     pipeline, at its producer's constructor *)
  Definition upan (l : uline) : nat :=
    match l with LPipe p _ => ualt_code (upl p PLPanic) | _ => 4 * fpan_of l end.
  Definition uexf (l : uline) : nat :=
    match l with
    | LPipe p n => ualt_code (upl p (PLRun (pl_exfb (LPipes p n))))
    | _ => 4 * fexf_of l
    end.
  Definition uexfb (l : uline) : list (bv 8) :=
    match l with LPipe p n => pl_exfb (LPipes p n) ++ u_prompt | _ => fexfb l end.
  (* the silent round, where the model has one: a pipeline's [PLRun []]
     (a pipeline that printed nothing, one of [plsafe]'s three), and the
     file model's at the blank line's [LEcho []] *)
  Definition unoc (l : uline) : option nat :=
    match l with
    | LPipe p _ => Some (ualt_code (upl p (PLRun [])))
    | _ => (fun c => 4 * c) <$> fnoc_of l
    end.
  (* ...and the out-of-memory death, admitted at EVERY line: every line
     sh reads but the blank one is parsed in a child *)
  Definition uoom : nat := ualt_code (UR ROom).

  Lemma upan_ok s l : uok adm s l (ualt_dec (upan l)).
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; cbn [upan];
      try (rewrite ualt_dec_R; exact (fpan_of_ok _)).
    rewrite ualt_dec_code. apply uok_upl. left. left. reflexivity.
  Qed.

  Lemma upan_free l : ufree (ualt_dec (upan l)) = true.
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; cbn [upan];
      try (rewrite ualt_dec_R; exact (fpan_of_free _)).
    rewrite ualt_dec_code. by destruct p.
  Qed.

  Lemma upan_panic l : upanic (ualt_dec (upan l)) = true.
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; cbn [upan];
      try (rewrite ualt_dec_R; exact (fpan_of_panic _)).
    rewrite ualt_dec_code, upl_panic. reflexivity.
  Qed.

  Lemma uexf_ok s l : uok adm s l (ualt_dec (uexf l)).
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; cbn [uexf];
      try (rewrite ualt_dec_R; exact (fexf_of_ok _)).
    rewrite ualt_dec_code. apply uok_upl. left. right. right. reflexivity.
  Qed.

  (* THE EXEC ALTERNATIVE IS FREE AT EVERY LINE: the file's at a file
     line, [exec echo failed] at an echo pipeline (whose admission reads
     no state), [exec cat failed] at a [cat f] pipeline, [exec seccomp
     failed] at a seccomp line *)
  Lemma uexf_free l : ufree (ualt_dec (uexf l)) = true.
  Proof using.
    destruct l as [ws | ws N | N | [ws | f] n | ws]; cbn [uexf];
      try (rewrite ualt_dec_R; exact (fexf_of_free _));
      rewrite ualt_dec_code; cbn [upl ufree pl_exfb st_dg_exec]; [reflexivity |].
    apply bool_decide_eq_true. by right.
  Qed.

  Lemma uexf_nopanic l : upanic (ualt_dec (uexf l)) = false.
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; cbn [uexf];
      try (rewrite ualt_dec_R; exact (fexf_of_nopanic _)).
    rewrite ualt_dec_code, upl_panic. reflexivity.
  Qed.

  Lemma uexf_cont s l : ucont s l (ualt_dec (uexf l)) = uexfb l.
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; cbn [uexf uexfb];
      try (rewrite ualt_dec_R; exact (cont_fexf _ _)).
    rewrite ualt_dec_code, upl_cont. reflexivity.
  Qed.

  (* a file line's silent round is the file model's, coded *)
  Lemma unoc_file l c :
    (forall p n, l <> LPipe p n) -> unoc l = Some c ->
    exists k, fnoc_of l = Some k /\ c = 4 * k.
  Proof using.
    intros Hl Hc. destruct l as [ws | ws N | N | p n | ws];
      [| | | exfalso; exact (Hl p n eq_refl) |];
      cbn [unoc] in Hc; destruct (fnoc_of _) as [k |] eqn:Hk; cbn in Hc;
      first [discriminate Hc | injection Hc as <-; by exists k].
  Qed.

  Lemma unoc_ok s l c : unoc l = Some c -> uok adm s l (ualt_dec c).
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; intros Hc.
    4: { cbn [unoc] in Hc. injection Hc as <-.
         rewrite ualt_dec_code. apply uok_upl. left. right. left. reflexivity. }
    all: match type of Hc with unoc ?l = _ =>
           destruct (unoc_file l c ltac:(intros ? ? ?; discriminate) Hc) as (k & Hk & ->) end;
         rewrite ualt_dec_R; exact (fnoc_of_ok _ k Hk).
  Qed.

  Lemma unoc_free l c : unoc l = Some c -> ufree (ualt_dec c) = true.
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; intros Hc.
    4: { cbn [unoc] in Hc. injection Hc as <-. rewrite ualt_dec_code.
         destruct p; cbn [upl ufree]; [reflexivity | apply bool_decide_eq_true; by left]. }
    all: match type of Hc with unoc ?l = _ =>
           destruct (unoc_file l c ltac:(intros ? ? ?; discriminate) Hc) as (k & Hk & ->) end;
         rewrite ualt_dec_R; exact (fnoc_of_free _ k Hk).
  Qed.

  Lemma unoc_nopanic l c : unoc l = Some c -> upanic (ualt_dec c) = false.
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; intros Hc.
    4: { cbn [unoc] in Hc. injection Hc as <-. rewrite ualt_dec_code, upl_panic. reflexivity. }
    all: match type of Hc with unoc ?l = _ =>
           destruct (unoc_file l c ltac:(intros ? ? ?; discriminate) Hc) as (k & Hk & ->) end;
         rewrite ualt_dec_R; exact (fnoc_of_nopanic _ k Hk).
  Qed.

  Lemma unoc_cont s l c : unoc l = Some c -> ucont s l (ualt_dec c) = u_prompt.
  Proof using.
    destruct l as [ws | ws N | N | p n | ws]; intros Hc.
    4: { cbn [unoc] in Hc. injection Hc as <-. rewrite ualt_dec_code, upl_cont. reflexivity. }
    all: match type of Hc with unoc ?l = _ =>
           destruct (unoc_file l c ltac:(intros ? ? ?; discriminate) Hc) as (k & Hk & ->) end;
         rewrite ualt_dec_R; exact (cont_fnoc _ _ k Hk).
  Qed.

  (* THE OUT-OF-MEMORY DEATH: admissible at every line and state, free,
     not a panic, never coverage-ending, and it moves nothing *)
  Lemma uoom_dec : ualt_dec uoom = UR ROom.
  Proof using. exact (ualt_dec_code (UR ROom)). Qed.

  Lemma uoom_ok s l : uok adm s l (ualt_dec uoom).
  Proof using.
    rewrite uoom_dec. destruct l as [ws | ws N | N | [ws | f] n | ws]; cbn [uok ralt_ok];
      first [exact I | reflexivity].
  Qed.

  Lemma uoom_free : ufree (ualt_dec uoom) = true.
  Proof using. by rewrite uoom_dec. Qed.

  Lemma uoom_nopanic : upanic (ualt_dec uoom) = false.
  Proof using. by rewrite uoom_dec. Qed.

  Lemma uoom_term : uterm (ualt_dec uoom) = false.
  Proof using. by rewrite uoom_dec. Qed.

  Lemma uoom_cont s l : ucont s l (ualt_dec uoom) = alt_oom.
  Proof using. by rewrite uoom_dec. Qed.

  Lemma uoom_step s l : ustep s l (ualt_dec uoom) = s.
  Proof using. rewrite uoom_dec. by destruct l. Qed.

  Lemma ucont_prompt s l a :
    uok adm s l a -> upanic a = false -> uterm a = false ->
    exists u, ucont s l a = u ++ u_prompt.
  Proof using.
    intros Hok Hp Ht. destruct l as [ws | ws N | N | p n | ws].
    1-3: destruct a as [r | x | x | u]; cbn [uok] in Hok; try contradiction;
         exact (cont_prompt s _ r Hok Hp).
    2: { destruct a as [r | x | x | u]; cbn [uok] in Hok; try contradiction;
           [exact (cont_prompt s _ r Hok Hp) | discriminate Ht]. }
    destruct (uok_pipe _ _ _ _ _ Hok) as [-> | (x & -> & _)].
    { exact (cont_prompt s (LPipe p n) ROom I Hp). }
    rewrite upl_panic in Hp. rewrite upl_term in Ht. rewrite upl_cont.
    destruct x as [| b | b]; try discriminate Hp; try discriminate Ht.
    exists b. reflexivity.
  Qed.

  Lemma ucont_nonnil s l a : uok adm s l a \/ a = ualt_dec 0 -> ucont s l a <> [].
  Proof using.
    intros Ha. destruct a as [r | x | x | u].
    { apply (cont_nonnil_dec s l r). destruct Ha as [Hok | Hq].
      - left. destruct l as [ws | ws N | N | p n | ws]; cbn [uok] in Hok;
          [exact Hok | exact Hok | exact Hok | subst r; exact I | exact Hok].
      - right. rewrite ualt_dec_0 in Hq. injection Hq as ->. reflexivity. }
    (* the seccomp round: its bytes are nonempty by the range condition *)
    3: { destruct Ha as [Hok | Hq]; [| rewrite ualt_dec_0 in Hq; discriminate Hq].
         destruct l as [ws | ws N | N | p n | ws]; cbn [uok] in Hok; try contradiction.
         exact Hok. }
    (* a pipeline alternative: the panic line and a block before the
       prompt are never empty, and a terminal one is nonempty by the
       range condition (it is not the out-of-range decode) *)
    all: destruct Ha as [Hok | Hq]; [| rewrite ualt_dec_0 in Hq; discriminate Hq].
    all: destruct l as [ws | ws N | N | p n | ws]; try (cbn [uok] in Hok; contradiction).
    all: destruct (uok_pipe _ _ _ _ _ Hok) as [Hx' | (x' & Hx' & Hx)]; [discriminate Hx' |].
    all: destruct p; cbn [upl] in Hx'; try discriminate Hx'; injection Hx' as <-.
    all: cbn [ucont]; destruct x as [| b | b]; cbn [plcont].
    all: first
      [ intros Hq; apply (f_equal length) in Hq; rewrite lb_panic_len in Hq; discriminate Hq
      | intros Hq; apply (f_equal length) in Hq; rewrite length_app, ll_prompt_len in Hq;
        cbn [length] in Hq; lia
      | destruct Hx as [Hsafe | [_ [Hne _]]]; [| exact Hne];
        exfalso; destruct Hsafe as [H | [H | H]]; discriminate H ].
  Qed.
End hooks.
