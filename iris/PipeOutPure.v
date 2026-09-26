(* PipeOutPure.v -- THE PIPELINE APPLICATION'S STAGE MACHINE, PURE.

   Design of record: claude-notes/design/app-pipe.md section 4.1, lane
   PIPE-STAGE, deliverable 1.  This file is [EchoOutPure.v]'s twin at
   [PipeDisc.sessp] -- the same stage machine over the pipeline session --
   and it is SIMPLER than upstream's [FileOutPure.v], because a pipe dies
   with its era: there is NO per-era extra state, no boot value, no typed
   witness, and nothing to thread.  Where [FileOutPure] carries [fo_f0]
   through every block, this file carries nothing.

   WHAT CHANGES FROM [EchoOutPure], AND WHAT DOES NOT.

   - [pending_at_p ps cs I] and [D_p ps cs E] are [EchoOutPure.pending_at]
     and [D] at [PipeDisc.alt_cont_p]; the append laws, F1 and F2 are that
     file's, lemma for lemma.
   - the range condition that was [Forall (fun c => c < 4) cs] is
     [alts_pre_p I cs]: every entry the choice list HAS is an alternative
     the LINE AT THAT INDEX admits.  It is POINTWISE and not
     [PipeDisc.alts_ok_p], because the list runs one short at a block
     boundary (a program files its alternative at the block's FIRST byte,
     which is after the echo that completed the line).  [alts_pad_p] fills
     it out, which is what lets the determinacy theorem -- stated at a FULL
     resolution -- be applied to a stage standing at a boundary.
   - [EchoOutPure]'s [cs_ok] HAS NO TWIN, for upstream's reason exactly:
     out of range [!!!] reads [0], which decodes to [PipeDisc.PEcho 0], and
     [palt_ok (LPipe ws) (PEcho 0)] is FALSE (after PIPE-MODEL-2's ruling
     only [PEcho 3] joins a pipeline line's alternatives).  So no total
     condition on [cs] can replace it and the padding is the honest fix --
     the same route [FileOutPure] took at [ralt_ok].
   - the prologue counter is [PipeDisc.pro_idx_p] (it counts [palt_panic],
     i.e. [PEcho 3], at EITHER line shape) and the side condition is
     [pro_ok_p] / [pro_pin_p].
   - F3 is [EchoOutPure.read_window_prefix] VERBATIM: it is about the log
     and the echoed entries and names no discipline.

   DETERMINACY NEEDS NO SECOND WITNESS.  [FileDisc.sessf_prefix_det2]
   exists only because a file's transcript reads the era's BOOT STATE, and
   the discipline's witness for it and the claim's own have no reason to be
   equal.  A pipeline round reads no state at all, so
   [PipeDisc.sessp_prefix_det] IS the lemma the stage spends;
   [sessp_prefix_det2] below is its restatement under the brief's name and
   is proved by [exact].  (Reported as such.)

   THE DISCIPLINE'S CLOSURE LAWS are here too ([disc_p_out], [disc_p_in],
   [disc_p_power], [disc_p_other], [disc_p_prefix]): [PipeDisc] landed
   [disc_input_p]'s full set and, of [disc_p]'s, only [disc_p_nil] and
   [disc_p_seg]; the ledger's three steps are stated at exactly these. *)
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
Require Import PipeDisc.
Require Import LineModelLinks.
(* as in EchoDisc / EchoOutPure: a pure file does not inherit ssreflect's
   [rewrite] from the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  SMALL LIST FACTS [EchoOut.v] ALSO STATES                           *)
(*                                                                        *)
(*  They are pure and sit ABOVE this file (in [EchoOut.v]), which this     *)
(*  file must not import: the claim's cone would drag [WpUart] into a      *)
(*  logic-free file.  Copied with a [pop_] prefix, exactly as             *)
(*  [FileOutPure] copies them with [fop_].                                 *)
(* ====================================================================== *)

Lemma pop_app_nonnil_r {A} (u v : list A) : v <> [] -> u ++ v <> [].
Proof using.
  intros Hv Hq. apply Hv. by destruct (app_eq_nil u v Hq) as [_ Hb].
Qed.

Lemma pop_removelast_take {A} (l : list A) :
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

Lemma pop_prefix_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> removelast l `prefix_of` removelast l'.
Proof using.
  intros Hp. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Ht : take (length l - 1)%nat l = take (length l - 1)%nat l').
  { destruct Hp as [z ->].
    rewrite (take_app_le l z (length l - 1)%nat); [done | lia]. }
  rewrite !pop_removelast_take Ht. apply prefix_take_le. lia.
Qed.

Lemma pop_prefix_of_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> l <> l' -> l `prefix_of` removelast l'.
Proof using.
  intros Hp Hne. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Hlt : (length l < length l')%nat).
  { destruct (decide (length l = length l')) as [He | He]; [| lia].
    exfalso. exact (Hne (prefix_length_eq _ _ Hp ltac:(lia))). }
  assert (Hl : l = take (length l) l').
  { destruct Hp as [z ->]. by rewrite take_app_length. }
  rewrite pop_removelast_take {1}Hl. apply prefix_take_le. lia.
Qed.

(* ====================================================================== *)
(*  2.  THE STAGE MACHINE: [pending_at_p] AND [D_p]                        *)
(* ====================================================================== *)

Definition pending_at_p (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then pro_of ps
  else if decide (rest_of I = [])
       then alt_cont_p ps cs (bodies_of I) (nlines I - 1) else [].

(* THE TRANSCRIPT DUE AFTER E's LAST ECHO.  [EchoOutPure.D_from]'s twin --
   structural on [E] from the LEFT with the input read so far as the
   accumulator, for the same reason ([cbn] reduces it on every [x :: E']). *)
Fixpoint D_from_p (ps cs : list nat) (pre : list (bv 8))
    (E : list (list mobs * bv 8)) : list (bv 8) :=
  match E with
  | [] => []
  | x :: E' => pending_at_p ps cs pre ++ [echo_of x.2]
               ++ D_from_p ps cs (pre ++ [x.2]) E'
  end.

Definition D_p (ps cs : list nat) (E : list (list mobs * bv 8))
  : list (bv 8) := D_from_p ps cs [] E.

(* ====================================================================== *)
(*  3.  WHAT THE CLAIM SAYS ABOUT [E]                                      *)
(* ====================================================================== *)

(* E's INDEX LAW is [EchoOutPure.E_index] verbatim (it names no
   discipline); its CONTENT LAW is D3 for the pipeline application. *)
Definition E_disc_p (E : list (list mobs * bv 8)) : Prop :=
  disc_input_p (snd <$> E).


(* ====================================================================== *)
(*  6.  THE CHOICE LIST: A POINTWISE RANGE CONDITION, AND ITS PADDING      *)
(* ====================================================================== *)

Definition alts_pre_p (I : list (bv 8)) (cs : list nat) : Prop :=
  forall (i : nat) (c : nat),
    cs !! i = Some c ->
    (i < nlines I)%nat
    /\ palt_ok (pline_of (bodies_of I !!! i)) (palt_of c).

(* NO ALTERNATIVE PRINTS NOTHING.  Every constant one ends in the prompt,
   [PRan]'s content is closed by it, and a [PEcho k] is nonempty for
   [k < 4] -- which covers both an alternative a line ADMITS (at either
   shape, [PEcho 3] included) and the out-of-range reading. *)
Lemma pcont_nonnil (l : pline) (a : palt) :
  palt_ok l a \/ a = PEcho 0%nat -> pcont l a <> [].
Proof using.
  intro Ha.
  assert (Hpr : u_prompt <> []).
  { pose proof u_prompt_pos as Hup.
    destruct u_prompt as [| z zs]; [cbn [length] in Hup; lia | done]. }
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont.
  - assert (Hk : (k < 4)%nat).
    { destruct Ha as [Ha | Heq]; [| injection Heq as <-; lia].
      destruct l as [ws | ws]; [exact Ha | rewrite /palt_ok in Ha; lia]. }
    exact (line_alts_of_nonnil (pline_ws l) k Hk).
  - by apply pop_app_nonnil_r.
  - rewrite /alt_execL. by apply pop_app_nonnil_r.
  - rewrite /alt_execR. by apply pop_app_nonnil_r.
  - by apply pop_app_nonnil_r.
  - rewrite /alt_pipe. by apply pop_app_nonnil_r.
  - (* THE TERMINAL ROUND'S BLOCK IS NONEMPTY because [palt_ok] refuses
       the empty selector: a fork-failure round that has printed nothing
       is not a round the claim has opened.  (Design section 4.3h's
       "[PForkS []] is the old [PFork]" would break this lemma, and with
       it every [pending_p] length argument below.) *)
    assert (Hok : palt_ok l (PForkS sel)).
    { destruct Ha as [Ha | Heq]; [exact Ha | discriminate Heq]. }
    destruct l as [ws | ws]; [by destruct Hok |].
    destruct Hok as (Hne & H1 & H2). intro Hq.
    apply (f_equal length) in Hq.
    rewrite (pmerge_length sel dg_execL alt_forkc H1 H2) in Hq.
    cbn [length] in Hq. by destruct sel.
  - exact Hpr.
Qed.

(* ====================================================================== *)
(*  6b.  THE ERA'S PROCESS-BYTE CURSOR, AT THE PIPELINE SESSION            *)
(* ====================================================================== *)

Fixpoint proc_before_from_p (ps cs : list nat) (pre I : list (bv 8))
  : list (bv 8) :=
  match I with
  | [] => []
  | b :: I' => pending_at_p ps cs pre ++ proc_before_from_p ps cs (pre ++ [b]) I'
  end.

Definition proc_before_p (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  proc_before_from_p ps cs [] I.

Definition pcount_p (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) : nat :=
  (length (proc_before_p ps cs (snd <$> E)) + length w)%nat.

(* ===================================================================== *)
(*  THE TWO-WRITER BLOCK'S PURE PIECES (was [PipeOutPure.v] until union  *)
(*  cut C9h)                                                             *)
(* ===================================================================== *)
(* as in PipeDisc / PipeOutPure: a pure file does not inherit ssreflect's
   [rewrite] from the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  2.  THE STAGE READING THAT ADMITS AN UNFILED BLOCK                     *)
(* ====================================================================== *)

(* the round in progress is a PIPELINE line -- the only shape whose
   alternatives include [PBoth] *)
Definition pboth_line (I : list (bv 8)) : Prop :=
  exists ws, pline_of (bodies_of I !!! (nlines I - 1)%nat) = LPipe ws.

(* ====================================================================== *)
(*  5.  WHAT A COMPLETED ROUND'S BLOCK CANNOT BE                           *)
(*                                                                        *)
(*  The refutation the claim's ECHO step needs in the both arm, and the    *)
(*  reason [sessp_prefix_det] never has to look at an unfiled round: a     *)
(*  non-panic alternative's continuation ENDS WITH THE PROMPT, whose first *)
(*  byte is '$', and no byte of a running merge is a '$'.  So a round      *)
(*  whose block is still in progress can never be mistaken for one whose   *)
(*  block is complete, at any selector.                                    *)
(* ====================================================================== *)

Lemma nodollar_prompt_head : ~ nodollar (Z_to_bv 8 36%Z).
Proof using.
  rewrite /nodollar. intro Hq. apply Hq.
  by vm_compute.
Qed.

(* ====================================================================== *)
(*  6.  THE ROUND'S LEND, GENERALISED (coordinator's amendment,           *)
(*      2026-09-19, after SH-PIPE-ROUND-2's [pipe_turn_one_writer])        *)
(*                                                                        *)
(*  [EchoOut.turn] is half a [mono_nat] authority, so ONE console writer   *)
(*  at a time -- and sh's runcmd child forks TWICE without knowing which   *)
(*  child will write the round's block.  So the two-cursor lease is not    *)
(*  the [PBoth] arm's mechanism: it is THE ROUND'S LEND on every arm.      *)
(*  The LEFT child's console bytes are always a prefix of [dg_execL] (it   *)
(*  either execs and writes into the PIPE, or fails and prints its         *)
(*  diagnostic); the RIGHT child's are a prefix of ONE list [R] fixed at   *)
(*  its first byte -- the LINE (cat printing what it read, [PRan]) or      *)
(*  [dg_execR] (its own diagnostic, [PExecR]).  So ALL FOUR block shapes   *)
(*  are [pmerge sel dg_execL R] at the two cursors, and the four           *)
(*  alternatives are four ways of finishing it.                           *)
(* ====================================================================== *)

Definition pend2 (R : list (bv 8)) (sel : list bool) : list (bv 8) :=
  pmerge sel dg_execL R.

(* ---- THE ROUND'S BLOCK SHAPE, at the two cursors and the right child's
       own source ---- *)

Definition wr_blk2_p (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) : Prop :=
  I <> []
  /\ rest_of I = []
  /\ length cs = (nlines I - 1)%nat
  /\ pboth_line I
  /\ pro_pin_p ps cs I
  /\ P = length (proc_before_p ps cs I)
  /\ length sel = (c1 + c2)%nat
  /\ count_true sel = c1
  /\ (c1 <= length dg_execL)%nat
  /\ (c2 <= length R)%nat.

(* THE BLOCK IN PROGRESS, of any shape: the round's entry is absent and
   the bytes so far are a prefix of the continuation of an alternative the
   line admits. *)
Definition pblk2_at (cs : list nat) (I : list (bv 8)) (w : list (bv 8))
    (a : nat) : Prop :=
  I <> []
  /\ rest_of I = []
  /\ length cs = (nlines I - 1)%nat
  /\ palt_ok (pline_of (bodies_of I !!! (nlines I - 1)%nat)) (palt_of a)
  /\ palt_panic (palt_of a) = false
  /\ w `prefix_of`
     pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat)) (palt_of a).

(* ===================================================================== *)
(*  THE HOOKS AT [pipe_lm] (was [PipeOutPure.v] until union cut C9h)       *)
(* ===================================================================== *)
From stdpp Require Import ssreflect.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S0  THE LINE, AND ITS ALTERNATIVES' OUTPUT                            *)
(* ===================================================================== *)

(* the line the last COMPLETE body of [I] parses to ([FileHooks.fline]) *)
Definition pline_at (I : list (bv 8)) : pline :=
  pline_of (bodies_of I !!! (nlines I - 1)%nat).

(* THE RECORD'S [lk_ab]: the block alternative [a] owes at input [I],
   guarded by ADMISSIBILITY alone (see the header). *)
(* THE GUARD GAINS [palt_isforkS = false] (lane PIPE-MODEL-3): the
   terminal fork-failure round's block is NEVER written through this
   layer -- it is written by TWO processes at the two cursors and its
   code is never filed -- and [PipeOut.pecl_step_write_blk], which files
   the code at the block's FIRST byte, must not be reachable at it.  The
   guard is where the claim's [cs_nofork] comes from: [pab_nofork]
   carries it out of the same lookup [pab_ok] reads. *)
Definition pab_gd (I : list (bv 8)) (a : nat) : Prop :=
  palt_ok (pline_at I) (palt_of a) /\ palt_isforkS (palt_of a) = false.

Global Instance pab_gd_dec I a : Decision (pab_gd I a).
Proof using. rewrite /pab_gd. apply _. Defined.




(* ---- THE BLOCK'S LAST TWO BYTES ARE THE SHELL'S PROMPT.  [pcont_shape]
        says so under [pline_ok]; a writer holds no such thing, so the
        "ends with the prompt" half is read off the eight constructors
        instead -- every one of them is literally [_ ++ u_prompt]. ---- *)
Lemma pcont_prompt (l : pline) (a : palt) :
  palt_ok l a -> palt_panic a = false -> palt_isforkS a = false ->
  exists u : list (bv 8), pcont l a = u ++ u_prompt.
Proof using.
  intros Hok Hp Hfk.
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont;
    [| | | | | | done |].
  - (* [PEcho k]: [k < 4] at an [LEcho] line, [k = 3] at an [LPipe] one --
       and the panic index is excluded, so [k < 3] either way. *)
    assert (Hk : (k < 3)%nat).
    { rewrite /palt_panic in Hp. apply bool_decide_eq_false in Hp.
      destruct l as [ws | ws]; cbn [palt_ok] in Hok; lia. }
    destruct k as [| [| [| k]]]; [| | | exfalso; lia].
    + exists (wl_line (drop 1 (pline_ws l))). exact (line_alts_of_0 _).
    + exists dg_execL. rewrite (line_alts_of_1 (pline_ws l)).
      by rewrite -alt_execL_echo /alt_execL.
    + exists []. rewrite (line_alts_of_2 (pline_ws l)). by rewrite app_nil_l.
  - exists (wl_line (drop 1 (pline_ws l))). reflexivity.
  - exists dg_execL. reflexivity.
  - exists dg_execR. reflexivity.
  - exists (pmerge sel dg_execL dg_execR). reflexivity.
  - exists (wl_line dg_pipe). reflexivity.
  - exists []. by rewrite app_nil_l.
Qed.




(* ---- THE THREE NAMED ALTERNATIVES ------------------------------------ *)

(* THE PANIC is the LITERAL 3 at BOTH line shapes -- the coordinator's
   ruling of 2026-09-18 ([PipeDisc.palt_ok_pipe_panic]) is exactly what
   makes [lk_pan] a constant here where the file's is per-line. *)
Lemma palt_of_3 : palt_of 3%nat = PEcho 3%nat.
Proof using. apply palt_of_lt4. lia. Qed.

Lemma ppan_panic : palt_panic (palt_of 3%nat) = true.
Proof using. rewrite palt_of_3. by vm_compute. Qed.

Lemma ppan_ok (l : pline) : palt_ok l (palt_of 3%nat).
Proof using.
  rewrite palt_of_3. destruct l as [ws | ws]; cbn [palt_ok]; lia.
Qed.

Lemma ppan_nofork : palt_isforkS (palt_of 3%nat) = false.
Proof using. rewrite palt_of_3. reflexivity. Qed.


(* THE EXEC-FAILED CHILD'S alternative is PER-LINE and the design's
   "literally 1" is refuted at the statement: [palt_ok (LPipe ws)
   (PEcho 1)] is FALSE (only [PEcho 3] joins a pipeline line's [PEcho]
   arms).  What IS echo's verbatim are the BYTES, through
   [PipeDisc.alt_execL_echo]. *)
Definition pexf_of (l : pline) : nat :=
  match l with LEcho _ => 1%nat | LPipe _ => palt_code PExecL end.

Definition pexfb (l : pline) : list (bv 8) :=
  match l with LEcho _ => alt_execfail | LPipe _ => alt_execL end.

Lemma pexf_of_ok (l : pline) : palt_ok l (palt_of (pexf_of l)).
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). cbn [palt_ok]. lia.
  - rewrite (palt_of_code PExecL). exact I.
Qed.

Lemma pexf_of_nopanic (l : pline) : palt_panic (palt_of (pexf_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). by vm_compute.
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.

Lemma pcont_pexf (l : pline) : pcont l (palt_of (pexf_of l)) = pexfb l.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of pexfb].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). cbn [pcont pline_ws].
    exact (line_alts_of_1 ws).
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.

Lemma pexf_of_nofork (l : pline) : palt_isforkS (palt_of (pexf_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). reflexivity.
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.



(* THE ALTERNATIVE A ROUND TAKES WHEN NOBODY WROTE: the shell's own prompt
   IS the block's first byte.  [PEcho 2] at an echo line, [PSilent] at a
   pipeline one; both print [u_prompt]. *)
Definition pnoc_of (l : pline) : nat :=
  match l with LEcho _ => 2%nat | LPipe _ => palt_code PSilent end.

Lemma pnoc_of_ok (l : pline) : palt_ok l (palt_of (pnoc_of l)).
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). cbn [palt_ok]. lia.
  - rewrite (palt_of_code PSilent). exact I.
Qed.

Lemma pnoc_of_nopanic (l : pline) : palt_panic (palt_of (pnoc_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). by vm_compute.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.

Lemma pcont_pnoc (l : pline) : pcont l (palt_of (pnoc_of l)) = u_prompt.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). cbn [pcont pline_ws].
    reflexivity.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.

Lemma pnoc_of_nofork (l : pline) : palt_isforkS (palt_of (pnoc_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). reflexivity.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.






(* ---- THE MODEL'S HOOKS ([LineModelLinks.lm_hooks] at the pipeline
        model): the panic is the literal 3, the exec failure and the
        silent alternative are per-line, state-freedom is [~ PForkS] (the
        arm written by two processes never goes through this layer), and
        what a WRITER knows of a continuation is [pcont_prompt] /
        [PipeOutPure.pcont_nonnil].  Everything section 0 said of [pab] /
        [papr] is then [LineModelLinks]'s lemma read back through the
        equations below. ---- *)
Lemma pfree_term (a : palt) : negb (palt_isforkS a) = true -> palt_isforkS a = false.
Proof using. destruct (palt_isforkS a); [discriminate | reflexivity]. Qed.

Lemma pfree_of_nofork (a : palt) : palt_isforkS a = false -> negb (palt_isforkS a) = true.
Proof using. intros ->. reflexivity. Qed.

Lemma pcont_nonnil_dec (l : pline) (a : palt) :
  palt_ok l a \/ a = palt_of 0%nat -> pcont l a <> [].
Proof using.
  rewrite (palt_of_lt4 0%nat ltac:(lia)). exact (pcont_nonnil l a).
Qed.

Definition pipe_hooks : lm_hooks pipe_lm :=
  MkLMH pipe_lm (fun a => negb (palt_isforkS a)) tt (fun _ => 3%nat) pexf_of pexfb
    (fun l => Some (pnoc_of l)) (fun _ => palt_ok_dec)
    (fun _ _ _ _ _ => eq_refl) pfree_term (fun _ _ _ _ _ H => H)
    (fun _ => ppan_ok) (fun _ => pfree_of_nofork _ ppan_nofork) (fun _ => ppan_panic)
    (fun _ => pexf_of_ok) (fun l => pfree_of_nofork _ (pexf_of_nofork l)) pexf_of_nopanic
    (fun _ l => pcont_pexf l)
    (fun s l c => lmh_noc_some (fun c => LineModel.lm_ok pipe_lm s l (LineModel.lm_dec pipe_lm c)) _ c
                    (pnoc_of_ok l))
    (fun l c => lmh_noc_some (fun c => negb (palt_isforkS (LineModel.lm_dec pipe_lm c)) = true) _ c
                  (pfree_of_nofork _ (pnoc_of_nofork l)))
    (fun l c => lmh_noc_some (fun c => LineModel.lm_panic pipe_lm (LineModel.lm_dec pipe_lm c) = false) _ c
                  (pnoc_of_nopanic l))
    (fun s l c => lmh_noc_some (fun c => LineModel.lm_cont pipe_lm s l (LineModel.lm_dec pipe_lm c) = u_prompt) _ c
                    (pcont_pnoc l))
    (fun _ l a Hok Hp Ht => pcont_prompt l a Hok Hp Ht)
    (fun _ l a H => pcont_nonnil_dec l a H).


