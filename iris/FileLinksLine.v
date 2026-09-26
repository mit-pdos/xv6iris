(* ===================================================================== *)
(*  FileLinksLine.v -- THE FILE APPLICATION'S CREDENTIAL FAMILIES.        *)
(*                                                                       *)
(*  Lane LINK-GEN-2.  [LinkRec.LinkRec]'s fields at the FILE claim:       *)
(*  [EchoLinks.v]'s and [EchoLinksLine.v]'s pure shapes and credential    *)
(*  families, restated at [FileOutPure]'s model -- [pro_pin_f],           *)
(*  [proc_before_f], [proc_stream_f], [pro_idx_f] and [FileDisc.          *)
(*  fstate_upto] -- and proved through [FileLinks.file_links].               *)
(*                                                                       *)
(*  WHAT IS SHARED AND NOT RESTATED: the PROLOGUE.  [pro_of], [pro_from], *)
(*  [pro_done], [pro_fail], [pro_rounds], [pro_alts], /init's banner and  *)
(*  the shell's prompt are [EchoDisc]'s and the file application runs the *)
(*  same /init, so [EchoLinks.pro_of_open_snoc_eq], [wr_prompt_head],     *)
(*  [wr_prompt_tail], [wr_prompt_len], [wr_pro_alts_0], [wr_ban_head],    *)
(*  [bodies_of_app_nonl], [nlines_app_nonl], [rest_of_app_nonl] and       *)
(*  [pro_rounds_one] are IMPORTED, not twinned.                           *)
(*                                                                       *)
(*  WHAT IS NEW, and it is the whole of what the file adds: the BLOCK a   *)
(*  line owes is [FileDisc.cont] at the state [fstate_upto] says the file is *)
(*  in, where echo's was [EchoDisc.line_alts_of] of the words that were   *)
(*  typed.  A program above the links names NO state, so the record's     *)
(*  [lk_ab] is the block AT THE ALTERNATIVES WHOSE OUTPUT DOES NOT DEPEND *)
(*  ON ONE -- every [ralt] but [RCRan] ([fstate_free]) -- and is [[]]        *)
(*  elsewhere, which makes the block-byte step premise-free exactly as    *)
(*  echo's is ([EchoDisc.line_alts_lt]).  cat's own round, the one        *)
(*  [RCRan] round, does not go through this family.                       *)
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
Require Import LineWords.
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import LineModel.       (* the line model, and its writer-side reading *)
Require Import LineModelLinks.
Require Import LineModelInst.   (* the stream equations at [file_lm] *)
Require Import FileHooks.       (* S0: the hooks, moved below [FileOut] *)
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.



(* ===================================================================== *)
(*  S1  THE PURE SHAPES, AT THE FILE MODEL                                *)
(*                                                                       *)
(*  [EchoLinks]'s [wr_pro] / [wr_blk] / [wr_open] / [wr_sp] / [wr_owed] / *)
(*  [wr_ban] and [EchoLinksLine]'s [wr_tail] / [wr_blk_t] / [wr_sp_t] /   *)
(*  [wr_open_t] / [blkcs], with [pro_pin_f], [proc_before_f],             *)
(*  [proc_stream_f], [pro_idx_f] and the era's BOOT STATE [s0] threaded.  *)
(*  Where echo tested [cs !!! (nlines I - 1) = 3] the file tests          *)
(*  [ralt_panic (ralt_at cs (nlines I - 1))], so the two new line shapes' *)
(*  fork alternatives open a round too.                                   *)
(* ===================================================================== *)
Definition wr_pro_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true)
  /\ ~ pro_done (pro_from (pro_idx_f cs (nlines I)) ps)
  /\ P = length (proc_stream_f ps cs (Some s0) I).

Definition wr_blk_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before_f ps cs (Some s0) I).

Definition wr_open_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (pro_idx_f cs (nlines I) < pro_rounds ps)%nat
  /\ P = length (proc_stream_f ps cs (Some s0) I).

Definition wr_owed_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  wr_pro_f ps cs s0 I P \/ wr_blk_f ps cs s0 I P.

Definition wr_sp_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  wr_open_f ps cs s0 I (S P)
  /\ proc_stream_f ps cs (Some s0) I !! P = Some (u_prompt !!! 1%nat).

Definition wr_pre_f (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then [] else alt_panic.

Definition wr_ban_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true)
  /\ (exists j : nat,
        pro_from (pro_idx_f cs (nlines I)) ps = pro_fail j
        /\ P = (length (proc_before_f ps cs (Some s0) I)
                + length (wr_pre_f I) + pro_round * j)%nat).

Definition wr_tail_f (ps cs : list nat) : Prop :=
  pro_from (S (pro_idx_f cs (length cs))) ps = [].

Definition wr_blk_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop := wr_blk_f ps cs s0 I P /\ wr_tail_f ps cs.

Definition wr_sp_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop := wr_sp_f ps cs s0 I P /\ wr_tail_f ps cs.

Definition wr_open_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : Prop := wr_open_f ps cs s0 I P /\ wr_tail_f ps cs.

Definition blkcs_f (cs : list nat) (a i : nat) : list nat :=
  match i with O => cs | S _ => cs ++ [a] end.

(* ---- the writer's stages are [LineModel]'s, by the stream equations ---- *)
Lemma wr_pro_f_lm ps cs s0 I P : wr_pro_f ps cs s0 I P = lm_wr_pro file_lm ps cs s0 I P.
Proof using. rewrite /wr_pro_f /lm_wr_pro ?proc_stream_f_lm ?proc_before_f_lm pro_idx_f_lm. reflexivity. Qed.
Lemma wr_blk_f_lm ps cs s0 I P : wr_blk_f ps cs s0 I P = lm_wr_blk file_lm ps cs s0 I P.
Proof using. rewrite /wr_blk_f /lm_wr_blk ?proc_stream_f_lm ?proc_before_f_lm. reflexivity. Qed.
Lemma wr_open_f_lm ps cs s0 I P : wr_open_f ps cs s0 I P = lm_wr_open file_lm ps cs s0 I P.
Proof using. rewrite /wr_open_f /lm_wr_open ?proc_stream_f_lm ?proc_before_f_lm pro_idx_f_lm. reflexivity. Qed.
Lemma wr_owed_f_lm ps cs s0 I P : wr_owed_f ps cs s0 I P = lm_wr_owed file_lm ps cs s0 I P.
Proof using. rewrite /wr_owed_f /lm_wr_owed wr_pro_f_lm wr_blk_f_lm. reflexivity. Qed.
Lemma wr_sp_f_lm ps cs s0 I P : wr_sp_f ps cs s0 I P = lm_wr_sp file_lm ps cs s0 I P.
Proof using. rewrite /wr_sp_f /lm_wr_sp wr_open_f_lm proc_stream_f_lm. reflexivity. Qed.
Lemma wr_ban_f_lm ps cs s0 I P : wr_ban_f ps cs s0 I P = lm_wr_ban file_lm ps cs s0 I P.
Proof using. rewrite /wr_ban_f /lm_wr_ban ?proc_stream_f_lm ?proc_before_f_lm pro_idx_f_lm. reflexivity. Qed.
Lemma wr_tail_f_lm ps cs : wr_tail_f ps cs = lm_wr_tail file_lm ps cs.
Proof using. rewrite /wr_tail_f /lm_wr_tail pro_idx_f_lm. reflexivity. Qed.
Lemma wr_blk_t_f_lm ps cs s0 I P : wr_blk_t_f ps cs s0 I P = lm_wr_blk_t file_lm ps cs s0 I P.
Proof using. rewrite /wr_blk_t_f /lm_wr_blk_t wr_blk_f_lm wr_tail_f_lm. reflexivity. Qed.
Lemma wr_sp_t_f_lm ps cs s0 I P : wr_sp_t_f ps cs s0 I P = lm_wr_sp_t file_lm ps cs s0 I P.
Proof using. rewrite /wr_sp_t_f /lm_wr_sp_t wr_sp_f_lm wr_tail_f_lm. reflexivity. Qed.
Lemma wr_open_t_f_lm ps cs s0 I P : wr_open_t_f ps cs s0 I P = lm_wr_open_t file_lm ps cs s0 I P.
Proof using. rewrite /wr_open_t_f /lm_wr_open_t wr_open_f_lm wr_tail_f_lm. reflexivity. Qed.


(* ===================================================================== *)
(*  S2  THE PURE LEMMAS                                                   *)
(* ===================================================================== *)

(* ---- the stage's own readings ---- *)
Lemma pro_pin_f_nil (ps cs : list nat) : pro_pin_f ps cs [].
Proof using.
  apply pro_pin_f_lm. apply (lm_pro_pin_nil file_lm).
Qed.

Lemma pro_pin_f_at (ps cs : list nat) (I : list (bv 8)) (q : nat) :
  pro_pin_f ps cs I -> (q < nstarted I)%nat ->
  (pro_idx_f cs q < pro_rounds ps)%nat.
Proof using.
  intros H Hq. rewrite pro_idx_f_lm.
  exact (lm_pro_pin_at file_lm ps cs I q (proj1 (pro_pin_f_lm _ _ _) H) Hq).
Qed.

Lemma wr_blk_nonnil_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : wr_blk_f ps cs s0 I P -> I <> [].
Proof using.
  rewrite wr_blk_f_lm. apply (lm_wr_blk_nonnil file_lm).
Qed.

Lemma wr_blk_lines_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : wr_blk_f ps cs s0 I P -> nlines I = S (length cs).
Proof using.
  rewrite wr_blk_f_lm. apply (lm_wr_blk_lines file_lm).
Qed.

Lemma wr_blk_started_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) : wr_blk_f ps cs s0 I P -> nstarted I = S (length cs).
Proof using.
  rewrite wr_blk_f_lm. apply (lm_wr_blk_started file_lm).
Qed.

(* ---- filing an alternative reads no round below the boundary ---- *)
Lemma wr_blk_pin_snoc_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) : wr_blk_f ps cs s0 I P -> pro_pin_f ps (cs ++ [a]) I.
Proof using.
  rewrite wr_blk_f_lm. intros Hw. apply pro_pin_f_lm.
  exact (lm_wr_blk_pin_snoc file_lm ps cs s0 I P a Hw).
Qed.

(* ...and it moves no byte of what is already out ---- *)
Lemma wr_blk_low_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  proc_before_f ps (cs ++ [a]) (Some s0) I = proc_before_f ps cs (Some s0) I.
Proof using.
  rewrite wr_blk_f_lm !proc_before_f_lm. apply (lm_wr_blk_low file_lm).
Qed.

(* THE BLOCK THE ROUND OWES once alternative [a] is filed, at a NON-PANIC
   state-free alternative: exactly [fab]. *)
Lemma wr_blk_pending_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  ralt_panic (ralt_dec a) = false ->
  pending_at_f ps (cs ++ [a]) (Some s0) I = fabs s0 cs I a.
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm fabs_lm. apply (lm_wr_blk_pending_s file_lm).
Qed.

Lemma wr_blk_pending_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  fapr I a ->
  pending_at_f ps (cs ++ [a]) (Some s0) I = fab I a.
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_pending file_lm file_hooks ps cs s0 I P a Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR *)
Lemma wr_blk_byte_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a j : nat) (b : bv 8) :
  wr_blk_f ps cs s0 I P -> ralt_panic (ralt_dec a) = false ->
  fabs s0 cs I a !! j = Some b ->
  proc_stream_f ps (cs ++ [a]) (Some s0) I !! (P + j)%nat = Some b.
Proof using.
  rewrite wr_blk_f_lm proc_stream_f_lm fabs_lm. apply (lm_wr_blk_byte_s file_lm).
Qed.

Lemma wr_blk_byte_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a j : nat) (b : bv 8) :
  wr_blk_f ps cs s0 I P -> fapr I a ->
  fab I a !! j = Some b ->
  proc_stream_f ps (cs ++ [a]) (Some s0) I !! (P + j)%nat = Some b.
Proof using.
  rewrite wr_blk_f_lm proc_stream_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_byte file_lm file_hooks ps cs s0 I P a j b Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

(* ---- the round index does not move at a non-panic alternative ---- *)
Lemma fd_snoc_lookup_total (cs : list nat) (a : nat) :
  (cs ++ [a]) !!! length cs = a.
Proof using.
  apply ll_snoc_lookup_total.
Qed.

Lemma pro_idx_f_snoc_ne (cs : list nat) (a : nat) :
  ralt_panic (ralt_dec a) = false ->
  pro_idx_f (cs ++ [a]) (S (length cs)) = pro_idx_f cs (length cs).
Proof using.
  rewrite !pro_idx_f_lm. apply (lm_pro_idx_snoc_ne file_lm).
Qed.

Lemma pro_idx_f_snoc_pan (cs : list nat) (a : nat) :
  ralt_panic (ralt_dec a) = true ->
  pro_idx_f (cs ++ [a]) (S (length cs)) = S (pro_idx_f cs (length cs)).
Proof using.
  rewrite !pro_idx_f_lm. apply (lm_pro_idx_snoc_pan file_lm).
Qed.

(* the block's bytes are a PREFIX of what the round then owes -- an
   equality at a non-panic alternative, a prefix at the panic one (whose
   block runs on into the next round's prologue).  That is all a BYTE
   lookup needs, so [wr_blk_byte_f] does not ask for [fapr]. *)
Lemma wr_blk_pending_pre_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  ralt_ok (fline I) (ralt_dec a) -> fstate_free (ralt_dec a) = true ->
  fab I a `prefix_of` pending_at_f ps (cs ++ [a]) (Some s0) I.
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm fab_lm fline_lm. apply (lm_wr_blk_pending_pre file_lm file_hooks).
Qed.

Lemma wr_tail_snoc_f (ps cs : list nat) (a : nat) :
  ralt_panic (ralt_dec a) = false -> wr_tail_f ps cs -> wr_tail_f ps (cs ++ [a]).
Proof using.
  rewrite !wr_tail_f_lm. apply (lm_wr_tail_snoc file_lm).
Qed.

(* ---- the prologue grows by exactly its alternative ---- *)
Lemma pending_at_f_round_snoc (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (a : nat) :
  rest_of I = [] ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true) ->
  ~ pro_done (pro_from (pro_idx_f cs (nlines I)) ps) ->
  (pro_idx_f cs (nlines I) <= pro_rounds ps)%nat ->
  pending_at_f (ps ++ [a]) cs (Some s0) I
  = pending_at_f ps cs (Some s0) I ++ pro_alts !!! a.
Proof using.
  rewrite !pending_at_f_lm !pro_idx_f_lm.
  apply (lm_pending_at_round_snoc file_lm file_lm_laws).
Qed.


(* ===================================================================== *)
(*  S3  THE ROUND'S BANNER, STILL OWED                                    *)
(* ===================================================================== *)
Lemma wr_ban_pro_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_ban_f ps cs s0 I P -> wr_pro_f ps cs s0 I P.
Proof using.
  rewrite wr_ban_f_lm wr_pro_f_lm. apply (lm_wr_ban_pro file_lm file_lm_laws).
Qed.

Lemma wr_ban_low_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_ban_f ps cs s0 I P ->
  proc_before_f (ps ++ [3%nat]) cs (Some s0) I = proc_before_f ps cs (Some s0) I.
Proof using.
  rewrite wr_ban_f_lm !proc_before_f_lm. apply (lm_wr_ban_low file_lm).
Qed.

Lemma wr_ban_filed_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_ban_f ps cs s0 I P ->
  exists j : nat,
    pro_from (pro_idx_f cs (nlines I)) (ps ++ [3%nat]) = pro_fail j ++ [3%nat]
    /\ P = (length (proc_before_f (ps ++ [3%nat]) cs (Some s0) I)
            + length (wr_pre_f I) + pro_round * j)%nat.
Proof using.
  rewrite wr_ban_f_lm proc_before_f_lm pro_idx_f_lm. intros Hw.
  destruct (lm_wr_ban_filed file_lm ps cs s0 I P Hw) as (j & H1 & H2).
  exists j. exact (conj H1 H2).
Qed.

Lemma wr_ban_byte_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P i : nat) (b : bv 8) :
  wr_ban_f ps cs s0 I P -> u_banner !! i = Some b ->
  proc_stream_f (ps ++ [3%nat]) cs (Some s0) I !! (P + i)%nat = Some b.
Proof using.
  rewrite wr_ban_f_lm proc_stream_f_lm. apply (lm_wr_ban_byte file_lm file_lm_laws).
Qed.

Lemma wr_ban_done_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_ban_f ps cs s0 I P ->
  wr_pro_f (ps ++ [3%nat]) cs s0 I (P + length u_banner)%nat.
Proof using.
  rewrite wr_ban_f_lm wr_pro_f_lm. apply (lm_wr_ban_done file_lm file_lm_laws).
Qed.

(* THE TRANSCRIPT'S HEAD *)
Lemma wr_ban_round0_f (s0 : fstate) : wr_ban_f [] [] s0 [] 0%nat.
Proof using.
  rewrite wr_ban_f_lm. apply (lm_wr_ban_round0 file_lm).
Qed.


(* ===================================================================== *)
(*  S4  THE GAP LAW AND THE LINE'S READ                                   *)
(* ===================================================================== *)
Lemma proc_before_from_gap_f (ps cs : list nat) (f0 : option fstate)
    (pre k : list (bv 8)) :
  (forall J : list (bv 8), J `prefix_of` k -> J <> k ->
     pending_at_f ps cs f0 (pre ++ J) = []) ->
  proc_before_from_f ps cs f0 pre k = [].
Proof using.
  rewrite proc_before_from_f_lm_o. intros Hj.
  apply (lm_proc_before_from_gap file_lm). intros J HJ Hne.
  rewrite -pending_at_f_lm_o. exact (Hj J HJ Hne).
Qed.

Lemma proc_before_line_f (ps cs : list nat) (f0 : option fstate)
    (I l : list (bv 8)) :
  rest_of I = [] -> wl_nl ∉ l ->
  proc_before_f ps cs f0 (I ++ l ++ [wl_nl]) = proc_stream_f ps cs f0 I.
Proof using.
  rewrite proc_before_f_lm_o proc_stream_f_lm_o. apply (lm_proc_before_line file_lm).
Qed.


(* ===================================================================== *)
(*  S5  THE STEPS, PURE                                                   *)
(* ===================================================================== *)

(* (1) the round's CHOICE BYTE at an open prologue: filing alternative 0
       appends the prompt's two bytes to the round's block *)
Lemma wr_pro_dollar_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_pro_f ps cs s0 I P -> wr_sp_f (ps ++ [0%nat]) cs s0 I (S P).
Proof using.
  rewrite wr_pro_f_lm wr_sp_f_lm. apply (lm_wr_pro_dollar file_lm file_lm_laws).
Qed.

(* (2) the LINE's choice byte at a settled round is the block of the
       alternative the round took ([LineModelLinks.lm_wr_blk_dollar] at
       it); there is no "nobody wrote" alternative to file *)

(* (3) the SPACE, and (4) the READ *)
Lemma wr_sp_open_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_sp_f ps cs s0 I P -> wr_open_f ps cs s0 I (S P).
Proof using.
  rewrite wr_sp_f_lm wr_open_f_lm. apply (lm_wr_sp_open file_lm).
Qed.

Lemma wr_open_read_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) (l : list (bv 8)) :
  wr_open_f ps cs s0 I P -> wl_nl ∉ l ->
  wr_blk_f ps cs s0 (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_f_lm wr_blk_f_lm. apply (lm_wr_open_read file_lm).
Qed.


(* ===================================================================== *)
(*  S6  THE TIGHT STEPS ([EchoLinksLine]'s S2 at the file model)          *)
(* ===================================================================== *)
Lemma wr_blk_open_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> ralt_panic (ralt_dec a) = false ->
  wr_open_t_f ps (cs ++ [a]) s0 I (P + length (fabs s0 cs I a))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_open_t_f_lm fabs_lm. apply (lm_wr_blk_open_s file_lm).
Qed.

Lemma wr_blk_open_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> fapr I a ->
  wr_open_t_f ps (cs ++ [a]) s0 I (P + length (fab I a))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_open_t_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_open file_lm file_hooks ps cs s0 I P a Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma wr_blk_sp_fs (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> faprs I a ->
  wr_sp_t_f ps (cs ++ [a]) s0 I (P + (length (fabs s0 cs I a) - 1))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_sp_t_f_lm fabs_lm. intros Hw Hpr.
  exact (lm_wr_blk_sp_s file_lm file_hooks ps cs s0 I P a Hw (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma wr_blk_sp_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_t_f ps cs s0 I P -> fapr I a ->
  wr_sp_t_f ps (cs ++ [a]) s0 I (P + (length (fab I a) - 1))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_sp_t_f_lm fab_lm. intros Hw Hpr.
  exact (lm_wr_blk_sp file_lm file_hooks ps cs s0 I P a Hw (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma wr_sp_open_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_sp_t_f ps cs s0 I P -> wr_open_t_f ps cs s0 I (S P).
Proof using.
  rewrite wr_sp_t_f_lm wr_open_t_f_lm. apply (lm_wr_sp_open_t file_lm).
Qed.

Lemma wr_open_read_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) (l : list (bv 8)) :
  wr_open_t_f ps cs s0 I P -> wl_nl ∉ l ->
  wr_blk_t_f ps cs s0 (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_t_f_lm wr_blk_t_f_lm. apply (lm_wr_open_read_t file_lm).
Qed.

Lemma wr_pro_tail_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_pro_f ps cs s0 I P -> wr_tail_f (ps ++ [0%nat]) cs.
Proof using.
  rewrite wr_pro_f_lm wr_tail_f_lm. apply (lm_wr_pro_tail file_lm).
Qed.

Lemma wr_pro_dollar_t_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_pro_f ps cs s0 I P -> wr_sp_t_f (ps ++ [0%nat]) cs s0 I (S P).
Proof using.
  rewrite wr_pro_f_lm wr_sp_t_f_lm. apply (lm_wr_pro_dollar_t file_lm file_lm_laws).
Qed.

(* the PANIC alternative opens a fresh round at the same input *)
Lemma wr_blk_pending_pan_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P : nat) :
  wr_blk_f ps cs s0 I P ->
  pending_at_f ps (cs ++ [fpan_of (fline I)]) (Some s0) I
  = alt_panic ++ pro_of (pro_from (S (pro_idx_f cs (length cs))) ps).
Proof using.
  rewrite wr_blk_f_lm pending_at_f_lm !pro_idx_f_lm.
  apply (lm_wr_blk_pending_pan file_lm file_lm_laws file_hooks).
Qed.

Lemma wr_blk_ban_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8)) (P : nat) :
  wr_blk_t_f ps cs s0 I P ->
  wr_ban_f ps (cs ++ [fpan_of (fline I)]) s0 I (P + length (fab I (fpan_of (fline I))))%nat.
Proof using.
  rewrite wr_blk_t_f_lm wr_ban_f_lm fab_lm.
  apply (lm_wr_blk_ban file_lm file_lm_laws file_hooks).
Qed.


(* ===================================================================== *)
(*  S7  THE DISCIPLINE LEMMA: an untainted input past a boundary means    *)
(*      the boundary's prompt was written ([EchoLinks.                    *)
(*      wr_owed_read_refute] at the file model).                          *)
(*                                                                       *)
(*  BOTH SIDES READ THE SAME BOOT STATE.  At the echo application the     *)
(*  stream is a function of [ps]/[cs]/[I] alone; here it also reads the   *)
(*  era's [s0], and the two halves agree because the writer's credential  *)
(*  and the reader's residue both carry [f0_lb] at the era's ONE file pin *)
(*  ([FileOut.file_era_pin_agree], then [f0_lb_agree]) -- which is what   *)
(*  [f0w] below packages.                                                 *)
(* ===================================================================== *)
Lemma pending_at_f_nonnil_at (ps cs0 : list nat) (f0 : option fstate)
    (I I0 : list (bv 8)) :
  I `prefix_of` I0 -> alts_pre I0 cs0 -> I <> [] -> rest_of I = [] ->
  pending_at_f ps cs0 f0 I <> [].
Proof using.
  rewrite pending_at_f_lm_o. apply (lm_pending_at_nonnil_at file_lm file_hooks).
Qed.

Lemma wr_owed_read_refute_f (ps cs ps0 cs0 : list nat) (s0 : fstate)
    (I I0 : list (bv 8)) (P : nat) :
  wr_owed_f ps cs s0 I P ->
  I `prefix_of` I0 -> I <> I0 -> rd_stage_f ps0 cs0 I0 ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (cs `prefix_of` cs0 \/ cs0 `prefix_of` cs) ->
  (length (proc_before_f ps0 cs0 (Some s0) I0) <= P)%nat -> False.
Proof using.
  rewrite wr_owed_f_lm proc_before_f_lm. intros Hw HI Hne Hrs.
  exact (lm_wr_owed_read_refute file_lm file_lm_laws file_hooks ps cs ps0 cs0 s0 I I0 P
           Hw HI Hne (proj1 (rd_stage_f_lm _ _ _ _) Hrs)).
Qed.


Lemma alt_panic_len5 : length alt_panic = 5%nat.
Proof using.
  exact lb_panic_len.
Qed.

(* the banner's shape, indexed by how many of its bytes are out: the
   FIRST byte files the letter, so from then on the resolution names it *)
Definition wr_banp_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P i : nat) : Prop :=
  match i with
  | O => wr_ban_f ps cs s0 I P
  | S _ => exists ps' : list nat, ps = ps' ++ [3%nat] /\ wr_ban_f ps' cs s0 I P
  end.


(* ===================================================================== *)
(*  S8  THE FILE'S PIECES OF THE CREDENTIAL FAMILIES                      *)
(*                                                                       *)
(*  The families themselves are [GenLinksLine]'s, once, at                *)
(*  [FileLinkGen.file_params]; what is the file's own is the era's BOOT   *)
(*  STATE witness ([f0w], pinned by the era's file pin), the writer's     *)
(*  cursor ([fcur]), the era's HEAD ([fhead]: the first process byte has  *)
(*  not been written, so there is no boot state to pin -- the deed's own  *)
(*  typed witness stands in its place, which                              *)
(*  [GenLinks.gwrite_link_first] consumes), the reader's residue          *)
(*  ([fwc_rres]) with the typed lines' witness ([flw]), and the turn.     *)
(* ===================================================================== *)
Section file_links_line.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FT := (file_taint (fgn_cl g)).

  (* THE ERA'S EXTRA STATE, as a resource.  The index is pinned to the
     CONSOLE era because the reader's residue has to agree with it and the
     record's [lk_rres] field is not indexed by the era. *)
  Definition f0w (k : nat) (s0 : fstate) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ ∃ vf : file_era, file_era_pin g k vf ∗ f0_lb vf s0)%I.

  Global Instance f0w_persistent k s : Persistent (f0w k s).
  Proof using . rewrite /f0w. apply _. Qed.
  Global Instance f0w_timeless k s : Timeless (f0w k s).
  Proof using . rewrite /f0w. apply _. Qed.

  Lemma f0w_agree (k k' : nat) (s s' : fstate) :
    f0w k s -∗ f0w k' s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "[-> H] [-> H']".
    iDestruct "H" as (vf) "[#Hp #Hl]". iDestruct "H'" as (vf') "[#Hp' #Hl']".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0_lb_agree with "Hl Hl'").
  Qed.

  (* THE READER'S BOOT WITNESS (RULING F0-BOOT): the boot ledger's entry
     alone, which init mints at boot -- so the reader's residue exists at
     the era's head, where nothing has been filed yet.  A writer's [f0w]
     is this beside the filed token, and the two agree on the state. *)
  Definition f0bw (k : nat) (s0 : fstate) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ ∃ vf : file_era, file_era_pin g k vf ∗ f0_bl vf s0)%I.

  Global Instance f0bw_persistent k s : Persistent (f0bw k s).
  Proof using . rewrite /f0bw. apply _. Qed.
  Global Instance f0bw_timeless k s : Timeless (f0bw k s).
  Proof using . rewrite /f0bw. apply _. Qed.

  Lemma f0bw_agree (k k' : nat) (s s' : fstate) :
    f0bw k s -∗ f0bw k' s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "[-> H] [-> H']".
    iDestruct "H" as (vf) "[#Hp #Hl]". iDestruct "H'" as (vf') "[#Hp' #Hl']".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0_bl_agree with "Hl Hl'").
  Qed.

  Lemma f0w_bw (k : nat) (s : fstate) : f0w k s -∗ f0bw k s.
  Proof using .
    iIntros "[-> H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iSplitR; [ by iPureIntro | ]. iExists vf. iFrame "Hp".
    iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma f0w_bw_agree (k k' : nat) (s s' : fstate) :
    f0w k s -∗ f0bw k' s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "H H'". iDestruct (f0w_bw with "H") as "H".
    iApply (f0bw_agree with "H H'").
  Qed.

  (* the writer's cursor at a NAMED stage *)
  Definition fcur (v : era_pins) (ps cs : list nat) (s0 : fstate)
      (I : list (bv 8)) (P k : nat) : iProp Σ :=
    (turn v P ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I ∗ f0w k s0)%I.

  Global Instance fcur_timeless v ps cs s0 I P k :
    Timeless (fcur v ps cs s0 I P k).
  Proof using . rewrite /fcur. apply _. Qed.

  (* THE ERA'S HEAD: nothing written, the boot state not yet filed, and
     the deed's typed witness in its place *)
  (* ...AND THE HEAD'S PRECONDITION: the typed witness of the boot state
     beside its (already minted) boot-ledger entry (RULING F0-BOOT) *)
  Definition f0pre : iProp Σ :=
    (∃ s : fstate, ⌜fstate_ok s⌝ ∗ (f0_typed g s ∨ FT) ∗ f0bw (S gen_id) s)%I.

  Definition fhead (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (⌜I = []⌝ ∗ ⌜k = S gen_id⌝ ∗ turn v 0%nat ∗ ps_lb v [] ∗ cs_lb v []
     ∗ inp_lb v [] ∗ (∃ vf : file_era, file_era_pin g k vf) ∗ f0pre)%I.

  Global Instance f0pre_timeless : Timeless f0pre.
  Proof using . rewrite /f0pre. apply _. Qed.
  Global Instance fhead_timeless k v I : Timeless (fhead k v I).
  Proof using . rewrite /fhead. apply _. Qed.

  (* THE DISPATCH FOR THE ELEVEN FAMILIES BELOW, NOT [apply _].  The tree
     carries 455 [Timeless] instances and most of the definitions under
     them are transparent, so the hint net cannot discriminate and a
     search tries nearly all of them: ~1.3s per GOAL at this altitude,
     which made the instance block 98s of this 111s file.  Descend through
     the CONNECTIVES and name the leaf instance, so no search runs at all.
     The dispatch must be SYNTACTIC: a [first [...]] spelling unifies up
     to delta and peels straight through a name that has its own
     instance. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless (fcur _ _ _ _ _ _ _) => apply fcur_timeless
    | |- Timeless (fhead _ _ _) => apply fhead_timeless
    | |- Timeless f0pre => apply f0pre_timeless
    | |- Timeless (f0w _ _) => apply f0w_timeless
    | |- Timeless (f0_typed _ _) => apply f0_typed_timeless
    | |- Timeless (file_taint _) => apply file_taint_timeless
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (turn_lb _ _) => apply turn_lb_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Timeless (file_era_pin _ _ _) => apply file_era_pin_timeless
    | |- Persistent (bi_exist _) => apply bi.exist_persistent; intro; tl_leaf
    | |- Persistent (bi_sep _ _) => apply bi.sep_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_or _ _) => apply bi.or_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_pure _) => apply bi.pure_persistent
    | |- Persistent (turn_lb _ _) => apply turn_lb_persistent
    | |- Persistent (ps_lb _ _) => apply ps_lb_persistent
    | |- Persistent (cs_lb _ _) => apply cs_lb_persistent
    | |- Persistent (inp_lb _ _) => apply inp_lb_persistent
    | |- Persistent (f0w _ _) => apply f0w_persistent
    | |- Persistent (f0_typed _ _) => apply f0_typed_persistent
    | |- Persistent (file_taint _) => apply file_taint_persistent
    | |- Persistent (file_era_pin _ _ _) => apply file_era_pin_persistent
    | |- _ => apply _
    end.

  Definition fwc_rres (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ (ps0 cs0 : list nat) (s0 : fstate),
       ⌜rd_stage_f ps0 cs0 I⌝
       ∗ turn_lb v (length (proc_before_f ps0 cs0 (Some s0) I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ f0bw (S gen_id) s0)%I.

  Global Instance fwc_rres_persistent v I : Persistent (fwc_rres v I).
  Proof using . rewrite /fwc_rres. tl_leaf. Qed.
  Global Instance fwc_rres_timeless v I : Timeless (fwc_rres v I).
  Proof using . rewrite /fwc_rres. tl_leaf. Qed.

  (* THE TYPED LINES' WITNESS (the PROGRAM STREAM, stretch 9): every
     [echo ... > f] line of the input the reader has consumed is in a list
     the LEDGER has a lower bound of -- which is what the child that writes
     the line to its file owes the claim ([FileWrite.file_wq]'s
     [(N, ws) ∈ ls]).  It
     is read off the consumed bytes' TAGS ([FileOut.ftag]) by
     [FileLineWit.echof_lines_of_consumed], and the left arm is the era's
     head, where no lower bound exists to be had. *)
  Definition flw (I : list (bv 8)) : iProp Σ :=
    (⌜echof_lines_in I = []⌝
     ∨ ∃ ls : list fwline,
         fl_lb (fgn_cl g) ls ∗ ⌜forall w, w ∈ echof_lines_in I -> w ∈ ls⌝)%I.

  Global Instance flw_persistent I : Persistent (flw I).
  Proof using . rewrite /flw. apply _. Qed.
  Global Instance flw_timeless I : Timeless (flw I).
  Proof using . rewrite /flw. apply _. Qed.

  (* ...and THE RECORD'S RESIDUE: the cursor bounds with the witness *)
  Definition fwc_rresw (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (fwc_rres v I ∗ flw I)%I.

  Global Instance fwc_rresw_persistent v I : Persistent (fwc_rresw v I).
  Proof using . rewrite /fwc_rresw. apply _. Qed.
  Global Instance fwc_rresw_timeless v I : Timeless (fwc_rresw v I).
  Proof using . rewrite /fwc_rresw. apply _. Qed.

  (* ---- the era's turn ([GenLinksLine.gen_link_inst]'s TURN at the
          file: [FileLinkGen.fturn0_gen] takes it apart) ---- *)
  Definition fturn_pre (k : nat) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ FileOut.fturn_core g k ∗ f0pre)%I.


End file_links_line.
