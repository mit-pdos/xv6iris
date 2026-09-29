(* ===================================================================== *)
(* UhistDefs.v -- THE PER-PROCESS KEY HISTORY'S ENTRIES (pure).            *)
(*                                                                        *)
(* claude-notes/design/ni-uhist.md D1.  A process's history is the list   *)
(* of its ROUNDS: the cause, the trapped key and the resumed key.  The    *)
(* trap loop ([ProofUserretClosed.stvec_handler_loop]) appends one entry  *)
(* per round, and the invariant it keeps is that every entry satisfies    *)
(* the kernel's round relation at the keys ([round_ok_keys]).  The ghost  *)
(* ([uhist_auth] / [uhist_own], last section) is here too, so that        *)
(* [SpecUsertrap]'s accessor can name it; its NAME is                      *)
(* [UsertrapRes.un_uh], and the residue carries it.                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import RiscvExtras.  (* [ret_pc] *)
Require Import ProcGeom.     (* [tf_epc_idx] *)
Require Import ProcDefs.     (* [ustate] / [pv_tf] / [pv_sz] / [pv_upt] *)
Require Import UserPtTree.   (* [ud_um] *)
Require Import UserPerm.     (* [perm_of] *)
Require Import FdSlots.      (* [fdstate] *)
Require Import UexecSlot.    (* [uvis] / [uvis_of] / [tf_w] *)
Require Import UexecRet.     (* [tf_resume_gpr0] / [tf_of] *)
Require Import UexecRound.   (* [uround_ok] *)
Require Import PipeNames.    (* [pipe_names] *)
Require Import Xv6Cameras.   (* [uledG] -- the ENCODED ledger camera *)

(* ===================================================================== *)
(* COUNTABILITY.  The history's camera is the ENCODED ledger             *)
(* ([Xv6Cameras.uledG]: a mono-list of [positive]s), so the entries must   *)
(* be [Countable].  The tree had [EqDecision] for the key's components but *)
(* no [Countable]; these are the missing instances, each an injection     *)
(* into a tuple/sum of countable types.                                    *)
(* ===================================================================== *)
Global Instance uperm_countable : Countable uperm.
Proof.
  refine (inj_countable' (fun u => (up_X u, up_W u))
                         (fun p => MkUperm p.1 p.2) _).
  by intros [].
Qed.

Global Instance offmode_countable : Countable offmode.
Proof.
  refine (inj_countable' (fun m => match m with OffParked => true | OffHeld => false end)
                         (fun b => if b then OffParked else OffHeld) _).
  by intros [].
Qed.

Global Instance pipe_names_countable : Countable pipe_names.
Proof.
  refine (inj_countable'
            (fun n => (pn_read n, pn_write n, pn_mread n, pn_mwrite n, pn_queue n))
            (fun t => MkPipeNames t.1.1.1.1 t.1.1.1.2 t.1.1.2 t.1.2 t.2) _).
  by intros [].
Qed.

Global Instance fdtype_countable : Countable fdtype.
Proof.
  refine (inj_countable'
            (fun t => match t with
                      | FdInode i g m => inl (i, g, m)
                      | FdPipe n => inr (inl n)
                      | FdDevice d => inr (inr d)
                      end)
            (fun s => match s with
                      | inl (i, g, m) => FdInode i g m
                      | inr (inl n) => FdPipe n
                      | inr (inr d) => FdDevice d
                      end) _).
  by intros [].
Qed.

Global Instance fdstate_countable : Countable fdstate.
Proof.
  refine (inj_countable'
            (fun s => match s with
                      | FdClosed => None
                      | FdOpen r w t => Some (r, w, t)
                      end)
            (fun o => match o with
                      | None => FdClosed
                      | Some (r, w, t) => FdOpen r w t
                      end) _).
  by intros [].
Qed.

Global Instance uvis_eq_dec : EqDecision uvis.
Proof. solve_decision. Defined.

Global Instance uvis_countable : Countable uvis.
Proof.
  refine (inj_countable'
            (fun W => (uvis_tf W, uvis_M W, uvis_perm W, uvis_sz W, uvis_fd W,
                       uvis_cwd W, uvis_gen W, uvis_ch W, uvis_pid W,
                       uvis_lazy W, uvis_secc W))
            (fun t => MkUvis t.1.1.1.1.1.1.1.1.1.1 t.1.1.1.1.1.1.1.1.1.2
                             t.1.1.1.1.1.1.1.1.2 t.1.1.1.1.1.1.1.2 t.1.1.1.1.1.1.2
                             t.1.1.1.1.1.2 t.1.1.1.1.2 t.1.1.1.2 t.1.1.2 t.1.2 t.2) _).
  by intros [].
Qed.

(* one round: the cause, the trapped key, the resumed key *)
Definition uround : Type := (mword 64 * uvis * uvis)%type.

(* the round relation at the two keys, spelled exactly as
   [UexecApply.uexec_ret_round_slot_of]'s hypothesis is at
   [g := tf_resume_gpr0 (uvis_tf W)], [sepc_v := tf_w (uvis_tf W) tf_epc_idx] *)
Definition round_ok_keys (sc : mword 64) (W W' : uvis) : Prop :=
  uround_ok sc (tf_of (tf_resume_gpr0 (uvis_tf W)) (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
    (uvis_M W) (uvis_perm W) (uvis_sz W) (uvis_cwd W) (uvis_lazy W) (uvis_secc W)
    (uvis_tf W') (uvis_M W') (uvis_perm W') (uvis_sz W') (uvis_cwd W') (uvis_lazy W')
    (uvis_secc W').

(* a history is well formed when every recorded round is a lawful one *)
Definition uhist_wf (h : list uround) : Prop :=
  Forall (fun e => round_ok_keys e.1.1 e.1.2 e.2) h.

Lemma uhist_wf_nil : uhist_wf [].
Proof. constructor. Qed.

Lemma uhist_wf_snoc h sc W W' :
  uhist_wf h -> round_ok_keys sc W W' -> uhist_wf (h ++ [(sc, W, W')]).
Proof.
  intros Hh Hr. apply Forall_app. split; [exact Hh|].
  constructor; [exact Hr | constructor].
Qed.

(* THE RECORD BRIDGE.  The loop holds the round relation at the record the
   round left ([U']); [uvis_of] projects exactly those fields, so the same
   relation IS the relation at the resumed key. *)
Lemma round_ok_keys_of_record sc W (U' : ustate) sts g cs pid :
  uround_ok sc (tf_of (tf_resume_gpr0 (uvis_tf W)) (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
    (uvis_M W) (uvis_perm W) (uvis_sz W) (uvis_cwd W) (uvis_lazy W) (uvis_secc W)
    (pv_tf (us_V U')) (us_M U') (perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))))
    (uint (pv_sz (us_V U'))) (pv_cwi (us_V U')) (pv_lazy (us_V U')) (pv_secc (us_V U')) ->
  round_ok_keys sc W (uvis_of U' sts g cs pid).
Proof. intros H. exact H. Qed.

(* ...and a round is countable as the product it is *)
Global Instance uround_eq_dec : EqDecision uround := _.
Global Instance uround_countable : Countable uround := _.

Section Uhist.
  Context `{!uledG Σ}.

  (* ------------------------------------------------------------------- *)
  (* THE GHOST (design/ni-uhist.md D2), at the ENCODED ledger camera     *)
  (* ([Xv6Cameras.uledG]): the list of rounds, each [encode]d.            *)
  (* ------------------------------------------------------------------- *)
  Definition uhist_auth (γ : gname) (h : list uround) : iProp Σ :=
    own γ (●ML ((encode <$> h) : list (leibnizO positive))).
  Definition uhist_lb (γ : gname) (h : list uround) : iProp Σ :=
    own γ (◯ML ((encode <$> h) : list (leibnizO positive))).

  Global Instance uhist_lb_persistent γ h : Persistent (uhist_lb γ h).
  Proof using . rewrite /uhist_lb. apply _. Qed.
  Global Instance uhist_lb_timeless γ h : Timeless (uhist_lb γ h).
  Proof using . rewrite /uhist_lb. apply _. Qed.
  Global Instance uhist_auth_timeless γ h : Timeless (uhist_auth γ h).
  Proof using . rewrite /uhist_auth. apply _. Qed.

  Lemma uhist_auth_lb γ h : uhist_auth γ h -∗ uhist_auth γ h ∗ uhist_lb γ h.
  Proof using .
    rewrite /uhist_auth /uhist_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML ((encode <$> h) : list (leibnizO positive))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  (* the encoding is injective, so a prefix of encodings is a prefix *)
  Local Lemma uhist_fmap_prefix (h h' : list uround) :
    (encode <$> h') `prefix_of` (encode <$> h) -> h' `prefix_of` h.
  Proof using .
    intros [k Hk].
    apply fmap_app_inv in Hk as (h1 & k1 & Heq1 & _ & ->).
    exists k1. f_equal. symmetry.
    apply (inj (fmap (M := list) encode)). exact Heq1.
  Qed.

  Lemma uhist_lb_prefix γ h h' : uhist_auth γ h -∗ uhist_lb γ h' -∗ ⌜h' `prefix_of` h⌝.
  Proof using .
    rewrite /uhist_auth /uhist_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. by apply uhist_fmap_prefix.
  Qed.

  (* two lower bounds of the one history are comparable *)
  Lemma uhist_lb_lb γ h h' :
    uhist_lb γ h -∗ uhist_lb γ h' -∗ ⌜h `prefix_of` h' \/ h' `prefix_of` h⌝.
  Proof using .
    rewrite /uhist_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    iPureIntro. destruct Hv as [Hv | Hv]; [left | right]; by apply uhist_fmap_prefix.
  Qed.

  Lemma uhist_grow γ h e :
    uhist_auth γ h ==∗ uhist_auth γ (h ++ [e])%list ∗ uhist_lb γ (h ++ [e])%list.
  Proof using .
    rewrite /uhist_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((encode <$> (h ++ [e])%list) : list (leibnizO positive)))
            with "Ha") as "Ha".
    { apply mono_list_update. rewrite fmap_app. by eexists. }
    iModIntro. iApply (uhist_auth_lb with "Ha").
  Qed.

  (* the residue's row: the history at some list, every round of it lawful *)
  Definition uhist_own (γ : gname) : iProp Σ :=
    (∃ h : list uround, uhist_auth γ h ∗ ⌜uhist_wf h⌝)%I.

  Lemma uhist_own_nil γ : uhist_auth γ [] -∗ uhist_own γ.
  Proof using .
    iIntros "H". iExists []. iFrame "H". iPureIntro. exact uhist_wf_nil.
  Qed.

End Uhist.
