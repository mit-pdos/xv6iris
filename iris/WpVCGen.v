(* ====================================================================== *)
(* WpVCGen.v -- a verification-condition generator for straight-line       *)
(* sequential instruction blocks.                                          *)
(*                                                                         *)
(* MOTIVATION.  The existing development proves an explicit Iris/CSL        *)
(* weakest-precondition for every instruction ([wp_c*], [wp_add], ...) and *)
(* chains them one-by-one through the full separation logic.  Each such    *)
(* step pays for BOTH (1) an Iris [state_interp] boundary AND (2) the       *)
(* fetch -> decode -> PMP/translate -> execute -> writeback reasoning, all  *)
(* carried out inside the logic.                                           *)
(*                                                                         *)
(* This file factors those apart.  The deterministic functional            *)
(* interpreter [exec] (RiscvExec.v) already discharges (2) by computation   *)
(* ([vm_compute]/[cbn]) -- this is the same "read-free" idea as             *)
(* [rvc_oneshot] but for the WHOLE fetch/decode/execute cycle.  We iterate  *)
(* it into [stepN], a pure block executor, so that ALL of (2) for an        *)
(* N-instruction block collapses into ONE [vm_compute] of                   *)
(* [stepN N sigma = Some sigma'].  What remains for Iris is only the cheap  *)
(* per-step boundary (1): open [mstate_interp], read the footprint values   *)
(* off the owned points-to, hand back the updated [mstate_interp].          *)
(*                                                                         *)
(* LIFTING INTO IRIS.  A single state-polymorphic one-boundary-for-the-      *)
(* whole-block rule is NOT provable: every [prim_step] ([Loop -> Loop])      *)
(* must reconstruct [state_interp] at the intermediate machine state, and   *)
(* that reconstruction needs the footprint's points-to fragments (the       *)
(* [gen_heap]/[ghost_map] authority alone cannot be updated).  What IS       *)
(* provable, by induction over the leaf rule [wp_exec_step], is the         *)
(* [Nat.iter] "telescoped" rule [wp_stepN] below: N nested per-step         *)
(* obligations whose innermost continuation is [WP Loop].  The user peels    *)
(* one layer per instruction, threading the footprint points-to through and  *)
(* projecting the single-step [exec] fact out of the one batched [stepN]     *)
(* computation.  Because the tail continuation is a plain [WP Loop], the     *)
(* rule composes with concurrent reasoning both BEFORE and AFTER the block.  *)
(* ====================================================================== *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The pure block executor.  [stepN n s] runs [n] deterministic         *)
(*    fetch-decode-execute cycles from [s]; [None] if any cycle is stuck    *)
(*    (a [Choose]/failure outcome -- i.e. genuine multi-hart nondeterminism *)
(*    or a fault -- which is exactly the boundary of a "sequential block"). *)
(* ---------------------------------------------------------------------- *)

Fixpoint stepN (n : nat) (s : mstate) : option mstate :=
  match n with
  | O => Some s
  | S k => match exec riscv_step s with
           | Some (_, s') => stepN k s'
           | None => None
           end
  end.

Lemma stepN_O s : stepN 0 s = Some s.
Proof. reflexivity. Qed.

(* Peel one instruction off the front of a proven block run: the batched
   [stepN (S k)] fact yields the head [exec] step AND the tail [stepN k].
   This is how the single [vm_compute] of the whole block is projected into
   the per-layer [exec] obligations that [wp_stepN] consumes. *)
Lemma stepN_S_inv k s s' :
  stepN (S k) s = Some s' ->
  exists s1, exec riscv_step s = Some (tt, s1) /\ stepN k s1 = Some s'.
Proof.
  cbn [stepN]. destruct (exec riscv_step s) as [[[] s1]|] eqn:E.
  - intros H. exists s1. split; [reflexivity | exact H].
  - intros H. discriminate H.
Qed.

(* [stepN] composes: n+m steps = n steps then m steps. *)
Lemma stepN_add n m s :
  stepN (n + m) s =
    match stepN n s with Some s' => stepN m s' | None => None end.
Proof.
  revert s. induction n as [|n IH]; intros s; [reflexivity|].
  cbn [stepN Nat.add]. destruct (exec riscv_step s) as [[[] s1]|]; [apply IH | reflexivity].
Qed.

Section VCGen.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---------------------------------------------------------------------- *)
  (* 2. The N-step Iris lifting rule ("telescoped" wp for a block).          *)
  (*                                                                         *)
  (*    [wp_stepN n] is the n-fold nesting of the leaf rule [wp_exec_step]    *)
  (*    with tail continuation [WP Loop].  Reading it top-down: the outermost *)
  (*    layer is the FIRST instruction; opening [mstate_interp] and supplying *)
  (*    [exec riscv_step sigma = Some (tt, sigma')] advances one cycle and     *)
  (*    hands back the updated interp together with the obligation for the    *)
  (*    REMAINING [n-1] layers; the innermost obligation is [WP Loop], i.e.    *)
  (*    the post-block continuation available to concurrent reasoning.        *)
  (* ---------------------------------------------------------------------- *)
  Lemma wp_stepN (n : nat) E Φ :
    Nat.iter n
      (fun IH : iProp Σ =>
         (∀ σ, mstate_interp σ ={E,∅}=∗
            ∃ σ', ⌜exec riscv_step σ = Some (tt, σ')⌝ ∗
               ▷ |={∅,E}=> mstate_interp σ' ∗ IH))%I
      (WP (Loop : expr riscv_lang) @ E {{ Φ }})
    ⊢ WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    induction n as [|n IH].
    - (* zero instructions: the block obligation IS the continuation. *)
      simpl. iIntros "H". iExact "H".
    - (* peel one instruction via the leaf rule, recurse on the tail. *)
      simpl Nat.iter. iIntros "H".
      iApply wp_exec_step. iIntros (σ) "Hσ".
      iMod ("H" with "Hσ") as (σ') "[%He Hk]".
      iModIntro. iExists σ'. iSplit; [done|].
      iNext. iMod "Hk" as "[Hσ' HIH]". iModIntro.
      iFrame "Hσ'". iApply IH. iExact "HIH".
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* 3. DEMO (manual).  Two facets of the design, self-contained.            *)
  (* ---------------------------------------------------------------------- *)

  (* 3a. The PURE side: one batched block run projects into the per-step      *)
  (*     [exec] facts each telescope layer needs -- this is the whole point   *)
  (*     of computing [stepN n sigma] ONCE (by [vm_compute]) instead of       *)
  (*     proving n separate single-instruction goals.                         *)
  Lemma demo_project σ0 σ3 :
    stepN 3 σ0 = Some σ3 ->
    exists σ1 σ2,
      exec riscv_step σ0 = Some (tt, σ1) /\
      exec riscv_step σ1 = Some (tt, σ2) /\
      exec riscv_step σ2 = Some (tt, σ3).
  Proof.
    intro H.
    apply stepN_S_inv in H as (σ1 & E0 & H).
    apply stepN_S_inv in H as (σ2 & E1 & H).
    apply stepN_S_inv in H as (σ3' & E2 & H).
    (* the last tail is [stepN 0 σ3' = Some σ3], i.e. σ3' = σ3 *)
    cbn [stepN] in H. injection H as <-.
    exists σ1, σ2. eauto.
  Qed.

  (* 3b. The IRIS side: a "stepper" is exactly what a single-instruction      *)
  (*     proof produces -- open [mstate_interp], exhibit the one-cycle [exec]  *)
  (*     transition (from a concrete decode/execute, e.g. [exec_riscv_step_   *)
  (*     ADD]), and hand back the [mstate_interp] of the post-state (via the   *)
  (*     footprint points-to updates).  [wp_stepN] threads N of these into a   *)
  (*     WP for the block whose tail is a plain [WP Loop], so anything (an     *)
  (*     invariant, another hart's step) can run after the block.             *)
  Definition stepper (E : coPset) (IH : iProp Σ) : iProp Σ :=
    (∀ σ, mstate_interp σ ={E,∅}=∗
       ∃ σ', ⌜exec riscv_step σ = Some (tt, σ')⌝ ∗
          ▷ |={∅,E}=> mstate_interp σ' ∗ IH)%I.

  (* A 2-instruction block: two steppers + the post-block continuation give a  *)
  (* WP for [Loop].  This is [wp_stepN 2] specialised; a real block replaces    *)
  (* each [stepper] with the concrete instruction's open/exec/reconstruct.      *)
  Lemma wp_block2 E Φ :
    stepper E (stepper E (WP (Loop : expr riscv_lang) @ E {{ Φ }}))
    ⊢ WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof. iApply (wp_stepN 2). Qed.

End VCGen.
