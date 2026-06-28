(* MinstretInv.v -- put the retired-instruction counter [minstret] and its
   per-cycle increment flag [minstret_increment] into ONE Iris invariant, and
   provide the leaf-WP step rule [wp_exec_step_minstret] that OPENS that
   invariant across the single instruction step in order to read/bump them.

   Motivation: every instruction step writes both registers
   (minstret_increment := b; minstret += b), so today every leaf WP must take
   the two points-to in its precondition and hand them back (bumped) in its
   postcondition -- they are threaded linearly through the entire boot proof.
   Their *values* are never actually inspected by callers (minstret is just a
   counter), so we move them into an invariant whose body pins NEITHER value.
   The invariant is then persistent (duplicable): a leaf only needs [minstret_inv]
   (shareable) instead of the two owned cells, and obtains the cells transiently
   by opening the invariant for the duration of the step. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec.
Local Open Scope Z_scope.

Section MinstretInv.
  Context `{!riscvGS Σ}.

  Definition minstretN : namespace := nroot .@ "minstret".

  (* Value-agnostic ownership of the two counter cells.  Because it quantifies
     [mst]/[mi] existentially, re-establishing it after a step (with the bumped
     values) is trivial, which is precisely what makes the invariant duplicable. *)
  Definition minstret_inv_body : iProp Σ :=
    (∃ (mst : mword 64) (mi : bool),
       minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi)%I.

  Definition minstret_inv : iProp Σ := inv minstretN minstret_inv_body.

  Global Instance minstret_inv_persistent : Persistent minstret_inv.
  Proof. apply _. Qed.

  (* Allocate the invariant once (e.g. during boot setup) from the owned cells. *)
  Lemma minstret_inv_alloc (mst : mword 64) (mi : bool) E :
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ mi ={E}=∗ minstret_inv.
  Proof.
    iIntros "Hmst Hmi". iApply inv_alloc. iNext.
    iExists mst, mi. iFrame.
  Qed.

  (* A CONVENIENCE step rule for leaves that need the two counter cells: it just
     [iInv]s [minstret_inv] on top of the general [wp_exec_step_fupd], so a leaf
     gets [minstret_inv_body] for the step and hands a fresh body back -- without
     repeating the invariant-opening boilerplate.  Nothing here is minstret-
     specific beyond the namespace; any invariant can be opened the same way by
     calling [wp_exec_step_fupd] directly (see the comment on it in RiscvExec.v).

     The obligation must:
       - produce the next state [σ'] and the exec witness (state [σ'] via
         [register_lookup minstret σ.(sregs)], a function of σ -- so the cells are
         NOT needed for the witness, only for the post-step [state_interp] update);
       - then, working at mask [E∖N], fold the minstret bump into [state_interp σ']
         and return a fresh [minstret_inv_body] to close the invariant. *)
  Lemma wp_exec_step_minstret E Φ :
    ↑minstretN ⊆ E →
    minstret_inv -∗
    (∀ σ ns κs nt, state_interp σ ns κs nt -∗ minstret_inv_body -∗
       ∃ σ', ⌜exec riscv_step σ = Some (tt, σ')⌝ ∗
          ▷ |={E ∖ ↑minstretN, E ∖ ↑minstretN}=>
               (state_interp σ' (S ns) κs nt ∗ minstret_inv_body ∗
                WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN) "#Hinv H".
    iApply (wp_exec_step_fupd E (E ∖ ↑minstretN)).
    iIntros (σ ns κs nt) "Hsi".
    (* open the invariant; this IS the [={E, E∖N}] move the obligation demands *)
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct ("H" $! σ ns κs nt with "Hsi Hbody") as (σ') "[%Hexec Hk]".
    iModIntro. iExists σ'. iSplit; first done.
    iNext.
    iMod "Hk" as "(Hsi' & Hbody' & HWP)".
    iMod ("Hclose" with "[$Hbody']") as "_".
    iModIntro. iFrame.
  Qed.

End MinstretInv.
