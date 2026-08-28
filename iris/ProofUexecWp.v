(* ===================================================================== *)
(* ProofUexecWp.v -- THE GENERIC INHABITANT of the user-execution WP slot. *)
(*                                                                         *)
(* See claude-notes/projects/user-wp-slot.md SS1.2.  [UexecWp.v] gives the  *)
(* slot's SHAPE; this file gives the one inhabitant that always exists:     *)
(* generic safety of arbitrary user-mode execution, repackaged so that the  *)
(* residue can carry it as a per-process resource.  [uexec_wp] is the       *)
(* forall-STATE form, which is precisely the form generic safety has: it    *)
(* accepts WHATEVER state userret resumes the process at.  (A verified      *)
(* program inhabits the trapframe-keyed form instead -- step 2/3, and not   *)
(* this file.)                                                             *)
(*                                                                         *)
(* The whole content is a REPACKAGING, and that is the point.  The slot     *)
(* hands over the resume state CONCRETE (hart ACTIVE, a named mstatus /     *)
(* trap-CSR / pc / register file, a named memory image [M]); [SpecUser]'s   *)
(* WP wants it weakened into [user_inv]'s existentials.  So the proof is    *)
(* exactly the [user_inv] construction that ProofUserretClosed's loop used  *)
(* to perform at its call site, moved HERE -- which is what lets the two    *)
(* call sites (the loop and the forkret entry) stop naming [USER] at all    *)
(* and simply APPLY whatever slot they were handed.                        *)
(*                                                                         *)
(* ...AND A Loeb, since MILESTONE G: [uexec_wp] is a guarded fixpoint whose *)
(* handler premise RETURNS the next round's WP, so the generic inhabitant   *)
(* has to say what it returns, and what it returns is ITSELF: generic       *)
(* safety, again, forever.  Mechanically: [iLoeb] gives [> box uexec_wp],   *)
(* the paired handler gives [> (frame * uexec_wp -* WP)], and the OLD-shape *)
(* [stvec_handler_wp] the safety theorem still wants is built by combining  *)
(* the two UNDER ONE LATER.  The safety tier (SpecUser/UserExec/ProofUser)  *)
(* is untouched by any of this: it never sees the return channel.           *)
(*                                                                         *)
(* [box]: no linear hypothesis is consumed, so the generic slot can be      *)
(* minted anywhere a [UEXEC_GEN] is in scope.  Consumers that already hold  *)
(* a [US : USER] derive it inline ([Module UG := UexecGen US.]) -- no new   *)
(* functor arguments on the existing compositions.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv WireInv.
Require Import UserPtTree UserFrame UserExec.
Require Import UexecWp.
Require Import SpecUser.
Local Open Scope Z_scope.
Import Defs.

Module UexecGen (US : USER) : UEXEC_GEN.

Section ProofUexecWp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Theorem uexec_wp_gen : ⊢ □ uexec_wp.
  Proof.
    (* the WP this slot RETURNS at every trap is this slot: the Löb
       hypothesis is both the recursion and the return value. *)
    iLöb as "IH".
    iModIntro.
    (* [iEval], not a bare [rewrite]: the latter would rewrite the proofmode
       context too and unfold [IH] -- which has to stay AT [uexec_wp], since
       that is what it is handed back as. *)
    iEval (rewrite uexec_wp_unfold /uexec_F).
    iIntros (h C pt Rut M g ms_v sc_v stval_v sepc_v va).
    iIntros (Hok Hms) "Hhw Hmin Hwire Hregs Hpt Hcfg Hrut Hh".
    (* THE OLD-SHAPE HANDLER, out of the PAIRED one: the safety theorem
       below takes [▷ stvec_handler_wp], i.e. "hand me a trap frame and I
       run forever", and what this slot was given is "hand me a trap frame
       AND the next WP".  The missing half is [IH], which lives under the
       same later -- so one [iNext] strips both and the two compose. *)
    iAssert (▷ stvec_handler_wp (CID := h) C pt Rut)%I
      with "[Hh]" as "Hhandler".
    { iNext. rewrite /stvec_handler_wp. iIntros "Hframe".
      iApply "Hh". iSplitL "Hframe"; [iExact "Hframe" | iExact "IH"]. }
    iApply (US.wp_user_exec_closed (CID := h) C pt Rut
              with "Hhw Hmin Hwire [Hregs Hpt Hcfg Hrut] Hhandler").
    (* the concrete state, packed into the loop invariant: the hart is
       ACTIVE (so [user_hart_ok] is [I] and the PC/nextPC lock-step fact is
       [va' = va] by construction), the mstatus pins come straight from the
       slot's own premise, and the pinned image [M] is forgotten -- which is
       precisely the information a GENERIC inhabitant may throw away and a
       verified program may not. *)
    iExists (HART_ACTIVE tt), ms_v, sc_v, stval_v, sepc_v, va, va, g.
    iSplitR; [ iPureIntro; exact I | ].
    iSplitR; [ iPureIntro; exact Hms | ].
    iSplitR; [ iPureIntro; intros u _; reflexivity | ].
    (* [user_regs] IS [u_regs] (UserExec.v defines it as the alias), so the
       slot's bundle goes straight across. *)
    iSplitL "Hregs"; [ rewrite /user_regs; iExact "Hregs" | ].
    iSplitL "Hpt"; [ iApply (user_pt_any_intro pt M with "Hpt") | ].
    iSplitL "Hcfg"; [ iExact "Hcfg" | ].
    iExact "Hrut".
  Qed.

End ProofUexecWp.

End UexecGen.
