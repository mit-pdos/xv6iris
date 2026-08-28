(* ===================================================================== *)
(* UexecWp.v -- THE USER-EXECUTION WP the trap loop runs, as a RESOURCE:   *)
(* the forall-state form of WHAT THIS PROCESS DOES WHEN USERRET RESUMES IT. *)
(*                                                                         *)
(* See claude-notes/projects/user-wp-slot.md (SS1.1 is this file).  The     *)
(* kernel's trap loop currently runs user mode through ONE hardwired        *)
(* theorem ([SpecUser.USER.wp_user_exec_closed]).  The project makes the WP *)
(* userret runs a per-process RESOURCE, carried in the kernel-side residue  *)
(* beside [proc_priv], extracted at userret and re-deposited each round.    *)
(* This file is that resource's TYPE, and nothing else: no proof of any     *)
(* inhabitant lives here (the generic one is ProofUexecWp.v, a verified     *)
(* program's is its own file), so the residue can name the slot without     *)
(* pulling a proof tower into its build path.                              *)
(*                                                                         *)
(* THE SHAPE, and why each piece is the way it is:                         *)
(*                                                                         *)
(*   * THE RESUME STATE IS forall-BOUND AND CONCRETE, not [user_inv].  The  *)
(*     loop HOLDS the concrete state at both application sites (today it    *)
(*     weakens it into [user_inv]'s existentials to call the generic WP),   *)
(*     and a verified program's WP NEEDS the concrete state.  The generic   *)
(*     inhabitant re-packs the foralls into [user_inv] internally.          *)
(*   * THERE IS NO PIN PARAMETER, and an earlier draft's [uexec_pin] was a  *)
(*     wrong turn.  [uexec_wp] is the forall-STATE form -- happy with any   *)
(*     resume state -- which is exactly what the generic safety theorem     *)
(*     proves and what the step-1 residue conjunct is.  The PER-PROCESS     *)
(*     form is a separate, TRAPFRAME-KEYED definition ([uexec_slot V M],    *)
(*     step 2/3, not here): its precondition is fixed to the state the      *)
(*     process's own trapframe and memory-view record, so the agreement     *)
(*     with the residue's data IS the type and there is no free-standing    *)
(*     pure precondition for anyone to discharge.                           *)
(*   * [Rut] IS forall-BOUND (abstract).  Both tiers treat the parked       *)
(*     kernel residue opaquely, and that is what keeps the RESIDUE out of   *)
(*     this definition: [uexec_wp] never names the residue, so the loop's   *)
(*     instantiation of [Rut] with a bundle that itself carries a slot is   *)
(*     an ordinary application.                                             *)
(*   * HART-FREE (the [forall h : CpuId] is INSIDE), like [uv_cap] and the  *)
(*     residue transports: the process may resume on any hart, and the slot *)
(*     rides the hart-free half of the residue.                             *)
(*   * THE HANDLER PREMISE IS A RETURN CHANNEL, and it is what makes this   *)
(*     a GUARDED FIXPOINT.  The kernel re-entry contract arrives from the   *)
(*     loop's Loeb hypothesis under a later, exactly as it always did, but  *)
(*     what user execution hands BACK at its trap is now the PAIR           *)
(*                                                                          *)
(*         user_trap_frame C pt Rut  *  <the NEXT user-execution WP>        *)
(*                                                                          *)
(*     so the WP the loop resumes a process with is the one the previous    *)
(*     round RETURNED, not a freshly minted generic (MILESTONE G).  The     *)
(*     recursive occurrence sits under the handler's own [>], which is      *)
(*     precisely the guard [Contractive] wants -- so the definition is      *)
(*     [fixpoint uexec_F], on the model of [ParkCap.park_token].            *)
(*     [UserExec.stvec_handler_wp] is the UNPAIRED form and stays what the  *)
(*     safety tier (SpecUser/UserExec/ProofUser) consumes: the generic      *)
(*     inhabitant builds one out of the pair and its own Loeb hypothesis.   *)
(*                                                                         *)
(* [loop_ok] LIVES HERE, moved down from SpecUserretClosed.v (which now     *)
(* re-exports this file, so every existing consumer still sees it under the *)
(* same name): the slot's statement needs it and this file must sit BELOW   *)
(* UsertrapRes.v.  Its ingredients -- [ucfg], [proc_pt_wf], TRAMPOLINE,     *)
(* [MIE_S]/[MEDELEG_S] -- all live lower already.                           *)
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
Require Import TrampPt.     (* [TRAMPOLINE] -- the stvec value [loop_ok] pins *)
Require Import IntrDefs.    (* [MEDELEG_S] -- ditto for medeleg *)
Require Import ProcPtOwn.   (* [ud_pas] / [proc_pt_wf] -- the descriptor facts *)
Require Import UserPtTree.  (* [uptd] / [user_pt_inv] *)
Require Import UserFrame.   (* [u_regs] -- the per-step mutable cells *)
Require Import UserExec.    (* [ucfg] / [user_cfg] / [user_mstatus_ok] /
                               [user_trap_frame] *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS1 The loop-invariant shape of the config record and the descriptor.   *)
(*                                                                         *)
(* VERBATIM from SpecUserretClosed.v, which is where it used to live: the   *)
(* four config fields the loop pins (stvec at the trampoline, mie at        *)
(* [MIE_S], medeleg at [MEDELEG_S], the config fraction whole) plus the two *)
(* descriptor facts uservec's own satp switch needs.  Every round           *)
(* re-establishes it, which is what makes it a loop invariant rather than   *)
(* an assumption about the first round.                                     *)
(* ===================================================================== *)
Definition loop_ok (C : ucfg) (pt : uptd) : Prop :=
  uc_stvec C = (mword_of_int TRAMPOLINE : mword 64) /\
  uc_dqc C = DfracOwn 1 /\
  uc_mie C = MIE_S /\
  uc_medeleg C = MEDELEG_S /\
  ud_data pt = ud_pas pt /\
  proc_pt_wf pt.

(* ===================================================================== *)
(* SS2 The slot, forall-state form, AS A GUARDED FIXPOINT.                 *)
(*                                                                         *)
(* NOT inside a [CpuId] section: the hart is the FIRST forall of the body   *)
(* (see the header), so a slot in hand is good at whatever hart the process *)
(* is next scheduled on.  [GEN] stays ambient, as everywhere else.          *)
(*                                                                         *)
(* [uexec_F X] is the body with the RETURN CHANNEL at [X]; the only         *)
(* occurrence of [X] is under the handler premise's [>], so the functional  *)
(* is contractive and [fixpoint] applies ([ParkCap.park_token_F] is the     *)
(* precedent, and its file structure is copied verbatim: functional,        *)
(* [Local Instance ... Contractive], [fixpoint], unfold lemma).             *)
(* ===================================================================== *)
Section UexecWp.
  Context `{!riscvGS Σ} `{GEN : GenId}.

  Definition uexec_F (X : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
       (M : gmap Z (bv 8)) (g : regfile)
       (ms_v sc_v stval_v sepc_v va : mword 64),
       ⌜loop_ok C pt⌝ -∗
       ⌜user_mstatus_ok ms_v⌝ -∗
       hw_config (CID := h) -∗ minstret_inv -∗ wire_inv -∗
       u_regs (CID := h) (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g -∗
       user_pt_inv (CID := h) pt M -∗
       user_cfg (CID := h) C -∗
       Rut pt -∗
       (* THE TRAP SEAM, in both directions at once: the kernel promises to
          handle the trap frame, user execution promises to hand back the WP
          the NEXT round is to run.  [X] occurs nowhere else, hence the
          guard. *)
       ▷ (user_trap_frame (CID := h) C pt Rut ∗ X -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  Local Instance uexec_F_contractive : Contractive uexec_F.
  Proof. rewrite /uexec_F. solve_contractive. Qed.

  Definition uexec_wp : iProp Σ := fixpoint uexec_F.

  Lemma uexec_wp_unfold : uexec_wp ⊣⊢ uexec_F uexec_wp.
  Proof. apply (fixpoint_unfold uexec_F). Qed.

End UexecWp.

(* [u_regs] bundles [gpr_file], the [iFrame] landmine class: sealed so a
   frame against a bundle holding a slot treats it as one atom.  The seal
   does not travel -- a file that puts a slot in the intuitionistic context
   must [Require Import UexecWp] directly (durable-notes).  Consumers that
   need to SEE the body go through [uexec_wp_unfold], never [rewrite
   /uexec_wp]: the fixpoint has no unfolding of its own. *)
Global Typeclasses Opaque uexec_wp.

(* ===================================================================== *)
(* SS3 The generic inhabitant, as an interface.                            *)
(*                                                                         *)
(* [ProofUexecWp.UexecGen] proves it out of a [SpecUser.USER].  It is [box] *)
(* because its proof uses no linear hypothesis, which is what lets the      *)
(* generic slot be MINTED wherever a [UEXEC_GEN] is in scope -- and the     *)
(* tree keeps that to TWO places, both of which eliminate the [box] once    *)
(* into a linear WP a park consumes: userinit's park ([ProofUserinit], via  *)
(* [LinkUserinit]) and sys_fork's kfork call ([ProofSysFork], via           *)
(* [LinkSysFork]).  Nothing PERSISTENT carries a WP -- [SyscParkEnv.        *)
(* park_world] used to, which made one duplicable from inside every trap    *)
(* round.  See claude-notes/design/user-wp-slot.md.                         *)
(* ===================================================================== *)
Module Type UEXEC_GEN.
  Parameter uexec_wp_gen :
    forall `{!riscvGS Σ} `{GEN : GenId}, ⊢ □ uexec_wp.
End UEXEC_GEN.
