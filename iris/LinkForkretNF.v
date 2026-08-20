(* LinkForkretNF.v -- forkret's contract WITHOUT the [first] premise,
   ASSUMED.  This is the one thing [ProofForkretPark.v] is a functor over,
   and the only new assumption the park argument adds.

   WHY IT IS NOT [LinkForkret.Forkret].  [ProofForkret.v] proves forkret on
   the already-booted path, i.e. from a DISCARDED [first_addr ↦₄ 0]
   ([SpecForkret.v]'s header argues that premise at length).  The park
   argument cannot pay it: [SchedCtx.proc_ctx] is resumed by whichever hart's
   scheduler picks the process up, and neither that scheduler nor the kfork
   that created the process holds any claim on the boot client's one-shot --
   the premise is a fact about the FIRST process ever scheduled, and a fresh
   one inherits nothing from it.  Threading a discarded points-to into every
   [proc_ctx] would put the boot client's premise inside the scheduler
   protocol, which is exactly where it does not belong.

   So the park argument is written against [SpecForkret.wp_forkret_nf_body],
   the same statement with that one premise dropped, and this file assumes
   it.  [SpecForkret.wp_forkret_body_of_nf] is the mechanical check that this
   is a STRENGTHENING of the proven contract rather than a different one:
   the proven theorem follows from this Axiom.

   WHAT DISCHARGES IT: the [if (first)] arm -- fsinit + kexec + the panic
   tail, plus the one-shot ghost that refutes the branch on every later
   entry.  claude-notes/projects/uservec.md is the tracker.  When that lands,
   [ProofForkret.v] proves [wp_forkret_nf_body] directly, this file becomes
   [Module ForkretNF := ForkretProof ...], and nothing about
   [ProofForkretPark.v] changes.

   ONE THING THAT PROOF MAY WANT AND THIS STATEMENT DOES NOT GIVE IT: the
   taken arm calls fsinit and kexec, whose environment (the block layer, the
   log, the icache) forkret holds only INSIDE the residue closer, i.e. only
   as something it can produce at the END.  If the arm's proof needs those
   resources up front, this contract grows a premise -- and so, one tier up,
   does [SpecForkretParkPaid.forkret_park_pkg].  The park argument is
   unaffected either way: it threads whatever forkret's precondition is.

   Written with an explicit [Axiom] rather than a [Declare Module] for the
   reason [LinkForkretPark.v] and [LinkIput.v] give: [Print Assumptions] sees
   either, but only the [Axiom] keyword is visible to
   [tools/proof_coverage.py]'s textual scan. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock.
Require Import FdSlots FileInvDefs.
Require Import IrefSlots InodeRegion ProcAvail.
Require Import IrefSlots.
Require Import ProcDefs.
Require Import UserPtTree.
Require Import DiskPtsto WpUart FsBlocks LogInv FsCrash KallocInv BioDefs.
Require Import SpecForkret.
Require Import LinkUserretClosed.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

(* The Axiom is stated at the CLOSED trap loop's residue -- the same
   [usertrap_res_bare] [LinkForkret.v] instantiates the real proof at -- or
   the two contracts would be about different bundles. *)
Axiom wp_forkret_nf_ax :
  forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (pt : uptd) (j : nat)
    (γl γf : gname) (s : string) (Rlk : iProp Σ)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool),
    wp_forkret_nf_body
      (fun h : CpuId => UserretClosedD.usertrap_res_bare (CID := h))
      pt j γl γf s Rlk pid V ks m av av2 eb.

Module ForkretNF : FORKRET_NF.
  (* the residue is re-exported inside a Section for the reason
     [ProofForkret.v]'s own [Section Res] is one: the module type's
     parameters carry fifteen implicit ghost-state arguments, and only a
     Context can resolve them. *)
  Section Res.
    Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
    Context `{GEN : GenId} `{CID : CpuId}.

    Definition usertrap_res := UserretClosedD.usertrap_res.
    Definition usertrap_res_parked := UserretClosedD.usertrap_res_parked.
    Definition usertrap_res_tlb_close := UserretClosedD.usertrap_res_tlb_close.
    Definition usertrap_res_tlb_open := UserretClosedD.usertrap_res_tlb_open.
    Definition usertrap_res_bare := UserretClosedD.usertrap_res_bare.
    Definition usertrap_res_pt_close := UserretClosedD.usertrap_res_pt_close.
    Definition usertrap_res_pt_open := UserretClosedD.usertrap_res_pt_open.
    Definition usertrap_res_bare_norm := UserretClosedD.usertrap_res_bare_norm.
    Definition usertrap_res_csrs_open := UserretClosedD.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := UserretClosedD.usertrap_res_sstc.
    Definition usertrap_res_tf_csrs_open := UserretClosedD.usertrap_res_tf_csrs_open.
    Definition usertrap_res_tf_open := UserretClosedD.usertrap_res_tf_open.
  End Res.

  Definition wp_forkret_nf := @wp_forkret_nf_ax.
End ForkretNF.
