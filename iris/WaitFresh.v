(* WaitFresh.v -- ONE reading of the wait-lock invariant: a generation that
   occupies NO slot is in NOBODY's children row.

   THE QUESTION THIS ANSWERS.  kfork, at [np->parent = p] (+0xd4 of kfork,
   [ProofKforkB5]), inserts the child's generation into the forking
   process's row.  The row's set GROWS -- [WaitInv.children_own_upd] is a
   plain ghost update and takes no freshness -- so the answer fork hands
   its parent says only [cs' = cs ∪ {[γ]}], which is satisfied by a [γ]
   that was already there.  A parent that forks twice from an empty set
   cannot then tell its two children apart: at [γ1 = γ2] the set after
   both forks is a singleton, the first reap empties it and the second
   wait's [-1] arm is consistent.  (Design app-pipe SS4.3x.  The gap is
   CLOSED above this file since SS4.3y relayed the conjunct through the sh
   tier: [UShPipeAssembly.ush_fork_ans_grows] is the refutation at sh's
   own row, and [ufork_ans_sets_differ] at [UexecRet.ufork_ans].)

   WHY THE INVARIANT ALREADY KNOWS.  [WaitInv.inv_rows] is the row
   converse: a generation in a row is the CURRENT generation of an
   OCCUPIED slot whose parent cell holds that row's address.  The child's
   generation is at no occupied slot -- [WaitInv.gen_halves_gen_uniq]
   against the fresh [ChildTok.gen_slot] says every occupied slot carrying
   it is the child's own, and the child's slot's parent cell still reads
   0.  So the two together refute membership.

   THE ONE PREMISE THAT IS NOT FREE is [pa <> zero_reg], the ROW OWNER'S
   address.  Every tie of the wait-lock invariant is guarded on a nonzero
   address (WaitInv.v's header says why: it is what keeps kfork's and
   reparent's writes premise-free), so at [pa = 0] the row's members are
   constrained by nothing and [g ∉ cs] is simply FALSE.  kfork's park
   block is stated at an opaque [pme] and did not carry the fact; lane
   PIPE-GEN buys it as a premise of [SpecKfork.wp_kfork_sconf_body],
   discharged at the dispatcher, where the running process's address IS
   [ProcGeom.proc_addr j] ([ProofSyscall]'s [sysc_proc_ties]).

   A LEAF FILE rather than a lemma inside [WaitInv.v]: the change is
   additive and WaitInv sits near the bottom of the tree (durable-notes,
   "put an ADDITIVE change to a shared invariant file in a NEW leaf
   file"). *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import CtxIdDefs.
Require Import ProcGeom.   (* [proc_addr] / [proc_addr_inj] *)
Require Import ChildTok.   (* [gen_slot] *)
Require Import Xv6Cameras. (* [wchG] -- the children map's camera *)
Require Import WaitInv.
Local Open Scope Z_scope.

Section WaitFresh.
  Context `{!riscvGS Σ}.
  Context `{!wchG Σ}.
  Context `{!ctokG Σ}.
  Context `{XI : CurCtx}.

  (* THE PROBE (design app-pipe SS4.3x (i)).  A generation whose slot's
     parent cell still reads 0 is in no row of the map -- in particular not
     in the row of the process that is about to become its parent, which is
     what makes fork's set union a GROWTH by one. *)
  Lemma children_inv_row_fresh (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map)
      (j : nat) (pa : mword 64) (g γ0 : gname) (cs : gset gname) :
    ps !! j = Some (zero_reg : mword 64) ->
    m !! γ0 = Some (pa, cs) ->
    (* THE PREMISE THE PARK BLOCK HAD TO BUY: the row owner's address.  At
       [pa = 0] every tie about the row is guarded away and the conclusion
       is false. *)
    pa <> (zero_reg : mword 64) ->
    children_inv ps gs m O -∗
    gen_slot g (proc_addr j) -∗
    ⌜ g ∉ cs ⌝.
  Proof using .
    intros Hj Hm Hpa. rewrite /children_inv /children_inv_at.
    iIntros "(Hgh & %Hp & _) #Hgs".
    destruct Hp as (Hlps & _ & _ & _ & Hir & _ & _).
    iDestruct (gen_halves_gen_uniq with "Hgh Hgs") as %Huniq.
    iPureIntro. intro Hin.
    destruct (Hir γ0 pa cs g Hm Hpa Hin) as (k & Hk & Hgk).
    assert (Hkb : (k < NPROC)%nat)
      by (rewrite -Hlps; eapply lookup_lt_Some; exact Hk).
    assert (Hjb : (j < NPROC)%nat)
      by (rewrite -Hlps; eapply lookup_lt_Some; exact Hj).
    assert (Hpk : proc_addr k = proc_addr j) by exact (Huniq k pa Hk Hpa Hgk).
    assert (Hkj : k = j) by exact (proc_addr_inj k j Hkb Hjb Hpk).
    subst k. rewrite Hj in Hk.
    assert (Hz : pa = (zero_reg : mword 64)) by congruence.
    exact (Hpa Hz).
  Qed.

End WaitFresh.
