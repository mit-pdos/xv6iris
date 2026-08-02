(* CpuOwn.v -- ownership of THIS cpu's [struct cpu] plus the push/pop
   interrupt discipline, as ONE predicate.

   [cpu_own n eb p C b] owns, for the ambient CpuId:
     - the per-cpu cells and the counting token [cpu_hart n eb p]
       (IntrDefs.v):
         cpus[cid].noff  ↦₄ n     -- the CELL IS the count level, so
                                     push/pop specs need no noff argument
                                     and no level-mirror premise;
         cpus[cid].intena         -- pinned to [eb] (the saved base enable
                                     state) while n ≥ 1; arbitrary at 0;
         cpus[cid].proc  ↦₈ p     -- the current-process field;
         [intr_count n eb]        -- the SIE ghost eighth + (at n ≥ 1,
                                     eb = true) the restore payload;
     - [C], the context-slot payload for cpus[cid].context:
       [cpu_ctx_free] at boot and while the scheduler itself runs; the
       scheduler tier instantiates it with the parked scheduler
       continuation.  Functions indifferent to the slot are ∀C-parametric
       and carry it opaquely.

   THE [b] INDEX -- the SIE state of the ambient [sie_cap_gpr] this bundle
   travels beside.  At [b = true] the cells and the token are NOT here:
   they ride in [sie_arm]'s enabled arm (IntrDefs.v), because with
   interrupts enabled a trap can migrate the thread and only what a leaf's
   [wp_next] re-delivers survives the crossing.  What is left at [b = true]
   is the pure fact the arm's ghost agreement pins anyway ([n = 0] and
   [eb = true], [intr_count_get_on]) plus the caller's frame [C], which is
   an opaque [iProp Σ] and therefore crosses for free.  push_off and
   pop_off are the two functions that move the payload across this seam.

   [cpu_own 0 false p cpu_ctx_free false] is constructible from raw boot
   resources (cells + the SIE eighth at '0') -- no trap handler, no
   stvec, no trap CSRs -- which is what makes push_off/pop_off (and the
   whole acquire/release cone above them) usable during early boot,
   where both are no-ops on SIE. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang HartTp.
Require Import RegFile.   (* [regfile]: the index algebra below names the map *)
Require Import SmodeCore.
Require Import IntrDefs.
Require Import ProcGeom.
Local Open Scope Z_scope.

Section CpuOwn.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Definition cpu_own (n : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (b : bool) : iProp Σ :=
    ((if b then ⌜ n = 0%nat /\ eb = true ⌝ else cpu_hart n eb p) ∗ C)%I.

  (* at the disabled index the bundle IS the cells + the token + the slot *)
  Lemma cpu_own_off (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :
    cpu_own n eb p C false ⊣⊢ cpu_hart n eb p ∗ C.
  Proof. reflexivity. Qed.

  (* ... and at the enabled index it is the pure fact plus the frame: the
     payload is inside [sie_arm true p].  This is not a weakening -- a
     caller could not have HELD the cells there anyway ([cpu_own_arm_excl]
     below refutes it), because the arm already owns them. *)
  Lemma cpu_own_on (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :
    cpu_own n eb p C true ⊣⊢ ⌜ n = 0%nat /\ eb = true ⌝ ∗ C.
  Proof. reflexivity. Qed.

  Lemma cpu_own_on_intro (p : mword 64) (C : iProp Σ) :
    C -∗ cpu_own 0 true p C true.
  Proof. iIntros "HC". iFrame "HC". iPureIntro. done. Qed.

  (* THE MOVE push_off makes at the enabled arm, and pop_off's inverse. *)
  Lemma cpu_own_of_arm (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :
    cpu_own n eb p C true -∗
    cpu_hart 0 true p -∗
    cpu_own 0 true p C false.
  Proof. iIntros "[_ HC] Hh". iFrame. Qed.

  Lemma cpu_own_to_arm (p : mword 64) (C : iProp Σ) :
    cpu_own 0 true p C false -∗
    cpu_hart 0 true p ∗ cpu_own 0 true p C true.
  Proof. iIntros "[Hh HC]". iFrame "Hh HC". iPureIntro. done. Qed.

  (* the cells are EXCLUSIVE, so nobody holds them beside the enabled arm *)
  Lemma cpu_hart_excl (n n' : nat) (eb eb' : bool) (p p' : mword 64) :
    cpu_hart n eb p -∗ cpu_hart n' eb' p' -∗ False.
  Proof.
    iIntros "((_ & Hn & _ & _) & _) ((_ & Hn' & _ & _) & _)".
    iDestruct (word4_pointsto_bytes with "Hn") as "Hb".
    iDestruct (word4_pointsto_bytes with "Hn'") as "Hb'".
    cbn [seq]. iDestruct "Hb" as "[H0 _]". iDestruct "Hb'" as "[H0' _]".
    iDestruct (mem_pointsto_ne with "H0 H0'") as %Hne. done.
  Qed.

  Lemma cpu_own_arm_excl (n n' : nat) (eb eb' : bool) (p p' : mword 64)
      (C : iProp Σ) :
    sie_arm true p -∗ cpu_own n' eb' p' C false -∗ False.
  Proof.
    iIntros "(_ & _ & _ & _ & _ & Hh) [Hh' _]".
    iApply (cpu_hart_excl with "Hh Hh'").
  Qed.

  (* ===================================================================== *)
  (* THE INDEX ALGEBRA -- DERIVE the ambient SIE index, never state it.     *)
  (*                                                                        *)
  (* [b] (the index of the ambient [sie_cap_gpr]) and the [(n, eb)] pair    *)
  (* this bundle carries are NOT independent: they are tied by ghost        *)
  (* agreement between [sie_arm]'s eighth and [intr_count]'s complementary  *)
  (* eighth, into exactly the expression every level-generic callee spells  *)
  (* as its EXIT index, [match n with O => eb | S _ => false end].  So a    *)
  (* contract that threads a plain [b] through a lock-holding function is   *)
  (* not necessarily a bug -- check whether the derivation closes first.    *)
  (*                                                                        *)
  (* These live HERE, beside the resources they are about, because a        *)
  (* whole-function [Proof*.v] may not [Require] another one and six of     *)
  (* them had independently hand-rolled the same three lines.  The three    *)
  (* facts are: the enabled base FORCES [b = true] at level 0; a level      *)
  (* above 0 is outright incompatible with the enabled index; and the       *)
  (* general agreement the other two specialize.                            *)
  (* ===================================================================== *)

  (* THE GENERAL FACT.  At [b = true] the bundle's own shape already packs
     [n = 0 /\ eb = true].  At [b = false] with [n = 0], [sie_arm false p]'s
     eighth (at '0') and [intr_count 0 eb]'s complementary eighth (at
     [sie_bit eb]) are eighths of the SAME ghost var, so agreement pins
     [eb = false].  At [b = false] with [n = S _] the match is [false]
     unconditionally and there is nothing to derive. *)
  Lemma cpu_own_eb_agree (m : regfile) (K : nat) (n : nat) (eb : bool)
      (p : mword 64) (C : iProp Σ) (b : bool) :
    sie_cap_gpr m K b p -∗ cpu_own n eb p C b -∗
    ⌜ match n with O => eb | S _ => false end = b ⌝.
  Proof.
    iIntros "Hcg Hown". destruct b.
    - iDestruct "Hown" as "[%Hpure _]". iPureIntro. destruct Hpure as [-> ->]. done.
    - iDestruct "Hown" as "[Hh _]". iDestruct "Hh" as "[_ Hic]".
      destruct n as [|n'].
      + iDestruct (sie_cap_gpr_split with "Hcg") as "(_ & _ & Hsie & _)".
        iDestruct "Hsie" as "(_ & _ & Hbit)".
        destruct eb.
        * iDestruct (ghost_var_agree with "Hbit Hic") as %Hbad.
          exfalso. apply (f_equal (@bv_unsigned _)) in Hbad.
          vm_compute in Hbad. discriminate.
        * iPureIntro. reflexivity.
      + iPureIntro. reflexivity.
  Qed.

  (* AN ENABLED BASE AT LEVEL 0 FORCES THE ENABLED INDEX.  This is what makes
     "state the contract at [b = false]" a VACUITY rather than a weakening for
     every level-0/enabled-base contract: there is no [b = false] instance. *)
  Lemma cpu_own_forces_on (m : regfile) (K : nat) (p : mword 64)
      (C : iProp Σ) (b : bool) :
    sie_cap_gpr m K b p -∗ cpu_own 0 true p C b -∗ ⌜ b = true ⌝.
  Proof.
    destruct b; [ by iIntros "_ _" |].
    iIntros "Hcg Hown".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbad.
    cbn in Hbad. discriminate Hbad.
  Qed.

  (* ... and the dual, which needs no capability at all: the enabled index's
     own arm carries [⌜n = 0⌝]. *)
  Lemma cpu_own_forces_off (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :
    cpu_own (S n) eb p C true -∗ False.
  Proof.
    iIntros "[%Hpure _]". destruct Hpure as [Hn _]. discriminate Hn.
  Qed.

  (* boot entry: raw cells + the SIE eighth at '0'.  [iv] arbitrary. *)
  Lemma cpu_own_init_boot (p : mword 64) (nv iv : mword 32)
      (C : iProp Σ) :
    nv = noff_val 0 ->
    a_cpu_noff cid_word ↦₄ nv -∗
    a_cpu_int cid_word ↦₄ iv -∗
    intr_off_tok -∗
    a_cpu_proc cid_word ↦₈ p -∗
    C -∗
    cpu_own 0 false p C false.
  Proof.
    intros ->. iIntros "Hnoff Hint Htok Hproc HC".
    iFrame "HC".
    iSplitR "Htok"; [| iApply (intr_count_init_off with "Htok") ].
    iSplitR. { iPureIntro. vm_compute. reflexivity. }
    iFrame "Hnoff Hproc". iExists iv. iExact "Hint".
  Qed.

  (* swap the context-slot payload (e.g. park / unpark the scheduler
     continuation) without disturbing the rest.  Index-generic: [C] is a
     frame at either arm. *)
  Lemma cpu_own_ctx_swap (n : nat) (eb : bool) (p : mword 64)
      (C C' : iProp Σ) (b : bool) :
    cpu_own n eb p C b -∗ (C -∗ C') -∗ cpu_own n eb p C' b.
  Proof.
    iIntros "[Hrest HC] HW". iFrame "Hrest". iApply ("HW" with "HC").
  Qed.

  (* retarget the proc field (the scheduler's c->proc writes).  Only at the
     DISABLED index: c->proc is written under a held lock, hence at level
     ≥ 1, hence with interrupts off. *)
  Lemma cpu_own_set_proc (n : nat) (eb : bool)
      (p p' : mword 64) (C : iProp Σ) :
    cpu_own n eb p C false -∗
    (a_cpu_proc cid_word ↦₈ p ∗
     (a_cpu_proc cid_word ↦₈ p' -∗ cpu_own n eb p' C false)).
  Proof.
    iIntros "(((%Hbound & Hnoff & Hint & Hproc) & Hcnt) & HC)".
    iFrame "Hproc". iIntros "Hproc". iFrame "Hnoff Hint Hcnt HC Hproc".
    iPureIntro. exact Hbound.
  Qed.

End CpuOwn.

(* ===================================================================== *)
(* THE HART TRANSPORT -- what makes a [b]-GENERIC consumer able to carry  *)
(* this bundle across an interrupts-possibly-enabled instruction.         *)
(*                                                                        *)
(* A leaf's [wp_next] hands back a FRESH hart and re-delivers only         *)
(* [sie_cap_gpr] there; a caller-held hart-indexed resource is stranded    *)
(* at the entry hart.  [cpu_own] escapes because it is hart-indexed only   *)
(* at [b = false] -- at [b = true] the hart-indexed payload has moved      *)
(* into [sie_arm], leaving a pure fact and the caller's own frame [C].     *)
(* So the two arms are discharged by the two halves of what a step         *)
(* actually gives you: at [b = true] by CONVERSION (there is no hart in    *)
(* the term), at [b = false] by [wp_next]'s conditional equality.  Chain   *)
(* the per-step equalities with [wp_next_chain] and apply this once.       *)
(* ===================================================================== *)
Lemma cpu_own_transport `{!riscvGS Σ} `{!sieG Σ}
    (CID0 CID1 : CpuId) (n : nat) (eb : bool) (p : mword 64)
    (C : iProp Σ) (b : bool) :
  (b = false \/ p = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
  cpu_own (CID := CID0) n eb p C b -∗ cpu_own (CID := CID1) n eb p C b.
Proof.
  intros Heq. destruct b.
  - (* enabled: the payload is in [sie_arm], nothing here mentions the hart *)
    iIntros "H". iExact "H".
  - (* disabled: no trap was taken, so the hart did not move *)
    rewrite (_ : CID1 = CID0); [ iIntros "$" | exact (Heq (or_introl eq_refl)) ].
Qed.
