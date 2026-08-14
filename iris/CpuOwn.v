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
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition cpu_own (n : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (b : bool) (lks : gset nat) : iProp Σ :=
    ((if b then ⌜ n = 0%nat /\ eb = true /\ lks = ∅ ⌝ else cpu_hart n eb p lks) ∗ C)%I.

  (* at the disabled index the bundle IS the cells + the token + the slot *)
  Lemma cpu_own_off (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (lks : gset nat) :
    cpu_own n eb p C false lks ⊣⊢ cpu_hart n eb p lks ∗ C.
  Proof. reflexivity. Qed.

  (* ... and at the enabled index it is the pure fact plus the frame: the
     payload is inside [sie_arm true p].  This is not a weakening -- a
     caller could not have HELD the cells there anyway ([cpu_own_arm_excl]
     below refutes it), because the arm already owns them. *)
  (* THE THEOREM THE WHOLE ABSTRACTION EXISTS FOR is the [lks = ∅] conjunct:
     a hart with interrupts ENABLED holds no spinlock. *)
  Lemma cpu_own_on (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (lks : gset nat) :
    cpu_own n eb p C true lks ⊣⊢ ⌜ n = 0%nat /\ eb = true /\ lks = ∅ ⌝ ∗ C.
  Proof. reflexivity. Qed.

  Lemma cpu_own_on_intro (p : mword 64) (C : iProp Σ) :
    C -∗ cpu_own 0 true p C true ∅.
  Proof. iIntros "HC". iFrame "HC". iPureIntro. done. Qed.

  (* THE MOVE push_off makes at the enabled arm, and pop_off's inverse. *)
  Lemma cpu_own_of_arm (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (lks : gset nat) :
    cpu_own n eb p C true lks -∗
    cpu_hart 0 true p ∅ -∗
    cpu_own 0 true p C false ∅.
  Proof. iIntros "[_ HC] Hh". iFrame. Qed.

  Lemma cpu_own_to_arm (p : mword 64) (C : iProp Σ) :
    cpu_own 0 true p C false ∅ -∗
    cpu_hart 0 true p ∅ ∗ cpu_own 0 true p C true ∅.
  Proof. iIntros "[Hh HC]". iFrame "Hh HC". iPureIntro. done. Qed.

  (* the cells are EXCLUSIVE, so nobody holds them beside the enabled arm *)
  Lemma cpu_hart_excl (n n' : nat) (eb eb' : bool) (p p' : mword 64)
      (lks lks' : gset nat) :
    cpu_hart n eb p lks -∗ cpu_hart n' eb' p' lks' -∗ False.
  Proof.
    iIntros "(((_ & Hn & _ & _) & _) & _) (((_ & Hn' & _ & _) & _) & _)".
    iDestruct (word4_pointsto_bytes with "Hn") as "Hb".
    iDestruct (word4_pointsto_bytes with "Hn'") as "Hb'".
    cbn [seq]. iDestruct "Hb" as "[H0 _]". iDestruct "Hb'" as "[H0' _]".
    iDestruct (mem_pointsto_ne with "H0 H0'") as %Hne. done.
  Qed.

  Lemma cpu_own_arm_excl (n n' : nat) (eb eb' : bool) (p p' : mword 64)
      (C : iProp Σ) (lks : gset nat) :
    sie_arm true p -∗ cpu_own n' eb' p' C false lks -∗ False.
  Proof.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & Hh) [Hh' _]".
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
      (p : mword 64) (C : iProp Σ) (b : bool) {lks : gset nat} :
    sie_cap_gpr m K b p -∗ cpu_own n eb p C b lks -∗
    ⌜ match n with O => eb | S _ => false end = b ⌝.
  Proof.
    iIntros "Hcg Hown". destruct b.
    - iDestruct "Hown" as "[%Hpure _]". iPureIntro. destruct Hpure as (-> & -> & _). done.
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
      (C : iProp Σ) (b : bool) {lks : gset nat} :
    sie_cap_gpr m K b p -∗ cpu_own 0 true p C b lks -∗ ⌜ b = true ⌝.
  Proof.
    destruct b; [ by iIntros "_ _" |].
    iIntros "Hcg Hown".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbad.
    cbn in Hbad. discriminate Hbad.
  Qed.

  (* ... and the dual, which needs no capability at all: the enabled index's
     own arm carries [⌜n = 0⌝]. *)
  Lemma cpu_own_forces_off (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (lks : gset nat) :
    cpu_own (S n) eb p C true lks -∗ False.
  Proof.
    iIntros "[%Hpure _]". destruct Hpure as [Hn _]. discriminate Hn.
  Qed.

  (* boot entry: raw cells + the SIE eighth at '0' + this hart's held-lock
     authority, which adequacy mints at the EMPTY set (a hart that has not
     run an instruction holds no locks).  [iv] arbitrary. *)
  Lemma cpu_own_init_boot (p : mword 64) (nv iv : mword 32)
      (C : iProp Σ) :
    nv = noff_val 0 ->
    a_cpu_noff cid_word ↦₄ nv -∗
    a_cpu_int cid_word ↦₄ iv -∗
    intr_off_tok -∗
    cur_proc p -∗
    lk_auth cpu_id ∅ -∗
    C -∗
    cpu_own 0 false p C false ∅.
  Proof.
    intros ->. iIntros "Hnoff Hint Htok Hproc Hlk HC".
    iFrame "HC".
    iSplitR "Htok"; [| iApply (intr_count_init_off with "Htok") ].
    iSplitR "Hlk";
      [| iApply (cpu_locks_lvl_intro 0 ∅); [ rewrite size_empty; lia
         | iApply (cpu_locks_intro_empty with "Hlk") ] ].
    iSplitR. { iPureIntro. vm_compute. reflexivity. }
    iFrame "Hnoff Hproc". iExists iv. iExact "Hint".
  Qed.

  (* ===================================================================== *)
  (* THE HELD-LOCK SET, NAMED.  The index-aware replacement for the old      *)
  (* [cpu_own_locks_acc], which handed out an EXISTENTIAL set because the    *)
  (* set was hidden inside [cpu_hart].  Now the caller already knows [lks];  *)
  (* what it needs is to take the authority out, hand it to the cpu-field    *)
  (* store leaf, and put back the set that leaf returns -- so this SWAPS     *)
  (* rather than restores.                                                   *)
  (*                                                                         *)
  (* Only at [b = false], which is not a restriction: a lock is taken and    *)
  (* released with interrupts off, and the [b = true] arm forces [lks = ∅]   *)
  (* anyway.                                                                 *)
  (* ===================================================================== *)
  (* PEEK at the level/set coupling without consuming the bundle.  acquire
     needs its ENTRY bound: after push_off the bundle sits at [S n] and only
     offers [size lks <= S n], which is one too weak to add a rank
     ([size ({[r]} ∪ lks) = S (size lks)], so the insert wants [size lks <= n]).
     The fact is pure, so extracting it before the push and carrying it across
     is enough -- both arms supply it, the enabled one because it forces
     [lks = ∅]. *)
  Lemma cpu_own_size_le (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (b : bool) (lks : gset nat) :
    cpu_own n eb p C b lks -∗ ⌜(size lks <= n)%nat⌝ ∗ cpu_own n eb p C b lks.
  Proof.
    destruct b.
    - iIntros "[%Hp HC]". destruct Hp as (Hn & Heb & Hl).
      iSplitR. { iPureIntro. subst lks. rewrite size_empty. lia. }
      iFrame "HC". iPureIntro. done.
    - iIntros "[Hh HC]".
      iEval (rewrite /cpu_hart /cpu_priv) in "Hh".
      iDestruct "Hh" as "((Hcells & Hlvl) & Hcnt)".
      iDestruct (cpu_locks_lvl_elim with "Hlvl") as "[Hlks %Hsz]".
      iSplitR; [ iPureIntro; exact Hsz | ].
      iFrame "HC". rewrite /cpu_hart /cpu_priv. iFrame "Hcells Hcnt".
      iApply (cpu_locks_lvl_intro n lks Hsz with "Hlks").
  Qed.

  Lemma cpu_own_locks_swap (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (lks : gset nat) :
    cpu_own n eb p C false lks -∗
    cpu_locks lks ∗ ⌜(size lks <= n)%nat⌝ ∗
    (∀ lks' : gset nat,
       ⌜(size lks' <= n)%nat⌝ -∗ cpu_locks lks' -∗ cpu_own n eb p C false lks').
  Proof.
    iIntros "Hown".
    iDestruct (bi.equiv_entails_1_1 _ _ (cpu_own_off n eb p C lks) with "Hown")
      as "[Hh HC]".
    iEval (rewrite /cpu_hart /cpu_priv) in "Hh".
    iDestruct "Hh" as "((Hcells & Hlvl) & Hcnt)".
    iDestruct (cpu_locks_lvl_elim with "Hlvl") as "[Hlks %Hsz]".
    iFrame "Hlks". iSplitR; [ iPureIntro; exact Hsz | ].
    iIntros (lks' Hsz') "Hlks".
    iApply (bi.equiv_entails_1_2 _ _ (cpu_own_off n eb p C lks')).
    iFrame "HC". rewrite /cpu_hart /cpu_priv. iFrame "Hcells Hcnt".
    iApply (cpu_locks_lvl_intro n lks' Hsz' with "Hlks").
  Qed.

  (* swap the context-slot payload (e.g. park / unpark the scheduler
     continuation) without disturbing the rest.  Index-generic: [C] is a
     frame at either arm. *)
  Lemma cpu_own_ctx_swap (n : nat) (eb : bool) (p : mword 64)
      (C C' : iProp Σ) (b : bool) (lks : gset nat) :
    cpu_own n eb p C b lks -∗ (C -∗ C') -∗ cpu_own n eb p C' b lks.
  Proof.
    iIntros "[Hrest HC] HW". iFrame "Hrest". iApply ("HW" with "HC").
  Qed.

  (* retarget the proc field (the scheduler's c->proc writes, and myproc()'s
     read).  Only at the DISABLED index: at [b = true] the cells have moved
     into the SIE arm.

     THE ACCESSOR HANDS OUT THE WHOLE CELL, which is what a store needs.
     [cpus[cid].proc] is private to this hart -- no invariant and no lock
     holds a fraction of it -- so neither [c->proc] store is mask-changing
     and neither needs anything but this bundle. *)
  Lemma cpu_own_set_proc (n : nat) (eb : bool)
      (p p' : mword 64) (C : iProp Σ) (lks : gset nat) :
    cpu_own n eb p C false lks -∗
    (cur_proc p ∗
     (cur_proc p' -∗ cpu_own n eb p' C false lks)).
  Proof.
    iIntros "((((%Hbound & Hnoff & Hint & Hproc) & Hlks) & Hcnt) & HC)".
    iFrame "Hproc". iIntros "Hproc". iFrame "Hnoff Hint Hlks Hcnt HC Hproc".
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
Lemma cpu_own_transport `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId}
    (CID0 CID1 : CpuId) (n : nat) (eb : bool) (p : mword 64)
    (C : iProp Σ) (b : bool) {lks : gset nat} :
  (b = false \/ p = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
  cpu_own (CID := CID0) n eb p C b lks -∗ cpu_own (CID := CID1) n eb p C b lks.
Proof.
  intros Heq. destruct b.
  - (* enabled: the payload is in [sie_arm], nothing here mentions the hart *)
    iIntros "H". iExact "H".
  - (* disabled: no trap was taken, so the hart did not move *)
    rewrite (_ : CID1 = CID0); [ iIntros "$" | exact (Heq (or_introl eq_refl)) ].
Qed.
