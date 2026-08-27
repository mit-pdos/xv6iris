(* CpuOwn.v -- ownership of THIS cpu's [struct cpu] plus the push/pop
   interrupt discipline, as ONE predicate.

   [cpu_own n eb p b] owns, for the ambient CpuId:
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

   NOTE ON THE (FORMER) [C] ARGUMENT.  This bundle used to carry a fourth
   argument [C], an arbitrary caller frame threaded alongside the cells --
   the context-slot payload for cpus[cid].context: [cpu_ctx_free] at boot
   and while the scheduler itself runs, or emp once a function does not
   need to say anything about it.  [C] added nothing [cpu_own] itself
   needed: at every call site it was either universally quantified and
   passed through unchanged (exactly what Iris's own frame rule already
   gives for free), or fixed to [emp] (an identity conjunct), or -- rarely,
   at a real crossing such as scheduler entry -- a genuine resource that is
   now simply held ALONGSIDE [cpu_own] as its own separating-conjunction
   partner ([cpu_ctx_free ∗ cpu_own ...]) rather than folded inside it.
   Removing the argument is not a weakening: [cpu_own n eb p b lks] here is
   definitionally what [cpu_own n eb p C b lks] used to be at [C := emp],
   and every site that needed something else now states that something
   else explicitly, beside this bundle, instead of inside it.

   THE [b] INDEX -- the SIE state of the ambient [sie_cap_gpr] this bundle
   travels beside.  At [b = true] the cells and the token are NOT here:
   they ride in [sie_arm]'s enabled arm (IntrDefs.v), because with
   interrupts enabled a trap can migrate the thread and only what a leaf's
   [wp_next] re-delivers survives the crossing.  What is left at [b = true]
   is the pure fact the arm's ghost agreement pins anyway ([n = 0] and
   [eb = true], [intr_count_get_on]).  push_off and pop_off are the two
   functions that move the payload across this seam.

   [cpu_own 0 false p false ∅] is constructible from raw boot resources
   (cells + the SIE eighth at '0') -- no trap handler, no stvec, no trap
   CSRs -- which is what makes push_off/pop_off (and the whole
   acquire/release cone above them) usable during early boot, where both
   are no-ops on SIE. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang HartTp.
Require Import RegFile.   (* [regfile]: the index algebra below names the map *)
Require Import IntrDefs.
Require Import ProcGeom.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

Section CpuOwn.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  Definition cpu_own (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) : iProp Σ :=
    (if b then ⌜ n = 0%nat /\ eb = true /\ lks = ∅ ⌝ else cpu_hart n eb p lks)%I.

  (* at the disabled index the bundle IS the cells + the token *)
  Lemma cpu_own_off (n : nat) (eb : bool) (p : mword 64) (lks : gset string) :
    cpu_own n eb p false lks ⊣⊢ cpu_hart n eb p lks.
  Proof. reflexivity. Qed.

  (* ... and at the enabled index it is just the pure fact: the payload is
     inside [sie_arm true p].  This is not a weakening -- a caller could not
     have HELD the cells there anyway ([cpu_own_arm_excl] below refutes it),
     because the arm already owns them. *)
  (* THE THEOREM THE WHOLE ABSTRACTION EXISTS FOR is the [lks = ∅] conjunct:
     a hart with interrupts ENABLED holds no spinlock. *)
  Lemma cpu_own_on (n : nat) (eb : bool) (p : mword 64) (lks : gset string) :
    cpu_own n eb p true lks ⊣⊢ ⌜ n = 0%nat /\ eb = true /\ lks = ∅ ⌝.
  Proof. reflexivity. Qed.

  Lemma cpu_own_on_intro (p : mword 64) :
    ⊢ cpu_own 0 true p true ∅.
  Proof. iPureIntro. done. Qed.

  (* THE MOVE push_off makes at the enabled arm, and pop_off's inverse. *)
  Lemma cpu_own_of_arm (n : nat) (eb : bool) (p : mword 64) (lks : gset string) :
    cpu_own n eb p true lks -∗
    cpu_hart 0 true p ∅ -∗
    cpu_own 0 true p false ∅.
  Proof. iIntros "_ Hh". iFrame "Hh". Qed.

  Lemma cpu_own_to_arm (p : mword 64) :
    cpu_own 0 true p false ∅ -∗
    cpu_hart 0 true p ∅ ∗ cpu_own 0 true p true ∅.
  Proof. iIntros "Hh". iFrame "Hh". iPureIntro. done. Qed.

  (* the cells are EXCLUSIVE, so nobody holds them beside the enabled arm *)
  Lemma cpu_hart_excl (n n' : nat) (eb eb' : bool) (p p' : mword 64)
      (lks lks' : gset string) :
    cpu_hart n eb p lks -∗ cpu_hart n' eb' p' lks' -∗ False.
  Proof.
    iIntros "(((_ & Hn & _ & _) & _) & _) (((_ & Hn' & _ & _) & _) & _)".
    iDestruct (ctx_word4_pointsto_bytes with "Hn") as "Hb".
    iDestruct (ctx_word4_pointsto_bytes with "Hn'") as "Hb'".
    cbn [seq]. iDestruct "Hb" as "[H0 _]". iDestruct "Hb'" as "[H0' _]".
    iDestruct (mem_pointsto_ne with "H0 H0'") as %Hne. done.
  Qed.

  Lemma cpu_own_arm_excl (n n' : nat) (eb eb' : bool) (p p' : mword 64)
      (lks : gset string) :
    sie_arm kt true p -∗ cpu_own n' eb' p' false lks -∗ False.
  Proof.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & Hh) Hh'".
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
      (p : mword 64) (b : bool) {lks : gset string} :
    sie_cap_gpr kt m K b p -∗ cpu_own n eb p b lks -∗
    ⌜ match n with O => eb | S _ => false end = b ⌝.
  Proof.
    iIntros "Hcg Hown". destruct b.
    - iDestruct "Hown" as "%Hpure". iPureIntro. destruct Hpure as (-> & -> & _). done.
    - iDestruct "Hown" as "[_ Hic]".
      destruct n as [|n'].
      + iDestruct (sie_cap_gpr_split with "Hcg") as "(_ & _ & Hsie & _)".
        iDestruct "Hsie" as "(_ & _ & Hbit & _)".
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
      (b : bool) {lks : gset string} :
    sie_cap_gpr kt m K b p -∗ cpu_own 0 true p b lks -∗ ⌜ b = true ⌝.
  Proof.
    destruct b; [ by iIntros "_ _" |].
    iIntros "Hcg Hown".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbad.
    cbn in Hbad. discriminate Hbad.
  Qed.

  (* ... and the dual, which needs no capability at all: the enabled index's
     own arm carries [⌜n = 0⌝]. *)
  Lemma cpu_own_forces_off (n : nat) (eb : bool) (p : mword 64)
      (lks : gset string) :
    cpu_own (S n) eb p true lks -∗ False.
  Proof.
    iIntros "%Hpure". destruct Hpure as [Hn _]. discriminate Hn.
  Qed.

  (* boot entry: raw cells + the SIE eighth at '0' + this hart's held-lock
     authority, which adequacy mints at the EMPTY set (a hart that has not
     run an instruction holds no locks).  [iv] arbitrary. *)
  (* [medeleg] arrives at the value [start()] left, which is the pinned
     [IntrDefs.MEDELEG_S]; the other three cells' values are not looked at. *)
  Lemma cpu_own_init_boot (p : mword 64) (nv iv : mword 32)
      (sscr mdl : mword 64) :
    nv = noff_val 0 ->
    mdl = MEDELEG_S ->
    a_cpu_noff cid_word ↦₄ nv -∗
    a_cpu_int cid_word ↦₄ iv -∗
    intr_off_tok -∗
    cur_proc p -∗
    lk_auth cpu_id ∅ -∗
    sscratch ↦ᵣ sscr -∗
    medeleg ↦ᵣ□ mdl -∗
    mstateen0 ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
    sstateen0 ↦ᵣ□ (mword_of_int 0 : mword 32) -∗
    cpu_own 0 false p false ∅.
  Proof.
    intros -> ->. iIntros "Hnoff Hint Htok Hproc Hlk Hssc Hmdl Hmse Hsse".
    iSplitR "Htok"; [| iApply (intr_count_init_off with "Htok") ].
    iSplitR "Hlk Hssc Hmdl Hmse Hsse".
    { iSplitR. { iPureIntro. vm_compute. reflexivity. }
      iFrame "Hnoff Hproc". iExists iv. iExact "Hint". }
    iSplitL "Hlk".
    { iApply (cpu_locks_lvl_intro 0 ∅); [ rewrite size_empty; lia
      | iApply (cpu_locks_intro_empty with "Hlk") ]. }
    iSplitL "Hssc". { iExists sscr. iExact "Hssc". }
    iFrame "Hmdl Hmse Hsse".
  Qed.

  (* THE PER-HART CSRs, IN AND OUT.  [hart_csrs] (IntrDefs.v) is a conjunct
     of [cpu_priv], so at the DISABLED index it is inside this bundle -- and
     that is the whole point of parking it here: the trampoline reaches
     [sscratch] through the residue that carries [cpu_own], and the trap loop
     hands the three pinned cells to [UserExec.user_cfg] for the user phase
     and gets them back on the next trap.  At [b = true] the payload is in
     [sie_arm]'s enabled arm instead, so this accessor is stated at [false]
     like the locks one above. *)
  Lemma cpu_own_csrs_open (n : nat) (eb : bool) (p : mword 64)
      (lks : gset string) :
    cpu_own n eb p false lks -∗
    hart_csrs ∗ (hart_csrs -∗ cpu_own n eb p false lks).
  Proof.
    iIntros "Hh".
    iEval (rewrite /cpu_own /cpu_hart /cpu_priv) in "Hh".
    iDestruct "Hh" as "((Hcells & Hlks & Hcsrs) & Hcnt)".
    iFrame "Hcsrs". iIntros "Hcsrs".
    rewrite /cpu_own /cpu_hart /cpu_priv. iFrame "Hcells Hlks Hcsrs Hcnt".
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
  Lemma cpu_own_size_le (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    cpu_own n eb p b lks -∗ ⌜(size lks <= n)%nat⌝ ∗ cpu_own n eb p b lks.
  Proof.
    destruct b.
    - iIntros "%Hp". destruct Hp as (Hn & Heb & Hl).
      iSplitR. { iPureIntro. subst lks. rewrite size_empty. lia. }
      iPureIntro. done.
    - iIntros "Hh".
      iEval (rewrite /cpu_hart /cpu_priv) in "Hh".
      iDestruct "Hh" as "((Hcells & Hlvl & Hcsrs) & Hcnt)".
      iDestruct (cpu_locks_lvl_elim with "Hlvl") as "[Hlks %Hsz]".
      iSplitR; [ iPureIntro; exact Hsz | ].
      rewrite /cpu_hart /cpu_priv. iFrame "Hcells Hcsrs Hcnt".
      iApply (cpu_locks_lvl_intro n lks Hsz with "Hlks").
  Qed.

  (* AT DEPTH ZERO THE HELD SET IS FORCED EMPTY, so a contract whose [cpu_own]
     pins [n = 0] -- every syscall body, [yield], the trap tails -- needs no
     order premise of its own: it DERIVES [lks = ∅], and every order goal its
     callees raise is then [locks_below ∅ _].  That is what keeps the premise
     from cascading out of the syscall layer and into [SpecSyscall] /
     [SpecUsertrap], whose [lks] is equally abstract but whose depth is the
     same zero. *)
  Lemma cpu_own_zero_empty (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    cpu_own 0%nat eb p b lks -∗ ⌜lks = ∅⌝ ∗ cpu_own 0%nat eb p b lks.
  Proof.
    iIntros "H". iDestruct (cpu_own_size_le with "H") as "[%Hsz H]".
    iFrame "H". iPureIntro. exact (size_le_zero_empty lks Hsz).
  Qed.

  Lemma cpu_own_locks_swap (n : nat) (eb : bool) (p : mword 64)
      (lks : gset string) :
    cpu_own n eb p false lks -∗
    cpu_locks lks ∗ ⌜(size lks <= n)%nat⌝ ∗
    (∀ lks' : gset string,
       ⌜(size lks' <= n)%nat⌝ -∗ cpu_locks lks' -∗ cpu_own n eb p false lks').
  Proof.
    iIntros "Hh".
    iEval (rewrite /cpu_hart /cpu_priv) in "Hh".
    iDestruct "Hh" as "((Hcells & Hlvl & Hcsrs) & Hcnt)".
    iDestruct (cpu_locks_lvl_elim with "Hlvl") as "[Hlks %Hsz]".
    iFrame "Hlks". iSplitR; [ iPureIntro; exact Hsz | ].
    iIntros (lks' Hsz') "Hlks".
    rewrite /cpu_own /cpu_hart /cpu_priv. iFrame "Hcells Hcsrs Hcnt".
    iApply (cpu_locks_lvl_intro n lks' Hsz' with "Hlks").
  Qed.

  (* retarget the proc field (the scheduler's c->proc writes, and myproc()'s
     read).  Only at the DISABLED index: at [b = true] the cells have moved
     into the SIE arm.

     THE ACCESSOR HANDS OUT THE WHOLE CELL, which is what a store needs.
     [cpus[cid].proc] is private to this hart -- no invariant and no lock
     holds a fraction of it -- so neither [c->proc] store is mask-changing
     and neither needs anything but this bundle. *)
  Lemma cpu_own_set_proc (n : nat) (eb : bool)
      (p p' : mword 64) (lks : gset string) :
    cpu_own n eb p false lks -∗
    (cur_proc p ∗
     (cur_proc p' -∗ cpu_own n eb p' false lks)).
  Proof.
    iIntros "(((%Hbound & Hnoff & Hint & Hproc) & Hlks) & Hcnt)".
    iFrame "Hproc". iIntros "Hproc". iFrame "Hnoff Hint Hlks Hcnt Hproc".
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
(* into [sie_arm], leaving a pure fact.  So the two arms are discharged    *)
(* by the two halves of what a step actually gives you: at [b = true] by   *)
(* CONVERSION (there is no hart in the term), at [b = false] by            *)
(* [wp_next]'s conditional equality.  Chain the per-step equalities with   *)
(* [wp_next_chain] and apply this once. *)
(* ===================================================================== *)
(* ONE context however many harts the statement names: the hart may move
   under a trap, the thread's context does not -- the flip makes that
   design point a binder. *)
Lemma cpu_own_transport `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{XI : CurCtx}
    (CID0 CID1 : CpuId) (n : nat) (eb : bool) (p : mword 64)
    (b : bool) {lks : gset string} :
  (b = false \/ p = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
  cpu_own (CID := CID0) n eb p b lks -∗ cpu_own (CID := CID1) n eb p b lks.
Proof.
  intros Heq. destruct b.
  - (* enabled: the payload is in [sie_arm], nothing here mentions the hart *)
    iIntros "H". iExact "H".
  - (* disabled: no trap was taken, so the hart did not move *)
    rewrite (_ : CID1 = CID0); [ iIntros "$" | exact (Heq (or_introl eq_refl)) ].
Qed.
