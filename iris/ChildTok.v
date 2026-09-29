(* ===================================================================== *)
(* ChildTok.v -- THE GENERATION, AS A SAVED PREDICATE CARRYING ITS SLOT,  *)
(* ITS PID AND ITS EXIT PAYLOAD.                                          *)
(*                                                                        *)
(* Design of record: claude-notes/projects/app-echo.md, the WAIT-EXIT     *)
(* section (the ESCROW shape).  A process's GENERATION is the             *)
(* ghost name allocproc mints for it -- the identity of THIS incarnation  *)
(* of a proc slot, which is what a wait()-side resource transfer has to   *)
(* be indexed by, a pid being reused and a generation not                 *)
(* ([UexecSlot.uvis_gen] is the key's reading of it).  The name carries   *)
(* three things at once, and they are one saved element rather than three *)
(* ghosts because every party that holds a piece of a generation has to   *)
(* agree with every other on all three:                                   *)
(*                                                                        *)
(*   the SLOT      the [proc_addr] of the slot this incarnation occupies  *)
(*                 -- [SchedCtx]'s and [ProcInv.proc_priv]'s own          *)
(*                 parameter, so the party that reads it has it in hand.  *)
(*   the PID       the pid <allocpid> chose, at the [mword 32] the cell   *)
(*                 holds.  A generation has one pid forever is then       *)
(*                 agreement and not an invariant.                        *)
(*   the PAYLOAD   [Q : Z -> iProp], the resources this process's exit    *)
(*                 owes its parent, as a function of the exit STATUS.     *)
(*                 allocproc mints it at the creator's choice; exit pays     *)
(*                 [Q xs] into the escrow; wait hands the parent [Q xs].  *)
(*                                                                        *)
(* WHY A SAVED PREDICATE.  The payload is an [iProp], so it cannot be a   *)
(* value in an ordinary camera without a step-index; [saved_anything_own] *)
(* at [genF] is the standard way to put one in a ghost -- and the ▷ that  *)
(* buys it is exactly the ▷ in the payment rule below, which the escrow   *)
(* pays for free (kexit's deposit and kwait's return are separated by at  *)
(* least one step) and a TIMELESS payload does not pay at all             *)
(* ([gen_pay_timeless]).                                                  *)
(*                                                                        *)
(* THE FOUR PIECES OF ONE GENERATION, and who holds them:                 *)
(*                                                                        *)
(*   [child_tok γ pid Q]  the PARENT's quarter, minted at fork.  Its      *)
(*                        holder is the one party wait() may hand the     *)
(*                        payload to.                                     *)
(*   [gen_kq γ pa pid Q]  the KERNEL's quarter, kept in the child's       *)
(*                        private block ([ProcInv.proc_priv_core]) until  *)
(*                        exit moves it into the ZOMBIE escrow.           *)
(*   [my_pay γ Q]         the CHILD's knowledge of its own payload:       *)
(*                        persistent, because it is what the child's slot *)
(*                        is built against and a slot is re-established   *)
(*                        at every trap.  It is the discarded HALF, so it *)
(*                        is also where the two persistent readings       *)
(*                        [gen_slot] / [gen_pid] come from.               *)
(*   [exit_tok γ pid xs]  the ESCROW: the kernel's quarter TOGETHER WITH  *)
(*                        the paid payload.  kexit produces it, kwait     *)
(*                        returns it, and [gen_pay] is what a parent      *)
(*                        holding the matching [child_tok] does with it.  *)
(*                                                                        *)
(* PERSISTENCE IS ONLY THROUGH THE DISCARDED FRACTION.  A quarter is a    *)
(* [DfracOwn], hence linear: neither the parent's token nor the kernel's  *)
(* may be duplicated, which is what makes -- the payload is paid once -- a *)
(* THEOREM.  The two readings are stated at [DfracDiscarded] for that     *)
(* reason -- they are facts, so they must come off the half fork discards *)
(* and never off a quarter.                                               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.algebra Require Import dfrac excl agree csum.  (* [exclR] -- the taken token's camera; [csumR]/[agreeR] -- the kill flag's one-shot *)
From xv6iris Require Import StepIndex.
From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import own saved_prop.
Require Import SailStdpp.Base SailStdpp.Values.
Local Open Scope Z_scope.

(* THE FUNCTOR.  A pair: the two VALUES the generation pins (its slot
   address and its pid, at [leibnizO] because both are discrete machine
   words) and the PREDICATE it saves (the exit payload, indexed by the exit
   status).  [constOF] on the left is what keeps the values out of the
   step-indexing: agreement on them is a PURE equality with no later,
   which is what [gen_agree] hands its callers. *)
(* ...AND THE THREE THINGS A GENERATION RECORDS BESIDES ITS PAYLOAD (lane
   SELF-KILL, §3a).

   [ga]  THE TAKEN TOKEN'S GHOST NAME, in the PURE component beside the
         slot and the pid, so agreement on it is a plain equality with no
         later.  It cannot be the generation's own name: [gn] is
         [saved_anything_alloc]'s, and no [own_alloc] variant targets a
         chosen name, so an exclusive token AT [gn] is not allocatable.
         The token itself is [taken_tok] below -- linear, exclusive, minted
         with the incarnation into the process's PRIVATE BLOCK, and what
         the exit path leaves in [SchedCtx]'s killed row when it takes the
         payment out of it: "killed and spent".  Once the row holds it a
         second taking is impossible, and the process cannot forge the
         payment back.
   THERE IS NO CREDENTIAL FIELD AND NO PAYMENT RULE HERE (coordinator,
   2026-09-13).  What a kill of this process costs is its OWN EXIT PAYLOAD
   AT -1, which this generation already tracks, so the predicate [K] of the
   earlier design and the opaque payment rule [Kp] that replaced it are
   both gone: [kill_owed] below is stated at [Q], and HOW a killer who
   holds only the application's supply pays is published by
   [SchedCtx.kill_paid] as the wand [□ (AppInv.app_sup -∗ Q (-1))] beside
   the persistent [my_pay] -- at an altitude where [app_sup] is nameable,
   which this one is not (this file requires stdpp, iris and Sail and
   nothing of the application). *)
(* ...AND THE FOURTH FIELD IS THE KILL FLAG'S ONE-SHOT (lane SELF-KILL,
   P6).  [p->killed] is set and never cleared while a process lives -- only
   freeproc zeroes it, and only on a slot whose process is already a ZOMBIE
   -- but <p->lock>'s payload quantifies the cell EXISTENTIALLY, so "the
   flag was nonzero a few instructions ago" is not a fact anything can
   carry across a release.  It has to be a GHOST fact, and a persistent
   one, because the party that reads the flag ([killed]) and the party that
   needs to know it ([kexit], which never reads it) are separated by two
   critical sections.
     [gk] is that ghost's name, in the PURE component beside the other
   two: PENDING while the row's zero arm holds it, SHOT the moment a writer
   sets the flag, and the shot half is persistent and duplicable, which is
   exactly what makes it relayable.  Its camera is [kshotR] below. *)
Definition genF : tFunctor :=
  prodTF (constTF (leibnizO (Values.mword 64 * Values.mword 32 * gname * gname)))
         (Z -d> ▶ ∙)%TF.

Global Instance genF_contractive : tFunctorContractive genF.
Proof. apply _. Qed.

(* THE TAKEN TOKEN'S VALUE, AND IT IS A TYPE OF OUR OWN.  [exclR unitO] is
   already an [inG] of the bundle ([Xv6Cameras.icache_tickG]), and two
   providers of one [inG] in one scope do not fail -- they make two
   instance paths whose propositions print identically
   (durable-notes.md).  A one-constructor inductive of this file's own
   makes the camera unmistakable. *)
Inductive taken_val := Taken.

Global Instance taken_val_eq_dec : EqDecision taken_val.
Proof. solve_decision. Defined.

Definition atokR : cmra := exclR (leibnizO taken_val).

(* THE KILL FLAG'S ONE-SHOT, AND ITS VALUE IS ALSO A TYPE OF OUR OWN.
   [csumR (exclR unitO) (agreeR unitO)] is already an [inG] of the bundle
   ([Xv6Cameras.kalloc_oneshotR]), and two providers of one [inG] in one
   scope make two instance paths whose propositions print identically
   (durable-notes.md) -- the same trap [atokR] above sidesteps, and by the
   same move. *)
Inductive shot_val := Shot.

Global Instance shot_val_eq_dec : EqDecision shot_val.
Proof. solve_decision. Defined.

Definition kshotR : cmra :=
  csumR (exclR (leibnizO shot_val)) (agreeR (leibnizO shot_val)).

(* THE CAPACITY CLASS, AND IT LIVES HERE rather than in [Xv6Cameras.v] with
   the bundle's other members.  The reason is import hygiene: the files
   that name this file's pieces are U-tier leaves that bind no
   whole-system bundle, so each has to name the class itself -- and naming
   [savedAnythingG Σ genF] raw would make every one of them import
   [saved_prop], whose own re-exports re-shadow [Forall_forall] and the
   numeral scopes at whatever point in the client's import list the
   [Require] happens to sit.  A CLASS OF OUR OWN costs the client one name
   and imports nothing.  [Xv6Cameras] re-exports it and [Xv6G.xv6_ctok] is
   the bundle's field, so the kernel side reaches it through the bundle
   and must not bind it again. *)
Class ctokG (Σ : gFunctors) := CtokG {
  ctok_inG :: savedAnythingG Σ genF;
  (* the taken token's camera rides the SAME class, for the reason the
     class exists at all: a U-tier leaf that names one names the other. *)
  ctok_taken :: inG Σ atokR;
  (* ...and so does the kill flag's one-shot, for the same reason *)
  ctok_shot :: inG Σ kshotR;
}.
Definition ctokΣ : gFunctors :=
  #[ savedAnythingΣ genF; GFunctor atokR; GFunctor kshotR ].
Global Instance subG_ctokΣ {Σ} : subG ctokΣ Σ -> ctokG Σ.
Proof. solve_inG. Qed.

Section ChildTok.
  Context `{!ctokG Σ}.

  Implicit Types (γ ga : gname) (dq : dfrac) (pa : Values.mword 64)
                 (pid : Values.mword 32) (Q : Z -> iProp Σ) (xs : Z).

  (* ------------------------------------------------------------------ *)
  (* THE TAKEN TOKEN.                                                     *)
  (* ------------------------------------------------------------------ *)

  (* WHAT A PROCESS SPENDS TO SAY IT IS STILL ITSELF.  Exclusive and
     per-INCARNATION (pids are reused, generations are not), minted with
     the generation and carried by the process.  Two readers cannot both
     hold it, which is the whole of its content: a process that holds its
     own token refutes any claim that its incarnation was killed, and a
     process that FAULTS ON PURPOSE hands it over as the credential its
     death costs. *)
  Definition taken_tok ga : iProp Σ := own ga (Excl (Taken : leibnizO taken_val)).

  Global Instance taken_tok_timeless ga : Timeless (taken_tok ga).
  Proof using . apply _. Qed.

  Lemma taken_tok_excl ga : taken_tok ga -∗ taken_tok ga -∗ False.
  Proof using .
    rewrite /taken_tok. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. exact (exclusive_l _ _ Hv).
  Qed.

  Lemma taken_tok_alloc : ⊢ |==> ∃ ga, taken_tok ga.
  Proof using . rewrite /taken_tok. iApply own_alloc. done. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE KILL FLAG'S ONE-SHOT, RAW.                                       *)
  (* ------------------------------------------------------------------ *)

  (* PENDING: the flag of this incarnation has never been set.  Exclusive,
     minted with the generation, and it lives in <p->lock>'s killed row --
     in the arm that CLAIMS the flag is zero ([SchedCtx.kill_row]).  A
     writer that sets the flag opens the row, finds this, and shoots it. *)
  Definition shot_pending gk : iProp Σ :=
    own gk (Cinl (Excl (Shot : leibnizO shot_val))).

  (* SHOT: the flag of this incarnation HAS been set.  Persistent, and
     that is the whole point -- it is what [killed] relays out of its
     critical section and what [kexit] uses, two critical sections later,
     to refute the row's zero arm. *)
  Definition shot_done gk : iProp Σ :=
    own gk (Cinr (to_agree (Shot : leibnizO shot_val))).

  Global Instance shot_done_persistent gk : Persistent (shot_done gk).
  Proof using . rewrite /shot_done. apply _. Qed.
  Global Instance shot_pending_timeless gk : Timeless (shot_pending gk).
  Proof using . apply _. Qed.
  Global Instance shot_done_timeless gk : Timeless (shot_done gk).
  Proof using . apply _. Qed.

  Lemma shot_pending_excl gk : shot_pending gk -∗ shot_pending gk -∗ False.
  Proof using .
    rewrite /shot_pending. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    exact (exclusive_l _ _ Hv).
  Qed.

  (* the two states are incompatible: this is what refutes the zero arm *)
  Lemma shot_pending_done gk : shot_pending gk -∗ shot_done gk -∗ False.
  Proof using .
    rewrite /shot_pending /shot_done. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %Hv.
  Qed.

  Lemma shot_fire gk : shot_pending gk ==∗ shot_done gk.
  Proof using .
    rewrite /shot_pending /shot_done. iIntros "H".
    iApply (own_update with "H"). by apply cmra_update_exclusive.
  Qed.

  Lemma shot_pending_alloc : ⊢ |==> ∃ gk, shot_pending gk.
  Proof using . rewrite /shot_pending. iApply own_alloc. done. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE GENERATION.                                                      *)
  (* ------------------------------------------------------------------ *)

  (* the saved element, spelled once: the three PURE values and the
     payload under [Next] (the functor's ▷) *)
  Definition gen_el pa pid ga gk Q : tFunctor_apply genF (iPropO Σ) :=
    (((pa, pid, ga, gk)
        : leibnizO (Values.mword 64 * Values.mword 32 * gname * gname)),
     Next ∘ Q).

  (* A FRACTION OF A GENERATION.  Every piece below is this at a fraction. *)
  Definition gen_own γ dq pa pid ga gk Q : iProp Σ :=
    saved_anything_own (F := genF) γ dq (gen_el pa pid ga gk Q).

  (* ---- the readings, and they are facts only off the discarded half ---- *)

  (* EVERYTHING THE DISCARDED HALF SAYS, AT ONCE.  The four readings below
     are this at one component named and the rest hidden; it is a reading
     in its own right because the party that CUTS the generation
     ([gen_split]) knows all four and every later reader wants a different
     one. *)
  Definition gen_know γ ga gk Q : iProp Σ :=
    (∃ pa pid, gen_own γ DfracDiscarded pa pid ga gk Q)%I.

  (* the slot this incarnation occupies *)
  Definition gen_slot γ pa : iProp Σ :=
    (∃ pid ga gk Q, gen_own γ DfracDiscarded pa pid ga gk Q)%I.

  (* ...and the pid it was given.  A generation has one pid forever, which
     is what the escrow's pid-keyed reading in [SpecKwait]'s success arm
     stands on. *)
  Definition gen_pid γ pid : iProp Σ :=
    (∃ pa ga gk Q, gen_own γ DfracDiscarded pa pid ga gk Q)%I.

  (* THE CHILD'S KNOWLEDGE OF ITS OWN PAYLOAD.  Persistent, so it travels
     into the child's slot and survives exec ([UexecSlot.uvis_gen] does),
     and so that a slot -- re-established at every trap -- may name it
     without owning anything linear. *)
  Definition my_pay γ Q : iProp Σ :=
    (∃ pa pid ga gk, gen_own γ DfracDiscarded pa pid ga gk Q)%I.

  (* ...AND THE SAME READING FOR THE THREE NEW COMPONENTS.  [gen_taken] is
     PURE agreement (the name is in the [constOF] half), the other two cost
     a later, exactly as the payload does. *)
  Definition gen_taken γ ga : iProp Σ :=
    (∃ pa pid gk Q, gen_own γ DfracDiscarded pa pid ga gk Q)%I.

  (* ...AND THE ONE-SHOT'S NAME, read the same way *)
  Definition gen_shotn γ gk : iProp Σ :=
    (∃ pa pid ga Q, gen_own γ DfracDiscarded pa pid ga gk Q)%I.

  Global Instance gen_know_persistent γ ga gk Q : Persistent (gen_know γ ga gk Q).
  Proof using . apply _. Qed.
  Global Instance gen_slot_persistent γ pa : Persistent (gen_slot γ pa).
  Proof using . apply _. Qed.
  Global Instance gen_pid_persistent γ pid : Persistent (gen_pid γ pid).
  Proof using . apply _. Qed.
  Global Instance my_pay_persistent γ Q : Persistent (my_pay γ Q).
  Proof using . apply _. Qed.
  Global Instance gen_taken_persistent γ ga : Persistent (gen_taken γ ga).
  Proof using . apply _. Qed.
  Global Instance gen_shotn_persistent γ gk : Persistent (gen_shotn γ gk).
  Proof using . apply _. Qed.


  (* the two projections of the whole reading *)
  Lemma gen_know_my_pay γ ga gk Q : gen_know γ ga gk Q -∗ my_pay γ Q.
  Proof using .
    rewrite /gen_know /my_pay. iIntros "H". iDestruct "H" as (pa pid) "H".
    iExists pa, pid, ga, gk. iExact "H".
  Qed.

  Lemma gen_know_taken γ ga gk Q : gen_know γ ga gk Q -∗ gen_taken γ ga.
  Proof using .
    rewrite /gen_know /gen_taken. iIntros "H". iDestruct "H" as (pa pid) "H".
    iExists pa, pid, gk, Q. iExact "H".
  Qed.

  Lemma gen_know_shotn γ ga gk Q : gen_know γ ga gk Q -∗ gen_shotn γ gk.
  Proof using .
    rewrite /gen_know /gen_shotn. iIntros "H". iDestruct "H" as (pa pid) "H".
    iExists pa, pid, ga, Q. iExact "H".
  Qed.

  (* ---- the two linear quarters ---- *)

  (* THE PARENT'S QUARTER, handed to the forking process at [kfork]'s pid
     arm.  The slot is existential: a parent is told which CHILD it has,
     not which proc slot the kernel put it in. *)
  Definition child_tok γ pid Q : iProp Σ :=
    (∃ pa ga gk, gen_own γ (DfracOwn (1/4)%Qp) pa pid ga gk Q)%I.

  (* THE KERNEL'S QUARTER, in the child's private block. *)
  Definition gen_kq γ pa pid Q : iProp Σ :=
    (∃ ga gk, gen_own γ (DfracOwn (1/4)%Qp) pa pid ga gk Q)%I.

  (* THE ESCROW.  What a ZOMBIE slot holds for its parent: the kernel's
     quarter of the dead incarnation's generation, and the payload PAID at
     the status the slot's [p_xstate] cell now reads.

     WHY TWO PREDICATES AND NOT ONE.  The party that pays is the exiting
     PROCESS, and what it deposits at the trap boundary is its own
     [my_pay γ Q'] beside [Q' xs] ([UexecRet.uexec_dep_F] at [USYS_exit]):
     a slot may only ever name the payload it can prove it has, which is
     what the persistent half is.  The party that HOLDS the kernel's
     quarter is kexit, out of the dying process's private block
     ([ProcInv.proc_priv_core]), and its [Q] is bound by that block's own
     existential.  The two are THE SAME PREDICATE -- agreement of two
     pieces of one generation -- but only up to the saved predicate's
     later, so pairing them here rather than rewriting one into the other
     is what keeps kexit's park later-free.  [gen_pay] pays the ▷ once, at
     the reaper, where it costs nothing.

     A KILL IS PAID TOO, AND OUT OF THE SAME PAYLOAD.  A process that
     [kill] marked is torn down by the kernel at its next trap, which runs
     [exit(-1)] with the process's own continuation undelivered -- so
     nothing the PROGRAM does can pay at that moment.  What pays is what
     the program handed the kernel when it trapped: its run carries
     [UkRun.ukn_pay N (-1)] as a linear conjunct precisely so that the
     kernel can spend it on the kill path, and hands it back at every
     resume that is not one ([UexecRet.uexec_pay_dep] / [uexec_pay_arm]).
     So a parent gets [Q (-1)] whether its child called [exit(-1)] or was
     killed, and there is exactly one arm here.

     KEYED AT THE STORED STATUS.  [xs] is the value in the slot's
     [p_xstate] cell, whose other half rides this same block
     ([ProcDefs.proc_dormant]); the reaper holds [p->lock], so the half it
     reads through [SchedCtx.proc_pub] and the half beside this escrow
     agree, and the status it copies out to the parent IS this [xs]. *)
  Definition exit_tok γ pid xs : iProp Σ :=
    (∃ pa Q Q', gen_kq γ pa pid Q ∗ my_pay γ Q' ∗ Q' xs)%I.

  (* ------------------------------------------------------------------ *)
  (* AGREEMENT.                                                          *)
  (* ------------------------------------------------------------------ *)

  (* Two pieces of one generation agree on all three components: on the
     slot and the pid PURELY (they are [constOF]), and on the payload up to
     the saved predicate's own later. *)
  (* THE THREE PURE COMPONENTS AGREE PURELY, and the payload up to the
     saved predicate's own later. *)
  Lemma gen_agree_all γ dq dq' pa pid ga gk Q pa' pid' ga' gk' Q' :
    gen_own γ dq pa pid ga gk Q -∗ gen_own γ dq' pa' pid' ga' gk' Q' -∗
    ⌜pa = pa' /\ pid = pid' /\ ga = ga' /\ gk = gk'⌝ ∗ ▷ (∀ xs, Q xs ≡ Q' xs).
  Proof using .
    iIntros "H1 H2".
    iDestruct (saved_anything_agree with "H1 H2") as "Heq".
    rewrite /gen_el prod_equivI /=.
    iDestruct "Heq" as "[Hv Hf]".
    iDestruct "Hv" as %Hv.
    iSplitR.
    { iPureIntro.
      change ((pa, pid, ga, gk) = (pa', pid', ga', gk')) in Hv.
      split; [ exact (f_equal (fun z => fst (fst (fst z))) Hv) | ].
      split; [ exact (f_equal (fun z => snd (fst (fst z))) Hv) | ].
      split; [ exact (f_equal (fun z => snd (fst z)) Hv)
             | exact (f_equal snd Hv) ]. }
    rewrite discrete_fun_equivI.
    rewrite bi.later_forall. iIntros (xs).
    iSpecialize ("Hf" $! xs). by rewrite later_equivI.
  Qed.

  (* the shape every existing caller wants: the pure half and the payload *)
  Lemma gen_agree γ dq dq' pa pid ga gk Q pa' pid' ga' gk' Q' :
    gen_own γ dq pa pid ga gk Q -∗ gen_own γ dq' pa' pid' ga' gk' Q' -∗
    ⌜pa = pa' /\ pid = pid' /\ ga = ga' /\ gk = gk'⌝ ∗ ▷ (∀ xs, Q xs ≡ Q' xs).
  Proof using .
    iIntros "H1 H2".
    iDestruct (gen_agree_all with "H1 H2") as "($ & $)".
  Qed.

  (* the pure half alone, which is all most callers want *)
  Lemma gen_agree_pure γ dq dq' pa pid ga gk Q pa' pid' ga' gk' Q' :
    gen_own γ dq pa pid ga gk Q -∗ gen_own γ dq' pa' pid' ga' gk' Q' -∗
    ⌜pa = pa' /\ pid = pid' /\ ga = ga' /\ gk = gk'⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (gen_agree with "H1 H2") as "[$ _]".
  Qed.

  (* ...AND THE TAKEN TOKEN'S NAME AGREES PURELY -- it rides the [constOF]
     half, so pinning it costs no later. *)
  Lemma gen_taken_agree γ ga ga' :
    gen_taken γ ga -∗ gen_taken γ ga' -∗ ⌜ga = ga'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid gk Q) "H1".
    iDestruct "H2" as (pa' pid' gk' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & _ & Hga & _). done.
  Qed.

  (* ...AND THE ONE-SHOT'S NAME, on exactly the same footing *)
  Lemma gen_shotn_agree γ gk gk' :
    gen_shotn γ gk -∗ gen_shotn γ gk' -∗ ⌜gk = gk'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid ga Q) "H1".
    iDestruct "H2" as (pa' pid' ga' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & _ & _ & Hgk). done.
  Qed.

  Lemma gen_slot_agree γ pa pa' :
    gen_slot γ pa -∗ gen_slot γ pa' -∗ ⌜pa = pa'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (pid ga gk Q) "H1".
    iDestruct "H2" as (pid' ga' gk' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(Hpa & _ & _ & _). done.
  Qed.

  Lemma gen_pid_agree γ pid pid' :
    gen_pid γ pid -∗ gen_pid γ pid' -∗ ⌜pid = pid'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (pa ga gk Q) "H1".
    iDestruct "H2" as (pa' ga' gk' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & Hpid & _ & _). done.
  Qed.

  (* THE ESCROW'S QUARTER NAMES THE PID ITS GENERATION WAS GIVEN.  Stated
     at the DERIVED forms so a reaper never has to unfold [gen_own] -- the
     conclusion is pure, so both inputs survive ([ProofKwait]'s reap holds
     the quarter across it). *)
  Lemma gen_pid_kq_agree γ pa pid pid' Q :
    gen_pid γ pid' -∗ gen_kq γ pa pid Q -∗ ⌜pid' = pid⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (pa1 ga1 gk1 Q1) "H1".
    iDestruct "H2" as (ga2 gk2) "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & Hpid & _ & _). done.
  Qed.

  (* ...AND THE TWO PERSISTENT READINGS AT THE NAMED SLOT AND PID.  A
     reading has to come off the DISCARDED half, and the half's own slot
     and pid are existential; the kernel's quarter is what names them.
     The quarter comes back -- the agreement it is used for is pure. *)
  Lemma my_pay_kq_readings γ pa pid Q :
    my_pay γ Q -∗ gen_kq γ pa pid Q -∗
    gen_slot γ pa ∗ gen_pid γ pid ∗ gen_kq γ pa pid Q.
  Proof using .
    iIntros "#H1 H2".
    iDestruct "H1" as (pa1 pid1 ga1 gk1) "#Hd".
    iAssert (⌜pa1 = pa /\ pid1 = pid⌝)%I as %[-> ->].
    { iDestruct "H2" as (ga2 gk2) "H2".
      iDestruct (gen_agree_pure with "Hd H2") as %(Hpa & Hpid & _ & _).
      iPureIntro. exact (conj Hpa Hpid). }
    iSplitR; [ iExists pid, ga1, gk1, Q; iExact "Hd" | ].
    iSplitR; [ iExists pa, ga1, gk1, Q; iExact "Hd" | ]. iExact "H2".
  Qed.

  (* a quarter reads the pid the persistent fact records *)
  Lemma child_tok_pid γ pid pid' Q :
    child_tok γ pid Q -∗ gen_pid γ pid' -∗ ⌜pid = pid'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (pa ga gk) "H1".
    iDestruct "H2" as (pa' ga' gk' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %(_ & Hpid & _ & _). done.
  Qed.

  (* ...and the child's persistent knowledge is the parent's payload *)
  Lemma my_pay_agree γ Q Q' :
    my_pay γ Q -∗ my_pay γ Q' -∗ ▷ (∀ xs, Q xs ≡ Q' xs).
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid ga gk) "H1".
    iDestruct "H2" as (pa' pid' ga' gk') "H2".
    iDestruct (gen_agree with "H1 H2") as "[_ $]".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* WHAT A KILL OF THIS INCARNATION COSTS (owner, 2026-09-13).           *)
  (* ------------------------------------------------------------------ *)

  (* THE PRICE OF A KILL IS THE TARGET'S OWN EXIT PAYLOAD AT -1.  A killed
     process is torn down by the kernel at its next trap, which runs
     [exit(-1)] with the process's own continuation undelivered -- so
     nothing the PROGRAM does can pay at that moment, and what the parent
     is owed is [Q (-1)] whether the child called [exit(-1)] or was killed.
     The killer therefore pays exactly that, and nothing else has to be
     invented: the generation already tracks [Q].

     THE PAYLOAD IS EXISTENTIAL AND THE KNOWLEDGE IS BESIDE IT, because a
     killer scans the proc table and holds the row of whatever slot it
     landed on: it cannot name that slot's payload, only carry it.
     [my_pay] is the persistent reading that says WHOSE payload it is, and
     it is what the party that cashes the row agrees against. *)
  Definition kill_owed γ : iProp Σ :=
    (∃ Q : Z -> iProp Σ, my_pay γ Q ∗ Q (-1))%I.

  (* ...AND THE MARKER THAT REPLACES IT IN THE ROW ONCE IT HAS BEEN SPENT,
     with the token's NAME hidden: the row is read by parties that know the
     generation and not the token's ghost name, and the name is a pure
     component of the generation, so the persistent reading pins it. *)
  Definition taken_at γ : iProp Σ := (∃ ga, gen_taken γ ga ∗ taken_tok ga)%I.

  Lemma taken_at_of γ ga : gen_taken γ ga -∗ taken_tok ga -∗ taken_at γ.
  Proof using . iIntros "#Hg H". iExists ga. iFrame "Hg H". Qed.

  (* two of them cannot exist: the name is pinned purely and the token is
     exclusive.  This is what makes the take ONE-SHOT. *)
  (* ------------------------------------------------------------------ *)
  (* ...AND THE KILL FLAG'S ONE-SHOT AT THE GENERATION (lane SELF-KILL,
     P6).  The two states, with the name hidden exactly as [taken_at]
     hides the marker's: <p->lock>'s killed row is read by parties that
     know the generation and not the ghost's name, and the name is a pure
     component of the generation, so the persistent reading pins it.

     WHERE EACH LIVES.  [kill_pend] is in the row's ZERO arm -- it is what
     that arm's claim rests on -- and a writer that sets the flag shoots
     it there.  [kill_shot] is PERSISTENT, so from the moment of the first
     write every later opening of the row can hand a copy out; that is
     what [killed] relays to its caller and what [kexit] spends, two
     critical sections later, to refute the zero arm and take the
     payment. *)
  Definition kill_pend γ : iProp Σ :=
    (∃ gk, gen_shotn γ gk ∗ shot_pending gk)%I.

  Definition kill_shot γ : iProp Σ :=
    (∃ gk, gen_shotn γ gk ∗ shot_done gk)%I.

  Global Instance kill_shot_persistent γ : Persistent (kill_shot γ).
  Proof using . rewrite /kill_shot. apply _. Qed.

  Lemma kill_pend_of γ gk : gen_shotn γ gk -∗ shot_pending gk -∗ kill_pend γ.
  Proof using . iIntros "#Hg H". iExists gk. iFrame "Hg H". Qed.

  Lemma kill_shot_of γ gk : gen_shotn γ gk -∗ shot_done gk -∗ kill_shot γ.
  Proof using . iIntros "#Hg #H". iExists gk. iFrame "Hg H". Qed.

  (* WHAT A WRITER OF [p->killed] DOES, and the only producer of the shot
     state there is. *)
  Lemma kill_pend_fire γ : kill_pend γ ==∗ kill_shot γ.
  Proof using .
    iIntros "H". iDestruct "H" as (gk) "[#Hg H]".
    iMod (shot_fire with "H") as "#H". iModIntro.
    iApply (kill_shot_of γ gk with "Hg H").
  Qed.

  (* ...AND WHAT THE SHOT STATE BUYS: the zero arm of the row is refuted,
     which is exactly the fact [kexit] cannot read off the cell. *)
  Lemma kill_pend_shot γ : kill_pend γ -∗ kill_shot γ -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (gk1) "[#Hg1 H1]". iDestruct "H2" as (gk2) "[#Hg2 H2]".
    iDestruct (gen_shotn_agree with "Hg1 Hg2") as %->.
    iApply (shot_pending_done with "H1 H2").
  Qed.

  Lemma taken_at_excl γ : taken_at γ -∗ taken_at γ -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct "H1" as (ga1) "[#Hg1 H1]". iDestruct "H2" as (ga2) "[#Hg2 H2]".
    iDestruct (gen_taken_agree with "Hg1 Hg2") as %->.
    iApply (taken_tok_excl with "H1 H2").
  Qed.

  Lemma kill_owed_of γ (Q : Z -> iProp Σ) :
    my_pay γ Q -∗ Q (-1) -∗ kill_owed γ.
  Proof using . iIntros "#Hmy H". iExists Q. iFrame "Hmy H". Qed.

  (* ...AND WHAT IT COSTS TO CASH IT AT A NAMED PAYLOAD: one LATER.  The
     two readings are of one SAVED predicate, so they agree only up to the
     saved predicate's own later, and nothing here knows the payload is
     timeless.  The party that spends this is usertrap's exit path, which
     is under a [WP] with instructions still to run between the read and
     the [kexit], so the later is stripped by a program step and costs
     nothing. *)
  Lemma kill_owed_pay γ (Q : Z -> iProp Σ) :
    my_pay γ Q -∗ kill_owed γ -∗ ▷ Q (-1).
  Proof using .
    iIntros "#Hmy H". iDestruct "H" as (Q') "[#Hmy' HQ]".
    iDestruct (my_pay_agree with "Hmy' Hmy") as "#Heq".
    iNext. iSpecialize ("Heq" $! (-1)). iRewrite -"Heq". iExact "HQ".
  Qed.

  (* ...and the ESCROW names the pid it is keyed at, off the discarded
     half it carries beside the kernel's quarter: the two are pieces of one
     generation, so they agree on the pid, and the persistent reading is
     therefore free to whoever holds the escrow.  A reaping parent spends
     it to tell the generation it reaped from the one it is waiting for. *)
  Lemma exit_tok_pid γ pid xs : exit_tok γ pid xs -∗ gen_pid γ pid.
  Proof using .
    iIntros "H". iDestruct "H" as (pa Q Q') "(Hk & Hmy & _)".
    iDestruct "Hk" as (ga gk) "Hk".
    iDestruct "Hmy" as (pa' pid' ga' gk') "#Hmy".
    iDestruct (gen_agree_pure with "Hk Hmy") as %(_ & Hpid & _ & _).
    rewrite /gen_pid Hpid. iExists pa', ga', gk', Q'. iExact "Hmy".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* PID UNIQUENESS OVER A SET OF GENERATIONS -- what makes a returned    *)
  (* pid NAME one of them.                                                *)
  (*                                                                      *)
  (* wait() returns a pid, and a pid is reused; what a parent needs is    *)
  (* that no OTHER child of its own carries the pid it was just handed,   *)
  (* so that the returned number identifies the generation whose escrow   *)
  (* came with it.  That is a fact about the whole set [cs] of the        *)
  (* parent's live children, and it is PERSISTENT: each member's pid is   *)
  (* the persistent reading of its own generation, and the implication    *)
  (* beside it is pure.  It can therefore be extracted under <wait_lock>  *)
  (* -- where the registrations that prove it live                        *)
  (* ([WaitInv.children_inv_pid]) -- and survive the release.             *)
  (*                                                                      *)
  (* A BIG-OP AND NOT A [□]-WAND OVER [gen_pid]: the party that spends it *)
  (* holds [child_tok], a QUARTER, and a quarter cannot produce           *)
  (* [gen_pid] -- the readings come off the DISCARDED half alone.  So the *)
  (* summary has to HAND OUT each member's pid rather than ask for it,    *)
  (* which is what [gen_uniq_tok] then pairs with the parent's token.     *)
  (* ------------------------------------------------------------------ *)
  Definition gen_uniq (cs : gset gname) (pid : mword 32) (γ' : gname) : iProp Σ :=
    ([∗ set] γ ∈ cs, ∃ pidγ : mword 32,
       gen_pid γ pidγ ∗ ⌜pidγ = pid -> γ = γ'⌝)%I.

  Global Instance gen_uniq_persistent cs pid γ' : Persistent (gen_uniq cs pid γ').
  Proof using . apply _. Qed.

  (* one member's reading, out of the summary *)
  Lemma gen_uniq_at (cs : gset gname) (pid : mword 32) (γ' γ : gname) :
    γ ∈ cs ->
    gen_uniq cs pid γ' -∗ ∃ pidγ : mword 32,
      gen_pid γ pidγ ∗ ⌜pidγ = pid -> γ = γ'⌝.
  Proof using .
    intro Hin. iIntros "H".
    iApply (big_sepS_elem_of _ cs γ Hin with "H").
  Qed.

  (* THE FORM A PARENT SPENDS: it holds a token for one of its children at
     the pid it forked, and the reaper's summary says that child IS the
     generation the escrow is at. *)
  Lemma gen_uniq_tok (cs : gset gname) (pid : mword 32) (γ' γ : gname)
      (Q : Z -> iProp Σ) :
    γ ∈ cs ->
    gen_uniq cs pid γ' -∗ child_tok γ pid Q -∗ ⌜γ = γ'⌝.
  Proof using .
    intro Hin. iIntros "Hu Ht".
    iDestruct (gen_uniq_at cs pid γ' γ Hin with "Hu") as (pidγ) "[Hgp %Himp]".
    iDestruct (child_tok_pid with "Ht Hgp") as %Heq.
    iPureIntro. exact (Himp (eq_sym Heq)).
  Qed.

  (* ...AND ITS CONTRAPOSITIVE, which is what a parent whose wait returned
     SOMEBODY ELSE'S pid spends: the generation that was reaped is not the
     one it is waiting for, so its own child is still in the set the reap
     left. *)
  Lemma exit_tok_tok_ne γ' γ (pid pid' : mword 32) (xs : Z) (Q : Z -> iProp Σ) :
    pid <> pid' ->
    exit_tok γ' pid xs -∗ child_tok γ pid' Q -∗ ⌜γ <> γ'⌝.
  Proof using .
    intro Hne. iIntros "He Ht".
    iDestruct (exit_tok_pid with "He") as "#Hgp".
    destruct (decide (γ = γ')) as [-> | Hd].
    - iDestruct (child_tok_pid with "Ht Hgp") as %Heq.
      iPureIntro. exfalso. exact (Hne (eq_sym Heq)).
    - iPureIntro. exact Hd.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE PAYMENT RULE -- what the whole file exists for.                  *)
  (*                                                                      *)
  (* INDEXED BY THE GENERATION, NOT BY THE PID: a stale token (child       *)
  (* reaped, escrow dropped, pid reused by a later incarnation) can never  *)
  (* combine, because the two names differ and nothing agrees.            *)
  (* ------------------------------------------------------------------ *)
  Lemma gen_pay γ pid Q xs :
    child_tok γ pid Q -∗ exit_tok γ pid xs -∗ ▷ Q xs.
  Proof using .
    iIntros "Ht He".
    iDestruct "Ht" as (pa ga gk) "Ht".
    iDestruct "He" as (pa' Q0 Q') "[Hk [Hmy HQ]]".
    iDestruct "Hmy" as (pa'' pid' ga'' gk'') "Hmy".
    iDestruct (gen_agree with "Ht Hmy") as "[_ Heq]".
    iNext. iSpecialize ("Heq" $! xs). by iRewrite "Heq".
  Qed.

  (* ...AND THE LATER-FREE FORM, at a payload the parent can strip.  The
     conclusion is [◇], not [|==>]: a plain basic update does NOT absorb
     the except-0 modality (its [IsExcept0] instance demands it of the
     body), while every site that could consume the payload -- a fancy
     update, a WP step -- does.  So a TIMELESS payload costs its reaper an
     [iMod] and no step at all. *)
  Lemma gen_pay_timeless γ pid Q xs `{!Timeless (Q xs)} :
    child_tok γ pid Q -∗ exit_tok γ pid xs -∗ ◇ (Q xs).
  Proof using .
    iIntros "Ht He".
    iDestruct (gen_pay with "Ht He") as "H".
    iMod "H". by iModIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE MINT, THE CHOICE, AND THE SPLIT.                                 *)
  (* ------------------------------------------------------------------ *)

  (* ...and its second: the three pieces, out of the whole.  1/4 to the
     parent, 1/4 to the kernel's copy in the child's block, and the
     remaining half DISCARDED -- which is what makes [my_pay] (and with it
     [gen_slot] / [gen_pid]) persistent. *)
  (* ...AND THE PERSISTENT THIRD PIECE IS THE WHOLE READING NOW: the party
     that cuts the generation knows both components, and each later reader
     wants a different one ([gen_know_my_pay] and [gen_know_taken]).
     Handing out [my_pay] alone would lose the taken token's name at the
     one point where it is known. *)
  Lemma gen_split γ pa pid ga gk Q :
    gen_own γ (DfracOwn 1) pa pid ga gk Q ==∗
    child_tok γ pid Q ∗ gen_kq γ pa pid Q ∗ gen_know γ ga gk Q.
  Proof using .
    iIntros "H". rewrite /gen_own.
    iEval (rewrite -Qp.half_half) in "H".
    iDestruct "H" as "[H1 H2]".
    iMod (saved_anything_persist with "H2") as "#Hp".
    iEval (rewrite -Qp.quarter_quarter) in "H1".
    iDestruct "H1" as "[Ha Hb]".
    iModIntro. iSplitL "Ha".
    { iExists pa, ga, gk. iExact "Ha". }
    iSplitL "Hb"; [ iExists ga, gk; iExact "Hb" |].
    iExists pa, pid. iExact "Hp".
  Qed.

  (* ALLOCPROC's step, AND IT IS THE ONLY ONE (lane SELF-KILL, §4b',
     coordinator's ruling (A) of 2026-09-13).  A fresh incarnation of slot
     [pa] at the pid <allocpid> chose, AT THE PAYLOAD ITS CREATOR NAMES --
     the parent's choice for a forked child, the trivial one for <init>.

     WHY THE CHOICE MOVED HERE.  It used to be a two-step mint: allocproc
     made a WHOLE generation at the trivial payload and the fork row
     re-chose with [gen_set] before splitting.  That order is no longer
     possible.  [SchedCtx]'s killed row is per-INCARNATION now and
     allocproc is what stores the nonzero pid the row is keyed at, so
     allocproc has to CLOSE that row -- and the row names the generation
     PERSISTENTLY ([kpay], [my_pay]).  A persistent reading is a
     [DfracDiscarded] share, which only [gen_split] produces, and
     [gen_set] is [saved_anything_update] and needs [DfracOwn 1]:
     [DfracOwn 1 ⋅ DfracDiscarded] is invalid, so the whole and a reading
     cannot coexist.  Choosing at the mint dissolves the conflict, and
     nothing is lost -- the only thing [gen_set] ever did was re-choose a
     credential after allocation, and the credential IS the payload now.

     IT MINTS THE TAKEN TOKEN WITH IT.  The token's name goes into the
     element, so every later reading says which token belongs to this
     incarnation, and the token itself comes out beside the generation for
     whoever is building the process (it rides the private block). *)
  (* WHAT ALLOCPROC HANDS ITS CALLER, as ONE row: the three pieces of the
     generation and the token minted with it.  Bundled rather than handed
     out as four rows so that [SpecAllocproc]'s post keeps its arity and
     every pass-through site is untouched. *)
  (* IT MINTS THE KILL FLAG'S ONE-SHOT TOO, in the PENDING state, and that
     is where <p->lock>'s killed row's zero arm comes from: allocproc
     closes the fresh incarnation's row at a flag it has just read to be
     zero, and this is the token that arm holds. *)
  (* THE NAMES ARE GONE FROM THE INTERFACE.  Both ghosts are handed out at
     their GENERATION-indexed forms ([taken_at], [kill_pend]) and the
     persistent reading as [my_pay], so no caller of allocproc binds a
     ghost name it has no use for. *)
  Definition gen_new γ pa pid Q : iProp Σ :=
    (child_tok γ pid Q ∗ gen_kq γ pa pid Q ∗ my_pay γ Q ∗ taken_at γ)%I.

  (* ...and the persistent reading comes off the row WITHOUT spending it,
     which is what allocproc founds the killed row's payment publication
     on ([SchedCtx.kill_paid]'s live arm names the payload). *)
  Lemma gen_new_my_pay γ pa pid Q :
    gen_new γ pa pid Q -∗ my_pay γ Q ∗ gen_new γ pa pid Q.
  Proof using .
    iIntros "H". rewrite /gen_new.
    iDestruct "H" as "(Ht & Hk & #Hmy & Hta)".
    iFrame "Hmy Ht Hk Hta".
  Qed.

  Lemma gen_new_split γ pa pid Q :
    gen_new γ pa pid Q -∗
    child_tok γ pid Q ∗ gen_kq γ pa pid Q ∗ my_pay γ Q ∗ taken_at γ.
  Proof using . iIntros "H". iExact "H". Qed.

  (* THE ONE-SHOT IS BESIDE THE ROW AND NOT IN IT, because allocproc SPENDS
     it: it goes straight into <p->lock>'s killed row's zero arm at the
     store that gives the slot its new pid, and never reaches the caller. *)
  Lemma gen_alloc pa pid (Q : Z -> iProp Σ) :
    ⊢ |==> ∃ γ : gname, gen_new γ pa pid Q ∗ kill_pend γ.
  Proof using .
    iMod taken_tok_alloc as (ga) "Hga".
    iMod shot_pending_alloc as (gk) "Hgk".
    iMod (saved_anything_alloc (F := genF)
            (gen_el pa pid ga gk Q) (DfracOwn 1)
            ltac:(done)) as (γ) "Hg".
    iMod (gen_split with "Hg") as "(Htok & Hkq & #Hknow)".
    iModIntro. iExists γ. rewrite /gen_new.
    iDestruct (gen_know_my_pay with "Hknow") as "#Hmy".
    iDestruct (gen_know_taken with "Hknow") as "#Hgt".
    iDestruct (gen_know_shotn with "Hknow") as "#Hgs".
    iFrame "Htok Hkq Hmy".
    iSplitL "Hga"; [ iApply (taken_at_of γ ga with "Hgt Hga") | ].
    iApply (kill_pend_of γ gk with "Hgs Hgk").
  Qed.


  (* the escrow, built PAID: what kexit does with the block's quarter and
     the DEPOSIT the exiting process made at the trap boundary -- the
     process's own [my_pay] and the payload paid at the status kexit
     stored. *)
  Lemma exit_tok_intro γ pa pid Q Q' xs :
    gen_kq γ pa pid Q -∗ my_pay γ Q' -∗ Q' xs -∗ exit_tok γ pid xs.
  Proof using . iIntros "Hk #Hmy HQ". iExists pa, Q, Q'. iFrame "Hk Hmy HQ". Qed.

End ChildTok.

Global Typeclasses Opaque gen_own.
