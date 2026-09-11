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
(*                 fork chooses it ([SpecKfork]'s [gen_set]); exit pays   *)
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
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own saved_prop.
Require Import SailStdpp.Base SailStdpp.Values.
Local Open Scope Z_scope.

(* THE FUNCTOR.  A pair: the two VALUES the generation pins (its slot
   address and its pid, at [leibnizO] because both are discrete machine
   words) and the PREDICATE it saves (the exit payload, indexed by the exit
   status).  [constOF] on the left is what keeps the values out of the
   step-indexing: agreement on them is a PURE equality with no later,
   which is what [gen_agree] hands its callers. *)
Definition genF : oFunctor :=
  prodOF (constOF (leibnizO (Values.mword 64 * Values.mword 32)))
         (Z -d> ▶ ∙).

Global Instance genF_contractive : oFunctorContractive genF.
Proof. apply _. Qed.

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
Class ctokG (Σ : gFunctors) := CtokG { ctok_inG :: savedAnythingG Σ genF }.
Definition ctokΣ : gFunctors := #[ savedAnythingΣ genF ].
Global Instance subG_ctokΣ {Σ} : subG ctokΣ Σ -> ctokG Σ.
Proof. solve_inG. Qed.

Section ChildTok.
  Context `{!ctokG Σ}.

  Implicit Types (γ : gname) (dq : dfrac) (pa : Values.mword 64)
                 (pid : Values.mword 32) (Q : Z -> iProp Σ) (xs : Z).

  (* the saved element, spelled once: the pair of values, and the payload
     under [Next] (the functor's ▷) *)
  Definition gen_el pa pid Q : oFunctor_apply genF (iPropO Σ) :=
    (((pa, pid) : leibnizO (Values.mword 64 * Values.mword 32)), Next ∘ Q).

  (* A FRACTION OF A GENERATION.  Every piece below is this at a fraction. *)
  Definition gen_own γ dq pa pid Q : iProp Σ :=
    saved_anything_own (F := genF) γ dq (gen_el pa pid Q).

  (* ---- the readings, and they are facts only off the discarded half ---- *)

  (* the slot this incarnation occupies *)
  Definition gen_slot γ pa : iProp Σ :=
    (∃ pid Q, gen_own γ DfracDiscarded pa pid Q)%I.

  (* ...and the pid it was given.  A generation has one pid forever, which
     is what the escrow's pid-keyed reading in [SpecKwait]'s success arm
     stands on. *)
  Definition gen_pid γ pid : iProp Σ :=
    (∃ pa Q, gen_own γ DfracDiscarded pa pid Q)%I.

  (* THE CHILD'S KNOWLEDGE OF ITS OWN PAYLOAD.  Persistent, so it travels
     into the child's slot and survives exec ([UexecSlot.uvis_gen] does),
     and so that a slot -- re-established at every trap -- may name it
     without owning anything linear. *)
  Definition my_pay γ Q : iProp Σ :=
    (∃ pa pid, gen_own γ DfracDiscarded pa pid Q)%I.

  Global Instance gen_slot_persistent γ pa : Persistent (gen_slot γ pa).
  Proof. apply _. Qed.
  Global Instance gen_pid_persistent γ pid : Persistent (gen_pid γ pid).
  Proof. apply _. Qed.
  Global Instance my_pay_persistent γ Q : Persistent (my_pay γ Q).
  Proof. apply _. Qed.

  (* ---- the two linear quarters ---- *)

  (* THE PARENT'S QUARTER, handed to the forking process at [kfork]'s pid
     arm.  The slot is existential: a parent is told which CHILD it has,
     not which proc slot the kernel put it in. *)
  Definition child_tok γ pid Q : iProp Σ :=
    (∃ pa, gen_own γ (DfracOwn (1/4)%Qp) pa pid Q)%I.

  (* THE KERNEL'S QUARTER, in the child's private block. *)
  Definition gen_kq γ pa pid Q : iProp Σ :=
    gen_own γ (DfracOwn (1/4)%Qp) pa pid Q.

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
  Lemma gen_agree γ dq dq' pa pid Q pa' pid' Q' :
    gen_own γ dq pa pid Q -∗ gen_own γ dq' pa' pid' Q' -∗
    ⌜pa = pa' /\ pid = pid'⌝ ∗ ▷ (∀ xs, Q xs ≡ Q' xs).
  Proof.
    iIntros "H1 H2".
    iDestruct (saved_anything_agree with "H1 H2") as "Heq".
    rewrite /gen_el prod_equivI /=.
    iDestruct "Heq" as "[Hv Hf]".
    iDestruct "Hv" as %Hv.
    iSplitR.
    { iPureIntro. change ((pa, pid) = (pa', pid')) in Hv.
      split; [exact (f_equal fst Hv) | exact (f_equal snd Hv)]. }
    rewrite discrete_fun_equivI.
    rewrite bi.later_forall. iIntros (xs).
    iSpecialize ("Hf" $! xs). by rewrite later_equivI.
  Qed.

  (* the pure half alone, which is all most callers want *)
  Lemma gen_agree_pure γ dq dq' pa pid Q pa' pid' Q' :
    gen_own γ dq pa pid Q -∗ gen_own γ dq' pa' pid' Q' -∗
    ⌜pa = pa' /\ pid = pid'⌝.
  Proof.
    iIntros "H1 H2". iDestruct (gen_agree with "H1 H2") as "[$ _]".
  Qed.

  Lemma gen_slot_agree γ pa pa' :
    gen_slot γ pa -∗ gen_slot γ pa' -∗ ⌜pa = pa'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pid Q) "H1". iDestruct "H2" as (pid' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %[Hpa _]. done.
  Qed.

  Lemma gen_pid_agree γ pid pid' :
    gen_pid γ pid -∗ gen_pid γ pid' -∗ ⌜pid = pid'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa Q) "H1". iDestruct "H2" as (pa' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %[_ Hpid]. done.
  Qed.

  (* a quarter reads the pid the persistent fact records *)
  Lemma child_tok_pid γ pid pid' Q :
    child_tok γ pid Q -∗ gen_pid γ pid' -∗ ⌜pid = pid'⌝.
  Proof.
    iIntros "H1 H2". iDestruct "H1" as (pa) "H1". iDestruct "H2" as (pa' Q') "H2".
    iDestruct (gen_agree_pure with "H1 H2") as %[_ Hpid]. done.
  Qed.

  (* ...and the child's persistent knowledge is the parent's payload *)
  Lemma my_pay_agree γ Q Q' :
    my_pay γ Q -∗ my_pay γ Q' -∗ ▷ (∀ xs, Q xs ≡ Q' xs).
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (pa pid) "H1". iDestruct "H2" as (pa' pid') "H2".
    iDestruct (gen_agree with "H1 H2") as "[_ $]".
  Qed.

  (* ...and the ESCROW names the pid it is keyed at, off the discarded
     half it carries beside the kernel's quarter: the two are pieces of one
     generation, so they agree on the pid, and the persistent reading is
     therefore free to whoever holds the escrow.  A reaping parent spends
     it to tell the generation it reaped from the one it is waiting for. *)
  Lemma exit_tok_pid γ pid xs : exit_tok γ pid xs -∗ gen_pid γ pid.
  Proof.
    iIntros "H". iDestruct "H" as (pa Q Q') "(Hk & Hmy & _)".
    iDestruct "Hmy" as (pa' pid') "#Hmy".
    iDestruct (gen_agree_pure with "Hk Hmy") as %[_ Hpid].
    rewrite /gen_pid Hpid. iExists pa', Q'. iExact "Hmy".
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
  Proof. apply _. Qed.

  (* one member's reading, out of the summary *)
  Lemma gen_uniq_at (cs : gset gname) (pid : mword 32) (γ' γ : gname) :
    γ ∈ cs ->
    gen_uniq cs pid γ' -∗ ∃ pidγ : mword 32,
      gen_pid γ pidγ ∗ ⌜pidγ = pid -> γ = γ'⌝.
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
    iIntros "Ht He".
    iDestruct "Ht" as (pa) "Ht".
    iDestruct "He" as (pa' Q0 Q') "[Hk [Hmy HQ]]".
    iDestruct "Hmy" as (pa'' pid') "Hmy".
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
  Proof.
    iIntros "Ht He".
    iDestruct (gen_pay with "Ht He") as "H".
    iMod "H". by iModIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE MINT, THE CHOICE, AND THE SPLIT.                                 *)
  (* ------------------------------------------------------------------ *)

  (* ALLOCPROC's step: a fresh incarnation of slot [pa] at the pid
     <allocpid> chose, owed nothing.  The trivial payload is what a slot
     that is never forked with a real one keeps. *)
  Lemma gen_alloc pa pid :
    ⊢ |==> ∃ γ, gen_own γ (DfracOwn 1) pa pid (fun _ => True)%I.
  Proof.
    iApply (saved_anything_alloc (F := genF)
              (gen_el pa pid (fun _ => True)%I) (DfracOwn 1)).
    done.
  Qed.

  (* KFORK's first step: the FORKING PARENT chooses what the child's exit
     will owe.  Only at FULL ownership -- once the quarters are out, the
     payload is fixed for the life of the incarnation. *)
  Lemma gen_set γ pa pid Q Q' :
    gen_own γ (DfracOwn 1) pa pid Q ==∗ gen_own γ (DfracOwn 1) pa pid Q'.
  Proof.
    iApply (saved_anything_update (F := genF) (gen_el pa pid Q')).
  Qed.

  (* ...and its second: the three pieces, out of the whole.  1/4 to the
     parent, 1/4 to the kernel's copy in the child's block, and the
     remaining half DISCARDED -- which is what makes [my_pay] (and with it
     [gen_slot] / [gen_pid]) persistent. *)
  Lemma gen_split γ pa pid Q :
    gen_own γ (DfracOwn 1) pa pid Q ==∗
    child_tok γ pid Q ∗ gen_kq γ pa pid Q ∗ my_pay γ Q.
  Proof.
    iIntros "H". rewrite /gen_own.
    iEval (rewrite -Qp.half_half) in "H".
    iDestruct "H" as "[H1 H2]".
    iMod (saved_anything_persist with "H2") as "#Hp".
    iEval (rewrite -Qp.quarter_quarter) in "H1".
    iDestruct "H1" as "[Ha Hb]".
    iModIntro. iSplitL "Ha".
    { iExists pa. iExact "Ha". }
    iSplitL "Hb"; [iExact "Hb" |].
    iExists pa, pid. iExact "Hp".
  Qed.

  (* the escrow, built PAID: what kexit does with the block's quarter and
     the DEPOSIT the exiting process made at the trap boundary -- the
     process's own [my_pay] and the payload paid at the status kexit
     stored. *)
  Lemma exit_tok_intro γ pa pid Q Q' xs :
    gen_kq γ pa pid Q -∗ my_pay γ Q' -∗ Q' xs -∗ exit_tok γ pid xs.
  Proof. iIntros "Hk #Hmy HQ". iExists pa, Q, Q'. iFrame "Hk Hmy HQ". Qed.

End ChildTok.

Global Typeclasses Opaque gen_own.
