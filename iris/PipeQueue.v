(* PipeQueue.v -- A PIPE'S CONTENTS AS GHOST STATE: the sequence of every
   byte ever written to it and the read pointer ([PipeNames.pipe_st]), as
   ONE authority the kernel keeps inside [pi->lock]'s payload and ONE
   EXACT fragment its user holds.

   Design of record: claude-notes/design/pipe.md, "The byte queue".  In
   one paragraph: the state is [pipe_st] over
   [Xv6Cameras.pipeqR = excl_authR (leibnizO pipe_st)]; [pipe_qauth] is
   the kernel's authority, [pipe_qfrag] the fragment -- an EXACT view (the
   two agree, and neither moves without the other).  Every byte a write
   pushes and every byte a read dequeues therefore goes through a fupd the
   fragment's holder supplies -- the LINK (section 2) -- through which the
   holder moves its fragment atomically with the pipe, learns the exact
   instantaneous state (and, for a read, the byte), and may move ghosts of
   its own.  [WpUart.out_link]'s shape, one object over.

   ...OR THE PIPE IS TAINTED.  The generic-safety supply must pay every
   syscall's deposit at every key out of a PERSISTENT supply, and an exact
   fragment cannot be in it; so [pi->lock]'s payload keeps the authority
   COUPLED to the ring only until somebody moves the ring without the
   fragment, and then DISCONNECTS them for good ([PipeInvDefs.pipe_qres]:
   the coupled arm, or the taint).  The price of a disconnect is the
   application's TAINT ([app_taint], the machine's kill credential:
   bought by the generic supply, never held by a verified program under an
   untainted discipline), so a fragment holder's claim is "exact, or the
   application is tainted" -- the console's [cons_dirty_cred] shape, and
   echo's [pristine ∨ taint].  Every read/write payment is the disjunction
   LINKS ∨ TAINT, and every post is FIRED ∨ TAINT.

   Contents: the algebra (1), the three links (2), the two CHAINS the
   read/write contracts take (3), the payments and the POSTS they hand
   back (4).  No machine model and no WP: the file sits below
   [PipeInvDefs], so anything that names a descriptor state can name a
   queue. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list gmap bitvector.definitions.
From iris.algebra Require Import auth cmra updates.
From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.       (* [riscvGS], [app_taint] *)
Require Import UserPtTree.       (* [uptd], [uva_rmapped], [umem_wr] *)
Require Export PipeNames.
Require Export Xv6Cameras.
Local Open Scope Z_scope.

Section PipeQueue.
  Context `{!riscvGS Σ, !pipeG Σ}.

  (* ================================================================== *)
  (*  1.  THE ALGEBRA                                                    *)
  (* ================================================================== *)

  (* THE AUTHORITY: the kernel's, inside [pi->lock] ([PipeInvDefs.pipe_qres]) *)
  Definition pipe_qauth (γ : gname) (s : pipe_st) : iProp Σ :=
    own γ (●E (s : leibnizO pipe_st)).
  (* THE FRAGMENT: exact and exclusive -- what [sys_pipe] hands the process
     that created the pipe, and what its links are built out of *)
  Definition pipe_qfrag (γ : gname) (s : pipe_st) : iProp Σ :=
    own γ (◯E (s : leibnizO pipe_st)).

  Global Instance pipe_qauth_timeless γ s : Timeless (pipe_qauth γ s).
  Proof using . rewrite /pipe_qauth. apply _. Qed.
  Global Instance pipe_qfrag_timeless γ s : Timeless (pipe_qfrag γ s).
  Proof using . rewrite /pipe_qfrag. apply _. Qed.

  (* minted by [PipeInv.new_pipe] at the birth state, beside the two ends *)
  Lemma pipe_queue_alloc : ⊢ |==> ∃ γ : gname, pipe_qauth γ pst0 ∗ pipe_qfrag γ pst0.
  Proof using .
    iMod (own_alloc (●E (pst0 : leibnizO pipe_st) ⋅ ◯E (pst0 : leibnizO pipe_st)))
      as (γ) "[Ha Hf]"; [apply excl_auth_valid |].
    iModIntro. iExists γ. iFrame "Ha Hf".
  Qed.

  (* the fragment IS the state *)
  Lemma pipe_queue_agree γ s s' :
    pipe_qauth γ s -∗ pipe_qfrag γ s' -∗ ⌜s' = s⌝.
  Proof using .
    iIntros "Ha Hf". iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro. symmetry. exact (excl_auth_agree_L _ _ Hv).
  Qed.

  Lemma pipe_qfrag_excl γ s s' : pipe_qfrag γ s -∗ pipe_qfrag γ s' -∗ False.
  Proof using .
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    exfalso. exact (proj1 (excl_auth_frag_op_valid _ _) Hv).
  Qed.

  Lemma pipe_qauth_excl γ s s' : pipe_qauth γ s -∗ pipe_qauth γ s' -∗ False.
  Proof using .
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    exfalso. exact (proj1 (excl_auth_auth_op_valid _ _) Hv).
  Qed.

  (* THE ONE STEP, and it needs both halves *)
  Lemma pipe_queue_update γ s s' (s'' : pipe_st) :
    pipe_qauth γ s -∗ pipe_qfrag γ s' ==∗ pipe_qauth γ s'' ∗ pipe_qfrag γ s''.
  Proof using .
    iIntros "Ha Hf". rewrite /pipe_qauth /pipe_qfrag -own_op.
    iApply (own_update_2 with "Ha Hf"). apply excl_auth_update.
  Qed.

  (* THE PRICE OF A DISCONNECT (design/pipe.md) IS THE APPLICATION'S TAINT
     ([RiscvPtsto.app_taint], the credential the machine already fixes for a
     kill): persistent, timeless, bought by the generic supply
     ([UexecExecInst.xv6_ssupply]) and by no verified program under an
     untainted discipline.  There is no pipe-local alias for it -- one
     resource, one name -- so every payment below names [app_taint]. *)

  (* ================================================================== *)
  (*  2.  THE LINKS: one fupd per step, supplied by the fragment's holder  *)
  (* ================================================================== *)

  (* THE MASK IS ⊤, and unlike the console's it is not forced: the pipe's
     payload is HELD by the thread that steps it (the lock is taken), so
     no invariant is open at the step.  A holder's fupd may open anything
     of its own -- the application invariant its fragment lives in. *)

  (* an OBSERVATION: the state is read and not moved.  Fired where a call
     stops because of the state -- piperead where the ring ran dry (an
     end-of-file is then a fact about the ghost state, [pst_eof]),
     pipewrite where the read end is shut. *)
  Definition pipe_olink (γ : gname) (Φ : pipe_st -> iProp Σ) : iProp Σ :=
    (∀ s : pipe_st, pipe_qauth γ s ={⊤}=∗ pipe_qauth γ s ∗ Φ s)%I.

  (* ...AND THE TWO END-KEYED OBSERVATIONS THE CHAINS ACTUALLY USE (lane
     PIPE-RO).  An observation node is fired by ONE of the two calls, and
     each of them runs on behalf of a process holding ONE END OPEN -- which
     the caller's credential proves ([PipeInvDefs.pipe_endstate_holder] at
     the end the contract is entered with: [SpecPipewrite]'s [w = true],
     [SpecPiperead]'s [w = false]).  Publishing that end to the observation
     is what gives the protocol the ORDER of the two enders, and with it the
     law that no round can be SHORT (design app-pipe.md SS4.3w, purchase 5;
     [PipeProto.pipe_no_short]):

     - the WRITER's observation fires at a shut READ end, and carries
       [ps_wo s = true] -- so no writer can observe after an end-of-file has
       been read, because an end-of-file is read at [ps_wo s = false] (P3);
     - the READER's observation fires at a dry ring, and carries
       [ps_ro s = true] -- so no end-of-file can be read after the read end
       has been seen shut, because that is (P4)'s [ps_ro s = false].

     Neither restricts the code and neither is a new fact about it: both are
     the caller's own credential, read through [pipe_qres]'s coupled arm.
     As with the write link, a premise WEAKENS the link, so an unconditional
     observer is still one of each ([pipe_wolink_of_olink] /
     [pipe_rolink_of_olink]) and no holder loses anything. *)
  Definition pipe_wolink (γ : gname) (Φ : pipe_st -> iProp Σ) : iProp Σ :=
    (∀ s : pipe_st,
       ⌜ps_wo s = true⌝ -∗ pipe_qauth γ s ={⊤}=∗ pipe_qauth γ s ∗ Φ s)%I.

  Definition pipe_rolink (γ : gname) (Φ : pipe_st -> iProp Σ) : iProp Σ :=
    (∀ s : pipe_st,
       ⌜ps_ro s = true⌝ -∗ pipe_qauth γ s ={⊤}=∗ pipe_qauth γ s ∗ Φ s)%I.

  (* THE WRITE LINK CARRIES TWO PURE PREMISES, AND BOTH FLAGS ARE OPEN at
     the state the byte lands in: [ps_wo s = true] (lane PQ-FLAG, design
     3.1) and [ps_ro s = true] (lane PQ-FLAG-2, design 3.1b).  Both are
     free of the machine, and neither restricts the code -- they differ in
     WHERE the fire site gets them:

     - [ps_wo s = true] comes from the CALLER'S CREDENTIAL.  [pipewrite]
       never loads [pi->writeopen]; instead it runs on behalf of a process
       holding a WRITABLE file on this pipe, so [SpecPipewrite] pins the
       end it is entered with to the write end and
       [PipeInvDefs.pipe_endstate_holder] reads [writeopen <> 0] off the
       payload against that share.
     - [ps_ro s = true] is the CODE'S OWN: [pipewrite] tests
       [pi->readopen == 0] under the SAME lock hold immediately before each
       byte's store (kernel/pipe.c -- the test, then either the full-ring
       sleep that loops back to the test, or the store), so the fire site
       simply reads the branch it is on.

     Both cross to the ghost through [pipe_qres]'s coupled arm, which reads
     [ps_wo s = pflag_bool wo] and [ps_ro s = pflag_bool ro].

     WHAT THEY BUY, in one line each.  The write-open premise FREEZES a
     pipe's contents at end-of-file: no write link fires after the write
     end shut, so a snapshot taken at [ps_wo s = false] is final (3.1's
     (P3)).  The read-open premise DERAILS a writer whose reader is gone:
     a holder that has once observed [ps_ro s = false] owns a persistent
     one-shot, and [ps_ro] is monotone (only [pst_close false] moves it,
     one way), so every later write link is VACUOUS -- which is how a
     program composes past a write that stopped short without lending
     anything across [fork]/[exec] (3.1b's (P4), lane ECHO-PIPE's wall).

     A premise WEAKENS what a holder has to supply, so no holder loses
     anything ([pipe_wlink_of_uncond] below). *)
  Definition pipe_wlink (γ : gname) (b : bv 8) (Φ : iProp Σ) : iProp Σ :=
    (∀ s : pipe_st,
       ⌜ps_wo s = true⌝ -∗ ⌜ps_ro s = true⌝ -∗ pipe_qauth γ s
       ={⊤}=∗ pipe_qauth γ (pst_write b s) ∗ Φ)%I.

  (* a read's link is told WHICH byte it dequeues; the kernel proves the
     pure premise from the ring coupling.

     IT CARRIES NO [ps_ro s = true] (lane PQ-FLAG, refuting the symmetric
     half of design/app-pipe.md 3.1, which called it "free"): piperead never
     reads [pi->readopen], so the only route to the fact is the caller's own
     [pipe_ref γp false q] -- and the FILE layer picks a pipe's end off
     [FileInvDefs.fc_wbool C] ([file_core_noff]), while fileread's pipe arm
     learns only [f->readable <> 0].  "A readable pipe file is the read end"
     is true of pipealloc and is nowhere in the file invariant, so the
     premise was unsupplyable at the fire site.

     PIPE-RO BUYS THE MISSING PUBLISHER: a pipe file's two ends are
     complementary ([FileInvDefs.fdpipe_ends], one conjunct on
     [fdstate_ok]'s pipe arm, paid by pipealloc's own stores), so a READABLE
     pipe row IS the read end, [SpecPiperead] is entered at [w = false], and
     the fire site reads [readopen <> 0] off the caller's share exactly as
     [pipewrite] reads [writeopen <> 0] off its own.

     WHAT IT BUYS is not this link -- a read moves neither flag nor the
     contents -- but the READER'S OBSERVATION beside it ([pipe_rolink]),
     whose end-of-file node is the protocol's second ender.  It is stated
     here for symmetry with [pipe_wlink] and because the fire site has it
     for free once per round; an older holder loses nothing
     ([pipe_rlink_of_uncond]). *)
  Definition pipe_rlink (γ : gname) (Φ : bv 8 -> iProp Σ) : iProp Σ :=
    (∀ (s : pipe_st) (b : bv 8),
       ⌜ps_ro s = true⌝ -∗ ⌜pst_next s = Some b⌝ -∗ pipe_qauth γ s
       ={⊤}=∗ pipe_qauth γ (pst_read s) ∗ Φ b)%I.

  (* closing end [w]: fired by pipeclose at the store that clears the flag
     word, i.e. at the LAST fileclose of that end -- the only place a flag
     word ever changes *)
  Definition pipe_clink (γ : gname) (w : bool) (Φ : iProp Σ) : iProp Σ :=
    (∀ s : pipe_st, pipe_qauth γ s ={⊤}=∗ pipe_qauth γ (pst_close w s) ∗ Φ)%I.

  (* THE HOLDER'S CONSTRUCTORS: a link out of the fragment.  The holder
     lends its fragment for the step and gets it back moved, under its own
     fupd, in which it may move whatever else it owns -- give the fragment
     straight back (a program that keeps it), or exchange it inside an
     invariant of its own. *)
  Lemma pipe_olink_of_frag γ (Φ : pipe_st -> iProp Σ) (s0 : pipe_st) :
    pipe_qfrag γ s0 -∗ (pipe_qfrag γ s0 ={⊤}=∗ Φ s0) -∗ pipe_olink γ Φ.
  Proof using .
    iIntros "Hf Hk" (s) "Ha".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod ("Hk" with "Hf") as "HΦ". iModIntro. iFrame "Ha HΦ".
  Qed.

  Lemma pipe_wlink_of_frag γ b (Φ : iProp Σ) (s0 : pipe_st) :
    pipe_qfrag γ s0 -∗
    (pipe_qfrag γ (pst_write b s0) ={⊤}=∗ Φ) -∗
    pipe_wlink γ b Φ.
  Proof using .
    iIntros "Hf Hk" (s) "_ _ Ha".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod (pipe_queue_update _ _ _ (pst_write b s0) with "Ha Hf") as "[Ha Hf]".
    iMod ("Hk" with "Hf") as "HΦ". iModIntro. iFrame "Ha HΦ".
  Qed.

  Lemma pipe_wolink_of_frag γ (Φ : pipe_st -> iProp Σ) (s0 : pipe_st) :
    pipe_qfrag γ s0 -∗ (pipe_qfrag γ s0 ={⊤}=∗ Φ s0) -∗ pipe_wolink γ Φ.
  Proof using .
    iIntros "Hf Hk" (s) "_ Ha".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod ("Hk" with "Hf") as "HΦ". iModIntro. iFrame "Ha HΦ".
  Qed.

  Lemma pipe_rolink_of_frag γ (Φ : pipe_st -> iProp Σ) (s0 : pipe_st) :
    pipe_qfrag γ s0 -∗ (pipe_qfrag γ s0 ={⊤}=∗ Φ s0) -∗ pipe_rolink γ Φ.
  Proof using .
    iIntros "Hf Hk" (s) "_ Ha".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod ("Hk" with "Hf") as "HΦ". iModIntro. iFrame "Ha HΦ".
  Qed.

  Lemma pipe_rlink_of_frag γ (Φ : bv 8 -> iProp Σ) (s0 : pipe_st) :
    pipe_qfrag γ s0 -∗
    (∀ b : bv 8, ⌜pst_next s0 = Some b⌝ -∗ pipe_qfrag γ (pst_read s0) ={⊤}=∗ Φ b) -∗
    pipe_rlink γ Φ.
  Proof using .
    iIntros "Hf Hk" (s b) "_ %Hb Ha".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod (pipe_queue_update _ _ _ (pst_read s0) with "Ha Hf") as "[Ha Hf]".
    iMod ("Hk" with "[%] Hf") as "HΦ"; [exact Hb |]. iModIntro. iFrame "Ha HΦ".
  Qed.

  Lemma pipe_clink_of_frag γ w (Φ : iProp Σ) (s0 : pipe_st) :
    pipe_qfrag γ s0 -∗
    (pipe_qfrag γ (pst_close w s0) ={⊤}=∗ Φ) -∗
    pipe_clink γ w Φ.
  Proof using .
    iIntros "Hf Hk" (s) "Ha".
    iDestruct (pipe_queue_agree with "Ha Hf") as %<-.
    iMod (pipe_queue_update _ _ _ (pst_close w s0) with "Ha Hf") as "[Ha Hf]".
    iMod ("Hk" with "Hf") as "HΦ". iModIntro. iFrame "Ha HΦ".
  Qed.

  Lemma pipe_olink_mono γ (Φ Φ' : pipe_st -> iProp Σ) :
    (∀ s, Φ s -∗ Φ' s) -∗ pipe_olink γ Φ -∗ pipe_olink γ Φ'.
  Proof using .
    iIntros "Hw Hl" (s) "Ha". iMod ("Hl" with "Ha") as "[$ HΦ]".
    iModIntro. by iApply "Hw".
  Qed.

  Lemma pipe_wlink_mono γ b (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ pipe_wlink γ b Φ -∗ pipe_wlink γ b Φ'.
  Proof using .
    iIntros "Hw Hl" (s) "%Hwo %Hro Ha".
    iMod ("Hl" with "[%] [%] Ha") as "[$ HΦ]"; [exact Hwo | exact Hro |].
    iModIntro. by iApply "Hw".
  Qed.

  (* SANITY, and the only direction that is true (lanes PQ-FLAG, PQ-FLAG-2):
     the premises WEAKEN the link.  An UNCONDITIONAL stepper -- the link as
     it was before 3.1 -- is still a [pipe_wlink], so every holder-side
     constructor and every chain node keeps working and nothing a holder
     could build before is lost.  The CONVERSE is false and deliberately not
     stated: a link that may assume both ends open cannot step a state with
     either shut, which is exactly the freeze (3.1) and the derail (3.1b)
     the protocol buys. *)
  Lemma pipe_wlink_of_uncond γ b (Φ : iProp Σ) :
    (∀ s : pipe_st, pipe_qauth γ s ={⊤}=∗ pipe_qauth γ (pst_write b s) ∗ Φ) -∗
    pipe_wlink γ b Φ.
  Proof using . iIntros "Hl" (s) "_ _ Ha". iApply ("Hl" $! s with "Ha"). Qed.

  (* ...and the one-premise link of 3.1 is still one too: the read-open
     premise alone weakens it further.  Stated so that a PQ-FLAG-era holder
     (a builder that knows only [ps_wo]) needs no rework. *)
  Lemma pipe_wlink_of_wo_only γ b (Φ : iProp Σ) :
    (∀ s : pipe_st, ⌜ps_wo s = true⌝ -∗ pipe_qauth γ s
       ={⊤}=∗ pipe_qauth γ (pst_write b s) ∗ Φ) -∗
    pipe_wlink γ b Φ.
  Proof using .
    iIntros "Hl" (s) "%Hwo _ Ha". iApply ("Hl" $! s with "[%] Ha"). exact Hwo.
  Qed.

  Lemma pipe_rlink_mono γ (Φ Φ' : bv 8 -> iProp Σ) :
    (∀ b : bv 8, Φ b -∗ Φ' b) -∗ pipe_rlink γ Φ -∗ pipe_rlink γ Φ'.
  Proof using .
    iIntros "Hw Hl" (s b) "%Hro %Hb Ha".
    iMod ("Hl" with "[%] [%] Ha") as "[$ HΦ]"; [exact Hro | exact Hb |].
    iModIntro. by iApply "Hw".
  Qed.

  (* ...and the read link's own sanity lemma (lane PIPE-RO, the mirror of
     [pipe_wlink_of_uncond]): the PQ-FLAG-era unconditional read stepper is
     still a [pipe_rlink], so nothing a holder could build before is lost.
     The converse is false and deliberately not stated -- a link that may
     assume the read end open cannot step a state with it shut, which is
     exactly what the reader-side order is bought with. *)
  Lemma pipe_rlink_of_uncond γ (Φ : bv 8 -> iProp Σ) :
    (∀ (s : pipe_st) (b : bv 8), ⌜pst_next s = Some b⌝ -∗ pipe_qauth γ s
       ={⊤}=∗ pipe_qauth γ (pst_read s) ∗ Φ b) -∗
    pipe_rlink γ Φ.
  Proof using .
    iIntros "Hl" (s b) "_ %Hb Ha". iApply ("Hl" $! s b with "[%] Ha"). exact Hb.
  Qed.

  Lemma pipe_wolink_mono γ (Φ Φ' : pipe_st -> iProp Σ) :
    (∀ s, Φ s -∗ Φ' s) -∗ pipe_wolink γ Φ -∗ pipe_wolink γ Φ'.
  Proof using .
    iIntros "Hw Hl" (s) "%Hwo Ha". iMod ("Hl" with "[%] Ha") as "[$ HΦ]"; [exact Hwo |].
    iModIntro. by iApply "Hw".
  Qed.

  Lemma pipe_rolink_mono γ (Φ Φ' : pipe_st -> iProp Σ) :
    (∀ s, Φ s -∗ Φ' s) -∗ pipe_rolink γ Φ -∗ pipe_rolink γ Φ'.
  Proof using .
    iIntros "Hw Hl" (s) "%Hro Ha". iMod ("Hl" with "[%] Ha") as "[$ HΦ]"; [exact Hro |].
    iModIntro. by iApply "Hw".
  Qed.

  (* an unconditional OBSERVER is still one of each (lane PIPE-RO) *)
  Lemma pipe_wolink_of_olink γ (Φ : pipe_st -> iProp Σ) :
    pipe_olink γ Φ -∗ pipe_wolink γ Φ.
  Proof using .
    rewrite /pipe_olink /pipe_wolink. iIntros "Hl" (s) "_ Ha".
    iApply ("Hl" $! s with "Ha").
  Qed.

  Lemma pipe_rolink_of_olink γ (Φ : pipe_st -> iProp Σ) :
    pipe_olink γ Φ -∗ pipe_rolink γ Φ.
  Proof using .
    rewrite /pipe_olink /pipe_rolink. iIntros "Hl" (s) "_ Ha".
    iApply ("Hl" $! s with "Ha").
  Qed.

  Lemma pipe_clink_mono γ w (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ pipe_clink γ w Φ -∗ pipe_clink γ w Φ'.
  Proof using .
    iIntros "Hw Hl" (s) "Ha". iMod ("Hl" with "Ha") as "[$ HΦ]".
    iModIntro. by iApply "Hw".
  Qed.

  (* ================================================================== *)
  (*  3.  THE CHAINS: what pipewrite / piperead take                      *)
  (* ================================================================== *)

  (* THE WRITE CHAIN is [SpecConsolewrite.cons_out_chain] with the pipe's
     link in place of the port's: one node per byte of the caller's run at
     the caller's PREFIX CURSOR [Q j] ("what I know after [j] bytes
     landed"), the byte at node [j] pinned to the image the caller lent at
     [ua + j] -- the pointwise reading copyin's post gives -- and beside
     them an OBSERVATION [Qe j s]: what the caller wants to be told if the
     loop stops at this node because the read end is shut ([ps_ro s =
     false]).  The kernel eliminates a node to one of its three conjuncts
     and hands the node back where it stops; the caller reads its cursor
     off the node ([pipe_wchain_cursor]).  The [∧] is additive: the choice
     is the KERNEL's. *)
  Fixpoint pipe_wchain (γ : gname) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) (j cnt : nat) : iProp Σ :=
    match cnt with
    | O => Q j
    | S cnt' =>
        (Q j
         ∧ pipe_wolink γ (Qe j)
         ∧ (∀ b : bv 8,
              ⌜M !! uint (add_vec_int ua (Z.of_nat j)) = Some b⌝ -∗
              pipe_wlink γ b (pipe_wchain γ M ua Q Qe (S j) cnt')))%I
    end.

  Lemma pipe_wchain_0 γ M ua Q Qe j : pipe_wchain γ M ua Q Qe j 0 ⊣⊢ Q j.
  Proof using . reflexivity. Qed.

  Lemma pipe_wchain_cursor γ M ua Q Qe j cnt : pipe_wchain γ M ua Q Qe j cnt -∗ Q j.
  Proof using . destruct cnt; [by iIntros "$" | by iIntros "[$ _]"]. Qed.

  (* THE READ CHAIN is over the DEQUEUED bytes: the cursor is [Q acc]
     ("what I know having taken [acc] out of the pipe"), node [acc]'s link
     hands the next byte to the next node, and the observation [Qe acc s]
     is fired if the loop stops at this node because the ring ran dry
     ([pst_empty s]; at nothing delivered that is an end-of-file, [pst_eof
     s]).  A read runs under one lock hold, so nothing else moves the queue
     between two nodes; the chain is per byte because the proof steps the
     ghost at each [nread++]. *)
  Fixpoint pipe_rchain (γ : gname) (Q : list (bv 8) -> iProp Σ)
      (Qe : list (bv 8) -> pipe_st -> iProp Σ)
      (acc : list (bv 8)) (cnt : nat) : iProp Σ :=
    match cnt with
    | O => Q acc
    | S cnt' =>
        (Q acc
         ∧ pipe_rolink γ (Qe acc)
         ∧ pipe_rlink γ (fun b => pipe_rchain γ Q Qe (acc ++ [b]) cnt'))%I
    end.

  Lemma pipe_rchain_0 γ Q Qe acc : pipe_rchain γ Q Qe acc 0 ⊣⊢ Q acc.
  Proof using . reflexivity. Qed.

  Lemma pipe_rchain_cursor γ Q Qe acc cnt : pipe_rchain γ Q Qe acc cnt -∗ Q acc.
  Proof using . destruct cnt; [by iIntros "$" | by iIntros "[$ _]"]. Qed.

  (* ================================================================== *)
  (*  4.  PAYMENTS AND POSTS                                              *)
  (* ================================================================== *)

  (* WHAT A CALLER PAYS: its links, or the taint.  The generic supply pays
     the taint out of its kill credential ([FsAbsInvFire]); a program that
     holds the fragment (or whose application invariant does) pays the
     links.  Every post below hands a caller that paid links and met a
     tainted pipe its payment back UNTOUCHED beside the credential. *)
  Definition pipe_wpay (γ : gname) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) (n : nat) : iProp Σ :=
    (pipe_wchain γ M ua Q Qe 0 n ∨ app_taint)%I.

  Definition pipe_rpay (γ : gname) (Q : list (bv 8) -> iProp Σ)
      (Qe : list (bv 8) -> pipe_st -> iProp Σ) (n : nat) : iProp Σ :=
    (pipe_rchain γ Q Qe [] n ∨ app_taint)%I.

  Definition pipe_cpay (γ : gname) (w : bool) (Φ : iProp Σ) : iProp Σ :=
    (pipe_clink γ w Φ ∨ app_taint)%I.

  Lemma pipe_wpay_taint γ M ua Q Qe n : app_taint -∗ pipe_wpay γ M ua Q Qe n.
  Proof using . iIntros "#H". rewrite /pipe_wpay. by iRight. Qed.
  Lemma pipe_rpay_taint γ Q Qe n : app_taint -∗ pipe_rpay γ Q Qe n.
  Proof using . iIntros "#H". rewrite /pipe_rpay. by iRight. Qed.
  Lemma pipe_cpay_taint γ w Φ : app_taint -∗ pipe_cpay γ w Φ.
  Proof using . iIntros "#H". rewrite /pipe_cpay. by iRight. Qed.

  (* A CLOSE'S POST.  The link FIRES exactly at the LAST fileclose of the
     end (the one that reaches pipeclose and clears the flag word), and the
     coupled arm of the lock invariant is what forces it: the flag word
     moves, so the ghost must.  [last] is what the closer can say about
     that -- a holder of the WHOLE reference ([q = 1]) is the last closer;
     any other closer may or may not be, and gets its payment back if it
     was not.  Tainted: the payment back beside the credential. *)
  Definition pipe_cpost (γ : gname) (w : bool) (Φ : iProp Σ) (last : bool) : iProp Σ :=
    (Φ
     ∨ (app_taint ∗ pipe_cpay γ w Φ)
     ∨ (⌜last = false⌝ ∗ pipe_cpay γ w Φ))%I.

  Lemma pipe_cpost_fired γ w Φ last : Φ -∗ pipe_cpost γ w Φ last.
  Proof using . iIntros "H". rewrite /pipe_cpost. by iLeft. Qed.
  Lemma pipe_cpost_taint γ w Φ last :
    app_taint -∗ pipe_cpay γ w Φ -∗ pipe_cpost γ w Φ last.
  Proof using . iIntros "#Ht Hp". rewrite /pipe_cpost. iRight. iLeft. iFrame "Hp Ht". Qed.
  Lemma pipe_cpost_unfired γ w Φ :
    pipe_cpay γ w Φ -∗ pipe_cpost γ w Φ false.
  Proof using . iIntros "Hp". rewrite /pipe_cpost. iRight. iRight. by iFrame "Hp". Qed.

  (* A WRITE'S POST.  FIRED, at the stop cursor [k] (the bytes pushed) with
     the answer: [k] itself -- the whole request, or copyin's reason for
     stopping (byte [k] of the run is not readable at the table the call
     was handed; [copyin_read]'s -1 arm, stated at the ENTRY descriptor
     because the map only grows), where the C answers -1 instead of 0 when
     the very first byte is the unreadable one (and the file layer's sign
     guard answers -1 at the empty count) -- or -1 with its reason: the
     writer was killed while the ring was full (node [k] untouched, [Rk] the
     incarnation's kill shot), or the read end is shut, OBSERVED at node [k]
     -- and an observation SPENDS the node: a chain node is [Q k ∧ olink ∧
     wlinks], one additive conjunction, so the observing arm hands back
     [Qe k s] and nothing else at [k] (a caller that wants its cursor back
     there puts it inside its own [Qe k]).  OR TAINT: the pipe was, or is
     now, disconnected -- the payment comes back untouched beside the
     credential.  A write is not atomic (it sleeps when the ring is full)
     so there is no snapshot: what a caller learns per byte, it learns in
     its own cursor. *)
  Definition pipe_wpost (P : uptd) (γ : gname) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) (Rk : iProp Σ)
      (n : nat) (r : mword 64) : iProp Σ :=
    ((∃ k : nat,
        ⌜(k <= n)%nat⌝ ∗
        ((⌜r = (mword_of_int (Z.of_nat k) : mword 64)
           \/ (k = 0%nat /\ r = (mword_of_int (-1) : mword 64))⌝ ∗
          ⌜k = n \/ ~ uva_rmapped P (uint (add_vec_int ua (Z.of_nat k)))⌝ ∗
          pipe_wchain γ M ua Q Qe k (n - k))
         ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜(k < n)%nat⌝ ∗ Rk ∗
            pipe_wchain γ M ua Q Qe k (n - k))
         ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜(k < n)%nat⌝ ∗
            ∃ s : pipe_st, ⌜ps_ro s = false⌝ ∗ Qe k s)))
     ∨ (app_taint ∗ pipe_wpay γ M ua Q Qe n))%I.

  (* the sign guard's exit, from the payment alone *)
  Lemma pipe_wpost_neg P γ M ua Q Qe Rk r :
    r = (mword_of_int (-1) : mword 64) ->
    pipe_wpay γ M ua Q Qe 0 -∗ pipe_wpost P γ M ua Q Qe Rk 0 r.
  Proof using .
    intros ->. iIntros "[Hch | #Ht]".
    - iLeft. iExists 0%nat. iSplitR; [by iPureIntro |].
      iLeft. iSplitR; [iPureIntro; by right |].
      iSplitR; [iPureIntro; by left |]. iExact "Hch".
    - iRight. iSplitR; [iExact "Ht" |]. by iApply pipe_wpay_taint.
  Qed.

  (* what every arm leaves at the cursor: the caller's own [Q k] wherever
     the node is untouched, the observation where it was spent *)
  Lemma pipe_wpost_cursor P γ M ua Q Qe Rk n r :
    pipe_wpost P γ M ua Q Qe Rk n r -∗
    (∃ k : nat,
       ⌜(k <= n)%nat⌝ ∗
       ((⌜r = (mword_of_int (Z.of_nat k) : mword 64)
          \/ (k = 0%nat /\ r = (mword_of_int (-1) : mword 64))⌝ ∗
         ⌜k = n \/ ~ uva_rmapped P (uint (add_vec_int ua (Z.of_nat k)))⌝ ∗ Q k)
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜(k < n)%nat⌝ ∗ Rk ∗ Q k)
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜(k < n)%nat⌝ ∗
           ∃ s : pipe_st, ⌜ps_ro s = false⌝ ∗ Qe k s)))
    ∨ (app_taint ∗ pipe_wpay γ M ua Q Qe n).
  Proof using .
    iIntros "[H | H]"; [| iRight; iExact "H"].
    iDestruct "H" as (k) "(%Hk & [(%Hr & %Hs & Hch) | [(%Hr & %Hs & Hk & Hch) | Hobs]])";
      iLeft; iExists k; (iSplitR; [by iPureIntro |]).
    - iLeft. iDestruct (pipe_wchain_cursor with "Hch") as "$". by iPureIntro.
    - iRight. iLeft. iDestruct (pipe_wchain_cursor with "Hch") as "$". iFrame "Hk". by iPureIntro.
    - iRight. iRight. iExact "Hobs".
  Qed.

  (* A READ'S STOP, at piperead's own window: [acc] the bytes dequeued --
     which are EXACTLY the bytes delivered, [d] of them, because the C
     dequeues a byte only after its copy-out succeeded -- and the reason,
     one of five.  The request was met.  The ring ran dry, OBSERVED at node
     [acc] ([Qe acc s] at [pst_empty s]; when nothing at all was delivered
     the write end is shut too, [ps_wo s = false], since the wait loop only
     lets an empty ring through when it is) -- and the observation spends
     the node, as at a write.  The copy-out of byte [d] faulted
     ([copyout_wrote]'s reason at the ENTRY table, the table only grows):
     that byte stays in the ring, and the answer is the count delivered, or
     -1 when it is nothing.  The reader was killed while it waited ([Rk],
     nothing dequeued).  Or the file layer's own sign guard, at the empty
     count.  The four non-observing reasons are [pipe_rstop_noobs]; they
     leave node [acc] untouched. *)
  Definition pipe_rstop_noobs (P : uptd) (addr : mword 64) (Rk : iProp Σ)
      (n d : nat) (r : mword 64) : iProp Σ :=
    ((⌜d = n /\ r = (mword_of_int (Z.of_nat d) : mword 64)⌝)
     ∨ (⌜(d < n)%nat /\ ~ uva_wmapped P (uint (add_vec_int addr (Z.of_nat d)))
         /\ ((0 < d)%nat /\ r = (mword_of_int (Z.of_nat d) : mword 64)
             \/ d = 0%nat /\ r = (mword_of_int (-1) : mword 64))⌝)
     ∨ (⌜d = 0%nat /\ r = (mword_of_int (-1) : mword 64)⌝ ∗ Rk)
     ∨ (⌜d = 0%nat /\ n = 0%nat /\ r = (mword_of_int (-1) : mword 64)⌝))%I.

  Definition pipe_rstop (P : uptd) (addr : mword 64)
      (Qe : list (bv 8) -> pipe_st -> iProp Σ) (Rk : iProp Σ)
      (n : nat) (acc : list (bv 8)) (d : nat) (r : mword 64) : iProp Σ :=
    (⌜length acc = d⌝ ∗
     ((⌜(d < n)%nat /\ r = (mword_of_int (Z.of_nat d) : mword 64)⌝ ∗
       ∃ s : pipe_st, ⌜pst_empty s /\ (d = 0%nat -> ps_wo s = false)⌝ ∗ Qe acc s)
      ∨ pipe_rstop_noobs P addr Rk n d r))%I.

  (* A READ'S POST: the stop, the window [bs] holding the delivered bytes,
     and the chain at [acc] wherever the stop did not spend it. *)
  Definition pipe_rpost (P : uptd) (γ : gname) (addr : mword 64)
      (Q : list (bv 8) -> iProp Σ)
      (Qe : list (bv 8) -> pipe_st -> iProp Σ) (Rk : iProp Σ)
      (n d : nat) (bs : nat -> bv 8) (r : mword 64) : iProp Σ :=
    ((∃ acc : list (bv 8),
        ⌜(length acc <= n)%nat⌝ ∗
        ⌜forall j : nat, (j < d)%nat -> bs j = acc !!! j⌝ ∗
        ((⌜(d < n)%nat /\ length acc = d
           /\ r = (mword_of_int (Z.of_nat d) : mword 64)⌝ ∗
          ∃ s : pipe_st, ⌜pst_empty s /\ (d = 0%nat -> ps_wo s = false)⌝ ∗ Qe acc s)
         ∨ (⌜length acc = d⌝ ∗ pipe_rstop_noobs P addr Rk n d r ∗
            pipe_rchain γ Q Qe acc (n - length acc))))
     ∨ (app_taint ∗ pipe_rpay γ Q Qe n))%I.

  (* the sign guard's exit, from the payment alone *)
  Lemma pipe_rpost_neg P γ addr Q Qe Rk (bs : nat -> bv 8) r :
    r = (mword_of_int (-1) : mword 64) ->
    pipe_rpay γ Q Qe 0 -∗ pipe_rpost P γ addr Q Qe Rk 0 0 bs r.
  Proof using .
    intros ->. iIntros "[Hch | #Ht]".
    - iLeft. iExists []. iSplitR; [by iPureIntro |].
      iSplitR; [iPureIntro; intros j Hj; lia |].
      iRight. iSplitR; [by iPureIntro |].
      iSplitR; [rewrite /pipe_rstop_noobs; iRight; iRight; iRight; by iPureIntro |].
      iExact "Hch".
    - iRight. iSplitR; [iExact "Ht" |]. by iApply pipe_rpay_taint.
  Qed.

  (* the stop alone, whichever arm: [pipe_rstop] out of a fired post, with
     the chain where the stop left it *)
  Lemma pipe_rpost_stop P γ addr Q Qe Rk n d bs r :
    pipe_rpost P γ addr Q Qe Rk n d bs r -∗
    (∃ acc : list (bv 8),
       ⌜(length acc <= n)%nat⌝ ∗
       ⌜forall j : nat, (j < d)%nat -> bs j = acc !!! j⌝ ∗
       pipe_rstop P addr Qe Rk n acc d r)
    ∨ (app_taint ∗ pipe_rpay γ Q Qe n).
  Proof using .
    iIntros "[H | H]"; [| iRight; iExact "H"].
    iDestruct "H" as (acc) "(%H1 & %H2 & [(%H3 & Hobs) | (%H3 & Hno & _)])";
      iLeft; iExists acc; (iSplitR; [by iPureIntro |]); (iSplitR; [by iPureIntro |]);
      rewrite /pipe_rstop.
    - iSplitR; [iPureIntro; tauto |]. iLeft. iSplitR; [iPureIntro; tauto |]. iExact "Hobs".
    - iSplitR; [by iPureIntro |]. iRight. iExact "Hno".
  Qed.

  (* ...AND THE SAME AT THE IMAGE, which is what the fileread tier and the
     trap post speak ([FsAbsReadFire.read_post_ok]'s convention, word for
     word): the bytes are read back out of the resume image under the
     caller's OWN linearity of its buffer. *)
  Definition pipe_rpost_img (P : uptd) (γ : gname) (Q : list (bv 8) -> iProp Σ)
      (Qe : list (bv 8) -> pipe_st -> iProp Σ) (Rk : iProp Σ)
      (n : nat) (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    ((∃ (acc : list (bv 8)) (d : nat),
        ⌜(length acc <= n)%nat⌝ ∗
        ⌜(forall i : nat, (i < d)%nat ->
            uint (add_vec_int addr (Z.of_nat i)) = (uint addr + Z.of_nat i)%Z) ->
         forall j : nat, (j < d)%nat ->
           M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (acc !!! j)⌝ ∗
        ((⌜(d < n)%nat /\ length acc = d
           /\ r = (mword_of_int (Z.of_nat d) : mword 64)⌝ ∗
          ∃ s : pipe_st, ⌜pst_empty s /\ (d = 0%nat -> ps_wo s = false)⌝ ∗ Qe acc s)
         ∨ (⌜length acc = d⌝ ∗ pipe_rstop_noobs P addr Rk n d r ∗
            pipe_rchain γ Q Qe acc (n - length acc))))
     ∨ (app_taint ∗ pipe_rpay γ Q Qe n))%I.

  (* the one step between them: piperead's window IS the image's run *)
  Lemma pipe_rpost_img_of P γ addr Q Qe Rk n d bs r (M : gmap Z (bv 8)) :
    pipe_rpost P γ addr Q Qe Rk n d bs r -∗
    pipe_rpost_img P γ Q Qe Rk n r (umem_wr M addr d bs) addr.
  Proof using .
    iIntros "[H | H]"; [iLeft | iRight; iExact "H"].
    iDestruct "H" as (acc) "(%Hle & %Hbs & Hst)".
    iExists acc, d. iFrame "Hst". iPureIntro. split; [exact Hle |].
    intros Hlin j Hj. rewrite (umem_wr_lookup_in M addr d bs j Hj Hlin).
    rewrite (Hbs j Hj). reflexivity.
  Qed.

  (* the sign guard's exit at the image, from the payment alone *)
  Lemma pipe_rpost_img_neg P γ Q Qe Rk r (M' : gmap Z (bv 8)) (addr : mword 64) :
    r = (mword_of_int (-1) : mword 64) ->
    pipe_rpay γ Q Qe 0 -∗ pipe_rpost_img P γ Q Qe Rk 0 r M' addr.
  Proof using .
    intros ->. iIntros "[Hch | #Ht]".
    - iLeft. iExists [], 0%nat. iSplitR; [by iPureIntro |].
      iSplitR; [iPureIntro; intros _ j Hj; lia |].
      iRight. iSplitR; [by iPureIntro |].
      iSplitR; [rewrite /pipe_rstop_noobs; iRight; iRight; iRight; by iPureIntro |].
      iExact "Hch".
    - iRight. iSplitR; [iExact "Ht" |]. by iApply pipe_rpay_taint.
  Qed.

  (* what every arm leaves at the cursor: the caller's own [Q acc] wherever
     the node is untouched, the observation where it was spent *)
  Lemma pipe_rpost_img_cursor P γ Q Qe Rk n r M' addr :
    pipe_rpost_img P γ Q Qe Rk n r M' addr -∗
    (∃ (acc : list (bv 8)) (d : nat),
       ⌜(length acc <= n)%nat⌝ ∗
       ⌜(forall i : nat, (i < d)%nat ->
           uint (add_vec_int addr (Z.of_nat i)) = (uint addr + Z.of_nat i)%Z) ->
        forall j : nat, (j < d)%nat ->
          M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (acc !!! j)⌝ ∗
       ((⌜(d < n)%nat /\ length acc = d
          /\ r = (mword_of_int (Z.of_nat d) : mword 64)⌝ ∗
         ∃ s : pipe_st, ⌜pst_empty s /\ (d = 0%nat -> ps_wo s = false)⌝ ∗ Qe acc s)
        ∨ (⌜length acc = d⌝ ∗ pipe_rstop_noobs P addr Rk n d r ∗ Q acc)))
    ∨ (app_taint ∗ pipe_rpay γ Q Qe n).
  Proof using .
    iIntros "[H | H]"; [| iRight; iExact "H"].
    iDestruct "H" as (acc d) "(%H1 & %H2 & [Hobs | (%H3 & Hno & Hch)])"; iLeft; iExists acc, d;
      (iSplitR; [by iPureIntro |]); (iSplitR; [by iPureIntro |]).
    - iLeft. iExact "Hobs".
    - iRight. iSplitR; [by iPureIntro |]. iFrame "Hno".
      iDestruct (pipe_rchain_cursor with "Hch") as "$".
  Qed.

End PipeQueue.

Global Typeclasses Opaque pipe_qauth pipe_qfrag pipe_olink pipe_wolink pipe_rolink pipe_wlink pipe_rlink pipe_clink.
