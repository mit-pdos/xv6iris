(* AppEcho.v -- THE ECHO APPLICATION: init spawns sh, the user types
   [echo hello world], sh forks and execs echo, echo prints the string back;
   the file system is never modified.

   Design of record: claude-notes/design/applications.md (§4 for this file's
   trace side, §5 for the lanes); worklist claude-notes/projects/app-echo.md.

   WHAT IS HERE.  The application's DATA and every obligation of
   [App.xv6_app_adequacy] that is provable without any of the lanes:

     the DISCIPLINE [disc]      -- every power cycle's input bytes so far
                                   are a prefix of [echo_line]^*;
                                   decidable, prefix-closed, and unmoved
                                   by output bytes and power events;
     the FIXED PART [echo_cl]   -- the taint counter's name, born once at
                                   0 by [echo_birth] (app-instances.md
                                   section 6 ruling 1, round D0: what used
                                   to be the machine's client counter is
                                   this application's own);
     the LEDGER [echo_R]        -- that counter at 0 while the input keeps
                                   the discipline and at 1 from the first
                                   byte that breaks it, so the counter at
                                   0 IS "untainted" and its lower bound at
                                   1 is the taint;
     its four steps             -- birth, the power arm, the tx arm, the
                                   rx arm ([echo_R_alloc] -- exactly the
                                   theorem's [HR0], out of [echo_cl] --
                                   [echo_R_pow], [echo_R_tx], [echo_R_rx]),
                                   each a basic update over the ledger
                                   alone: the theorem's wands frame the
                                   UART ghosts around them;
     the PREDICATE [echo_pred]  -- TAINTED OR PINNED: either the taint
                                   ([echo_taint], the ledger counter's
                                   lower bound at 1) or the binaries are
                                   the image's -- the era-0 pins of /init,
                                   /sh and /echo ([FsInitPinBoot.era0_pins],
                                   [FsShPin.era0_sh_pins],
                                   [FsEchoPin.era0_echo_pins]) read on the
                                   abstract state's VIEW ([FsAbsDefs.aview],
                                   app-instances.md round A).  The taint
                                   arm is what makes the claim SUPPLIABLE
                                   after the console discipline breaks
                                   (app-echo.md "ARM-c"): [echo_taint ⊢
                                   app_sup_raw (echo_pred γ) r], which no
                                   closed hypothesis proves;
     the BOOT obligation AT ERA 0 -- the founded map satisfies the pins
                                   when the disk is the mkfs image
                                   ([echo_fs_era0], [echo_init]), and at
                                   the theorem's own literal shape
                                   ([echo_init_img]);
     the RECORD [app_echo]      -- the [App.xv6_app] value, with every
                                   hypothesis of [App.xv6_app_adequacy] but
                                   [Hinit_boot] and [Hphi] discharged as a
                                   lemma at its fields.

   WHAT AN APPLICATION OWES, and what echo can pay.  The obligations of
   [App.xv6_app_adequacy] are [Hbirth], [Happ_xfer], [Happ_init],
   [Hinit_boot], the trace ledger's five and [Hphi] -- there is no parked
   license any more, and no SUPPLY either, and those two retirements are
   what make a CONSTRAINING application an instance at all: the blanket
   promise admitted every one-row move, which no pin survives, and the
   supply says the claim is trivially true, which [taint ∨ pins] is only
   after the taint is minted.

   THE TWO OPEN HYPOTHESES, and which lane closes each.  Every other
   hypothesis of [App.xv6_app_adequacy] is a lemma in section 6 below, at
   the theorem's own binder with [A := app_echo].  The two that are not:

     [Hinit_boot] -- LANE E2 (ARM-c (1b), INIT-BOOT).  Echo's own PINNED
       exec bundle at "/init": [PinnedExec.pinned_exec_bundle] over the
       era-0 pins, with [UInitKernel.init_slot_of_kexec] as the slot piece
       and the taint arm paid by [echo_sup_of_taint].  Mirrors [UInitSh],
       which is the same construction at /sh.
     [Hphi] -- LANE E5 (the output side).  [echo_phi] IS [True] HERE, and
       that is a placeholder, not a claim: at [True] the whole theorem
       would say SAFETY AND NOTHING ELSE.  E5 writes the real conclusion
       ([good_out]: every power cycle's output is a prefix of the console
       stream its input calls for), and [Hphi] at it reads the durable
       claim's taint arm against [echo_R_untainted].

   WHAT IS DELIBERATELY NOT HERE: a theorem.  [Hphi] at the placeholder
   would go through, but [Hinit_boot] is open, and a theorem taking it as
   a hypothesis would be durable-notes.md's GAP-premise trap -- so the
   application is a DEFINITION with its obligations as free-standing
   lemmas, and the two above are the worklist. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [cycles_of], [open_seg], [trace_shape] *)
(* the vocabulary of the era-0 pin theorems, imported by name: Import is
   not transitive *)
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsImgDisk.
Require Import SystemAdequacy.
Require Import FsImgCheck.
Require Import FsImg.            (* [fs_sb], [FsImg.sb_logstart] *)
Require Import FsState.
Require Import FsAbsDefs.        (* [aview], [abs_view] *)
Require Import FsInitPin.        (* [era0_D]: era 0's own durable map *)
Require Import FsInitPinBoot.    (* [era0_pins], [era0_recovery_pins],
                                    [era0_recovery] *)
Require Import FsShPin.          (* [era0_sh_pins], [era0_recovery_sh_pins] *)
Require Import FsEchoPin.        (* [era0_echo_pins], [era0_recovery_echo_pins] *)
Require Import FsTree.           (* [fname] *)
Require Import FsAbsDelta.       (* [cre_pre], [delta_create]: the mknod
                                    commit's own pre- and post-shapes *)
Require Import ConsoleInv.       (* [CONSOLE] *)
Require Import FsConsPin.        (* [cons_absent] / [cons_present_at], the
                                    era-0 console state and its transport,
                                    and section 5's delta algebra *)
Require Import FsCfgBoot.        (* [fs_boot_image_wf]: the theorem's [Himg] *)
Require Import FsDurImg.         (* [img_state], [img_snap_ok]: era 0's snapshot *)
Require Import AppInv.           (* [app_xfer_raw], [app_xfer_raw_pers_or_pure],
                                    [app_sup_raw]: the transport and the supply *)
(* the UART arms' own vocabulary: the theorem states [Htx]/[Hrx] with the
   device's ghosts framed around the ledger step, so the dischargers below
   need the names, not just the cone *)
Require Import DevModel.         (* [uart_state], [uart_tx_pop], [uart_loopback],
                                    [u_wire] *)
Require Import UartNames.        (* [uart_names] *)
Require Import RiscvPtsto.       (* [riscvGS], [obsN] *)
Require Import WpUart.           (* [uart_ghosts], [uartN] *)
Require Import App.              (* [xv6_app], [MkApp] and the theorem whose
                                    binders the dischargers are stated at *)
(* THE DISCIPLINE AND THE CLAIM, as pure combinatorics.  EXPORTED: the
   landed names ([echo_line], [star_prefix], [ins], [disc_seg], [disc]) are
   read unqualified by [UConsLine.v], and moving them out must not move
   them for a reader. *)
Require Export EchoDisc.
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE DISCIPLINE -- NOW IN [EchoDisc.v]                              *)
(*                                                                        *)
(*  The console discipline stopped being a predicate on the INPUT BYTES    *)
(*  ALONE (review-echo-plan-2026-09-12.md, finding 7: the theorem is FALSE *)
(*  at that discipline, because the 129th unconsumed byte is dropped       *)
(*  silently) and became the owner's RATE BOUND over the interleaved       *)
(*  trace -- D0 (wait for all seven harts) and D1/D2 (wait for the prompt, *)
(*  then for each byte's echo) beside the old content condition D3.  The   *)
(*  whole of it is pure combinatorics over [list mobs], so it lives in     *)
(*  [EchoDisc.v] -- EXPORTED here, because everything stated against the   *)
(*  landed names ([echo_line], [star_prefix], [disc_seg], [disc]) keeps    *)
(*  naming them unqualified.                                               *)
(*                                                                        *)
(*  What this file uses from there: [disc] (the new discipline) and its    *)
(*  [disc_nil] / [disc_out] / [disc_power] / [disc_in] closure laws, which *)
(*  hold at the SAME statements they held at before, so the ledger's four  *)
(*  steps below are unchanged; [disc_dec], which [echo_phase] decides;     *)
(*  [disc_old] and [disc_proj], the bridge every landed consumer of the    *)
(*  old predicate reads it through; and [disc_seg'] / [good_out], which    *)
(*  section 5's conclusion is written in.                                  *)
(* ====================================================================== *)
(* ====================================================================== *)
(*  2.  THE FIXED PART AND THE LEDGER: the taint counter reads the         *)
(*      discipline                                                         *)
(* ====================================================================== *)

(* THE FIXED PART'S TYPE (app-instances.md section 6 ruling 1): the taint
   counter's ghost name.  The machine's record carries one value of it for
   the whole run ([RiscvPtsto.riscv_client]), born by [echo_birth]. *)
Definition echo_fixed : Type := gname.

Section EchoLedger.
  Context `{!mono_natG Σ}.

  (* what the birth step yields: the counter, whole, at 0 *)
  Definition echo_cl (γ : echo_fixed) : iProp Σ :=
    mono_nat_auth_own γ 1 0%nat.

  (* THE BIRTH STEP: run first by the power theorem, before the crash slot,
     so both the crash predicate and the ledger can name the counter *)
  Lemma echo_birth : ⊢ |==> ∃ γ : echo_fixed, echo_cl γ.
  Proof.
    iMod (mono_nat_own_alloc 0%nat) as (γ) "[Ha _]".
    iModIntro. iExists γ. iExact "Ha".
  Qed.

  (* the counter's value at a history: 0 while disciplined, 1 after *)
  Definition echo_phase (h : list mobs) : nat :=
    if decide (disc h) then 0%nat else 1%nat.

  Definition echo_R (γcl : echo_fixed) (h : list mobs) : iProp Σ :=
    mono_nat_auth_own γcl 1 (echo_phase h).

  Global Instance echo_R_timeless γcl h : Timeless (echo_R γcl h).
  Proof. rewrite /echo_R. apply _. Qed.

  (* THE TAINT, ONCE.  The ledger's counter has left 0 and can never come
     back, so its lower bound at 1 is a PERMANENT, PERSISTENT fact: "the
     console input has broken the discipline at some point in this run".
     It is stated here and used in all three places that name it -- the
     input tag's right arm, the predicate's left arm, and the supply
     [echo_sup_of_taint] the generic user-execution slot is minted on --
     so the three cannot drift apart. *)
  Definition echo_taint (γcl : echo_fixed) : iProp Σ :=
    mono_nat_lb_own γcl 1.

  Global Instance echo_taint_persistent γcl : Persistent (echo_taint γcl).
  Proof. rewrite /echo_taint. apply _. Qed.
  Global Instance echo_taint_timeless γcl : Timeless (echo_taint γcl).
  Proof. rewrite /echo_taint. apply _. Qed.

  (* THE INPUT TAG (app-echo.md lane L5), this application's entry in the
     machine's ambient tag slot ([RiscvPtsto.riscv_rx_tag], set by
     [App.xv6_app_adequacy] from [App.app_tag]): of every byte the
     environment pushed, either the history up to and including it kept the
     console discipline, or the taint is already a permanent fact.
     Persistent in both arms, which is what lets the UART's receive column
     hand a copy to every reader of the byte. *)
  Definition echo_tag (γcl : echo_fixed) (h : list mobs) : iProp Σ :=
    (⌜disc h⌝ ∨ echo_taint γcl)%I.

  Global Instance echo_tag_persistent γcl h : Persistent (echo_tag γcl h).
  Proof. rewrite /echo_tag. apply _. Qed.
  Global Instance echo_tag_timeless γcl h : Timeless (echo_tag γcl h).
  Proof. rewrite /echo_tag. apply _. Qed.

  (* "untainted" is the counter at 0: what the end of the trace reads.  The
     taint is this application's own fact now (it was the machine's
     [client_lb 1] before round D0). *)
  Lemma echo_R_untainted γcl h :
    disc h -> echo_R γcl h -∗ echo_taint γcl -∗ False.
  Proof.
    intros Hd. iIntros "Ha Hlb".
    rewrite /echo_R /echo_taint /echo_phase decide_True; last exact Hd.
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle]. lia.
  Qed.

  (* birth: the counter arrives at 0 out of the birth step's yield, and the
     empty history is disciplined -- exactly [App.xv6_app_adequacy]'s [HR0] *)
  Lemma echo_R_alloc γcl :
    echo_cl γcl ⊢ |==> echo_R γcl [].
  Proof.
    iIntros "H". rewrite /echo_cl /echo_R /echo_phase decide_True; last exact disc_nil.
    by iModIntro.
  Qed.

  (* a power event moves nothing *)
  Lemma echo_R_pow (γcl : gname) (h : list mobs) (on : bool) :
    echo_R γcl h ==∗ echo_R γcl (h ++ [if on then ObsPowerOff else ObsPowerOn]).
  Proof.
    iIntros "H". rewrite /echo_R /echo_phase.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_power h on)). by iModIntro.
  Qed.

  (* an output byte moves nothing *)
  Lemma echo_R_tx γcl h b :
    trace_shape h true ->
    echo_R γcl h ==∗ echo_R γcl (h ++ [ObsUartOut b]).
  Proof.
    intros Hsh. iIntros "H". rewrite /echo_R /echo_phase.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_out h b Hsh)). by iModIntro.
  Qed.

  (* an input byte: still disciplined (0 stays), the first bad byte (0 -> 1),
     or already tainted (1 stays) -- monotone in every case.  It also mints
     THE BYTE'S TAG: the left arm when the history is still disciplined, the
     counter's lower bound otherwise, which is exactly [echo_tag]. *)
  Lemma echo_R_rx γcl h b :
    trace_shape h true ->
    echo_R γcl h ==∗
      echo_R γcl (h ++ [ObsUartIn b]) ∗ echo_tag γcl (h ++ [ObsUartIn b]).
  Proof.
    intros Hsh. iIntros "H". rewrite /echo_R /echo_tag /echo_taint /echo_phase.
    destruct (decide (disc (h ++ [ObsUartIn b]))) as [Hd'|Hd'].
    - rewrite decide_True; last exact (disc_in h b Hsh Hd').
      iModIntro. iFrame "H". iLeft. iPureIntro. exact Hd'.
    - (* off the discipline: the counter is at 1 either way, and its lower
         bound is the taint *)
      (* the destruct above already reduced the RHS's [decide] to 1; the
         LHS's is 0 or 1 and both are below it *)
      iMod (mono_nat_own_update 1%nat with "H") as "[H #Hlb]";
        [destruct (decide (disc h)); lia|].
      iModIntro. iFrame "H". iRight. iExact "Hlb".
  Qed.
End EchoLedger.


(* ====================================================================== *)
(*  3.  THE PREDICATE: TAINTED, OR THE BINARIES ARE THE IMAGE'S            *)
(* ====================================================================== *)

(* /init, /sh and /echo are the image's, path and content, on the abstract
   state's VIEW.  Per-inum rather than "the map is the image's" on purpose:
   the durable snapshot pins a state per inum and no whole-map equality
   exists (fs-syscall-specs.md lane D, gap (3)).  This half of the claim is
   PURE -- it owns nothing -- so it is a [Prop] and the predicate embeds
   it. *)
Definition echo_fs_pure (av : aview) : Prop :=
  era0_pins av /\ era0_sh_pins av /\ era0_echo_pins av.

(* THE APPLICATION'S INSTANCE NAMES: the console one-shot's ghost name,
   one per instance of the claim (the running one, and one per durable
   copy the transport mints).  Echo's claim owned no per-instance ghost
   while it was three pins about the IMAGE; the console is the first thing
   it says that /init's own write establishes, and a monotone flag is what
   carries "established" across the views a later syscall observes. *)
(* TWO GHOSTS, and one will not do.  The FLAG [cons_made] has to refute
   the claim's ABSENT arm (that is what /init's SECOND open runs on: the
   console it just made is still there), and the KEY [cons_key] has to
   refute the claim's two PRESENT arms (that is what /init's FIRST open
   runs on: at era 0 there is no console, so the walk misses and the call
   returns [-1]).  No single ghost does both: the claim's authority cannot
   be in two places at once, and a PERSISTENT witness of "not yet shot"
   cannot exist -- it would survive the shot.  So the instance names are a
   PAIR, [(flag, key)], and the transport allocates both. *)
Definition echo_names : Type := gname * gname.

Section EchoPred.
  (* the console flag's camera: a [mono_list] over inums, at [] before the
     console is made and at [[i]] after -- so the AUTHORITY is the
     exclusive "not yet / made at [i]" token and the LOWER BOUND is the
     persistent "made at [i]".  ([mono_nat] cannot carry the inum, and the
     inum is the whole point: it is what ties the walk's terminal cursor
     at one view to the observation's row at another.) *)
  Context `{!mono_natG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  (* ---------------------------------------------------------------- *)
  (*  3a.  THE CONSOLE FLAG                                             *)
  (* ---------------------------------------------------------------- *)

  (* THE TOKEN: exclusive, born with the instance, spent by the mknod that
     creates the console. *)
  Definition cons_tok (r : echo_names) : iProp Σ :=
    own r.1 (●ML ([] : list (leibnizO Z))).

  (* ...and what it becomes: the authority at the inum the mknod chose *)
  Definition cons_shot (r : echo_names) (i : Z) : iProp Σ :=
    own r.1 (●ML ([i] : list (leibnizO Z))).

  (* THE FLAG, PERSISTENT: "the console was made, at inum [i]".  This is
     the fact /init carries from its mknod to its open, and it is the ONE
     thing that makes the claim's console conjunct a PIN at a fixed inum
     rather than an existential a walk cannot follow. *)
  Definition cons_made (r : echo_names) (i : Z) : iProp Σ :=
    own r.1 (◯ML ([i] : list (leibnizO Z))).

  (* THE KEY: "the console has not been made yet", as an EXCLUSIVE resource
     rather than as a fact.  /init is handed it at the era mint, spends it
     into the mknod's phase-1 step -- which is the instant the view becomes
     present -- and gets it back as that piece's refund on every path where
     the commit did not fire.  While it holds the key, the claim's two
     PRESENT arms are refuted at EVERY view, which is what makes "the
     console is absent" a fact /init can carry into a walk cursor
     ([UInitCons] section 5).

     IT IS THE SAME CAMERA as the flag, at the second name: [●ML []] is
     exclusive, which is the only property asked of it -- so no binder
     anywhere gains a camera. *)
  Definition cons_key (r : echo_names) : iProp Σ :=
    own r.2 (●ML ([] : list (leibnizO Z))).

  Global Instance cons_key_timeless r : Timeless (cons_key r).
  Proof. rewrite /cons_key. apply _. Qed.

  Lemma cons_key_excl (r : echo_names) : cons_key r -∗ cons_key r -∗ False.
  Proof.
    rewrite /cons_key. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    iPureIntro. apply mono_list_auth_dfrac_op_valid_L in Hv.
    destruct Hv as [Hd _]. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hd).
  Qed.

  Global Instance cons_made_persistent r i : Persistent (cons_made r i).
  Proof. rewrite /cons_made. apply _. Qed.
  Global Instance cons_made_timeless r i : Timeless (cons_made r i).
  Proof. rewrite /cons_made. apply _. Qed.
  Global Instance cons_tok_timeless r : Timeless (cons_tok r).
  Proof. rewrite /cons_tok. apply _. Qed.
  Global Instance cons_shot_timeless r i : Timeless (cons_shot r i).
  Proof. rewrite /cons_shot. apply _. Qed.

  (* THE EXCLUSION, which is what a holder of the flag refutes the
     unmade states with: a lower bound at [[i]] and an authority at [[]]
     do not compose ([[i]] is not a prefix of [[]]). *)
  Lemma cons_tok_made_False (r : echo_names) (i : Z) :
    cons_tok r -∗ cons_made r i -∗ False.
  Proof.
    rewrite /cons_tok /cons_made. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. destruct Hv as [k Hk]. by destruct k; simplify_eq/=.
  Qed.

  (* THE AGREEMENT: the flag names ONE inum *)
  Lemma cons_shot_made_agree (r : echo_names) (i j : Z) :
    cons_shot r i -∗ cons_made r j -∗ ⌜j = i⌝.
  Proof.
    rewrite /cons_shot /cons_made. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. destruct Hv as [k Hk]. by simplify_eq/=.
  Qed.

  Lemma cons_made_agree (r : echo_names) (i j : Z) :
    cons_made r i -∗ cons_made r j -∗ ⌜j = i⌝.
  Proof.
    rewrite /cons_made. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    iPureIntro. destruct Hv as [[k Hk] | [k Hk]]; by simplify_eq/=.
  Qed.

  (* THE SNAPSHOT: the authority yields its own lower bound and stays *)
  Lemma cons_shot_made (r : echo_names) (i : Z) :
    cons_shot r i -∗ cons_shot r i ∗ cons_made r i.
  Proof.
    rewrite /cons_shot /cons_made. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML ([i] : list (leibnizO Z)))
                 with "Ha") as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  (* THE ONE UPDATE, and it happens inside /init's mknod commit *)
  Lemma cons_shoot (r : echo_names) (i : Z) :
    cons_tok r ==∗ cons_shot r i ∗ cons_made r i.
  Proof.
    rewrite /cons_tok /cons_shot. iIntros "Ha".
    iMod (own_update _ _ (●ML ([i] : list (leibnizO Z))) with "Ha") as "Ha".
    { apply mono_list_update. apply prefix_nil. }
    iModIntro. iApply (cons_shot_made r i with "Ha").
  Qed.

  (* THE INSTANCE IS BORN with the flag unraised and the key in hand: both
     names are fresh, and the key is what the era mint hands /init. *)
  Lemma cons_tok_alloc : ⊢ |==> ∃ r : echo_names, cons_tok r ∗ cons_key r.
  Proof.
    iMod (own_alloc (●ML ([] : list (leibnizO Z)))) as (g1) "H1";
      [ apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO Z)))) as (g2) "H2";
      [ apply mono_list_auth_valid |].
    iModIntro. iExists (g1, g2). rewrite /cons_tok /cons_key /=. iFrame "H1 H2".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3b.  THE CONSOLE'S STATE, AS THE CLAIM CARRIES IT                 *)
  (* ---------------------------------------------------------------- *)

  (* THREE ARMS, and the middle one is a WINDOW rather than a state the
     system rests in: the console is not there and nobody has made it; it
     is there and the flag has not been raised yet (the instant between
     the mknod commit's two phases); it is there and the flag names its
     inum.

     WHAT IS NOT HERE, deliberately: an "it was made and is gone again"
     arm.  The claim promises the console STAYS, exactly as it promises
     /sh's row stays -- an unlink of either is a view move no verified
     program of this application pays for, and the generic slot's payer
     ([AppInv.app_sup]) is tainted by construction. *)
  Definition cons_state (r : echo_names) (av : aview) : iProp Σ :=
    ((⌜cons_absent av⌝ ∗ cons_tok r)
     ∨ (∃ i : Z, ⌜cons_present_at i av⌝ ∗ cons_key r ∗ cons_tok r)
     ∨ (∃ i : Z, ⌜cons_present_at i av⌝ ∗ cons_key r ∗ cons_shot r i))%I.

  Global Instance cons_state_timeless r av : Timeless (cons_state r av).
  Proof. rewrite /cons_state. apply _. Qed.

  (* THE APPLICATION'S PREDICATE ([App.app_pred], app-instances.md section
     1 and app-echo.md "ARM-c"): TAINTED, or the three binaries are the
     image's AND the console is in one of its three states.  The left arm
     is the permanent fact that the console input has broken the
     discipline.

     IT IS NO LONGER PERSISTENT, and that is the ghost shape's one cost:
     the console conjunct owns the flag's authority, which is exclusive by
     construction (it is what makes "made" a fact a holder can rely on).
     It is still TIMELESS, which is what every fire strips it under, and
     the transport pays by ALLOCATING a fresh flag for the copy
     ([echo_xfer] below) rather than by duplicating. *)
  Definition echo_pred (γ : echo_fixed) (r : echo_names) (av : aview)
      : iProp Σ :=
    (echo_taint γ ∨ (⌜echo_fs_pure av⌝ ∗ cons_state r av))%I.

  Global Instance echo_pred_timeless γ r av : Timeless (echo_pred γ r av).
  Proof. rewrite /echo_pred. apply _. Qed.

  (* the era-0 shape: the pins, the console absent, the flag unraised *)
  Lemma echo_pred_absent (γ : echo_fixed) (r : echo_names) (av : aview) :
    echo_fs_pure av -> cons_absent av -> cons_tok r -∗ echo_pred γ r av.
  Proof.
    intros Hp Hc. iIntros "Ht". rewrite /echo_pred. iRight.
    iSplitR; [ by iPureIntro |]. rewrite /cons_state. iLeft.
    iSplitR; [ by iPureIntro | iExact "Ht" ].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3c.  THE CLAIM LAW THE PINNED OPEN RUNS ON                        *)
  (*                                                                    *)
  (*  [PinnedObs.pinned_obs] takes exactly this: a DUPLICATING law that  *)
  (*  hands the claim back and yields a PURE pin of the view it was      *)
  (*  read at, or the taint.  A holder of the flag at [i] refutes both   *)
  (*  unmade arms -- each carries the authority at [[]] -- and reads the *)
  (*  third at its own inum by the flag's agreement.  This is why the    *)
  (*  flag is what /init carries from its mknod to its open.            *)
  (* ---------------------------------------------------------------- *)
  Lemma echo_cons_law (γ : echo_fixed) (r : echo_names) (i : Z) :
    cons_made r i -∗
    □ (∀ v : aview, echo_pred γ r v -∗
         echo_pred γ r v ∗ (⌜cons_present_at i v⌝ ∨ echo_taint γ)).
  Proof.
    iIntros "#Hm !>" (v) "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iSplitR; [ iLeft; iExact "Ht" |]. iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | Hc]]".
    - iDestruct (cons_tok_made_False r i with "Htok Hm") as %[].
    - iDestruct "Hc" as (j) "(%Hpr & Hkey & Htok)".
      iDestruct (cons_tok_made_False r i with "Htok Hm") as %[].
    - iDestruct "Hc" as (j) "(%Hpr & Hkey & Hsh)".
      iDestruct (cons_shot_made_agree r j i with "Hsh Hm") as %Heq.
      subst i.
      iSplitL "Hsh Hkey".
      + iRight. iSplitR; [ by iPureIntro |]. rewrite /cons_state.
        iRight. iRight. iExists j. iFrame "Hkey Hsh". by iPureIntro.
      + iLeft. by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3c'.  THE CLAIM LAW THE *FIRST* OPEN RUNS ON                      *)
  (*                                                                    *)
  (*  The mirror of [echo_cons_law], and the reason the key exists: a    *)
  (*  holder of the KEY refutes both PRESENT arms -- each carries one --  *)
  (*  so at every view the claim holds of, the console is ABSENT.  That   *)
  (*  is [PinnedObs.pin_misses_at]'s input, and it is what makes /init's  *)
  (*  first [open("console")] provably return [-1] instead of leaving an  *)
  (*  arm nobody can refute.                                             *)
  (*                                                                    *)
  (*  LINEAR, not [□]-over-nothing: the key is exclusive.  It goes in and *)
  (*  comes back, so one key answers the walk's hop, the mknod's step and *)
  (*  -- if the mknod failed -- the second open in turn.                  *)
  (* ---------------------------------------------------------------- *)
  Lemma echo_cons_abs_law (γ : echo_fixed) (r : echo_names) :
    ⊢ □ (∀ v : aview, cons_key r -∗ echo_pred γ r v -∗
           echo_pred γ r v ∗ cons_key r ∗ (⌜cons_absent v⌝ ∨ echo_taint γ)).
  Proof.
    iIntros "!>" (v) "Hkey Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iSplitR; [ iLeft; iExact "Ht" |]. iFrame "Hkey". iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | Hc]]".
    - iSplitL "Htok".
      + iRight. iSplitR; [ by iPureIntro |]. iLeft.
        iSplitR; [ by iPureIntro | iExact "Htok" ].
      + iFrame "Hkey". iLeft. by iPureIntro.
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
  Qed.

  (* ...and the step the mknod's PHASE 1 takes with it: the key turns the
     claim's three arms into ONE (the absent one), so the console's state
     moves ABSENT -> PRESENT at the inum the create chose and the key goes
     INTO the claim beside the flag's authority.  This is the whole of what
     [AppInv.app_step] owes at /init's own write. *)
  Lemma echo_cons_mknod (γ : echo_fixed) (r : echo_names) (av : aview)
      (ents : gmap fname Z) (nl : nat) (i : Z) :
    cre_pre av FsImg.ROOTINO fname_console ents nl i (ADev CONSOLE 0) ->
    cons_key r -∗ echo_pred γ r av -∗
      echo_pred γ r (delta_create FsImg.ROOTINO fname_console i
                       (ADev CONSOLE 0) av).
  Proof.
    intros Hpre. iIntros "Hkey Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]"; [ by iLeft |].
    iRight. iSplitR.
    { iPureIntro. destruct Hpins as (H1 & H2 & H3). split_and!.
      - apply file_pin_init.
        exact (file_pin_create fname_init INIT_INO init_bytes FsImg.ROOTINO
                 fname_console ents nl i CONSOLE 0 av Hpre
                 (proj2 (file_pin_init av) H1)).
      - apply file_pin_sh.
        exact (file_pin_create fname_sh SH_INO sh_bytes FsImg.ROOTINO
                 fname_console ents nl i CONSOLE 0 av Hpre
                 (proj2 (file_pin_sh av) H2)).
      - apply file_pin_echo.
        exact (file_pin_create fname_echo ECHO_INO echo_bytes FsImg.ROOTINO
                 fname_console ents nl i CONSOLE 0 av Hpre
                 (proj2 (file_pin_echo av) H3)). }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | Hc]]".
    - iRight. iLeft. iExists i. iFrame "Hkey Htok". iPureIntro.
      exact (cons_state_mknod ents nl i av Hpre).
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
  Qed.

  (* ...AND THE SHOOT, which is the mknod commit's PHASE 2: the view is
     already present at [i], so the claim's only arms are the two present
     ones; the flag's authority moves [[] -> [i]] and the persistent
     [cons_made r i] comes out.  (An arm that is ALREADY shot agrees at
     [i], because [apath_at] is functional.) *)
  Lemma echo_cons_shoot (γ : echo_fixed) (r : echo_names) (av : aview)
      (i : Z) :
    cons_present_at i av ->
    echo_pred γ r av ==∗ echo_pred γ r av ∗ (cons_made r i ∨ echo_taint γ).
  Proof.
    intros Hpr. iIntros "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iModIntro. iSplitR; [ by iLeft |]. iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab _] | [Hc | Hc]]".
    { (* absent and present at once: the entry both is and is not there *)
      exfalso. rewrite /cons_absent (cons_present_astep i av Hpr) in Hab.
      discriminate Hab. }
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Htok)".
      iMod (cons_shoot r i with "Htok") as "[Hsh #Hm]".
      iModIntro. iSplitR "Hm".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight.
        iExists i. iFrame "Hkey Hsh". by iPureIntro.
      + iLeft. iExact "Hm".
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Hsh)".
      assert (Hij : j = i).
      { destruct Hprj as (Hpj & _ & _). destruct Hpr as (Hpi & _ & _).
        rewrite Hpj in Hpi. by injection Hpi. }
      subst j.
      iDestruct (cons_shot_made r i with "Hsh") as "[Hsh #Hm]".
      iModIntro. iSplitR "Hm".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight.
        iExists i. iFrame "Hkey Hsh". by iPureIntro.
      + iLeft. iExact "Hm".
  Qed.

  (* THE PURE HALF OF THE CLAIM, read off without spending it: the three
     binaries are the image's, or the taint.  The mknod's ARM leg stashes
     this at its own view and hands it on in the permit, which is what the
     UNARM leg needs to know the pins survive deleting a FRESH inum. *)
  Lemma echo_fs_pure_acc (γ : echo_fixed) (r : echo_names) (v : aview) :
    echo_pred γ r v -∗ echo_pred γ r v ∗ (⌜echo_fs_pure v⌝ ∨ echo_taint γ).
  Proof.
    iIntros "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iSplitR; [ by iLeft |]. iRight. iExact "Ht". }
    iSplitL "Hcs"; [ iRight; by iFrame "Hcs" | iLeft; by iPureIntro ].
  Qed.

  (* THE ARM LEG'S STEP: a DEVICE row appears at an inum the view does not
     have.  Free -- the commit's own freshness is all of it. *)
  Lemma echo_cons_arm (γ : echo_fixed) (r : echo_names) (av : aview)
      (i ma mi : Z) :
    av !! i = None ->
    echo_pred γ r av -∗ echo_pred γ r (delta_arm i (ADev ma mi) av).
  Proof.
    intros Hfree. iIntros "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]"; [ by iLeft |].
    iRight. iSplitR.
    { iPureIntro. destruct Hpins as (H1 & H2 & H3). split_and!.
      - apply file_pin_init.
        exact (file_pin_arm fname_init INIT_INO init_bytes i ma mi av Hfree
                 (proj2 (file_pin_init av) H1)).
      - apply file_pin_sh.
        exact (file_pin_arm fname_sh SH_INO sh_bytes i ma mi av Hfree
                 (proj2 (file_pin_sh av) H2)).
      - apply file_pin_echo.
        exact (file_pin_arm fname_echo ECHO_INO echo_bytes i ma mi av Hfree
                 (proj2 (file_pin_echo av) H3)). }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | Hc]]".
    - iLeft. iFrame "Htok". iPureIntro. exact (cons_absent_arm i ma mi av Hab).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Htok)".
      iRight. iLeft. iExists j. iFrame "Hkey Htok". iPureIntro.
      exact (cons_present_arm j i ma mi av Hfree Hprj).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Hsh)".
      iRight. iRight. iExists j. iFrame "Hkey Hsh". iPureIntro.
      exact (cons_present_arm j i ma mi av Hfree Hprj).
  Qed.

  (* THE UNARM LEG'S STEP, and it is PURE: the row at a FRESH inum goes
     away again.  The pins survive because the arm's own view did not have
     the inum ([FsConsPin.file_pin_unarm_fresh] -- the permit carries that
     view's pure claim), and the console survives because at the unarm's
     view it is ABSENT, which is what the KEY established one level up
     ([echo_cons_abs_law]); at an absent view [FsConsPin.cons_absent_unarm]
     has no side condition at all. *)
  Lemma echo_cons_unarm (γ : echo_fixed) (r : echo_names) (av0 av : aview)
      (i : Z) :
    av0 !! i = None ->
    echo_fs_pure av0 ->
    cons_absent av ->
    echo_pred γ r av -∗ echo_pred γ r (delta_unarm i av).
  Proof.
    intros Hfree Hp0 Hab0. iIntros "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]"; [ by iLeft |].
    iRight. iSplitR.
    { iPureIntro. destruct Hpins as (H1 & H2 & H3).
      destruct Hp0 as (G1 & G2 & G3). split_and!.
      - apply file_pin_init.
        exact (file_pin_unarm_fresh fname_init INIT_INO init_bytes i av0 av
                 Hfree (proj2 (file_pin_init av0) G1)
                 (proj2 (file_pin_init av) H1)).
      - apply file_pin_sh.
        exact (file_pin_unarm_fresh fname_sh SH_INO sh_bytes i av0 av
                 Hfree (proj2 (file_pin_sh av0) G2)
                 (proj2 (file_pin_sh av) H2)).
      - apply file_pin_echo.
        exact (file_pin_unarm_fresh fname_echo ECHO_INO echo_bytes i av0 av
                 Hfree (proj2 (file_pin_echo av0) G3)
                 (proj2 (file_pin_echo av) H3)). }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | Hc]]".
    - iLeft. iFrame "Htok". iPureIntro. exact (cons_absent_unarm i av Hab).
    - iDestruct "Hc" as (j) "(%Hprj & _ & _)".
      exfalso. rewrite /cons_absent (cons_present_astep j av Hprj) in Hab0.
      discriminate Hab0.
    - iDestruct "Hc" as (j) "(%Hprj & _ & _)".
      exfalso. rewrite /cons_absent (cons_present_astep j av Hprj) in Hab0.
      discriminate Hab0.
  Qed.

  (* ...and the create that is NOT the console's: the claim survives with
     no key spent, which is what the mknod's phase-1 step takes at any
     other [(d, nm)] the call could have reached. *)
  Lemma echo_cons_create_other (γ : echo_fixed) (r : echo_names) (av : aview)
      (d : Z) (nmn : fname) (ents : gmap fname Z) (nl : nat) (i : Z)
      (ma mi : Z) :
    cre_pre av d nmn ents nl i (ADev ma mi) ->
    (d <> FsImg.ROOTINO \/ nmn <> fname_console) ->
    echo_pred γ r av -∗
      echo_pred γ r (delta_create d nmn i (ADev ma mi) av).
  Proof.
    intros Hpre Hother. iIntros "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]"; [ by iLeft |].
    iRight. iSplitR.
    { iPureIntro. destruct Hpins as (H1 & H2 & H3). split_and!.
      - apply file_pin_init.
        exact (file_pin_create fname_init INIT_INO init_bytes d nmn ents nl i
                 ma mi av Hpre (proj2 (file_pin_init av) H1)).
      - apply file_pin_sh.
        exact (file_pin_create fname_sh SH_INO sh_bytes d nmn ents nl i
                 ma mi av Hpre (proj2 (file_pin_sh av) H2)).
      - apply file_pin_echo.
        exact (file_pin_create fname_echo ECHO_INO echo_bytes d nmn ents nl i
                 ma mi av Hpre (proj2 (file_pin_echo av) H3)). }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | Hc]]".
    - iLeft. iFrame "Htok". iPureIntro.
      exact (cons_absent_create_other d nmn ents nl i ma mi av Hpre Hother Hab).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Htok)".
      iRight. iLeft. iExists j. iFrame "Hkey Htok". iPureIntro.
      exact (cons_present_create_other j d nmn ents nl i ma mi av Hpre Hprj).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Hsh)".
      iRight. iRight. iExists j. iFrame "Hkey Hsh". iPureIntro.
      exact (cons_present_create_other j d nmn ents nl i ma mi av Hpre Hprj).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3a.  THE TRANSPORT ([Happ_xfer])                                  *)
  (* ---------------------------------------------------------------- *)

  (* app-instances.md round C, section 1: a copy of the claim at fresh
     instance names without spending the original.  Both arms of
     [echo_pred] are persistent, so the general law does it. *)
  Lemma echo_xfer (γ : echo_fixed) : ⊢ app_xfer_raw (echo_pred γ).
  Proof.
    rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    (* THE FRESH FLAG IS ALLOCATED AT THE VIEW'S OWN VALUE
       ([FsConsPin.cons_inum]) and not at the arm's: the allocation is an
       update and the claim is under a later, so the value has to be chosen
       BEFORE the arm is read.  The view decides it -- that is what
       [cons_inum_absent] / [cons_inum_present] say -- so each arm then
       finds the flag it needs. *)
    iMod (own_alloc (●ML (cons_inum av : list (leibnizO Z)))) as (g1) "Ha";
      [ apply mono_list_auth_valid |].
    (* ...AND A FRESH KEY BESIDE IT.  The copy's present arms need one, and
       it is fresh, so nothing holds it and nothing is spent.  (The absent
       arm needs none, which is why the allocation is unconditional and the
       arms below simply drop it.) *)
    iMod (own_alloc (●ML ([] : list (leibnizO Z)))) as (g2) "Hk";
      [ apply mono_list_auth_valid |].
    set (r' := (g1, g2) : echo_names).
    (* both halves are [▷]-shaped, so the rest of the proof runs under ONE
       later, with the original claim stripped by it *)
    iAssert (▷ (echo_pred γ r av ∗ echo_pred γ r' av))%I with "[H Ha Hk]" as "HH";
      last first.
    { iDestruct "HH" as "[H1 H2]". iModIntro. iFrame "H1". iExists r'.
      iExact "H2". }
    iNext. rewrite /echo_pred.
    iDestruct "H" as "[#Ht | [%Hpins Hcs]]".
    { iSplitR; [ by iLeft | by iLeft ]. }
    rewrite /cons_state /cons_tok /cons_shot /cons_key /r' /=.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | Hc]]".
    - rewrite (cons_inum_absent av Hab).
      iSplitL "Htok".
      + iRight. iSplitR; [ by iPureIntro |]. iLeft.
        iSplitR; [ by iPureIntro | iExact "Htok" ].
      + iRight. iSplitR; [ by iPureIntro |]. iLeft.
        iSplitR; [ by iPureIntro | iExact "Ha" ].
    - iDestruct "Hc" as (i) "(%Hpr & Hkey & Htok)".
      rewrite (cons_inum_present i av Hpr).
      iSplitL "Htok Hkey".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iLeft.
        iExists i. iFrame "Hkey Htok". by iPureIntro.
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight.
        iExists i. iFrame "Hk Ha". by iPureIntro.
    - iDestruct "Hc" as (i) "(%Hpr & Hkey & Hsh)".
      rewrite (cons_inum_present i av Hpr).
      iSplitL "Hsh Hkey".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight.
        iExists i. iFrame "Hkey Hsh". by iPureIntro.
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight.
        iExists i. iFrame "Hk Ha". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3b.  THE SUPPLY, OFF THE TAINT (app-echo.md "ARM-c")              *)
  (* ---------------------------------------------------------------- *)

  (* [AppInv.app_sup_raw] says the claim holds of EVERY view -- the
     credential a generic user-execution slot is minted on.  No closed
     hypothesis of this application proves it (that is exactly why the
     supply obligation left the theorem), but the TAINT does: under
     it the left disjunct is available at every view.  This is what a
     tainted process spends at the pinned exec gate's taint arm and at
     sh's continuation. *)
  Lemma echo_sup_of_taint (γ : echo_fixed) (r : echo_names) :
    echo_taint γ -∗ app_sup_raw (echo_pred γ) r.
  Proof.
    iIntros "#Ht". rewrite /app_sup_raw. iIntros "!>" (av).
    rewrite /echo_pred. iLeft. iExact "Ht".
  Qed.

  (* ...AND THE CONVERSE, which is what makes the credential a tokenless
     console read leaves ([ConsoleInv.cons_dirty_cred app_sup]) READ AS THE
     TAINT (app-echo.md, lane SH-LINE, S4).  The claim is about EVERY view,
     and the empty view is a view: it satisfies none of the three pins, so
     the only disjunct that can hold at it is the taint.  That is the step
     sh's read takes when its window comes back under the dirty
     disjunction -- somebody consumed console input behind its back, and
     what it is handed instead of the window is exactly this credential. *)
  Lemma echo_taint_of_sup (γ : echo_fixed) (r : echo_names) :
    app_sup_raw (echo_pred γ) r -∗ echo_taint γ.
  Proof.
    rewrite /app_sup_raw. iIntros "#Hs".
    iSpecialize ("Hs" $! (∅ : aview)).
    rewrite /echo_pred.
    iDestruct "Hs" as "[Ht | [%Hp _]]"; [ iExact "Ht" | ].
    exfalso. destruct Hp as (_ & (_ & Hc & _) & _).
    (* [lookup_empty] is a FIELD of stdpp's [FinMap] class, so the [∅] in
       its statement is that class's projection and does not match the
       [gmap] instance SYNTACTICALLY -- [rewrite] fails on it where
       [apply], which unifies up to conversion, goes through. *)
    by apply lookup_empty_Some in Hc.
  Qed.
End EchoPred.

(* ====================================================================== *)
(*  4.  THE ERA-0 CLAIM                                                    *)
(* ====================================================================== *)

(* THE PINS AT THE MAP A BOOT FOUNDS ITS FILE SYSTEM AT, when the disk is
   mkfs's image -- the three pin files' transport theorems, read together.
   About the [Prop]; the predicate's right disjunct embeds it. *)
Lemma echo_fs_era0 (dk : Z -> bv 8) (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  echo_fs_pure (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec HS. split.
  - exact (era0_recovery_pins dk D S Hdk Hrec HS).
  - split.
    + exact (era0_recovery_sh_pins dk D S Hdk Hrec HS).
    + exact (era0_recovery_echo_pins dk D S Hdk Hrec HS).
Qed.

Section EchoInit.
  Context `{!mono_natG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  (* ...as the era-0 obligation's shape: the claim at the founded state's
     view, at the one instance, under the update.  It takes the RIGHT
     disjunct -- there is no taint at boot, and none is needed. *)
  (* THE ERA-0 CLAIM *AND THE KEY*, which is the form the boot arm wants:
     the instance is born with the flag unraised, the console absent, and
     the key IN HAND -- and the key is what /init carries to its first open
     and its mknod ([UInitCons] sections 5-6).  [echo_init] below is this
     with the key dropped, which is the shape [App.xv6_app_adequacy]'s
     [Happ_init] binder is stated at; E2's boot arm takes THIS one and
     routes the key into /init's own bundle. *)
  Lemma echo_init_key (γ : echo_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    ⊢ |==> ∃ r : echo_names,
        echo_pred γ r (abs_view (fss_inodes S)) ∗ cons_key r.
  Proof.
    intros Hdk Hrec HS.
    (* the instance IS the console flag and its key, so the era-0 claim is
       where both are born -- unraised, beside the three pins and the
       absent console *)
    iMod cons_tok_alloc as (r) "[Htok Hkey]".
    iModIntro. iExists r. iFrame "Hkey".
    iApply (echo_pred_absent γ r _ (echo_fs_era0 dk D S Hdk Hrec HS)
              (era0_recovery_cons_absent dk D S Hdk Hrec HS) with "Htok").
  Qed.

  Lemma echo_init (γ : echo_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    ⊢ |==> ∃ r : echo_names, echo_pred γ r (abs_view (fss_inodes S)).
  Proof.
    intros Hdk Hrec HS.
    iMod (echo_init_key γ dk D S Hdk Hrec HS) as (r) "[Hp _]".
    iModIntro. iExists r. iExact "Hp".
  Qed.

  (* ...AND AT THE THEOREM'S OWN LITERAL SHAPE ([App.xv6_app_adequacy]'s
     [Happ_init]): the state the boot's snapshot IS, [FsDurImg.img_state]
     of the machine's disk.  THE COMPOSITION, in three steps and no more:

       [FsDurImg.img_snap_ok] turns the theorem's own [Himg]
         ([FsCfgBoot.fs_boot_image_wf], nothing new) into [snap_ok] of
         that state at [fs_restrict] of the image's home blocks;
       the era-0 disk equation identifies that map with
         [FsInitPin.era0_D] and [FsInitPinBoot.era0_recovery] produces the
         [fs_recovery] the pin transports take;
       [echo_init] above reads the three pins off it.

     ([SystemAdequacy.fsimg_snap_ok] is the same composition's non-vacuity
     witness at the literal image -- [img_snap_ok] at [fsimg_image_wf] --
     which is what says the premises below are satisfiable at all.)  The
     generic application's [app_triv_init] sidesteps every step of this:
     its claim holds of an arbitrary view, so it never has to know which
     state the boot founded at. *)
  Lemma echo_init_img (γ : echo_fixed) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    fs_blocks dk = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    ⊢ |==> ∃ r : echo_names,
        echo_pred γ r (abs_view (fss_inodes
          (FsDurImg.img_state (fs_blocks dk) sb nib))).
  Proof.
    intros Himg Hdk -> ->.
    pose proof (img_snap_ok dk ndisk fsimg_sb nib fsimg_cov Himg) as HS.
    (* the era-0 disk equation, applied to BOTH the snapshot's state and
       the map it is a snapshot of: the map is then [FsInitPin.era0_D] by
       its own definition and [echo_init] takes it with no bridge *)
    rewrite Hdk in HS. rewrite Hdk.
    exact (echo_init γ dk era0_D _ Hdk (era0_recovery dk Hdk) HS).
  Qed.
End EchoInit.

(* ====================================================================== *)
(*  5.  THE CONCLUSION                                                     *)
(* ====================================================================== *)

(* THE CONCLUSION, at last: every power cycle whose input kept the console
   discipline emitted, on the wire, an interleaving of the kernel's ten
   boot messages with a PREFIX of the session transcript that cycle's input
   calls for ([EchoDisc.good_out]).  It was [True] until 2026-09-12, and at
   [True] the whole theorem said SAFETY AND NOTHING ELSE.

   [App.app_phi] takes the operational state as well; echo's conclusion
   reads only the trace, so the state argument is dropped -- the durable
   half of the claim is [echo_pred] in the crash slot, not here.

   THE OBLIGATION IS OPEN.  [Hphi] -- the hypothesis of
   [App.xv6_app_adequacy] that this must be proved at -- IS NOT PROVED BY
   THIS FILE AND NOT BY THE LANE THAT WROTE THIS DEFINITION.  It needs the
   kernel's per-byte source tagging (lane TX-TAG), the located write
   receipts (TX-RECEIPT / ECHO-RECEIPT) and the ledger's shadow of the
   accepted list (APP-IFACE); the proof is E5's, and it reads the ledger
   against [echo_R_untainted] on the crash slot's taint arm.  There is
   deliberately NO lemma here that looks like it discharges [Hphi]. *)
Definition echo_phi : gstate -> list mobs -> Prop :=
  fun _ h => Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of h).

(* what the conclusion says once the discipline held: the claim, per cycle,
   with no hypothesis left in front of it *)
Lemma echo_phi_disc (g : gstate) (h : list mobs) :
  disc h -> echo_phi g h -> Forall good_out (cycles_of h).
Proof.
  rewrite /disc /echo_phi. intros Hd Hphi.
  apply Forall_lookup. intros i seg Hi.
  eapply Forall_lookup_1 in Hphi; [|exact Hi].
  apply Hphi. by eapply Forall_lookup_1 in Hd; [|exact Hi].
Qed.

(* ====================================================================== *)
(*  6.  THE RECORD, AND THE OBLIGATIONS DISCHARGED AT ITS FIELDS           *)
(*                                                                        *)
(*  Every hypothesis of [App.xv6_app_adequacy] except [Hinit_boot] and     *)
(*  [Hphi] is a lemma below, stated at the theorem's own binder with       *)
(*  [A := app_echo] -- so an instance of the theorem is those lemmas, the  *)
(*  two open ones, and nothing else to restate.  THERE IS NO THEOREM HERE: *)
(*  [Hinit_boot] is open, and a theorem taking it as a hypothesis would be *)
(*  durable-notes.md's GAP-premise trap.                                   *)
(* ====================================================================== *)

Section EchoApp.
  Context `{!mono_natG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  Definition app_echo : xv6_app Σ :=
    MkApp echo_fixed echo_cl echo_names echo_pred echo_R echo_tag echo_phi.

  (* ---- THE BIRTH STEP ---- *)
  Lemma echo_Hbirth : ⊢ |==> ∃ c : app_fixed app_echo, app_cl app_echo c.
  Proof. cbn [app_echo app_fixed app_cl]. exact echo_birth. Qed.

  (* ---- THE TRACE LEDGER'S FIVE ---- *)
  Lemma echo_HRt (c : app_fixed app_echo) (h : list mobs) :
    Timeless (app_R app_echo c h).
  Proof. cbn [app_echo app_fixed app_R] in c |- *. apply _. Qed.

  Lemma echo_Htagp (c : app_fixed app_echo) (h : list mobs) :
    Persistent (app_tag app_echo c h).
  Proof. cbn [app_echo app_fixed app_tag] in c |- *. apply _. Qed.

  Lemma echo_Htagt (c : app_fixed app_echo) (h : list mobs) :
    Timeless (app_tag app_echo c h).
  Proof. cbn [app_echo app_fixed app_tag] in c |- *. apply _. Qed.

  Lemma echo_HR0 (c : app_fixed app_echo) :
    app_cl app_echo c ⊢ |==> app_R app_echo c [].
  Proof. cbn [app_echo app_fixed app_cl app_R] in c |- *. exact (echo_R_alloc c). Qed.

  Lemma echo_Hpow (c : app_fixed app_echo) (h : list mobs) (on : bool)
      (dk : Z -> bv 8) :
    trace_shape h on ->
    ⊢ app_R app_echo c h ==∗
      app_R app_echo c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list.
  Proof.
    intros _. cbn [app_echo app_fixed app_R] in c |- *.
    iIntros "H". iApply (echo_R_pow c h on with "H").
  Qed.

  (* the two UART arms, at the theorem's literal shape: the device ghosts
     are FRAMED around the ledger step, which is [echo_R_tx]/[echo_R_rx].
     [uartGhostG] is what [uart_ghosts] reads; it is a MEMBER of [Xv6G.xv6G],
     which the theorem carries ambiently, so a binder here is what the
     theorem's own context supplies at the application site. *)
  Lemma echo_Htx `{!uartGhostG Σ}
      (HR : riscvGS Σ) (c : app_fixed app_echo) (γ : uart_names) :
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
           ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
           ⌜trace_shape h true⌝ -∗ ⌜obs_wire (open_seg h) = u_wire u⌝ -∗
           uart_ghosts γ u' -∗ app_R app_echo c h
             ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
           uart_ghosts γ u' ∗ app_R app_echo c (h ++ [ObsUartOut b])%list).
  Proof.
    cbn [app_echo app_fixed app_R] in c |- *.
    iIntros "!>" (h b u u') "_ _ %Hsh _ Hg Hled".
    iMod (echo_R_tx c h b Hsh with "Hled") as "Hled".
    iModIntro. iFrame "Hg Hled".
  Qed.

  Lemma echo_Hrx `{!uartGhostG Σ}
      (HR : riscvGS Σ) (c : app_fixed app_echo) (γ : uart_names) :
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
           ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
           uart_ghosts γ u' -∗ app_R app_echo c h
             ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
           uart_ghosts γ u' ∗ app_R app_echo c (h ++ [ObsUartIn b])%list ∗
           app_tag app_echo c (h ++ [ObsUartIn b])%list).
  Proof.
    cbn [app_echo app_fixed app_R app_tag] in c |- *.
    iIntros "!>" (h b u u') "_ %Hsh Hg Hled".
    iMod (echo_R_rx c h b Hsh with "Hled") as "[Hled Htag]".
    iModIntro. iFrame "Hg Hled Htag".
  Qed.

  (* ---- THE TRANSPORT ---- *)
  Lemma echo_Happ_xfer (c : app_fixed app_echo) :
    ⊢ app_xfer_raw (app_pred app_echo c).
  Proof.
    cbn [app_echo app_fixed app_names app_pred] in c |- *. exact (echo_xfer c).
  Qed.

  (* ---- THE ERA-0 CLAIM, at the theorem's binder.  [g], [sb], [nib] and
     [cov] are the theorem's own, and the three era-0 equations are what a
     closed corollary at the real image supplies from its own [Hdisk]
     ([App.xv6_app_adequacy_triv_xv6Σ]'s shape). ---- *)
  Lemma echo_Happ_init (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES sb nib cov ->
    fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P ->
    sb = fsimg_sb ->
    cov = fsimg_cov ->
    forall c : app_fixed app_echo,
      ⊢ |==> ∃ r : app_names app_echo,
          app_pred app_echo c r (abs_view (fss_inodes (FsDurImg.img_state
             (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))).
  Proof.
    intros Himg Hdk Hsb Hcov c.
    cbn [app_echo app_fixed app_names app_pred] in c |- *.
    exact (echo_init_img c _ XV6_DISK_BYTES sb nib cov Himg Hdk Hsb Hcov).
  Qed.
End EchoApp.
