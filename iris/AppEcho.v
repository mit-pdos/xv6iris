(* AppEcho.v -- THE ECHO APPLICATION: init spawns sh, the user types an
   [echo] line -- A DIFFERENT ONE EACH ROUND -- sh forks and execs echo,
   echo prints the arguments back; the file system is never modified.

   Design of record: claude-notes/design/applications.md (§4 for this file's
   trace side, §5 for the lanes); worklist claude-notes/projects/app-echo.md.

   WHAT IS HERE.  The application's DATA and every obligation of
   [App.xv6_app_adequacy] that is provable without any of the lanes:

     the DISCIPLINE [disc]      -- every power cycle's input bytes so far
                                   parse as admissible lines
                                   ([EchoDisc.disc_input]); decidable,
                                   prefix-closed, and unmoved by output
                                   bytes and power events;
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

   THE ONE OPEN HYPOTHESIS, and which lane closes it.  Every other
   hypothesis of [App.xv6_app_adequacy] is a lemma in section 6 below, at
   the theorem's own binder with [A := app_echo].  The one that is not
   ([Hphi]'s entry is kept for the record: it was open until lane ECHO-OUT
   part 5):

     [Hinit_boot] -- LANE E2 (ARM-c (1b), INIT-BOOT).  Echo's own PINNED
       exec bundle at "/init": [PinnedExec.pinned_exec_bundle] over the
       era-0 pins, with [UInitKernel.init_slot_of_kexec] as the slot piece
       and the taint arm paid by [echo_sup_of_taint].  Mirrors [UInitSh],
       which is the same construction at /sh.
     [Hphi] -- CLOSED (lane ECHO-OUT part 5).  [echo_phi] is the real
       conclusion -- if the input kept the discipline for the whole run,
       every power cycle's output is a prefix of the console stream its
       input calls for ([EchoDisc.good_out]) -- and the obligation is read
       off the LEDGER by [echo_R_phi]/[echo_Hphi_R] here and discharged at
       [UInitBootAdequacy], which is where the adequacy literal lives.

   WHAT IS DELIBERATELY NOT HERE: a theorem.  [Hphi] at the placeholder
   would go through, but [Hinit_boot] is open, and a theorem taking it as
   a hypothesis would be durable-notes.md's GAP-premise trap -- so the
   application is a DEFINITION with its obligations as free-standing
   lemmas, and the two above are the worklist. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [cycles_of], [open_seg], [trace_shape] *)
(* the vocabulary of the era-0 pin theorems, imported by name: Import is
   not transitive *)
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsImgDisk.
Require Import SystemAdequacy.
Require Import FsBootParams.  (* [XV6_DISK_BYTES], [fsimg_cov]              *)
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
Require Export EchoFsPure.       (* [echo_fs_pure] -- this
                                    application's pure claim, split out
                                    for [UInitSh].  EXPORT: existing
                                    importers unchanged.            *)
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
Require Import CtxIdDefs.           (* [CurCtx]: the echo obligation's context *)
Require Import SpecConsoleintr. (* [cons_echo_shift]: the echo obligation   *)
Require Import FileInvDefs.      (* [fileG]/[file_app]: the era's classes, which
                                    the tx/rx wands' identification premise
                                    names (lane APP-IFACE item (c)) *)
Require Import AppCfg.           (* [MkAppcfg]: ...and the record it equates *)
Require Import FsCfg.            (* [fsc_uart]: the era's own UART names *)
Require Import App.              (* [xv6_app], [MkApp] and the theorem whose
                                    binders the dischargers are stated at *)
(* THE APPLICATION CLAIM'S IRIS HALF (lane ECHO-OUT).  Every field this file
   used to fill with a placeholder -- the two port claims, the era's turn,
   the echo window token -- and the LEDGER itself are [EchoOut]'s now, at
   the taint this file defines; what stays here is the fixed part, the
   durable predicate and the record. *)
Require Import EchoOut.
(* THE DISCIPLINE AND THE CLAIM, as pure combinatorics.  EXPORTED: the
   landed names ([line_ok], [disc_input], [ins], [disc_seg], [disc]) are
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
(*  trace -- D1/D2 (wait for the prompt, then for each byte's echo) beside *)
(*  the old content condition D3, all read off the CONSOLE UART's wire,    *)
(*  which nothing but the session writes (the kernel's own messages go to  *)
(*  the other port and are not the theorem's concern).  The               *)
(*  whole of it is pure combinatorics over [list mobs], so it lives in     *)
(*  [EchoDisc.v] -- EXPORTED here, because everything stated against the   *)
(*  landed names ([line_ok], [disc_input], [disc_seg], [disc]) keeps       *)
(*  naming them unqualified.                                               *)
(*                                                                        *)
(*  What this file uses from there: [disc] (the new discipline) and its    *)
(*  [disc_nil] / [disc_out] / [disc_power] / [disc_in] closure laws, which *)
(*  hold at the SAME statements they held at before, so the ledger's four  *)
(*  steps below are unchanged; [disc_dec], which [echo_phase] decides;     *)
(*  and [disc_seg'] / [good_out], which                                    *)
(*  section 5's conclusion is written in.                                  *)
(* ====================================================================== *)
(* ====================================================================== *)
(*  2.  THE FIXED PART AND THE LEDGER: the taint counter reads the         *)
(*      discipline                                                         *)
(* ====================================================================== *)

(* THE FIXED PART'S TYPE (app-instances.md section 6 ruling 1): the TAINT
   COUNTER's ghost name and the ERA MAP's ([EchoOut.echo_gn]).  It was the
   counter's name alone until lane ECHO-OUT part 5; the era map is what the
   ledger's power-on step mints an era's pin in, and it has to be born with
   the counter because the machine's record carries ONE value of the fixed
   part for the whole run ([RiscvPtsto.riscv_client]), born by
   [echo_birth]. *)
Definition echo_fixed : Type := EchoOut.echo_gn.

Section EchoLedger.
  (* ONE class, and it REPLACES the bare [mono_natG] this section used to
     take (lane ECHO-OUT part 5).  [EchoOut.echoOutG] CARRIES [mono_natG]
     ([eo_mono_nat]), so a second binder beside it would be the
     duplicate-class trap ([Xv6Cameras]'s note): the taint below has to be
     the SAME [mono_nat_lb_own] the ledger's counter conjunct is stated at,
     or [EchoOut.echo_led_phi]'s premise is unsuppliable. *)
  Context `{!echoOutG Σ}.

  (* THE TAINT, ONCE.  The ledger's counter has left 0 and can never come
     back, so its lower bound at 1 is a PERMANENT, PERSISTENT fact: "the
     console input has broken the discipline at some point in this run".
     It is stated here and used in all the places that name it -- the input
     tag's right arm, the predicate's left arm, the supply
     [echo_sup_of_taint] the generic user-execution slot is minted on, and
     -- since lane ECHO-OUT -- the TAINT ARM of every claim [EchoOut]
     states, which this file passes in as that file's [T]. *)
  Definition echo_taint (γcl : echo_fixed) : iProp Σ :=
    mono_nat_lb_own (eg_taint γcl) 1.

  Global Instance echo_taint_persistent γcl : Persistent (echo_taint γcl).
  Proof using . rewrite /echo_taint. apply _. Qed.
  Global Instance echo_taint_timeless γcl : Timeless (echo_taint γcl).
  Proof using . rewrite /echo_taint. apply _. Qed.

  (* what the birth step yields: the counter, whole, at 0, AND the era map
     empty -- [EchoOut.echo_led_init]'s two arguments, which is what makes
     the ledger's first state derivable from the birth alone. *)
  Definition echo_cl (γcl : echo_fixed) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γcl) 1 0%nat
     ∗ ghost_map_auth (eg_pin γcl) 1 (∅ : gmap nat era_pins))%I.

  (* THE BIRTH STEP: run first by the power theorem, before the crash slot,
     so both the crash predicate and the ledger can name the counter *)
  Lemma echo_birth : ⊢ |==> ∃ γ : echo_fixed, echo_cl γ.
  Proof using .
    iMod (mono_nat_own_alloc 0%nat) as (γt) "[Ha _]".
    iMod (ghost_map_alloc (∅ : gmap nat era_pins)) as (γp) "[Hm _]".
    iModIntro. iExists (MkEchoGn γt γp). rewrite /echo_cl /=. iFrame "Ha Hm".
  Qed.

  (* THE LEDGER is [EchoOut.echo_led] at this file's taint (lane ECHO-OUT
     part 5).  It was the taint counter alone; it keeps that counter, and
     adds the ERA MAP's authority -- spent at the power-on step and nowhere
     else -- and the PHI conjunct the conclusion is read off. *)
  Definition echo_R (γcl : echo_fixed) (h : list mobs) : iProp Σ :=
    EchoOut.echo_led (echo_taint γcl) γcl h.

  Global Instance echo_R_timeless γcl h : Timeless (echo_R γcl h).
  Proof using . rewrite /echo_R. apply _. Qed.

  (* THE INPUT TAG (app-echo.md lane L5), this application's entry in the
     machine's ambient tag slot ([RiscvPtsto.riscv_rx_tag], set by
     [App.xv6_app_adequacy] from [App.app_tag]): of every byte the
     environment pushed, the history's SHAPE (lane ECHO-OUT part 3, B), and
     either the history up to and including it kept the console discipline
     or the taint is already a permanent fact.  Persistent in both arms,
     which is what lets the UART's receive column hand a copy to every
     reader of the byte.
     IT IS [EchoOut.etag] AT THE TAINT, which is the form
     [App.Happ_echo]'s tag equation is discharged at. *)
  Definition echo_tag (γcl : echo_fixed) (h : list mobs) : iProp Σ :=
    EchoOut.etag (echo_taint γcl) h.

  Global Instance echo_tag_persistent γcl h : Persistent (echo_tag γcl h).
  Proof using . rewrite /echo_tag. apply _. Qed.
  Global Instance echo_tag_timeless γcl h : Timeless (echo_tag γcl h).
  Proof using . rewrite /echo_tag. apply _. Qed.

  (* "untainted" is the counter at 0: what the end of the trace reads.  The
     taint is this application's own fact now (it was the machine's
     [client_lb 1] before round D0). *)
  Lemma echo_R_untainted γcl h :
    disc h -> echo_R γcl h -∗ echo_taint γcl -∗ False.
  Proof using .
    intros Hd. iIntros "H Hlb".
    rewrite /echo_R /EchoOut.echo_led /echo_taint decide_True; last exact Hd.
    iDestruct "H" as "(Ha & _ & _)".
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle]. lia.
  Qed.

  (* THE CONCLUSION, READ OFF THE LEDGER (lane ECHO-OUT part 5, [Hphi]'s
     one ingredient): [EchoOut.echo_led_phi] with the taint supplied by
     DEFINITION -- [echo_taint] IS the lower bound that lemma asks for, so
     its premise is the identity. *)
  Lemma echo_R_phi (γcl : echo_fixed) (h : list mobs) :
    echo_R γcl h ⊢ ⌜disc h -> Forall good_out (cycles_of h)⌝.
  Proof using .
    rewrite /echo_R. iIntros "H".
    iApply (EchoOut.echo_led_phi (echo_taint γcl) γcl h with "[] H").
    rewrite /echo_taint. iIntros "$".
  Qed.

  (* birth: the ledger arrives out of the birth step's yield -- exactly
     [App.xv6_app_adequacy]'s [HR0] *)
  Lemma echo_R_alloc γcl :
    echo_cl γcl ⊢ |==> echo_R γcl [].
  Proof using .
    rewrite /echo_cl /echo_R. iIntros "[Ht Hm]". iModIntro.
    iApply (EchoOut.echo_led_init (echo_taint γcl) γcl with "Ht Hm").
  Qed.

  (* an input byte: still disciplined (0 stays), the first bad byte (0 -> 1),
     or already tainted (1 stays) -- monotone in every case.  It also mints
     THE BYTE'S TAG: the left arm when the history is still disciplined, the
     counter's lower bound otherwise, which is exactly [echo_tag]. *)
  Lemma echo_R_rx γcl h i b :
    trace_shape h true ->
    echo_R γcl h ==∗
      echo_R γcl (h ++ [ObsUartIn i b]) ∗ echo_tag γcl (h ++ [ObsUartIn i b]).
  Proof using .
    intros Hsh. iIntros "H". rewrite /echo_R.
    iMod (EchoOut.echo_led_rx (echo_taint γcl) γcl h i b Hsh with "H")
      as "[H Htg]".
    iModIntro. iFrame "H". rewrite /echo_tag /EchoOut.etag.
    iSplitR; [| iExact "Htg"].
    iPureIntro. eapply trace_shape_snoc; [exact Hsh | reflexivity].
  Qed.
End EchoLedger.


(* ====================================================================== *)
(*  3.  THE PREDICATE: TAINTED, OR THE BINARIES ARE THE IMAGE'S            *)
(* ====================================================================== *)

(* [echo_fs_pure] MOVED DOWN to [EchoFsPure.v] (re-exported above):
   [UInitSh] names this [Prop] in [init_sh_slot_core]'s statement and
   wants nothing else of this application. *)

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
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.

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
  Proof using . rewrite /cons_key. apply _. Qed.

  (* ...AND WHAT THE KEY BECOMES WHEN /init's MKNOD FAILS: THE SEAL.
     app-echo.md, lane SH-OPEN's finding -- sh's own console preamble has
     to be able to prove ITS first [open] misses, and sh cannot hold the
     key (it is exclusive, and it would have to cross init's [box]-ed exec
     supply).  So on the repair arm's failure /init SPENDS the key into
     the claim: the key's own name is advanced from [[]] to [[0]], the
     AUTHORITY at [[0]] goes into a fourth, SEALED-ABSENT arm of
     [cons_state], and the LOWER BOUND at [[0]] -- persistent -- is handed
     out as [cons_never].

     WHY THE SEAL LIVES AT THE KEY'S NAME [r.2] AND NOT AT THE FLAG'S
     [r.1] AT A SENTINEL INUM: a sentinel in the flag would have to be
     refuted against the PRESENT arms, whose inum is existential and which
     nothing constrains to be non-negative, so "the sentinel is not an
     inum" is not provable.  At the key's name it is one exclusion and no
     arithmetic: every PRESENT arm holds [cons_key r = ●ML []] at [r.2],
     and a lower bound at [[0]] does not compose with it.

     ABSENCE IS STABLE UNDER THE SEAL because law (f) -- the only step
     that puts the console under `console` at the root -- DEMANDS the key,
     and after the seal nobody holds one.  A power cycle does not inherit
     the seal: the transport mints a FRESH key for the clone at every
     view whose [cons_inum] is [[]], so a sealed era does not seal the
     next. *)
  Definition cons_seal_tok (r : echo_names) : iProp Σ :=
    own r.2 (●ML ([0] : list (leibnizO Z))).

  (* THE CREDENTIAL: "the console will never be made at this instance",
     persistent, and it is what [UInitCons.init_cons_abs_law] is
     instantiated at once /init's mknod has failed. *)
  Definition cons_never (r : echo_names) : iProp Σ :=
    own r.2 (◯ML ([0] : list (leibnizO Z))).

  Global Instance cons_never_persistent r : Persistent (cons_never r).
  Proof using . rewrite /cons_never. apply _. Qed.
  Global Instance cons_never_timeless r : Timeless (cons_never r).
  Proof using . rewrite /cons_never. apply _. Qed.
  Global Instance cons_seal_tok_timeless r : Timeless (cons_seal_tok r).
  Proof using . rewrite /cons_seal_tok. apply _. Qed.

  (* the two exclusions the sealed arm is read by: an UNSEALED key refutes
     it, and so does a second seal *)
  Lemma cons_key_never_False (r : echo_names) :
    cons_key r -∗ cons_never r -∗ False.
  Proof using .
    rewrite /cons_key /cons_never. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. destruct Hv as [k Hk]. by destruct k; simplify_eq/=.
  Qed.

  Lemma cons_key_seal_False (r : echo_names) :
    cons_key r -∗ cons_seal_tok r -∗ False.
  Proof using .
    rewrite /cons_key /cons_seal_tok. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    iPureIntro. apply mono_list_auth_dfrac_op_valid_L in Hv.
    destruct Hv as [Hd _]. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hd).
  Qed.

  (* the seal's snapshot, and the update that takes it: [cons_shoot]'s
     twin at the key's name *)
  Lemma cons_seal_never (r : echo_names) :
    cons_seal_tok r -∗ cons_seal_tok r ∗ cons_never r.
  Proof using .
    rewrite /cons_seal_tok /cons_never. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML ([0] : list (leibnizO Z)))
                 with "Ha") as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  Lemma cons_seal (r : echo_names) :
    cons_key r ==∗ cons_seal_tok r ∗ cons_never r.
  Proof using .
    rewrite /cons_key /cons_seal_tok. iIntros "Ha".
    iMod (own_update _ _ (●ML ([0] : list (leibnizO Z))) with "Ha") as "Ha".
    { apply mono_list_update. apply prefix_nil. }
    iModIntro. iApply (cons_seal_never r with "Ha").
  Qed.

  Lemma cons_key_excl (r : echo_names) : cons_key r -∗ cons_key r -∗ False.
  Proof using .
    rewrite /cons_key. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    iPureIntro. apply mono_list_auth_dfrac_op_valid_L in Hv.
    destruct Hv as [Hd _]. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hd).
  Qed.

  Global Instance cons_made_persistent r i : Persistent (cons_made r i).
  Proof using . rewrite /cons_made. apply _. Qed.
  Global Instance cons_made_timeless r i : Timeless (cons_made r i).
  Proof using . rewrite /cons_made. apply _. Qed.
  Global Instance cons_tok_timeless r : Timeless (cons_tok r).
  Proof using . rewrite /cons_tok. apply _. Qed.
  Global Instance cons_shot_timeless r i : Timeless (cons_shot r i).
  Proof using . rewrite /cons_shot. apply _. Qed.

  (* THE EXCLUSION, which is what a holder of the flag refutes the
     unmade states with: a lower bound at [[i]] and an authority at [[]]
     do not compose ([[i]] is not a prefix of [[]]). *)
  Lemma cons_tok_made_False (r : echo_names) (i : Z) :
    cons_tok r -∗ cons_made r i -∗ False.
  Proof using .
    rewrite /cons_tok /cons_made. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. destruct Hv as [k Hk]. by destruct k; simplify_eq/=.
  Qed.

  (* THE AGREEMENT: the flag names ONE inum *)
  Lemma cons_shot_made_agree (r : echo_names) (i j : Z) :
    cons_shot r i -∗ cons_made r j -∗ ⌜j = i⌝.
  Proof using .
    rewrite /cons_shot /cons_made. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. destruct Hv as [k Hk]. by simplify_eq/=.
  Qed.

  Lemma cons_made_agree (r : echo_names) (i j : Z) :
    cons_made r i -∗ cons_made r j -∗ ⌜j = i⌝.
  Proof using .
    rewrite /cons_made. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    iPureIntro. destruct Hv as [[k Hk] | [k Hk]]; by simplify_eq/=.
  Qed.

  (* THE SNAPSHOT: the authority yields its own lower bound and stays *)
  Lemma cons_shot_made (r : echo_names) (i : Z) :
    cons_shot r i -∗ cons_shot r i ∗ cons_made r i.
  Proof using .
    rewrite /cons_shot /cons_made. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML ([i] : list (leibnizO Z)))
                 with "Ha") as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  (* THE ONE UPDATE, and it happens inside /init's mknod commit *)
  Lemma cons_shoot (r : echo_names) (i : Z) :
    cons_tok r ==∗ cons_shot r i ∗ cons_made r i.
  Proof using .
    rewrite /cons_tok /cons_shot. iIntros "Ha".
    iMod (own_update _ _ (●ML ([i] : list (leibnizO Z))) with "Ha") as "Ha".
    { apply mono_list_update. apply prefix_nil. }
    iModIntro. iApply (cons_shot_made r i with "Ha").
  Qed.

  (* THE INSTANCE IS BORN with the flag unraised and the key in hand: both
     names are fresh, and the key is what the era mint hands /init. *)
  Lemma cons_tok_alloc : ⊢ |==> ∃ r : echo_names, cons_tok r ∗ cons_key r.
  Proof using .
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
  (* ...AND A FOURTH, SEALED-ABSENT (lane SH-OPEN's finding): the console
     is not there, nobody made it, AND THE KEY HAS BEEN SPENT -- /init's
     repair mknod failed and it will not try again, so the state can no
     longer move to a PRESENT one.  The arm holds the SEALED key
     authority; the persistent [cons_never] a holder reads it by is what
     sh's own first open runs on. *)
  Definition cons_state (r : echo_names) (av : aview) : iProp Σ :=
    ((⌜cons_absent av⌝ ∗ cons_tok r)
     ∨ (∃ i : Z, ⌜cons_present_at i av⌝ ∗ cons_key r ∗ cons_tok r)
     ∨ (∃ i : Z, ⌜cons_present_at i av⌝ ∗ cons_key r ∗ cons_shot r i)
     ∨ (⌜cons_absent av⌝ ∗ cons_tok r ∗ cons_seal_tok r))%I.

  Global Instance cons_state_timeless r av : Timeless (cons_state r av).
  Proof using . rewrite /cons_state. apply _. Qed.

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
  Proof using . rewrite /echo_pred. apply _. Qed.

  (* the era-0 shape: the pins, the console absent, the flag unraised *)
  Lemma echo_pred_absent (γ : echo_fixed) (r : echo_names) (av : aview) :
    echo_fs_pure av -> cons_absent av -> cons_tok r -∗ echo_pred γ r av.
  Proof using .
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
  Proof using .
    iIntros "#Hm !>" (v) "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iSplitR; [ iLeft; iExact "Ht" |]. iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iDestruct (cons_tok_made_False r i with "Htok Hm") as %[].
    - iDestruct "Hc" as (j) "(%Hpr & Hkey & Htok)".
      iDestruct (cons_tok_made_False r i with "Htok Hm") as %[].
    - iDestruct "Hc" as (j) "(%Hpr & Hkey & Hsh)".
      iDestruct (cons_shot_made_agree r j i with "Hsh Hm") as %Heq.
      subst i.
      iSplitL "Hsh Hkey".
      + iRight. iSplitR; [ by iPureIntro |]. rewrite /cons_state.
        iRight. iRight. iLeft. iExists j. iFrame "Hkey Hsh". by iPureIntro.
      + iLeft. by iPureIntro.
    - (* SEALED-ABSENT: the token is still unspent, so the flag refutes it *)
      iDestruct (cons_tok_made_False r i with "Htok Hm") as %[].
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
  Proof using .
    iIntros "!>" (v) "Hkey Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iSplitR; [ iLeft; iExact "Ht" |]. iFrame "Hkey". iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iSplitL "Htok".
      + iRight. iSplitR; [ by iPureIntro |]. iLeft.
        iSplitR; [ by iPureIntro | iExact "Htok" ].
      + iFrame "Hkey". iLeft. by iPureIntro.
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - (* SEALED: the seal IS the key's name advanced, so an unsealed key
         beside it is two authorities at one name *)
      iDestruct (cons_key_seal_False r with "Hkey Hseal") as %[].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3c''. THE CLAIM LAW SH'S FIRST OPEN RUNS ON (lane SH-OPEN)        *)
  (*                                                                    *)
  (*  The SEAL's law, and the [□] shape of [echo_cons_abs_law]: the      *)
  (*  credential is persistent, so nothing goes in and comes back.  A    *)
  (*  holder knows the console is absent at EVERY view the claim holds   *)
  (*  of -- the two PRESENT arms each carry an UNSEALED key, which a     *)
  (*  lower bound at [[0]] refutes, and the two absent arms say it.      *)
  (*  [UInitCons.init_cons_abs_law T (cons_never r)] is this, one        *)
  (*  weakening away.                                                    *)
  (* ---------------------------------------------------------------- *)
  (* THE CREDENTIAL IS THE GHOST FRAGMENT ITSELF, never a derived
     [□]-wand, and the law is stated [□ (K -∗ □ …)] rather than
     [K -∗ □ …]: lane SH-OPEN's consumer ([UShConsK.sh_cons_never_law])
     takes it at an abstract [K] with [Persistent K] AND [Timeless K],
     because its walk strips a later off the credential inside
     [AppInv.app_inv].  [cons_never] is [◯ML [0]] at the key's own name,
     so both instances hold ([cons_never_persistent] /
     [cons_never_timeless] above) and the discharge is one [exact]. *)
  Lemma echo_cons_never_law (γ : echo_fixed) (r : echo_names) :
    ⊢ □ (cons_never r -∗
           □ (∀ v : aview, echo_pred γ r v -∗
                echo_pred γ r v ∗ (⌜cons_absent v⌝ ∨ echo_taint γ))).
  Proof using .
    iIntros "!> #Hn !>" (v) "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iSplitR; [ iLeft; iExact "Ht" |]. iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iSplitL "Htok".
      + iRight. iSplitR; [ by iPureIntro |]. iLeft.
        iSplitR; [ by iPureIntro | iExact "Htok" ].
      + iLeft. by iPureIntro.
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_never_False r with "Hk2 Hn") as %[].
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_never_False r with "Hk2 Hn") as %[].
    - iSplitL "Htok Hseal".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iRight.
        iFrame "Htok Hseal". by iPureIntro.
      + iLeft. by iPureIntro.
  Qed.

  (* ...AND THE STEP THAT MINTS IT, which is /init's repair arm when the
     mknod FAILED: the key it went in with is spent into the claim and
     what comes back is the persistent credential.  The view is absent --
     that is what the key already said -- so the arm the claim lands in is
     the sealed one.  THE TOKEN IS NOT SPENT: the console was never made. *)
  Lemma echo_cons_seal_step (γ : echo_fixed) (r : echo_names) (av : aview) :
    cons_key r -∗ echo_pred γ r av ==∗
      echo_pred γ r av ∗ (cons_never r ∨ echo_taint γ).
  Proof using .
    iIntros "Hkey Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iModIntro. iSplitR; [ by iLeft |]. iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iMod (cons_seal r with "Hkey") as "[Hseal #Hn]".
      iModIntro. iSplitR "Hn".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iRight.
        iFrame "Htok Hseal". by iPureIntro.
      + iLeft. iExact "Hn".
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - iDestruct (cons_key_seal_False r with "Hkey Hseal") as %[].
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
  Proof using .
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
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iRight. iLeft. iExists i. iFrame "Hkey Htok". iPureIntro.
      exact (cons_state_mknod ents nl i av Hpre).
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - iDestruct "Hc" as (j) "(_ & Hk2 & _)".
      iDestruct (cons_key_excl r with "Hkey Hk2") as %[].
    - (* THE SEAL IS WHY ABSENCE IS STABLE: this step is the only one that
         puts the console under `console` at the root, and it demands the
         key -- which a sealed claim has already taken. *)
      iDestruct (cons_key_seal_False r with "Hkey Hseal") as %[].
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
  Proof using .
    intros Hpr. iIntros "Hp". rewrite /echo_pred.
    iDestruct "Hp" as "[#Ht | [%Hpins Hcs]]".
    { iModIntro. iSplitR; [ by iLeft |]. iRight. iExact "Ht". }
    rewrite /cons_state.
    iDestruct "Hcs" as "[[%Hab _] | [Hc | [Hc | [%Hab4 _]]]]";
      [ | | | (* the sealed arm is absent too, and absent and present at
                 once is the same contradiction *)
        exfalso; rewrite /cons_absent (cons_present_astep i av Hpr) in Hab4;
        discriminate Hab4 ].
    { (* absent and present at once: the entry both is and is not there *)
      exfalso. rewrite /cons_absent (cons_present_astep i av Hpr) in Hab.
      discriminate Hab. }
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Htok)".
      iMod (cons_shoot r i with "Htok") as "[Hsh #Hm]".
      iModIntro. iSplitR "Hm".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
        iExists i. iFrame "Hkey Hsh". by iPureIntro.
      + iLeft. iExact "Hm".
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Hsh)".
      assert (Hij : j = i).
      { destruct Hprj as (Hpj & _ & _). destruct Hpr as (Hpi & _ & _).
        rewrite Hpj in Hpi. by injection Hpi. }
      subst j.
      iDestruct (cons_shot_made r i with "Hsh") as "[Hsh #Hm]".
      iModIntro. iSplitR "Hm".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
        iExists i. iFrame "Hkey Hsh". by iPureIntro.
      + iLeft. iExact "Hm".
  Qed.

  (* THE PURE HALF OF THE CLAIM, read off without spending it: the three
     binaries are the image's, or the taint.  The mknod's ARM leg stashes
     this at its own view and hands it on in the permit, which is what the
     UNARM leg needs to know the pins survive deleting a FRESH inum. *)
  Lemma echo_fs_pure_acc (γ : echo_fixed) (r : echo_names) (v : aview) :
    echo_pred γ r v -∗ echo_pred γ r v ∗ (⌜echo_fs_pure v⌝ ∨ echo_taint γ).
  Proof using .
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
  Proof using .
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
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iLeft. iFrame "Htok". iPureIntro. exact (cons_absent_arm i ma mi av Hab).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Htok)".
      iRight. iLeft. iExists j. iFrame "Hkey Htok". iPureIntro.
      exact (cons_present_arm j i ma mi av Hfree Hprj).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Hsh)".
      iRight. iRight. iLeft. iExists j. iFrame "Hkey Hsh". iPureIntro.
      exact (cons_present_arm j i ma mi av Hfree Hprj).
    - iRight. iRight. iRight. iFrame "Htok Hseal". iPureIntro.
      exact (cons_absent_arm i ma mi av Hab4).
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
  Proof using .
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
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iLeft. iFrame "Htok". iPureIntro. exact (cons_absent_unarm i av Hab).
    - iDestruct "Hc" as (j) "(%Hprj & _ & _)".
      exfalso. rewrite /cons_absent (cons_present_astep j av Hprj) in Hab0.
      discriminate Hab0.
    - iDestruct "Hc" as (j) "(%Hprj & _ & _)".
      exfalso. rewrite /cons_absent (cons_present_astep j av Hprj) in Hab0.
      discriminate Hab0.
    - iRight. iRight. iRight. iFrame "Htok Hseal". iPureIntro.
      exact (cons_absent_unarm i av Hab4).
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
  Proof using .
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
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iLeft. iFrame "Htok". iPureIntro.
      exact (cons_absent_create_other d nmn ents nl i ma mi av Hpre Hother Hab).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Htok)".
      iRight. iLeft. iExists j. iFrame "Hkey Htok". iPureIntro.
      exact (cons_present_create_other j d nmn ents nl i ma mi av Hpre Hprj).
    - iDestruct "Hc" as (j) "(%Hprj & Hkey & Hsh)".
      iRight. iRight. iLeft. iExists j. iFrame "Hkey Hsh". iPureIntro.
      exact (cons_present_create_other j d nmn ents nl i ma mi av Hpre Hprj).
    - iRight. iRight. iRight. iFrame "Htok Hseal". iPureIntro.
      exact (cons_absent_create_other d nmn ents nl i ma mi av Hpre Hother Hab4).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3d.  THE SAME TWO STEPS AT THE *FLAG* ARM (lane E2)               *)
  (*                                                                    *)
  (*  /init's console dance has to be proved at BOTH arms of             *)
  (*  [echo_boot], and at the FLAG arm there is no key: what /init holds  *)
  (*  is the persistent [cons_made r i], the node is already there, and   *)
  (*  its repair [mknod] -- reached when the FIRST open failed at         *)
  (*  [filealloc]/[fdalloc], which /init proves nothing about (app-echo   *)
  (*  .md, OPEN-PIN FINDINGS, FACT 3) -- cannot commit.  So the two steps *)
  (*  its bundle still owes are these: the UNARM leg at a PRESENT view,   *)
  (*  and the console's OWN create at a PRESENT view, which is VACUOUS    *)
  (*  ([cre_pre] wants the name free in the root and the pin says it is   *)
  (*  taken).  The other six laws are the landed ones verbatim: the arm   *)
  (*  leg, any other create, the pure half and the supply do not read the *)
  (*  console's state at all.                                            *)
  (* ---------------------------------------------------------------- *)

  (* THE UNARM LEG AT THE FLAG.  [echo_cons_unarm]'s twin: the permit
     carries the ARM's own view [av0], and what survives the removal of a
     row at a FRESH inum is the console at the flag's inum
     ([FsConsPin.cons_present_unarm_fresh]) rather than its absence. *)
  Lemma echo_cons_unarm_present (γ : echo_fixed) (r : echo_names)
      (av0 av : aview) (i j : Z) :
    av0 !! i = None ->
    echo_fs_pure av0 ->
    cons_present_at j av0 ->
    cons_made r j -∗ echo_pred γ r av -∗ echo_pred γ r (delta_unarm i av).
  Proof using .
    intros Hfree Hp0 Hpr0. iIntros "#Hm Hp". rewrite /echo_pred.
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
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
    - iDestruct (cons_tok_made_False r j with "Htok Hm") as %[].
    - iDestruct "Hc" as (k) "(_ & _ & Htok)".
      iDestruct (cons_tok_made_False r j with "Htok Hm") as %[].
    - iDestruct "Hc" as (k) "(%Hprk & Hkey & Hsh)".
      iDestruct (cons_shot_made_agree r k j with "Hsh Hm") as %Heq.
      subst k.
      iRight. iRight. iLeft. iExists j. iFrame "Hkey Hsh". iPureIntro.
      exact (cons_present_unarm_fresh j i av0 av Hfree Hpr0 Hprk).
    - iDestruct (cons_tok_made_False r j with "Htok Hm") as %[].
  Qed.

  (* THE CONSOLE'S OWN CREATE AT THE FLAG, and it is VACUOUS: the pin says
     `console` resolves in the root, [cre_pre] says the root's map does not
     have the name.  This is the law [UInitCons]'s mknod bundle takes at
     (f) when /init is running on the flag rather than the key, and it is
     why nothing has to be spent there. *)
  Lemma echo_cons_mknod_present (γ : echo_fixed) (r : echo_names)
      (av : aview) (ents : gmap fname Z) (nl : nat) (i j : Z) :
    cre_pre av FsImg.ROOTINO fname_console ents nl i (ADev CONSOLE 0) ->
    cons_made r j -∗ echo_pred γ r av -∗
      echo_pred γ r (delta_create FsImg.ROOTINO fname_console i
                       (ADev CONSOLE 0) av).
  Proof using .
    intros Hpre. iIntros "#Hm Hp".
    iDestruct (echo_cons_law γ r j with "Hm") as "#Hl".
    iDestruct ("Hl" $! av with "Hp") as "[Hp [%Hpr | #Ht]]"; last first.
    { rewrite /echo_pred. by iLeft. }
    exfalso.
    pose proof (cons_present_astep j av Hpr) as Hst.
    destruct Hpre as (Hd & Hfresh & _).
    rewrite /astep /aents Hd /= /anode_ents /= Hfresh in Hst.
    discriminate Hst.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3a.  THE TRANSPORT ([Happ_xfer])                                  *)
  (* ---------------------------------------------------------------- *)

  (* app-instances.md round C, section 1: a copy of the claim at fresh
     instance names without spending the original.  Both arms of
     [echo_pred] are persistent, so the general law does it. *)
  Lemma echo_xfer (γ : echo_fixed) : ⊢ app_xfer_raw (echo_pred γ).
  Proof using .
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
    rewrite /cons_state /cons_tok /cons_shot /cons_key /cons_seal_tok /r' /=.
    iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
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
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
        iExists i. iFrame "Hk Ha". by iPureIntro.
    - iDestruct "Hc" as (i) "(%Hpr & Hkey & Hsh)".
      rewrite (cons_inum_present i av Hpr).
      iSplitL "Hsh Hkey".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
        iExists i. iFrame "Hkey Hsh". by iPureIntro.
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
        iExists i. iFrame "Hk Ha". by iPureIntro.
    - (* SEALED-ABSENT: the original keeps its seal; the copy is born
         UNSEALED, at a fresh key it does not yet need -- a sealed era does
         not seal the next. *)
      rewrite (cons_inum_absent av Hab4).
      iSplitL "Htok Hseal".
      + iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iRight.
        iSplitR; [ by iPureIntro | iFrame "Htok Hseal" ].
      + iRight. iSplitR; [ by iPureIntro |]. iLeft.
        iSplitR; [ by iPureIntro | iExact "Ha" ].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3a'. THE FIRST PROCESS'S BOOT RESOURCE ([App.app_boot])           *)
  (* ---------------------------------------------------------------- *)

  (* WHAT /init IS HANDED AT THE ERA MINT, and it is a DISJUNCTION, not the
     bare key.  THE ARM IS DECIDED BY THE VIEW ([FsConsPin.cons_inum av]),
     NEVER BY THE ERA NUMBER: the KEY arm whenever the view has no console
     node (era 0's image, which carries none -- mkfs writes no device inode
     -- and equally any later era whose /init never committed its [mknod] or
     whose [mknod] failed), the FLAG arm whenever the view has one.  The key
     is what makes a missing node's [open] provably return [-1]; the flag is
     what makes a present node's [open] a pinned observation at its inum.
     The key cannot be BOTH: at a view with the node, the claim's PRESENT
     arms hold [cons_key r] themselves ([cons_state] below), so the
     transport has no second copy to hand out -- and /init does not want
     one there.  So /init's console dance has to be proved at BOTH arms,
     at every era. *)
  (* ...AT THE ERA'S NUMBER (lane CONS-IO milestone C), which this
     placeholder-era resource does not read: the console key is the same
     thing whatever era it is handed in. *)
  Definition echo_boot (γ : echo_fixed) (k : nat) (r : echo_names) : iProp Σ :=
    (cons_key r ∨ ∃ i : Z, cons_made r i)%I.

  (* THE TRANSPORT, WITH THE BOOT RESOURCE ([App.Happ_boot]).  The arm is
     decided OUTSIDE the later, by [FsConsPin.cons_inum av] -- a pure
     function of the view, which is exactly why the fresh flag is allocated
     at it -- so the resource handed over is not under the claim's [▷]. *)
  (* THE TWO-COMPONENT SHAPE IS [app_xfer_boot_raw]'s OWN AGAIN (lane
     CONS-IO milestone E): lanes OUT-FUPD and CONS-IO had bolted the era's
     two port claims onto the transport, and the founding moved to
     [App.Hpow]'s power-on arm, so there is nothing to bolt. *)
  Lemma echo_xfer_boot (γ : echo_fixed) (k : nat) :
    ⊢ □ (∀ (r : echo_names) (av : FsAbsDefs.aview),
           ▷ echo_pred γ r av ==∗ ▷ echo_pred γ r av ∗
           ∃ r' : echo_names, ▷ echo_pred γ r' av ∗ echo_boot γ k r').
  Proof using .
    iIntros "!>" (r av) "H".
    iMod (own_alloc (●ML (cons_inum av : list (leibnizO Z)))) as (g1) "Ha";
      [ apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO Z)))) as (g2) "Hk";
      [ apply mono_list_auth_valid |].
    set (r' := (g1, g2) : echo_names).
    destruct (cons_inum av) as [| i0 tl] eqn:Hci.
    - (* NO CONSOLE AT THIS VIEW: the fresh key is what /init gets, and the
         copy's only reachable arm ([cons_absent]) needs the flag alone. *)
      iAssert (▷ (echo_pred γ r av ∗ echo_pred γ r' av))%I
        with "[H Ha]" as "HH"; last first.
      { iDestruct "HH" as "[H1 H2]". iModIntro. iFrame "H1". iExists r'.
        iSplitL "H2"; [ iExact "H2" |].
        rewrite /echo_boot. iLeft. rewrite /cons_key /r' /=. iExact "Hk". }
      iNext. rewrite /echo_pred.
      iDestruct "H" as "[#Ht | [%Hpins Hcs]]".
      { iSplitR; [ by iLeft | by iLeft ]. }
      rewrite /cons_state /cons_tok /cons_shot /cons_key /cons_seal_tok /r' /=.
      iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 [Htok Hseal]]]]]".
      + iSplitL "Htok".
        * iRight. iSplitR; [ by iPureIntro |]. iLeft.
          iSplitR; [ by iPureIntro | iExact "Htok" ].
        * iRight. iSplitR; [ by iPureIntro |]. iLeft.
          iSplitR; [ by iPureIntro | iExact "Ha" ].
      + iDestruct "Hc" as (i) "(%Hpr & _ & _)".
        pose proof (cons_inum_present i av Hpr) as Hx. congruence.
      + iDestruct "Hc" as (i) "(%Hpr & _ & _)".
        pose proof (cons_inum_present i av Hpr) as Hx. congruence.
      + (* SEALED-ABSENT: the FRESH key is still what /init gets -- the
           seal is this instance's, not the next one's *)
        iSplitL "Htok Hseal".
        * iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iRight.
          iSplitR; [ by iPureIntro | iFrame "Htok Hseal" ].
        * iRight. iSplitR; [ by iPureIntro |]. iLeft.
          iSplitR; [ by iPureIntro | iExact "Ha" ].
    - (* THE CONSOLE IS THERE: /init gets the flag, off the fresh
         authority's own lower bound, and the fresh key goes into the
         copy's claim where the two PRESENT arms want it. *)
      iDestruct (own_mono _ _ (◯ML ([i0] : list (leibnizO Z))) with "Ha")
        as "#Hmade".
      { etrans; [| apply (mono_list_included (DfracOwn 1))].
        apply mono_list_lb_mono. by exists tl. }
      iAssert (▷ (echo_pred γ r av ∗ echo_pred γ r' av))%I
        with "[H Ha Hk]" as "HH"; last first.
      { iDestruct "HH" as "[H1 H2]". iModIntro. iFrame "H1". iExists r'.
        iSplitL "H2"; [ iExact "H2" |].
        rewrite /echo_boot. iRight. iExists i0.
        rewrite /cons_made /r' /=. iExact "Hmade". }
      iNext. rewrite /echo_pred.
      iDestruct "H" as "[#Ht | [%Hpins Hcs]]".
      { iSplitR; [ by iLeft | by iLeft ]. }
      rewrite /cons_state /cons_tok /cons_shot /cons_key /cons_seal_tok /r' /=.
      iDestruct "Hcs" as "[[%Hab Htok] | [Hc | [Hc | [%Hab4 _]]]]";
        [ | | | pose proof (cons_inum_absent av Hab4) as Hx; congruence ].
      + pose proof (cons_inum_absent av Hab) as Hx. congruence.
      + iDestruct "Hc" as (i) "(%Hpr & Hkey & Htok)".
        pose proof (cons_inum_present i av Hpr) as Hx.
        rewrite Hci in Hx. simplify_eq.
        iSplitL "Htok Hkey".
        * iRight. iSplitR; [ by iPureIntro |]. iRight. iLeft.
          iExists _. iFrame "Hkey Htok". by iPureIntro.
        * iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
          iExists _. iFrame "Hk Ha". by iPureIntro.
      + iDestruct "Hc" as (i) "(%Hpr & Hkey & Hsh)".
        pose proof (cons_inum_present i av Hpr) as Hx.
        rewrite Hci in Hx. simplify_eq.
        iSplitL "Hsh Hkey".
        * iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
          iExists _. iFrame "Hkey Hsh". by iPureIntro.
        * iRight. iSplitR; [ by iPureIntro |]. iRight. iRight. iLeft.
          iExists _. iFrame "Hk Ha". by iPureIntro.
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
  Proof using .
    iIntros "#Ht". rewrite /app_sup_raw. iIntros "!>" (av).
    rewrite /echo_pred. iLeft. iExact "Ht".
  Qed.

  (* ...AND THE CONVERSE, which is what makes the credential a tokenless
     console read leaves ([ConsoleInv.cons_dirty_cred app_rdcred], at its
     [app_sup] arm) READ AS THE TAINT (app-echo.md, lane SH-LINE, S4).  The claim is about EVERY view,
     and the empty view is a view: it satisfies none of the three pins, so
     the only disjunct that can hold at it is the taint.  That is the step
     sh's read takes when its window comes back under the dirty
     disjunction -- somebody consumed console input behind its back, and
     what it is handed instead of the window is exactly this credential. *)
  Lemma echo_taint_of_sup (γ : echo_fixed) (r : echo_names) :
    app_sup_raw (echo_pred γ) r -∗ echo_taint γ.
  Proof using .
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
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.

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
  Proof using .
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
  Proof using .
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
  Proof using .
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

(* THE CONCLUSION, at last: if the console input kept the discipline for the
   WHOLE run, then every power cycle emitted, on the CONSOLE's wire, a
   PREFIX of the session transcript that cycle's input calls for
   ([EchoDisc.good_out]) -- and nothing else, because the kernel's own
   messages go to the other UART.  It was [True] until 2026-09-12, and at
   [True] the whole theorem said SAFETY AND NOTHING ELSE.

   THE GUARD IS THE WHOLE HISTORY'S, NOT THE CYCLE'S (the owner's ruling,
   lane ECHO-OUT part 5: "there's no per-cycle form -- once we get taint in
   one era, it's tainted forever").  Until part 5 this was the PER-CYCLE
   form [Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of h)],
   which the ledger cannot pay: the taint is a run-wide monotone counter,
   so what the ledger holds is "the input was disciplined THROUGHOUT, or
   the taint" -- and that is exactly the implication below
   ([EchoOut.echo_led_phi]).

   [App.app_phi] takes the operational state as well; echo's conclusion
   reads only the trace, so the state argument is dropped -- the durable
   half of the claim is [echo_pred] in the crash slot, not here.

   THE OBLIGATION IS CLOSED (lane ECHO-OUT part 5).  [App.xv6_app_adequacy]'s
   [Hphi] is discharged at [UInitBootAdequacy] from [echo_R_phi] above, via
   [RiscvAdequacy.obs_ledger_at_phi]: the ledger is a pure reading, so the
   crash slot and the power interpretation are dropped. *)
Definition echo_phi : gstate -> list mobs -> Prop :=
  fun _ h => disc h -> Forall good_out (cycles_of h).

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
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  (* ---- THE FOUR CLAIMS, AT [EchoOut]'S (lane ECHO-OUT part 5).  They
         were [emp] placeholders until here; each is that file's claim at
         THIS file's taint, which is the [T] every one of its taint arms is
         stated at. ---- *)

  (* THE OUTPUT CLAIM: the taint, or the era's paired arm holding the four
     authorities -- the cursor, the line choices, the echoed list and a
     quarter of the window counter -- with the pure account of the accepted
     bytes ([EchoOut.eout_pure]) that [eout_drain] turns into
     [EchoDisc.good_out]. *)
  (* THE ERA'S TURN: <init>'s console credential, the era's cursor at ZERO
     with the two bounds a write spends -- literally
     [EchoOut.echo_write_link]'s argument list at [P = 0].  It takes no
     taint arm: it is MINTED once per era by the ledger's power-on step and
     nothing else may produce one. *)
  Definition echo_turn (γ : echo_fixed) : nat -> iProp Σ :=
    EchoOut.eturn γ.

  (* [echo_win] lived here. *)

  (* THE MERGED CONSOLE CLAIM (redesign R2/R3): the era's four authorities
     over ONE console history -- what the port's invariant carries, what a
     writer's link moves by [EvOut], what consoleintr's arm moves by
     [EvOpen]/[EvByte]/[EvClose] and what a read moves by [EvRead]. *)
  (* THE APPLICATION'S CONSOLE INTERFACE (redesign R4), as one value: the
     tag beside a received byte, the kill credential (which IS the taint --
     a kill under this discipline is impossible, so what a party a kill
     touched may keep is the fact the taint already states), and the
     console claim. *)
  Definition echo_cons (γ : echo_fixed) :
      nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ :=
    EchoOut.ecl (echo_taint γ) γ.

  Global Instance echo_cons_timeless γ k h H :
    Timeless (echo_cons γ k h H).
  Proof using . rewrite /echo_cons. apply _. Qed.

  (* ...AND THE INTERFACE'S LICENCE LAW ([RiscvPtsto.ai_lic], lane
     SUP-ONE): the taint IS echo's kill credential, and a tainted
     application's console claim answers ANY boundary event out of its
     taint arm.  This is [echo_al_sup]'s conclusion read one step earlier
     -- at the CREDENTIAL rather than at the supply -- and it is the proof
     [UInitBoot] used to write out by hand. *)
  Lemma echo_cons_lic (γ : echo_fixed) :
    echo_taint γ ⊢
      □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
           (ev : ConsLog.cons_ev),
           echo_cons γ k h H ==∗ echo_cons γ k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /echo_cons. iIntros "#Ht !>" (k h H ev) "Ho".
    iApply (EchoOut.ecl_sup (echo_taint γ) γ k h H ev with "Ht Ho").
  Qed.

  (* THE APPLICATION'S CONSOLE INTERFACE (redesign R4), as one value: the
     tag beside a received byte, the kill credential (which IS the taint --
     a kill under this discipline is impossible, so what a party a kill
     touched may keep is the fact the taint already states), and the console
     claim.  The three instances ride with them, where they were five
     obligations of [App.xv6_app_adequacy]. *)
  Definition echo_ifc (γ : echo_fixed) : app_iface Σ :=
    MkAppIface (echo_tag γ) (echo_tag_persistent γ) (echo_tag_timeless γ)
               (echo_taint γ) (echo_taint_persistent γ)
               (echo_taint_timeless γ)
               (echo_cons γ) (echo_cons_timeless γ)
               (echo_cons_lic γ)
               wild_none (@wild_none_persistent Σ) (@wild_none_timeless Σ)
               (wild_none_lic (echo_cons γ)).

  Definition app_echo : xv6_app Σ :=
    MkApp echo_fixed echo_cl echo_names echo_pred echo_boot echo_R
          echo_ifc echo_turn echo_phi.

  (* ---- THE BIRTH STEP ---- *)
  Lemma echo_Hbirth : ⊢ |==> ∃ c : app_fixed app_echo, app_cl app_echo c.
  Proof using . cbn [app_echo app_fixed app_cl]. exact echo_birth. Qed.

  (* ---- THE TRACE LEDGER'S FIVE ---- *)
  Lemma echo_HRt (c : app_fixed app_echo) (h : list mobs) :
    Timeless (app_R app_echo c h).
  Proof using . cbn [app_echo app_fixed app_R] in c |- *. apply _. Qed.

  (* [echo_Htagp], [echo_Htagt], [echo_Hkillp] and [echo_Hkillt] lived
     here: they ride [echo_ifc] now (redesign R4). *)

  Lemma echo_Hkillt (c : app_fixed app_echo) :
    Timeless (app_kill app_echo c).
  Proof using . cbn [app_echo app_fixed app_kill] in c |- *. apply _. Qed.

  (* the supply buys the credential, and at echo the two are the same
     reading of the counter ([echo_taint_of_sup]) *)
  Lemma echo_al_kill (c : app_fixed app_echo) (r : app_names app_echo) :
    AppInv.app_sup_raw (app_pred app_echo c) r ⊢ □ app_kill app_echo c.
  Proof using .
    rewrite /app_kill.
    cbn [app_echo app_fixed app_names app_pred app_ifc echo_ifc ai_kill]
      in c, r |- *.
    iIntros "#Hs". iModIntro. iApply (echo_taint_of_sup c r with "Hs").
  Qed.

  (* [echo_Houtt], [echo_Hinpt], [echo_Hwint] and [echo_Hconst] lived here:
     the claims' instances, which ride [echo_ifc] now. *)

  (* [echo_al_sup] lived here: one resource admits one law. *)

  (* ONE LICENCE (redesign R2): a holder of the supply is a party the
     discipline has already accounted for, so its claim answers ANY
     boundary event -- out of the taint arm, which is what holding the
     supply buys ([echo_taint_of_sup]). *)
  Lemma echo_al_sup (c : app_fixed app_echo) (r : app_names app_echo) :
    AppInv.app_sup_raw (app_pred app_echo c) r
      ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
             (ev : ConsLog.cons_ev),
             app_cons app_echo c k h H ==∗
             app_cons app_echo c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /app_cons.
    cbn [app_echo app_fixed app_names app_ifc echo_ifc ai_cons echo_cons]
      in c, r |- *.
    iIntros "#Hs".
    iDestruct (echo_taint_of_sup c r with "Hs") as "#Ht".
    iIntros "!>" (k h H ev) "Ho".
    iApply (EchoOut.ecl_sup (echo_taint c) c k h H ev with "Ht Ho").
  Qed.

  Lemma echo_HR0 (c : app_fixed app_echo) :
    app_cl app_echo c ⊢ |==> app_R app_echo c [].
  Proof using . cbn [app_echo app_fixed app_cl app_R] in c |- *. exact (echo_R_alloc c). Qed.

  (* ...AND THE ERA'S FOUR YIELDS ON THE ON-ARM (lane CONS-IO milestone E,
     e5-design REVISION 8; the claims are real since lane ECHO-OUT part 5).
     This is where the era's ghosts are allocated, its pin is minted in the
     ledger's era map, and the four shares are split out:
     [EchoOut.echo_led_pow_cl] is exactly this obligation's shape. *)
  Lemma echo_Hpow (c : app_fixed app_echo) (h : list mobs) (on : bool)
      (dk : Z -> bv 8) :
    trace_shape h on ->
    ⊢ app_R app_echo c h ==∗
      app_R app_echo c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
      (if on then emp
       else app_cons app_echo c (S (obs_boots h)) []
              (LogEntryDefs.MkCH [] [] [] None) ∗
            (* ...and the era's turn beside it: this is where the era's
               LINEAR seed is minted out of the ledger, for <init>. *)
            app_turn app_echo c (S (obs_boots h))).
  Proof using .
    intros _.
    rewrite /app_cons.
    cbn [app_echo app_fixed app_R echo_R app_ifc echo_ifc ai_cons echo_cons
         app_turn echo_turn] in c |- *.
    iApply (EchoOut.echo_led_pow_cl (echo_taint c) c h on).
  Qed.

  (* the two UART arms, at the theorem's literal shape: the device ghosts
     are FRAMED around the ledger step, which is [echo_R_tx]/[echo_R_rx].
     [uartGhostG] is what [uart_ghosts] reads; it is a MEMBER of [Xv6G.xv6G],
     which the theorem carries ambiently, so a binder here is what the
     theorem's own context supplies at the application site. *)
  Lemma echo_Htx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_echo) (r : app_names app_echo)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_echo) (app_pred app_echo c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
           (ho : list mobs) (H : LogEntryDefs.cons_hist),
           ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
           ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
           (* the LOOP-off rider, the witness history's reality, and the
              accepted bytes as the history's own field (redesign R2) *)
           ⌜u_wire u = u_out u⌝ -∗ ⌜obs_boots h = S gen_id⌝ -∗
           ⌜ho `prefix_of` h⌝ -∗
           ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
           (if i is Uart0 then app_cons app_echo c (S gen_id) ho H else emp) -∗
           uart_ghosts γ u' -∗ app_R app_echo c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           (if i is Uart0 then app_cons app_echo c (S gen_id) ho H else emp) ∗
           uart_ghosts γ u' ∗ app_R app_echo c (h ++ [ObsUartOut i b])%list).
  Proof using .
    intros _ _.
    rewrite /app_cons.
    cbn [app_echo app_fixed app_R echo_R app_ifc echo_ifc ai_cons echo_cons]
      in c |- *.
    iIntros "!>" (h b u u' ho H)
      "%Htxp %Hlp %Hsh %Hwi %Hwo %Hbt %Hpo %Hacc Ho Hg Hled".
    (* THE GOODNESS OF THE DRAINED SEGMENT, at the console and nowhere else
       (handover 5 §7b).  [EchoOut.eout_drain] reads the claim at its own
       witness [ho] and returns it untouched; its two arithmetic premises
       are that an OUTPUT adds no input, and that the wire extended by this
       byte is a prefix of what the port has accepted. *)
    iAssert (|==> (if i is Uart0
                   then EchoOut.ecl (echo_taint c) c (S gen_id) ho H
                   else emp)
                  ∗ (echo_taint c
                     ∨ ⌜i = Uart0 ->
                        good_out (open_seg h ++ [ObsUartOut i b])⌝))%I
      with "[Ho]" as ">[Ho Hgo]".
    { destruct i; last first.
      { iModIntro. iFrame "Ho". iRight. iPureIntro. discriminate. }
      (* AN OUTPUT ADDS NO INPUT, so the drained segment sits in the claim's
         own cycle *)
      assert (Hins : ins (open_seg h ++ [ObsUartOut Uart0 b])
                     = ins (open_seg h))
        by (by rewrite ins_app ins_out app_nil_r).
      (* ...AND THE WIRE, EXTENDED BY THIS BYTE, IS A PREFIX OF WHAT THE
         PORT HAS ACCEPTED: [uart_acc u = uart_acc u' = u_out u' ++ u_tx u']
         and [u_out u' = u_out u ++ [b]] *)
      assert (Hpre : obs_wire Uart0 (open_seg h ++ [ObsUartOut Uart0 b])
                     `prefix_of` uart_acc u).
      { rewrite obs_wire_app Hwi Hwo.
        replace (obs_wire Uart0 [ObsUartOut Uart0 b]) with [b] by reflexivity.
        rewrite -(DevModel.uart_tx_pop_acc u b u' Htxp) /DevModel.uart_acc
                (DevModel.uart_tx_pop_out u b u' Htxp).
        exists (u_tx u'). by rewrite -app_assoc. }
      iDestruct (EchoOut.ecl_drain (echo_taint c) c (S gen_id) h ho H
                   (open_seg h ++ [ObsUartOut Uart0 b])
                   Hsh Hbt Hpo Hins ltac:(rewrite Hacc; exact Hpre)
                   with "Ho") as "[Ho Hgo]".
      iModIntro. iFrame "Ho".
      iDestruct "Hgo" as "[HT | %Hg]"; [by iLeft |].
      iRight. iPureIntro. by intros _. }
    iMod (EchoOut.echo_led_tx (echo_taint c) c h i b Hsh with "Hgo Hled")
      as "Hled".
    iModIntro. iFrame "Ho Hg Hled".
  Qed.

  (* THE ECHO'S JUSTIFICATION (lane OUT-FUPD, F3; REAL since lane ECHO-OUT
     part 5).  [EchoOut.echo_happ_echo] is the proof: the tag's disciplined
     arm gives the shift the history's shape and its discipline, the
     kernel-lent window token pays the store, and the taint arm answers
     every firing after the discipline has broken.  All this file does is
     hand it the FOUR record equations at the [boot_fixedGS] literal. *)
  Lemma echo_Happ_echo (HR : riscvGS Σ) (c : app_fixed app_echo) :
    (* ONE EQUATION (redesign R4): the shift reads the machine's ambient tag
       family and its ambient console claim, and both are projections of the
       interface this record sets. *)
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_echo c ->
    ⊢ ∀ (GEN : GenId) (XI : CurCtx), @cons_echo_shift Σ HR GEN XI.
  Proof using .
    cbn [app_echo app_fixed app_ifc] in c |- *.
    intros Hiface.
    iApply (EchoOut.echo_happ_echo (echo_taint c) c (HRg := HR)).
    - rewrite /riscv_cons_res Hiface. by cbn [echo_ifc ai_cons echo_cons].
    - rewrite /riscv_rx_tag Hiface. by cbn [echo_ifc ai_tag].
  Qed.

  Lemma echo_Hrx `{!uartGhostG Σ} `{HF : !fileG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      (c : app_fixed app_echo) (r : app_names app_echo)
      (i : uart_id) (γ : uart_names) :
    @file_app Σ HF = MkAppcfg (app_names app_echo) (app_pred app_echo c) r ->
    (i = Uart0 -> FsCfg.fsc_uart = γ) ->
    ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
           ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
           ⌜obs_boots h = S gen_id⌝ -∗
           uart_ghosts γ u' -∗ app_R app_echo c h
             ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
           uart_ghosts γ u' ∗ app_R app_echo c (h ++ [ObsUartIn i b])%list ∗
           app_tag app_echo c (h ++ [ObsUartIn i b])%list).
  Proof using .
    intros _ _.
    cbn [app_echo app_fixed app_R app_tag] in c |- *.
    iIntros "!>" (h b u u') "_ %Hsh _ Hg Hled".
    iMod (echo_R_rx c h i b Hsh with "Hled") as "[Hled Htag]".
    iModIntro. iFrame "Hg Hled Htag".
  Qed.

  (* ---- THE TRANSPORT, WITH THE FIRST PROCESS'S BOOT RESOURCE ---- *)
  Lemma echo_Happ_boot (c : app_fixed app_echo) (k : nat) :
    ⊢ app_xfer_boot_raw (app_pred app_echo c) (app_boot app_echo c k).
  Proof using .
    cbn [app_echo app_fixed app_names app_pred app_boot] in c |- *.
    rewrite /app_xfer_boot_raw. iApply echo_xfer_boot.
  Qed.

  (* ...and the old obligation, which the commit's law and the era mint
     still take ([SystemAdequacy.app_xfer_raw_of_boot]) *)
  Lemma echo_Happ_xfer (c : app_fixed app_echo) :
    ⊢ app_xfer_raw (app_pred app_echo c).
  Proof using .
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
  Proof using .
    intros Himg Hdk Hsb Hcov c.
    cbn [app_echo app_fixed app_names app_pred] in c |- *.
    exact (echo_init_img c _ XV6_DISK_BYTES sb nib cov Himg Hdk Hsb Hcov).
  Qed.

  (* ---- THE CONCLUSION'S ONE INGREDIENT (lane ECHO-OUT part 5).  [Hphi]
         itself is discharged at [UInitBootAdequacy] -- this file does not
         carry the adequacy cone's [boot_fixedGS] literal -- and what it
         needs from here is that the LEDGER ALONE decides [app_phi], which
         is [RiscvAdequacy.obs_ledger_at_phi]'s premise exactly.  The crash
         slot and the power interpretation are dropped: the taint is a fact
         about the TRACE, and the ledger holds it. ---- *)
  Lemma echo_Hphi_R (c : app_fixed app_echo) (g : gstate) (h : list mobs) :
    app_R app_echo c h ⊢ ⌜app_phi app_echo g h⌝.
  Proof using .
    cbn [app_echo app_fixed app_R app_phi echo_phi] in c |- *.
    exact (echo_R_phi c h).
  Qed.
End EchoApp.
