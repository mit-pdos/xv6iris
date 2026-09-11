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
From iris.base_logic.lib Require Import mono_nat.
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
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE DISCIPLINE                                                     *)
(* ====================================================================== *)

(* the console line the discipline admits: "echo hello world\n" *)
Definition echo_line : list (bv 8) :=
  Z_to_bv 8 <$> [101; 99; 104; 111; 32; 104; 101; 108; 108; 111; 32;
                 119; 111; 114; 108; 100; 10].

Lemma echo_line_length : length echo_line = 17%nat.
Proof. reflexivity. Qed.
Lemma echo_line_pos : (0 < length echo_line)%nat.
Proof. rewrite echo_line_length. lia. Qed.

(* the INPUT bytes of an observation list, in order *)
Definition ins (h : list mobs) : list (bv 8) :=
  omap (fun e => match e with ObsUartIn b => Some b | _ => None end) h.

Lemma ins_app (h κ : list mobs) : ins (h ++ κ) = ins h ++ ins κ.
Proof. by rewrite /ins omap_app. Qed.

Lemma ins_in (b : bv 8) : ins [ObsUartIn b] = [b].
Proof. reflexivity. Qed.
Lemma ins_out (b : bv 8) : ins [ObsUartOut b] = [].
Proof. reflexivity. Qed.

(* [l] IS A PREFIX OF [pat]^*, spelled so that it is decidable by one
   list equality and prefix-closed by one [take]: the first [length l]
   letters of [pat] repeated [length l] times are the first [length l]
   letters of [pat]^ω whenever [pat] is nonempty. *)
Definition star_prefix (pat l : list (bv 8)) : Prop :=
  l = take (length l) (concat (replicate (length l) pat)).

Global Instance star_prefix_dec pat l : Decision (star_prefix pat l).
Proof. rewrite /star_prefix. apply _. Qed.

Lemma star_prefix_nil pat : star_prefix pat [].
Proof. reflexivity. Qed.

Lemma concat_replicate_S {A} (n : nat) (pat : list A) :
  concat (replicate (S n) pat) = concat (replicate n pat) ++ pat.
Proof. by rewrite replicate_S_end concat_app /= app_nil_r. Qed.

Lemma concat_replicate_length {A} (n : nat) (pat : list A) :
  length (concat (replicate n pat)) = (n * length pat)%nat.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite concat_replicate_S length_app IH. lia.
Qed.

(* the one law the rx step needs: breaking the discipline is forever.  The
   first [length l] letters of the longer word are the first [length l]
   letters of the shorter one, because [pat^length l] already has them. *)
Lemma star_prefix_snoc pat l b :
  (0 < length pat)%nat ->
  star_prefix pat (l ++ [b]) -> star_prefix pat l.
Proof.
  rewrite /star_prefix. intros Hpat Hsnoc.
  apply (f_equal (take (length l))) in Hsnoc.
  rewrite take_app_length take_take in Hsnoc.
  rewrite length_app /= in Hsnoc.
  rewrite Nat.min_l in Hsnoc; [|lia].
  rewrite Nat.add_1_r concat_replicate_S in Hsnoc.
  rewrite take_app_le in Hsnoc; [exact Hsnoc|].
  rewrite concat_replicate_length. nia.
Qed.

(* one power cycle's input keeps the discipline *)
Definition disc_seg (seg : list mobs) : Prop := star_prefix echo_line (ins seg).

Global Instance disc_seg_dec seg : Decision (disc_seg seg).
Proof. rewrite /disc_seg. apply _. Qed.

Lemma disc_seg_nil : disc_seg [].
Proof. exact (star_prefix_nil _). Qed.

(* THE DISCIPLINE, over the WHOLE history (uart-trace.md ruling 1): every
   cycle's input so far is a prefix of [echo_line]^*.  [cycles_of h] lists
   every cycle, the open one LAST while the power is on
   ([ObsTrace.trace_shape_cycles]), so the open cycle is covered. *)
Definition disc (h : list mobs) : Prop := Forall disc_seg (cycles_of h).

Global Instance disc_dec h : Decision (disc h).
Proof. rewrite /disc. apply _. Qed.

Lemma disc_nil : disc [].
Proof. constructor. Qed.

(* ---- closure laws, one per event kind ---- *)

Lemma disc_seg_out (seg : list mobs) (b : bv 8) :
  disc_seg (seg ++ [ObsUartOut b]) <-> disc_seg seg.
Proof. rewrite /disc_seg ins_app ins_out app_nil_r. done. Qed.

Lemma disc_out (h : list mobs) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartOut b]) <-> disc h.
Proof.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartOut b] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton disc_seg_out. done.
Qed.

Lemma disc_power (h : list mobs) (on : bool) :
  disc (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> disc h.
Proof.
  rewrite /disc. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on Forall_app Forall_singleton.
    split; [by intros [? _] | intros ?; split; [done | exact disc_seg_nil]].
Qed.

Lemma disc_in (h : list mobs) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartIn b]) -> disc h.
Proof.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartIn b] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton.
  intros [Hall Hseg]. split; [exact Hall|].
  rewrite /disc_seg ins_app ins_in in Hseg.
  exact (star_prefix_snoc _ _ _ echo_line_pos Hseg).
Qed.

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

(* the application's instance names.  Echo's claim owns no per-instance
   ghost, so there is exactly one instance and nothing indexes it. *)
Definition echo_names : Type := unit.

Section EchoPred.
  Context `{!mono_natG Σ}.

  (* THE APPLICATION'S PREDICATE ([App.app_pred], app-instances.md section
     1 and app-echo.md "ARM-c"): TAINTED OR PINNED.  The left arm is the
     permanent fact that the console input has broken the discipline; the
     right arm is the three pins.  Both arms are persistent, which is the
     whole of the transport ([echo_xfer]), and the left arm alone proves
     the claim of EVERY view, which is the whole of the supply
     ([echo_sup_of_taint]) -- the credential a process that answers for
     nothing runs on.  The instance argument is ignored: there is one. *)
  Definition echo_pred (γ : echo_fixed) (_ : echo_names) (av : aview)
      : iProp Σ :=
    (echo_taint γ ∨ ⌜echo_fs_pure av⌝)%I.

  Global Instance echo_pred_persistent γ r av : Persistent (echo_pred γ r av).
  Proof. rewrite /echo_pred. apply _. Qed.
  Global Instance echo_pred_timeless γ r av : Timeless (echo_pred γ r av).
  Proof. rewrite /echo_pred. apply _. Qed.

  Lemma echo_pred_pins (γ : echo_fixed) (r : echo_names) (av : aview) :
    echo_fs_pure av -> ⊢ echo_pred γ r av.
  Proof. intros H. rewrite /echo_pred. iRight. iPureIntro. exact H. Qed.

  (* ---------------------------------------------------------------- *)
  (*  3a.  THE TRANSPORT ([Happ_xfer])                                  *)
  (* ---------------------------------------------------------------- *)

  (* app-instances.md round C, section 1: a copy of the claim at fresh
     instance names without spending the original.  Both arms of
     [echo_pred] are persistent, so the general law does it. *)
  Lemma echo_xfer (γ : echo_fixed) : ⊢ app_xfer_raw (echo_pred γ).
  Proof. apply app_xfer_raw_pers_or_pure. intros r av. apply _. Qed.

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
  Context `{!mono_natG Σ}.

  (* ...as the era-0 obligation's shape: the claim at the founded state's
     view, at the one instance, under the update.  It takes the RIGHT
     disjunct -- there is no taint at boot, and none is needed. *)
  Lemma echo_init (γ : echo_fixed) (dk : Z -> bv 8)
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
    fs_blocks dk = fsimg_P ->
    fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
    snap_ok S D ->
    ⊢ |==> ∃ r : echo_names, echo_pred γ r (abs_view (fss_inodes S)).
  Proof.
    intros Hdk Hrec HS. iModIntro. iExists ().
    iApply (echo_pred_pins γ () _ (echo_fs_era0 dk D S Hdk Hrec HS)).
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

(* THE CONCLUSION IS NOT WRITTEN YET, and this is the placeholder that says
   so LOUDLY.  [App.app_phi] is read at the end of the run by [Hphi]; the
   echo application's real one is "every power cycle's output is a prefix
   of the console stream its input calls for" ([good_out], app-echo.md's
   target statement), which needs the output side's located write receipts.
   At [True] the whole theorem would say SAFETY AND NOTHING ELSE -- an
   honest statement, but not this application's.  It is a [Definition] and
   never a hypothesis, so nothing downstream can mistake it for a claim. *)
Definition echo_phi : gstate -> list mobs -> Prop := fun _ _ => True.

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
  Context `{!mono_natG Σ}.

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
