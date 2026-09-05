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
     the PREDICATE [echo_fs]    -- the binaries are the image's: the era-0
                                   pins of /init and /sh
                                   ([FsInitPinBoot.era0_pins],
                                   [FsShPin.era0_sh_pins]) read on the
                                   abstract state's VIEW ([FsAbsDefs.aview],
                                   app-instances.md round A -- the
                                   application's [app_pred], ignoring its
                                   fixed part and its instance; echo's own
                                   pin is lane L6's, with its Uk-engine
                                   proof);
     the BOOT obligation AT ERA 0 -- the founded map satisfies [echo_fs]
                                   when the disk is the mkfs image
                                   ([echo_fs_era0]).

   WHAT IS DELIBERATELY NOT HERE: a theorem.  The application's parked
   license ([AppInv.app_auto], over [AppInv.top_move]) is UNPAYABLE for
   [echo_fs] until round E of app-instances.md narrows [top_move] -- in
   round A it admits every one-row move, which no pin survives -- exactly
   as the old delta-free license was payable only from [tainted]; the boot
   lend at a non-pristine boot needs the durable instance (round C); the
   conclusion needs both.  A theorem taking those as hypotheses would be
   durable-notes.md's GAP-premise trap, so the application is a
   definition and its lanes are the worklist. *)
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
Require Import FsState.
Require Import FsNode.           (* [fs_node] *)
Require Import FsAbsDefs.        (* [aview], [abs_view] *)
Require Import FsInitPinBoot.    (* [era0_pins], [era0_recovery_pins] *)
Require Import FsShPin.          (* [era0_sh_pins], [era0_recovery_sh_pins] *)
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

  (* "untainted" is the counter at 0: what the end of the trace reads.  The
     TAINT [mono_nat_lb_own γcl 1] is this application's own fact now (it
     was the machine's [client_lb 1] before round D0). *)
  Lemma echo_R_untainted γcl h :
    disc h -> echo_R γcl h -∗ mono_nat_lb_own γcl 1 -∗ False.
  Proof.
    intros Hd. iIntros "Ha Hlb". rewrite /echo_R /echo_phase decide_True; last exact Hd.
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
     or already tainted (1 stays) -- monotone in every case *)
  Lemma echo_R_rx γcl h b :
    trace_shape h true ->
    echo_R γcl h ==∗ echo_R γcl (h ++ [ObsUartIn b]).
  Proof.
    intros Hsh. iIntros "H". rewrite /echo_R /echo_phase.
    destruct (decide (disc (h ++ [ObsUartIn b]))) as [Hd'|Hd'].
    - rewrite decide_True; last exact (disc_in h b Hsh Hd'). by iModIntro.
    - destruct (decide (disc h)) as [Hd|Hd].
      + iMod (mono_nat_own_update 1%nat with "H") as "[H _]"; [lia|]. by iModIntro.
      + by iModIntro.
  Qed.
End EchoLedger.

(* ====================================================================== *)
(*  3.  THE PREDICATE: the binaries are the image's                        *)
(* ====================================================================== *)

(* /init and /sh are the image's, path and content, on the abstract state's
   VIEW.  Echo's own pin is lane L6's (with the Uk-engine proof that needs
   it).  Per-inum rather than "the map is the image's" on purpose: the
   durable snapshot pins a state per inum and no whole-map equality exists
   (fs-syscall-specs.md lane D, gap (3)).  The claim is PURE -- it owns
   nothing -- so it is stated as a Prop and embedded: the application's
   predicate is an iProp over the view at a fixed name and an instance
   ([AppCfg.app_pred], app-instances.md section 7), and this application's
   happens to be [⌜echo_fs_pure av⌝] at every name and instance. *)
Definition echo_fs_pure (av : aview) : Prop :=
  era0_pins av /\ era0_sh_pins av.

Section EchoFs.
  Context {Σ : gFunctors}.

  Definition echo_fs (av : aview) : iProp Σ := ⌜echo_fs_pure av⌝%I.

  Lemma echo_fs_intro (av : aview) : echo_fs_pure av -> ⊢ echo_fs av.
  Proof. intros H. rewrite /echo_fs. iPureIntro. exact H. Qed.
End EchoFs.

(* THE BOOT OBLIGATION AT ERA 0: the view of the map a boot founds its file
   system at satisfies the predicate when the disk is mkfs's image -- the
   two pin files' transport theorems, read together.  About the Prop;
   [echo_fs_intro] lifts it. *)
Lemma echo_fs_era0 (dk : Z -> bv 8) (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  echo_fs_pure (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec HS. split.
  - exact (era0_recovery_pins dk D S Hdk Hrec HS).
  - exact (era0_recovery_sh_pins dk D S Hdk Hrec HS).
Qed.
