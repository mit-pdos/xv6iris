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
     the LEDGER [echo_R]        -- the client phase counter at 0 while the
                                   input keeps the discipline and at 1
                                   from the first byte that breaks it, so
                                   [client_auth 0] IS "untainted";
     its four steps             -- birth, the power arm, the tx arm, the
                                   rx arm ([echo_R_alloc], [echo_R_pow],
                                   [echo_R_tx], [echo_R_rx]), each a basic
                                   update over the ledger alone: the
                                   theorem's wands frame the UART ghosts
                                   around them;
     the PREDICATE [echo_fs]    -- the binaries are the image's: the era-0
                                   pins of /init and /sh
                                   ([FsInitPinBoot.era0_pins],
                                   [FsShPin.era0_sh_pins]) read on the
                                   abstract state (echo's own pin is lane
                                   L6's, with its Uk-engine proof);
     the BOOT obligation AT ERA 0 -- the founded map satisfies [echo_fs]
                                   when the disk is the mkfs image
                                   ([echo_fs_era0]).

   WHAT IS DELIBERATELY NOT HERE: a theorem.  The license is payable only
   from [tainted] until lane L2; the boot lend at a non-pristine boot
   needs the crash predicate's application conjunct (lane L4); the
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
Require Import FsAbsDefs.        (* [abs_view] *)
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
(*  2.  THE LEDGER: the client phase counter reads the discipline          *)
(* ====================================================================== *)

Section EchoLedger.
  Context `{!mono_natG Σ}.

  (* the counter's value at a history: 0 while disciplined, 1 after *)
  Definition echo_phase (h : list mobs) : nat :=
    if decide (disc h) then 0%nat else 1%nat.

  Definition echo_R (γcl : gname) (h : list mobs) : iProp Σ :=
    mono_nat_auth_own γcl 1 (echo_phase h).

  Global Instance echo_R_timeless γcl h : Timeless (echo_R γcl h).
  Proof. rewrite /echo_R. apply _. Qed.

  (* "untainted" is the counter at 0: what the end of the trace reads *)
  Lemma echo_R_untainted γcl h :
    disc h -> echo_R γcl h -∗ mono_nat_lb_own γcl 1 -∗ False.
  Proof.
    intros Hd. iIntros "Ha Hlb". rewrite /echo_R /echo_phase decide_True; last exact Hd.
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle]. lia.
  Qed.

  (* birth: the counter arrives at 0, and the empty history is disciplined *)
  Lemma echo_R_alloc γcl :
    mono_nat_auth_own γcl 1 0%nat ⊢ |==> echo_R γcl [].
  Proof.
    iIntros "H". rewrite /echo_R /echo_phase decide_True; last exact disc_nil.
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

(* /init and /sh are the image's, path and content, on the abstract state.
   Echo's own pin is lane L6's (with the Uk-engine proof that needs it).
   Per-inum rather than "the map is the image's" on purpose: the durable
   snapshot pins a state per inum and no whole-map equality exists
   (fs-syscall-specs.md lane D, gap (3)). *)
Definition echo_fs (I : gmap Z fs_node) : Prop :=
  era0_pins (abs_view I) /\ era0_sh_pins (abs_view I).

(* THE BOOT OBLIGATION AT ERA 0: the map a boot founds its file system at
   satisfies the predicate when the disk is mkfs's image -- the two pin
   files' transport theorems, read together. *)
Lemma echo_fs_era0 (dk : Z -> bv 8) (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  echo_fs (fss_inodes S).
Proof.
  intros Hdk Hrec HS. split.
  - exact (era0_recovery_pins dk D S Hdk Hrec HS).
  - exact (era0_recovery_sh_pins dk D S Hdk Hrec HS).
Qed.
