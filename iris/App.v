(* App.v -- APPLICATIONS: the record, and the whole-system theorem at one.

   Design of record: claude-notes/projects/app-instances.md (sections 0-2,
   6, 7), superseding design/applications.md sections 1-3 while its rounds
   land.  An application is a collection of user programs plus what it
   claims -- a FIXED PART (section 6 ruling 1: a [Type] of its own, born
   once by its birth step and carried by the machine's record for the
   whole run), a predicate on the abstract file-system state's VIEW at the
   fixed part and at its own per-instance ghost names ([AppCfg.appcfg]'s
   data), what it is lent at every boot about the durable state, a trace
   ledger, and a pure conclusion.  The DATA is the record [xv6_app]; the
   OBLIGATIONS are the premises of [xv6_app_adequacy], stated exactly as
   [SystemAdequacy.xv6_power_adequacy_gen] states them (at the raw gnames
   and the fixed part, the [boot_fixedGS] literal), so that an application
   that can pay some and not others is a DEFINITION and never a vacuous
   theorem.

   THE GENERIC APPLICATION [app_triv] -- user space does anything, the
   abstract state is anything, the kernel stays correct -- pays every
   obligation trivially; [SystemAdequacy.xv6_trace_adequacy] and its
   siblings are [xv6_power_adequacy_gen] at exactly its data.  The first
   non-trivial application is [AppEcho.v]; what it still owes is
   claude-notes/projects/app-echo.md.

   HOW THE PIECES MEET THE THEOREM.
   - [app_fixed]/[app_cl] are the BIRTH STEP: [Hbirth] runs FIRST in
     [RiscvAdequacy.riscv_power_adequacy], before the crash slot, and the
     value it yields is [RiscvPtsto.riscv_client] of every era's record.
   - [app_names]/[app_pred] become the era's [AppCfg.appcfg]:
     [SystemAdequacy.xv6_boot_era] builds the record
     [MkAppcfg _ (app_pred c) r] -- the fixed part APPLIED -- at the
     running instance [r] the boot obligation witnesses and threads it to
     the era mint ([FsCfgSnap.fs_cfg_alloc_snap]), which founds the
     application's invariant ([AppInv.app_inv]: its half of the abstract
     map's authority beside its claim) at the founded map's view.  The
     claim IS the application's DURABLE one (app-instances.md round C):
     the crash slot is the composite [SystemAdequacy.xv6_slot] -- the file
     system's record beside the application's claim at the same snapshot
     name ([AppDur.app_dur_raw]) -- the PowerOn arm clones it onto the
     lend by the TRANSPORT [Happ_xfer], and the boot founds the era from
     the lent claim.  Era 0's claim is [Happ_init], at the image's state.
   - [Happ_auto] is the application's PARKED LICENSE ([AppInv.app_auto]):
     the moves it admits from anyone -- in round A, every one-row move
     ([AppInv.top_move]), which is why a constraining application cannot
     pay it yet ([AppEcho]); the era mint parks it in [app_inv].
   - [app_R c] is the trace slot's resource at the fixed part; [HR0]
     RECEIVES the birth step's yield ([obs_ledger_at_alloc_cl]) -- for the
     echo application, its taint counter at 0; the power step and the two
     UART-arm wands are [xv6_trace_adequacy]'s, quantified over the fixed
     part (the record's [riscv_client] is it by iota at the boot).
   - [app_phi] is read at the end of the run by [Hphi], which holds the
     crash predicate and the ledger side by side -- which is where an
     application relates "the input kept the discipline" (its counter at
     0) to "the durable state is still what it claims" (the crash
     predicate's arm of the disjunction; lane L4). *)
(* Require block: SystemAdequacy.v's, VERBATIM (durable-notes: trimmed
   imports have OOM'd the build), plus this file's own lines. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang ObsTrace RiscvPtsto.
Require Import FsState.
Require Import FsAbsDefs.        (* [aview], [abs_view]: the claim is over the view *)
Require Import AppInv.           (* [app_auto_raw]: the parked license, at the raw gname *)
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import FsCfgBoot.
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import FsDurSnap.
Require Import VirtioModel.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import FsImg.
Require Import ProcAvail.
Require Import Xv6G.
(* ...and the rest of SystemAdequacy's block, which the first cut missed:
   a class name that is not in scope silently becomes a VARIABLE
   (durable-notes), which is how [ufdG] became one here once. *)
Require Import UserFd.
(* ...and this file's own *)
Require Import FsNode.
Require Import AppCfg.           (* [appcfg]: what the record's data becomes at the era *)
Require Import SystemAdequacy.
(* the image's own superblock and region width, and the disk literal, for
   the closed corollary at the real image *)
Require Import FsImgCheck.
Require FsImgDisk.
Local Open Scope Z_scope.

Record xv6_app (Σ : gFunctors) := MkApp {
  (* THE FIXED PART (app-instances.md section 6 ruling 1): its type, and
     what the birth step yields about a value of it -- born once, before
     the crash slot, and the machine record's [riscv_client] for the run *)
  app_fixed : Type;
  app_cl    : app_fixed -> iProp Σ;
  (* the application's own per-instance ghost names, and its predicate on
     the abstract state's VIEW at the fixed part and an instance
     (section 1): an iProp -- a claim that OWNS resources -- and, applied
     at the fixed part, the era's [AppCfg.app_pred] *)
  app_names : Type;
  app_pred  : app_fixed -> app_names -> aview -> iProp Σ;
  (* the trace ledger, at the fixed part (section 4) *)
  app_R     : app_fixed -> list mobs -> iProp Σ;
  (* the conclusion, over the operational state and the run's trace *)
  app_phi   : gstate -> list mobs -> Prop;
}.
Arguments MkApp {Σ} _ _ _ _ _ _.
Arguments app_fixed {Σ} _. Arguments app_cl {Σ} _ _.
Arguments app_names {Σ} _. Arguments app_pred {Σ} _ _ _ _.
Arguments app_R {Σ} _ _ _. Arguments app_phi {Σ} _ _ _.

(* THE GENERIC APPLICATION: no fixed part, nothing claimed, nothing read *)
Definition app_triv (Σ : gFunctors) : xv6_app Σ :=
  MkApp unit (fun _ => True%I) unit (fun _ _ _ => True%I)
        (fun _ _ => emp%I) (fun _ _ => True).

(* ---------------------------------------------------------------------- *)
(* THE THEOREM.  [xv6_power_adequacy_gen] at the application: the birth    *)
(* step is [app_cl]'s, the trace slot is the ledger of [app_R] at the fixed *)
(* part, the lend is the FS's epoch beside [app_lend], the era's predicate  *)
(* is [app_pred] at the fixed part and the instance the boot obligation     *)
(* witnesses.                                                               *)
(* ---------------------------------------------------------------------- *)
Theorem xv6_app_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ}
    `{!ufdG Σ}
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (A : xv6_app Σ)
    (* ---- THE BIRTH STEP (app-instances.md section 6 ruling 1): one value
       of the fixed part, with what [app_cl] says of it ---- *)
    (Hbirth : ⊢ |==> ∃ c : app_fixed A, app_cl A c)
    (* ---- the trace ledger's obligations ([xv6_trace_adequacy]'s, the
       birth step's yield received at the ledger's birth) ---- *)
    (HRt : forall (c : app_fixed A) (h : list mobs), Timeless (app_R A c h))
    (HR0 : forall c : app_fixed A, app_cl A c ⊢ |==> app_R A c [])
    (Hpow : forall (c : app_fixed A) (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ app_R A c h ==∗
         app_R A c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list)
    (* the two UART-arm wands, at any value of the fixed part: the era
       instance's [riscv_client] is the one the boot's record carries, and
       the record's client type is [app_fixed A] only at that literal *)
    (Htx : forall (HR : riscvGS Σ) (c : app_fixed A) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire (open_seg h) = u_wire u⌝ -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartOut b])%list))
    (Hrx : forall (HR : riscvGS Σ) (c : app_fixed A) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartIn b])%list))
    (* ---- the application's three obligations on its predicate
       (app-instances.md sections 1-3, round C): the TRANSPORT (its one
       durability obligation -- a copy of the claim at fresh instance names,
       under the later every crossing hands it over at), the ERA-0 claim
       at the image's own abstract state, and the parked license ---- *)
    (Happ_xfer : forall c : app_fixed A, ⊢ app_xfer_raw (app_pred A c))
    (Happ_init : forall c : app_fixed A,
       ⊢ |==> ∃ r : app_names A,
           app_pred A c r (abs_view (fss_inodes (FsDurImg.img_state
              (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))))
    (Happ_auto : forall (c : app_fixed A) (r : app_names A),
       ⊢ app_auto_raw (app_pred A c) r)
    (* ---- the conclusion's proof, at the end of the run: it holds the
       COMPOSITE crash slot ([SystemAdequacy.xv6_slot]: the file system's
       record beside the application's durable claim at the same snapshot
       name) and the ledger side by side ---- *)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γsw γobs : gname) (c : app_fixed A)
                   (T : list mobs) (g' : gstate) (h : list mobs),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
                  γd γsw γreg γstart c)
               γobs T (obs_ledger_at (app_R A c) γobs) (app_fixed A) c) g' -∗
         ghost_var γobs (1/2) h -∗ ⌜obs_wf h g'⌝ -∗
         ▷ xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
             γd γsw γreg γstart c -∗
         ▷ obs_ledger_at (app_R A c) γobs -∗
         ◇ ⌜app_phi A g' h⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
              sb nib cov) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ app_phi A g2 κs.
Proof.
  (* the permit at the ledger: the application's two wands, at the record
     the era boots over -- where [riscv_client] IS the fixed part the
     ledger was born with, by iota once the record's shape is destructed *)
  assert (Hperm : forall (HR : riscvGS Σ) (GEN : GenId) (γ : uart_names),
      (exists (Hinv : invGS Σ) (γgen γstart γreg γd γsw γobs : gname)
              (c : app_fixed A) (T : list mobs),
         riscv_fixedGS =
           boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
             (xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
                γd γsw γreg γstart c)
             γobs T (obs_ledger_at (app_R A c) γobs) (app_fixed A) c) ->
      ⊢ obs_inv -∗ uart_obs_permit γ).
  { intros HRg GEN γ (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Gcl & GT & Heq).
    refine (uart_obs_permit_ledger (app_R A Gcl) γ (HRt Gcl) _
              (Htx HRg Gcl γ) (Hrx HRg Gcl γ)).
    rewrite Heq. reflexivity. }
  exact (xv6_power_adequacy_gen Σ g sb nib cov
           (app_fixed A) (app_cl A) Hbirth
           (app_names A) (app_pred A) Happ_xfer Happ_init Happ_auto
           (fun γobs c => obs_ledger_at (app_R A c) γobs)
           (fun γobs c =>
              obs_ledger_at_alloc_cl (app_R A c) γobs (app_cl A c) (HR0 c))
           (fun γd γobs c =>
              obs_ledger_at_step XV6_DISK_BYTES (app_R A c) (HRt c) (Hpow c)
                γd γobs)
           Hperm (app_phi A) Hphi Hgen0 Hpow0 Himg).
Qed.

(* ---------------------------------------------------------------------- *)
(* THE GENERIC APPLICATION PAYS EVERYTHING: the five obligations that       *)
(* mention its data, each in one line.  [xv6_trace_adequacy] is the record  *)
(* at these with a client's ledger in place of [emp].                       *)
(* ---------------------------------------------------------------------- *)
Section AppTriv.
  Context {Σ : gFunctors} `{!riscvGpreS Σ}.

  (* the birth step: no fixed part, so [()] and nothing about it *)
  Lemma app_triv_birth :
    ⊢ |==> ∃ c : app_fixed (app_triv Σ), app_cl (app_triv Σ) c.
  Proof.
    iModIntro. cbn [app_triv app_fixed app_cl].
    iExists (). iPureIntro. exact Logic.I.
  Qed.

  (* the transport: a predicate that holds of every view is its own copy *)
  Lemma app_triv_xfer (c : app_fixed (app_triv Σ)) :
    ⊢ app_xfer_raw (app_pred (app_triv Σ) c).
  Proof.
    cbn [app_triv app_pred]. apply app_xfer_raw_triv.
    intros r av. reflexivity.
  Qed.

  (* era 0: the claim at any view, at the one instance *)
  Lemma app_triv_init (c : app_fixed (app_triv Σ)) (av : aview) :
    ⊢ |==> ∃ r : app_names (app_triv Σ), app_pred (app_triv Σ) c r av.
  Proof.
    iModIntro. cbn [app_triv app_names app_pred].
    iExists (). iPureIntro. exact Logic.I.
  Qed.

  Lemma app_triv_auto (c : app_fixed (app_triv Σ)) (r : app_names (app_triv Σ)) :
    ⊢ app_auto_raw (app_pred (app_triv Σ) c) r.
  Proof.
    cbn [app_triv app_pred]. apply app_auto_raw_triv.
    intros r' av. reflexivity.
  Qed.

  Lemma app_triv_R0 (c : app_fixed (app_triv Σ)) :
    app_cl (app_triv Σ) c ⊢ |==> app_R (app_triv Σ) c [].
  Proof. iIntros "_". by iModIntro. Qed.
End AppTriv.

(* ---------------------------------------------------------------------- *)
(* THE ARBITRARY APPLICATION, CLOSED: at the real image, powered off,       *)
(* never booted, every run is reducible.  The application's conclusion is   *)
(* [True], so the statement says reducibility and nothing else -- and       *)
(* DELIBERATELY names no [Σ]: stated as [app_phi (app_triv xv6Σ) g2 κs] it  *)
(* would unfold through the record at the functor list and put the whole    *)
(* ghost layer (the camera classes [xv6Σ] names) into the STATEMENT's       *)
(* trusted base, ~500 lines nobody has to read for "every run is           *)
(* reducible" (tools/tcb; measured 2026-09-05).  Every obligation of the    *)
(* record is a line; the generic user-safety WP is what the boot mints, so  *)
(* user space does anything and the abstract state is anything.            *)
(* ---------------------------------------------------------------------- *)
Corollary xv6_app_adequacy_triv_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2.
Proof.
  intros n κs t2 g2 Hn.
  refine (proj1 (xv6_app_adequacy xv6Σ g fsimg_sb fsimg_nib fsimg_cov (app_triv xv6Σ)
           app_triv_birth
           ltac:(intros c h; cbn [app_triv app_R]; apply _)
           app_triv_R0
           ltac:(intros c h on dk _; cbn [app_triv app_R]; iIntros "_"; by iModIntro)
           ltac:(intros HR c γ; cbn [app_triv app_R];
                 iIntros "!>" (h b u u') "_ _ _ _ Hg _"; iModIntro; by iFrame "Hg")
           ltac:(intros HR c γ; cbn [app_triv app_R];
                 iIntros "!>" (h b u u') "_ _ Hg _"; iModIntro; by iFrame "Hg")
           app_triv_xfer
           ltac:(intros c; exact (app_triv_init c _))
           app_triv_auto
           ltac:(intros Hinv γgen γstart γreg γd γsw γobs c T g' h;
                 iIntros "_ _ _ _ _"; iModIntro; iPureIntro; exact Logic.I)
           Hgen0 Hpow0 _ n κs t2 g2 Hn)).
  rewrite Hdisk. exact fsimg_image_wf.
Qed.
