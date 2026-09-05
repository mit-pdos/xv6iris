(* App.v -- APPLICATIONS: the record, and the whole-system theorem at one.

   Design of record: claude-notes/projects/app-instances.md (sections 0-2,
   7), superseding design/applications.md sections 1-3 while its rounds
   land.  An application is a collection of user programs plus what it
   claims -- a predicate on the abstract file-system state's VIEW, at its
   own per-instance ghost names ([AppCfg.appcfg]'s data), what it is lent
   at every boot about the durable state, a trace ledger, and a pure
   conclusion.  The DATA is the record [xv6_app]; the OBLIGATIONS are the
   premises of [xv6_app_adequacy], stated exactly as
   [SystemAdequacy.xv6_power_adequacy_gen] states them (at the raw gnames,
   the [boot_fixedGS] literal), so that an application that can pay some
   and not others is a DEFINITION and never a vacuous theorem.

   THE GENERIC APPLICATION [app_triv] -- user space does anything, the
   abstract state is anything, the kernel stays correct -- pays every
   obligation trivially; [SystemAdequacy.xv6_trace_adequacy] and its
   siblings are [xv6_power_adequacy_gen] at exactly its data.  The first
   non-trivial application is [AppEcho.v]; what it still owes is
   claude-notes/projects/app-echo.md.

   HOW THE PIECES MEET THE THEOREM.
   - [app_names]/[app_pred] become the era's [AppCfg.appcfg]:
     [SystemAdequacy.xv6_boot_era] builds the record [MkAppcfg _ app_pred r]
     at the running instance [r] the boot obligation witnesses and threads
     it to the era mint ([FsCfgSnap.fs_cfg_alloc_snap]), which founds the
     application's invariant ([AppInv.app_inv]: its half of the abstract
     map's authority beside its claim) at the founded map's view.  The
     claim is the application's BOOT obligation [Happ_boot], paid out of
     what the PowerOn arm lent ([app_lend γcl dk], produced by [Hlend] out
     of the crash predicate) -- until round C, when the durable instance
     replaces the lend.
   - [Happ_auto] is the application's PARKED LICENSE ([AppInv.app_auto]):
     the moves it admits from anyone -- in round A, every one-row move
     ([AppInv.top_move]), which is why a constraining application cannot
     pay it yet ([AppEcho]); the era mint parks it in [app_inv].
   - [app_R γcl] is the trace slot's resource at the client phase counter's
     name; [HR0] RECEIVES the counter at 0 ([obs_ledger_at_alloc_client]);
     the power step and the two UART-arm wands are [xv6_trace_adequacy]'s,
     at the ambient [riscv_client_name].
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
  (* the application's own per-instance ghost names, and its predicate on
     the abstract state's VIEW at a fixed name and an instance
     (app-instances.md section 1): an iProp -- a claim that OWNS resources
     -- and the era's [AppCfg.app_pred] *)
  app_names : Type;
  app_pred  : gname -> app_names -> aview -> iProp Σ;
  (* what the PowerOn arm lends the boot about the durable state, at the
     client phase counter's name (section 3); the boot obligation reads it *)
  app_lend : gname -> (Z -> bv 8) -> iProp Σ;
  (* the trace ledger, at the client phase counter's name (section 4) *)
  app_R    : gname -> list mobs -> iProp Σ;
  (* the conclusion, over the operational state and the run's trace *)
  app_phi  : gstate -> list mobs -> Prop;
}.
Arguments MkApp {Σ} _ _ _ _ _.
Arguments app_names {Σ} _. Arguments app_pred {Σ} _ _ _ _.
Arguments app_lend {Σ} _ _ _.
Arguments app_R {Σ} _ _ _. Arguments app_phi {Σ} _ _ _.

(* THE GENERIC APPLICATION: nothing claimed, nothing lent, nothing read *)
Definition app_triv (Σ : gFunctors) : xv6_app Σ :=
  MkApp unit (fun _ _ _ => True%I) (fun _ _ => emp%I) (fun _ _ => emp%I)
        (fun _ _ => True).

(* ---------------------------------------------------------------------- *)
(* THE THEOREM.  [xv6_power_adequacy_gen] at the application: the trace     *)
(* slot is the ledger of [app_R] at the client name, the lend is the FS's   *)
(* epoch beside [app_lend], the era's predicate is [app_pred] at the        *)
(* instance the boot obligation witnesses.                                  *)
(* ---------------------------------------------------------------------- *)
Theorem xv6_app_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ}
    `{!ufdG Σ}
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (A : xv6_app Σ)
    (* ---- the trace ledger's obligations ([xv6_trace_adequacy]'s, the
       counter received at the birth) ---- *)
    (HRt : forall (γcl : gname) (h : list mobs), Timeless (app_R A γcl h))
    (HR0 : forall γcl : gname,
       mono_nat_auth_own γcl 1 0%nat ⊢ |==> app_R A γcl [])
    (Hpow : forall (γcl : gname) (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ app_R A γcl h ==∗
         app_R A γcl (h ++ [if on then ObsPowerOff else ObsPowerOn])%list)
    (Htx : forall (HR : riscvGS Σ) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire (open_seg h) = u_wire u⌝ -∗
              uart_ghosts γ u' -∗ app_R A riscv_client_name h
                ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A riscv_client_name (h ++ [ObsUartOut b])%list))
    (Hrx : forall (HR : riscvGS Σ) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              uart_ghosts γ u' -∗ app_R A riscv_client_name h
                ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A riscv_client_name (h ++ [ObsUartIn b])%list))
    (* ---- the boot's lend, out of the crash predicate (section 3) ---- *)
    (Hlend : forall (γd γsw γreg γst γcl : gname) (dk : Z -> bv 8),
       ⊢ ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γst cov (FsImg.sb_logstart sb) -∗
         |==> ◇ (▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γst cov
                    (FsImg.sb_logstart sb) ∗
                 app_lend A γcl dk))
    (* ---- the era's two obligations (app-instances.md sections 1-2): the
       running claim at the founded map's view, at SOME instance -- the one
       the era runs at -- and the parked license ---- *)
    (Happ_boot : forall (γcl : gname) (S : fs_state_rec)
                        (D : gmap Z (list (bv 8))) (dk : Z -> bv 8),
       snap_ok S D ->
       fs_recovery (fs_blocks dk) D cov (FsImg.sb_logstart sb) ->
       ⊢ app_lend A γcl dk -∗
         |==> ∃ r : app_names A, app_pred A γcl r (abs_view (fss_inodes S)))
    (Happ_auto : forall (γcl : gname) (r : app_names A),
       ⊢ app_auto_raw γcl (app_pred A) r)
    (* ---- the conclusion's proof, at the end of the run ---- *)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γsw γobs γcl : gname) (T : list mobs)
                   (g' : gstate) (h : list mobs),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart cov
                  (FsImg.sb_logstart sb))
               γobs T (obs_ledger_at (app_R A γcl) γobs) γcl) g' -∗
         ghost_var γobs (1/2) h -∗ ⌜obs_wf h g'⌝ -∗
         ▷ P_fs_named γd XV6_DISK_BYTES γsw γreg γstart cov (FsImg.sb_logstart sb) -∗
         ▷ obs_ledger_at (app_R A γcl) γobs -∗
         ◇ ⌜app_phi A g' h⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
              sb nib cov) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ app_phi A g2 κs.
Proof.
  (* the permit at the ledger: the application's two wands, at the record
     the era boots over -- where [riscv_client_name] IS the counter the
     ledger was born with *)
  assert (Hperm : forall (HR : riscvGS Σ) (GEN : GenId) (γ : uart_names),
      (exists (Hinv : invGS Σ) (γgen γstart γreg γd γsw γobs γcl : gname)
              (T : list mobs),
         riscv_fixedGS =
           boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
             (P_fs_named γd XV6_DISK_BYTES γsw γreg γstart cov
                (FsImg.sb_logstart sb))
             γobs T (obs_ledger_at (app_R A γcl) γobs) γcl) ->
      ⊢ obs_inv -∗ uart_obs_permit γ).
  { intros HRg GEN γ (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Gcl & GT & Heq).
    refine (uart_obs_permit_ledger (app_R A riscv_client_name) γ (HRt _) _
              (Htx HRg γ) (Hrx HRg γ)).
    rewrite Heq. reflexivity. }
  exact (xv6_power_adequacy_gen Σ g sb nib cov
           (app_names A) (app_pred A) (app_lend A) Hlend Happ_boot Happ_auto
           (fun γobs γcl => obs_ledger_at (app_R A γcl) γobs)
           (fun γobs γcl =>
              obs_ledger_at_alloc_client (app_R A γcl) γobs γcl (HR0 γcl))
           (fun γd γobs γcl =>
              obs_ledger_at_step XV6_DISK_BYTES (app_R A γcl) (HRt γcl) (Hpow γcl)
                γd γobs)
           Hperm (app_phi A) Hphi Hgen0 Hpow0 Himg).
Qed.

(* ---------------------------------------------------------------------- *)
(* THE GENERIC APPLICATION PAYS EVERYTHING: the four obligations that       *)
(* mention its data, each in one line.  [xv6_trace_adequacy] is the record  *)
(* at these with a client's ledger in place of [emp].                       *)
(* ---------------------------------------------------------------------- *)
Section AppTriv.
  Context {Σ : gFunctors} `{!riscvGpreS Σ}.

  Lemma app_triv_boot (γcl : gname) (S : fs_state_rec) (dk : Z -> bv 8) :
    ⊢ app_lend (app_triv Σ) γcl dk -∗
      |==> ∃ r : app_names (app_triv Σ),
             app_pred (app_triv Σ) γcl r (abs_view (fss_inodes S)).
  Proof.
    iIntros "_". iModIntro. cbn [app_triv app_names app_pred].
    iExists (). iPureIntro. exact Logic.I.
  Qed.

  Lemma app_triv_auto (γcl : gname) (r : app_names (app_triv Σ)) :
    ⊢ app_auto_raw γcl (app_pred (app_triv Σ)) r.
  Proof.
    cbn [app_triv app_pred]. apply app_auto_raw_triv.
    intros f r' av. reflexivity.
  Qed.

  Lemma app_triv_R0 (γcl : gname) :
    mono_nat_auth_own γcl 1 0%nat ⊢ |==> app_R (app_triv Σ) γcl [].
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
           ltac:(intros γcl h; cbn [app_triv app_R]; apply _)
           app_triv_R0
           ltac:(intros γcl h on dk _; cbn [app_triv app_R]; iIntros "_"; by iModIntro)
           ltac:(intros HR γ; cbn [app_triv app_R];
                 iIntros "!>" (h b u u') "_ _ _ _ Hg _"; iModIntro; by iFrame "Hg")
           ltac:(intros HR γ; cbn [app_triv app_R];
                 iIntros "!>" (h b u u') "_ _ Hg _"; iModIntro; by iFrame "Hg")
           ltac:(intros γd γsw γreg γst γcl dk; cbn [app_triv app_lend];
                 iIntros "HP"; iModIntro; iModIntro; by iFrame "HP")
           ltac:(intros γcl S D dk _ _; exact (app_triv_boot γcl S dk))
           app_triv_auto
           ltac:(intros Hinv γgen γstart γreg γd γsw γobs γcl T g' h;
                 iIntros "_ _ _ _ _"; iModIntro; iPureIntro; exact Logic.I)
           Hgen0 Hpow0 _ n κs t2 g2 Hn)).
  rewrite Hdisk. exact fsimg_image_wf.
Qed.
