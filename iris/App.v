(* App.v -- APPLICATIONS: the record, and the whole-system theorem at one.

   Design of record: claude-notes/design/applications.md and the
   application-side sections of claude-notes/projects/app-echo.md (the
   "app-instances.md" this header used to cite does not exist; its round
   and section numbers survive below as cross-references into those two).
   An application is a collection of user programs plus what it
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

   THE OBLIGATIONS ARE SIX FAMILIES, and that is all of them: [Hbirth],
   [Happ_xfer], [Happ_init], [Hinit_boot], the trace ledger's ([HR0],
   [HRt], [Hpow], [Htx], [Hrx]) and [Hphi].  There is no parked license:
   the BLANKET PROMISE that the claim survives every one-row move of the
   map is gone, because the AU fires' steps come out of the PROCESS's own
   deposit ([UexecSG.sbundle_at]); and there is no supply either -- the
   kernel mints no user-execution slot, so what the application owes about
   user execution is the FIRST PROCESS'S EXEC BUNDLE and nothing else.

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
   - [Hinit_boot] is the FIRST PROCESS'S EXEC BUNDLE
     ([InitBoot.init_boot_bundle]): kexec's caller-side bundle at "/init",
     whose SLOT PIECE answers at the key kexec builds.  forkret's boot arm
     runs that kexec between the first park and the first resume, so no
     slot the kernel could have minted survives it -- which is why this,
     and not a supply, is what the application owes about user execution.
     The generic application discharges it from the trivial mint
     ([SystemAdequacy.init_boot_of_triv]); a constraining application
     discharges it from its own pinned bundle at "/init".  Either way it
     is a discharged premise, not a gap (see [SystemAdequacy]'s
     [Hinit_boot]).
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
Require Import InitBoot.         (* [init_boot_bundle]: the first process's
                                    exec bundle, the application's one
                                    obligation about user execution *)
Require Import InodeInv.         (* [ROOTINO] *)
Require Import AppCfg.           (* [MkAppcfg]: the era's application record,
                                    which [Hinit_boot]'s equation names *)
Require Import AppInv.           (* [app_sup_raw]: the supply, at the raw
                                    gname *)
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import FsCfgBoot.
Require Import RiscvAdequacy.
Require Import FsCrash.
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
  (* WHAT THE ERA'S INSTANCE IS BORN WITH BESIDE ITS CLAIM (lane APP-IFACE
     item (a), review-echo-plan finding 6): the resource the FIRST PROCESS'S
     proof is handed at [Hinit_boot] -- for the echo application, the
     console-absence key /init carries from its first [open] to its [mknod].
     LINEAR, so it cannot live inside the claim (a resource borrowed from
     the claim has to go back) and cannot be persistent (then it would say
     nothing); its producer is therefore the TRANSPORT, which is where the
     era's instance is born ([Happ_boot]).  [emp] for an application that
     wants nothing. *)
  app_boot  : app_fixed -> app_names -> iProp Σ;
  (* the trace ledger, at the fixed part (section 4) *)
  app_R     : app_fixed -> list mobs -> iProp Σ;
  (* THE INPUT TAG (app-echo.md lane L5): what the application claims of a
     byte the environment pushed, at the history it arrived at.  Persistent
     (the obligation [Htagp] below), because the UART's receive column keeps
     one per queued byte and every reader copies it out.  It is the record's
     entry for the machine's ambient [RiscvPtsto.riscv_rx_tag]. *)
  app_tag   : app_fixed -> list mobs -> iProp Σ;
  (* the conclusion, over the operational state and the run's trace *)
  app_phi   : gstate -> list mobs -> Prop;
}.
Arguments MkApp {Σ} _ _ _ _ _ _ _ _.
Arguments app_fixed {Σ} _. Arguments app_cl {Σ} _ _.
Arguments app_names {Σ} _. Arguments app_pred {Σ} _ _ _ _.
Arguments app_boot {Σ} _ _ _.
Arguments app_R {Σ} _ _ _. Arguments app_tag {Σ} _ _ _.
Arguments app_phi {Σ} _ _ _.

(* THE GENERIC APPLICATION: no fixed part, nothing claimed, nothing read *)
Definition app_triv (Σ : gFunctors) : xv6_app Σ :=
  MkApp unit (fun _ => True%I) unit (fun _ _ _ => True%I) (fun _ _ => emp%I)
        (fun _ _ => emp%I) (fun _ _ => True%I) (fun _ _ => True).

(* ---------------------------------------------------------------------- *)
(* THE THEOREM.  [xv6_power_adequacy_gen] at the application: the birth    *)
(* step is [app_cl]'s, the trace slot is the ledger of [app_R] at the fixed *)
(* part, the lend is the FS's epoch beside [app_lend], the era's predicate  *)
(* is [app_pred] at the fixed part and the instance the boot obligation     *)
(* witnesses.                                                               *)
(* ---------------------------------------------------------------------- *)
Theorem xv6_app_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}
    `{!ufdG Σ}
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (A : xv6_app Σ)
    (* ---- THE BIRTH STEP (app-instances.md section 6 ruling 1): one value
       of the fixed part, with what [app_cl] says of it ---- *)
    (Hbirth : ⊢ |==> ∃ c : app_fixed A, app_cl A c)
    (* ---- the trace ledger's obligations ([xv6_trace_adequacy]'s, the
       birth step's yield received at the ledger's birth) ---- *)
    (HRt : forall (c : app_fixed A) (h : list mobs), Timeless (app_R A c h))
    (* the tag is copied out of the UART's receive column once per reader,
       so it has to be duplicable by construction *)
    (Htagp : forall (c : app_fixed A) (h : list mobs), Persistent (app_tag A c h))
    (* ...and timeless, because the receive column that files it lives in the
       UART invariant, whose body every device leaf strips a later off *)
    (Htagt : forall (c : app_fixed A) (h : list mobs), Timeless (app_tag A c h))
    (HR0 : forall c : app_fixed A, app_cl A c ⊢ |==> app_R A c [])
    (Hpow : forall (c : app_fixed A) (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ app_R A c h ==∗
         app_R A c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list)
    (* the two UART-arm wands, at any value of the fixed part: the era
       instance's [riscv_client] is the one the boot's record carries, and
       the record's client type is [app_fixed A] only at that literal *)
    (* THE ERA IDENTIFICATION (lane APP-IFACE item (c), review-echo-plan
       finding 3).  These two used to be quantified over an ARBITRARY
       [γ : uart_names], so the ledger could learn nothing about THE ERA's
       UART ghosts at an event -- and the whole output side rests on doing
       exactly that ([SystemUartAccepted.v]'s header, app-echo.md O4).  They
       are quantified over the ERA's [fileG] instead, with the two equations
       the boot HAS and hands over: the era's application record, and
       [fsc_uart] -- the [γ] every kernel-side UART fact of this era is
       stated at.  This is [Hinit_boot]'s own shape, and it is not a new
       assumption about the world: it NARROWS the wands' domain from every
       [γ] to the era's. *)
    (Htx : forall (HR : riscvGS Σ) `{HF : !fileG Σ}
                  (c : app_fixed A) (r : app_names A)
                  (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
       (* THE ERA IDENTIFICATION IS THE CONSOLE'S.  Only that port's ghosts
          are the era's [fsc_uart]; the other port has its own bundle and no
          kernel fact is stated at it, so the tie is conditional on which
          port the arm belongs to. *)
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       (* AT EVERY PORT.  The board has two 16550s and either may step, so
          the ledger owes an account of an event on EITHER -- an untagged
          obligation would let a byte on the kernel's port slip past the
          claim about the console's. *)
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartOut i b])%list))
    (Hrx : forall (HR : riscvGS Σ) `{HF : !fileG Σ}
                  (c : app_fixed A) (r : app_names A)
                  (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartIn i b])%list ∗
              app_tag A c (h ++ [ObsUartIn i b])%list))
    (* ---- the application's three obligations on its predicate
       (app-instances.md sections 1-3, round C): the TRANSPORT (its one
       durability obligation -- a copy of the claim at fresh instance names,
       under the later every crossing hands it over at), the ERA-0 claim
       at the image's own abstract state, and the supply ---- *)
    (* ...the TRANSPORT, which since lane APP-IFACE item (a) also hands the
       clone its own BOOT RESOURCE ([app_xfer_raw_of_boot] is the old
       obligation, and is what the commit's law and the era mint keep
       taking).  The transport is the producer because the era's instance is
       born there: the machine starts powered OFF, so every boot -- era 0's
       included -- founds its file system from the PowerOn arm's clone, and
       [Happ_init]'s instance never reaches one. *)
    (Happ_boot : forall c : app_fixed A,
       ⊢ app_xfer_boot_raw (app_pred A c) (app_boot A c))
    (Happ_init : forall c : app_fixed A,
       ⊢ |==> ∃ r : app_names A,
           app_pred A c r (abs_view (fss_inodes (FsDurImg.img_state
              (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))))
    (* ...and THE FIRST PROCESS'S EXEC BUNDLE (ARM-c): the one thing the
       application owes the kernel about user execution.  Quantified over
       the era's ghost classes for the reason
       [SystemAdequacy.xv6_power_adequacy_gen]'s own [Hinit_boot] gives --
       they are born by the boot mint -- and its paragraph carries the
       argument for why it is not the GAP-premise trap. *)
    (Hinit_boot :
       forall (HR : riscvGS Σ) (GEN : GenId)
              `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
                HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
              (c : app_fixed A) (r : app_names A),
         @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
         (* (b) THE RX-TAG EQUATION (lane APP-IFACE): the machine's ambient
            input-tag family IS this application's.  A FACT about the
            instance the theorem is taken at -- the [boot_fixedGS] literal
            below fixes the field to [app_tag A c] -- not an assumption
            about the world, and the premise a pinned <init> discharges
            [UConsLine.ush_tag_law] from. *)
         riscv_rx_tag = app_tag A c ->
         (* ...and (b') THE GENERATION-COUNTER EQUATION (lane APP-IFACE, the
            same pattern as the rx-tag one above).  The era's [A] is FIXED
            before [HR] exists, so the camera [A]'s own predicate carries
            for the taint counter is the PRE-structure's, while [AppInv]'s
            laws ABOUT that predicate are at the FIXED layer's.
            [RiscvAdequacy.boot_fixedGS] fills every anonymous class slot
            from [riscvGpreS] (its header: "All resolve from
            [riscvGpreS]"), so at the instance this theorem is taken at the
            two are the SAME TERM -- a fact about that instance, not an
            assumption about the world, and the premise that lets the
            record's predicate meet [AppInv]'s laws. *)
         @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
         (* ...and (a) THE BOOT RESOURCE, LINEARLY, at the instance the
            record equation names *)
         ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot A c r -∗
           |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0)
    (* ---- the conclusion's proof, at the end of the run: it holds the
       COMPOSITE crash slot ([SystemAdequacy.xv6_slot]: the file system's
       record beside the application's durable claim at the same snapshot
       name) and the ledger side by side ---- *)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γsw γobs γhist : gname) (c : app_fixed A)
                   (T : list mobs) (g' : gstate) (h : list mobs),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
                  γd γsw γreg γstart c)
               γobs T (obs_ledger_at (app_R A c) γobs) γhist
               (app_tag A c) (Htagp c) (Htagt c) (app_fixed A) c) g' -∗
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
  assert (Hperm : forall (HR : riscvGS Σ) (GEN : GenId) (HF : fileG Σ)
                         (r : app_names A) (i : uart_id) (γ : uart_names),
      (exists (Hinv : invGS Σ) (γgen γstart γreg γd γsw γobs γhist : gname)
              (c : app_fixed A) (T : list mobs),
         riscv_fixedGS =
           boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
             (xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
                γd γsw γreg γstart c)
             γobs T (obs_ledger_at (app_R A c) γobs) γhist
             (app_tag A c) (Htagp c) (Htagt c) (app_fixed A) c
         /\ @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r
         /\ (i = Uart0 -> FsCfg.fsc_uart = γ)) ->
      ⊢ obs_inv -∗ uart_obs_permit i γ).
  { intros HRg GEN HFi ri i γ
      (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Ghist & Gcl & GT & Heq & Happ & Huart).
    refine (uart_obs_permit_ledger i (app_R A Gcl) (app_tag A Gcl) γ (HRt Gcl)
              _ _ (Htx HRg HFi Gcl ri i γ Happ Huart)
                  (Hrx HRg HFi Gcl ri i γ Happ Huart));
      rewrite Heq; reflexivity. }
  exact (xv6_power_adequacy_gen Σ g sb nib cov
           (app_fixed A) (app_cl A) Hbirth
           (app_names A) (app_pred A) (app_boot A) Happ_boot Happ_init
           (app_tag A) Htagp Htagt Hinit_boot
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

  (* the transport: a predicate that holds of every view is its own copy,
     and the generic application hands its first process nothing *)
  Lemma app_triv_xfer (c : app_fixed (app_triv Σ)) :
    ⊢ app_xfer_boot_raw (app_pred (app_triv Σ) c) (app_boot (app_triv Σ) c).
  Proof.
    cbn [app_triv app_pred app_boot]. apply app_xfer_boot_raw_triv.
    intros r av. reflexivity.
  Qed.

  (* era 0: the claim at any view, at the one instance *)
  Lemma app_triv_init (c : app_fixed (app_triv Σ)) (av : aview) :
    ⊢ |==> ∃ r : app_names (app_triv Σ), app_pred (app_triv Σ) c r av.
  Proof.
    iModIntro. cbn [app_triv app_names app_pred].
    iExists (). iPureIntro. exact Logic.I.
  Qed.

  (* THE FIRST PROCESS'S EXEC BUNDLE: the generic application's predicate
     IS [True], so its supply is free ([AppInv.app_sup_raw_triv]) and the
     bundle is the trivial one over the generic mint
     ([SystemAdequacy.init_boot_of_triv]) -- every hop says yes, the
     observation hands the authority back, and both slot wands answer with
     the user-execution WP every key admits. *)
  (* the two classes the section does not carry: the bundle is an [iProp]
     over the kernel's ghost state, and its slot piece is [UexecRet.uslot],
     which reads the descriptor class *)
  Lemma app_triv_init_boot
      `{HX : !xv6G Σ, HU : !ufdG Σ}
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (c : app_fixed (app_triv Σ)) (r : app_names (app_triv Σ)) :
    @file_app Σ HF
      = MkAppcfg (app_names (app_triv Σ)) (app_pred (app_triv Σ) c) r ->
    riscv_rx_tag = app_tag (app_triv Σ) c ->
    (* ...and the generation-counter equation (lane APP-IFACE (b')), which
       the generic application takes and does not use *)
    @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
    ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot (app_triv Σ) c r -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof.
    intros Heq _ _. iIntros "_ _". iModIntro.
    (* the rewrite goes BEFORE the [intros]: [r'] is typed at
       [app_names file_app], so rewriting under it is a dependent rewrite *)
    iApply init_boot_of_triv. rewrite Heq. intros r' av.
    cbn [app_triv app_pred app_names]. reflexivity.
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
           ltac:(intros c h; cbn [app_triv app_tag]; apply _)
           ltac:(intros c h; cbn [app_triv app_tag]; apply _)
           app_triv_R0
           ltac:(intros c h on dk _; cbn [app_triv app_R]; iIntros "_"; by iModIntro)
           ltac:(intros HR HFi c r i γ _ _; cbn [app_triv app_R];
                 iIntros "!>" (h b u u') "_ _ _ _ Hg _"; iModIntro; by iFrame "Hg")
           ltac:(intros HR HFi c r i γ _ _; cbn [app_triv app_R app_tag];
                 iIntros "!>" (h b u u') "_ _ Hg _"; iModIntro;
                 iFrame "Hg"; auto)
           app_triv_xfer
           ltac:(intros c; exact (app_triv_init c _))
           app_triv_init_boot
           ltac:(intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h;
                 iIntros "_ _ _ _ _"; iModIntro; iPureIntro; exact Logic.I)
           Hgen0 Hpow0 _ n κs t2 g2 Hn)).
  rewrite Hdisk. exact fsimg_image_wf.
Qed.
