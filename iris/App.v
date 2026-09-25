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
Require Import FsBootParams.  (* [XV6_DISK_BYTES], [fsimg_cov], [fsimg_nib] *)
Require Import CtxIdDefs.             (* [CurCtx]: the echo obligation's context *)
Require Import SpecConsoleintr.    (* [cons_echo_shift]: the echo obligation  *)
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
  (* ...AT THE ERA (lane CONS-IO milestone C): the boot resource is the
     era's, so it carries the era's NUMBER beside its instance. *)
  app_boot  : app_fixed -> nat -> app_names -> iProp Σ;
  (* the trace ledger, at the fixed part (section 4) *)
  app_R     : app_fixed -> list mobs -> iProp Σ;
  (* THE APPLICATION'S CONSOLE INTERFACE, as ONE field (redesign R4), and
     the machine's [RiscvPtsto.riscvF_app_iface] is set from it.  Its three
     components, spelled as projections below:

     [app_tag] -- THE INPUT TAG (app-echo.md lane L5): what the application
     claims of a byte the environment pushed, at the history it arrived at.
     PERSISTENT, because the UART's receive column keeps one per queued byte
     and every reader copies it out.

     [app_kill] -- THE KILL CREDENTIAL (lane KILL-PAY, K1): what the
     application charges for a kill.  A kill is legal, and every party it
     touches -- the killer, the killed slot's public payload, the trap that
     observes [p->killed], the -1 the process exits with, the -1 a console
     read returns -- is handed this, so a verified continuation goes GENERIC
     where a kill could have happened instead of being refuted.  PERSISTENT
     and BOUGHT BY THE SUPPLY ([al_kill]), which is what lets the kernel
     charge the kill price at a trap it cannot rule out without charging any
     verified program.  For echo it is the TAINT; [True] for an application
     that puts no price on a kill.

     [app_cons] -- THE CONSOLE CLAIM (redesign R2/R3): what the application
     claims of the whole console boundary -- the bytes the UART has
     accepted, the accepted-input log, what a process has been given, and
     the arm consoleintr has in progress.  Read against an input-history
     prefix of the run.  A RESOURCE and not a [Prop], because a pure
     predicate cannot say WHO may write and the console echo's shift is then
     unprovable against an impostor's byte.  THE CONSOLE'S ONLY: the board
     has two 16550s and by the owner's ruling the kernel's own port (printk,
     panic) is unconstrained, so the UART invariant indexes for us
     ([WpUart.chist_at] is this at [Uart0] and [emp] at [Uart1]).  INDEXED
     BY THE ERA NUMBER (lane CONS-IO milestone C), because a process of a
     dead era keeps its linear writer's token inside that era's closed
     invariants and an era-agnostic link would let such a stale writer pay
     the CURRENT era's claim.  ITS FOUNDING IS THE APPLICATION'S OWN, AT THE
     POWER-ON STEP (see [Hpow] below) and not the transport's: a transport
     is a [□] over a bupd that returns its own input, so a founding
     derivable from it is derivable unboundedly.

     THE THREE TIMELESSNESS/PERSISTENCE INSTANCES RIDE THE INTERFACE, where
     they were five obligations of the theorem below. *)
  app_ifc   : app_fixed -> app_iface Σ;
  (* THE ERA'S CONSOLE TURN (app-echo.md, "E5 -- THE APPLICATION CLAIM",
     lane CONS-IO milestone F): what <init> is handed at the era's boot,
     beside [app_boot].  The kernel neither reads it nor mints it: [Hpow]'s
     power-on arm yields it once per era, the boot carries it
     ([RiscvAdequacy.power_boot_res] -> [Hinit_boot] ->
     [UInitKernel.init_boot_pay] -> [UkInitMain.wp_kinit_start]) and <init>
     holds it.  It is the application's own resource, so it can be the
     linear right to speak first on the console -- which is exactly what an
     echo discipline needs and what nothing per-era can say by itself. *)
  app_turn  : app_fixed -> nat -> iProp Σ;
  (* the conclusion, over the operational state and the run's trace *)
  app_phi   : gstate -> list mobs -> Prop;
}.
Arguments MkApp {Σ} _ _ _ _ _ _ _ _ _.
Arguments app_fixed {Σ} _. Arguments app_cl {Σ} _ _.
Arguments app_names {Σ} _. Arguments app_pred {Σ} _ _ _ _.
Arguments app_boot {Σ} _ _ _ _.
Arguments app_R {Σ} _ _ _. Arguments app_ifc {Σ} _ _.
Arguments app_turn {Σ} _ _ _.

(* the interface's three components, as projections: every site that named
   a field still names one, and the record carries ONE thing. *)
Definition app_tag {Σ} (A : xv6_app Σ) (c : app_fixed A) : list mobs -> iProp Σ :=
  ai_tag (app_ifc A c).
Definition app_kill {Σ} (A : xv6_app Σ) (c : app_fixed A) : iProp Σ :=
  ai_kill (app_ifc A c).
Definition app_cons {Σ} (A : xv6_app Σ) (c : app_fixed A) :
    nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ :=
  ai_cons (app_ifc A c).

Global Instance app_tag_persistent {Σ} (A : xv6_app Σ) c h :
  Persistent (app_tag A c h).
Proof. rewrite /app_tag. apply ai_tag_persistent. Qed.
Global Instance app_tag_timeless {Σ} (A : xv6_app Σ) c h :
  Timeless (app_tag A c h).
Proof. rewrite /app_tag. apply ai_tag_timeless. Qed.
Global Instance app_kill_persistent {Σ} (A : xv6_app Σ) c :
  Persistent (app_kill A c).
Proof. rewrite /app_kill. apply ai_kill_persistent. Qed.
Global Instance app_kill_timeless {Σ} (A : xv6_app Σ) c :
  Timeless (app_kill A c).
Proof. rewrite /app_kill. apply ai_kill_timeless. Qed.
Global Instance app_cons_timeless {Σ} (A : xv6_app Σ) c k h H :
  Timeless (app_cons A c k h H).
Proof. rewrite /app_cons. apply ai_cons_timeless. Qed.
Arguments app_phi {Σ} _ _ _.

(* THE GENERIC APPLICATION: no fixed part, nothing claimed, nothing read *)
Definition app_triv (Σ : gFunctors) : xv6_app Σ :=

  MkApp unit (fun _ => True%I) unit (fun _ _ _ => True%I) (fun _ _ _ => emp%I)
        (fun _ _ => emp%I)
        (* the console interface: a tag that says nothing, no price on a
           kill, nothing claimed of the console (redesign R2/R4) *)
        (fun _ => app_iface_triv Σ)
        (* the era's turn: the generic application has no console
           discipline, so it is [emp] (lane CONS-IO F) *)
        (fun _ _ => emp%I)
        (fun _ _ => True).

(* ====================================================================== *)
(*  WHAT AN APPLICATION OWES (post-qed-redesign §3.2, R4).                 *)
(*                                                                        *)
(*  The record above is DATA -- the predicates and the interface an        *)
(*  application chooses.  These are the LAWS about that data, and making   *)
(*  them a class is what turns -- this application pays some obligations   *)
(*  and not others -- from a fact about a [Theorem]'s argument list into a *)
(*  DEFINITION: an application with an instance may use the theorem, one   *)
(*  without cannot, and a partial application ([AppTree], whose first      *)
(*  process's bundle is still open) simply has no instance yet.            *)
(*                                                                        *)
(*  THE TWO LAWS THAT ARE NOT HERE are the two that are about an IMAGE and *)
(*  not about the application: [Happ_init], the era-0 claim at the boot    *)
(*  image's own abstract state, and [Hphi], the conclusion read off the    *)
(*  ledger at the run's coverage set.  Echo's era-0 claim holds at the     *)
(*  LITERAL image and nowhere else ([AppEcho.echo_Happ_init] takes         *)
(*  [fs_blocks … = fsimg_P], [sb = fsimg_sb], [cov = fsimg_cov]), so a     *)
(*  field quantified over every image would be FALSE for it.  They stay    *)
(*  arguments of the theorem, where the image is in scope.                 *)
(* ====================================================================== *)
Section AppLaws.
Context {Σ : gFunctors}.
Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
          !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
Context `{!ufdG Σ}.

Class xv6_app_laws (A : xv6_app Σ) := MkAppLaws {
  al_birth : ⊢ |==> ∃ c : app_fixed A, app_cl A c;
  al_Rt : forall (c : app_fixed A) (h : list mobs), Timeless (app_R A c h);
  al_kill : forall (c : app_fixed A) (r : app_names A),
       AppInv.app_sup_raw (app_pred A c) r ⊢ □ app_kill A c;
  al_sup : forall (c : app_fixed A) (r : app_names A),
       AppInv.app_sup_raw (app_pred A c) r
         ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
                (ev : ConsLog.cons_ev),
                app_cons A c k h H ==∗
                app_cons A c k h (ConsLog.cons_step H ev));
  al_R0 : forall c : app_fixed A, app_cl A c ⊢ |==> app_R A c [];
  al_pow : forall (c : app_fixed A) (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ app_R A c h ==∗
         app_R A c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
         (if on then emp
          else app_cons A c (S (obs_boots h)) []
                 (LogEntryDefs.MkCH [] [] [] None) ∗
               (* ...AND THE ERA'S TURN (lane CONS-IO milestone F).  The
                  same arm and the same reason: this is the one step of the
                  machine that runs the application's ledger exactly once
                  per era, so it is the only place a per-era LINEAR thing
                  can be minted, and the kernel carries it to <init>. *)
               app_turn A c (S (obs_boots h)));
  al_tx : forall (HR : riscvGS Σ) (GEN : GenId) (HF : fileG Σ)
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
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
              (ho : list mobs) (H : LogEntryDefs.cons_hist),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
              (* THE WIRE IS THE DRAINED SEQUENCE.  A clause of the UART
                 invariant's receive column since TX-TAG's rider
                 ([WpUart.uart_colE_wire_out]), handed over here because it
                 is what makes the accepted sequence an EXTENSION of the
                 wire: [uart_acc u = u_out u ++ u_tx u] and [u_wire u =
                 u_out u], so the wire is a prefix of [uart_acc u] and a
                 prefix-closed output claim transfers to it.  This closes
                 the premise TX-TAG left owed to E5. *)
              ⌜u_wire u = u_out u⌝ -∗
              (* ...AND THE ERA STAMP (lane CONS-IO milestone C): the era
                 this history belongs to is [S gen_id], which is the index
                 the two claims below are read at. *)
              ⌜obs_boots h = S gen_id⌝ -∗
              (* ...AND THE OUTPUT CLAIM at the drain (lane OUT-FUPD), at a
                 WITNESS HISTORY [ho] the console invariant holds a monotone
                 lower bound on -- so [ho] is a real prefix of the run's own
                 history, and the application lifts the claim from [ho] to
                 [h] by its own input-monotonicity.  Every accepted byte was
                 justified at its store by the writer's own view shift, so
                 this is where the kernel's output discipline reaches the
                 ledger -- and it is the only channel: the invariant carries
                 no application resource.  Conditional on the port, because
                 the kernel's own UART constrains nothing. *)
              ⌜ho `prefix_of` h⌝ -∗
              (* ...AND THE ACCEPTED BYTES ARE THE HISTORY'S OWN FIELD
                 (redesign R2).  It used to be an argument, because the
                 output claim was stated over them; the merged claim keeps
                 them inside, so the tie the drain needs is a premise. *)
              ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
              (* ...TAKEN LINEARLY AND GIVEN BACK.  The claim is the
                 application's own authority, so the ledger step reads it
                 against its own ledger and returns it to the invariant it
                 was borrowed from.  ONE claim at ONE witness, where there
                 were two at two. *)
              (if i is Uart0 then app_cons A c (S gen_id) ho H else emp) -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              (if i is Uart0 then app_cons A c (S gen_id) ho H else emp) ∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartOut i b])%list);
  al_rx : forall (HR : riscvGS Σ) (GEN : GenId) (HF : fileG Σ)
                  (c : app_fixed A) (r : app_names A)
                  (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              (* the arrival's era, on [Htx]'s mould (milestone C) *)
              ⌜obs_boots h = S gen_id⌝ -∗
              uart_ghosts γ u' -∗ app_R A c h
                ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ app_R A c (h ++ [ObsUartIn i b])%list ∗
              app_tag A c (h ++ [ObsUartIn i b])%list);
  al_xfer : forall (c : app_fixed A) (k : nat),
       ⊢ app_xfer_boot_raw (app_pred A c) (app_boot A c k);
  al_programs :
       forall (HR : riscvGS Σ) (GEN : GenId)
              (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
              (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
              (c : app_fixed A) (r : app_names A),
         @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r ->
         (* (b) THE RX-TAG EQUATION (lane APP-IFACE): the machine's ambient
            input-tag family IS this application's.  A FACT about the
            instance the theorem is taken at -- the [boot_fixedGS] literal
            below fixes the field to [app_tag A c] -- not an assumption
            about the world, and the premise a pinned <init> discharges
            [UConsLine.ush_tag_law] from. *)
         (* ...and THE INTERFACE EQUATION (redesign R4): the machine's
            ambient tag family, kill credential and console claim ARE this
            application's.  ONE equation where there were three -- a
            discharge that reads only one of them derives it by unfolding
            the projection. *)
         @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc A c ->
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
         ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot A c (S gen_id) r -∗
           (* ...and (a') THE ERA'S TURN beside it (lane CONS-IO milestone
              F): the application's own per-era credential, minted at the
              power-on step and carried here by the kernel.  <init> holds
              it; lane IO-LEAF spends it at the era's first banner byte. *)
           app_turn A c (S gen_id) -∗
           |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0;
  al_echo :
       forall (HR : riscvGS Σ) (c : app_fixed A),
         (* the shift reads the ambient tag family and the ambient console
            claim; ONE equation carries both (redesign R4) *)
         @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc A c ->

         (* AT EVERY ERA (milestone C): the shift is era-indexed and takes
            the era stamp on the byte's history, so the obligation is
            quantified over the generation as it is over the context. *)
         ⊢ ∀ (GEN : GenId) (XI : CurCtx),
             @SpecConsoleintr.cons_echo_shift Σ HR GEN XI;
}.
End AppLaws.

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
    (* ---- THE ELEVEN LAWS, AS ONE CLASS INSTANCE (redesign R4).  They
       were eleven binders here; an application that has them may use this
       theorem and one that does not cannot, which is what makes
       [xv6_app_laws] a definition rather than a reading of an argument
       list.  The two that are NOT in it are the two about an IMAGE:
       [Happ_init] and [Hphi] below. ---- *)
    `{AL : !xv6_app_laws A}
    (Happ_init : forall c : app_fixed A,
       ⊢ |==> ∃ r : app_names A,
           app_pred A c r (abs_view (fss_inodes (FsDurImg.img_state
              (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))))
    (* ...and THE FIRST PROCESS'S EXEC BUNDLE (ARM-c): the one thing the
       application owes the kernel about user execution.  Quantified over
       the era's ghost classes for the reason
       [SystemAdequacy.xv6_power_adequacy_gen]'s own [al_programs] gives --
       they are born by the boot mint -- and its paragraph carries the
       argument for why it is not the GAP-premise trap. *)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γsw γobs γhist : gname) (c : app_fixed A)
                   (T : list mobs) (g' : gstate) (h : list mobs),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (xv6_slot (app_names A) (app_pred A) cov (FsImg.sb_logstart sb)
                  γd γsw γreg γstart c)
               γobs T (obs_ledger_at (app_R A c) γobs) γhist
               (app_ifc A c)
               (app_fixed A) c) g' -∗
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
             (app_ifc A c)
             (app_fixed A) c
         /\ @file_app Σ HF = MkAppcfg (app_names A) (app_pred A c) r
         /\ (i = Uart0 -> FsCfg.fsc_uart = γ)) ->
      ⊢ obs_inv -∗ uart_obs_permit i γ).
  { intros HRg GEN HFi ri i γ
      (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Ghist & Gcl & GT & Heq & Happ & Huart).
    refine (uart_obs_permit_ledger i (app_R A Gcl) (app_tag A Gcl)
              (app_cons A Gcl) γ (al_Rt Gcl)
              _ _ _ (al_tx HRg GEN HFi Gcl ri i γ Happ Huart)
                    (al_rx HRg GEN HFi Gcl ri i γ Happ Huart));
      rewrite Heq; reflexivity. }
  exact (xv6_power_adequacy_gen Σ g sb nib cov
           (app_fixed A) (app_cl A) al_birth
           (app_names A) (app_pred A) (app_boot A)
           (app_ifc A)
           (app_turn A) al_xfer Happ_init
           al_kill
           al_sup al_programs
           al_echo
           (fun γobs c => obs_ledger_at (app_R A c) γobs)
           (fun γobs c =>
              obs_ledger_at_alloc_cl (app_R A c) γobs (app_cl A c) (al_R0 c))
           (fun γd γobs c =>
              obs_ledger_at_step XV6_DISK_BYTES (app_R A c) (al_Rt c)
                (app_cons A c) (app_turn A c)
                (al_pow c) γd γobs)
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
  Proof using .
    iModIntro. cbn [app_triv app_fixed app_cl].
    iExists (). iPureIntro. exact Logic.I.
  Qed.

  (* the transport: a predicate that holds of every view is its own copy,
     and the generic application hands its first process nothing *)
  Lemma app_triv_xfer (c : app_fixed (app_triv Σ)) (k : nat) :
    ⊢ app_xfer_boot_raw (app_pred (app_triv Σ) c) (app_boot (app_triv Σ) c k).
  Proof using .
    cbn [app_triv app_pred app_boot].
    apply app_xfer_boot_raw_triv. intros r av. reflexivity.
  Qed.

  (* era 0: the claim at any view, at the one instance *)
  Lemma app_triv_init (c : app_fixed (app_triv Σ)) (av : aview) :
    ⊢ |==> ∃ r : app_names (app_triv Σ), app_pred (app_triv Σ) c r av.
  Proof using .
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
    (* ...and the interface equation (redesign R4): one where there were
       three *)
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc (app_triv Σ) c ->
    (* ...and the generation-counter equation (lane APP-IFACE (b')), which
       the generic application takes and does not use *)
    @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->

    ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot (app_triv Σ) c (S gen_id) r -∗
      (* ...and the era's turn, likewise taken and not used *)
      app_turn (app_triv Σ) c (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0.
  Proof using .
    intros Heq Hiface _. iIntros "_ _ _". iModIntro.
    (* the rewrite goes BEFORE the [intros]: [r'] is typed at
       [app_names file_app], so rewriting under it is a dependent rewrite *)
    iApply init_boot_of_triv.
    - rewrite Heq. intros r' av.
      cbn [app_triv app_pred app_names]. reflexivity.
    - rewrite /app_taint Hiface.
      cbn [app_triv app_ifc app_iface_triv ai_kill]. reflexivity.
  Qed.

  Lemma app_triv_R0 (c : app_fixed (app_triv Σ)) :
    app_cl (app_triv Σ) c ⊢ |==> app_R (app_triv Σ) c [].
  Proof using . iIntros "_". by iModIntro. Qed.

  (* ---- THE GENERIC APPLICATION'S LAWS, as the instance (redesign R4).
         Eleven one-liners where the closed corollary below used to spell
         eleven [ltac:] blocks inside one [refine]. ---- *)
  Context `{!xv6G Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
            !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ} `{!ufdG Σ}.

  Global Instance app_triv_laws : xv6_app_laws (app_triv Σ).
  Proof using ufdG0.
    split.
    - exact app_triv_birth.
    - intros c h. cbn [app_triv app_R]. apply _.
    - intros c r.
      rewrite /app_kill. cbn [app_triv app_ifc app_iface_triv ai_kill].
      iIntros "_"; iModIntro; done.
    - (* ONE LICENCE (redesign R2): the generic claim is [emp], so every
         event on it is free *)
      intros c r.
      rewrite /app_cons. cbn [app_triv app_ifc app_iface_triv ai_cons].
      rewrite /cons_res_triv.
      iIntros "_ !>" (k h H ev) "_". by iModIntro.
    - exact app_triv_R0.
    - intros c h on dk _.
      rewrite /app_cons.
      cbn [app_triv app_R app_ifc app_iface_triv ai_cons app_turn].
      iIntros "_"; iModIntro; iSplitR; [done |].
      destruct on; by repeat iSplitR.
    - intros HR GEN HFi c r i γ _ _. cbn [app_triv app_R].
      iIntros "!>" (h b u u' ho H) "_ _ _ _ _ _ _ _ Ho Hg _"; iModIntro.
      iFrame "Ho Hg"; done.
    - intros HR GEN HFi c r i γ _ _. rewrite /app_tag.
      cbn [app_triv app_R app_ifc app_iface_triv ai_tag].
      iIntros "!>" (h b u u') "_ _ _ Hg _"; iModIntro.
      iFrame "Hg"; auto.
    - exact app_triv_xfer.
    - exact app_triv_init_boot.
    - (* the echo justifies itself at the trivial console claim *)
      intros HR c Hiface. iIntros (GEN XI).
      iApply (SpecConsoleintr.cons_echo_shift_triv (XI := XI)).
      rewrite /riscv_cons_res Hiface.
      cbn [app_triv app_ifc app_iface_triv ai_cons]. reflexivity.
  Qed.
End AppTriv.

(* ---------------------------------------------------------------------- *)
(* THE ARBITRARY APPLICATION, CLOSED: at the real image, powered off,       *)
(* never booted, every run is reducible.  The application's conclusion is   *)
(* [True], so the statement says reducibility and nothing else -- and       *)
(* DELIBERATELY names no [Σ]: stated as [app_phi (app_triv xv6Σ) g2 κs] it  *)
(* would unfold through the record at the functor list and put the whole    *)
(* ghost layer (the camera classes [xv6Σ] names) into the STATEMENT's       *)
(* trusted base, ~500 lines nobody has to read for “every run is           *)
(* reducible” (tools/tcb; measured 2026-09-05).  Every obligation of the    *)
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
  refine (proj1 (xv6_app_adequacy xv6Σ g fsimg_sb fsimg_nib fsimg_cov
           (app_triv xv6Σ)
           (* the eleven laws, as the instance (redesign R4) *)
           ltac:(intros c; exact (app_triv_init c _))
           ltac:(intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h;
                 iIntros "_ _ _ _ _"; iModIntro; iPureIntro; exact Logic.I)
           Hgen0 Hpow0 _ n κs t2 g2 Hn)).
  rewrite Hdisk. exact fsimg_image_wf.
Qed.
