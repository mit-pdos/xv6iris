(* ====================================================================== *)
(* SystemAdequacy.v -- THE SYSTEM THEOREM.                                 *)
(*                                                                        *)
(* [xv6_power_adequacy]: a machine that starts POWERED OFF at generation 0  *)
(* and is then power-cycled forever never gets stuck.  Every configuration  *)
(* reachable from the one-thread pool [[PowerLoopE]] by ANY interleaving of *)
(* power cycles, hart steps and device steps is reducible -- and there is    *)
(* no Iris judgment, no ghost state and no hypothesis about the software    *)
(* anywhere in the statement.                                              *)
(*                                                                        *)
(* It is exactly three things composed:                                    *)
(*                                                                        *)
(*   [RiscvAdequacy.riscv_power_adequacy]  -- the power thread + Iris        *)
(*                                            adequacy, over an arbitrary   *)
(*                                            per-era boot entailment;      *)
(*   [BootShared.boot_shared_alloc]        -- that entailment's allocation,  *)
(*                                            ONCE per era;                 *)
(*   [BootChain.boot_hart_primary] /       -- one hart's whole life, the arm *)
(*   [BootChain.boot_hart_secondary]          chosen by its index;           *)
(*                                                                        *)
(* plus the three device-loop WPs, exactly as [riscv_device_adequacy] does. *)
(*                                                                        *)
(* THE DISPATCH LIVES HERE, deliberately (BootChain §5's note): a           *)
(* [boot_hart] that selected the arm itself would have to take the boot     *)
(* supply for EVERY hart, or take it under an [if decide ... then ... else  *)
(* True].  This file holds the supply for hart 0 only, peels [enum CPU] at  *)
(* its head, and applies §5 there and §4 to the tail -- where every element *)
(* is an [FS], hence provably nonzero.                                     *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang ObsTrace RiscvPtsto.
(* durable-disk 2b-A / B3: the era's two file-system-state capacity classes.
   Required EARLY so the later imports shadow [FsState]'s four colliding
   exports again ([fs_view], [link_auth], [byte_range], [blk_owned]); the
   IMPORT is what makes [fsLinkG]/[fsTopG]'s instance fields active, which a
   bare [Require] does not. *)
Require Import FsState.
Require FsAbsDefs.          (* [anode], [abs_view]: the application's claim is over the view
                               (Require, not Import: it re-exports FsState) *)
Require Import AppDur.      (* [app_dur_raw]: the application's DURABLE claim beside the snapshot,
                               tied by the guest half of its map (app-instances.md round C) *)
Require Import InitBoot.    (* [init_boot_bundle]: the first process's exec bundle,
                               which the theorem's [Hinit_boot] delivers *)
Require Import InodeInv.    (* [ROOTINO]: the first process's working directory *)
Require Import UexecExecMint.  (* [uslot_mint]: the GENERIC application's discharge *)
Require Import LinkUserinit.   (* [UG.uexec_wp_gen]: ...and the [box] it eliminates *)
Require Import AppInv.      (* [app_sup_raw]: the application's supply, at the raw gname,
                               beside its boot obligation (applications.md) *)
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import AppCfg.      (* [MkAppcfg]: the boot builds the application's record for the mint *)
Require Import WpUart.
Require Import BootConfig.
Require Import BootChain BootShared.
Require Import SpecConsoleintr.   (* [cons_echo_shift]: the echo obligation *)
Require Import FsCfgBoot.   (* [fs_boot_image_wf], moved down at stage (f) *)
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import FsDurSnap.   (* [snap_ok] -- the theorem's durability claim *)
Require Import FsBootParams. (* [XV6_DISK_BYTES], [fs_boot_pure],
                                [fsimg_cov], [fsimg_nib] -- the pure
                                parameters, moved out of this file  *)
Require Import FsDurImg.    (* [img_snap_ok] / [img_P_dur_alloc]: era 0's own
                               epoch, the ONE value-first allocation left *)
Require Import FirstTok.    (* [fs_extent_of_image] *)
(* THE LITERAL mkfs IMAGE.  Both halves, since the corollary at the bottom
   of this file discharges every image hypothesis: [FsImgDisk] is the
   machine-facing half ([fsimg_dk], its block view, one recovery fact) and
   [FsImgCheck] is what the image MEANS as a file system.  [FsImgCheck] is
   ~120 s of [vm_compute] and used to be kept off this file's cone for that
   reason ([FsAdequacyImg.v], retired); it costs nothing on the critical
   path, because the era-0 pin files ([FsInitPin] / [FsInitPinBoot] /
   [FsShPin]) already require it, so it is built long before this file's
   own dependencies are ready. *)
Require Import FsImgDisk.
Require Import FsImgCheck.
Require Import VirtioModel.  (* [v_disk] *)
Require Import IrefSlots.
Require Import LogDefs.   (* [log_mirror_born] -- row (B) of the fsinit bundle *)
Require Import Xv6Cameras.  (* its record constructors *)
Require Import FsImg.  (* [fs_sb]: the era-wide image hypothesis's shape.  No
   computation and no literal image comes with it -- [FsImgCheck.v] is what
   instantiates the sweeps, and it is NOT on this file's cone. *)
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.   (* [own_context_boot]: the per-hart thread-of-control mint *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(* 1. Peeling the hart enumeration at its head.                            *)
(*                                                                        *)
(* [enum CPU] IS [0%fin :: FS <$> enum (fin 7)] by conversion (stdpp's      *)
(* [fin_enum]), so the boot hart and the seven secondaries separate with no *)
(* case analysis on a hart variable anywhere -- and every element of the    *)
(* tail is syntactically an [FS], which is what discharges the secondary    *)
(* arm's [fin_to_nat c <> 0] premise.                                      *)
(* ---------------------------------------------------------------------- *)

Require Import UserFd.   (* [ufdΣ]/[ufdG] *)
Lemma cpu_enum_cons : (enum CPU : list CPU) = 0%fin :: (FS <$> enum (fin 7)).
Proof. reflexivity. Qed.

Lemma big_sepL_cpu_split {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ list] c ∈ enum CPU, Φ c)
  ⊣⊢ Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c)).
Proof.
  rewrite {1}cpu_enum_cons big_sepL_cons big_sepL_fmap. done.
Qed.

(* the two DIRECTIONS, spelled separately.  [iApply]/[iDestruct] on a [⊣⊢]
   picks a direction of its own accord and the resulting list is not the one
   either side of the goal has, so the failure reads as an unapplicable
   [big_sepL_impl] several lines later. *)
Lemma big_sepL_cpu_peel {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ list] c ∈ enum CPU, Φ c)
  ⊢ Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c)).
Proof. apply bi.equiv_entails_1_1, big_sepL_cpu_split. Qed.

Lemma big_sepL_cpu_glue {PROP : bi} (Φ : CPU -> PROP) :
  Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c))
  ⊢ [∗ list] c ∈ enum CPU, Φ c.
Proof. apply bi.equiv_entails_1_2, big_sepL_cpu_split. Qed.

Lemma fin_FS_nz (c : fin 7) : (fin_to_nat (FS c) <> 0)%nat.
Proof. cbn. lia. Qed.

Lemma fin_0_z : (fin_to_nat (0%fin : CPU) = 0)%nat.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ONE ERA'S BOOT: the entailment [riscv_power_adequacy] asks for.       *)
(* ---------------------------------------------------------------------- *)

(* [XV6_DISK_BYTES] -- the boot mint's range -- and [fs_boot_pure] -- the   *)
(* pure projection of the crash predicate -- MOVED DOWN to                 *)
(* [FsBootParams.v] (required above).  Both are stated over [FsCrash] /     *)
(* [FsDurSnap] vocabulary alone, so [FsDurSyscall] and the pin files can    *)
(* name them without importing the adequacy cone.                          *)

(* THE THREE ERA-INDEPENDENT FACTS a boot needs about the COVERED RANGE
   (durable-disk lane E-himg), read off the initial machine's image.

   [cov] and the crash predicate's [logstart] are parameters of the whole
   execution -- one invariant, allocated once into the fixed layer -- so
   they are the same at every era, and a PER-ERA snapshot is a fact about
   [S] and [D] alone and therefore cannot mention either.  Everything else a
   later boot needs about its disk comes off [fs_boot_pure]; these three are
   what remains, and they cost nothing because they are already conjuncts
   (or immediate readings) of the image hypothesis at [g].

   [logstart = 2] is what identifies the crash predicate's log start with
   the era's own ([FsImg.sbo_logstart] pins the snapshot's superblock at the
   same 2), and the log region's coverage is [1 <= b < data_start -> b ∈ cov]
   read at the log's own blocks. *)
Lemma cov_facts_of_image (dk : Z -> bv 8) (ndisk : nat)
    (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z) :
  fs_boot_image_wf dk ndisk sb nib cov ->
  FsBoot.fs_cov_in cov ndisk
  /\ log_region_set (FsImg.sb_logstart sb) ⊆ cov
  /\ FsImg.sb_logstart sb = 2.
Proof.
  intros (Hwf & _ & _ & _ & _ & _ & Hcovin & Hcovmeta & _).
  pose proof (FsImg.fsimg_wf_sb _ _ Hwf) as Hsb.
  pose proof (FsImg.sbo_logstart _ Hsb) as Hls.
  pose proof (FsImg.sbo_nlog _ Hsb) as Hnl.
  pose proof (FsImg.sbo_inodestart _ Hsb) as Hist.
  pose proof (FsImg.sbo_bmapstart _ Hsb) as Hbms.
  pose proof (FsImg.sbo_ninodes _ Hsb) as Hni. unfold FsImg.ROOTINO in Hni.
  assert (Hdv : 0 <= FsImg.sb_ninodes sb / 16) by (apply Z.div_pos; lia).
  split; [exact Hcovin |].
  split; [| exact Hls].
  apply elem_of_subseteq. intros b Hb.
  pose proof (log_region_range _ _ Hb) as Hbb.
  unfold LOGBLOCKS in Hbb. apply Hcovmeta.
  unfold FsImg.fs_data_start. lia.
Qed.

(* ...AND THE SAME FACT AS A TRACE HOOK.  [fs_boot_pure] above is delivered
   INTO each boot, by [riscv_power_adequacy]'s [Hproj] channel.  This is the
   shape that exports it OUT of the whole execution: the trace obligation
   [Hphi], at the crash predicate this file always uses.

   IT IS THE SAME LEMMA.  [FsCrash.P_fs_project] is what discharges [Hproj];
   [RiscvAdequacy.disk_proj_trace] is the adapter that promotes a
   [Hproj]-shaped projection to a [Hphi]-shaped one, by pulling the durable
   disk's auth out of [state_interp] ([RiscvAdequacy.power_interp_disk_auth]
   -- a FIXED conjunct, so it is there at every state of the trace, powered
   on or off).  Nothing new is proved and nothing new is assumed. *)
(* ---------------------------------------------------------------------- *)
(* THE BOOT RESOURCE'S CHANNEL (review-echo-plan finding 6, lane APP-IFACE  *)
(* item (a)).  What the FIRST PROCESS'S proof needs beside the era's claim  *)
(* -- for the echo application, the console-absence key its /init carries   *)
(* from its first [open] to its [mknod] -- is EXCLUSIVE, so it cannot be    *)
(* read out of the claim (a linear resource inside the claim has to go back *)
(* in) and it cannot be persistent (then it would say nothing).  It has to  *)
(* be MINTED WHERE THE ERA'S INSTANCE IS BORN, beside the fresh claim, and  *)
(* the era's instance is born by the TRANSPORT: the machine starts powered  *)
(* off, so EVERY boot -- era 0's included -- takes its claim off            *)
(* [riscv_power_adequacy]'s PowerOn arm, which clones the crash slot's      *)
(* claim at fresh names.  [Happ_init]'s instance never reaches a boot.      *)
(*                                                                        *)
(* So the transport is the producer: [app_xfer_boot_raw A B] is             *)
(* [AppInv.app_xfer_raw A] with the clone's own [B r'] beside it.  It is    *)
(* STRICTLY STRONGER ([app_xfer_raw_of_boot]), so the commit's law and the  *)
(* era mint keep taking the old one and only the PowerOn arm reads the new  *)
(* conjunct.                                                               *)
(* ---------------------------------------------------------------------- *)
(* ...AND IT NO LONGER FOUNDS THE ERA'S PORT CLAIMS (lane CONS-IO milestone
   E, e5-design REVISION 8).  Lanes OUT-FUPD and CONS-IO put the two claims
   here, at the clone: [O [] []] and [I [] [] []] beside [B r'].  That was
   unsound as a discipline and ECHO-OUT part 2 hit the wall.  This is a [□]
   over a bupd whose ONLY input [▷ A r av] it hands straight back, so
   [O [] []] is derivable from nothing, unboundedly and at every era -- the
   founded arm of a claim reached this way has to be PURE, and then no
   ledger fact can refute a claim "reset" to it.  The founding moved to the
   POWER-ON STEP ([App.Hpow]'s on-arm), where the application holds its
   own ledger and can mint a LINEAR per-era seed; the kernel carries the
   yield from there to the boot on [RiscvAdequacy.power_boot_res].  So this
   is back to what lane APP-IFACE left: the clone and its boot resource. *)
Definition app_xfer_boot_raw {Σ : gFunctors} {N : Type}
    (A : N -> FsAbsDefs.aview -> iProp Σ) (B : N -> iProp Σ) : iProp Σ :=
  (□ (∀ (r : N) (av : FsAbsDefs.aview),
        ▷ A r av ==∗ ▷ A r av ∗
        ∃ r' : N, ▷ A r' av ∗ B r'))%I.

Global Instance app_xfer_boot_raw_persistent {Σ} {N}
    (A : N -> FsAbsDefs.aview -> iProp Σ) (B : N -> iProp Σ) :
  Persistent (app_xfer_boot_raw A B).
Proof. rewrite /app_xfer_boot_raw. apply _. Qed.

Lemma app_xfer_raw_of_boot {Σ} {N} (A : N -> FsAbsDefs.aview -> iProp Σ)
    (B : N -> iProp Σ) :
  (⊢ app_xfer_boot_raw A B) -> ⊢ AppInv.app_xfer_raw A.
Proof.
  intros Hb. rewrite /AppInv.app_xfer_raw.
  iPoseProof Hb as "#H". iEval (rewrite /app_xfer_boot_raw) in "H".
  iIntros "!>" (r av) "HA".
  iMod ("H" with "HA") as "[HA Hn]". iDestruct "Hn" as (r') "[HA' _]".
  iModIntro. iFrame "HA". iExists r'. iExact "HA'".
Qed.

(* the generic application's: nothing claimed and nothing handed over *)
Lemma app_xfer_boot_raw_triv {Σ} {N} (A : N -> FsAbsDefs.aview -> iProp Σ) :
  (forall r av, A r av ⊣⊢ True) ->
  ⊢ app_xfer_boot_raw A (fun _ => emp%I).
Proof.
  intros Htriv. rewrite /app_xfer_boot_raw. iIntros "!>" (r av) "H".
  iModIntro. iSplitL "H"; [iExact "H" |]. iExists r.
  iSplitL; [| done].
  iNext. iApply (bi.equiv_entails_1_2 _ _ (Htriv r av)).
  iPureIntro. exact Logic.I.
Qed.

(* THE TRIVIAL TRACE SLOT'S FOUNDING (lane CONS-IO milestone E).  Since the
   era's console claim is founded at the POWER-ON step, every client of
   [RiscvAdequacy.obs_pred_at_step] -- the slot that keeps no ledger -- owes
   it at the empty run.  At the GENERIC application it is [emp]
   ([RiscvPtsto.cons_res_triv]), so it is free; it is a lemma rather than an
   inline tactic because the call site is inside a [refine] whose implicit
   [Σ] is not yet resolved when an [ltac:] would run. *)
(* [out_res_triv_founded] and [in_res_triv_founded] lived here. *)

(* ...and the ONE claim's (redesign R2), which is what the founding asks
   for now: the empty console history at the empty run. *)
Lemma cons_res_triv_founded (Σ : gFunctors) (k : nat) :
  ⊢ @cons_res_triv Σ k [] (LogEntryDefs.MkCH [] [] [] None).
Proof. rewrite /cons_res_triv. iEmpIntro. Qed.

(* ...and the ECHO WINDOW TOKEN's (lane CONS-IO milestone F), on the same
   mould: at the generic application the token is [emp], so the era's mint
   costs the trivial slot nothing.  The turn is discharged inline at [emp]
   ([bi.emp_valid] is [iEmpIntro] there too). *)
(* [win_res_triv_founded] lived here. *)

Lemma turn_triv_founded (Σ : gFunctors) (k : nat) : ⊢ (emp : iProp Σ)%I.
Proof. iEmpIntro. Qed.

(* THE DURABLE CLAIM AT A NAMED INSTANCE.  [AppDur.app_dur_raw] closes the
   instance existentially, which is right for the SLOT (nothing outside it
   names the instance) and wrong for the LEND, whose boot resource is at
   the same [r] as the claim it travels with.  This is that predicate with
   [r] exposed; [app_dur_raw] is it with the existential put back. *)
Definition app_dur_at {Σ : gFunctors} `{!fsTopG Σ} {N : Type}
    (A : N -> FsAbsDefs.aview -> iProp Σ) (gt : gname) (r : N) : iProp Σ :=
  (∃ I : gmap Z FsNode.fs_node,
     ghost_map_auth gt (1/2) I ∗ A r (FsAbsDefs.abs_view I))%I.

Lemma app_dur_at_pack {Σ} `{!fsTopG Σ} {N}
    (A : N -> FsAbsDefs.aview -> iProp Σ) (gt : gname) (r : N)
    (I : gmap Z FsNode.fs_node) :
  ghost_map_auth gt (1/2) I -∗ ▷ A r (FsAbsDefs.abs_view I) -∗
  ▷ app_dur_at A gt r.
Proof.
  iIntros "Hh Hp". iNext. rewrite /app_dur_at. iExists I. iFrame "Hh Hp".
Qed.

Lemma app_dur_at_agree {Σ} `{!fsTopG Σ} {N}
    (A : N -> FsAbsDefs.aview -> iProp Σ) (gt : gname) (r : N)
    (q : Qp) (I : gmap Z FsNode.fs_node) :
  ghost_map_auth gt q I -∗ ▷ app_dur_at A gt r -∗
    ◇ (ghost_map_auth gt q I ∗ ghost_map_auth gt (1/2) I ∗
       ▷ A r (FsAbsDefs.abs_view I)).
Proof.
  iIntros "Hk Hg". rewrite /app_dur_at.
  iDestruct (bi.later_exist_except_0 with "Hg") as "Hg".
  iMod "Hg" as (I') "[>Hh Hp]".
  iDestruct (ghost_map_auth_agree with "Hk Hh") as %<-.
  iModIntro. iFrame "Hk Hh". iExact "Hp".
Qed.

(* THE ERA'S UART NAMES, READ OFF THE BOOT SUPPLY (lane APP-IFACE item (c),
   review-echo-plan finding 3).  [FsCfgBoot.fs_boot_supply] already CARRIES
   the tie -- the era's configuration record names the very [uart_names] the
   boot minted -- and the trace permit is built at that same [gud] a few
   lines later.  This is that pure conjunct, peeled off without spending the
   supply ([FsCfgBoot.fs_boot_supply_app_inv] is the shape). *)
Lemma fs_boot_supply_uart {Sg : gFunctors} `{!riscvGS Sg, !xv6G Sg, !bioslotG Sg}
    `{XI : CtxIdDefs.CurCtx}
    (ICFG : icfg) (FSC : FsCfg.fscfg) (APP : appcfg Sg) (dk : Z -> bv 8)
    (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
    (gud : uart_names) (guv : DiskPtsto.disk_names) (cnm : cons_names)
    (Rspent : gset Z) (Pb : Z -> list (bv 8)) (Xexc : gset Z) :
  fs_boot_supply ICFG FSC APP dk sb nib cov gud guv cnm Rspent Pb Xexc ⊢
    ⌜@FsCfg.fsc_uart FSC = gud⌝ ∧
    fs_boot_supply ICFG FSC APP dk sb nib cov gud guv cnm Rspent Pb Xexc.
Proof.
  iIntros "H". iSplit; [| iExact "H"].
  rewrite /fs_boot_supply.
  iDestruct "H" as "(_ & _ & _ & %Hu & _)". iPureIntro. exact Hu.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE COMPOSITE CRASH SLOT (app-instances.md round C, section 6 rulings   *)
(* 3 and 7).  Two predicates side by side under the one fixed-layer        *)
(* invariant: the file system's durability record at its snapshot's map    *)
(* name ([FsCrash.P_fs_named_at]), and the application's durable claim at  *)
(* that SAME name ([AppDur.app_dur_raw] at the application's predicate,    *)
(* its fixed part applied) -- tied to the snapshot by the guest half of    *)
(* the map's authority, and by nothing else.  The binder is the SLOT's:   *)
(* the record is untouched in statement and the application's conjunct is *)
(* its own.  No later on the guest here: the slot sits under the machine's *)
(* own [▷] ([crash_inv]).                                                  *)
(* ---------------------------------------------------------------------- *)
Definition xv6_slot {Σ : gFunctors} `{!xv6G Σ, !riscvGpreS Σ}
    {CT : Type} (N : Type) (app_fs : CT -> N -> FsAbsDefs.aview -> iProp Σ)
    (cov : gset Z) (ls : Z)
    (γd γsw γreg γst : gname) (c : CT) : iProp Σ :=
  (∃ gt : gname,
     P_fs_named_at gt γd XV6_DISK_BYTES γsw γreg γst cov ls ∗
     app_dur_raw (app_fs c) gt)%I.

(* THE PURE PROJECTION OF THE COMPOSITE: the file system's half is
   projected ([FsCrash.P_fs_project]) and the guest is FRAMED -- the map
   name does not move.  Both [Hproj] and the trace hooks below are this. *)
Lemma xv6_slot_project {Σ : gFunctors} `{!xv6G Σ, !riscvGpreS Σ}
    {CT : Type} (N : Type) (app_fs : CT -> N -> FsAbsDefs.aview -> iProp Σ)
    (cov : gset Z) (ls : Z)
    (γd γsw γreg γst : gname) (c : CT) (dk : Z -> bv 8) :
  ⊢ disk_img_auth_sized γd XV6_DISK_BYTES dk -∗
    ▷ xv6_slot N app_fs cov ls γd γsw γreg γst c -∗
    ◇ (disk_img_auth_sized γd XV6_DISK_BYTES dk ∗
       ▷ xv6_slot N app_fs cov ls γd γsw γreg γst c ∗
       ⌜fs_boot_pure cov ls dk⌝).
Proof.
  iIntros "Ha HP". rewrite /xv6_slot.
  iDestruct "HP" as (gt) "[HP HG]".
  iMod (P_fs_project gt γd XV6_DISK_BYTES γsw γreg γst cov ls dk
          with "Ha HP") as "(Ha & HP & %Hp)".
  (* placed by name, never framed: the record owns the durable disk's byte
     big-op behind a [Definition] (durable-notes on [iFrame]) *)
  iModIntro. iSplitL "Ha"; [iExact "Ha" |]. iSplitL; [| iPureIntro; exact Hp].
  iNext. iExists gt. iSplitL "HP"; [iExact "HP" | iExact "HG"].
Qed.

Lemma fs_trace_hook (Σ : gFunctors) `{!xv6G Σ, !riscvGpreS Σ}
    (cov : gset Z) (ls : Z) (CT N : Type)
    (app_fs : CT -> N -> FsAbsDefs.aview -> iProp Σ)
    (Hinv : invGS Σ) (γgen γstart γreg γd γsw γobs γhist : gname) (c : CT)
    (* the application's console interface (redesign R4): carried by the
       record literal, read by nothing here *)
    (T : list mobs) (Ai : app_iface Σ)
    (g' : gstate) :
  ⊢ @power_interp Σ
       (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
          (xv6_slot N app_fs cov ls γd γsw γreg γstart c)
          γobs T (obs_pred_at γobs) γhist Ai CT c) g' -∗
    ▷ xv6_slot N app_fs cov ls γd γsw γreg γstart c -∗
    ◇ ⌜fs_boot_pure cov ls (v_disk (g'.(gdev).(dvirtio)))⌝.
Proof.
  exact (disk_proj_trace XV6_DISK_BYTES CT
           (xv6_slot N app_fs cov ls)
           (fs_boot_pure cov ls)
           (xv6_slot_project N app_fs cov ls)
           Hinv γgen γstart γreg γd γsw γobs T (obs_pred_at γobs) γhist
           Ai c g').
Qed.

(* ...AND A [phi] THAT IS NOT ABOUT THE DISK AT ALL, beside it.

   [fs_boot_pure] is read off the crash INVARIANT (through the durable
   disk's auth); [resv_ok] is read straight off [state_interp]'s ERA
   conjunct, with no invariant involved.  They are put in ONE [phi] here on
   purpose: [phi] is a single [Prop], so a client that wants several facts
   conjoins them, and the two conjuncts below travel through two entirely
   different conjuncts of [state_interp].  That is the demonstration that
   [riscv_power_adequacy]'s trace channel is not a disk channel.

   The [gpow] guard on the second is forced and is not a weakness: between a
   PowerOff and the next PowerOn there IS no era, so registers, memory and
   the device fabric are described by no ghost state at all.  A UART or
   memory invariant would be stated the same way -- guarded by [gpow], via
   [RiscvAdequacy.power_interp_era] and the client's own era receipt. *)
Definition xv6_trace_pure (cov : gset Z) (ls : Z) (g : gstate) : Prop :=
  (* THE DISK, from the crash invariant *)
  fs_boot_pure cov ls (v_disk (g.(gdev).(dvirtio))) /\
  (* NOT THE DISK: the reservation invariant, from the era conjunct *)
  (g.(gpow) = true -> resv_ok g).

Lemma xv6_trace_hook (Σ : gFunctors) `{!xv6G Σ, !riscvGpreS Σ}
    (cov : gset Z) (ls : Z) (CT N : Type)
    (app_fs : CT -> N -> FsAbsDefs.aview -> iProp Σ)
    (Hinv : invGS Σ) (γgen γstart γreg γd γsw γobs γhist : gname) (c : CT)
    (T : list mobs) (Ai : app_iface Σ)
    (g' : gstate) :
  ⊢ @power_interp Σ
       (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
          (xv6_slot N app_fs cov ls γd γsw γreg γstart c)
          γobs T (obs_pred_at γobs) γhist Ai CT c) g' -∗
    ▷ xv6_slot N app_fs cov ls γd γsw γreg γstart c -∗
    ◇ ⌜xv6_trace_pure cov ls g'⌝.
Proof.
  iIntros "Hsi HP".
  (* the era-side fact first: its conclusion is PURE, so [state_interp] is
     not spent and the disk projection still has it *)
  iDestruct (power_interp_resv_ok with "Hsi") as %Hresv.
  iDestruct (fs_trace_hook Σ cov ls CT N app_fs Hinv γgen γstart γreg γd γsw
               γobs γhist c T Ai g' with "Hsi HP") as ">%Hdisk".
  iModIntro. iPureIntro. split; [exact Hdisk | exact Hresv].
Qed.

Section SystemBoot.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{!ufdG Σ}.
  Context `{!fileGpreS Σ, !fdslotGpreS Σ, !irefslotGpreS Σ, !pavGpreS Σ, !bioslotGpreS Σ}.
  (* the [wait_lock] children map's capacity: [Xv6Cameras.wchG] carries the
     NAME, so it left [Xv6G]'s bundle and only the functor half is assumed
     here -- [BootShared.boot_shared_alloc] mints the instance. *)
  Context `{!wchGpreS Σ}.
  (* B3's two classes are [xv6G] MEMBERS now (2b-inode-3 / 2b-inode-4), so
     nothing extra is bound here -- see [FsCfgBoot]'s era section. *)
  Context `{GEN : GenId}.

  (* NO [fileG] AND NO [icacheG] BINDER ANY MORE (fs-cfg-boot.md stage
     (d2b)).  [fileG] carries [IcacheRefDefs.icfg] and [FsCfg.fscfg] as
     superclass fields, and nothing in the tree ever produced either: the
     two records used to be the hardcoded [adequacy_icfg]/[adequacy_fscfg]
     of this file, at [icfg_nib = 0], where an [IcacheHeld.inode_held] cannot
     exist -- so the boot cone's one assumed contract was VACUOUS at the
     instance the corollaries below are taken at.  [boot_shared_alloc] now
     MINTS both inside the era fupd, off the era's own disk, and hands the
     class back existentially; only the camera ([fileGpreS]) is a functor
     constraint. *)
  (* WHAT THE POWER ARM LENDS THIS BOOT IS THE CRASH PREDICATE'S OWN EPOCH
     (durable-disk BT-3).  It was a client parameter at BT-1, carried and
     dropped; it is NAMED here now, because this is where it is SPENT: the
     era splits it off [power_boot_res], pins its committed map to its own
     with [FsCrash.fs_recovery_det], and unpacks it -- and the abstract
     state the whole boot mint is configured at is the one that comes OUT
     of that resource, not one an existential in [fs_boot_pure] chose.
     That is what makes the durability claim's [snap_ok] a READING at every
     era and a premise of nothing. *)
  Lemma xv6_boot_era (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
      (* THE APPLICATION'S FILE-SYSTEM SIDE (claude-notes/projects/
         app-instances.md sections 1-2, 6): its predicate on the abstract
         state's view, ALREADY APPLIED at the application's fixed part
         (round D0: the caller applies [app_fs riscv_client] -- inside the
         boot hook the record is the [boot_fixedGS ... c] literal, so
         [riscv_client = c] by conversion); this boot BUILDS the era's
         application record [MkAppcfg N A r] for the mint -- and its LEND
         -- what the PowerOn arm hands this boot about the durable state,
         likewise already applied at the fixed part, riding
         [power_boot_res]'s [Rb] beside the file system's own
         [P_fs_lend]. *)
      (N : Type) (A : N -> gmap Z FsAbsDefs.anode -> iProp Σ)
      (* THE FIRST PROCESS'S BOOT RESOURCE (lane APP-IFACE item (a),
         review-echo-plan finding 6): what the application hands the era's
         <init> beside its claim, at the era's own instance.  Produced by
         the transport at the PowerOn clone and carried here by the lend;
         spent by [Hinit_boot] below and nowhere else. *)
      (* ...ERA-INDEXED (lane CONS-IO milestone C): this era's number is
         [S gen_id], and the three are read at it and nowhere else. *)
      (B : nat -> N -> iProp Σ)
      (* THE ERA'S TURN (lane CONS-IO milestone F): the APPLICATION's own
         per-era credential for <init>, minted at the power-on step and
         carried here on [power_boot_res] beside the two claims.  An opaque
         [iProp] already applied at this era's number -- the system theorem
         instantiates it at [App.app_turn A c (S gen_id)] -- because nothing
         at this altitude may name the application's record. *)
      (Tn : iProp Σ)
      (* NO PORT-CLAIM PARAMETERS (lane CONS-IO milestone E).  The era's
         two claims used to be produced by the transport at the clone and
         carried here by the lend, with two equations ([Houteq]/[Hineq])
         tying them to the fixed record's fields.  They are the
         APPLICATION's yield at the power-on step now and ride
         [power_boot_res] itself, already AT the fixed record's fields, so
         this entailment neither names them nor ties them. *)
      (* THE TRANSPORT (app-instances.md round C, section 1): the
         application's one durability obligation, parked in the era's
         invariant by the mint and carried to fsinit on the kit, where the
         commit's law copies the running claim onto each fresh snapshot.
         The boot itself needs no transport: the lent durable claim IS the
         era's running one. *)
      (Happ_xfer : ⊢ app_xfer_raw A)
      (* THE FIRST PROCESS'S EXEC BUNDLE (ARM-c), and it is the ONE thing
         the application owes the kernel about user execution.  THE KERNEL
         NEVER MINTS A SLOT: forkret's boot arm runs kexec("/init") between
         the first park and the first resume, so the only key that process
         can be given is the one kexec builds -- and what answers at that
         key is the SLOT PIECE of the exec bundle the arm is called with.
         This boot hands the bundle to the boot hart's chain; main forwards
         it to userinit, whose park carries it to that arm
         ([InitBoot.init_boot_bundle], [ParkCap.park_pkg]'s BOOT mode).

         QUANTIFIED OVER THE ERA'S GHOST CLASSES, because they do not exist
         until [BootShared.boot_shared_alloc] has run -- the equation ties
         the [appcfg] it built to this era's application, exactly as
         [Hperm]'s premise ties the fixed record.  It receives the
         application's own invariant, which is what a CONSTRAINING
         application reads its pins out of; the bupd is there so a
         discharge may mint ghosts of its own.

         WHY THIS IS NOT THE GAP-PREMISE TRAP.  It is discharged BY PROOF
         at every instance: the generic application's from the trivial
         supply and the generic mint ([init_boot_of_sup] below), echo's
         from its pinned bundle at "/init".  The SUPPLY [AppInv.app_sup_raw]
         -- "the claim is trivially true" -- is honest for the generic
         theorem and unpayable by any constraining application, which is
         why the obligation is stated at the BUNDLE and the supply stays
         inside the generic discharge. *)
      (Hinit_boot :
         forall `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
                  HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ} (r : N),
           @file_app Σ HF = MkAppcfg N A r ->
           ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ B (Datatypes.S gen_id) r -∗
             (* ...AND THE ERA'S TURN BESIDE IT (lane CONS-IO milestone F):
                the application's own per-era credential, carried from the
                power-on step and handed to <init> in the boot bundle's one
                linear slot ([UInitKernel.init_boot_pay]).  What it buys is
                what no per-era resource can say on its own -- that THIS
                era's console turn is <init>'s, once. *)
             Tn -∗
             |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0)
      (* THE ECHO'S JUSTIFICATION (lane OUT-FUPD, F3), the second thing the
         application owes the kernel about the console and the twin of
         [Hinit_boot] one level down: consoleintr's echo pushes bytes at
         [Uart0], the port whose invariant now carries the application's own
         output claim, and the interrupt path has nothing of its own to pay
         the store's view shift with.  So the payment is the application's,
         minted once into [SpecConsoleintr.console_caps] by main and
         persistent, so every byte's echo re-uses it.  QUANTIFIED OVER THE
         CONTEXT because the boot chain runs at the boot hart's own [CtxId]
         and nothing in the shift is context-relative.  The generic
         application discharges it by [SpecConsoleintr.cons_echo_shift_triv],
         a constraining one out of its own discipline. *)
      (* ...AT EVERY ERA (lane CONS-IO milestone C): the shift is
         era-indexed and takes the byte's era stamp, so the obligation is
         quantified over the generation as it is over the context, and this
         boot spends it at its own [gen_id]. *)
      (Hecho : ⊢ ∀ (GEN0 : GenId) (XI : CurCtx),
                   cons_echo_shift (GEN := GEN0) (XI := XI)) :
    boot_facts g ->
    (* THE PROJECTION THE POWER THEOREM PROVES AT THIS ERA, AND IT IS THE
       WHOLE OF WHAT THIS BOOT KNOWS ABOUT ITS DISK (durable-disk lane
       E-himg).  The crash predicate's own reading of the disk this boot
       runs on -- the durable extent, the recovery record, the header
       invariant and the DURABLE SNAPSHOT -- extracted from [P_fs] by
       [FsCrash.P_fs_project] rather than assumed.  There is no image
       hypothesis at this era and there cannot be one: what a later era
       boots on is whatever the previous era committed. *)
    fs_boot_pure cov (FsImg.sb_logstart sb)
      (v_disk (g.(gdev).(dvirtio))) ->
    (* ...AND THE THREE FACTS ABOUT THE COVERED RANGE, which the snapshot
       cannot carry: [cov] and the crash predicate's [logstart] are FIXED
       across power cycles while the era's superblock is not, so these are
       read once off the initial machine and threaded. *)
    FsBoot.fs_cov_in cov XV6_DISK_BYTES ->
    log_region_set (FsImg.sb_logstart sb) ⊆ cov ->
    FsImg.sb_logstart sb = 2 ->
    (* NO PORT-CLAIM EQUATIONS (lane CONS-IO milestone E).  The two
       equations [riscv_out_res = O] / [riscv_in_res = I] were here to
       identify the TRANSPORT's abstract yield with the fixed record's
       fields.  The claims come on [power_boot_res] now, already at those
       fields, so there is nothing to identify. *)
    (* THE CRASH SLOT'S VALUE, as a PURE equation (fs-cfg-boot.md stage
       (f), row 7 of [FirstTok.first_boot_persist]).  The boot cone needs
       [FsCrash.fs_crash_seam], and no fupd inside an era can mint it:
       the seam relates the FIXED ghost layer's [riscv_crash_pred] FIELD to
       the FS's own [P_fs], and the per-era obligation
       [RiscvAdequacy.riscv_power_adequacy] asks for is quantified over an
       ARBITRARY [riscvFixedGS], so an era learns nothing about that field.
       Adequacy is where the record is built, so adequacy is where the fact
       has to come from -- that is [riscv_power_adequacy]'s [Hcp], and this
       premise is [Hcp] read at the FS's own [Pc].  The seam is assembled
       from it below and rides [first_tok] to forkret's first arm. *)
    (* ...SINCE ROUND C THE SLOT IS THE COMPOSITE: the record at its
       snapshot's map name beside the application's durable claim at that
       name ([FsCrash.P_fs_comp] at the guest [app_dur_raw A]). *)
    riscv_crash_pred = P_fs_comp (app_dur_raw A) cov (FsImg.sb_logstart sb) ->
    (* THE TRACE SLOT'S VALUE, likewise (claude-notes/completed/uart-trace.md):
       this boot states no trace property, so the slot holds the trivial
       predicate, and that is what discharges the UART thread's permit. *)
    (* THE UART THREAD'S TRACE PERMIT (uart-trace.md): what this boot cannot
       prove itself, since it depends on the trace slot's value -- the
       trivial slot's is [WpUart.uart_obs_permit_triv], a ledger's is
       [uart_obs_permit_ledger].  A Coq-level premise, so the system theorem
       passes its own down. *)
    (* ...AND IT IS STATED AT THE ERA'S OWN NAMES SINCE lane APP-IFACE item
       (c) (review-echo-plan finding 3): the permit used to be quantified
       over an ARBITRARY [γ : uart_names], so a ledger's tx/rx wand could
       learn nothing about THE ERA's UART ghosts.  It is quantified over the
       era's ghost classes instead -- exactly as [Hinit_boot] is, and for the
       same reason -- with the two equations the boot HAS: the era's
       application record, and [fsc_uart], which is the [γ] every kernel-side
       UART fact in this era is stated at. *)
    (forall `{HF : !fileG Σ} (r : N) (i : uart_id) (γ : uart_names),
       @file_app Σ HF = MkAppcfg N A r ->
       (i = Uart0 -> FsCfg.fsc_uart = γ) ->
       ⊢ obs_inv -∗ uart_obs_permit i γ) ->
    obs_inv -∗
    power_boot_res riscv_eraGS gen_id boot_D NPROC XV6_DISK_BYTES
      (fun dk => mirror_of (fs_blocks dk))
      (* THE LEND (round C): the crash predicate's clone at its map name,
         and the application's durable claim at that same name, tied by the
         guest half -- what the PowerOn arm produced by [FsCrash.P_fs_swap]
         and the transport *)
      (* ...AT A NAMED INSTANCE, and with the BOOT RESOURCE beside it (lane
         APP-IFACE item (a)): [app_dur_raw] closes the instance
         existentially, which is right for the slot and wrong here -- the
         resource [Hinit_boot] spends is at the same [r] as the claim the
         era founds its file system from. *)
      (* ...AND THE ERA'S OUTPUT CLAIM AT THE EMPTY RUN (lane OUT-FUPD),
         beside the boot resource and produced by the same transport: the
         claim holds the application's authority, so it is minted per era
         and the mint founds the console port's invariant clause from it. *)
      (fun dk => ∃ (gt : gname) (r : N),
         P_fs_lend_at gt cov (FsImg.sb_logstart sb) dk ∗
         ▷ app_dur_at A gt r ∗ B (Datatypes.S gen_id) r)%I Tn g
    ={⊤}=∗
      ([∗ list] c ∈ enum CPU,
         mWP (LoopE gen_id c : expr riscv_lang) @ ⊤) ∗
      ([∗ list] i ∈ enum uart_id, mWP (UartLoopE gen_id i : expr riscv_lang) @ ⊤) ∗
      mWP (DiskLoopE gen_id : expr riscv_lang) @ ⊤ ∗
      mWP (PlicLoopE gen_id : expr riscv_lang) @ ⊤.
  Proof using bioslotGpreS0 fdslotGpreS0 fileGpreS0 irefslotGpreS0 pavGpreS0 ufdG0 wchGpreS0.
    intros Hbf Hpure Hcovin Hlogsub Hls2 Hcp Hperm.
    iIntros "#Hoinv Hres".
    (* ================================================================ *)
    (* THE ERA'S OWN CONFIGURATION, OFF THE SNAPSHOT (durable-disk lane  *)
    (* E-himg).  [fs_boot_pure] names the committed map [D] and an        *)
    (* abstract state [S] it encodes; the boot mint takes a total block   *)
    (* view, which is [FsCrash.fs_rec_view] of that map, and the era's    *)
    (* superblock and region width are [S]'s own.  The one thing that     *)
    (* has to be reconciled is the LOG START: the crash predicate's is a  *)
    (* parameter and [S]'s comes out of its own superblock, and           *)
    (* [FsImg.sbo_logstart] pins both at 2.                               *)
    (* ================================================================ *)
    (* THE PURE EXPORT'S OWN [S] IS NOT USED (durable-disk BT-3).
       [fs_boot_pure] still carries [exists S, snap_ok S D] -- it is the
       theorem's durability claim and [FirstTok] reads it -- but the boot
       takes its state off the LENT EPOCH below, so nothing here has to
       identify two abstract states and no determinacy theorem is needed.
       What the projection is still indispensable for is [D] itself: it is
       what [fs_recovery_det] pins the lent map to. *)
    destruct Hpure as (Hext & D & Hrec & Hhwf & _).
    (* ---- THE LENT EPOCH, OFF [power_boot_res]'s CLIENT CONJUNCT ---- *)
    iDestruct (power_boot_res_lend with "Hres") as "[Hlend Hres]".
    (* ...which is the file system's clone at its map name beside the
       APPLICATION's durable claim at that name (round C) *)
    iEval (cbv beta) in "Hlend".
    iDestruct "Hlend" as (gtn rap) "(Hlend & Hguest & Hbres)".
    iEval (rewrite /P_fs_lend_at) in "Hlend".
    iDestruct "Hlend" as (D0) "[%Hrec0 Hdur]".
    (* the identification, and it is one step: recovery is a FUNCTION of the
       physical disk, so the map the crash predicate's epoch stands at IS
       the map this boot's own projection names. *)
    pose proof (fs_recovery_det _ _ _ _ _ Hrec0 Hrec) as HD0. subst D0.
    (* ...and the state comes out of the resource. *)
    iEval (rewrite /P_dur_at) in "Hdur".
    iDestruct "Hdur" as (gsn gln S) "Hdursnap".
    (* THE APPLICATION'S CLAIM COMES OUT OF THE GUEST (round C, section 3
       crossing 3): the guest's half agrees with the clone's kernel half, so
       the claim is about the clone's own state -- the founded map -- at
       SOME instance, which becomes the era's running one.  The guest half
       itself is dropped: the era founds its own map. *)
    iDestruct (fs_snap_top_acc with "Hdursnap") as "[Htopk Hdursnap]".
    iMod (app_dur_at_agree A gtn rap (1/2) (fss_inodes S) with "Htopk Hguest")
      as "(Htopk & _ & Hok)".
    iDestruct ("Hdursnap" with "Htopk") as "Hdursnap".
    iDestruct (fs_snap_read_ok_keep _ _ _ _ _
                 (fs_recovery_blocks_full _ _ _ _ Hrec) with "Hdursnap")
      as "[%Hsnok Hdursnap]".
    pose proof (sk_bytes Hsnok) as Hsnb.
    pose proof (sk_sbok Hsnb) as Hsbok.
    pose proof (FsImg.sbo_logstart _ Hsbok) as Hls'.
    pose proof (FsImg.sbo_ninodes _ Hsbok) as Hni.
    unfold FsImg.ROOTINO in Hni.
    assert (Hdv : 0 <= FsImg.sb_ninodes (fss_sb S) / 16)
      by (apply Z.div_pos; lia).
    assert (Hlseq : FsImg.sb_logstart (fss_sb S) = FsImg.sb_logstart sb)
      by (rewrite Hls' Hls2; reflexivity).
    pose (Pb := fs_rec_view
                  (fs_blocks (v_disk (g.(gdev).(dvirtio)))) D).
    assert (Hbundle : fs_boot_snap_wf (v_disk (g.(gdev).(dvirtio)))
                        XV6_DISK_BYTES S Pb (fss_sb S) (fs_nib S) cov).
    { split; [reflexivity |].
      split; [rewrite /fs_nib Z2Nat.id; [reflexivity | lia] |].
      split.
      { rewrite Hlseq (fs_recovery_restrict _ D cov _ Hrec Hhwf).
        exact Hsnok. }
      split.
      { intros b. apply fs_rec_view_len;
          [intros b'; apply fs_blocks_length
          | intros b' bs Hbs; exact (sk_bsz Hsnb b' bs Hbs)]. }
      split; [rewrite Hlseq; exact Hhwf |].
      split.
      { rewrite Hlseq. intros b Hh Hout.
        exact (fs_rec_view_raw _ D cov _ b Hrec Hhwf Hh Hout). }
      split.
      { rewrite Hlseq. intros i b Hi.
        exact (fs_rec_view_slot _ D cov _ i b Hrec Hhwf Hi). }
      split; [exact Hcovin | rewrite Hlseq; exact Hlogsub]. }
    (* THE EPOCH, RESPELLED AT THE MINT'S OWN LEDGER: [fs_rec_view] cut to
       the home set IS the committed map ([fs_recovery_restrict]), so this
       is a rewrite and not a transport. *)
    assert (HDeq : fs_restrict Pb
                     (fs_home_set cov (FsImg.sb_logstart (fss_sb S))) = D).
    { rewrite Hlseq. exact (fs_recovery_restrict _ D cov _ Hrec Hhwf). }
    iEval (rewrite -HDeq) in "Hdursnap".
    (* THE SEAM, ASSEMBLED FROM THE SLOT EQUATION and put in the
       intuitionistic context: it rides [FirstTok.first_boot_persist] from
       here to forkret's first arm.  Both directions are the identity once
       [Hcp] has rewritten the field away, which is exactly what "the FS's
       predicate IS the crash predicate" means.  It is spelled at the ERA's
       superblock, which is where the boot chain wants it; [Hlseq] is the
       one step. *)
    iAssert (fs_crash_seam_at (app_dur_raw A) cov (FsImg.sb_logstart (fss_sb S)))
      as "#Hseamg".
    { rewrite Hlseq /fs_crash_seam_at. iModIntro.
      rewrite Hcp. iSplitL; iIntros "H"; iExact "H". }
    (* ...and its arity-free form, which the boot chain's sixty carriers
       take (the seam at SOME guest) *)
    iPoseProof (fs_crash_seam_of_at with "Hseamg") as "#Hseam".
    (* THE BOOT HART'S THREAD-OF-CONTROL TOKEN (tso-port M2): minted HERE,
       before the shared carve, so the carve's ξ-indexed rows are pinned at
       the identity the boot hart will run as.  The secondaries mint their
       own below; each reads the started deposit through its own token. *)
    iMod (own_context_boot (CID := 0%fin)) as (ξ0) "Hthr0".
    (* THE APPLICATION'S RUNNING CLAIM IS THE LENT DURABLE ONE (round C):
       [Hok] is at the founded map [fss_inodes S], later-shaped, at the
       instance [r] the transport minted; the transport comes with it, and
       the seam at the application's guest goes down to fsinit on the kit.
       All of it goes into the mint through [boot_shared_alloc]. *)
    iPoseProof Happ_xfer as "#Hxfer".
    (* THE ERA'S TWO PORT CLAIMS ARE NOT HERE (lane CONS-IO milestone E):
       they ride [power_boot_res] straight into the mint, which unpacks and
       consumes them at [Uart0]. *)
    iMod (boot_shared_alloc (XI := ξ0) g XV6_DISK_BYTES (fss_sb S) (fs_nib S) cov
            S Pb (MkAppcfg N A rap) (fun _ => emp)%I Tn gsn gln gtn Hbf Hbundle
            with "Hok Hxfer Hseamg Hdursnap Hres")
      as (Hfd Hir Hpav Hbs Hwch HF γd γd1 γv cnm Rspent γi ξd)
      "(%Hdimg & %Hcnu & %Happ & #Htext & #Hdata &
        #Hpinned & #Hubw0 & #Hubw1 & #Hurw0 & #Hurw1 &
        #Hstarted & Hprim & #Hdev & #Hdev1 & #Hplic & #Hwinv & Hturn &
        #Hcinv & #Hcert & Hharts & Hlk & Hgl & Hmdata & Hpark & Hpst & Hpavail & Hchb & Huart &
        Htok & Hhi & Hlgh & Harm & Hdlab & Huart1 & Htok1 & Hhi1 & Hlgh1 & Harm1 & Hdlab1 &
        Hcfg & Hclaim & Hcmauth & #Hdone & Hkpt & Hkptb & Hkmap & Hmir & Hpages & Hirauth &
        Hirslot & Hfs)".
    (* THE FIRST PROCESS'S EXEC BUNDLE, off [Hinit_boot] at the era's own
       ghost classes -- which is why the hypothesis quantifies over them:
       the mint above is where they are born.  The application's invariant
       it is handed is [FsCfgKits.fs_kit_fsinit_ghost]'s application row,
       which rides [Hfs] to main; persistent, so the copy is free.  LINEAR
       -- it goes down the BOOT hart's chain and nowhere else. *)
    (* AT THE ERA'S OWN [GenId], BY NAME: the lemma's [GEN] occurs in
       neither side of its entailment, so resolution would leave it an
       evar and the proof term would not close. *)
    iDestruct (FsCfgBoot.fs_boot_supply_app_inv (GEN := GEN) with "Hfs")
      as "[#Happinv Hfs]".
    (* THE ERA'S UART NAMES, off the supply (item (c)): the equation the
       trace permit is built at, read before the supply goes down the boot
       hart's chain. *)
    iDestruct (fs_boot_supply_uart with "Hfs") as "[%Huart Hfs]".
    iMod (Hinit_boot Hbs Hfd Hir Hpav Hwch HF rap Happ
            with "Happinv Hbres Hturn") as "Hboot".
    (* THE FILE SYSTEM'S BOOT KITS ARE NO LONGER DROPPED (stage (e)).
       [Hfs] is the ten configuration ties plus [fs_kit_icache] plus
       [fs_kit_fsinit_ghost], and [Hirauth] is the iref-slot authority
       [icache_boot_at] takes.  Both now ride [boot_hart_primary] into
       [SpecMain]'s boot arm, where [ProofMain.mn_grp_fs] runs
       [icache_boot_at] on them and hands the four inode-cache rows to
       [userinit] -- which is what discharged [LinkNameiRootBoot]'s Axiom. *)
    (* the harts' reservation mirrors (design §3a) are gone from this
       interface: [boot_shared_alloc] threads each into its hart's [pc_is]. *)
    (* [Hmdata] IS [BootShared.main_data_raw] -- the image's writable
       initialized globals (`first`, `nextpid`), which [kernel_data] stopped
       claiming when it was narrowed to [rodata_end].  It is threaded to main
       now: [ProofMain.mn_grp_kvm] spends `nextpid` on the [newlock] that
       builds [PidLock]'s lock, which is allocproc's premise and hence
       userinit's.  `first` rides along and is dropped there -- its consumer
       is forkret's [if (first)] arm. *)
    iDestruct "Huart" as (l0) "(Htx & #Hsent & #Hlb & %Hl0)".
    iDestruct "Hdlab" as (b0) "Hdlab".
    (* ...AND THE SAME TWO ROWS AT THE SECOND PORT (bump 163d39b): main runs
       [uartinitone] there too, so port 1 owes the transmitter token, the
       transmitted-prefix bound, the receipt and the UNFROZEN DLAB half,
       exactly as the console does.  What it does NOT owe is any claim about
       the bytes -- its output is unconstrained. *)
    iDestruct "Huart1" as (l1) "(Htx1 & #Hsent1 & #Hlb1 & %Hl1)".
    iDestruct "Hdlab1" as (b1) "Hdlab1".
    iDestruct "Hcfg" as (c0) "[%Hlive Hcfg]".
    iDestruct "Hpages" as (ps) "(%Hprun & %Hplen & Hpages)".
    (* one row out of [boot_shared_alloc], two premises at [BootChain] -- the
       halves are what main spends and drops separately *)
    iDestruct "Hmdata" as "[Hmfirst Hmnext]".
    (* THE ERA'S MIRROR IS ROW (B) of [FirstTok.first_fsinit], and main
       parks it there for initlog.  Since durable-disk 1a it arrives
       VALUE-BEARING -- the era's half at the picture of its own disk plus
       the swap receipt -- so there is nothing to weaken here: what
       [boot_shared_alloc] hands over IS the shape [SpecInitlog] takes. *)
    iDestruct (big_sepL_cpu_peel with "Hharts") as "[Hh0 Hhrest]".
    (* the three device threads' invariants, off the one device fabric *)
    iDestruct (dev_inv_uart with "Hdev") as "#Huinv".
    (* THE PLIC INVARIANT IS KEYED BY BOTH PORTS, and the bundle ∃-packs the
       second port's names (WpUart.v, [dev_inv]).  Nothing HERE needs to know
       which they are -- the three device threads only ever move slots by
       [plic_slots_stable], which is port-generic -- so the packed witness is
       what the loops are instantiated at.  The site that DOES need the
       concrete [γd1] is main's second deposit, and it gets [plic_inv γd γd1]
       from [boot_shared_alloc] directly. *)
    iDestruct (dev_inv_plic with "Hdev") as (γp1) "#Hpinv".
    iDestruct (dev_inv_disk with "Hdev") as "#Hvinv".
    iDestruct (dev_inv_perm with "Hdev") as "#Hqinv".
    iModIntro.
    iSplitL "Hthr0 Hprim Hh0 Hhrest Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail Hchb Hfs Hmir Hirslot Hirauth Hboot Htx Htok Hhi Hlgh Harm Hdlab Htx1 Htok1 Hhi1 Hlgh1 Harm1 Hdlab1 Hcfg Hclaim Hcmauth Hkpt Hkptb Hkmap
             Hpages".
    { iApply (big_sepL_cpu_glue
                (fun c => mWP (LoopE gen_id c : expr riscv_lang) @ ⊤
)%I).
      iSplitL "Hthr0 Hprim Hh0 Hlk Hgl Hmfirst Hmnext Hpark Hpst Hpavail Hchb Hfs Hmir Hirslot Hirauth Hboot Htx Htok Hhi Hlgh Harm Hdlab Htx1 Htok1 Hhi1 Hlgh1 Harm1 Hdlab1 Hcfg Hclaim Hcmauth Hkpt Hkptb Hkmap
               Hpages".
      { (* THE BOOT HART: the arm that consumes the whole supply. *)
        (* AT [HF] EXPLICITLY, not by resolution.  [SpecMain.MAIN]'s
           parameters are ∀-quantified over the classes, so handing the
           chain the instance the era fupd just built is an APPLICATION;
           asking resolution for a [fileG Σ] here would take the
           [subG_fileΣ -> fscfg -> file_fscfg -> fileG] cycle instead
           (FileInv.v's "two instance paths print identically and do not
           unify", and the 400 GB divergence the deleted [adequacy_fscfg]
           was written to block). *)
        iDestruct "Hh0" as (iv) "Hh0".
        (* THE BOOT HART'S THREAD OF CONTROL (tso-port leg M2) is [ξ0],
           minted ABOVE -- before the carve, so that the whole boot supply
           is carved at it (see the note there) -- and used as the AMBIENT
           context of the chain below: that is what lets
           [BootBridge.boot_bridge] take the token rather than mint it, and
           hence what keeps every lemma in main's cone context-implicit.
           ONE PER HART, not one for the system: [TsoCtx.own_context] is
           exclusive, so the eight harts run at eight distinct [CtxId]s. *)
        (* ROW BY ROW, NOT ONE [iApply … with "H1 … H30"], and this is a
           PERFORMANCE fix, not a style one (tso-port.md §0.16′).  MEASURED:
           with one mismatched premise in the list, the single [iApply] runs
           past TWENTY-THREE MINUTES at 2 GB and never reports; the
           [iSpecialize] chain below names the offending premise in 0.75 s.
           [iApply] with a spec list builds the whole application and unifies
           it against the goal in one go, so a mismatch deep in the list has
           nowhere to fail fast; specializing one premise at a time gives the
           unifier a head symbol to differ at.  §0.13′'s rule -- "a crawl IS
           the signature of an unprovable crossing" -- applies to tactics as
           well as to goals: never leave a 30-premise [iApply] as the place a
           mismatch has to surface. *)
        iPoseProof (boot_hart_primary (fileG0 := HF) (CID := 0%fin) (XI := ξ0)
                  (g.(gregs) 0%fin) iv DfracDiscarded γd γv cnm γi ξd ps l0 b0 c0
                  γd1 l1 b1
                  (v_disk (g.(gdev).(dvirtio))) (fss_sb S) (fs_nib S) cov
                  XV6_DISK_BYTES S Pb Rspent
                  (boot_regs_of_facts g Hbf 0%fin) fin_0_z Hprun Hplen Hlive
                  Hl0 Hl1 Hcnu Hbundle) as "HP".
        iSpecialize ("HP" with "Htext").
        iSpecialize ("HP" with "Hdata").
        iSpecialize ("HP" with "Hh0").
        iSpecialize ("HP" with "Hthr0").
        (* the started deposit at flip's shape (A6.132/A6.138): the [inv] over
           the position-indexed, [CtxMorph] payload every hart absorbs at its
           own context after its acquire fence, and its primitive receipt *)
        iSpecialize ("HP" with "Hstarted").
        iSpecialize ("HP" with "Hprim").
        (* THE ECHO'S JUSTIFICATION, at the boot hart's own context *)
        iSpecialize ("HP" with "[]"); [iApply (Hecho $! GEN ξ0) |].
        iSpecialize ("HP" with "Hlk").
        iSpecialize ("HP" with "Hgl").
        iSpecialize ("HP" with "Hmfirst").
        iSpecialize ("HP" with "Hmnext").
        iSpecialize ("HP" with "Hpark").
        iSpecialize ("HP" with "Hpst").
        iSpecialize ("HP" with "Hpavail").
        iSpecialize ("HP" with "Hchb").
        iSpecialize ("HP" with "Hfs").
        iSpecialize ("HP" with "Hmir").
        iSpecialize ("HP" with "Hirslot").
        iSpecialize ("HP" with "Hirauth").
        iSpecialize ("HP" with "Hcert").
        iSpecialize ("HP" with "Hseam").
        iSpecialize ("HP" with "Hdev").
        iSpecialize ("HP" with "Hwinv").
        (* THE FIRST PROCESS'S EXEC BUNDLE, off [Hinit_boot] above -- at
           the era's own ghost classes, and LINEAR, which is why only the
           BOOT hart's chain carries it (the secondaries never call
           userinit). *)
        iSpecialize ("HP" with "Hboot").
        iSpecialize ("HP" with "Htx").
        iSpecialize ("HP" with "Hsent").
        iSpecialize ("HP" with "Hlb").
        (* THE RECEIVE TOKEN, on its way to uartinit's FCR flush, and the
           ring's partner half of the HIGH-WATER MARK beside it *)
        iSpecialize ("HP" with "Htok").
        iSpecialize ("HP" with "Hhi").
        (* ...and the LOG's high-water half beside it (lane CONS-IO) *)
        iSpecialize ("HP" with "Hlgh").
        (* ...and the consoleintr arm's half (redesign R2), parked in the
           same payload *)
        iSpecialize ("HP" with "Harm").
        iSpecialize ("HP" with "Hdlab").
        (* ---- THE SECOND PORT'S THIRTEEN ROWS (bump 163d39b).  Two
           invariants -- UART1's own, and the PLIC's at the two CONCRETE
           bundles, which main needs by name for port 1's receive-token
           deposit ([dev_inv]'s PLIC conjunct ∃-packs the second name, and
           that is what keeps that bundle at arity 2) -- then [uarts_pinned]
           and the four `.data` words every [WriteReg] in [uartinitone]
           loads its MMIO base from, then port 1's ghost row. ---- *)
        iSpecialize ("HP" with "Hdev1").
        iSpecialize ("HP" with "Hplic").
        iSpecialize ("HP" with "Hpinned").
        iSpecialize ("HP" with "Hubw0").
        iSpecialize ("HP" with "Hurw0").
        iSpecialize ("HP" with "Hubw1").
        iSpecialize ("HP" with "Hurw1").
        iSpecialize ("HP" with "Htx1").
        iSpecialize ("HP" with "Hsent1").
        iSpecialize ("HP" with "Hlb1").
        iSpecialize ("HP" with "Htok1").
        iSpecialize ("HP" with "Hhi1").
        iSpecialize ("HP" with "Hlgh1").
        iSpecialize ("HP" with "Harm1").
        iSpecialize ("HP" with "Hdlab1").
        iSpecialize ("HP" with "Hcfg").
        iSpecialize ("HP" with "Hclaim").
        iSpecialize ("HP" with "Hcmauth").
        iSpecialize ("HP" with "Hdone").
        iSpecialize ("HP" with "Hkpt").
        iSpecialize ("HP" with "Hkptb").
        iSpecialize ("HP" with "Hkmap").
        iSpecialize ("HP" with "Hpages").
        iApply "HP". }
      (* THE SEVEN SECONDARIES: every element of the tail is an [FS]. *)
      iApply (big_sepL_impl with "Hhrest").
      iIntros "!>" (k c _) "Hh".
      iDestruct "Hh" as (iv) "Hh".
      (* one thread of control per secondary hart, minted the same way and
         for the same reason as the boot hart's above *)
      iApply fupd_wp.
      iMod (own_context_boot (CID := FS c)) as (ξc) "Hthrc".
      iModIntro.
      iApply (boot_hart_secondary (fileG0 := HF) (CID := FS c) (XI := ξc)
                (g.(gregs) (FS c)) iv DfracDiscarded γd γv γi ξd
                (boot_regs_of_facts g Hbf (FS c)) (fin_FS_nz c)
                with "Htext Hdata Hh Hthrc Hstarted"). }
    (* ONE THREAD PER PORT.  The console's runs under the bundle's
       invariant; the second port's under its own, at its own ghosts -- and
       both take a permit from the SAME application ledger, which is why
       [Hperm] is quantified over the port. *)
    iDestruct (Hperm HF rap Uart0 γd Happ (fun _ => Huart) with "Hoinv")
      as "#Hperm".
    iDestruct (Hperm HF rap Uart1 γd1 Happ ltac:(intros Hc; discriminate Hc)
                 with "Hoinv") as "#Hperm1".
    iSplitR.
    { rewrite /enum /uart_id_finite /=.
      iSplitR;
        [iApply (wp_uart_loop Uart0 γd γd γp1 with "Hcert Huinv Hpinv Hperm")|].
      iSplitR; [|done].
      iApply (wp_uart_loop Uart1 γd1 γd γp1 with "Hcert Hdev1 Hpinv Hperm1"). }
    iSplitR;
      [iApply (wp_disk_loop γd γp1 γv Hdimg with "Hcert Hcinv Hqinv Hvinv Hpinv") |].
    iApply (wp_plic_loop γd γp1 with "Hcert Hpinv Hwinv").
  Qed.

End SystemBoot.

(* ---------------------------------------------------------------------- *)
(* 2b. THE GENERIC APPLICATION'S DISCHARGE OF [Hinit_boot].                *)
(*                                                                        *)
(* A machine running UNVERIFIED user programs owes the kernel a first      *)
(* process's exec bundle like any other application, and its is the        *)
(* TRIVIAL one: the walk says yes at a [True] cursor, the observation      *)
(* hands the lent authority straight back, and BOTH slot wands answer with *)
(* the generic inhabitant -- the user-execution WP every key admits        *)
(* ([ProofUexecWp.uexec_wp_gen]'s [box], eliminated here), minted on the    *)
(* application's supply -- which lives exactly here, inside this generic    *)
(* discharge, and in no kernel contract.                                    *)
(* ---------------------------------------------------------------------- *)

(* ...AND THE OUTPUT LICENCE THE GENERIC SUPPLY NOW CARRIES (lane
   OUT-FUPD), as a Coq-level premise rather than a resource argument: the
   application's supply is what BUYS it ([App]'s [al_sup]),
   read at the era's fixed-record equation for the output claim
   ([Houtfix], the twin of [Hinit_boot]'s rx-tag equation), so a caller
   that already hands over [app_sup] hands over nothing new. *)
Lemma init_boot_of_sup {Σ}
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ} `{GEN : GenId}
    (cw : Z) (secc : mword 64) (sts : list fdstate) :
  (* ...AND THE KILL CREDENTIAL AND THE OUTPUT LICENCE BESIDE THE SUPPLY
     (lanes KILL-PAY §1c and OUT-FUPD).  The generic slot's deposit is the
     generic supply, and since the trap deposit at an unexpected cause
     carries the price of a kill ([UexecRet.uexec_ret_F]) and the generic
     [write(2)] on the console carries the price of a byte
     ([SpecConsolewrite.cons_out_chain_of_licence]), that supply is the
     PAIR.  The CREDENTIAL is the application's and comes in from the boot
     exactly as the supply does ([xv6_power_adequacy_gen]'s [Hkill_sup]).
     THE LICENCE IS NEITHER (lane SUP-ONE): it was a Coq-level premise
     here ([app_sup ⊢ cons_licence]) and is now the interface's own law
     ([RiscvPtsto.ai_lic], read as [WpUart.cons_licence_of_taint]), so the
     taint below buys it and this theorem states one thing fewer. *)
  (* NO ALL-PARKED FACT (lane OFF-HAND-6, H3): the exec crossing's taint
     arm stopped asking for one, because a held row's half is in the
     descriptor bundle (design/app-file.md SS3 fact 4). *)
  app_sup -∗ app_taint -∗ init_boot_bundle cw secc sts.
Proof.
  iIntros "#Hsup #Hkc".
  iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hgen".
  iDestruct (UexecExecMint.uslot_mint with "Hsup Hkc Hgen") as "#Hmk".
  iApply (init_boot_bundle_triv cw secc sts with "Hmk").
Qed.

(* ...and at the generic application's predicate, which is what the three
   corollaries below and [App.xv6_app_adequacy_triv_xv6Σ] hand in *)
Lemma init_boot_of_triv {Σ}
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ} `{GEN : GenId}
    (cw : Z) (secc : mword 64) (sts : list fdstate) :
  (forall r av, app_pred r av ⊣⊢ True) ->
  (* ...and the machine's kill credential is the trivial one, so the
     generic discharge pays it for nothing (lane KILL-PAY, K1) *)
  app_taint = kill_cred_triv ->
  ⊢ init_boot_bundle cw secc sts.
Proof.
  intros Htriv Hkc. iApply (init_boot_of_sup cw secc sts).
  { iApply app_sup_of_triv. exact Htriv. }
  rewrite Hkc /kill_cred_triv. done.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE SYSTEM THEOREM.                                                  *)
(* ---------------------------------------------------------------------- *)

Theorem xv6_power_adequacy_gen Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}
    (* the PROGRAM's descriptor-table class: [xv6Σ] supplies it, and the
       user slot minted during boot is allocated at it.  NAMED, because the
       boot application below is explicit ([@]) and passes it positionally. *)
    `{Hufd : !ufdG Σ}
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (* THE APPLICATION'S FILE-SYSTEM SIDE (claude-notes/projects/
       app-instances.md sections 1-3, round C): its predicate on the
       abstract state's view, the TRANSPORT ([Happ_xfer]: what copies its
       claim onto each fresh durable instance -- the PowerOn clone in
       [Hswap] below, the commit's snapshot in the file system's law), its
       ERA-0 claim ([Happ_init], packed into the initial composite slot
       beside the image's snapshot) and the FIRST PROCESS'S EXEC BUNDLE
       ([Hinit_boot], the one thing the application owes the kernel about
       user execution -- see its own paragraph).
       The durable claim rides the crash slot ([xv6_slot]) and the lend
       ([Rb] below); the boot founds the era's running one from the lend.
       All at the RAW forms over an arbitrary value of the application's
       FIXED PART (app-instances.md section 6 ruling 1, round D0: its
       [Type] [CT], what its birth step [Hbirth] yields, and the step
       itself, run by the power theorem BEFORE the crash slot), because the
       fixed record does not exist yet; once its shape is destructed below,
       the raw forms at the record's [c] ARE [xv6_boot_era]'s pinned ones
       by iota.  The generic application is [unit] / [fun _ => True] /
       [fun _ _ _ => True] / [emp] / [init_boot_of_sup] (the instances
       after this theorem). *)
    (CT : Type) (Cl : CT -> iProp Σ)
    (Hbirth : ⊢ |==> ∃ c : CT, Cl c)
    (app_names : Type) (app_fs : CT -> app_names -> gmap Z FsAbsDefs.anode -> iProp Σ)
    (* THE FIRST PROCESS'S BOOT RESOURCE (lane APP-IFACE item (a),
       review-echo-plan finding 6): what the application hands the era's
       <init> beside the era's claim, at the era's own instance.  For the
       generic application it is [emp]; for the echo application it is the
       console-absence key /init's first [open] runs on.  It cannot ride
       [Happ_init] -- the machine starts powered OFF, so EVERY boot, era 0's
       included, takes its claim off the PowerOn arm's clone and never off
       [Happ_init]'s instance -- and it cannot be read out of the claim,
       being exclusive.  So its producer is the TRANSPORT. *)
    (app_boot : CT -> nat -> app_names -> iProp Σ)
    (* THE OUTPUT PREDICATE, at the fixed part (app-echo.md, lane OUT-FUPD).
       The transmit side's twin of the tag family: what the application
       claims of the bytes the CONSOLE UART has accepted, read against an
       input-history prefix of the run.  The console port's invariant
       carries it ([WpUart.uart_out_claim] inside [WpUart.uart_colE]) and
       the one transmit store re-establishes it from the writer's own view
       shift; the kernel's port carries [emp] instead
       ([WpUart.chist_at]).  A RESOURCE and not a [Prop]
       ([RiscvPtsto.riscv_cons_res]), TIMELESS so the device invariant's body
       still strips its later; its FOUNDING is the application transport's
       ([app_xfer_boot_raw]'s third component), which is why there is no
       founding premise here -- and which is why it is DECLARED BEFORE
       [Happ_boot], whose statement names it. *)
    (* THE APPLICATION'S CONSOLE INTERFACE (redesign R4), at the fixed
       part: the tag family every kernel contract that carries a tag reads,
       the credential a kill pays with, and the claim about the console
       boundary -- ONE argument where there were three with five instance
       arguments beside them, and ONE equation at [Hinit_boot] and
       [Happ_echo] where there were three.  DECLARED BEFORE [Happ_boot],
       whose statement names the claim, and before [Hinit_boot], whose
       equation names the interface. *)
    (Ai : CT -> app_iface Σ)
    (* ...and the ERA'S TURN, which is no field at all: the application's
       per-era credential for <init>, produced by the same power-on step and
       delivered to [Hinit_boot] below.  [App.xv6_app]'s [app_turn]. *)
    (Tnn : CT -> nat -> iProp Σ)
    (* THE TRANSPORT (app-instances.md round C, section 1; section 6 ruling
       5): a copy of the claim can be made at fresh instance names without
       spending the original, under the later every crossing hands it over
       at.  It is what copies the running claim onto each commit's snapshot
       and the crash slot's claim onto each PowerOn clone.
       SINCE lane APP-IFACE item (a) it also hands the clone its own boot
       resource; [app_xfer_raw_of_boot] is the old obligation, which is what
       the commit's law and the era mint keep taking. *)
    (Happ_boot : forall (c : CT) (k : nat),
       ⊢ app_xfer_boot_raw (app_fs c) (app_boot c k))
    (* ERA 0 (round C, section 1): the claim at the IMAGE's own abstract
       state -- the one snapshot in the tree with no source instance -- at
       some instance; packed against the image snapshot's guest half into
       the initial crash slot *)
    (Happ_init : forall c : CT,
       ⊢ |==> ∃ r : app_names,
           app_fs c r (FsAbsDefs.abs_view
             (fss_inodes (FsDurImg.img_state
                (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))))

    (* ...AND THE ONE OBLIGATION THAT MAKES IT PAYABLE (K1): the
       application's SUPPLY -- "the claim holds of every view", which is
       what an unconstraining application hands the generic slot -- buys
       the credential.  This is what lets the GENERIC user-execution slot
       pay the kill price at a trap the kernel cannot rule out, without any
       verified program being charged: the generic slot already runs on the
       supply ([UexecExecInst.xv6_ssupply]), so the credential rides it.
       For echo the credential IS the taint and this is
       [AppEcho.echo_taint_of_sup]; for the generic application both sides
       are [True].  PERSISTENT in the conclusion, because every party a kill
       touches keeps a copy. *)
    (Hkill_sup : forall (c : CT) (r : app_names),
       AppInv.app_sup_raw (app_fs c) r ⊢ □ ai_kill (Ai c))
    (* WHAT HOLDING THE APPLICATION'S SUPPLY ENTITLES A PROCESS TO (lane
       OUT-FUPD, the generic write's payment): the kernel's generic supply
       carries an OUTPUT LICENCE ([WpUart.cons_licence]) and this sets its
       price.  [App]'s [al_sup] is this obligation. *)
    (* ONE LICENCE (redesign R2), covering the generic [write(2)]'s byte,
       consoleintr's shift and [read(2)] on fd 0 alike: all three are
       events on one resource.  [App]'s [al_sup] is this
       obligation, and [al_sup] is gone. *)
    (Hout_sup : forall (c : CT) (r : app_names),
       AppInv.app_sup_raw (app_fs c) r
         ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
                (ev : ConsLog.cons_ev),
                ai_cons (Ai c) k h H ==∗
                ai_cons (Ai c) k h (ConsLog.cons_step H ev)))
    (* THE FIRST PROCESS'S EXEC BUNDLE (ARM-c): the ONE thing the
       application owes the kernel about user execution.  The kernel mints
       no user-execution slot; the first process's comes out of the
       kexec("/init") forkret's boot arm runs, answered by this bundle's
       own slot piece.  [xv6_boot_era]'s [Hinit_boot] carries the
       paragraph on why this is not the GAP-premise trap; the generic
       application discharges it by [init_boot_of_sup], a constraining one
       by its pinned bundle at "/init".
       QUANTIFIED OVER THE GHOST RECORD AND THE ERA'S CLASSES the way
       [Hperm] is -- none of them exists where this theorem is stated. *)
    (* ...AND, SINCE lane APP-IFACE, WITH TWO MORE THINGS THE BOOT HAS AND
       THE FIRST PROCESS'S PROOF NEEDS.  (b) THE RX-TAG EQUATION: the
       machine's ambient input-tag family IS the application's, which this
       theorem's own [boot_fixedGS] literal fixes -- a fact about the
       instance the theorem is taken at, not an assumption about the world,
       and the premise a pinned <init> discharges [UConsLine.ush_tag_law]
       from.  (a) THE BOOT RESOURCE, LINEARLY, at the same instance the
       record equation names. *)
    (Hinit_boot :
       forall (HR : riscvGS Σ) (GEN : GenId)
              `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
                HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
              (c : CT) (r : app_names),
         @file_app Σ HF = MkAppcfg app_names (app_fs c) r ->
         (* ...and (b'') THE INTERFACE EQUATION (redesign R4): the machine's
            ambient tag family, kill credential and console claim ARE the
            application's, which this theorem's own [boot_fixedGS] literal
            fixes.  ONE equation where there were three -- a discharge that
            reads only the tag derives it by [rewrite /riscv_rx_tag Hiface].
            It is what lets a pinned <init> turn [Hout_sup] into the
            machine's licence and build its own generic slot. *)
         @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = Ai c ->
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
         ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot c (Datatypes.S gen_id) r -∗
           (* ...AND THE ERA'S TURN (lane CONS-IO milestone F), beside the
              boot resource: the application's own per-era credential,
              minted at the power-on step and handed to <init>. *)
           Tnn c (Datatypes.S gen_id) -∗
           |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) ProcDefs.secc_all fdt0)
    (* THE ECHO'S JUSTIFICATION (lane OUT-FUPD, F3), the SECOND thing the
       application owes the kernel about the console.  consoleintr echoes
       an input byte through consputc at [Uart0] -- the port whose
       invariant carries the application's own output claim -- from the
       interrupt path, which holds nothing it could pay the store's view
       shift with.  So the payment is the application's: it is minted once
       into [SpecConsoleintr.console_caps] at main and persistent, so every
       byte's echo re-uses it.  Stated at the same two record equations
       [Hinit_boot] takes, because the shift reads the machine's ambient tag
       family and its ambient output claim and both ARE the application's
       at the [boot_fixedGS] literal this theorem builds.  Quantified over
       the context: nothing in the shift is context-relative, and the boot
       chain runs at the boot hart's own [CtxId]. *)
    (Happ_echo :
       forall (HR : riscvGS Σ) (c : CT),
         (* the shift reads the ambient tag family and the ambient console
            claim; ONE equation carries both (redesign R4) *)
         @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = Ai c ->
         ⊢ ∀ (GEN : GenId) (XI : CurCtx), @cons_echo_shift Σ HR GEN XI)
    (* THE TRACE INVARIANT, PASSED THROUGH TO
       [RiscvAdequacy.riscv_power_adequacy] (whose header is the full
       story).  [phi] is any pure statement about the OPERATIONAL state, and
       [Hphi] proves it from the two things adequacy holds at every point of
       the trace: [state_interp] -- the only bridge between the logic and
       [gstate] -- and the fixed-layer crash invariant, whose predicate here
       IS the file system's durability record [FsCrash.P_fs_named].  The
       conclusion then carries [phi] at EVERY reachable state, not just at
       the boot states [Ppure] is delivered to.

       Stated at the [boot_fixedGS] literal, exactly as the theorem below
       consumes it, so every field projection reduces by iota; the client
       never has to see a [riscvFixedGS] it did not build. *)
    (* THE TRACE SLOT AND ITS HOOKS, PASSED THROUGH (uart-trace.md): the
       predicate, its birth, its power hook, and the UART thread's permit
       it discharges -- each stated at this file's own record literal, as
       [Hphi] is.  [xv6_power_adequacy] below fills the slot with the
       trivial predicate, [xv6_trace_adequacy] with a client's ledger. *)
    (Pt : gname -> CT -> iProp Σ)
    (* ...the second argument is the application's FIXED PART
       (app-instances.md section 6 ruling 1): born by [Hbirth] before the
       crash slot, and its yield owned by the trace slot from birth *)
    (HPt : forall (γobs : gname) (c : CT),
       Cl c ∗ ghost_var γobs (1/2) ([] : list mobs)
         ⊢ |==> Pt γobs c)
    (* ...AND ON THE POWER-ON ARM IT FOUNDS THE ERA'S TWO PORT CLAIMS (lane
       CONS-IO milestone E): the transport founded them until e5-design
       REVISION 8 showed the founding was derivable from nothing there, so
       it moved to the one step that runs the client's trace slot once per
       era.  [RiscvAdequacy.power_boot_res] carries the yield to the boot. *)
    (Hobs : forall (γd γobs : gname) (c : CT) (h : list mobs) (on : bool)
                   (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ disk_img_auth_sized γd XV6_DISK_BYTES dk -∗ ▷ Pt γobs c -∗
         ghost_var γobs (1/2) h ==∗
           ◇ (disk_img_auth_sized γd XV6_DISK_BYTES dk ∗ ▷ Pt γobs c ∗
              ghost_var γobs (1/2)
                (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
              (if on then emp
               else ai_cons (Ai c) (Datatypes.S (obs_boots h)) []
                      (LogEntryDefs.MkCH [] [] [] None) ∗
                    (* ...AND THE ERA'S TURN (lane CONS-IO milestone F),
                       the same arm's other yield: it goes to <init>. *)
                    Tnn c (Datatypes.S (obs_boots h)))))
    (* ...AND SINCE lane APP-IFACE item (c) (review-echo-plan finding 3) IT
       IS STATED AT THE ERA'S OWN UART NAMES.  It used to be quantified over
       an ARBITRARY [γ : uart_names], and a ledger's tx/rx wands inherit that
       quantifier -- so no ledger resource could be about THE ERA's UART
       ghosts at an event ([SystemUartAccepted.v]'s header).  The era's ghost
       classes and the two equations the boot HAS -- the era's application
       record, and [fsc_uart], which is the [γ] every kernel-side UART fact
       in the era is stated at -- are exactly [Hinit_boot]'s shape. *)
    (Hperm : forall (HR : riscvGS Σ) (GEN : GenId) `{HF : !fileG Σ}
                    (r : app_names) (i : uart_id) (γ : uart_names),
       (exists (Hinv : invGS Σ) (γgen γstart γreg γd γsw γobs γhist : gname)
               (c : CT) (T : list mobs),
          riscv_fixedGS =
            boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
              (xv6_slot app_names app_fs cov (FsImg.sb_logstart sb)
                 γd γsw γreg γstart c)
              γobs T (Pt γobs c) γhist (Ai c) CT c
          /\ @file_app Σ HF = MkAppcfg app_names (app_fs c) r
          /\ (i = Uart0 -> FsCfg.fsc_uart = γ)) ->
       ⊢ obs_inv -∗ uart_obs_permit i γ)
    (phi : gstate -> list mobs -> Prop)
    (* ...the slot [Hphi] holds at the end of the run is the COMPOSITE
       (round C): the application reads its durable claim off it beside the
       file system's record and the ledger *)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γsw γobs γhist : gname) (c : CT)
                   (T : list mobs) (g' : gstate) (h : list mobs),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (xv6_slot app_names app_fs cov (FsImg.sb_logstart sb)
                  γd γsw γreg γstart c)
               γobs T (Pt γobs c) γhist (Ai c) CT c) g' -∗
         ghost_var γobs (1/2) h -∗ ⌜obs_wf h g'⌝ -∗
         ▷ xv6_slot app_names app_fs cov (FsImg.sb_logstart sb)
             γd γsw γreg γstart c -∗
         ▷ Pt γobs c -∗
         ◇ ⌜phi g' h⌝)
    (* the hypotheses about the machine: it is off, and nothing has ever
       run.  Everything else a boot needs -- RAM total and holding the loaded
       kernel image, the per-hart reset registers, the reset devices -- is
       supplied per ERA by [RiscvLang.boot_shape], which the power thread's
       PowerOn transition establishes itself. *)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* ...AND ONE ABOUT THE DISK, AND IT IS ONE EQUATION ABOUT [g]
       (durable-disk lane E-himg): the machine the system is switched on
       with carries the file system's image.  NOTHING IS ASSUMED ABOUT ANY
       LATER ERA -- what a later boot finds is whatever the previous era
       committed, and that the committed view is still a file system is what
       [FsCrash.P_fs]'s durable snapshot says and what [fs_boot_pure]
       delivers into every boot.  The conclusion mentions none of it, so
       this is the price of a NON-VACUOUS boot cone, not a weaker theorem
       about reducibility.  the corollary at the bottom of this file discharges it at the literal
       mkfs image. *)
    (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
              sb nib cov) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2 κs.
Proof.
  (* THE CRASH SLOT IS NO LONGER [True] HERE, AND THE STATEMENT IS UNCHANGED
     (fs-cfg-boot.md stage (f)).  This theorem used to instantiate
     [Pc := fun _ => True] -- "never stuck, nothing claimed about a power
     cycle".  It cannot any more: the boot cone now builds
     [FirstTok.first_boot_persist], whose seventh row is
     [FsCrash.fs_crash_seam], and at a constant-[True] slot that seam is
     FALSE (it would have to produce [P_fs] out of [True]).

     So the slot is filled with the FS record here too, and the recovery
     obligation that comes with it is DISCHARGED rather than assumed:
     [FsCrash.fs_recovery_total] says every disk image recovers to SOME
     committed state, which is all [P_fs_alloc] needs.  What this theorem
     says about a power cycle is still nothing, because [D0] is existential
     and never mentioned again -- [xv6_fs_adequacy_xv6Σ] at the bottom of
     this file is the one that makes a claim at every reachable state, by
     instantiating [phi] at the crash predicate's own pure content. *)
  destruct (fs_recovery_total (fs_blocks (v_disk (g.(gdev).(dvirtio))))
              cov (FsImg.sb_logstart sb)) as [D0 Hrec].
  (* the durable disk's extent, and the three ERA-INDEPENDENT facts about
     the covered range, all read off the initial machine's image *)
  pose proof (cov_facts_of_image _ _ sb nib cov Himg)
    as (Hcovin & Hlogsub & Hls2).
  assert (Hext : fs_extent cov (FsImg.sb_logstart sb) XV6_DISK_BYTES).
  { pose proof Himg as Hw.
    destruct Hw as (Hwf & _ & _ & _ & _ & Hnibeq & Hcin & Hcmeta & _).
    exact (FirstTok.fs_extent_of_image _ _ _ _ _ Hwf Hnibeq Hcin Hcmeta). }
  (* ...and the header invariant [P_fs_alloc] now carries (stage B's
     [hdr_wf]): the image's log is clean, so [hdr_wf_zero] closes it.  The
     boot state's disk IS [g]'s ([virtio_reset] keeps [v_disk]), so the
     image sweep applies by conversion. *)
  assert (Hhwf : hdr_wf (fs_blocks (v_disk (g.(gdev).(dvirtio)))) cov
                   (FsImg.sb_logstart sb)).
  { pose proof Himg as Hw.
    destruct Hw as (Hwf & _).
    apply hdr_wf_zero. rewrite /log_hdr_bno /hdr_n.
    exact (FsImg.fsimg_wf_log _ _ Hwf). }
  (* ...AND THE DURABLE SNAPSHOT ITSELF (lane CE, re-pointed by lane H5):
     [FsCrash.P_fs] carries one copy of the file-system predicate at the
     committed map, so the era-0 mint needs THE EPOCH, not a pure tie.  The
     image's log is clean, so [D0] is exactly its home blocks, and
     [FsDurImg.img_P_dur_alloc] -- the tree's ONE value-first allocation,
     over [FsDurAlloc]'s carve -- builds it.
     THIS IS THE ONLY PLACE THE IMAGE DECODER IS READ: every later era's boot
     re-founds the file system from the snapshot the previous era committed. *)
  assert (Hsnap0 : ⊢ |==> ∃ gt : gname,
            P_dur_at gt D0 ∗
            snap_guest gt (fss_inodes (FsDurImg.img_state
               (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib))).
  { pose proof Himg as Hw.
    assert (Hclean : hdr_n (fs_blocks (v_disk (g.(gdev).(dvirtio)))
                              (log_hdr_bno (FsImg.sb_logstart sb))) = 0).
    { rewrite /hdr_n /log_hdr_bno.
      exact (FsImg.fsimg_wf_log _ _ (proj1 Hw)). }
    rewrite (proj1 (fs_recovery_clean _ D0 cov (FsImg.sb_logstart sb) Hclean)
               Hrec).
    exact (img_P_dur_alloc _ XV6_DISK_BYTES sb nib cov Hw). }
  (* THE CRASH PREDICATE AT ERA 0: the record from mkfs's recovery fact,
     and the DURABLE DISK's fragments -- the whole [0, XV6_DISK_BYTES) of the
     initial image, handed over once by the power theorem and owned by the
     predicate from here on (design/crash.md, "The durable disk").  This is
     the only place the initial image is ever named. *)
  intros n κs t2 g2 Hn.
  refine (riscv_power_adequacy Σ boot_D NPROC XV6_DISK_BYTES g
           (* THE APPLICATION'S BIRTH STEP, straight through: the power
              theorem runs it first (app-instances.md section 6 ruling 1) *)
           CT Cl Hbirth
           (* THE COMPOSITE SLOT (round C): the record at its snapshot's map
              name, beside the application's durable claim at that name, at
              the application's fixed part [c] *)
           (xv6_slot app_names app_fs cov (FsImg.sb_logstart sb))
           (* ERA 0: the record from mkfs's recovery fact and the image's
              snapshot, whose guest half packs the application's era-0
              claim ([Happ_init]) *)
           ltac:(intros γd γsw γreg γst c; iIntros "(Hfr & Hsw)";
                 iMod (P_fs_alloc γsw γreg γst _ D0
                         (FsDurImg.img_state
                            (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib)
                         cov (FsImg.sb_logstart sb) Hrec Hhwf Hsnap0
                         with "Hsw") as (γs gt) "(%Hseq & HP & Hguest & _)";
                 iMod (Happ_init c) as (r) "Hcl";
                 iModIntro; rewrite /xv6_slot; iExists gt;
                 iSplitR "Hguest Hcl";
                 [ rewrite /P_fs_named_at;
                   iExists (v_disk (g.(gdev).(dvirtio))); iFrame "Hfr";
                   iSplitR; [iPureIntro; exact Hext |];
                   rewrite /P_fs_rec_named_at; iExists γs;
                   iSplitR; [iPureIntro; exact Hseq | iExact "HP"]
                 | iEval (rewrite /snap_guest) in "Hguest";
                   rewrite /app_dur_raw;
                   iExists r, (fss_inodes (FsDurImg.img_state
                      (fs_blocks (v_disk (g.(gdev).(dvirtio)))) sb nib));
                   iSplitL "Hguest"; [iExact "Hguest" | iExact "Hcl"] ])
           (* THE PURE PROJECTION (stage H0): the crash predicate's own
              reading of the physical disk, at every era.  [P_fs_project] IS
              the obligation on the file system's half -- the durable auth
              is lent for the one agreement that identifies [P_fs]'s image
              with the machine's, and nothing is spent; the application's
              conjunct is framed ([xv6_slot_project]). *)
           (fs_boot_pure cov (FsImg.sb_logstart sb))
           (xv6_slot_project app_names app_fs cov (FsImg.sb_logstart sb))
           (* CUSTODY AT BIRTH (durable-disk 1a): the era's mirror is the
              picture of the era's own disk, and [P_fs_swap] IS the hook's
              obligation -- it installs [P_fs]'s custody arm at that
              variable in the same fupd, so the era boots already holding a
              true picture and the swap receipt. *)
           (fun dk => mirror_of (fs_blocks dk))
           (* THE LENT RESOURCE (durable-disk BT-2): THE CRASH PREDICATE'S
              OWN EPOCH, at the map the machine's disk recovers to.  This
              is the whole boot-side transport: [P_fs_swap] runs at the
              PowerOn arm with [crashN] open and the fixed disk auth in
              hand -- the one place [dk] is the MACHINE's -- takes the
              epoch out through [FsCrash.P_fs_dur_acc], clones it with
              [FsDurSnap.P_dur_clone] (the transport at [q = 1], which
              costs no new pure premise) and closes the accessor, so the
              record keeps its own and the era gets a copy.  Its [D] is
              pinned to the boot's own by [fs_recovery_det], which is why
              no state-determinacy theorem is needed.  [xv6_boot_era]
              splits it off [power_boot_res] and hands its contents to the
              mint (durable-disk BT-3). *)
           (* ...BESIDE THE APPLICATION'S DURABLE CLAIM (app-instances.md
              round C, section 3 crossing 2): [P_fs_swap] clones the record's
              snapshot and hands the clone's guest half out at the slot's
              own map; the transport ([Happ_xfer]) copies the slot's claim
              under its later; the copy packs onto the clone's half and
              rides the lend, the original goes back into the slot. *)
           (* ...AND THE BOOT RESOURCE BESIDE IT (lane APP-IFACE item (a)):
              the clone's instance is EXPOSED here, because what the boot
              hands the first process is at that instance and nothing else
              ties the two. *)
           (* ...AND AT THE ERA'S NUMBER (lane CONS-IO milestone C): the
              boot resource is era-indexed, and the era this lend is
              produced for is [gen], so [Rb] is a function of the
              generation.  [S gen] is the era's index -- the machine powers
              on at [ggen = gen], and [ObsTrace.obs_wf] then reads
              [obs_boots h = gen + 1] at every history of the era. *)
           (* NO PORT CLAIMS ON THE LEND (lane CONS-IO milestone E): the
              transport founded them here until e5-design REVISION 8 showed
              that a founding through [app_xfer_boot_raw] is derivable from
              nothing.  They are the application's yield at the POWER-ON
              step now, and they ride [power_boot_res] itself. *)
           (fun c k dk => ∃ (gt : gname) (r : app_names),
              P_fs_lend_at gt cov (FsImg.sb_logstart sb) dk ∗
              ▷ app_dur_at (app_fs c) gt r ∗ app_boot c (Datatypes.S k) r)%I
           ltac:(intros γd γsw γreg γst c Er gen dk; cbv beta;
                 iIntros "#Hreg #Hst Hsa Ha HM HP";
                 rewrite /xv6_slot; iDestruct "HP" as (gt) "[HP HG]";
                 iMod (app_dur_raw_open with "HG") as (r I) "[Hh Hcl]";
                 iMod (P_fs_swap gt γd XV6_DISK_BYTES γsw γreg γst cov
                         (FsImg.sb_logstart sb) dk Er gen I
                         with "Hreg Hst Hsa Ha HM [Hh] HP")
                   as ">(Hsa & Ha & HP & HM & #Hsw & Hh & Hl)";
                 [rewrite /snap_guest; iExact "Hh" |];
                 iPoseProof (Happ_boot c (Datatypes.S gen)) as "#Hxfer";
                 iEval (rewrite /app_xfer_boot_raw) in "Hxfer";
                 iMod ("Hxfer" with "Hcl") as "[Hcl Hnew]";
                 iDestruct "Hnew" as (rnew) "[Hnew Hbnew]";
                 iDestruct "Hl" as (gt') "[Hl Hg']";
                 iEval (rewrite /snap_guest) in "Hh Hg'";
                 (* NO BARE [iFrame] PAST THE SLOT (durable-notes: "[iFrame]
                    resolves its instances up to delta"): the slot's record
                    owns the durable disk's 2 MB byte big-op behind a
                    [Definition], and a frame that has to pass it to reach
                    a later conjunct unfolds it -- measured unbounded.
                    Every conjunct is placed by name. *)
                 iModIntro; iModIntro;
                 iSplitL "Hsa"; [iExact "Hsa" |];
                 iSplitL "Ha"; [iExact "Ha" |];
                 iSplitL "HP Hh Hcl";
                 [ iNext; iExists gt; iSplitL "HP"; [iExact "HP" |];
                   rewrite /app_dur_raw; iExists r, I;
                   iSplitL "Hh"; [iExact "Hh" | iExact "Hcl"] |];
                 iSplitL "HM"; [iExact "HM" |];
                 iSplitR; [iExact "Hsw" |];
                 iExists gt', rnew; iSplitL "Hl"; [iExact "Hl" |];
                 iSplitL "Hg' Hnew";
                 [ iApply (app_dur_at_pack with "Hg' Hnew")
                 | iExact "Hbnew" ])
           (* THE TRACE SLOT AND THE TRACE HOOK, threaded straight through:
              this layer fixes the crash predicate but says nothing about the
              trace, so both pass down unexamined. *)
           Pt Ai Tnn HPt Hobs phi Hphi
           Hgen0 Hpow _ n κs t2 g2 Hn).
  (* the per-era boot entailment, at the era instance the power thread just
     minted.  [riscv_fixedGS (RiscvGS Σ F HE)] iota-reduces to [F] and
     [riscv_eraGS] to [HE], so §2's statement at the composed instance IS
     this obligation (crash.md's M0 gotcha, in the direction that works). *)
  intros F HE gen g' Hbf Hpure Hi Gg Gs Gr Gt Gsw Gob Ghist Gcl GT Hfix.
  (* THE INTERFACE EQUATION (redesign R4, on lane APP-IFACE item (b)'s
     mould), read off the record BEFORE it is substituted away: the equation
     is a projection of the literal this theorem itself builds, so it is
     [reflexivity] once the field is exposed -- but the [Hinit_boot]
     application below names the record through an evar, at which no
     projection reduces, so the fact has to be a NAMED hypothesis rather
     than an [eq_refl] in the term.  ONE assertion where there were three:
     the tag family, the kill credential and the console claim are
     projections of it. *)
  assert (Hifacefix : @riscvF_app_iface Σ F = Ai Gcl)
    by (rewrite Hfix; reflexivity).
  (* ...AND ITS TWIN FOR THE GENERATION COUNTER (lane APP-IFACE (b')), read
     off the same literal and for the same reason: [boot_fixedGS] resolves
     the anonymous class slots from [riscvGpreS], so the fixed layer's
     counter IS the pre-structure's here. *)
  assert (Hgenfix : @riscvF_genGS Σ F = riscv_pre_genGS)
    by (rewrite Hfix; reflexivity).
  subst F.
  (* THE RECORD'S SHAPE, substituted: every projection below reduces, which
     is what makes the crash slot's value -- and hence the seam -- visible
     to the boot cone at all.  [RiscvAdequacy.boot_fixedGS]'s header is the
     argument for why an equation about [riscv_crash_pred] alone would not
     do (the ghost CLASS instances have to agree too). *)
  (* one [_] fewer since durable-disk 2b-inode-3: [fsTopG] is an [xv6G]
     member now, so the section generalises one class less. *)
  (* one [_] MORE since the program's descriptor class ([UserFd.ufdG]) joined
     the section: this application counts them positionally. *)
  (* ...and one more again since the children map's camera
     ([Xv6Cameras.wchGpreS]) joined it: the boot fupd is what mints the map
     and its NPROC rows ([WaitInv.children_res_alloc]). *)
  (* the application's data and obligations, APPLIED at the era's fixed part
     [Gcl] (round D0): below the boot nothing names the record's
     [riscv_client], so they are terms here, not holes *)
  refine (@xv6_boot_era Σ (RiscvGS Σ _ HE) _ Hufd _ _ _ _ _ _ gen g' sb nib cov
            app_names (app_fs Gcl) (app_boot Gcl)
            (Tnn Gcl (Datatypes.S gen))
            (app_xfer_raw_of_boot _ _ (Happ_boot Gcl (Datatypes.S gen)))
            (fun HBs HFd HIr HPav HWc HF r Hr =>
               Hinit_boot (RiscvGS Σ _ HE) gen HBs HFd HIr HPav HWc HF Gcl r
                 Hr Hifacefix Hgenfix)
            (Happ_echo (RiscvGS Σ _ HE) Gcl Hifacefix)
            Hbf Hpure Hcovin Hlogsub Hls2 _ _).
  (* the descriptor class comes back as a GOAL here rather than being
     shelved, because the application is explicit ([@]); it is the section's
     own instance. *)
  { reflexivity. }
  (* the UART thread's permit, at the record the era boots over *)
  intros HF r i γ Happ Huart.
  apply (Hperm _ gen HF r i γ).
  exists Hi, Gg, Gs, Gr, Gt, Gsw, Gob, Ghist, Gcl, GT.
  split_and!; [reflexivity | exact Happ | exact Huart].
Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. THE TWO INSTANCES OF THE TRACE SLOT.                                *)
(*                                                                        *)
(* [xv6_power_adequacy] is the theorem as it was before the trace layer:   *)
(* the slot at the TRIVIAL predicate, [phi] about the state alone, the     *)
(* conclusion over [rtc erased_step].  [xv6_trace_adequacy] is the         *)
(* packaged trace theorem at xv6: a client's timeless trace resource [R],  *)
(* its birth, its power step, its two UART-arm wands and its pure reading  *)
(* [P], and the conclusion is [P] of the run's observable trace.           *)
(* ---------------------------------------------------------------------- *)
Theorem xv6_power_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}
    (* the program's descriptor-table class -- supplied by [xv6Σ] *)
    `{!ufdG Σ}
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (phi : gstate -> Prop)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γd γsw γobs γhist : gname) (c : unit)
                   (T : list mobs) (g' : gstate),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (xv6_slot unit (fun _ _ _ => True%I) cov (FsImg.sb_logstart sb)
                  γd γsw γreg γstart c)
               γobs T (obs_pred_at γobs) γhist (app_iface_triv Σ) unit c) g' -∗
         ▷ xv6_slot unit (fun _ _ _ => True%I) cov (FsImg.sb_logstart sb)
             γd γsw γreg γstart c -∗
         ◇ ⌜phi g'⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
              sb nib cov) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
Proof.
  intros t2 g2 Hrtc.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hn).
  refine (xv6_power_adequacy_gen Σ g sb nib cov
            (* the GENERIC application (applications.md section 0): no fixed
               part, any abstract state, nothing lent, the supply outright *)
            unit (fun _ => True%I)
            ltac:(iModIntro; iExists (); iPureIntro; exact Logic.I)
            unit (fun _ _ _ => True%I)
            (fun _ _ _ => emp%I)
            (fun _ : unit => app_iface_triv _)
            (fun (_ : unit) (_ : nat) => emp%I)
            ltac:(intros c k; apply app_xfer_boot_raw_triv;
                  intros r av; reflexivity)
            ltac:(intros c; cbv beta; iModIntro; iExists ();
                  iPureIntro; exact Logic.I)
            ltac:(intros ci ri; iIntros "_"; iModIntro; done)
            ltac:(intros ci ri; rewrite /ai_cons /app_iface_triv /cons_res_triv;
                  iIntros "_ !>" (k h H ev) "_"; by iModIntro)
            ltac:(intros HRi GENi HBsi HFdi HIri HPavi HWci HFi ci ri
                         Heq Hiface Hgeni;
                  iIntros "_ _ _"; iModIntro; iApply init_boot_of_triv;
                  [ rewrite Heq; intros r' av; reflexivity
                  | rewrite /app_taint Hiface; reflexivity ])
            (* THE ECHO'S JUSTIFICATION, at the TRIVIAL console claim: every
               link is free, so the echo justifies itself. *)
            ltac:(intros HRi ci Hifacei; iIntros (GEN XI);
                  iApply (cons_echo_shift_triv (XI := XI));
                  rewrite /riscv_cons_res Hifacei; reflexivity)
            (fun γobs _ => obs_pred_at γobs)
            (obs_pred_at_alloc_cl (fun _ : unit => True%I))
            (fun γd γobs _ =>
               obs_pred_at_step XV6_DISK_BYTES cons_res_triv
                 (fun _ => emp%I)
                 (cons_res_triv_founded Σ) (turn_triv_founded Σ) γd γobs)
            _ (fun g _ => phi g)
            ltac:(intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h;
                  iIntros "Hsi _ _ HP _";
                  iApply (Hphi Hinv γgen γstart γreg γd γsw γobs γhist c T g'
                            with "Hsi HP"))
            Hgen0 Hpow Himg n κs t2 g2 Hn).
  (* the permit at the trivial slot *)
  intros HR GEN HFi ri i γ
         (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Ghist & Gcl & GT & Heq & _ & _).
  apply (uart_obs_permit_triv i γ); rewrite Heq; reflexivity.
Qed.

Theorem xv6_trace_adequacy Σ
    `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}
    `{!ufdG Σ}   (* the program's descriptor-table class (from [xv6Σ]) *)
    (g : gstate) (sb : fs_sb) (nib : nat) (cov : gset Z)
    (R : list mobs -> iProp Σ) (HRt : forall h, Timeless (R h))
    (* THE INPUT TAG FAMILY (app-echo.md lane L5): what the client claims of
       each byte the environment pushed, at the history it arrived at.  The
       rx wand below produces it; the machine's ambient slot IS it. *)
    (Tg : list mobs -> iProp Σ) (HTg : forall h, Persistent (Tg h))
    (HTgt : forall h, Timeless (Tg h))
    (* THE OUTPUT PREDICATE (app-echo.md lane OUT-FUPD): what the client
       claims of the bytes the CONSOLE UART has accepted, read against an
       input-history prefix of the run.  The transmit wand below is handed
       it at every drain, together with the fact that the witness history is
       a prefix of the run's own; the writers re-established it at each
       store. *)
    (* ONE CLAIM OVER THE WHOLE CONSOLE HISTORY (redesign R2): what the
       client claims of the bytes the console UART has accepted, of the
       inputs it logged and of the ones a process has been given. *)
    (Cres : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ)
    (HCrest : forall k h H, Timeless (Cres k h H))
    (HR0 : ⊢ |==> R [])
    (* THE POWER STEP -- AND THE FOUNDING OF THE ERA'S TWO PORT CLAIMS
       (lane CONS-IO milestone E, e5-design REVISION 8).  The claims below
       are the client's own and hold its per-era authority, so they cannot
       be founded out of nothing (the transport founded them until E, and a
       transport's [□] over a self-returning bupd makes the founded arm
       derivable unboundedly).  A power-ON starts an era and runs the
       client's ledger, so it is the one step that can mint a LINEAR per-era
       seed; the kernel carries the yield from here to the boot, which
       founds the console port's invariant clause with it.  The era is
       [S (obs_boots h)], the boot count of the POST-event history. *)
    (Hpow : forall (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ R h ==∗ R (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
         (if on then emp
          else Cres (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)))
    (* the two UART-arm steps ([WpUart.uart_obs_permit_ledger]): the byte
       that reached the wire, and the environment's byte -- which also mints
       the byte's tag.  Quantified over the era instance because the fancy
       update needs its [invGS]; the wands themselves mention nothing
       era-specific. *)
    (* AT EVERY PORT: either 16550 may step, and the environment may type
       on the kernel's port at any moment, so the ledger owes an account of
       an event on either wire. *)
    (Htx : forall (HR : riscvGS Σ) (GEN : GenId) (i : uart_id) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
              (ho : list mobs) (H : LogEntryDefs.cons_hist),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
              (* THE WIRE IS THE DRAINED SEQUENCE (the clause TX-TAG left
                 owed): with LOOP off throughout, [u_wire] and [u_out] are
                 the same list, so the wire is a PREFIX of [uart_acc u] and
                 a prefix-closed output claim transfers to it. *)
              ⌜u_wire u = u_out u⌝ -∗
              (* ...AND THE ERA STAMP (lane CONS-IO milestone C): the era
                 this history belongs to is [S gen_id], which is the index
                 the two claims below are read at. *)
              ⌜obs_boots h = S gen_id⌝ -∗
              (* ...AND THE OUTPUT CLAIM ITSELF, at a WITNESS HISTORY the
                 invariant holds a monotone lower bound on -- so [ho] is a
                 real prefix of the run's own history [h], and the client
                 lifts the claim to [h] by its own input-monotonicity.  This
                 is the ONLY channel from the console UART's invariant to
                 the ledger, and hence to [Hphi]. *)
              ⌜ho `prefix_of` h⌝ -∗
              (* ...AND THE ACCEPTED BYTES ARE THE HISTORY'S OWN FIELD
                 (redesign R2), so the tie the drain needs is a premise. *)
              ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
              (* ...TAKEN LINEARLY AND GIVEN BACK: the claim holds the
                 application's authority, so the ledger step reads it
                 against its own ledger and puts it where it found it. *)
              (if i is Uart0 then Cres (Datatypes.S gen_id) ho H else emp) -∗
              uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              (if i is Uart0 then Cres (Datatypes.S gen_id) ho H else emp) ∗
              uart_ghosts γ u' ∗ R (h ++ [ObsUartOut i b])%list))
    (Hrx : forall (HR : riscvGS Σ) (GEN : GenId) (i : uart_id) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              ⌜obs_boots h = S gen_id⌝ -∗
              uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ R (h ++ [ObsUartIn i b])%list ∗
              Tg (h ++ [ObsUartIn i b])%list))
    (* THE ECHO'S JUSTIFICATION (lane OUT-FUPD, F3): consoleintr echoes an
       input byte through consputc at [Uart0], whose invariant carries the
       client's own output claim, and the interrupt path holds nothing it
       could pay the store's view shift with -- so the payment is the
       client's.  Stated at the two record equations the boot has, because
       the shift reads the machine's ambient tag family and its ambient
       output claim and both ARE the client's at the record adequacy
       builds. *)
    (Hecho : forall (HRg : riscvGS Σ),
       (* the shift reads ONE claim (redesign R2) *)
       @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = Cres ->
       @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = Tg ->
       ⊢ ∀ (GEN : GenId) (XI : CurCtx), @cons_echo_shift Σ HRg GEN XI)
    (* WHAT A LEDGER CLIENT OWES ABOUT ITS OWN OUTPUT CLAIM (lane
       OUT-FUPD).  This theorem runs the GENERIC application, so the kernel
       can say nothing at all about [Ores]: the two things the boot and the
       generic user-execution slot need of it are the client's.

       (i) IT HAS TO BE FOUNDED -- BY [Hpow] ABOVE (lane CONS-IO milestone
       E), not here: the founding moved to the power-on step, and the
       TRANSPORT premise this theorem used to take ([Hxfer], the clone at
       the trivial predicate with the two founded claims bolted on) went
       with it.  What is left of the transport is the CLONE, and at the
       generic application the predicate and the boot resource are both
       trivial, so it is [app_xfer_boot_raw_triv] outright and no premise
       at all: a premise provable from nothing is noise on the trusted
       surface.
       (ii) THE GENERIC SLOT'S WRITE HAS TO BE LICENSED.  Every user
       process here runs on the generic user-execution slot, whose
       [write(2)] on the console is paid out of [WpUart.cons_licence]; with
       [Ores] arbitrary only the client can say that its claim survives an
       arbitrary byte.  A client whose claim does NOT survive one does not
       use this theorem: it uses [App.xv6_app_adequacy] with a constraining
       [app_pred], where the SUPPLY is what gates the licence. *)
    (* ONE LICENCE (redesign R2): the client's claim survives any boundary
       event -- the generic slot's [write(2)] byte, consoleintr's shift and
       [read(2)] on fd 0 alike. *)
    (Hout_lic : ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
                       (ev : ConsLog.cons_ev),
                       Cres k h H ==∗ Cres k h (ConsLog.cons_step H ev)))
    (P : list mobs -> Prop) (HR : forall h, R h ⊢ ⌜P h⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
              sb nib cov) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ P κs.
Proof.
  refine (xv6_power_adequacy_gen Σ g sb nib cov
            (* the GENERIC application (applications.md section 0): no fixed
               part, any abstract state, nothing lent, the supply outright *)
            unit (fun _ => True%I)
            ltac:(iModIntro; iExists (); iPureIntro; exact Logic.I)
            unit (fun _ _ _ => True%I)
            (fun _ _ _ => emp%I)
            (* the interface: the CLIENT's tag family and console claim,
               with the trivial credential beside them (redesign R4) *)
            (fun _ : unit =>
               MkAppIface Tg HTg HTgt kill_cred_triv
                 (@kill_cred_triv_persistent _) (@kill_cred_triv_timeless _)
                 Cres HCrest
                 (* the LICENCE law (lane SUP-ONE): the client's own
                    [Hout_lic], which this theorem already takes *)
                 ltac:(iIntros "_"; iApply Hout_lic)
                 (* no masked program: the wild credential is absent *)
                 wild_none (@wild_none_persistent _) (@wild_none_timeless _)
                 (wild_none_lic Cres)
                 wild_none (@wild_none_persistent _) (@wild_none_timeless _))
            (fun (_ : unit) (_ : nat) => emp%I)
            (* THE TRANSPORT IS THE CLIENT'S at this theorem: it is what
               founds the client's own output claim per era. *)
            ltac:(intros c k; apply app_xfer_boot_raw_triv;
                  intros r av; reflexivity)
            ltac:(intros c; cbv beta; iModIntro; iExists ();
                  iPureIntro; exact Logic.I)
            ltac:(intros ci ri; iIntros "_"; iModIntro; done)
            ltac:(intros ci ri; iIntros "_"; iApply Hout_lic)
            (* the first process's slot, on the GENERIC supply and the
               client's own licences *)
            ltac:(intros HRi GENi HBsi HFdi HIri HPavi HWci HFi ci ri
                         Heq Hiface Hgeni;
                  iIntros "_ _ _"; iModIntro; iApply init_boot_of_sup;
                  [ iApply app_sup_of_triv; rewrite Heq; intros r' av;
                    reflexivity
                  | rewrite /app_taint Hiface /= /kill_cred_triv;
                    done ])
            ltac:(intros HRi ci Hiface;
                  exact (Hecho HRi
                           ltac:(rewrite /riscv_cons_res Hiface; reflexivity)
                           ltac:(rewrite /riscv_rx_tag Hiface; reflexivity)))
            (fun γobs _ => obs_ledger_at R γobs)
            (fun γobs _ => obs_ledger_at_alloc_cl R γobs True%I
                             ltac:(iIntros "_"; iMod HR0 as "HR"; by iModIntro))
            (fun γd γobs _ =>
               obs_ledger_at_step XV6_DISK_BYTES R HRt Cres
                 (fun _ => emp%I)
                 ltac:(intros h on dk Hsh; iIntros "HR";
                       iMod (Hpow h on dk Hsh with "HR") as "[HR Hf]";
                       iModIntro; iSplitL "HR"; [iExact "HR" |];
                       destruct on; [done |];
                       iSplitL "Hf"; [iExact "Hf" | done])
                 γd γobs)
            _ (fun _ h => P h)
            ltac:(intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h;
                  iIntros "_ Hauth _ _ HPt";
                  iApply (obs_ledger_at_phi R HRt P HR γobs h with "Hauth HPt"))
            Hgen0 Hpow0 Himg).
  (* the permit at the ledger: the client's two wands *)
  intros HRg GEN HFi ri i γ
         (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Ghist & Gcl & GT & Heq & _ & _).
  refine (uart_obs_permit_ledger i R Tg Cres γ HRt _ _ _
            (Htx HRg GEN i γ) (Hrx HRg GEN i γ));
    rewrite Heq; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. ...and at a CONCRETE functor list, so nothing at all is assumed.     *)
(* ---------------------------------------------------------------------- *)

(* [adequacy_icfg] AND [adequacy_fscfg] ARE GONE, and their deletion is the
   point of fs-cfg-boot.md stage (d2b).  They were two [Local Instance]s of
   all-[1%positive] records -- an [IcacheRefDefs.icfg] with [icfg_nib = 0] and an
   [FsCfg.fscfg] nobody allocated -- and they existed only because [fileG]
   had to be RESOLVED here: nothing in the tree could produce either record,
   so the corollaries below could not be stated without inventing them.  At
   [icfg_nib = 0] an [IcacheHeld.inode_held] cannot exist, so the boot cone's
   one assumed contract ([SpecNameiRootBoot.v]'s [namei("/")]) was VACUOUS at
   exactly the instance the corollaries were taken at.  That was a defect in
   the top-level statement, not a missing convenience.

   [BootShared.boot_shared_alloc] now MINTS both records inside the era fupd
   (off the era's own disk, at the parsed superblock's geometry) and returns
   the reassembled [fileG] existentially, so this file resolves [fileGpreS]
   -- whose only instance is [subG] on the functor list -- and never
   [fileG].  The 400 GB nontermination hazard documented at [adequacy_fscfg]
   goes with it: the cycle it blocked was
   [fileG -> subG_fileΣ -> fscfg -> file_fscfg -> fileG], and with no site
   resolving [fileG] there is nothing to enter it.  The compressed note now
   lives where [FileInvDefs.fileG_of] is APPLIED (BootShared.v §5) and at the
   chain application in §2 above. *)

Definition xv6Σ : gFunctors :=
  (* [ufdΣ] is the PROGRAM's descriptor-table ghost map ([UserFd]): the
     authority rides inside [UkRun.urun] and the handles are what a
     user-level proof carries.  Distinct from [fdslotΣ], which is the
     kernel/process split over the same descriptors. *)
  #[ riscvΣ; xv6GΣ; fileΣ; fdslotΣ; irefslotΣ; pavΣ; wchΣ; ufdΣ ].

(* THE POWER THEOREM AT THE CONCRETE FUNCTOR LIST: every class is
   discharged, so "nothing about the ghost state is assumed" is checked
   rather than claimed.  [Himg] is still a premise -- this corollary does
   not name the literal image.

   IT IS NO LONGER THE ASSUMPTION AUDIT'S TARGET.  [SystemAssumptions.v]
   now audits [xv6_fs_adequacy_xv6Σ] at the bottom of this file, which is
   the theorem with NOTHING left as a premise and so the only one whose
   axiom list is the whole story.  The cost of that is real and expected:
   naming [FsImgDisk.fsimg_dk] pulls Rocq's [PrimString]/[PrimInt63]
   primitives in (MEASURED: ten extra entries, on any constant naming the
   image), so the baseline the audit diffs against is THIRTEEN, not three.
   Those ten are structural -- the same set appears on every literal-image
   theorem ([ElfKernel.v] / [ElfUser.v] / [FsImgCheck.v]) -- and
   durable-notes' "adequacy-print baseline" lists them by name so a reader
   can tell them from a regression. *)

(* ---------------------------------------------------------------------- *)
(* 1.  THE IMAGE'S COVERAGE SET (ruling R4) and the inode-region size.     *)
(*                                                                        *)
(* [fsimg_cov], [fsimg_cov_elem_of] and [fsimg_nib] MOVED DOWN to          *)
(* [FsBootParams.v] (required above): they are definitions over nothing    *)
(* but arithmetic, and the file-system pin files that need only those      *)
(* three no longer import this file to get them.                          *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 2.  THE IMAGE HYPOTHESIS, DISCHARGED.                                   *)
(*                                                                        *)
(* [BootShared.fs_boot_image_wf]'s nine conjuncts at the literal image.     *)
(* Two are [FsImgCheck] citations; the other seven are arithmetic on the    *)
(* superblock's own eight numbers                                          *)
(* ([MkFsSb 0x10203040 2000 1953 200 31 2 33 46]) and on [fsimg_cov]'s      *)
(* membership law.  NO [vm_compute]: [fsimg_P] IS [fs_blocks fsimg_dk] by   *)
(* definition, so the two sweeps are cited, not re-run.                     *)
(* ---------------------------------------------------------------------- *)

(* [2 ^ 32], as a closed equation, so no goal below asks [lia] to evaluate a
   power.  (Conversion, not computation on the image.) *)
Local Lemma two_pow_32 : (2 : Z) ^ 32 = 4294967296.
Proof. reflexivity. Qed.

Local Lemma xv6_disk_bytes_z : Z.of_nat XV6_DISK_BYTES = 2048000.
Proof. unfold XV6_DISK_BYTES. rewrite Nat2Z.inj_mul. reflexivity. Qed.

Lemma fsimg_image_wf :
  fs_boot_image_wf FsImgDisk.fsimg_dk XV6_DISK_BYTES
    fsimg_sb fsimg_nib fsimg_cov.
Proof.
  rewrite /fs_boot_image_wf /fsimg_nib.
  (* (1) W1-W9, cited *)
  split; [exact fsimg_wf_ok |].
  (* (2) the whole [16*nib] region's L3/L4 and free tail, cited *)
  split; [exact fsimg_region_wf |].
  (* (3) the region covers every inum the superblock claims: 200 <= 208 *)
  split; [cbv [fsimg_sb sb_ninodes]; lia |].
  (* (4) and it fits in a 32-bit inum *)
  split; [rewrite two_pow_32; lia |].
  (* (5) it is not empty *)
  split; [lia |].
  (* (6) mkfs rounds [ninodes] up to a whole block: 13 = 200/16 + 1 *)
  split; [cbv [fsimg_sb sb_ninodes]; reflexivity |].
  (* (7) every covered block is a real client block inside the mint *)
  split.
  { intros b Hb. apply fsimg_cov_elem_of in Hb.
    rewrite xv6_disk_bytes_z. lia. }
  (* (8) every METADATA block is covered: block 1 up to the bitmap block *)
  split.
  { intros b Hb. apply fsimg_cov_elem_of.
    cbv [fs_data_start fsimg_sb sb_bmapstart] in Hb. lia. }
  (* (9) ...and every DATA block, up to the superblock's [size] *)
  split.
  { intros b Hb. apply fsimg_cov_elem_of.
    cbv [fs_data_start fsimg_sb sb_bmapstart sb_size] in Hb. lia. }
  (* (10) block 1's bytes ARE the record -- CITED, not recomputed: this is
     [FsImgCheck.fsimg_parse_sb], which the check file already proves.
     [fsimg_P] IS [fs_blocks fsimg_dk] by definition. *)
  split; [exact fsimg_parse_sb |].
  (* (11) the ushort bound: 16 * 13 = 208 <= 65536 *)
  split; [vm_compute; discriminate |].
  (* (12) the image is 2000 blocks: 2048000 = 1024 * 2000 *)
  split; [rewrite xv6_disk_bytes_z; cbv [fsimg_sb sb_size]; lia |].
  (* (13) the file-nlink EQUALITY sweep -- CITED, like (1)/(2)/(10):
     [FsImgCheck.fsimg_links_eq], and [fsimg_P] IS [fs_blocks fsimg_dk]. *)
  split; [exact fsimg_links_eq |].
  (* (14) every FREE record of the region is BARE -- CITED:
     [FsImgCheck.fsimg_region_bare], the same thirteen inode blocks the two
     region sweeps above read. *)
  split; [exact fsimg_region_bare |].
  (* (15) no live non-dot root record names the root -- CITED:
     [FsImgCheck.fsimg_root_no_self], one O(nrec) pass over the root. *)
  exact fsimg_root_no_self.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2b. THE NON-VACUITY WITNESS FOR THE DURABLE SNAPSHOT (plan section 7).  *)
(*                                                                        *)
(* [FsDurImg.img_snap_ok] is hedged behind [fs_boot_image_wf]'s fifteen     *)
(* conjuncts, so the plan's vacuity discipline owes a witness AT THE REAL   *)
(* INSTANCE -- xv6's own superblock layout, not a made-up one.  This is     *)
(* it, and it costs NO computation: it is [fsimg_image_wf] above, whose     *)
(* every image conjunct is a [FsImgCheck] citation.  What it says is that   *)
(* the mkfs image really does denote an abstract file-system state whose    *)
(* encoding is the image's own committed home blocks, with the used-set     *)
(* coupling and the per-inode local clauses -- i.e. that the durable        *)
(* snapshot the WAL carries is not empty at era 0.                          *)
(*                                                                        *)
(* IT MUST BE HERE AND NOT INSIDE A SECTION: a [vm_compute] on a goal       *)
(* containing a section variable hangs (durable-notes.md), and every        *)
(* literal-image fact this cites is already a closed lemma of              *)
(* [FsImgCheck].                                                           *)
(* ---------------------------------------------------------------------- *)
Theorem fsimg_snap_ok :
  snap_ok (img_state fsimg_P fsimg_sb fsimg_nib)
          (fs_restrict fsimg_P
             (fs_home_set fsimg_cov (FsImg.sb_logstart fsimg_sb))).
Proof.
  exact (img_snap_ok FsImgDisk.fsimg_dk XV6_DISK_BYTES fsimg_sb fsimg_nib
           fsimg_cov fsimg_image_wf).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3.  THE TWO COROLLARIES, AT ONE EQUATION ABOUT [g].                     *)
(*                                                                        *)
(* [fsimg_at_every_era] IS GONE (durable-disk lane E-himg), and so is the  *)
(* [SystemAdequacy.fs_boot_image_eras] it was a bridge to.  Both said THE  *)
(* LITERAL IMAGE IS ON THE DISK AT EVERY ERA, which is refutable -- era N's *)
(* disk is whatever era N-1 wrote, so one [create] falsifies it.  The      *)
(* general theorem takes the image ONCE, at the machine the system is      *)
(* switched on with, and every later boot reads its file system off the    *)
(* crash predicate's durable snapshot instead.  So the corollary below     *)
(* assumes exactly what a reader would expect: the initial disk is mkfs's.  *)
(* ---------------------------------------------------------------------- *)

(* THE SYSTEM THEOREM AT THE LITERAL mkfs IMAGE -- the end of the line, and
   the [Print Assumptions] target ([SystemAssumptions.v]).

   NOTHING ABOUT THE FILE SYSTEM IS ASSUMED BEYOND THE INITIAL DISK: the
   one hypothesis is that the machine is switched on with the image mkfs
   built.  [FsImgDisk.fsimg_dk] is kernel-rocq/FsImgRaw.v's 2,048,000
   bytes, zero-padded beyond them (a virtio disk reads zeroes past the file
   backing it, and [XV6_DISK_BYTES] is larger than the image).

   THE PARAMETERS, and why each is what it is:
     [logstart] is pinned to [2], the IMAGE'S OWN [logstart]
       ([FsImgCheck.fsimg_sb_logstart] is what checks that the superblock
       says so);
     [cov] is [fsimg_cov] (section 1), NO LONGER PARAMETRIC: stocking the
       inode pool from the image forces every block a live inode names into
       it;
     [sb]/[nib] are the parsed superblock and its inode region's 13 blocks.

   THERE IS NO [Hrec] TO DISCHARGE.  There used to be: a second generic
   theorem [xv6_fs_adequacy] took mkfs's recovery obligation as a premise
   and this corollary supplied it from [FsImgDisk.fsimg_recovery].  That
   theorem was [xv6_power_adequacy] with two premises its conclusion never
   used -- provable from it by [intros; eapply xv6_power_adequacy;
   eassumption] -- so it is gone, and with it the obligation.  Do not
   reintroduce a "FS-flavoured" generic theorem: the FS content of this
   statement is entirely in [phi], and [phi] is [xv6_trace_pure].

   What the image MEANS as a file system -- [FsImg.fsimg_wf], and that
   /init /sh /echo /sync hold exactly the tracked ELF raws the U-mode proofs
   reason about -- is [iris/FsImgCheck.v], which this file Requires. *)

(* ---------------------------------------------------------------------- *)
(* 4. ...AT THE CONCRETE FUNCTOR LIST *AND* AT THE LITERAL mkfs IMAGE,      *)
(*    with [phi] STILL FREE.                                               *)
(*                                                                        *)
(* Two of the three things the general theorem leaves open are settled     *)
(* here -- the ghost state (every class discharged, so nothing about the   *)
(* ghost state is assumed is CHECKED rather than claimed) and the DISK.    *)
(* [phi] stays open, which is the point: a client with some other pure     *)
(* trace property -- a UART trace, a memory invariant -- instantiates THIS *)
(* and owes nothing about the image.                                      *)
(*                                                                        *)
(* WHY THE IMAGE IS DISCHARGED HERE AND NOT LOWER DOWN.  [Himg] cannot be  *)
(* discharged before the disk is named, and naming it in                   *)
(* [xv6_power_adequacy] would destroy that theorem's generality -- so this *)
(* is the earliest rung where it CAN go, and every statement below is      *)
(* image-free as a result.  The cost is that [sb]/[nib]/[cov] are no       *)
(* longer parameters here: pinning the disk pins them to [fsimg_sb] /      *)
(* [fsimg_nib] / [fsimg_cov].  A client wanting the concrete functor list  *)
(* at some OTHER image goes one rung up to [xv6_power_adequacy], which is  *)
(* still abstract in all three.                                           *)
(* ---------------------------------------------------------------------- *)
Corollary xv6_power_adequacy_xv6Σ (g : gstate)
    (phi : gstate -> Prop)
    (Hphi : forall (Hinv : invGS xv6Σ)
                   (γgen γstart γreg γd γsw γobs γhist : gname) (c : unit)
                   (T : list mobs) (g' : gstate),
       ⊢ @power_interp xv6Σ
            (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
               (xv6_slot unit (fun _ _ _ => True%I) fsimg_cov
                  (FsImg.sb_logstart fsimg_sb) γd γsw γreg γstart c)
               γobs T (obs_pred_at γobs) γhist (app_iface_triv xv6Σ)
               unit c) g' -∗
         ▷ xv6_slot unit (fun _ _ _ => True%I) fsimg_cov
             (FsImg.sb_logstart fsimg_sb) γd γsw γreg γstart c -∗
         ◇ ⌜phi g'⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* THE ONE HYPOTHESIS LEFT, and it is about the HARDWARE SETUP, not the
       file system: the machine is switched on with the disk mkfs wrote. *)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
Proof.
  apply (xv6_power_adequacy xv6Σ g fsimg_sb fsimg_nib fsimg_cov phi Hphi
           Hgen0 Hpow).
  (* THE IMAGE, DISCHARGED: [Hdisk] rewrites the machine's disk to the
     literal image, and [fsimg_image_wf] -- a CLOSED lemma, six [exact]s off
     [FsImgCheck]'s sweeps plus arithmetic -- closes it. *)
  rewrite Hdisk. exact fsimg_image_wf.
Qed.


(* ---------------------------------------------------------------------- *)
(* 4b. THE TRACE INVARIANT AT A NON-TRIVIAL [phi], DISK AND NON-DISK.      *)
(*                                                                        *)
(* [phi] above is a parameter, so the theorem is only as strong as what a  *)
(* client puts in it -- and [fun _ => True] is a legal choice.  This       *)
(* corollary is the demonstration that the slot is not vacuous: it         *)
(* instantiates [phi] at [fs_boot_pure], the pure content of the FS's      *)
(* DURABILITY invariant [FsCrash.P_fs_named] (the durable extent's         *)
(* geometry, plus: the physical image recovers to a committed view that IS *)
(* A FILE SYSTEM -- [FsDurSnap.snap_ok] of some abstract state -- and its  *)
(* log header is well-formed), and concludes it at                         *)
(* EVERY state the CSL-free operational semantics can reach -- across      *)
(* every power cycle, since [crash_inv] is fixed-layer and hence the same  *)
(* invariant at every era.                                                 *)
(*                                                                        *)
(* IT COSTS NO NEW PROOF.  [FsCrash.P_fs_project] is already the           *)
(* obligation [Hproj] -- the projection the power theorem runs at each     *)
(* PowerOn to tell a boot what disk it is booting on -- and                *)
(* [RiscvAdequacy.disk_proj_trace] is the adapter that promotes exactly    *)
(* that shape to [Hphi]'s.  The two hooks read the same fact off the same  *)
(* invariant; the difference is only where it is delivered (into a boot,   *)
(* versus out of the whole execution).                                     *)

Corollary xv6_fs_adequacy_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\
    xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb) g2.
Proof.
  (* NOTHING IS LEFT BUT [phi].  The image went one rung up, so all this
     does is choose the pure trace property and hand over its Iris-side
     proof.  [logstart] is not an argument: the crash predicate sits at the
     SUPERBLOCK'S own log start (fs-cfg-boot.md stage (f) -- the boot seam's
     [fsc_logst] is tied to it), and [FsImg.sb_logstart fsimg_sb] IS the [2]
     this corollary used to pass, by conversion on the record literal. *)
  exact (xv6_power_adequacy_xv6Σ g
           (xv6_trace_pure fsimg_cov (FsImg.sb_logstart fsimg_sb))
           (fun Hinv γgen γstart γreg γd γsw γobs γhist c T g' =>
              xv6_trace_hook xv6Σ fsimg_cov (FsImg.sb_logstart fsimg_sb)
                unit unit (fun _ _ _ => True%I)
                Hinv γgen γstart γreg γd γsw γobs γhist c T
                (app_iface_triv xv6Σ) g')
           Hgen0 Hpow Hdisk).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4c. THE TRACE THEOREM AT THE IMAGE, and the smallest closed instance.  *)
(*                                                                        *)
(* [xv6_trace_adequacy_xv6Σ] is [xv6_trace_adequacy] with the functor list *)
(* and the disk fixed, [R]/[P] free.  [xv6_obs_wf_xv6Σ] is the closed     *)
(* demonstration: at the real image, every run's observable trace is      *)
(* well-formed -- PowerOn, console I/O, PowerOff, PowerOn, ... with the    *)
(* boot count and the wire tie ([ObsTrace.obs_wf]) -- read off the trace   *)
(* conjunct of [state_interp] with the slot at the trivial predicate.      *)
(* ---------------------------------------------------------------------- *)
Corollary xv6_trace_adequacy_xv6Σ (g : gstate)
    (R : list mobs -> iProp xv6Σ) (HRt : forall h, Timeless (R h))
    (Tg : list mobs -> iProp xv6Σ) (HTg : forall h, Persistent (Tg h))
    (HTgt : forall h, Timeless (Tg h))
    (* ONE CLAIM OVER THE WHOLE CONSOLE HISTORY (redesign R2): what the
       client claims of the bytes the console UART has accepted, of the
       inputs it logged and of the ones a process has been given. *)
    (Cres : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp xv6Σ)
    (HCrest : forall k h H, Timeless (Cres k h H))
    (HR0 : ⊢ |==> R [])
    (* ...and the era's two port claims, founded by the power-ON arm (lane
       CONS-IO milestone E) *)
    (Hpow : forall (h : list mobs) (on : bool) (dk : Z -> bv 8),
       trace_shape h on ->
       ⊢ R h ==∗ R (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
         (if on then emp
          else Cres (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)))
    (Htx : forall (HR : riscvGS xv6Σ) (GEN : GenId) (i : uart_id) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
              (ho : list mobs) (H : LogEntryDefs.cons_hist),
              ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
              ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
              (* THE WIRE IS THE DRAINED SEQUENCE (the clause TX-TAG left
                 owed): with LOOP off throughout, [u_wire] and [u_out] are
                 the same list, so the wire is a PREFIX of [uart_acc u] and
                 a prefix-closed output claim transfers to it. *)
              ⌜u_wire u = u_out u⌝ -∗
              (* ...AND THE ERA STAMP (lane CONS-IO milestone C): the era
                 this history belongs to is [S gen_id], which is the index
                 the two claims below are read at. *)
              ⌜obs_boots h = S gen_id⌝ -∗
              (* ...AND THE OUTPUT CLAIM ITSELF, at a WITNESS HISTORY the
                 invariant holds a monotone lower bound on -- so [ho] is a
                 real prefix of the run's own history [h], and the client
                 lifts the claim to [h] by its own input-monotonicity.  This
                 is the ONLY channel from the console UART's invariant to
                 the ledger, and hence to [Hphi]. *)
              ⌜ho `prefix_of` h⌝ -∗
              (* ...AND THE ACCEPTED BYTES ARE THE HISTORY'S OWN FIELD
                 (redesign R2), so the tie the drain needs is a premise. *)
              ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
              (* ...TAKEN LINEARLY AND GIVEN BACK: the claim holds the
                 application's authority, so the ledger step reads it
                 against its own ledger and puts it where it found it. *)
              (if i is Uart0 then Cres (Datatypes.S gen_id) ho H else emp) -∗
              uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              (if i is Uart0 then Cres (Datatypes.S gen_id) ho H else emp) ∗
              uart_ghosts γ u' ∗ R (h ++ [ObsUartOut i b])%list))
    (Hrx : forall (HR : riscvGS xv6Σ) (GEN : GenId) (i : uart_id) (γ : uart_names),
       ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
              ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
              ⌜obs_boots h = S gen_id⌝ -∗
              uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
              uart_ghosts γ u' ∗ R (h ++ [ObsUartIn i b])%list ∗
              Tg (h ++ [ObsUartIn i b])%list))
    (* THE ECHO'S JUSTIFICATION (lane OUT-FUPD, F3): consoleintr echoes an
       input byte through consputc at [Uart0], whose invariant carries the
       client's own output claim, and the interrupt path holds nothing it
       could pay the store's view shift with -- so the payment is the
       client's.  Stated at the two record equations the boot has, because
       the shift reads the machine's ambient tag family and its ambient
       output claim and both ARE the client's at the record adequacy
       builds. *)
    (Hecho : forall (HRg : riscvGS xv6Σ),
       (* the shift reads ONE claim (redesign R2) *)
       @riscv_cons_res xv6Σ (@riscv_fixedGS xv6Σ HRg) = Cres ->
       @riscv_rx_tag xv6Σ (@riscv_fixedGS xv6Σ HRg) = Tg ->
       ⊢ ∀ (GEN : GenId) (XI : CurCtx), @cons_echo_shift xv6Σ HRg GEN XI)
    (* ONE LICENCE (redesign R2): the client's claim survives any boundary
       event -- the generic slot's [write(2)] byte, consoleintr's shift and
       [read(2)] on fd 0 alike. *)
    (Hout_lic : ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
                       (ev : ConsLog.cons_ev),
                       Cres k h H ==∗ Cres k h (ConsLog.cons_step H ev)))
    (P : list mobs -> Prop) (HR : forall h, R h ⊢ ⌜P h⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ P κs.
Proof.
  apply (xv6_trace_adequacy xv6Σ g fsimg_sb fsimg_nib fsimg_cov R HRt Tg HTg
           HTgt Cres HCrest HR0 Hpow Htx Hrx Hecho
           Hout_lic P HR Hgen0 Hpow0).
  rewrite Hdisk. exact fsimg_image_wf.
Qed.

Corollary xv6_obs_wf_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    nsteps n ([PowerLoopE : expr riscv_lang], g) κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ obs_wf κs g2.
Proof.
  refine (xv6_power_adequacy_gen xv6Σ g fsimg_sb fsimg_nib fsimg_cov
            (* the GENERIC application (applications.md section 0): no fixed
               part, any abstract state, nothing lent, the supply outright *)
            unit (fun _ => True%I)
            ltac:(iModIntro; iExists (); iPureIntro; exact Logic.I)
            unit (fun _ _ _ => True%I)
            (fun _ _ _ => emp%I)
            (fun _ : unit => app_iface_triv _)
            (fun (_ : unit) (_ : nat) => emp%I)
            ltac:(intros c k; apply app_xfer_boot_raw_triv;
                  intros r av; reflexivity)
            ltac:(intros c; cbv beta; iModIntro; iExists ();
                  iPureIntro; exact Logic.I)
            ltac:(intros ci ri; iIntros "_"; iModIntro; done)
            ltac:(intros ci ri; rewrite /ai_cons /app_iface_triv /cons_res_triv;
                  iIntros "_ !>" (k h H ev) "_"; by iModIntro)
            ltac:(intros HRi GENi HBsi HFdi HIri HPavi HWci HFi ci ri
                         Heq Hiface Hgeni;
                  iIntros "_ _ _"; iModIntro; iApply init_boot_of_triv;
                  [ rewrite Heq; intros r' av; reflexivity
                  | rewrite /app_taint Hiface; reflexivity ])
            (* THE ECHO'S JUSTIFICATION, at the TRIVIAL console claim: every
               link is free, so the echo justifies itself. *)
            ltac:(intros HRi ci Hifacei; iIntros (GEN XI);
                  iApply (cons_echo_shift_triv (XI := XI));
                  rewrite /riscv_cons_res Hifacei; reflexivity)
            (fun γobs _ => obs_pred_at γobs)
            (obs_pred_at_alloc_cl (fun _ : unit => True%I))
            (fun γd γobs _ =>
               obs_pred_at_step XV6_DISK_BYTES cons_res_triv
                 (fun _ => emp%I)
                 (cons_res_triv_founded xv6Σ) (turn_triv_founded xv6Σ) γd γobs)
            _ (fun g h => obs_wf h g)
            ltac:(intros Hinv γgen γstart γreg γd γsw γobs γhist c T g' h;
                  iIntros "_ _ %Hwf _ _"; iModIntro; iPureIntro; exact Hwf)
            Hgen0 Hpow0 _).
  { intros HR GEN HFi ri i γ
           (Hi & Gg & Gs & Gr & Gt & Gsw & Gob & Ghist & Gcl & GT & Heq & _ & _).
    apply (uart_obs_permit_triv i γ); rewrite Heq; reflexivity. }
  rewrite Hdisk. exact fsimg_image_wf.
Qed.
