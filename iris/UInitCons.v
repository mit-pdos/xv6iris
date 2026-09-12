(* ===================================================================== *)
(* UInitCons.v -- OPEN-PIN'S STATEMENTS: what /init's console prologue    *)
(* establishes, and what it cannot.                                      *)
(*                                                                       *)
(* [UInitSh.v] is this file's sibling one syscall over: init's own EXEC   *)
(* deposit, PAID out of the application's claim that /sh is the image's   *)
(* file.  Here it is init's own OPEN deposit, paid out of the claim that  *)
(* the console device node is the one init's own mknod created            *)
(* ([AppEcho.cons_made], [FsConsPin.cons_present_at]).                    *)
(*                                                                       *)
(* This is PHASE 1 of the lane, on [UConsLine.v]'s mold: every shape the  *)
(* rewiring has to hit, stated and typechecked, with everything that is   *)
(* already provable PROVED and the rest stated as the shapes phase 2      *)
(* produces.                                                             *)
(*                                                                       *)
(*   §1  init's path argument, as bytes                                   *)
(*   §2  THE PIN RESOLVES, at init's cwd -- and §2b the pin that MISSES    *)
(*   §3  init's pinned open bundle (the SECOND open)                       *)
(*   §4  the receipt, read: fd 0 is the console device                     *)
(*   §5  THE FIRST OPEN, WHICH MUST FAIL                                   *)
(*   §6  the mknod step, and the flag it mints                             *)
(*   §7  the ledger rows and INIT'S HEAD                                   *)
(*   §8  what [AppEcho] still owes: the absence credential                 *)
(*                                                                       *)
(* WHAT PHASE 1 FOUND:                                                    *)
(*                                                                       *)
(*  (a) INIT NEVER TESTS ITS SECOND open.  Its C is                        *)
(*        if (open(console, O_RDWR) < 0) { mknod; open again }            *)
(*        dup(0); dup(0);                                                  *)
(*      and the decode confirms it: 0x7e is [jal <open>] and 0x82 is       *)
(*      [c.j 0x1e], an UNCONDITIONAL jump, with a0 dropped                 *)
(*      ([UCodeInit.uis_init_7e] / [uis_init_82]; [UkInitMain.v:1694-1717] *)
(*      walks exactly that and never branches on the result).  So init     *)
(*      runs the two dups, the printf and the fork WHATEVER the second     *)
(*      open returned -- it does NOT stop, and `init does not start sh on  *)
(*      failure` is false of this code.  Init's head is therefore a        *)
(*      DISJUNCTION its child (sh) consumes, not a single row: §7.         *)
(*                                                                       *)
(*  (b) INIT'S FIRST open IS PINNED -- at the pin that MISSES, not at one  *)
(*      that resolves.  At era 0 the console is ABSENT                     *)
(*      ([FsConsPin.era0_cons_absent]) and the walk dies at hop 0, so the  *)
(*      call returns [-1] and the success arm is REFUTED rather than       *)
(*      carried (§5).  That is what turns init's head from four arms into  *)
(*      three.  It costs an EXCLUSIVE absence credential, because the      *)
(*      claim's console conjunct has PRESENT arms and no [□] law can rule  *)
(*      them out: §8.                                                      *)
(*                                                                       *)
(*  (c) THE TWO LEGS SPEC-TIGHTEN FIXED are no longer premises here:      *)
(*      open's truncation commit rides [om_trunc vom] (init's opens have   *)
(*      the bit clear) and mknod's UNARM leg is reached only through       *)
(*      [FsAbsCreateFire.aunarm_of_arm], at a FRESH inum.                  *)
(*                                                                       *)
(*  (d) [UserFd.ustd γfd fdt0] IS UNSATISFIABLE -- [ustd] carries          *)
(*      [length l = NSTD] (= 3) and [fdt0] is [NOFILE] (= 16) closed       *)
(*      slots.  init's ledger is [take NSTD fdt0] (§7).                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
(* THE GHOST BINDER LIST'S DEFINING MODULES, each IMPORTED and not merely
   required ([PinnedObs.v]'s header). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.            (* [fdslotG], [fdstate], [fdt0] *)
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.             (* [ustd], [ualloc], [fd_lowest_closed] *)
Require Import UInitFd.            (* the prologue's ledger rows and INIT'S
                                      HEAD, at an ABSTRACT descriptor -- the
                                      program tier ([UkInit], [UkInitMain])
                                      names the same rows at a section
                                      variable *)
Require Import PathElems.          (* [path_elems] *)
Require Import FsTree.             (* [fname] *)
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import AppCfg AppInv.
Require Import ArgPath.
Require Import PieceFam.
Require Import FsAbsEra.
Require Import FsAbsDefs.
Require Import FsAbsDelta.         (* [cre_pre] *)
Require Import SysOpenDefs.
Require Import SpecSysOpen.
Require Import SysMknodDefs.       (* [npar_elems] *)
Require Import FsAbsCreateFire.    (* [acre_commit_at], [cre_arm_fired],
                                      [aunarm_of_arm], [cre_child_unfired] *)
Require Import SpecSysMknod.       (* [mknod_au_at], [mknod_post_ok] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import FsImgCheck.
Require Import FsConsPin.          (* the console's two states, and its pin *)
Require Import PinnedObs.
Require Import PinnedOpen.
Require Import AppEcho.            (* [echo_taint], [cons_made], [cons_tok],
                                      [echo_pred], [echo_cons_law] *)
Require FsImg.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PATH init PASSES, as a byte list                              *)
(*                                                                        *)
(*  [UInitSh.init_sh_pl]'s twin: [ArgPath.arg_path_of] reads the caller's  *)
(*  string off its image as a [list (bv 8)] and the pin speaks of a list   *)
(*  of NAMES, and at a single-element path the join is the identity on the *)
(*  bytes -- so the byte list is spelled AS the name.  init's argument 0   *)
(*  is 0x970 at both call sites ([UCodeInit.uis_init_12] / [uis_init_7a]). *)
(* ===================================================================== *)
Definition init_cons_pl : list (bv 8) := fname_console.

Lemma init_cons_path_elems : path_elems init_cons_pl = cons_path.
Proof. vm_compute. reflexivity. Qed.

Lemma init_cons_pl_len : length init_cons_pl = 7%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2.  THE PIN RESOLVES, at init's cwd                                    *)
(*                                                                        *)
(*  [PinnedObs.pin_resolves_at] at the console's PRESENT state: the walk   *)
(*  starts at the cwd (the path is relative, and init's cwd is the root    *)
(*  anyway), ends at [i], and at every view the state holds of, the run is *)
(*  a run and [i]'s row is the console device.  All three conjuncts are    *)
(*  [FsConsPin.cons_present_at]'s own, which is why that definition is     *)
(*  spelled as [FsShPin.era0_sh_pins] is.                                  *)
(* ===================================================================== *)
Lemma cons_pin_resolves_at (i : Z) :
  pin_resolves_at (cons_present_at i) FsImg.ROOTINO init_cons_pl
    [FsImg.ROOTINO; i] i cons_dev.
Proof.
  rewrite /pin_resolves_at. split_and!.
  - (* the start: the path is RELATIVE, so the walk starts at the cwd --
       which is the root anyway, so both arms of [um_start_of] agree *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (init_cons_pl !! 0%nat = Some PathElems.SLASH));
      reflexivity.
  - rewrite init_cons_path_elems. reflexivity.
  - intros v (_ & Hrow & Hrun). rewrite init_cons_path_elems.
    split; [exact Hrun | exact Hrow].
Qed.

(* ===================================================================== *)
(*  2b.  ...AND THE PIN THAT MISSES, at era 0                             *)
(*                                                                        *)
(*  [PinnedObs.pin_misses_at] at the console's ABSENT state.  The walk     *)
(*  starts at the root and `console` is not one of the root's entries --   *)
(*  which is [FsConsPin.cons_absent] verbatim, because that definition is  *)
(*  stated at [astep] for exactly this consumer.  This is what refutes     *)
(*  /init's FIRST open: the walk dies at hop 0, the syscall returns [-1],  *)
(*  and the repair arm runs.                                              *)
(* ===================================================================== *)
Lemma cons_pin_misses_at :
  pin_misses_at cons_absent FsImg.ROOTINO init_cons_pl FsImg.ROOTINO.
Proof.
  rewrite /pin_misses_at. split.
  - unfold FsAbsEra.um_start_of.
    destruct (decide (init_cons_pl !! 0%nat = Some PathElems.SLASH));
      reflexivity.
  - intros v s Habs Hs. rewrite init_cons_path_elems /cons_path in Hs.
    injection Hs as <-. exact Habs.
Qed.

(* ...and the path is not empty, which is what makes the walk's TERMINAL
   cursor a later hop than hop 0 and hence the taint. *)
Lemma init_cons_path_elems_ne : path_elems init_cons_pl <> [].
Proof. rewrite init_cons_path_elems /cons_path. discriminate. Qed.

(* the parent prefix of `console` is EMPTY: mknod's walk has no hops at
   all and its cursor is the start rule alone. *)
Lemma init_cons_npar_elems : npar_elems init_cons_pl = [].
Proof. rewrite /npar_elems init_cons_path_elems /cons_path. reflexivity. Qed.

Lemma init_cons_npar_len : length (npar_elems init_cons_pl) = 0%nat.
Proof. rewrite init_cons_npar_elems. reflexivity. Qed.

(* ...the same list under [FsAbsEra]'s name for it, which is what
   [ep_hops_from] is stated over *)
Lemma init_cons_np_elems : np_elems init_cons_pl = [].
Proof. rewrite /np_elems init_cons_path_elems /cons_path. reflexivity. Qed.

(* init's cwd IS the root and its path is relative, so both arms of the
   start rule agree *)
Lemma init_cons_start :
  um_start_of FsImg.ROOTINO init_cons_pl = FsImg.ROOTINO.
Proof.
  unfold FsAbsEra.um_start_of.
  destruct (decide (init_cons_pl !! 0%nat = Some PathElems.SLASH));
    reflexivity.
Qed.

(* ...and the created NAME is `console` *)
Lemma init_cons_last :
  list_basics.last (path_elems init_cons_pl) = Some fname_console.
Proof. rewrite init_cons_path_elems /cons_path. reflexivity. Qed.

Section UInitCons.
  (* [PinnedOpen]'s binder list, plus the two the ledger and the flag need:
     [ufdG] for [UserFd.ustd] and the console flag's camera for
     [AppEcho.cons_made]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId}.
  Context `{!ufdG Σ}.
  Context `{!mono_natG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  (* =================================================================== *)
  (*  3.  INIT'S PINNED OPEN BUNDLE                                       *)
  (*                                                                      *)
  (*  [PinnedOpen.pinned_open_bundle] at the console pin.  THE CLAIM LAW   *)
  (*  IS A PREMISE, exactly as it is for [UInitSh.init_sh_slot]: this file *)
  (*  is stated over the ambient [appcfg], and what discharges the premise *)
  (*  at an era whose record is echo's is [AppEcho.echo_cons_law] applied  *)
  (*  to the flag init's own mknod minted (§6).                            *)
  (*                                                                      *)
  (*  THE TRUNCATION PIECE RIDES [om_trunc vom] ([SysOpenDefs.             *)
  (*  open_trunc_piece]).  init's opens are [O_RDWR] with the bit clear, so *)
  (*  [init_cons_open_bundle_rdwr] below owes NOTHING for it; the general   *)
  (*  form keeps the guarded piece as a premise.                            *)
  (* =================================================================== *)
  Lemma init_cons_open_bundle (γfs : fs_names) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (i : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    arg_path_of M pv init_cons_pl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜cons_present_at i v⌝ ∨ T)) -∗
    app_inv γfs -∗
    open_trunc_piece (fs_gamma_L γfs) vom Ft -∗
    open_in (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (pobs_P T [FsImg.ROOTINO; i]) (pobs_Pmiss T) Farm Fun Fok Fex
      (pobs_Fo (cons_present_at i) T) Ft.
  Proof.
    intros Hcr Hpath. iIntros "#Hcl #Hinv Ht".
    iApply (pinned_open_bundle γfs (cons_present_at i) T FsImg.ROOTINO
              init_cons_pl [FsImg.ROOTINO; i] i cons_dev M pv vom Ft
              Farm Fun Fok Fex Hcr (cons_pin_resolves_at i) Hpath
              with "Hcl Hinv Ht").
  Qed.

  (* ...AT INIT'S OWN OMODE.  [open("console", O_RDWR)] is [vom = 2]:
     [SysOpenDefs.om_rdwr_plain] reads both [om_create] and [om_trunc] off
     it as false, so the bundle is the pin and nothing else -- no trunc
     piece, and hence no [AppInv.app_step] at a row the console claim
     pins. *)
  Lemma init_cons_open_bundle_rdwr (γfs : fs_names) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (i : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_arg vom = 2 ->
    arg_path_of M pv init_cons_pl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜cons_present_at i v⌝ ∨ T)) -∗
    app_inv γfs -∗
    open_in (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (pobs_P T [FsImg.ROOTINO; i]) (pobs_Pmiss T) Farm Fun Fok Fex
      (pobs_Fo (cons_present_at i) T) Ft.
  Proof.
    intros Hom Hpath. iIntros "#Hcl #Hinv".
    destruct (om_rdwr_plain vom Hom) as [Hcr Htr].
    iApply (init_cons_open_bundle γfs T i M pv vom Ft Farm Fun Fok Fex
              Hcr Hpath with "Hcl Hinv []").
    iApply (open_trunc_piece_none _ vom Ft Htr).
  Qed.

  (* =================================================================== *)
  (*  4.  THE RECEIPT, READ: fd 0 IS THE CONSOLE DEVICE                   *)
  (*                                                                      *)
  (*  [PinnedOpen.pinned_open_dev] at the console's node.  The major is    *)
  (*  [ConsoleInv.CONSOLE] because the pin's node is, and that is the      *)
  (*  whole content: [SpecFileread]'s console arm is keyed by a [decide]   *)
  (*  on exactly this number ([UConsLine.ush_std_cons]'s note).            *)
  (* =================================================================== *)
  Lemma init_cons_recv (γfs : fs_names) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (i : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (r : mword 64) (fdv' : list fdstate) :
    arg_path_of M pv init_cons_pl ->
    open_receipt_plain (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (pobs_P T [FsImg.ROOTINO; i]) (pobs_Pmiss T)
      (pobs_Fo (cons_present_at i) T) Ft sts r fdv' -∗
      ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝)
       ∨ (⌜open_fd_rcpt (om_readable vom) (om_writable vom)
              (FdDevice CONSOLE) sts r fdv'⌝
          ∗ open_trunc_piece (fs_gamma_L γfs) vom Ft)
       ∨ T).
  Proof.
    intros Hpath. iIntros "Hrc".
    iApply (pinned_open_dev γfs (cons_present_at i) T FsImg.ROOTINO
              init_cons_pl [FsImg.ROOTINO; i] i CONSOLE 0 1%nat M pv vom Ft
              sts r fdv' (cons_pin_resolves_at i) Hpath with "Hrc").
  Qed.

  (* =================================================================== *)
  (*  5.  THE FIRST OPEN, WHICH MUST FAIL                                 *)
  (*                                                                      *)
  (*  At era 0 the console node does not exist ([FsConsPin.               *)
  (*  era0_cons_absent]), so /init's first [open("console", O_RDWR)]       *)
  (*  returns [-1] and its [blt a0,x0] at 0x1a takes the REPAIR arm.  What *)
  (*  makes that a fact init can PROVE -- rather than an arm it has to     *)
  (*  carry -- is [PinnedObs.pobs_walk_dead] at the ABSENT pin: the walk   *)
  (*  dies at hop 0 and the cursor the receipt hands back at the terminal  *)
  (*  hop is the taint, so the whole success fold collapses.               *)
  (*                                                                      *)
  (*  WHAT IT COSTS: an EXCLUSIVE absence credential [K] and the LINEAR    *)
  (*  claim law below.  "The console is not there" is not a consequence of *)
  (*  the claim alone -- [AppEcho.cons_state]'s second and third arms are  *)
  (*  PRESENT arms, and refuting them needs a resource, not a [□].  §7     *)
  (*  says which resource, and what [AppEcho] still owes to mint it.       *)
  (* =================================================================== *)

  (* THE LINEAR CLAIM LAW: holding [K], every view the application's claim
     holds of has no console -- and [K] comes back, because the walk uses
     it at one hop and init needs it again at the mknod (§6) and, if the
     mknod fails, at the second open. *)
  (* GENERALISED OVER THE FACT THE CREDENTIAL PINS (lane E2).  /init's
     console dance runs at TWO credentials, one per arm of the
     application's boot resource: the KEY, which says the console is
     ABSENT at every view the claim holds of, and the FLAG, which says it
     is PRESENT at a fixed inum.  Every consumer below reads the
     credential exactly once, to turn it into a PURE fact about the view
     the fire is at -- so the fact is a parameter and the two arms are one
     law, not two. *)
  Definition init_cons_pin_law (Pv : aview -> Prop) (T K : iProp Σ)
      : iProp Σ :=
    (□ (∀ v : aview, K -∗ app_pred app_run v -∗
          app_pred app_run v ∗ K ∗ (⌜Pv v⌝ ∨ T)))%I.

  Definition init_cons_abs_law (T K : iProp Σ) : iProp Σ :=
    init_cons_pin_law cons_absent T K.

  (* init's own bundle for an open it expects to fail.  The observation
     piece is the TRIVIAL one and honestly so: the walk dies before any
     node is locked, so it is never fired. *)
  Lemma init_cons_open_bundle_absent (γfs : fs_names) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (K : iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_arg vom = 2 ->
    arg_path_of M pv init_cons_pl ->
    init_cons_abs_law T K -∗
    pobs_miss_free Pmiss -∗
    app_inv γfs -∗
    K -∗
    open_in (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (pobs_P_dead T FsImg.ROOTINO) Pmiss Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Ft.
  Proof.
    intros Hom Hpath. iIntros "#Hcl #Hfree #Hinv HK".
    destruct (om_rdwr_plain vom Hom) as [Hcr Htr].
    iApply (pinned_open_bundle_dead γfs cons_absent T K Pmiss FsImg.ROOTINO
              init_cons_pl FsImg.ROOTINO M pv vom Ft Farm Fun Fok Fex
              Hcr Htr cons_pin_misses_at Hpath with "Hcl Hfree Hinv HK").
  Qed.

  (* ...AND THE RECEIPT: the call failed and the descriptor table did not
     move, or the application is tainted.  THERE IS NO THIRD ARM -- this is
     what kills the `fd 0 is open at SOME type` arm the head carried while
     init's first open went through the generic leaf. *)
  Lemma init_cons_open_recv_absent (γfs : fs_names) (T : iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (r : mword 64) (fdv' : list fdstate) :
    arg_path_of M pv init_cons_pl ->
    open_receipt_plain (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (pobs_P_dead T FsImg.ROOTINO) Pmiss Fo Ft sts r fdv' -∗
      ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝) ∨ T).
  Proof.
    intros Hpath. iIntros "Hrc".
    iApply (pinned_open_dead γfs T Pmiss FsImg.ROOTINO init_cons_pl
              FsImg.ROOTINO M pv vom Fo Ft sts r fdv' Hpath
              init_cons_path_elems_ne with "Hrc").
  Qed.

  (* =================================================================== *)
  (*  6.  THE MKNOD STEP, AND THE FLAG IT MINTS                           *)
  (*                                                                      *)
  (*  This is where the console comes into existence and where the claim   *)
  (*  moves, and it is the one place the application's own write pays an   *)
  (*  [AppInv.app_step] rather than reading one out of [AppInv.app_sup].   *)
  (*  The shape, at [SpecSysMknod.mknod_au_at]'s four families:            *)
  (*                                                                      *)
  (*   the WALK [init_mk_P]  the parent prefix of `console` is EMPTY       *)
  (*     ([init_cons_npar_elems]), so the cursor is the start rule alone:  *)
  (*     `hop 0 stands on the root`, and there is no hop at all.  The miss *)
  (*     family is therefore never read.                                   *)
  (*   [Fok] THE PARENT COMMIT  fires at the create's own [(d, nm, i)].    *)
  (*     Phase 1 opens [appN], reads the claim, and -- when the fire is AT  *)
  (*     THE ROOT UNDER `console` -- hands out a step that moves the       *)
  (*     console's state ABSENT -> PRESENT AT [i]                          *)
  (*     ([FsConsPin.cons_state_mknod]) carrying the flag's authority AND   *)
  (*     the absence credential [K] into the claim; at any other [(d, nm)]  *)
  (*     the step is [FsConsPin.cons_absent_create_other] /                 *)
  (*     [_present_create_other] and the pins are [FsConsPin.              *)
  (*     file_pin_create].  Phase 2 then SHOOTS the flag ([AppEcho.         *)
  (*     cons_shoot]) -- the view is already present, so the arm it lands   *)
  (*     in is the third -- and the receipt hands [AppEcho.cons_made r i]   *)
  (*     back.                                                             *)
  (*   [Farm] THE ARM LEG  free: [FsConsPin.file_pin_arm] /                 *)
  (*     [cons_absent_arm] / [cons_present_arm] need only the commit's own  *)
  (*     freshness premise.                                                 *)
  (*   [Fun] THE UNARM LEG  free SINCE SPEC-TIGHTEN: the piece is reached   *)
  (*     only through [FsAbsCreateFire.aunarm_of_arm], at the inum the      *)
  (*     ARM's receipt names, and that inum was absent from the view --     *)
  (*     [FsConsPin.file_pin_unarm_fresh] / [cons_present_unarm_fresh].     *)
  (*                                                                       *)
  (*  THE REFUND OF [Fok] IS [K].  A mknod that does not commit gives the   *)
  (*  credential back ([init_cons_mknod_fail_recv]), which is exactly what  *)
  (*  the CLOSED arm of the head needs: init's SECOND open is then the      *)
  (*  dead one again and fd 0 stays closed.                                 *)
  (* =================================================================== *)

  (* THE FOUR FAMILIES, and what each carries.

     [init_mk_Farm] IS WHERE THE PERMIT'S PAYLOAD LIVES.  The arm's receipt
     is the permit whichever child leg spends
     ([FsAbsCreateFire.acre_commit_at_gen]'s note), so init parks in it the
     two things a leg may need: the claim's PURE half at the arm's own view
     (the unarm needs it to know a FRESH inum is none of the pins') and the
     KEY (the create needs it to move the console's state; the unarm needs
     it to know the console is absent).  [Farm]'s REFUND is the key too,
     for the path where the arm never fires at all. *)
  (* ...AND IT PARKS THE CREDENTIAL'S READING OF THE ARM'S OWN VIEW.  The
     unarm needs to know that the row it removes is not the console's, and
     at the FLAG arm that is "the console is at [i] at the view the arm
     fired at" ([FsConsPin.cons_present_unarm_fresh]'s [av0] premise).  At
     the KEY arm [Pv] is [cons_absent] and the conjunct is not read. *)
  Definition init_mk_Farm (Pv : aview -> Prop) (T K : iProp Σ)
      : pfam Σ (aview -> Z -> iProp Σ) :=
    MkPfam (fun (av : aview) (_ : Z) =>
              ((⌜echo_fs_pure av⌝ ∗ ⌜Pv av⌝ ∗ K) ∨ T)%I) K.

  (* the unarm hands the key back -- a mknod whose dirlink failed leaves
     init holding what it went in with *)
  Definition init_mk_Fun (T K : iProp Σ) : pfam Σ (aview -> Z -> iProp Σ) :=
    MkPfam (fun (_ : aview) (_ : Z) => (K ∨ T)%I) True%I.

  (* the parent commit's receipt: at the CONSOLE's own create the flag, at
     any other the key back, or the taint.  Stated as a disjunction because
     the commit fires wherever the call reached and the claim must survive
     either. *)
  Definition init_cons_fok (r : echo_names) (T K : iProp Σ)
      : aview -> Z -> fname -> Z -> iProp Σ :=
    fun (av : aview) (d : Z) (nm : fname) (i : Z) =>
      ((⌜d <> FsImg.ROOTINO \/ nm <> fname_console⌝ ∗ K)
       ∨ cons_made r i ∨ T)%I.

  Definition init_mk_Fok (r : echo_names) (T K : iProp Σ)
      : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    MkPfam (init_cons_fok r T K) True%I.

  Definition init_mk_Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I).

  (* ...and what init reads out of [Fok] once its own walk cursor has said
     the parent IS the root and its own path reading has said the name IS
     `console`: the flag at the created inum, or the taint. *)
  Definition init_cons_made_of_fok (r : echo_names) (T : iProp Σ)
      (i : Z) : iProp Σ := (cons_made r i ∨ T)%I.

  Lemma init_cons_fok_at (r : echo_names) (T K : iProp Σ) (av : aview) (i : Z) :
    init_cons_fok r T K av FsImg.ROOTINO fname_console i -∗
    init_cons_made_of_fok r T i.
  Proof.
    rewrite /init_cons_fok /init_cons_made_of_fok.
    iIntros "[[%Hne _] | H]"; [| iExact "H"].
    exfalso. destruct Hne as [Hc | Hc]; exact (Hc eq_refl).
  Qed.

  (* the cursor: the parent prefix of `console` is EMPTY, so the walk has no
     hop at all and the cursor is the start rule alone *)
  Definition init_mk_P (T : iProp Σ) (k : nat) (d : Z) : iProp Σ :=
    (⌜k = 0%nat /\ d = FsImg.ROOTINO⌝ ∨ T)%I.

  (* =================================================================== *)
  (*  6b.  THE BUNDLE, PROVED                                             *)
  (*                                                                      *)
  (*  Eight premises, and every one of them is [AppEcho]'s: (a) the supply *)
  (*  off the taint ([echo_sup_of_taint]), (b) the claim's pure half       *)
  (*  ([echo_fs_pure_acc]), (c) the ABSENCE law at the key                 *)
  (*  ([echo_cons_abs_law]), (d) the arm leg ([echo_cons_arm]), (e) the    *)
  (*  unarm leg ([echo_cons_unarm]), (f) the console's own create          *)
  (*  ([echo_cons_mknod]), (g) any other create                            *)
  (*  ([echo_cons_create_other]) and (h) the shoot ([echo_cons_shoot]).    *)
  (*  They are premises because this file is stated over the AMBIENT       *)
  (*  [appcfg] and only an era whose record is echo's can name it.         *)
  (* =================================================================== *)
  Lemma init_cons_mknod_bundle (γfs : fs_names) (r : echo_names)
      (Pv : aview -> Prop)
      (T K : iProp Σ) `{!Persistent T} `{!Timeless T} `{!Timeless K}
      `{HTL : forall v : aview, Timeless (app_pred app_run v)}
      (M : gmap Z (bv 8)) (pv : mword 64) :
    arg_path_of M pv init_cons_pl ->
    □ (T -∗ app_sup) -∗
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T)) -∗
    init_cons_pin_law Pv T K -∗
    □ (∀ (av : aview) (i : Z), ⌜av !! i = None⌝ -∗
         app_pred app_run av -∗
         app_pred app_run (delta_arm i (ADev CONSOLE 0) av)) -∗
    □ (∀ (av0 av : aview) (i : Z),
         ⌜av0 !! i = None⌝ -∗ ⌜echo_fs_pure av0⌝ -∗ ⌜Pv av0⌝ -∗ ⌜Pv av⌝ -∗
         app_pred app_run av -∗
         app_pred app_run (delta_unarm i av)) -∗
    □ (∀ (av : aview) (ents : gmap fname Z) (nl : nat) (i : Z),
         ⌜cre_pre av FsImg.ROOTINO fname_console ents nl i (ADev CONSOLE 0)⌝ -∗
         K -∗ app_pred app_run av -∗
         app_pred app_run (delta_create FsImg.ROOTINO fname_console i
                             (ADev CONSOLE 0) av)) -∗
    □ (∀ (av : aview) (d : Z) (nmn : fname) (ents : gmap fname Z)
         (nl : nat) (i : Z),
         ⌜cre_pre av d nmn ents nl i (ADev CONSOLE 0)⌝ -∗
         ⌜d <> FsImg.ROOTINO \/ nmn <> fname_console⌝ -∗
         app_pred app_run av -∗
         app_pred app_run (delta_create d nmn i (ADev CONSOLE 0) av)) -∗
    □ (∀ (av : aview) (i : Z), ⌜cons_present_at i av⌝ -∗
         app_pred app_run av ==∗
         app_pred app_run av ∗ (cons_made r i ∨ T)) -∗
    app_inv γfs -∗
    K -∗
    mknod_au_at (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv CONSOLE 0
      (init_mk_P T) (fun _ _ => True%I)
      (init_mk_Farm Pv T K) (init_mk_Fun T K) (init_mk_Fok r T K) init_mk_Fex.
  Proof.
    intros Hpath.
    iIntros "#Hsup #Hpure #Habs #Harml #Hunl #Hmk #Hoth #Hshoot #Hinv HK".
    rewrite /mknod_au_at.
    (* ---- THE WALK: the parent prefix is EMPTY, so the cursor is the
       start rule and there is no hop ---- *)
    iSplitR.
    { iIntros (pl) "%Hpath'".
      rewrite (arg_path_of_uniq M pv pl init_cons_pl Hpath' Hpath).
      rewrite /ep_start. iIntros (r0 Hr0). iModIntro. iSplitR.
      - rewrite /init_mk_P. iLeft. iPureIntro.
        split; [ reflexivity | by rewrite Hr0 init_cons_start ].
      - rewrite /ep_hops_from init_cons_np_elems. by iApply big_sepL_nil'. }
    (* ---- THE PARENT LEG ---- *)
    iSplitR.
    { iApply pf_at_intro. iSplit; last first.
      { rewrite /init_mk_Fok /=. done. }
      rewrite /acre_commit_at /acre_commit_at_gen.
      iIntros (I d i nm ents nl) "%Hpre Hperm Hka".
      rewrite /init_mk_Farm /cre_arm_fired /=.
      iDestruct "Hperm" as (av0) "[%Hfree Hpay]".
      destruct (decide (d = FsImg.ROOTINO /\ nm = fname_console))
        as [[Hd Hnm] | Hother].
      - (* THE CONSOLE'S OWN CREATE *)
        subst d nm.
        iDestruct "Hpay" as "[[%Hp0 [%Hpv0 HK0]] | #HT]".
        + iModIntro. iFrame "Hka". iSplitL "HK0".
          { rewrite /app_step. iIntros (n') "%Heq Hp". rewrite Heq. iNext.
            iApply ("Hmk" $! (abs_view I) ents nl i with "[%] HK0 Hp").
            exact Hpre. }
          iIntros (I') "%Heq' Hka".
          assert (Hpr : cons_present_at i (abs_view I')).
          { rewrite Heq'. exact (cons_state_mknod ents nl i (abs_view I) Hpre). }
          iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]";
            [ set_solver | ].
          iEval (rewrite /app_body) in "Hbody".
          iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom & #Hx)".
          iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
          iDestruct "Hp" as ">Hp".
          iMod ("Hshoot" $! (abs_view I') i with "[%] Hp") as "[Hp Hm]";
            [ exact Hpr | ].
          iMod ("Hclose" with "[Hh Hp]") as "_".
          { iNext. rewrite /app_body. iExists I'. iFrame "Hh Hp Hx".
            iPureIntro. exact Hdom. }
          iModIntro. iFrame "Hka". rewrite /init_cons_fok. iRight. iExact "Hm".
        + iDestruct ("Hsup" with "HT") as "#Hs".
          iModIntro. iFrame "Hka". iSplitR.
          { iApply (app_step_acc FsImg.ROOTINO I _ with "Hs"). }
          iIntros (I') "%Heq' Hka". iModIntro. iFrame "Hka".
          rewrite /init_cons_fok. iRight. iRight. iExact "HT".
      - (* ANY OTHER (d, nm): the claim survives and the key comes back *)
        assert (Hne : d <> FsImg.ROOTINO \/ nm <> fname_console).
        { destruct (decide (d = FsImg.ROOTINO)) as [-> | Hd]; [| by left].
          right. intros ->. exact (Hother (conj eq_refl eq_refl)). }
        iDestruct "Hpay" as "[[%Hp0 [%Hpv0 HK0]] | #HT]".
        + iModIntro. iFrame "Hka". iSplitR.
          { rewrite /app_step. iIntros (n') "%Heq Hp". rewrite Heq. iNext.
            iApply ("Hoth" $! (abs_view I) d nm ents nl i with "[%] [%] Hp");
              [ exact Hpre | exact Hne ]. }
          iIntros (I') "%Heq' Hka". iModIntro. iFrame "Hka".
          rewrite /init_cons_fok. iLeft. iFrame "HK0". by iPureIntro.
        + iDestruct ("Hsup" with "HT") as "#Hs".
          iModIntro. iFrame "Hka". iSplitR.
          { iApply (app_step_acc d I _ with "Hs"). }
          iIntros (I') "%Heq' Hka". iModIntro. iFrame "Hka".
          rewrite /init_cons_fok. iRight. iRight. iExact "HT". }
    (* ---- THE EXISTS OBSERVATION: free ---- *)
    iSplitR.
    { rewrite /init_mk_Fex. iApply pf_at_triv.
      iApply dlookup_commit_at_unit. }
    rewrite /cre_child_unfired. iSplitL "HK".
    { (* ---- THE ARM LEG: free, and it MINTS THE PERMIT ---- *)
      iApply pf_at_intro. iSplit; last first.
      { rewrite /init_mk_Farm /=. iExact "HK". }
      rewrite /aarm_commit_at.
      iIntros (I i) "%Hnone %Hsome Hka".
      iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
      iEval (rewrite /app_body) in "Hbody".
      iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom & #Hx)".
      iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
      iAssert (▷ (app_pred app_run (abs_view I)
                  ∗ (⌜echo_fs_pure (abs_view I)⌝ ∨ T)))%I
        with "[Hp]" as "Hpc".
      { iNext. iApply ("Hpure" with "Hp"). }
      iDestruct "Hpc" as "[Hp Hc]". iMod "Hc".
      (* ...and the credential's own reading of the arm's view, which is
         what the UNARM leg needs at [av0] *)
      iAssert (▷ (app_pred app_run (abs_view I) ∗ K
                  ∗ (⌜Pv (abs_view I)⌝ ∨ T)))%I with "[Hp HK]" as "Hpv".
      { iNext. iApply ("Habs" with "HK Hp"). }
      iDestruct "Hpv" as "[Hp [HK Hcv]]". iMod "Hcv". iMod "HK".
      iMod ("Hclose" with "[Hh Hp]") as "_".
      { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
        iPureIntro. exact Hdom. }
      iModIntro. iFrame "Hka". iSplitR.
      { rewrite /app_step. iIntros (n') "%Heq Hp". rewrite Heq. iNext.
        iApply ("Harml" $! (abs_view I) i with "[%] Hp"). exact Hnone. }
      iIntros (I') "%Heq' Hka". iModIntro. iFrame "Hka".
      rewrite /init_mk_Farm /=.
      iDestruct "Hc" as "[%Hp0 | #HT]"; last first.
      { iRight. iExact "HT". }
      iDestruct "Hcv" as "[%Hpv0 | #HT]"; last first.
      { iRight. iExact "HT". }
      iLeft. iFrame "HK". by iPureIntro. }
    (* ---- THE UNARM LEG: it SPENDS THE PERMIT ---- *)
    iApply pf_at_intro. iSplit; last first.
    { rewrite /init_mk_Fun /=. done. }
    rewrite /aunarm_of_arm. iIntros (i) "Hperm".
    rewrite /init_mk_Farm /cre_arm_fired /=.
    iDestruct "Hperm" as (av0) "[%Hfree Hpay]".
    rewrite /aunarm_commit_at. iIntros (I c) "%Hrow Hka".
    iDestruct "Hpay" as "[[%Hp0 [%Hpv0 HK0]] | #HT]"; last first.
    { iDestruct ("Hsup" with "HT") as "#Hs".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (app_step_acc i I _ with "Hs"). }
      iIntros (I') "%Heq Hka". iModIntro. iFrame "Hka".
      rewrite /init_mk_Fun /=. iRight. iExact "HT". }
    (* THE KEY SAYS THE CONSOLE IS ABSENT AT THIS VIEW, and at an absent
       view the unarm owes no side condition at all
       ([FsConsPin.cons_absent_unarm]). *)
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iAssert (▷ (app_pred app_run (abs_view I) ∗ K
                ∗ (⌜Pv (abs_view I)⌝ ∨ T)))%I
      with "[Hp HK0]" as "Hpc".
    { iNext. iApply ("Habs" with "HK0 Hp"). }
    iDestruct "Hpc" as "[Hp [HK0 Hc]]". iMod "Hc". iMod "HK0".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka".
    iDestruct "Hc" as "[%Hab | #HT]".
    - iSplitR.
      { rewrite /app_step. iIntros (n') "%Heq Hp". rewrite Heq. iNext.
        iApply ("Hunl" $! av0 (abs_view I) i with "[%] [%] [%] [%] Hp");
          [ exact Hfree | exact Hp0 | exact Hpv0 | exact Hab ]. }
      iIntros (I') "%Heq' Hka". iModIntro. iFrame "Hka".
      rewrite /init_mk_Fun /=. iLeft. iExact "HK0".
    - iDestruct ("Hsup" with "HT") as "#Hs".
      iSplitR.
      { iApply (app_step_acc i I _ with "Hs"). }
      iIntros (I') "%Heq' Hka". iModIntro. iFrame "Hka".
      rewrite /init_mk_Fun /=. iRight. iExact "HT".
  Qed.

  (* WHAT INIT GETS BACK ON SUCCESS: the flag, at the inum the create
     chose.  The cursor says the parent was the root and the path reading
     says the name was `console`, so [init_cons_fok]'s left arm is refuted
     and the receipt collapses. *)
  Lemma init_cons_mknod_recv (γfs : fs_names) (r : echo_names)
      (Pv : aview -> Prop) (T K : iProp Σ)
      (M : gmap Z (bv 8)) (pv : mword 64) :
    arg_path_of M pv init_cons_pl ->
    mknod_post_ok (fs_gamma_L γfs) M pv CONSOLE 0 (init_mk_P T)
      (init_mk_Farm Pv T K) (init_mk_Fun T K) (init_mk_Fok r T K) init_mk_Fex -∗
      ((∃ i : Z, cons_made r i) ∨ T).
  Proof.
    intros Hpath. rewrite /mknod_post_ok. iIntros "H".
    iDestruct "H" as (pl i) "(%Hpath' & %Hb & H)".
    rewrite (arg_path_of_uniq M pv pl init_cons_pl Hpath' Hpath).
    iDestruct "H" as (av d nm ents nl) "(%Hlast & %Hcre & HP & _ & Hok & _)".
    rewrite init_cons_last in Hlast. injection Hlast as <-.
    rewrite init_cons_npar_len /init_mk_P.
    iDestruct "HP" as "[%Hp | HT]"; [| iRight; iExact "HT" ].
    destruct Hp as [_ Hd]. subst d.
    rewrite /init_mk_Fok /=.
    iDestruct (init_cons_fok_at r T K av i with "Hok") as "H".
    rewrite /init_cons_made_of_fok.
    iDestruct "H" as "[Hm | HT]";
      [ iLeft; iExists i; iExact "Hm" | iRight; iExact "HT" ].
  Qed.

  (* ...AND ON FAILURE: no step and no flag, but THE KEY COMES BACK -- it is
     the arm piece's refund on every path where the arm never fired, and the
     unarm's own receipt on the path where the do-then-undo pair did.  This
     is the CLOSED arm's input: init's SECOND open is §5's MISS pin again. *)
  Lemma init_cons_mknod_fail_recv (γfs : fs_names) (r : echo_names)
      (Pv : aview -> Prop) (T K : iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv : mword 64) :
    mknod_post_fail (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv CONSOLE 0
      (init_mk_P T) Pmiss (init_mk_Farm Pv T K) (init_mk_Fun T K)
      (init_mk_Fok r T K) init_mk_Fex -∗ (K ∨ T).
  Proof.
    rewrite /mknod_post_fail /cre_child_unfired /cre_child_pair. iIntros "H".
    iDestruct "H" as "[Hau | Hf]".
    { rewrite /mknod_au_at. iDestruct "Hau" as "(_ & _ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm"). }
    iDestruct "Hf" as (pl) "(_ & [Hd | Hc])".
    - iDestruct "Hd" as "(_ & _ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm").
    - iDestruct "Hc" as (d) "(_ & _ & _ & [Hun | Hpair])".
      + iDestruct "Hun" as "(Harm & _)".
        iLeft. iApply (pf_at_refund with "Harm").
      + iDestruct "Hpair" as (i) "Hu". rewrite /cre_unarm_fired.
        iDestruct "Hu" as (av cc) "(_ & Hk)".
        rewrite /init_mk_Fun /=. iExact "Hk".
  Qed.

  (* =================================================================== *)
  (*  7.  THE LEDGER ROWS, AND INIT'S HEAD                                *)
  (* =================================================================== *)

  (* THE LEDGER init ENTERS WITH.  [UserFd.ustd] is the low [NSTD] slots
     and nothing else, so the ledger is [take NSTD fdt0] -- THREE closed
     descriptors -- and NOT [FdSlots.fdt0], which is [NOFILE] of them and
     which [ustd] refutes by length -- see the header's finding (d). *)
  Definition init_cons_l0 : list fdstate := ufd_l0.

  Lemma init_cons_l0_len : length init_cons_l0 = NSTD.
  Proof. exact ufd_l0_len. Qed.

  (* the console descriptor /init's open and its two dups install *)
  Definition init_cons_fd : fdstate := FdOpen true true (FdDevice CONSOLE).

  (* THE LEDGER THE PROLOGUE LEAVES ON THE GOOD PATH: the open lands at 0
     and the two dups at 1 and 2, each decided by the ledger itself
     ([UserFd.ualloc]'s lowest-free discipline) and not by the kernel. *)
  Definition init_cons_l3 : list fdstate := ufd_l3 init_cons_fd.

  (* the three scans, by computation: this is what turns
     [UserFd.ualloc]'s two arms into ONE at each of init's three calls. *)
  Lemma init_cons_scan0 : fd_lowest_closed init_cons_l0 = Some 0%nat.
  Proof. reflexivity. Qed.
  Lemma init_cons_scan1 :
    fd_lowest_closed (<[0%nat := init_cons_fd]> init_cons_l0) = Some 1%nat.
  Proof. reflexivity. Qed.
  Lemma init_cons_scan2 :
    fd_lowest_closed
      (<[1%nat := init_cons_fd]> (<[0%nat := init_cons_fd]> init_cons_l0))
    = Some 2%nat.
  Proof. reflexivity. Qed.

  (* ...and the three readings of [ualloc] they license, which is the
     whole of "which descriptor came back" at each of init's calls. *)
  Lemma init_cons_alloc0 (γfd : gname) (fd : nat) :
    ualloc γfd init_cons_l0 fd init_cons_fd -∗
    ⌜fd = 0%nat⌝ ∗ ustd γfd (<[0%nat := init_cons_fd]> init_cons_l0).
  Proof. iApply (ualloc_std γfd init_cons_l0 fd 0%nat init_cons_fd init_cons_scan0). Qed.

  Lemma init_cons_alloc1 (γfd : gname) (fd : nat) :
    ualloc γfd (<[0%nat := init_cons_fd]> init_cons_l0) fd init_cons_fd -∗
    ⌜fd = 1%nat⌝ ∗ ustd γfd (<[1%nat := init_cons_fd]>
                               (<[0%nat := init_cons_fd]> init_cons_l0)).
  Proof.
    iApply (ualloc_std γfd _ fd 1%nat init_cons_fd init_cons_scan1).
  Qed.

  Lemma init_cons_alloc2 (γfd : gname) (fd : nat) :
    ualloc γfd (<[1%nat := init_cons_fd]>
                  (<[0%nat := init_cons_fd]> init_cons_l0)) fd init_cons_fd -∗
    ⌜fd = 2%nat⌝ ∗ ustd γfd init_cons_l3.
  Proof.
    iApply (ualloc_std γfd _ fd 2%nat init_cons_fd init_cons_scan2).
  Qed.

  (* WHAT SH-LINE NEEDS OF fd 0 ([UConsLine.ush_std_cons] at init's side):
     the ledger, with row 0 an OPEN READABLE CONSOLE DEVICE.  After the two
     dups rows 1 and 2 carry the same descriptor, which is what makes
     sh's writes reach the console at all. *)
  Definition init_std_cons (γfd : gname) (l : list fdstate) : iProp Σ :=
    (ustd γfd l ∗
     ⌜exists wr : bool, l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE))⌝)%I.

  Lemma init_cons_l3_row :
    init_cons_l3 !! 0%nat = Some (FdOpen true true (FdDevice CONSOLE)).
  Proof. reflexivity. Qed.

  Lemma init_std_cons_l3 (γfd : gname) :
    ustd γfd init_cons_l3 -∗ init_std_cons γfd init_cons_l3.
  Proof.
    iIntros "H". rewrite /init_std_cons. iFrame "H". iPureIntro.
    exists true. exact init_cons_l3_row.
  Qed.

  (* THE SECOND OPEN'S LEDGER MOVE, off the two halves: the LEAF hands back
     [UserFd.ualloc] at init's own ledger, which decides the NUMBER
     ([init_cons_alloc0]); the RECEIPT (§4) decides the TYPE, and at
     [om_arg vom = 2] both mode bits are set ([SysOpenDefs.om_rdwr_modes]).
     Together: the descriptor is [init_cons_fd]. *)
  Lemma init_cons_open_fd (vom : mword 64) (sts : list fdstate)
      (r : mword 64) (fdv' : list fdstate) :
    om_arg vom = 2 ->
    open_fd_rcpt (om_readable vom) (om_writable vom) (FdDevice CONSOLE)
      sts r fdv' ->
    exists fd : nat,
      r = (mword_of_int (Z.of_nat fd) : mword 64)
      /\ sts !! fd = Some FdClosed
      /\ fdv' = <[fd := init_cons_fd]> sts.
  Proof.
    intros Hom Hrc. destruct (om_rdwr_modes vom Hom) as [Hrd Hwr].
    rewrite Hrd Hwr in Hrc. exact Hrc.
  Qed.

  (* THE TWO DUPS, at the CONSOLE arm.  The source claim is the LEDGER's own
     row 0 ([UserFd.ufd_own]'s left arm -- a standard stream, not a handle),
     and the TRACKED leaf's [st <> FdClosed] premise holds there. *)
  Lemma init_cons_fd_ne : init_cons_fd <> FdClosed.
  Proof. discriminate. Qed.

  Lemma init_cons_dup_src (γfd : gname) (l : list fdstate) :
    l !! 0%nat = Some init_cons_fd -> ⊢ ufd_own γfd l 0%nat init_cons_fd.
  Proof.
    intros Hl. iApply (ufd_own_std γfd l 0%nat init_cons_fd); [ | exact Hl ].
    unfold NSTD. lia.
  Qed.

  Lemma init_cons_l1_row :
    (<[0%nat := init_cons_fd]> init_cons_l0) !! 0%nat = Some init_cons_fd.
  Proof. reflexivity. Qed.

  Lemma init_cons_l2_row :
    (<[1%nat := init_cons_fd]> (<[0%nat := init_cons_fd]> init_cons_l0))
      !! 0%nat = Some init_cons_fd.
  Proof. reflexivity. Qed.

  (* ...AND THE CLOSED ARM HAS NO TRACKED DUP LEAF.  There fd 0 is CLOSED,
     and [UkRunSys.wp_uk_ecall_dup] takes [st <> FdClosed] as a PREMISE, so
     init's two dups on that arm cannot go through it.  The row itself says
     the call fails and nothing moves ([UsysMemOk.usys_fd_ok]'s dup failure
     arm gives [fdv' = fdv]), so what is missing is a `dup at a CLOSED
     descriptor` leaf returning [-1] with the LEDGER UNCHANGED.  Until it
     exists the CLOSED arm's dups run through
     [UkRunSys.wp_uk_ecall_dup_untracked], whose post is a ledger at a state
     it does not name -- and the head's CLOSED arm below is stated at
     [init_cons_l0], which is what the missing leaf would deliver. *)
  Lemma init_cons_l0_row0 : init_cons_l0 !! 0%nat = Some FdClosed.
  Proof. reflexivity. Qed.

  (* INIT'S HEAD: THREE ARMS.  What the fork carries to sh is one of

       CONSOLE  the repair arm's mknod made the node, the second open
                reached the PINNED device (§3/§4) and the two dups copied
                it -- the row SH-LINE consumes;
       CLOSED   the mknod failed, or the second open failed at [filealloc]
                / [fdalloc] (which init proves nothing about).  fd 0 is
                still closed, both dups fail on a closed descriptor, and
                nothing sh writes reaches anything.  The trace theorem
                holds on that run because no byte is ever produced;
       TAINT    the application is off its discipline and says nothing.

     THE `fd 0 IS OPEN AT SOME TYPE' ARM IS GONE.  It was there because
     init's FIRST open went through the generic leaf and its success arm
     was not refutable; §5 refutes it -- at era 0 that open's walk provably
     misses, so it returns [-1] and the repair arm runs. *)
  (* ...AND IT IS [UInitFd.ufd_head] AT THIS ERA'S TWO CHOICES: the taint is
     echo's ([AppEcho.echo_taint]) and the descriptor is the console device
     the pinned open installed.  The rows themselves are stated at an
     ABSTRACT descriptor one file down, because /init's own WALK
     ([UkInit], [UkInitMain]) has to name them too and the program tier
     names no application ([UConsLine.v:202]). *)
  Definition init_cons_head (γcl : echo_fixed) (γfd : gname) : iProp Σ :=
    ufd_head (echo_taint γcl) init_cons_fd γfd.

  (* the three readings the callers take: sh's entry consumes either of the
     first two ([UConsLine.ush_std_cons] is the CONSOLE one), and the fork
     hands the child the same list at a fresh name. *)
  Lemma init_cons_head_console (γcl : echo_fixed) (γfd : gname) :
    ustd γfd init_cons_l3 -∗ init_cons_head γcl γfd.
  Proof. iIntros "H". iApply (ufd_head_l3 with "H"). Qed.

  Lemma init_cons_head_closed (γcl : echo_fixed) (γfd : gname) :
    ustd γfd init_cons_l0 -∗ init_cons_head γcl γfd.
  Proof. iIntros "H". iApply (ufd_head_closed with "H"). Qed.

  Lemma init_cons_head_taint (γcl : echo_fixed) (γfd : gname)
      (l : list fdstate) :
    echo_taint γcl -∗ ustd γfd l -∗ init_cons_head γcl γfd.
  Proof. iIntros "#Ht H". iApply (ufd_head_taint with "Ht H"). Qed.

  (* ...and the ledger every arm carries, which is what the two [dup]
     leaves and the fork are stated over. *)
  Lemma init_cons_head_ledger (γcl : echo_fixed) (γfd : gname) :
    init_cons_head γcl γfd -∗ ∃ l : list fdstate, ustd γfd l.
  Proof. iIntros "H". iApply (ufd_head_ledger with "H"). Qed.

  (* ...AND WHAT SH-LINE READS OFF THE CONSOLE ARM: row 0 is an OPEN
     READABLE CONSOLE DEVICE ([UConsLine.ush_std_cons]'s own shape).  The
     ledger is EXISTENTIAL because /init cannot rule out a failing dup
     ([UInitFd.ufd_head]'s note); what it CAN say is the row sh reads its
     line from. *)
  Lemma init_std_cons_of_head (γcl : echo_fixed) (γfd : gname) :
    init_cons_head γcl γfd -∗
    (∃ l : list fdstate, init_std_cons γfd l)
    ∨ ustd γfd init_cons_l0 ∨ (ustd_any γfd ∗ echo_taint γcl).
  Proof.
    rewrite /init_cons_head /ufd_head /ufd_std_at /init_std_cons.
    iIntros "[H | H]"; [| by iRight ].
    iDestruct "H" as (l) "[H %Hr]". iLeft. iExists l. iFrame "H".
    iPureIntro. exists true. exact Hr.
  Qed.

  (* =================================================================== *)
  (*  8.  THE ABSENCE CREDENTIAL, AND WHERE IT COMES FROM                *)
  (*                                                                      *)
  (*  [init_cons_abs_law T K] is discharged at an era whose record is      *)
  (*  echo's by [AppEcho.echo_cons_abs_law] at [K := AppEcho.cons_key r]:  *)
  (*  the claim's two PRESENT arms each carry that token, so a holder      *)
  (*  refutes both and "the console is absent" holds of EVERY view the     *)
  (*  claim holds of.  [AppEcho.echo_names] is now the PAIR [(flag, key)]  *)
  (*  and [AppEcho.echo_xfer] allocates both; [AppEcho.echo_init_key] is   *)
  (*  the era-0 claim WITH the key beside it, which is the form E2's boot  *)
  (*  arm hands /init (and [AppEcho.echo_init] is that with the key        *)
  (*  dropped, which is the shape [App.xv6_app_adequacy]'s [Happ_init]     *)
  (*  binder is stated at).  THE KEY IS A PREMISE HERE for the reason      *)
  (*  every law in this file is: the file is stated over the AMBIENT       *)
  (*  [appcfg], and only an era whose record is echo's can name it.        *)
  (*                                                                      *)
  (*  THE FOUR STEPS THE MKNOD BUNDLE OWES are likewise [AppEcho]'s:       *)
  (*  [echo_cons_mknod] (phase 1 at the root under `console`: ABSENT ->    *)
  (*  PRESENT, the key going in), [echo_cons_create_other] (phase 1        *)
  (*  anywhere else), [echo_cons_shoot] (phase 2: the flag, and            *)
  (*  [cons_made r i] out) and the arm leg.  All four are proved.  The     *)
  (*  UNARM leg is not, and cannot be at this bundle shape -- see the      *)
  (*  note at [init_cons_mknod_bundle].                                    *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  9.  THE LAWS, AS ONE BUNDLE -- AND ECHO'S DISCHARGE                 *)
  (*                                                                      *)
  (*  Every lemma in SS3, SS5 and SS6 takes the application's laws as        *)
  (*  PREMISES, because this file is stated over the AMBIENT [appcfg] and  *)
  (*  only an era whose record is echo's can name [AppEcho]'s.  There are  *)
  (*  eight of them for the mknod step plus the PRESENT claim law the      *)
  (*  second open runs on, and passing nine wands at three call sites is   *)
  (*  how a premise list rots -- so they are bundled here, ONCE, and the   *)
  (*  three bundles above are restated against the bundle.                 *)
  (*                                                                      *)
  (*  ALL NINE ARE [□], so the bundle is PERSISTENT: it is a constant of   *)
  (*  the era, not a resource /init spends.  What /init spends is the KEY  *)
  (*  ([AppEcho.cons_key]), which enters beside it.                        *)
  (*                                                                      *)
  (*  WHERE THEY COME FROM: [init_cons_laws_echo] below, out of the nine   *)
  (*  named [AppEcho] lemmas, under the era's record equation -- the       *)
  (*  [file_app = MkAppcfg …] premise [App.xv6_app_adequacy]'s             *)
  (*  [Hinit_boot] already carries and E2's boot arm supplies.  THE KEY    *)
  (*  ENTERS THE SAME WAY: [AppEcho.echo_init_key] is the era-0 claim WITH *)
  (*  the key beside it, and E2's boot arm routes it into /init's entry    *)
  (*  ([UkInitMain.wp_kinit_start_body]'s [K] premise).                    *)
  (* =================================================================== *)
  Definition init_cons_laws_at (Pv : aview -> Prop) (T K : iProp Σ)
      (r : echo_names) : iProp Σ :=
    ((* (a) the supply, off the taint *)
     □ (T -∗ app_sup)
     (* (b) the claim's PURE half, read off without spending it *)
     ∗ □ (∀ v : aview, app_pred app_run v -∗
            app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T))
     (* (c) the CREDENTIAL's law -- what the FIRST open runs on.  At the
        KEY arm [Pv] is [cons_absent]; at the FLAG arm it is
        [cons_present_at i]. *)
     ∗ init_cons_pin_law Pv T K
     (* (d) the arm leg *)
     ∗ □ (∀ (av : aview) (i : Z), ⌜av !! i = None⌝ -∗
            app_pred app_run av -∗
            app_pred app_run (delta_arm i (ADev CONSOLE 0) av))
     (* (e) the unarm leg *)
     ∗ □ (∀ (av0 av : aview) (i : Z),
            ⌜av0 !! i = None⌝ -∗ ⌜echo_fs_pure av0⌝ -∗ ⌜Pv av0⌝ -∗
            ⌜Pv av⌝ -∗
            app_pred app_run av -∗
            app_pred app_run (delta_unarm i av))
     (* (f) the console's OWN create: the key goes in, the state moves *)
     ∗ □ (∀ (av : aview) (ents : gmap fname Z) (nl : nat) (i : Z),
            ⌜cre_pre av FsImg.ROOTINO fname_console ents nl i (ADev CONSOLE 0)⌝ -∗
            K -∗ app_pred app_run av -∗
            app_pred app_run (delta_create FsImg.ROOTINO fname_console i
                                (ADev CONSOLE 0) av))
     (* (g) any other create the call could have reached *)
     ∗ □ (∀ (av : aview) (d : Z) (nmn : fname) (ents : gmap fname Z)
            (nl : nat) (i : Z),
            ⌜cre_pre av d nmn ents nl i (ADev CONSOLE 0)⌝ -∗
            ⌜d <> FsImg.ROOTINO \/ nmn <> fname_console⌝ -∗
            app_pred app_run av -∗
            app_pred app_run (delta_create d nmn i (ADev CONSOLE 0) av))
     (* (h) the SHOOT: phase 2 of the commit, and the flag out *)
     ∗ □ (∀ (av : aview) (i : Z), ⌜cons_present_at i av⌝ -∗
            app_pred app_run av ==∗
            app_pred app_run av ∗ (cons_made r i ∨ T))
     (* (i) ...AND THE PRESENT LAW THE SECOND OPEN RUNS ON.  Not one of the
        mknod step's eight: it is a CONSEQUENCE of the flag the step mints,
        and it is what turns the flag into the pin the resolving open is
        stated at. *)
     ∗ □ (∀ i : Z, cons_made r i -∗
            □ (∀ v : aview, app_pred app_run v -∗
                 app_pred app_run v ∗ (⌜cons_present_at i v⌝ ∨ T))))%I.

  (* ...and the landed name, at the ABSENT arm: every consumer that does
     not care which credential is in play keeps working by delta. *)
  Definition init_cons_laws (T K : iProp Σ) (r : echo_names) : iProp Σ :=
    init_cons_laws_at cons_absent T K r.

  Global Instance init_cons_laws_at_persistent Pv (T K : iProp Σ)
      (r : echo_names) : Persistent (init_cons_laws_at Pv T K r).
  Proof. rewrite /init_cons_laws_at /init_cons_pin_law. apply _. Qed.

  Global Instance init_cons_laws_persistent (T K : iProp Σ) (r : echo_names) :
    Persistent (init_cons_laws T K r).
  Proof. rewrite /init_cons_laws. apply _. Qed.

  (* ===================================================================== *)
  (*  9b.  THE CREDENTIAL /init HANDS THE SHELL (lane E2 / SH-OPEN)         *)
  (*                                                                       *)
  (*  What crosses /init's exec into sh's entry is not a resource but a     *)
  (*  LAW: at every view the claim holds of, the console is absent (so      *)
  (*  sh's own first [open] misses and its repair arm runs) or it is at a   *)
  (*  fixed inum (so sh's first open is the pinned one).  PERSISTENT, and   *)
  (*  it has to be: it crosses [UkInit.init_exec_sup_lend]'s [□] and is     *)
  (*  read once per round of /init's restart loop.  That is why /init's     *)
  (*  failed mknod SEALS its key rather than passing it on                  *)
  (*  ([AppEcho.cons_never]).                                              *)
  (* ===================================================================== *)
  Definition init_cons_cred (T : iProp Σ) (r : echo_names) : iProp Σ :=
    (cons_never r ∨ (∃ i : Z, cons_made r i) ∨ T)%I.

  Global Instance init_cons_cred_persistent T r `{!Persistent T} :
    Persistent (init_cons_cred T r).
  Proof. rewrite /init_cons_cred. apply _. Qed.

  Lemma init_cons_cred_of_never (T : iProp Σ) (r : echo_names) :
    cons_never r -∗ init_cons_cred T r.
  Proof. iIntros "#H". rewrite /init_cons_cred. by iLeft. Qed.

  Lemma init_cons_cred_of_made (T : iProp Σ) (r : echo_names) (i : Z) :
    cons_made r i -∗ init_cons_cred T r.
  Proof.
    iIntros "#H". rewrite /init_cons_cred. iRight. iLeft. by iExists i.
  Qed.

  Lemma init_cons_cred_of_taint (T : iProp Σ) (r : echo_names) :
    T -∗ init_cons_cred T r.
  Proof. iIntros "H". rewrite /init_cons_cred. iRight. by iRight. Qed.

  (* ---- the three bundles, restated against the bundle ---- *)

  Lemma init_cons_laws_mknod_bundle (γfs : fs_names) (r : echo_names)
      (Pv : aview -> Prop)
      (T K : iProp Σ) `{!Persistent T} `{!Timeless T} `{!Timeless K}
      `{HTL : forall v : aview, Timeless (app_pred app_run v)}
      (M : gmap Z (bv 8)) (pv : mword 64) :
    arg_path_of M pv init_cons_pl ->
    init_cons_laws_at Pv T K r -∗
    app_inv γfs -∗
    K -∗
    mknod_au_at (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv CONSOLE 0
      (init_mk_P T) (fun _ _ => True%I)
      (init_mk_Farm Pv T K) (init_mk_Fun T K) (init_mk_Fok r T K) init_mk_Fex.
  Proof.
    intros Hpath. rewrite /init_cons_laws_at.
    iIntros "(#Ha & #Hb & #Hc & #Hd & #He & #Hf & #Hg & #Hh & _) #Hinv HK".
    iApply (init_cons_mknod_bundle γfs r Pv T K M pv Hpath
              with "Ha Hb Hc Hd He Hf Hg Hh Hinv HK").
  Qed.

  Lemma init_cons_laws_open_absent (γfs : fs_names)
      (T K : iProp Σ) `{!Persistent T} `{!Timeless T}
      (Pmiss : nat -> Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_arg vom = 2 ->
    arg_path_of M pv init_cons_pl ->
    init_cons_abs_law T K -∗
    pobs_miss_free Pmiss -∗
    app_inv γfs -∗
    K -∗
    open_in (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (pobs_P_dead T FsImg.ROOTINO) Pmiss Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Ft.
  Proof.
    intros Hom Hpath.
    iIntros "#Hc #Hfree #Hinv HK".
    iApply (init_cons_open_bundle_absent γfs T K Pmiss M pv vom Ft
              Farm Fun Fok Fex Hom Hpath with "Hc Hfree Hinv HK").
  Qed.

  Lemma init_cons_laws_open_console (γfs : fs_names) (r : echo_names)
      (Pv : aview -> Prop)
      (T K : iProp Σ) `{!Persistent T} `{!Timeless T} (i : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_arg vom = 2 ->
    arg_path_of M pv init_cons_pl ->
    init_cons_laws_at Pv T K r -∗
    cons_made r i -∗
    app_inv γfs -∗
    open_in (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (pobs_P T [FsImg.ROOTINO; i]) (pobs_Pmiss T) Farm Fun Fok Fex
      (pobs_Fo (cons_present_at i) T) Ft.
  Proof.
    intros Hom Hpath. rewrite /init_cons_laws_at.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & #Hi) #Hm #Hinv".
    iDestruct ("Hi" $! i with "Hm") as "#Hcl".
    iApply (init_cons_open_bundle_rdwr γfs T i M pv vom Ft
              Farm Fun Fok Fex Hom Hpath with "Hcl Hinv").
  Qed.

  (* ---- AND THE DISCHARGE, at an era whose record is echo's ---- *)
  (*
     THE RECORD EQUATION IS THE PREMISE, and the rewrite goes FIRST, before
     anything typed at [app_names file_app] is introduced -- [App.
     app_triv_init_boot] is the precedent and its note says why (the names
     are a FIELD of the record, so rewriting under a term of that type is a
     dependent rewrite).  After it every conjunct is one of [AppEcho]'s
     nine lemmas at [echo_pred γ] and the era's own instance [r].
  *)
  Lemma init_cons_laws_echo (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    ⊢ init_cons_laws (echo_taint γ) (cons_key r) r.
  Proof.
    intros Heq.
    rewrite /init_cons_laws /init_cons_laws_at /init_cons_abs_law
            /init_cons_pin_law.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht". iApply (echo_sup_of_taint γ r with "Ht").
    - iIntros "!>" (v) "Hp". iApply (echo_fs_pure_acc γ r v with "Hp").
    - iApply (echo_cons_abs_law γ r).
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (echo_cons_arm γ r av i CONSOLE 0 Hfree with "Hp").
    - iIntros "!>" (av0 av i) "%Hfree %Hp0 %Hab0 %Hab Hp".
      iApply (echo_cons_unarm γ r av0 av i Hfree Hp0 Hab with "Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (echo_cons_mknod γ r av ents nl i Hpre with "Hk Hp").
    - iIntros "!>" (av d nmn ents nl i) "%Hpre %Hne Hp".
      iApply (echo_cons_create_other γ r av d nmn ents nl i CONSOLE 0
                Hpre Hne with "Hp").
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (echo_cons_shoot γ r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm". iApply (echo_cons_law γ r i with "Hm").
  Qed.

  (* ---- ...AND AT THE FLAG ARM (lane E2) ---- *)
  (*
     The SAME nine laws at the OTHER credential: /init is holding the
     persistent flag rather than the exclusive key, so the fact its walk
     pins is "the console is at [i0]" rather than "there is no console",
     and the two laws that read the fact are the present-state twins
     ([AppEcho.echo_cons_unarm_present] and [echo_cons_mknod_present], the
     second VACUOUS -- a create of `console` at the root cannot fire at a
     view where `console` already resolves).  The other seven are the
     absent arm's verbatim: none of them reads the console's state.
  *)
  Lemma init_cons_laws_made_echo (γ : echo_fixed) (r : echo_names) (i0 : Z) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    cons_made r i0 -∗
    init_cons_laws_at (cons_present_at i0) (echo_taint γ) (cons_made r i0) r.
  Proof.
    intros Heq. rewrite /init_cons_laws_at /init_cons_pin_law.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iIntros "#Hm".
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht". iApply (echo_sup_of_taint γ r with "Ht").
    - iIntros "!>" (v) "Hp". iApply (echo_fs_pure_acc γ r v with "Hp").
    - iIntros "!>" (v) "#Hm' Hp".
      iDestruct (echo_cons_law γ r i0 with "Hm") as "#Hl".
      iDestruct ("Hl" $! v with "Hp") as "[Hp Hc]". iFrame "Hp Hm' Hc".
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (echo_cons_arm γ r av i CONSOLE 0 Hfree with "Hp").
    - iIntros "!>" (av0 av i) "%Hfree %Hp0 %Hpv0 %Hpv Hp".
      iApply (echo_cons_unarm_present γ r av0 av i i0 Hfree Hp0 Hpv0
                with "Hm Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (echo_cons_mknod_present γ r av ents nl i i0 Hpre with "Hk Hp").
    - iIntros "!>" (av d nmn ents nl i) "%Hpre %Hne Hp".
      iApply (echo_cons_create_other γ r av d nmn ents nl i CONSOLE 0
                Hpre Hne with "Hp").
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (echo_cons_shoot γ r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm2". iApply (echo_cons_law γ r i with "Hm2").
  Qed.

End UInitCons.
