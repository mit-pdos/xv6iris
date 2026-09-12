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
(* rewiring has to hit, stated and typechecked, with the three that are   *)
(* already provable PROVED -- the pin resolves (§2), the pinned bundle    *)
(* (§3) and the reading of the receipt at the console (§4) -- and the     *)
(* rest stated as the shapes phase 2 produces.                            *)
(*                                                                       *)
(*   §1  init's path argument, as bytes                                   *)
(*   §2  THE PIN RESOLVES, at init's cwd                                  *)
(*   §3  init's pinned open bundle                                        *)
(*   §4  the receipt, read: fd 0 is the console device                    *)
(*   §5  the ledger rows and INIT'S HEAD                                  *)
(*   §6  the mknod step, and the flag it mints                            *)
(*                                                                       *)
(* WHAT PHASE 1 FOUND -- four things, and three of them are about what    *)
(* init CANNOT prove:                                                     *)
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
(*      DISJUNCTION its child (sh) consumes, not a single row: §5.         *)
(*                                                                       *)
(*  (b) INIT'S FIRST open CANNOT BE PINNED.  A pinned bundle answers the   *)
(*      walk out of the claim, and at era 0 the claim's console arm is     *)
(*      ABSENT ([FsConsPin.era0_cons_absent]) -- which is the right fact,  *)
(*      but the exclusion that turns it into a cursor (`no view I observe  *)
(*      has a console`) is the flag's AUTHORITY ([AppEcho.cons_tok]), and  *)
(*      that token lives in the claim, not in init's hands.  So init's     *)
(*      first open goes through the generic leaf and its SUCCESS arm is    *)
(*      not refutable: §5's third arm.                                     *)
(*                                                                       *)
(*  (c) THE TWO LEGS NO CONSTRAINING CLAIM CAN PAY: open's TRUNCATION      *)
(*      commit and mknod's UNARM leg (see [FsConsPin.v] §5c and            *)
(*      [PinnedOpen.v]'s header).  Both are premises here.                 *)
(*                                                                       *)
(*  (d) ...and what DOES work, with no friction at all: the mknod's own    *)
(*      parent commit and its ARM leg, which is where the console's state  *)
(*      moves and the flag is minted (§6).                                 *)
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
  (*  5.  THE LEDGER ROWS, AND INIT'S HEAD                                *)
  (* =================================================================== *)

  (* WHAT SH-LINE NEEDS OF fd 0 ([UConsLine.ush_std_cons] at init's side):
     the ledger, with row 0 an OPEN READABLE CONSOLE DEVICE.  After the two
     dups rows 1 and 2 carry the same descriptor, which is what makes
     sh's writes reach the console at all. *)
  Definition init_std_cons (γfd : gname) (l : list fdstate) : iProp Σ :=
    (ustd γfd l ∗
     ⌜exists wr : bool, l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE))⌝)%I.

  (* THE LEDGER THE PROLOGUE LEAVES ON THE GOOD PATH.  init enters with
     [FdSlots.fdt0] -- every descriptor closed, so
     [FdSlots.fd_lowest_closed_fdt0] says the open lands at 0 -- and the
     two dups land at 1 and 2. *)
  Definition init_cons_l3 : list fdstate :=
    <[2%nat := FdOpen true true (FdDevice CONSOLE)]>
      (<[1%nat := FdOpen true true (FdDevice CONSOLE)]>
         (<[0%nat := FdOpen true true (FdDevice CONSOLE)]> fdt0)).

  (* INIT'S HEAD, and it is a DISJUNCTION because init never tests either
     open (header (a)): what the fork carries to sh is one of FOUR things.

       CONSOLE   the open that ran (the first or the repair arm's second)
                 reached the pinned device, and the two dups copied it:
                 the row SH-LINE consumes;
       CLOSED    the second open FAILED (at [filealloc] or [fdalloc], which
                 init proves nothing about) -- so fd 0 is still closed, both
                 dups fail on a closed descriptor, and nothing sh writes
                 reaches anything.  The trace theorem holds on that run
                 because no byte is ever produced;
       UNKNOWN   the FIRST open SUCCEEDED.  At era 0 it cannot (the console
                 is absent and [FsConsPin.era0_cons_absent] says so), but
                 init cannot prove that: the exclusion is the flag's
                 authority and the claim holds it (header (b)).  The
                 descriptor is open at SOME type;
       TAINT     the application is off its discipline and says nothing.

     THE THIRD ARM IS THE ONE TO KILL, and there is exactly one way: hand
     init the flag's authority at the era mint ([AppEcho.cons_tok], which
     E2's boot arm is the place for), which turns `the view I observe has
     no console` into a fact init can carry -- and then the first open's
     bundle is the pinned one at the ABSENT state and its success arm is
     refuted.  That needs [PinnedObs] to admit a MISS (its [pobs_Pmiss] is
     the taint today, which is right for exec and wrong for a walk that may
     legitimately find nothing).  Both are phase-2 decisions for the owner. *)
  Definition init_cons_head (γcl : echo_fixed) (γfd : gname) : iProp Σ :=
    (init_std_cons γfd init_cons_l3
     ∨ ustd γfd fdt0
     ∨ (∃ l : list fdstate, ustd γfd l)
     ∨ ((∃ l : list fdstate, ustd γfd l) ∗ echo_taint γcl))%I.

  (* =================================================================== *)
  (*  6.  THE MKNOD STEP, AND THE FLAG IT MINTS                           *)
  (*                                                                      *)
  (*  This is where the console comes into existence and where the claim   *)
  (*  moves, and it is the one place the application's own write pays an   *)
  (*  [AppInv.app_step] rather than reading one out of [AppInv.app_sup].   *)
  (*  The shape, at [SpecSysMknod.mknod_au_at]'s four families:            *)
  (*                                                                      *)
  (*   the WALK [P]/[Pmiss]  the parent prefix of `console` is EMPTY, so   *)
  (*     the cursor is the start rule alone: [P 0 d] is `d is the root`.   *)
  (*   [Fok] THE PARENT COMMIT  fires at the create's own [(d, nm, i)].    *)
  (*     Phase 1 opens [appN], reads the claim, and -- when the fire is AT  *)
  (*     THE ROOT UNDER `console` -- hands out a step that moves the       *)
  (*     console's state ABSENT -> PRESENT AT [i]                          *)
  (*     ([FsConsPin.cons_state_mknod]) carrying the flag's authority       *)
  (*     across unchanged; at any other [(d, nm)] the step is              *)
  (*     [FsConsPin.cons_absent_create_other] / [_present_create_other]     *)
  (*     and the pins are [FsConsPin.file_pin_create].  Phase 2 then SHOOTS *)
  (*     the flag ([AppEcho.cons_shoot]) -- the view is already present, so *)
  (*     the arm it lands in is the third -- and the receipt hands          *)
  (*     [AppEcho.cons_made r i] back.                                      *)
  (*   [Farm] THE ARM LEG  free: [FsConsPin.file_pin_arm] /                 *)
  (*     [cons_absent_arm] / [cons_present_arm] need only the commit's own  *)
  (*     freshness premise.                                                 *)
  (*   [Fun] THE UNARM LEG  NOT PAYABLE: [FsConsPin.file_pin_unarm] needs   *)
  (*     [i <> ino] and the commit quantifies [i] over every view row at    *)
  (*     nlink 1 (header (c)).  A premise here.                             *)
  (*                                                                       *)
  (*  WHAT INIT GETS BACK is [SpecSysMknod.mknod_post_ok]'s existential at  *)
  (*  the inum the create chose, with the flag beside it -- which is        *)
  (*  exactly §3's premise.                                                 *)
  (* =================================================================== *)

  (* the receipt family init deposits at the parent commit: the flag, at
     the inum the create chose, WHEN the create was the console's.  Stated
     as a disjunction because the commit fires wherever the call reached
     and the claim must survive either. *)
  Definition init_cons_fok (r : echo_names) (T : iProp Σ)
      : aview -> Z -> fname -> Z -> iProp Σ :=
    fun (av : aview) (d : Z) (nm : fname) (i : Z) =>
      (⌜d <> FsImg.ROOTINO \/ nm <> fname_console⌝
       ∨ cons_made r i ∨ T)%I.

  (* ...and what init reads out of it once its own walk cursor has said the
     parent IS the root and its own path reading has said the name IS
     `console`: the flag at the created inum, or the taint. *)
  Definition init_cons_made_of_fok (r : echo_names) (T : iProp Σ)
      (i : Z) : iProp Σ := (cons_made r i ∨ T)%I.

  Lemma init_cons_fok_at (r : echo_names) (T : iProp Σ) (av : aview) (i : Z) :
    init_cons_fok r T av FsImg.ROOTINO fname_console i -∗
    init_cons_made_of_fok r T i.
  Proof.
    rewrite /init_cons_fok /init_cons_made_of_fok.
    iIntros "[%Hne | H]"; [| iExact "H"].
    exfalso. destruct Hne as [Hc | Hc]; exact (Hc eq_refl).
  Qed.

End UInitCons.
