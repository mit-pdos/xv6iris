(* ===================================================================== *)
(* UShEcho.v -- E4 SH-ECHO, THE APPLICATION HALF: sh's exec of /echo PAID *)
(* out of the echo application's claim, and what echo's own slot then     *)
(* promises about the four bytes it writes.                              *)
(*                                                                        *)
(* [UInitSh.v] is the mould one level up: init execs /sh on                *)
(* [FsShPin.era0_sh_pins] and answers exec's slot piece with               *)
(* [UShKernel.sh_slot_of_kexec].  This file is the same shape one level    *)
(* DOWN -- sh's forked child execs /echo on [FsEchoPin.era0_echo_pins] and *)
(* answers with echo's own entry -- and the two differences are worth      *)
(* naming:                                                                *)
(*                                                                        *)
(*  THE PATH IS NOT A CONSTANT.  init's "sh" is a literal in its rodata    *)
(*  ([UCodeInit.init_ro] at 0x9a8) and its argv a literal in its data, so  *)
(*  [UInitSh.init_args_det] is three [vm_compute]s over the dump.  sh's    *)
(*  "echo" is a run of the LINE BUFFER, cut by [nulterminate], and its     *)
(*  argv is a malloc'd node -- so the reading is off the NODE                *)
(*  ([UkShRun.ush_cmd], persistent) against the heap the deposit lends,     *)
(*  and the pure input is [UkShEcho.echo_argv_bytes] rather than a map      *)
(*  equation.                                                              *)
(*                                                                        *)
(*  ECHO'S ENTRY IS KEY-LEVEL, NOT EXEC-LEVEL.                             *)
(*  [UShKernel.sh_slot_of_kexec] exists; echo has no twin.                 *)
(*  [UEchoKernel.echo_uexec_slot] states its nine premises about the KEY    *)
(*  (that is what makes [UexecCond.echo_gate] decidable), and what the      *)
(*  exec channel offers is [SpecKexec.kexec_image_ok] -- so the bridge      *)
(*  [echo_slot_of_kexec] below is E4's own piece, and it is the one place   *)
(*  where [kexec_args_at] (the argument block kexec BUILT) has to produce   *)
(*  [UkAbi.uk_args_c] (the argument block echo READS).                      *)
(*                                                                        *)
(* PHASE 1.  Statements, in the vocabulary the landed lemmas speak; the    *)
(* closed facts about the image and the pin are PROVED.  Nothing is        *)
(* [Admitted], nothing is a placeholder premise.                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import RegFile.           (* [regfile] *)
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap UkRun.
Require Import UserFd UserCwd UserChildren.
Require Import ChildTok.
Require Import ElfFile ElfUser ElfLoadable.
Require Import PathElems FsTree FsBlocks FsBytesGamma.
Require Import FsCfg.             (* [fsc_fs] -- the era's file-system names *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import WpMmodeLeafBase.   (* [csp_rs1] *)
Require Import UmodeArith UmodeAbi.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import PinnedObs PinnedExec.
Require Import FsEchoPin.
Require Import SpecKexec SpecSysExec SpecCopyin.
Require Import KexecDefs.
Require Import UkAbi.
Require Import UexecSG UexecExecInst UexecExecMint.
Require Import UCodeEcho.
Require Import UkEcho UEchoKernel.
Require Import UkSh UkShRun UkShEcho.
Require Import UConsLine EchoDisc.
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  1.  THE PATH sh PASSES, as a byte list                                *)
(*                                                                        *)
(*  argv[0] is the line's first token, whose four bytes are "echo"; the    *)
(*  pin speaks of [FsEchoPin.echo_path], a list of NAMES.  As at "sh",     *)
(*  [PathElems.path_elems] joins them and the join is the identity on the  *)
(*  bytes, so the byte list is spelled AS the name.                        *)
(* ===================================================================== *)
Definition echo_pl : list (bv 8) := FsImgCheck.fname_echo.

Lemma echo_path_elems : path_elems echo_pl = FsEchoPin.echo_path.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_pl_len : length echo_pl = 4%nat.
Proof. reflexivity. Qed.

(* ...and the bytes are the disciplined line's first token, which is what
   ties the pin to what sh actually passes ([UkShEcho.echo_argv_bytes] at
   [i = 0]). *)
Lemma echo_pl_line (j : nat) :
  (j < 4)%nat -> echo_pl !!! j = echo_line !!! j.
Proof.
  intro Hj.
  do 4 (destruct j as [| j]; [ vm_compute; reflexivity | ]). lia.
Qed.

(* ===================================================================== *)
(*  2.  THE PIN RESOLVES, at the child's cwd                              *)
(* ===================================================================== *)
Lemma sh_echo_pin_resolves :
  pin_resolves FsEchoPin.era0_echo_pins FsImg.ROOTINO echo_pl
    [FsImg.ROOTINO; FsEchoPin.ECHO_INO] FsEchoPin.ECHO_INO
    ElfUser.echo_elf 1%nat.
Proof.
  split_and!.
  - (* "echo" is RELATIVE, so the walk starts at the cwd -- the root *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (echo_pl !! 0%nat = Some PathElems.SLASH)); reflexivity.
  - rewrite echo_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite echo_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsEchoPin.echo_bytes_elf. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  /echo IS A FILE xv6's exec LOADS                                  *)
(*                                                                        *)
(*  [ElfLoadable.v]'s two instances at the third image.  It belongs        *)
(*  BESIDE them; it is here in phase 1 only so that stating E4 costs no    *)
(*  rebuild of the cone above [ElfLoadable.v], and moving it is a phase-2  *)
(*  line.                                                                 *)
(* ===================================================================== *)
Lemma echo_elf_loadable : kexec_loadable ElfUser.echo_elf.
Proof.
  unfold kexec_loadable.
  split; [ exact ElfUser.echo_elf_wf | ].
  split; [ apply ehdr_phoff_of_b; vm_compute; reflexivity | ].
  split; [ apply phdrs_loadable_of_b; vm_compute; reflexivity
         | apply loads_ascending_of_b; vm_compute; reflexivity ].
Qed.

Lemma echo_anode_loadable (nl : nat) :
  anode_loadable (MkAnode (AFile ElfUser.echo_elf) nl).
Proof.
  exists ElfUser.echo_elf, nl.
  split; [ reflexivity | exact echo_elf_loadable ].
Qed.

Section UShEcho.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally): NO [Context {SG}] /
     [Context {PS}] here, exactly as in [UInitSh]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  4.  THE INGREDIENTS -- [UInitSh.init_sh_slot] at /echo              *)
  (*                                                                      *)
  (*  Three persistent pieces and no [Pay]: the file-system invariant, the *)
  (*  duplicating claim law at [FsEchoPin.era0_echo_pins], and the taint's *)
  (*  generic slot.  init's fourth conjunct is sh's entry payload          *)
  (*  ([UInitSh.sh_pay]); echo's entry takes NO application-supplied       *)
  (*  resource -- its argv comes off the key and its one deposit is        *)
  (*  [UkRun.udepw_law 16] (E5) -- so [PinnedExec]'s linear [Pay] is [emp] *)
  (*  at this instance and nothing crosses the exec but the key.           *)
  (* =================================================================== *)
  Definition sh_echo_slot (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FsEchoPin.era0_echo_pins v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗ R -∗ uslot W))%I.

  Global Instance sh_echo_slot_persistent T : Persistent (sh_echo_slot T).
  Proof. rewrite /sh_echo_slot. apply _. Qed.

  (* =================================================================== *)
  (*  5.  THE TWO READINGS OF SH'S OWN IMAGE                              *)
  (*                                                                      *)
  (*  [PinnedExec.pinned_exec_bundle]'s two pure inputs, at sh's key.      *)
  (*  Both are read off the NODE (persistent, [DfracDiscarded]) against    *)
  (*  the heap [UkRun.udepw_at] lends the supplier -- the loan is the      *)
  (*  whole reason [udepw_at] hands the authorities over and takes them    *)
  (*  back (UkRun.v, the note at [udepw_at]).                              *)
  (* =================================================================== *)

  (* THE PATH: argv[0]'s string IS "echo", terminated. *)
  Definition sh_echo_path_of : Prop :=
    forall (gt gd gs : gname) (M : gmap Z (bv 8))
           (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8),
      UkShEcho.echo_argv_bytes g ->
      ⊢ uheap gt gd gs M pm sz -∗
        ush_cmd gd t (UkShEcho.echo_cmd s0 g) -∗
        ⌜ exec_path_of M (mword_of_int s0 : mword 64) echo_pl ⌝.

  (* THE VECTOR: sh's arguments are DETERMINED by the node it built.
     [UInitSh.init_args_det] is this lemma at init's constant image; the
     conclusion is stronger here because echo's entry reads the BYTES and
     not only the count and the lengths. *)
  Definition echo_args_det : Prop :=
    forall (gt gd gs : gname) (M : gmap Z (bv 8))
           (pm : gmap (mword 27) uperm) (sz s0 t : Z) (g : nat -> bv 8)
           (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
      UkShEcho.echo_argv_bytes g ->
      exec_args_of M (mword_of_int (t + 8) : mword 64) na alen afun ->
      ⊢ uheap gt gd gs M pm sz -∗
        ush_cmd gd t (UkShEcho.echo_cmd s0 g) -∗
        ⌜ na = 3%nat
          /\ (forall i : nat, (i < 3)%nat -> alen i = UkShEcho.echo_alen i)
          /\ (forall i j : nat, (i < 3)%nat -> (j < UkShEcho.echo_alen i)%nat ->
                afun i j
                = echo_line !!! (UkShEcho.echo_off i + j)%nat) ⌝.

  (* =================================================================== *)
  (*  6.  ECHO'S ENTRY AT THE EXEC CHANNEL                                *)
  (*                                                                      *)
  (*  [UShKernel.sh_slot_of_kexec]'s twin, and the piece E4 owes that sh's *)
  (*  lane never needed: [UEchoKernel.echo_uexec_slot] asks for            *)
  (*  [UkAbi.uk_args_c] and the two presence rows about the argument area, *)
  (*  and what [SpecKexec.kexec_image_ok] gives is [kexec_args_at] -- the  *)
  (*  strings at [kxc_sp top alen (S i)], the NULs after them and the      *)
  (*  [na + 1]-word vector at [kxc_sp_final].  Turning the second into the *)
  (*  first is the whole content of this obligation; the rest             *)
  (*  (entry pc, the text inclusion, the X-and-not-W page, the frame's     *)
  (*  zeroed bytes, the fd length, the map stop) is [sh_slot_of_kexec]'s   *)
  (*  derivation verbatim.                                                *)
  (*                                                                      *)
  (*  THE ROOM PREMISE is echo's 96 bytes (twelve words below the entry    *)
  (*  sp) where sh's is [2 + (8 + (16 + (ush_Dbody + n0)))] words; the     *)
  (*  supplier closes it by closed arithmetic at [na = 3] and             *)
  (*  [alen = 4, 5, 5] ([UInitSh.init_sh_room] is the mould).              *)
  (*                                                                      *)
  (*  THE PAYLOAD IS TRIVIAL: the process that execs is the one sh FORKED  *)
  (*  ([UkFork.wp_uk_ecall_fork_any]'s child arm), so [Q := fun _ => True] *)
  (*  and [echo_uexec_slot]'s own pay row is the one it already has.       *)
  (* =================================================================== *)
  Definition echo_slot_of_kexec : Prop :=
    forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
           (sts : list fdstate) (W' : uvis),
      kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
      kexec_sz ElfUser.echo_elf - PGSIZE + 96
        <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
      length sts = NOFILE ->
      ⊢ udepw_law 16 -∗ udep -∗
        my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W'.

  (* =================================================================== *)
  (*  7.  THE ASSEMBLY: sh's pinned bundle pays its exec supply            *)
  (*                                                                      *)
  (*  [UInitSh.init_exec_sup_of_sh_slot] at /echo.  The taint arm is       *)
  (*  [UexecExecMint.uslot_mint_all] (the generic slot at a constant       *)
  (*  payload -- here the trivial one), the resolving arm is               *)
  (*  [echo_slot_of_kexec] above, and the bundle is                        *)
  (*  [PinnedExec.pinned_exec_bundle] at                                   *)
  (*  [Pin := FsEchoPin.era0_echo_pins], [cw := FsImg.ROOTINO],            *)
  (*  [pl := echo_pl], [hops := [ROOTINO; ECHO_INO]],                      *)
  (*  [f := ElfUser.echo_elf], [nl := 1], [Pay := emp],                    *)
  (*  [Q := fun _ => True].                                                *)
  (* =================================================================== *)
  Definition sh_exec_sup_of_echo_slot : Prop :=
    forall (T : iProp Σ),
      Persistent T -> Timeless T ->
      (forall k : Z, free_num k -> psok k) ->
      echo_slot_of_kexec ->
      sh_echo_path_of ->
      echo_args_det ->
      ⊢ udep -∗ udepw_law 16 -∗ sh_echo_slot T -∗
        UkShEcho.sh_exec_sup_echo.

  (* =================================================================== *)
  (*  8.  S3 -- ECHO'S OUTPUT                                             *)
  (*                                                                      *)
  (*  echo's loop is                                                       *)
  (*    for (i = 1; i < argc; i++) {                                       *)
  (*      write(1, argv[i], strlen(argv[i]));                              *)
  (*      write(1, i + 1 < argc ? " " : "\n", 1);                          *)
  (*    }                                                                  *)
  (*  so at [argc = 3] it writes four buffers, in this order.              *)
  (* =================================================================== *)
  Definition echo_out : list (bv 8) :=
    sb "hello" ++ sb " " ++ sb "world" ++ nlb.

  (* ANTI-VACUITY: those are the bytes the target statement's expected
     stream carries for one cycle. *)
  Lemma echo_out_string : echo_out = sb "hello world" ++ nlb.
  Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

  Lemma echo_out_length : length echo_out = 12%nat.
  Proof. vm_compute. reflexivity. Qed.

  (* ---- E4's OWN PART: the argv echo reads off its key ARE the strings -- *)
  (* [UEchoKernel.echo_arg] is a FUNCTION of the key (the pointer is the
     eight image bytes of the slot read as a word, the length is what a
     scan finds, the bytes are the image's), so what has to be shown is
     that [kexec_args_at]'s block, built from the [(na, alen, afun)] that
     [echo_args_det] pinned, is read back as the same three strings. *)
  Definition echo_key_args : Prop :=
    forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
           (sts : list fdstate) (W' : uvis),
      kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
      na = 3%nat ->
      (forall i : nat, (i < 3)%nat -> alen i = UkShEcho.echo_alen i) ->
      (forall i j : nat, (i < 3)%nat -> (j < UkShEcho.echo_alen i)%nat ->
         afun i j = echo_line !!! (UkShEcho.echo_off i + j)%nat) ->
      Z.to_nat (uvis_argc W') = 3%nat
      /\ (forall i : nat, (i < 3)%nat ->
            ua_len (echo_arg (uvis_M W') (uvis_av W') i)
            = UkShEcho.echo_alen i
            /\ forall j : nat, (j < UkShEcho.echo_alen i)%nat ->
                 ua_bytes (echo_arg (uvis_M W') (uvis_av W') i) j
                 = echo_line !!! (UkShEcho.echo_off i + j)%nat).

  (* ---- the shape a list of [uarg]s has when it IS echo's three -------- *)
  Definition echo_argv_is (args : list uarg) : Prop :=
    length args = 3%nat
    /\ forall (i : nat) (x : uarg), args !! i = Some x ->
         ua_len x = UkShEcho.echo_alen i
         /\ forall j : nat, (j < UkShEcho.echo_alen i)%nat ->
              ua_bytes x j = echo_line !!! (UkShEcho.echo_off i + j)%nat.

  (* ---- ECHO'S POST OVER ITS TRANSCRIPT ------------------------------- *)
  (*                                                                       *)
  (*  [UkEcho.wp_kecho_write] goes through [UkRunSys]'s QUIET row today:   *)
  (*  it returns an unconstrained [ret] and says nothing about a byte.     *)
  (*  The leaf that KEEPS the receipt is TX-RECEIPT's                      *)
  (*  [wp_uk_ecall_write_recv] -- "my transcript grew by exactly the first *)
  (*  [r] bytes of my buffer" -- and it is NOT built here (it is E5's, on  *)
  (*  lane/tx-receipt).  So it is a NAMED HYPOTHESIS: [recv N] is that     *)
  (*  leaf and [tx N bs] the program-side transcript handle it moves.      *)
  (*                                                                       *)
  (*  WHAT E4 OWES against it is the two things this lane knows and E5     *)
  (*  does not: the argv bytes ARE "echo", "hello", "world"                *)
  (*  ([echo_key_args], from [echo_cmd] through the exec channel) and the  *)
  (*  LOOP'S ORDER -- so the transcript at echo's [exit] ecall is the      *)
  (*  entry's plus [echo_out], and nothing else.                           *)
  (* =================================================================== *)
  Definition echo_writes_out
      (recv : uk_names Σ -> iProp Σ)
      (tx : uk_names Σ -> list (bv 8) -> iProp Σ) : Prop :=
    forall (N : uk_names Σ) (h : CpuId) (m : regfile) (av : Z)
           (args : list uarg) (bs : list (bv 8)) (n : nat),
      m !!! Regidx a0_idx
        = (mword_of_int (Z.of_nat (length args)) : mword 64) ->
      m !!! Regidx a1_idx = (mword_of_int av : mword 64) ->
      echo_argv_is args ->
      ⊢ recv N -∗ udepw_law 16 -∗ echo_code (ukn_t N) -∗
        uargv (ukn_d N) av args -∗ tx N bs -∗
        urun N h m (mword_of_int EchoSyms.start) (2 + (8 + (2 + n))) -∗
        (∀ (h' : CpuId) (m' : regfile),
           tx N (bs ++ echo_out) -∗
           urun N h' m' (mword_of_int EchoSyms.exit) n -∗
           WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang).

End UShEcho.
