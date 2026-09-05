(* SpecFilereadAU.v -- fileread's ATOMIC-UPDATE contract on the INODE arm:
   [SpecFileread.wp_fileread_sconf_body] VERBATIM, with the descriptor's state
   pinned to [FdOpen true wb (FdInode i)] and the return-value clause replaced
   by [SpecSysReadAU]'s armed post over the ONE read-only commit.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the read AU
   prover).  A PARALLEL FORM beside [SpecFileread.FILEREAD] -- R10: that file
   does not move, and a caller that wants the landed blanket keeps calling the
   landed contract.  The mold is [SpecFilewriteAU.v] one size down: read has
   no bundle, no loop and no carried state, so this file is the body and the
   seal and nothing else.

   ==== WHY THE SEAM IS AT FILEREAD AND NOT AT READI ====================

   The same argument the write lane recorded, with the sign flipped.  On the
   write side the abstract row MOVES at filewrite's own [ireg_top_retag], so
   the fire had to be fused into that line.  On the read side the row does not
   move at all: [SpecReadi] takes the metadata cells and the byte legs and
   gives them back, and the whole transfer sits inside ONE [ilock]/[iunlock]
   window ([SpecSysReadAU]'s THE ONE INSTANT, verified against the object
   code).  So the observation is a free choice of instruction boundary inside
   that window, and the natural one is the FIRST -- as soon as [f->off] has
   been checked out, since the receipt reports the offset the call used.
   readi therefore needs no AU twin either, and the fire
   ([FsAbsReadFire.arf_read_fire]) REPLACES NOTHING: it is one insertion.

   ==== WHAT THE PREMISE PINS, AND WHAT IT BUYS =========================

   [st = FdOpen true wb (FdInode i)] -- open, READABLE, an inode descriptor at
   inum [i].  Four consequences, all of them removals:

   - [fileread_env] / [fileread_env_out] reduce to the fs bundles, so the pipe
     and device arms are out of this contract's domain BY PREMISE (a console
     read is not an fs observation; a pipe read is a pipe-buffer story);
   - the [f->readable == 0] early return at +0x0e cannot fire
     ([FileInvDefs.fdstate_ok] ties the state to the byte the [lbu] reads);
   - the ELSE arm's [panic("fileread")] is unreachable, so this contract's
     functor takes THREE parameters and not six -- Piperead, Consoleread and
     Panic are gone, and with Consoleread goes the one axiom
     [LinkFileread]'s cone rests on;
   - the receipt speaks about THE CALLER'S file: the [i] the fire observes is
     the [i] the descriptor names ([ProofFilereadAU.frau_pay_carve] is what
     reads the two off ONE payload record).

   THE DIRECTORY ROW STAYS.  Unlike write, the premise does NOT make the
   observed row a file: xv6's open() keeps T_DIR under FD_INODE (ls reads
   directories through read()), so [ard_ret_tie]'s two arms both survive here
   and the contract's own arm structure is what carries them.  What the
   payload's fifth carve output DOES kill is the DEVICE row -- but that shows
   up only inside [ard_ret_tie]'s wildcard, which already weakens toward the
   caller, so this statement does not have to mention it.

   The return value is still fileread's own -- the count or -1 -- and the arms
   imply the landed [fileread_ret] rather than restating it
   ([SpecSysReadAU.ard_ret_tie_ret] on the ok arm, the -1 literal on the
   other).

   THE WINDOW SURVIVES.  fileread's post names the user-memory window
   ([umem_wr (us_M U) addr d bs]) and this contract keeps it verbatim: the AU
   says nothing about the destination bytes (SpecSysReadAU's WHAT "DELIVERED"
   DOES NOT MEAN), and the syscall shell above still needs the window to
   rebuild [proc_priv].

   ==== ...AND THE WINDOW'S LENGTH IS THE ANSWER ========================

   [SpecFileread]'s own post gained the exact-count conjunct

       r = mword_of_int (Z.of_nat d)  \/  r = mword_of_int (-1)

   and this contract RELAYS IT, in the landed spelling and the landed
   position (immediately after the [d <= max 0 n] bound).  A non-negative
   answer IS the number of bytes written, so a caller that also holds
   [read_arms] learns the window's LENGTH from the abstract count and not
   merely a bound on it: on the [AFile] row [ard_ret_tie] pins [r] to
   [ard_count], hence [d = ard_count (Z.to_nat n) off (length bs)] --
   "read delivered exactly the bytes the abstract state had to give".
   [SpecSysReadAU.ard_ret_tie_pos] (the -1 disjunct is refuted on an ok
   arm, so the window's length IS the answer -- on the DIRECTORY row too)
   and [SpecSysReadAU.ard_ret_tie_exact_file] (the file row's composition
   all the way to the abstract count) are that join, stated once.

   THE -1 ARM CANNOT SAY MORE, AND HERE THAT IS THE CODE'S DOING, not a
   weak spec.  readi overwrites its running [tot] with -1 when a copyout
   faults, DISCARDING blocks it has already delivered

       if (either_copyout(...) == -1) { brelse(bp); tot = -1; break; }

   -- so this contract's fault arm really can return -1 with bytes in the
   user buffer, and [d] then bounds them without counting them.  It is the
   one arm where the AU's own receipt says MORE than the count does: the
   observation FIRED, so [read_post_fail]'s right disjunct still reports
   the value the transfer was serving from.  (The pipe and console -1s
   upstream's [fileread] also carries are killed-process arms and never
   reach user mode; they are out of this contract's domain by premise.)

   BINDERS: [SpecFileread]'s section list VERBATIM -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import Xv6Cameras.
Require Import SpecFileread.       (* the landed contract this parallels     *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsBytesGamma.
Require Import Xv6G.
Require Import FsCfg.
Require Import SpecSysReadAU.      (* [read_arms], the armed post            *)
Require Import FsAbsReadFire.      (* [aread_commit_at], the dischargeable
                                      form of the commit                     *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbsDefs.              (* LAST (FsAbs's own rule)                *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* [SpecFileread.wp_fileread_sconf_body], premise for premise and resource for
   resource; the three edits are marked. *)
Definition wp_fileread_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                    (* kalloc, the file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (st : fdstate)            (* the borrowed reference  *)
    (fn : fread_names)                           (* the heavy arms' ghosts  *)
    (pidv : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
    (wb : bool) (i : Z) (γo : gname)             (* the descriptor's mode
                                                    bit, its inum and its
                                                    offset shadow           *)
    (Φr : aview -> nat -> anode -> nat -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fileread in
  let pj := proc_addr j in
  let addr := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let Γfs := fs_gamma_L fsc_fs in
  (fileread_stack <= K)%nat ->
  (k < NFILE)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  - 2 ^ 31 <= n < 2 ^ 31 ->
  (* EDIT 1: THE DESCRIPTOR IS AN OPEN, READABLE INODE AT [i].  The pipe,
     device and panic arms, and the [f->readable == 0] early return, are out
     of this contract's domain by premise. *)
  st = FdOpen true wb (FdInode i γo) ->
  eb = true ->
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  file_ref γf k q st -∗
  proc_priv_core pj pidv U -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv γs -∗
  fileread_env γf fn st -∗
  (* EDIT 2: THE CALLER'S ONE READ-ONLY COMMIT, fired at the single instant
     inside the lock window (the RAW-MAP form: the astate-shaped one is not
     dischargeable -- FsAbsReadFire's header). *)
  aread_commit_at Γfs fsabsE i γo Φr -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd) (d : nat) (bs : nat -> bv 8),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      (* EDIT 3: the armed post REPLACES [⌜fileread_ret n r⌝] -- each arm
         pins [r], so the landed blanket is implied. *)
      ⌜(Z.of_nat d <= Z.max 0 n)%Z⌝ -∗
      (* ...AND A NON-NEGATIVE ANSWER IS EXACTLY THE COUNT WRITTEN.  The
         landed conjunct, relayed in its landed spelling and position (this
         file's "...AND THE WINDOW'S LENGTH IS THE ANSWER"): joined with
         [read_arms] it turns the window's length into the ABSTRACT count on
         the [AFile] row ([SpecSysReadAU.ard_ret_tie_exact]).  The -1 arm
         keeps only the bound, and that is readi's doing, not the spec's. *)
      ⌜r = (mword_of_int (Z.of_nat d) : mword 64)
       \/ r = (mword_of_int (-1) : mword 64)⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q st -∗
      proc_priv_core pj pidv
        (upd_usM (us_upt U P') (umem_wr (us_M U) addr d bs)) -∗
      fileread_env_out fn st -∗
      read_arms Γfs i γo n Φr r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEREAD_AU.
  Parameter wp_fileread_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate)
      (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (lks : gset string) (wb : bool) (i : Z) (γo : gname)
      (Φr : aview -> nat -> anode -> nat -> iProp Σ),
      wp_fileread_au_body γf γs j γlp k q st fn pidv U m K eb n b lks
        wb i γo Φr.
End FILEREAD_AU.
