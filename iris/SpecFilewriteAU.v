(* SpecFilewriteAU.v -- filewrite's ATOMIC-UPDATE contract on the INODE arm:
   [SpecFilewrite.wp_filewrite_sconf_body] VERBATIM, with the descriptor's
   state pinned to [FdInode i] and the return-value clause replaced by
   [SpecSysWriteAUEra]'s armed post over a per-chunk commit bundle.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the write AU
   prover).  A PARALLEL FORM beside [SpecFilewrite.FILEWRITE] -- R10: that
   file does not move, and a caller that wants the landed blanket keeps
   calling the landed contract.

   ==== WHY THE SEAM IS AT FILEWRITE AND NOT AT WRITEI ==================

   The abstract row moves at the γtop RETAG, and the retag is
   filewrite's -- [ProofFilewrite.v]'s "THE RETAG OWES THE ROW", the
   [InodeRegion.ireg_top_retag] it performs between writei's return and its
   [iunlock].  [SpecWritei] never touches γtop at all: it takes
   [inode_meta] / [inode_map] / [inode_blocks] / [dinode_at] and gives them
   back at the new record, and the era fragment is the CALLER's.  So writei
   needs no AU twin, and the fire ([FsAbsWriteFire.wrf_awrite_fire])
   replaces exactly one line of the landed loop.

   ==== WHAT THE PROVER OF THIS CONTRACT OWES ===========================

   The loop, and only the loop.  [SpecSysWriteAU]'s header calls it the
   structural centre and it is: filewrite's chunk loop fires ONE two-phase
   commit per chunk, at that chunk's own retag instant, accumulating the
   caller's receipt bundle.  The invariant that carries it, in the landed
   loop's own vocabulary ([ProofFilewrite.fw_loop]'s [iz] and its fuel):

     ∃ p : nat, ∃ bss : list (list (bv 8)),
       ⌜length bss = p⌝
       ∗ ⌜Z.of_nat (length (concat bss)) = iz⌝     (* the offset IS the total *)
       ∗ ⌜iz = FW_MAX * Z.of_nat p⌝                (* every fired chunk is full *)
       ∗ wri_receipts i Φw bss                      (* the fired receipts       *)
       ∗ awrite_commits_at Γfs ∅ i Φw p (wchunks n - p)   (* the unfired suffix *)

   -- and the three arithmetic facts it needs are
   [FsAbsWriteFire.wri_count_lt] (the bundle is not exhausted while the loop
   runs), [wri_count_step] (it is not exhausted after one more fire) and
   [wri_count_done] (the exit at [iz = n]).  The second conjunct is what
   makes the totals arithmetic free on BOTH arms: the ok arm exits at
   [iz = n], the fail arm at [iz < n], and in both cases the exit value of
   [iz] IS [length (concat bss)].

   THE SHORT CHUNK IS NOT FIRED.  writei may stop part-way and leave a
   DISTURBED tail of at most one block ([SpecWritei]'s [dist]); those bytes
   are not the splice, so that chunk's instant carries no receipt.  It costs
   nothing: writei promises [tot = n -> dist = 0] and the loop BREAKS on
   [r <> n1], so every chunk that continues the loop is full and clean, and
   the one that ends the loop is simply absent from [bss].  See
   [FsAbsWriteFire]'s header, second finding.

   THE PEEL IS NOT NEEDED.  sys_open's trunc receipt had to travel with a
   peeled payload because one [bs0] is shared across an existential reseal;
   write's chunks each RE-LOCK, so the pre-row a chunk observes is read off
   the same [top_frag] its fire retags, inside one critical section.

   ==== WHAT THE PREMISE PINS, AND WHAT IT BUYS =========================

   [st = FdOpen rb true (FdInode i)] -- open, WRITABLE, an inode descriptor
   at inum [i].  Three consequences, all of them removals:

   - [filewrite_env] / [filewrite_env_out] reduce to the fs bundles, so the
     pipe and device arms are out of this contract's domain BY PREMISE (a
     console write is not an fs delta; a pipe write is a pipe-buffer story);
   - the [f->writable == 0] early return cannot fire
     ([FileInvDefs.fdstate_ok] ties the state to the cell the [lbu] reads);
   - the receipts speak about THE CALLER'S file: the [i] the fire retags is
     the [i] the descriptor names.

   The return value is still filewrite's own -- [n] or [-1], nothing
   between -- and the arms imply the landed [filewrite_ret] rather than
   restating it (the ok arm gives [r = mword_of_int n] with [0 <= n], the
   fail arm [-1]).

   BINDERS: [SpecFilewrite]'s section list VERBATIM -- [fileG] is bound and
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
Require Import ConsoleInv.
Require Import FsBlocks.
Require Import InodeInv.
Require Import SpecFilewrite.   (* the landed contract this parallels       *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsBytesGamma.
Require Import Xv6G.
Require Import FsCfg.
Require Import SpecSysWriteAU.     (* [wchunks], [wri_receipts]             *)
Require Import FsAbsWriteFire.     (* [awrite_commits_at]                   *)
Require Import SpecSysWriteAUEra.  (* [write_arms_at]                       *)
Require Import FsAbs.              (* LAST (FsAbs's own rule)               *)
Import Defs.

Local Open Scope Z_scope.

(* [SpecFilewrite.wp_filewrite_sconf_body], premise for premise and resource
   for resource; the three edits are marked. *)
Definition wp_filewrite_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ,
      !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)                    (* kalloc, file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (st : fdstate)            (* the borrowed reference  *)
    (fn : fwrite_names)                          (* the heavy arms' ghosts  *)
    (pidv : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
    (rb : bool) (i : Z)                          (* the descriptor's mode
                                                    bit and its inum        *)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let Γfs := fs_gamma_L fsc_fs in
  (filewrite_stack <= K)%nat ->
  (k < NFILE)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  fwn_j fn = j ->
  fwn_procs fn = γs ->
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  - 2 ^ 31 <= n < 2 ^ 31 ->
  (* EDIT 1: THE DESCRIPTOR IS AN OPEN, WRITABLE INODE AT [i].  The pipe,
     device and panic arms are out of this contract's domain by premise. *)
  st = FdOpen rb true (FdInode i) ->
  eb = true ->
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  file_ref γf k q st -∗
  proc_priv_core pj pidv U -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv γs -∗
  filewrite_env γf fn st -∗
  (* EDIT 2: THE CALLER'S PER-CHUNK COMMIT BUNDLE, one commit per possible
     chunk, indexed from 0 ([wchunks n] of them). *)
  awrite_commits_at Γfs ∅ i Φw 0%nat (wchunks n) -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt (us_V U)) P'⌝ -∗
      (* EDIT 3: the armed post REPLACES [⌜filewrite_ret n r⌝] -- each arm
         pins [r], so the landed blanket is implied. *)
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q st -∗
      proc_priv_core pj pidv (us_upt U P') -∗
      filewrite_env_out fn st -∗
      write_arms_at Γfs i n Φw r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEWRITE_AU.
  Parameter wp_filewrite_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (lks : gset string) (rb : bool) (i : Z)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_filewrite_au_body γf γs j γlp k q st fn pidv U m K eb n b lks
        rb i Φw.
End FILEWRITE_AU.
