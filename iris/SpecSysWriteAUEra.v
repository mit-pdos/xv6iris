(* SpecSysWriteAUEra.v -- sys_write's ATOMIC-UPDATE contract AT THE
   AUTHORITY-SHAPED COMMIT: [SpecSysWriteAU]'s statement with the ONE thing
   the landed inventory forces changed, and nothing else.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the write AU
   prover).  A PARALLEL FORM beside [SpecSysWriteAU.wp_sys_write_au] -- R10:
   that file does not move.  The mknod lane's [SpecSysMknodAUEra] is the
   precedent and this file is the same move at the write delta.

   ==== THE ONE CHANGE, AND WHY IT IS FORCED ============================

   [SpecSysWriteAU.awrite_commit] is stated over [FsAbs.astate].  The
   prover's only source of [astate] is the γtop authority inside
   [InodeRegion.ftop_inv]; borrowing it is fine, GIVING IT BACK is not.
   [astate Γ av] is [∃ I, ghost_map_auth (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝]
   and [abs_view] is not injective, so a client's fupd may legitimately
   return an authority at a DIFFERENT map with the same reading -- e.g. the
   same bytes behind a different block map -- and [ftop_body]'s row
   ([ftop_clean I A], a statement about the RECORDS) is then unprovable.
   Neither phase is dischargeable, and the two-phase forms do not relate in
   either direction (phase 2 names the POST map, which no [astate] at the
   delta determines).  [FsAbsMknodFire]'s header is the long form of this
   argument; [FsAbsWriteFire]'s is the short one at this delta.

   So the commits below are [FsAbsWriteFire.awrite_commit_at] -- the same
   two phases at the RAW MAP, with the very same [ghost_map_auth] handed
   back -- and everything else in this file is [SpecSysWriteAU]'s, name for
   name:

   - THE FRAME IS REUSED VERBATIM.  [SpecSysWriteAU.wp_sys_write_au_frame]
     is already abstracted over the caller's bundle and the armed post
     ([EXTRA], [ARMS]), and its continuation matches
     [SpecSysWrite.wp_sys_write_sconf_body]'s at the current head (write
     does not move the image -- filewrite only READS the user source -- so
     the [M'] binder that made [SpecSysMknodAU]'s frame unusable does not
     arise here).  This form is that frame at the new bundle and arms.
   - THE RECEIPTS ARE REUSED VERBATIM.  [wri_receipts] and
     [wri_receipts_chained] mention no commit, so nothing about them moves.
   - THE ARMS, THE TOTALS AND THE COUNT BOUND are [write_post_ok] /
     [write_post_fail] / [write_arms] with [awrite_commits] replaced by
     [awrite_commits_at] in the refund, and nothing else.

   ==== THE STABLE COROLLARY ============================================

   [write_stable_arms_at] is [SpecSysWriteAU.write_stable_arms] at the same
   substitution, un-keyed escape disjunct and all.  It is sealed here as a
   SECOND module type rather than a second parameter of the first, because
   its derivation is assembly off the AU form (frame the client's share
   through the call, take the escape disjunct at [off0 := 0]) and a
   consumer that does not want it should not have to pay for it.  Its two
   honesty caveats are the frozen file's, unchanged: the share is on the
   WRITTEN row, so the form is vacuous against a live inum until the tree
   layer's exclusivity fact replaces the fraction premise; and the chained
   disjunct is the documented intent, not a deliverable.

   BINDERS: [SpecSysWriteAU]'s section list VERBATIM. *)
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
Require Import SpecArgfd.      (* [arg_fd]                                  *)
Require Import SpecSysRead.    (* [sys_rw_count]                            *)
Require Import ConsoleInv.
Require Import FsBlocks.       (* [blk_splice]                              *)
Require Import InodeInv.       (* [MAXFILE]                                 *)
Require Import SpecFilewrite.  (* [FW_MAX], [fwrite_names], the env bundles *)
Require Import SpecSysWrite.   (* [sys_write_stack]                         *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsBytesGamma.   (* [fs_gamma_L]: the live Γ                  *)
Require Import Xv6G.
Require Import FsCfg.
Require Import SpecSysWriteAU. (* the frozen statement this parallels       *)
Require Import FsAbsWriteFire. (* [awrite_commit_at] and its bundle         *)
Require Import FsAbs.          (* LAST (FsAbs's own rule)                   *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Section SysWriteAUEra.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  1.  The arms, at the authority-shaped bundle                        *)
  (* ------------------------------------------------------------------ *)

  (* ret n (0 <= n): every byte landed.  The fired chunks concatenate to the
     whole count and the unfired tail of the bundle refunds. *)
  Definition write_post_ok_at Γ (i : Z) (n : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜Z.of_nat (length (concat bss)) = n⌝ ∗
       ⌜(length bss <= wchunks n)%nat⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_commits_at Γ ∅ i Φ (length bss)
         (wchunks n - length bss)%nat)%I.

  (* ret -1: filewrite's honest partial arm.  A PREFIX of chunks fired --
     possibly empty -- their deltas are REAL, and the total falls short of
     the count.  The short chunk that ENDED the loop is deliberately not in
     [bss]: writei's disturbed tail is not the splice, so its instant is not
     one this contract's receipts can speak about (FsAbsWriteFire's second
     finding).  That is exactly the slack "< n" leaves. *)
  Definition write_post_fail_at Γ (i : Z) (n : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜Z.of_nat (length (concat bss)) < n \/ (n < 0 /\ bss = [])⌝ ∗
       ⌜(length bss <= wchunks n)%nat⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_commits_at Γ ∅ i Φ (length bss)
         (wchunks n - length bss)%nat)%I.

  (* THE THIRD ARM, AND IT IS THIS LANE'S THIRD FINDING.  The descriptor
     may name an inode that does not read as a FILE.  [FsAbs.abs_node]'s
     third arm is [ADev (fn_major n) (fn_minor n)], and writei moves
     neither field -- nor [di_nlink] -- so on such a row the abstract view
     does not move AT ALL: every chunk's [delta_write] is the IDENTITY
     ([delta_write] is total on purpose, and a non-[AFile] row is its
     fixpoint).  Nothing this contract can observe happened at that chunk,
     so the arm delivers whatever PREFIX of receipts was already fired,
     refunds the rest of the bundle, and says NOTHING about the totals --
     which is the whole difference from the fail arm, and the honest one:
     the count in a0 is about bytes on disk blocks, and this arm is where
     those bytes have no abstract reading.

     THE ARM IS UNREACHABLE IN XV6 AND THE PROOF CANNOT SAY SO.  sys_open
     sets [f->type = FD_DEVICE] exactly when [ip->type == T_DEVICE], so an
     FD_INODE descriptor's inode is a regular file -- but no resource in
     the tree records it.  The fd payload's whole type witness is
     [FileInvDefs.inode_pay]'s [∃ ty, ity_shot g ty ∗ ⌜wr = true -> ty <>
     T_DIR_z⌝] (surfaced by [SpecFileread.fileread_pay_carve]), which
     excludes a DIRECTORY and nothing else, and [inode_pay] does not even
     take the descriptor's [fc_type] as a parameter.  Closing the arm is a
     one-conjunct strengthening at [FileInvDefs.file_payload]'s inode arm
     ([fc_type Cf = FD_INODE -> bv_unsigned ty = T_FILE_z]), discharged at
     sys_open's publication where the code's own [ip->type == T_DEVICE]
     test decides which [f->type] is written -- OWNER'S CALL under R10,
     and it ripples through the file layer's callers.  Recorded as this
     lane's owner question 1.  Until it lands the arm stays, and a
     consumer keys on it by exclusion: an ok arm with no receipts and a
     full refund is the "not a file" answer. *)
  Definition write_post_nofile_at Γ (i : Z) (n : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜(length bss <= wchunks n)%nat⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_commits_at Γ ∅ i Φ (length bss)
         (wchunks n - length bss)%nat)%I.

  Definition write_arms_at Γ (i : Z) (n : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝ ∗ write_post_ok_at Γ i n Φ)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ write_post_fail_at Γ i n Φ)
     ∨ (⌜(r = (mword_of_int n : mword 64) /\ 0 <= n)
         \/ r = (mword_of_int (-1) : mword 64)⌝
        ∗ write_post_nofile_at Γ i n Φ))%I.

  (* the stable corollary's arms, at the same substitution *)
  Definition write_stable_arms_at Γ (i : Z) (n : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    (nview Γ q i (MkAnode (AFile bs0) nl) ∗
     ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝ ∗
         ∃ (off0 : nat) (bss : list (list (bv 8))),
           ⌜(off0 <= length bs0)%nat⌝ ∗
           ⌜Z.of_nat (length (concat bss)) = n⌝ ∗
           ⌜(length bss <= wchunks n)%nat⌝ ∗
           (wri_receipts_chained i bs0 nl off0 Φ bss
            ∨ wri_receipts i Φ bss) ∗
           awrite_commits_at Γ ∅ i Φ (length bss)
             (wchunks n - length bss)%nat)
      ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
         ∗ write_post_fail_at Γ i n Φ)
      (* the not-a-file arm rides here too.  A client holding the share
         BELIEVES the row is a file, and is right -- but the derivation
         cannot say so: refuting the arm means reading the authority at
         the instant, which is the AU form's job and not a corollary's.
         When owner question 1 lands, this disjunct goes with the one it
         is inherited from. *)
      ∨ (⌜(r = (mword_of_int n : mword 64) /\ 0 <= n)
          \/ r = (mword_of_int (-1) : mword 64)⌝
         ∗ write_post_nofile_at Γ i n Φ)))%I.

End SysWriteAUEra.

Global Typeclasses Opaque write_post_ok_at write_post_fail_at
  write_post_nofile_at write_arms_at write_stable_arms_at.

(* ===================================================================== *)
(*  2.  THE CONTRACT: SpecSysWriteAU's FRAME, at the new bundle           *)
(* ===================================================================== *)

Definition wp_sys_write_au_era_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fwrite_names)
    (pidv : mword 32) (U : ustate)
    (v v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_write_au_frame γf γs j γlp fn pidv U v v2 m K eb b lks
    fd fv rb i
    (awrite_commits_at Γfs ∅ i Φw 0%nat (wchunks n))
    (write_arms_at Γfs i n Φw).

Definition wp_sys_write_au_era_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fwrite_names)
    (pidv : mword 32) (U : ustate)
    (v v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
    (q : Qp) (bs0 : list (bv 8)) (nl : nat)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_write_au_frame γf γs j γlp fn pidv U v v2 m K eb b lks
    fd fv rb i
    (nview Γfs q i (MkAnode (AFile bs0) nl)
     ∗ awrite_commits_at Γfs ∅ i Φw 0%nat (wchunks n))%I
    (write_stable_arms_at Γfs i n q bs0 nl Φw).

(* ===================================================================== *)
(*  3.  THE SEALS                                                         *)
(* ===================================================================== *)

Module Type SYSWRITE_AU_ERA.
  Parameter wp_sys_write_au_era :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (v v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_sys_write_au_era_body γf γs j γlp fn pidv U v v2 m K eb b lks
        fd fv rb i Φw.
End SYSWRITE_AU_ERA.

(* owed as a DERIVATION from [wp_sys_write_au_era] + the agreement seed
   ([FsAbsWriteFire.awrite_commit_at_pinned]), never as a second walk; the
   escape arm of [write_stable_arms_at] is what makes it land *)
Module Type SYSWRITE_AU_ERA_STABLE.
  Parameter wp_sys_write_au_era_stable :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (v v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (i : Z)
      (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_sys_write_au_era_stable_body γf γs j γlp fn pidv U v v2 m K eb b
        lks fd fv rb i q bs0 nl Φw.
End SYSWRITE_AU_ERA_STABLE.
