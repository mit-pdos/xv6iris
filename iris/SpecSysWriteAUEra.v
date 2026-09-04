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

   ==== ...AND ONE DELETION, PAID FOR BY TWO OWNER RULINGS ==============

   The frozen sketch's THIRD arm ("the row does not read as a FILE") is
   GONE, together with [write_post_nofile_at] and the chunk loop's [clean]
   flag: [FileInvDefs.inode_pay] now carries the FD_INODE ⇒ not-a-device
   conjunct and filewrite's inode arm reads [di_type = T_FILE_z] outright.
   No third arm and no skip replaced it either: [SpecWritei]'s success arm
   reports [off <= di_size] of the pre-write record (the second ruling), so
   every chunk the loop runs to completion is one the fire can take, and
   TWO arms keyed on the return value alone are the whole post.

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
Require Import RegFile.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import IrefSlots.
Require Import ProcDefs.
Require Import FileInvDefs.
Require Import SpecSysRead.    (* [sys_rw_count]                            *)
Require Import Xv6Cameras.       (* [blk_splice]                              *)
Require Import SpecFilewrite.  (* [FW_MAX], [fwrite_names], the env bundles *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsBytesGamma.   (* [fs_gamma_L]: the live Γ                  *)
Require Import Xv6G.
Require Import FsCfg.
Require Import SpecCopyin.     (* [ubytes_at]: the content seam (RULING A)  *)
Require Import SpecSysWriteAU. (* the frozen statement this parallels       *)
Require Import FsAbsWriteFire. (* [awrite_commit_at] and its bundle         *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
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
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜Z.of_nat (length (concat bss)) = n⌝ ∗
       ⌜(length bss <= wchunks n)%nat⌝ ∗
       (* WHAT WAS WRITTEN (RULING A, 2026-08-31 -- the content seam).  The
          DECOMPOSITION [bss] stays existential, because the kernel picks the
          chunk boundaries by transaction budget; the BYTES do not.  Their
          concatenation IS the caller's own run at [ua] in the image it lent
          ([SpecCopyin.ubytes_at]), so a receipt bundle now determines every
          byte it claims to have spliced.

          STATED ON THE CONCATENATION, NOT PER CHUNK, and that is the honest
          shape: the per-chunk FILE offsets are existential on purpose
          (nothing ties chunk k+1's to chunk k's -- another writer through
          the same struct file moves [f->off] between them), while the
          SOURCE offsets chain by construction, because filewrite reads
          [addr + i] with [i] its own running total.  So the source side can
          be pinned end-to-end where the destination side cannot. *)
       ⌜ubytes_at M ua (concat bss)⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_commits_at Γ fsabsE i Φ (length bss)
         (wchunks n - length bss)%nat)%I.

  (* ret -1: filewrite's honest partial arm.  A PREFIX of chunks fired --
     possibly empty -- their deltas are REAL, and the total falls short of
     the count.  The short chunk that ENDED the loop is deliberately not in
     [bss]: writei's disturbed tail is not the splice, so its instant is not
     one this contract's receipts can speak about (FsAbsWriteFire's second
     finding).  That is exactly the slack "< n" leaves. *)
  Definition write_post_fail_at Γ (i : Z) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜Z.of_nat (length (concat bss)) < n \/ (n < 0 /\ bss = [])⌝ ∗
       ⌜(length bss <= wchunks n)%nat⌝ ∗
       (* the FIRED PREFIX's bytes are pinned too (RULING A): a partial write
          delivers a PREFIX of the caller's buffer, and now says so *)
       ⌜ubytes_at M ua (concat bss)⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_commits_at Γ fsabsE i Φ (length bss)
         (wchunks n - length bss)%nat)%I.

  (* THERE IS NO THIRD ARM.  The frozen sketch of this file carried one --
     "the row does not read as a FILE" -- because the fd payload's whole
     type witness excluded a DIRECTORY and nothing else, so a T_DEVICE
     inode behind an FD_INODE descriptor was not refutable and every
     chunk's [delta_write] was then the identity.  THAT IS RULED AND PAID
     (2026-08-29, the [file_payload] strengthening lane):
     [FileInvDefs.inode_pay]'s FD_INODE arm now carries
     [fdty = FD_INODE -> bv_unsigned ty <> T_DEVICE_z], surfaced by
     [SpecFileread.fileread_pay_carve]'s fifth output, and filewrite's
     inode arm joins it to ilock's [ity_shot] and to [inode_rec_local]'s
     four-way enumeration to read [di_type = T_FILE_z] outright.  The arm,
     its [write_post_nofile_at] and the loop's [clean] flag all go.

     AND NOTHING REMAINS BESIDE IT.  A chunk fires only if its start is
     inside the file ([wri_pre]'s [off <= length bs0]) -- and
     [SpecWritei]'s SUCCESS arm now EXPOSES that guard (owner's ruling,
     2026-08-29: the writing arm reports [off <= di_size] of the pre-write
     record, the negation of the reason its own [-1] arm reports).  So
     there is no chunk the prover has to skip, the two arms are keyed on
     the return value alone, and this arm answers exactly [-1]. *)
  Definition write_arms_at Γ (i : Z) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝
      ∗ write_post_ok_at Γ i n M ua Φ)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ write_post_fail_at Γ i n M ua Φ))%I.

  (* the stable corollary's arms, at the same substitution *)
  Definition write_stable_arms_at Γ (i : Z) (n : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    (nview Γ q i (MkAnode (AFile bs0) nl) ∗
     ((⌜r = (mword_of_int n : mword 64) /\ 0 <= n⌝ ∗
         ∃ (off0 : nat) (bss : list (list (bv 8))),
           ⌜(off0 <= length bs0)%nat⌝ ∗
           ⌜Z.of_nat (length (concat bss)) = n⌝ ∗
           ⌜(length bss <= wchunks n)%nat⌝ ∗
           (* the single-delta reading now names the delta's BYTES: they are
              the caller's own run at [ua] (RULING A) *)
           ⌜ubytes_at M ua (concat bss)⌝ ∗
           (wri_receipts_chained i bs0 nl off0 Φ bss
            ∨ wri_receipts i Φ bss) ∗
           awrite_commits_at Γ fsabsE i Φ (length bss)
             (wchunks n - length bss)%nat)
      ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
         ∗ write_post_fail_at Γ i n M ua Φ)))%I.

End SysWriteAUEra.

Global Typeclasses Opaque write_post_ok_at write_post_fail_at
  write_arms_at write_stable_arms_at.

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
    (v v1 v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (rb : bool) (i : Z) (γo : gname)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_write_au_frame γf γs j γlp fn pidv U v v1 v2 m K eb b lks
    fd fv rb i γo
    (awrite_commits_at Γfs fsabsE i Φw 0%nat (wchunks n))
    (* RULING A: the receipts are stated at the caller's OWN image and at
       the buffer address IT passed -- syscall argument 1. *)
    (write_arms_at Γfs i n (us_M U) v1 Φw).

Definition wp_sys_write_au_era_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (fn : fwrite_names)
    (pidv : mword 32) (U : ustate)
    (v v1 v2 : mword 64)
    (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    (fd : nat) (fv : mword 64) (rb : bool) (i : Z) (γo : gname)
    (q : Qp) (bs0 : list (bv 8)) (nl : nat)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let n := sys_rw_count v2 in
  wp_sys_write_au_frame γf γs j γlp fn pidv U v v1 v2 m K eb b lks
    fd fv rb i γo
    (nview Γfs q i (MkAnode (AFile bs0) nl)
     ∗ awrite_commits_at Γfs fsabsE i Φw 0%nat (wchunks n))%I
    (write_stable_arms_at Γfs i n q bs0 nl (us_M U) v1 Φw).

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
      (v v1 v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (i : Z) (γo : gname)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_sys_write_au_era_body γf γs j γlp fn pidv U v v1 v2 m K eb b lks
        fd fv rb i γo Φw.
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
      (v v1 v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (rb : bool) (i : Z) (γo : gname)
      (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_sys_write_au_era_stable_body γf γs j γlp fn pidv U v v1 v2 m K eb b
        lks fd fv rb i γo q bs0 nl Φw.
End SYSWRITE_AU_ERA_STABLE.
