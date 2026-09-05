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
   commit per chunk, at that chunk's own retag instant, moving the
   descriptor's offset shadow in the same fupd, and accumulating the
   caller's receipts off the commit CHAIN ([FsAbsWriteFire.awrite_chain]).
   The invariant that carries it, in the landed loop's own vocabulary
   ([ProofFilewrite.fw_loop]'s [iz] and its fuel):

     ∃ p : nat, ∃ bss : list (list (bv 8)),
       ⌜length bss = p⌝
       ∗ ⌜Z.of_nat (length (concat bss)) = iz⌝     (* the offset IS the total *)
       ∗ ⌜iz = FW_MAX * Z.of_nat p⌝                (* every fired chunk is full *)
       ∗ wri_receipts i Φw bss                      (* the fired receipts       *)
       ∗ awrite_chain Γfs fsabsE i γo Φw p (wchunks n - p)   (* the rest of the chain *)

   -- and the three arithmetic facts it needs are
   [FsAbsWriteFire.wri_count_lt] (the bundle is not exhausted while the loop
   runs), [wri_count_step] (it is not exhausted after one more fire) and
   [wri_count_done] (the exit at [iz = n]).  The second conjunct is what
   makes the totals arithmetic free on BOTH arms: the ok arm exits at
   [iz = n], the fail arm at [iz < n], and in both cases the exit value of
   [iz] IS [length (concat bss)].

   THE SHORT CHUNK IS NOT FIRED -- BUT ITS OFFSET MOVE IS PAID.  writei may
   stop part-way and leave a DISTURBED tail of at most one block
   ([SpecWritei]'s [dist]); those bytes are not the splice, so that chunk's
   instant carries no receipt.  It costs little: writei promises
   [tot = n -> dist = 0] and the loop BREAKS on [r <> n1], so every chunk
   that continues the loop is full and clean, and the one that ends the
   loop is absent from [bss] -- but if it wrote anything, [f->off] advanced
   by it, and the kernel's half of the offset shadow follows through the
   chain's PARTIAL arm ([awrite_part_at]), which is why the fail arm's
   chain resumes one node past the receipts ([x <= 1]).  See
   [FsAbsWriteFire]'s header.

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
Require Import Xv6Cameras.
Require Import SpecFilewrite.   (* the landed contract this parallels       *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsBytesGamma.
Require Import Xv6G.
Require Import FsCfg.
Require Import SpecSysWriteAU.     (* [wchunks], [wri_receipts]             *)
Require Import FsAbsWriteFire.     (* [awrite_chain]                        *)
Require Import OffGv.              (* [off_gv]                              *)
Require Import SpecCopyin.         (* [ubytes_at]: the content seam         *)
Require Import SpecSysWriteAUEra.  (* [write_arms_at]                       *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbs.              (* LAST (FsAbs's own rule)               *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* [SpecFilewrite.wp_filewrite_sconf_body], premise for premise and resource
   for resource; the three edits are marked. *)
Definition wp_filewrite_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ,
      !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)                    (* kalloc, file table  *)
    (γs : list gname) (j : nat) (γlp : gname)    (* the running process     *)
    (k : nat) (q : Qp) (st : fdstate)            (* the borrowed reference  *)
    (fn : fwrite_names)                          (* the heavy arms' ghosts  *)
    (pidv : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
    (rb : bool) (i : Z) (γo : gname)             (* the descriptor's mode
                                                    bit, its inum and its
                                                    offset shadow           *)
    (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* THE USER SOURCE (RULING A).  filewrite reads [addr + i] per chunk with
     [i] its own running total, so a1 is the base the whole run is pinned
     at; a [let], not a premise, so no caller moves. *)
  let uaddr : mword 64 := m !!! Regidx (mword_of_int 11 : mword 5) in
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
  st = FdOpen rb true (FdInode i γo) ->
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
  (* EDIT 2: THE CALLER'S COMMIT CHAIN, one node per possible chunk,
     indexed from 0 ([wchunks n] of them); each node moves the bytes and the
     descriptor's offset shadow in one fupd ([FsAbsWriteFire.awrite_chain]). *)
  awrite_chain Γfs fsabsE i γo Φw 0%nat (wchunks n) -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (r : mword 64) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      (* EDIT 3: the armed post REPLACES [⌜filewrite_ret n r⌝] -- each arm
         pins [r], so the landed blanket is implied. *)
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = r⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      file_ref γf k q st -∗
      proc_priv_core pj pidv (us_upt U P') -∗
      filewrite_env_out fn st -∗
      write_arms_at Γfs i γo n (us_M U) uaddr Φw r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE LOOP'S CARRIED AU STATE, AND ITS FIVE MOVES                       *)
(* ===================================================================== *)

(* This is the vocabulary the prover of [FILEWRITE_AU] threads through
   [ProofFilewrite.fw_loop]'s induction, discharged HERE so the loop
   proof is plumbing rather than design.

   [fw_au_raw Γ i γo n Φ t p x] is "[p] chunks have fired, they wrote [t]
   bytes in total, here are their receipts and here is the rest of the
   chain, resuming [x] nodes past them" -- [x] is 0 on every loop entry and
   becomes 1 only at the exit a SHORT chunk forces, when its offset move
   spent the chain's partial arm ([FsAbsWriteFire.awrite_part_at]).  It is
   the ONLY iProp the loop carries; the two facts that make it a loop
   INVARIANT are Coq-level and ride as ordinary premises of [fw_loop]:

     t = iz   /\   t = FW_MAX * Z.of_nat p

   -- the fired total IS the running offset, and every fired chunk was
   exactly [FW_MAX].  THERE IS NO [clean] FLAG AND NO SLACK.  Both were
   the price of a gap that is now closed: a chunk fires only when its
   start is INSIDE the file ([wri_pre]'s [off <= length bs0], the splice's
   own side condition), and [SpecWritei]'s SUCCESS ARM NOW REPORTS THAT
   GUARD (owner's ruling, 2026-08-29 -- the writing arm carries
   [off <= di_size] of the pre-write record, the negation of the reason
   its own [-1] arm carries).  So no chunk the loop completes has to be
   skipped, [t] never falls behind [iz], and the loop needs neither the
   inequality nor a branch for the case it admitted.

   WHY THE TIE IS NOT INSIDE THE iProp.  The last chunk may be SHORT, so
   [t = FW_MAX * p] is false of the state the exhausted exit hands out; it
   is a truth about every LOOP ENTRY, not about every state.  Keeping it
   Coq-level is what lets the four moves below be tie-free.

   THE FIVE MOVES, one per thing the loop does with it: start it
   ([_init]), spend one node's FULL arm at a chunk's fire ([_take] -- the
   peel and the receipt snoc, with the instant-count bound coming from
   [FsAbsWriteFire.wri_count_step]), spend one node's PARTIAL arm at a
   short chunk's offset move ([_spend_part]), and read it off at each of
   the two exits ([_ok] at [t = n], [_fail] at [t < n] or at the
   capstone's never-entered loop). *)

Section FilewriteAUState.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  Definition fw_au_raw Γ (i : Z) (γo : gname) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (t : Z) (p x : nat) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜length bss = p⌝ ∗
       ⌜Z.of_nat (length (concat bss)) = t⌝ ∗
       ⌜(p + x <= wchunks n)%nat⌝ ∗
       ⌜(x <= 1)%nat⌝ ∗
       (* THE CONTENT HALF (RULING A).  What has been spliced so far IS the
          caller's own run at [ua].  It rides INSIDE the iProp rather than as
          a Coq-level tie beside it, because unlike [t = FW_MAX * p] it is
          true of every state the loop hands out -- the exhausted exit
          included -- and both exits read it off unchanged. *)
       ⌜ubytes_at M ua (concat bss)⌝ ∗
       wri_receipts i Φ bss ∗
       awrite_chain Γ fsabsE i γo Φ (p + x) (wchunks n - p - x)%nat)%I.

  Lemma fw_au_raw_init Γ (i : Z) γo (n : Z) M ua Φ :
    awrite_chain Γ fsabsE i γo Φ 0%nat (wchunks n) -∗
    fw_au_raw Γ i γo n M ua Φ 0 0%nat 0%nat.
  Proof.
    iIntros "Hcm". rewrite /fw_au_raw. iExists [].
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; apply ubytes_at_nil |].
    iSplitR; [iApply wri_receipts_nil |].
    rewrite !Nat.sub_0_r (Nat.add_0_r 0). iExact "Hcm".
  Qed.

  (* ONE CHUNK'S FIRE, both halves: the head node's FULL arm comes out at the
     index the chain handed it out at (its continuation IS the rest of the
     chain), and the closer takes the receipt and that rest back. *)
  Lemma fw_au_raw_take Γ (i : Z) γo (n : Z) M ua Φ (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_raw Γ i γo n M ua Φ t p 0%nat -∗
      awrite_full_at Γ fsabsE i γo p Φ
        (awrite_chain Γ fsabsE i γo Φ (S p) (wchunks n - S p)) ∗
      (∀ (bs : list (bv 8)) (av : aview) (off : nat) (bs0 : list (bv 8))
         (nl : nat),
         ⌜wri_pre av i off bs bs0 nl⌝ -∗
         (* THE CONTENT PREMISE (RULING A): this chunk was copied from the
            base BUMPED BY THE RUNNING TOTAL, which is [t] -- filewrite's
            [add a2,s4,s6] with [s4 = i] the loop's own count.  That is the
            whole of what the fire owes, and it is exactly what
            [SpecWritei]'s user-arm clause delivers. *)
         ⌜ubytes_at M (add_vec_int ua t) bs⌝ -∗
         Φ p av off bs -∗
         awrite_chain Γ fsabsE i γo Φ (S p) (wchunks n - S p) -∗
         fw_au_raw Γ i γo n M ua Φ (t + Z.of_nat (length bs)) (S p) 0%nat).
  Proof.
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_raw.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hrs & Hcm)".
    (* the peel: the chain has at least one node left *)
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_S.
    iDestruct "Hcm" as "[Hhead _]".
    iFrame "Hhead". iIntros (bs av off bs0 nl) "%Hpre %Hbyc HΦ Htail".
    iExists (bss ++ [bs])%list.
    assert (Hlen' : length ((bss ++ [bs])%list) = S p)
      by (rewrite length_app Hlen /=; lia).
    iSplitR; [by iPureIntro |].
    iSplitR.
    { iPureIntro. rewrite concat_app length_app /= app_nil_r. lia. }
    iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; lia |].
    (* THE APPEND: the accumulated run and this chunk are ADJACENT at [ua],
       because [t] IS the accumulated length ([Htot]). *)
    iSplitR.
    { iPureIntro. rewrite concat_app /= app_nil_r.
      apply (ubytes_at_app M ua (concat bss) bs Hby).
      rewrite Htot. exact Hbyc. }
    iSplitL "Hrs HΦ".
    { iApply (wri_receipts_snoc i Φ bss bs av off bs0 nl Hpre
                with "Hrs [HΦ]"). rewrite Hlen. iExact "HΦ". }
    rewrite (Nat.add_0_r (S p)) (Nat.sub_0_r (wchunks n - S p)). iExact "Htail".
  Qed.

  (* ONE SHORT CHUNK'S OFFSET MOVE: the head node's PARTIAL arm comes out,
     and the closer takes the rest of the chain back one node further on,
     with no receipt -- the state the fail exit reads off. *)
  Lemma fw_au_raw_spend_part Γ (i : Z) γo (n : Z) M ua Φ (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_raw Γ i γo n M ua Φ t p 0%nat -∗
      awrite_part_at fsabsE γo
        (awrite_chain Γ fsabsE i γo Φ (S p) (wchunks n - S p)) ∗
      (awrite_chain Γ fsabsE i γo Φ (S p) (wchunks n - S p) -∗
       fw_au_raw Γ i γo n M ua Φ t p 1%nat).
  Proof.
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_raw.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hrs & Hcm)".
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_S.
    iDestruct "Hcm" as "[_ Hpart]".
    iFrame "Hpart". iIntros "Htail".
    iExists bss.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; lia |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [by iPureIntro |]. iFrame "Hrs".
    assert (Hcnt' : (wchunks n - p - 1 = wchunks n - S p)%nat) by lia.
    rewrite Hcnt' Nat.add_1_r. iExact "Htail".
  Qed.

  (* THE EXITS *)
  Lemma fw_au_raw_ok Γ (i : Z) γo (n : Z) M ua Φ (p : nat) :
    fw_au_raw Γ i γo n M ua Φ n p 0%nat -∗ write_post_ok_at Γ i γo n M ua Φ.
  Proof.
    iIntros "Hst". rewrite /fw_au_raw /write_post_ok_at.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hrs & Hcm)".
    iExists bss. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; lia |]. iSplitR; [by iPureIntro |].
    iFrame "Hrs". rewrite Hlen (Nat.add_0_r p) (Nat.sub_0_r (wchunks n - p)). iExact "Hcm".
  Qed.

  (* THE FAIL EXIT, AT BOTH OF ITS TWO SHAPES.  [t < n] is the loop's own
     (the short-write break, the only way out of the loop that is not the
     count); the second disjunct is the CAPSTONE's, on the [n < 0] guard at
     +0x20, where the loop is never entered and the chain refunds whole. *)
  Lemma fw_au_raw_fail Γ (i : Z) γo (n : Z) M ua Φ (t : Z) (p x : nat) :
    (t < n)%Z \/ (n < 0)%Z /\ p = 0%nat ->
    fw_au_raw Γ i γo n M ua Φ t p x -∗ write_post_fail_at Γ i γo n M ua Φ.
  Proof.
    intros Hex. iIntros "Hst". rewrite /fw_au_raw /write_post_fail_at.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hrs & Hcm)".
    iExists bss, x. iSplitR.
    { iPureIntro. destruct Hex as [Htn | [Hneg Hp0]].
      - left. lia.
      - right. split; [exact Hneg |].
        apply nil_length_inv. rewrite Hlen. exact Hp0. }
    iSplitR; [iPureIntro; lia |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [by iPureIntro |].
    iFrame "Hrs". rewrite Hlen. iExact "Hcm".
  Qed.

End FilewriteAUState.

Global Typeclasses Opaque fw_au_raw.

Module Type FILEWRITE_AU.
  Parameter wp_filewrite_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate)
      (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (lks : gset string) (rb : bool) (i : Z) (γo : gname)
      (Φw : nat -> aview -> nat -> list (bv 8) -> iProp Σ),
      wp_filewrite_au_body γf γs j γlp k q st fn pidv U m K eb n b lks
        rb i γo Φw.
End FILEWRITE_AU.
