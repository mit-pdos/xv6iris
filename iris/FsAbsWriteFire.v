(* FsAbsWriteFire.v -- sys_write's PER-CHUNK FIRE POINT, DISCHARGED AGAINST
   THE INVARIANT, plus the reading bridge and the instant-count arithmetic
   [SpecSysWriteAU]'s header owes its prover (items 1, 2, 4 and the [wri_pre]
   half of item 5).

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the write AU
   prover).  A NEW LEAF rather than an append to [FsAbsMknodFire.v] /
   [FsAbsOpenFire.v], for the mirror's reason every other campaign leaf
   records ([FsAbsNpar], [FsAbsPins], [FsAbsStart]): the build mirror forbids
   touching a tracked file.  Fuse the fire leaves when one of them is next
   edited.

   ==== WHY THE COMMITS ARE RESTATED AT THE AUTHORITY ===================

   [FsAbsMknodFire]'s FIRST FINDING, verbatim at the write delta, and it is
   the reason this file exists at all.  [SpecSysWriteAU.awrite_commit] is
   stated over [FsAbs.astate]:

       astate Γ av ={E}=∗ astate Γ av ∗
         (astate Γ (delta_write i off bs av) ={E}=∗ ... ∗ Φ k av off bs)

   and the prover's only source of [astate] is the γtop authority inside
   [InodeRegion.ftop_inv].  Borrowing it is fine; GIVING IT BACK is not.
   [astate Γ av] is [∃ I, ghost_map_auth (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝]
   and [abs_view] IS NOT INJECTIVE, so what a client's fupd returns is an
   authority at SOME map with the right READING -- while [ftop_body]'s row
   ([ftop_clean I A]) is a statement about the RECORDS.  Concretely: a
   client may move a file's block map, keeping its bytes, and hand back an
   authority at which [inode_local] no longer holds; the invariant cannot
   be closed.  So the astate-shaped commit is not dischargeable, IN EITHER
   PHASE, and the two-phase forms do not relate in either direction (phase
   2 names the POST map, which no [astate] at the delta determines).

   [awrite_commit_at] below is therefore a PARALLEL FORM beside the frozen
   one, in the campaign's usual sense -- R10 leaves [SpecSysWriteAU]
   byte-identical and the era-side contract ([SpecSysWriteAUEra]) carries
   these.  Everything the frozen file offers a client is offered here at the
   same strength: the trivial-receipt units ([_unit]) and the agreement seed
   ([_pinned]) the stable corollary is derived from.

   ==== THE FIRE POINT: ONE PER CHUNK, AT THAT CHUNK'S RETAG =============

   [wrf_awrite_fire] is [FsAbsMknodFire.mkf_acre_fire]'s /
   [FsAbsOpenFire.opf_atrunc_fire]'s two-phase mold at
   [SpecSysWriteAU.delta_write], FUSED WITH THE ROW RETAG: it replaces the
   [InodeRegion.ireg_top_retag] filewrite's inode arm performs after writei
   returns (ProofFilewrite.v's "THE RETAG OWES THE ROW"), with one extra
   premise (the chunk's commit) and one extra payout (the receipt).  Same
   [inode_local] premise, same payout, and the caller's two phases on
   either side of the [ghost_map_update] INSIDE the one [ftopN] critical
   section -- which is what makes the pair ONE instant per chunk.

   THE PEEL IS NOT NEEDED HERE, and that is a finding.  sys_open's trunc
   commit had to travel with a PEELED payload ([ProofSysOpenAUParts.so_flat])
   because one [bs0] is shared between an observation fired at [ilock] and a
   receipt fired at the retag far below, with an existential [data] resealed
   in between.  filewrite's chunks each RE-LOCK: every chunk opens its own
   [ic_loaded], reads its own [datal], fires, and reseals before the next
   [ilock].  The pre-row a chunk's phase 1 observes is read off the SAME
   [top_frag] the fire retags, inside the same critical section, so no
   witness has to survive a reseal and the payload travels sealed.

   ==== ITEM 2: THE READING BRIDGE ======================================

   [wrf_file_bytes_splice] is the pure heart: writei's RANGE CLAUSE plus its
   size arithmetic IS the splice.  Given [off <= sz] and the pointwise
   reading "the new bytes are [wrote] inside [off, off+tot) and the old ones
   outside", the new file's byte list at the new size [max (off+tot) sz] is
   [blk_splice off (wrote <$> seq 0 tot)] of the old one -- with the length
   coming out of [SpecSysWriteAU.blk_splice_length_grow], which is exactly
   why the delta MAY GROW the file.  [wrf_write_row] lifts it through
   [abs_of] at an era node, and [wrf_wi_size] is the [wi_dinode] half.

   THE [dist] CAVEAT, AND WHY IT COSTS THE PROOF NOTHING.  writei's post
   allows a DISTURBED region of at most one block immediately after the
   written range -- the in-memory tail of a block whose either_copyin
   faulted part-way.  Its bytes are NOT the splice, so a chunk with
   [dist <> 0] must not be fired.  It never has to be: writei promises
   [tot = n -> dist = 0], and filewrite's loop BREAKS on [r <> n1], so every
   chunk that continues the loop is a FULL chunk with [dist = 0] and the
   short chunk that ends it is not fired at all (its bytes are simply not
   in [bss], and the fail arm's total falls short by exactly that much).
   This is the one place the contract's honest silence about WHERE the loop
   died is load-bearing.

   ==== ITEM 4: THE INSTANT COUNT =======================================

   Section 4's arithmetic, and it is sharper than "at most [wchunks n]":
   EVERY FIRED CHUNK BUT THE LAST IS EXACTLY [FW_MAX] BYTES.  The kernel's
   chunk is [min (n - i) FW_MAX], so a chunk shorter than [FW_MAX] exhausts
   the count and the loop exits -- hence while the loop is running the total
   written is [p * FW_MAX] for [p] fired chunks.  [wri_count_lt] and
   [wri_count_step] are that invariant's two uses (the running bound and the
   bound after one more fire); [wri_count_full] is the exit at [t = n].
   The loop invariant this file is written for is therefore

       Z.of_nat iz = FW_MAX * Z.of_nat p   /\   iz = length (concat bss)

   -- the running offset IS the fired total, and the fired COUNT is that
   total divided by the chunk cap.

   BINDERS: [FsAbsMknodFire]'s section list VERBATIM (which is
   [SpecSysWriteAU]'s) -- [fileG] is bound and [icacheG]/[icfg] resolve only
   through its fields. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import RiscvExtras.      (* [moi32_small]                           *)
Require Import DinodeEnc.
Require Import DirView.          (* [T_DIR_z]                               *)
Require Import FsTree.           (* [file_bytes]                            *)
Require Import PathElems.
Require Import FsBlocks.         (* [blk_splice] and its three lookups      *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import BioDefs.          (* [BSIZE]                                 *)
Require Import InodeDefs.        (* [file_byte]                             *)
Require Import InodeInv.         (* [MAXFILE], [blk_holes_zero]             *)
Require Import InodeLock.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
(* the three binder classes the section list names, IMPORTED rather than
   inherited ([FsAbsMknodFire]'s header records why). *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import SpecWritei.       (* [wi_dinode]                             *)
Require Import SpecFilewrite.    (* [FW_MAX]                                *)
Require Import SpecSysMknodAU.   (* [abs_view_insert]                       *)
Require Import SpecSysWriteAU.   (* the contract this file serves           *)
Require Import FsAbsMknodFire.   (* [mkf_auth_nview]                        *)
Require Import FsAbsOpenFire.    (* [opf_era_file_row], [opf_era_type]      *)
Require FsImg.                   (* [T_FILE_z] -- Require, NOT Import       *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE BYTE-LIST ARITHMETIC (pure, no binder)                        *)
(* ===================================================================== *)

Lemma wrf_fb_length (data : nat -> list (bv 8)) (sz : nat) :
  length (file_bytes data sz) = sz.
Proof. rewrite /file_bytes length_fmap length_seq //. Qed.

Lemma wrf_fb_lookup (data : nat -> list (bv 8)) (sz j : nat) :
  (j < sz)%nat -> file_bytes data sz !! j = Some (file_byte data j).
Proof.
  intros Hj. rewrite /file_bytes list_lookup_fmap.
  assert (Hs : seq 0 sz !! j = Some j).
  { apply lookup_seq. split; [lia | exact Hj]. }
  rewrite Hs //.
Qed.

(* the written run, as a list *)
Definition wrf_run (wrote : nat -> bv 8) (tot : nat) : list (bv 8) :=
  wrote <$> seq 0 tot.

Lemma wrf_run_length (wrote : nat -> bv 8) (tot : nat) :
  length (wrf_run wrote tot) = tot.
Proof. rewrite /wrf_run length_fmap length_seq //. Qed.

Lemma wrf_run_lookup (wrote : nat -> bv 8) (tot j : nat) :
  (j < tot)%nat -> wrf_run wrote tot !! j = Some (wrote j).
Proof.
  intros Hj. rewrite /wrf_run list_lookup_fmap.
  assert (Hs : seq 0 tot !! j = Some j).
  { apply lookup_seq. split; [lia | exact Hj]. }
  rewrite Hs //.
Qed.

(* ---- ITEM 2's PURE HEART: THE RANGE CLAUSE IS THE SPLICE ------------- *)

(* The hypothesis is BOUNDED ([k] below the new size) on purpose: at the era
   node the pointwise reading only transports below [MAXFILE * BSIZE], which
   the file cap makes exactly the range this lemma consults. *)
Lemma wrf_file_bytes_splice (data data' : nat -> list (bv 8))
    (sz off tot : nat) (wrote : nat -> bv 8) :
  (off <= sz)%nat ->
  (forall k : nat, (k < Nat.max (off + tot) sz)%nat ->
     file_byte data' k
     = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
       then wrote (k - off)%nat
       else file_byte data k) ->
  file_bytes data' (Nat.max (off + tot) sz)
  = blk_splice off (wrf_run wrote tot) (file_bytes data sz).
Proof.
  intros Hoff Hbytes.
  assert (Hsub : length (wrf_run wrote tot) = tot) by apply wrf_run_length.
  assert (Hbs : length (file_bytes data sz) = sz) by apply wrf_fb_length.
  assert (Hlen : length (blk_splice off (wrf_run wrote tot)
                           (file_bytes data sz))
                 = Nat.max (off + tot) sz).
  { rewrite (blk_splice_length_grow off (wrf_run wrote tot)
               (file_bytes data sz) ltac:(rewrite Hbs; exact Hoff)).
    rewrite Hsub Hbs //. }
  apply list_eq. intros j.
  destruct (decide (j < Nat.max (off + tot) sz)%nat) as [Hj | Hj];
    [| rewrite lookup_ge_None_2; [| rewrite wrf_fb_length; lia];
       symmetry; apply lookup_ge_None_2; rewrite Hlen; lia].
  rewrite (wrf_fb_lookup data' _ j Hj) (Hbytes j Hj).
  destruct (decide (j < off)%nat) as [Hlt | Hge].
  - rewrite (blk_splice_lookup_lt off (wrf_run wrote tot) (file_bytes data sz)
               j ltac:(rewrite Hbs; exact Hoff) Hlt).
    rewrite (wrf_fb_lookup data sz j ltac:(lia)).
    destruct (decide ((off <= j)%nat /\ (j < off + tot)%nat)) as [[H1 _] | _];
      [lia | reflexivity].
  - destruct (decide (j < off + tot)%nat) as [Hmid | Hgi].
    + rewrite (blk_splice_lookup_mid off (wrf_run wrote tot)
                 (file_bytes data sz) j ltac:(rewrite Hbs; exact Hoff)
                 ltac:(lia) ltac:(rewrite Hsub; lia)).
      rewrite (wrf_run_lookup wrote tot (j - off)%nat ltac:(lia)).
      destruct (decide ((off <= j)%nat /\ (j < off + tot)%nat)) as [_ | Hno];
        [reflexivity | exfalso; apply Hno; lia].
    + rewrite (blk_splice_lookup_ge off (wrf_run wrote tot)
                 (file_bytes data sz) j ltac:(rewrite Hbs; exact Hoff)
                 ltac:(rewrite Hsub; lia)).
      rewrite (wrf_fb_lookup data sz j ltac:(lia)).
      destruct (decide ((off <= j)%nat /\ (j < off + tot)%nat)) as [[_ H2] | _];
        [lia | reflexivity].
Qed.

(* ---- THE ERA NODE's TRANSPORT --------------------------------------- *)

(* [k `div` BSIZE] is inside the block map exactly when [k] is inside the
   file cap, which is the only range the readings above consult. *)
Lemma wrf_div_maxfile (k : nat) :
  (k < MAXFILE * BSIZE)%nat -> (k `div` BSIZE < MAXFILE)%nat.
Proof.
  intros Hk.
  assert (Hlt : (k < BSIZE * MAXFILE)%nat)
    by (unfold MAXFILE, BSIZE, NDIRECT in *; lia).
  first [ apply Nat.Div0.div_lt_upper_bound; exact Hlt
        | apply Nat.div_lt_upper_bound; [unfold BSIZE; lia | exact Hlt] ].
Qed.

Lemma wrf_era_file_byte (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (k : nat) :
  blk_holes_zero bm data -> (k < MAXFILE * BSIZE)%nat ->
  file_byte (fn_data (era_node dn bm data)) k = file_byte data k.
Proof.
  intros Hh Hk. rewrite /file_byte.
  rewrite (era_node_data dn bm data (k `div` BSIZE)%nat Hh
             (wrf_div_maxfile k Hk)) //.
Qed.

Lemma wrf_era_bytes (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  fn_file_bytes (era_node dn bm data)
  = file_bytes (fn_data (era_node dn bm data))
               (Z.to_nat (bv_unsigned (di_size dn))).
Proof. rewrite /fn_file_bytes /fn_size era_node_rec //. Qed.

(* [wi_dinode]'s size IS the [max] the splice's length says it must be. *)
Lemma wrf_wi_size (dn : dinode) (bm' : blkmap) (off tot : nat) :
  (Z.of_nat (off + tot) < 2 ^ 32) ->
  Z.to_nat (bv_unsigned (di_size (wi_dinode dn bm' off tot)))
  = Nat.max (off + tot) (Z.to_nat (bv_unsigned (di_size dn))).
Proof.
  intros Hlt.
  pose proof (bv_unsigned_in_range _ (di_size dn)) as [Hlo Hhi].
  rewrite /wi_dinode /=.
  destruct (decide (bv_unsigned (di_size dn) < Z.of_nat (off + tot)))
    as [Hgrow | Hkeep].
  - rewrite (moi32_small (Z.of_nat (off + tot)) ltac:(lia)). lia.
  - lia.
Qed.

(* ---- THE ROW, END TO END -------------------------------------------- *)

(* The premises are exactly what filewrite's inode arm holds when writei
   returns on its success arm: the record's type is [T_FILE], the two
   payloads normalise their holes, the size grew to the [max], the range
   clause is writei's own (with [dist = 0], see the header), and the start
   is inside the old bytes. *)
Lemma wrf_write_row (dn dn' : dinode) (bm bm' : blkmap)
    (data data' : nat -> list (bv 8)) (off tot : nat) (wrote : nat -> bv 8) :
  bv_unsigned (di_type dn) = FsImg.T_FILE_z ->
  di_type dn' = di_type dn ->
  di_nlink dn' = di_nlink dn ->
  blk_holes_zero bm data ->
  blk_holes_zero bm' data' ->
  Z.to_nat (bv_unsigned (di_size dn'))
    = Nat.max (off + tot) (Z.to_nat (bv_unsigned (di_size dn))) ->
  (off <= Z.to_nat (bv_unsigned (di_size dn)))%nat ->
  (off + tot <= MAXFILE * BSIZE)%nat ->
  (Z.to_nat (bv_unsigned (di_size dn)) <= MAXFILE * BSIZE)%nat ->
  (forall k : nat, (k < MAXFILE * BSIZE)%nat ->
     file_byte data' k
     = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
       then wrote (k - off)%nat
       else file_byte data k) ->
  abs_of (era_node dn' bm' data')
  = MkAnode (AFile (blk_splice off (wrf_run wrote tot)
                      (fn_file_bytes (era_node dn bm data))))
            (fn_nlink (era_node dn bm data)).
Proof.
  intros Hty Hty' Hnl' Hh Hh' Hsz' Hoff Hcap Hcap0 Hrange.
  assert (Hty2 : bv_unsigned (di_type dn') = FsImg.T_FILE_z)
    by (rewrite Hty'; exact Hty).
  assert (Hnl : fn_nlink (era_node dn' bm' data')
                = fn_nlink (era_node dn bm data))
    by (rewrite /fn_nlink !era_node_rec Hnl' //).
  assert (Hb : fn_file_bytes (era_node dn' bm' data')
               = blk_splice off (wrf_run wrote tot)
                   (fn_file_bytes (era_node dn bm data))).
  { rewrite (wrf_era_bytes dn' bm' data') (wrf_era_bytes dn bm data) Hsz'.
    apply (wrf_file_bytes_splice (fn_data (era_node dn bm data))
             (fn_data (era_node dn' bm' data'))
             (Z.to_nat (bv_unsigned (di_size dn))) off tot wrote Hoff).
    intros k Hk.
    assert (Hkb : (k < MAXFILE * BSIZE)%nat) by lia.
    rewrite (wrf_era_file_byte dn' bm' data' k Hh' Hkb)
            (wrf_era_file_byte dn bm data k Hh Hkb).
    exact (Hrange k Hkb). }
  rewrite (opf_era_file_row dn' bm' data' Hty2) Hb Hnl //.
Qed.

(* ===================================================================== *)
(*  1.  ITEM 4: THE INSTANT COUNT                                         *)
(* ===================================================================== *)

(* [t] bytes written in [p] full chunks, and the loop still running: the
   bundle has not been exhausted. *)
Lemma wri_count_lt (n t : Z) (p : nat) :
  0 <= t -> t < n -> t = FW_MAX * Z.of_nat p -> (p <= wchunks n)%nat.
Proof.
  intros Ht Htn Heq. rewrite /wchunks.
  assert (Hd : Z.of_nat p <= (n + FW_MAX - 1) / FW_MAX).
  { apply Z.div_le_lower_bound; rewrite /FW_MAX in Heq |- *; lia. }
  lia.
Qed.

(* ...and after ONE more chunk fires, whatever its size. *)
Lemma wri_count_step (n t : Z) (p : nat) :
  0 <= t -> t < n -> t = FW_MAX * Z.of_nat p -> (S p <= wchunks n)%nat.
Proof.
  intros Ht Htn Heq. rewrite /wchunks.
  assert (Hd : Z.of_nat (S p) <= (n + FW_MAX - 1) / FW_MAX).
  { apply Z.div_le_lower_bound; rewrite /FW_MAX in Heq |- *; lia. }
  lia.
Qed.

(* the exit reading: the count the ok arm reports IS the fired total *)
Lemma wri_count_done (n : Z) (p : nat) :
  0 <= n -> n = FW_MAX * Z.of_nat p -> (p <= wchunks n)%nat.
Proof.
  intros Hn Heq. rewrite /wchunks.
  assert (Hd : Z.of_nat p <= (n + FW_MAX - 1) / FW_MAX).
  { apply Z.div_le_lower_bound; rewrite /FW_MAX in Heq |- *; lia. }
  lia.
Qed.

(* the chunk the kernel picks is positive whenever the loop is entered --
   [wri_pre]'s [0 < length bs] guard, at the source *)
Lemma wri_chunk_pos (n t : Z) : 0 <= t -> t < n -> 0 < Z.min (n - t) FW_MAX.
Proof. intros Ht Htn. rewrite /FW_MAX. lia. Qed.

Section WriteFire.
  (* [FsAbsMknodFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  2.  THE AUTHORITY-SHAPED CHUNK COMMIT                               *)
  (* =================================================================== *)

  (* [SpecSysWriteAU.awrite_commit] one step down: the RAW MAP goes in and
     the very same [ghost_map_auth] comes back, so the invariant's row
     obligation survives.  Phase 2 is quantified over the POST map and
     constrained by its READING alone, so a client still witnesses exactly
     "the chunk's delta was applied" and nothing about the record the mover
     chose. *)
  Definition awrite_commit_at Γ (E : coPset) (i : Z) (k : nat)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) 1 I' ={E}=∗
            ghost_map_auth (γtop Γ) 1 I' ∗ Φ k (abs_view I) off bs))%I.

  (* THE BUNDLE, at the same indexing as [SpecSysWriteAU.awrite_commits]. *)
  Definition awrite_commits_at Γ (E : coPset) (i : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (lo cnt : nat) : iProp Σ :=
    ([∗ list] k ∈ seq lo cnt, awrite_commit_at Γ E i k Φ)%I.

  (* the loop's own peel: fire the head, carry the tail *)
  Lemma awrite_commits_at_peel Γ E i Φ lo cnt :
    awrite_commits_at Γ E i Φ lo (S cnt)
    ⊣⊢ awrite_commit_at Γ E i lo Φ ∗ awrite_commits_at Γ E i Φ (S lo) cnt.
  Proof.
    rewrite /awrite_commits_at /= //.
  Qed.

  Lemma awrite_commits_at_nil Γ E i Φ lo :
    ⊢ awrite_commits_at Γ E i Φ lo 0.
  Proof. rewrite /awrite_commits_at //=. Qed.

  (* satisfiability: the seal cannot be vacuously blocked on the caller's
     side ([SpecSysWriteAU]'s [_unit] pair, restated at this shape) *)
  Lemma awrite_commit_at_unit Γ E i k :
    ⊢ awrite_commit_at Γ E i k (fun _ _ _ _ => True%I).
  Proof.
    rewrite /awrite_commit_at. iIntros (I off bs bs0 nl) "%Hpre Ha".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma awrite_commits_at_unit Γ E i lo cnt :
    ⊢ awrite_commits_at Γ E i (fun _ _ _ _ => True%I) lo cnt.
  Proof.
    rewrite /awrite_commits_at. iApply big_sepL_intro.
    iIntros "!>" (j k Hk). iApply awrite_commit_at_unit.
  Qed.

  (* THE STABLE SEED at this shape: a held [nview] share turns the phase-1
     observation into "a state whose row at MY inum is MY value".
     [FsAbsMknodFire.mkf_auth_nview] is the agreement, reused. *)
  Lemma awrite_commit_at_pinned Γ E (i : Z) (k : nat) (q : Qp) (jpin : Z)
      (a : anode) (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :
    nview Γ q jpin a -∗
    (∀ (av : aview) (off : nat) (bs : list (bv 8)),
       ⌜av !! jpin = Some a⌝ -∗ nview Γ q jpin a -∗ Φ k av off bs) -∗
    awrite_commit_at Γ E i k Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /awrite_commit_at.
    iIntros (I off bs bs0 nl) "%Hpre Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'". iApply ("HΦ" $! (abs_view I) off bs with "[%] Hn"). done.
  Qed.

  (* =================================================================== *)
  (*  3.  ITEM 1: THE CHUNK FIRE, FUSED WITH THE ROW RETAG                *)
  (* =================================================================== *)

  (* Replaces the [InodeRegion.ireg_top_retag] filewrite's inode arm calls
     after writei returns: same [inode_local] premise, same payout (the
     moved fragment), plus the caller's two phases inside the one [ftopN]
     critical section.  The receipt's pre-state row is the OBSERVED one --
     the fragment read is the one the fire retags, so nothing can move
     between the observation and the update. *)
  Lemma wrf_awrite_fire (γfs : fs_names) (E : coPset) (i : Z) (k : nat)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (off : nat) (bs bs0 : list (bv 8)) (nl : nat) (n n' : fs_node) :
    ↑ftopN ⊆ E ->
    inode_local i n' ->
    (0 < length bs)%nat ->
    (off <= length bs0)%nat ->
    (off + length bs <= MAXFILE * BSIZE)%nat ->
    abs_of n = MkAnode (AFile bs0) nl ->
    abs_of n' = MkAnode (AFile (blk_splice off bs bs0)) nl ->
    ftop_inv γfs -∗
    awrite_commit_at (fs_gamma_L γfs) ∅ i k Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      top_frag (fs_gamma_L γfs) i n'
      ∗ ∃ av : aview, ⌜wri_pre av i off bs bs0 nl⌝ ∗ Φ k av off bs.
  Proof.
    intros HE Hloc Hpos Hoff Hcap Habs Habs'. iIntros "#Hi Hcm Hf".
    (* the re-spelling [mkf_acre_fire] does, and for the same reason: the
       unifier cannot solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! i = Some (MkAnode (AFile bs0) nl)).
    { by rewrite (abs_view_lookup I i n Hlk) Habs. }
    assert (Hpre : wri_pre (abs_view I) i off bs bs0 nl).
    { rewrite /wri_pre. split_and!; [exact Hrow | exact Hpos | exact Hoff |
                                     exact Hcap]. }
    (* the delta collapses to the ONE-ROW insert, and the insert's reading
       is the written record's own row *)
    assert (Hdelta : abs_view (<[i := n']> I)
                     = delta_write i off bs (abs_view I)).
    { rewrite (abs_view_insert I i n') Habs'.
      by rewrite (delta_write_file (abs_view I) i off bs bs0 nl Hrow). }
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
    iMod ("Hcm" $! I off bs bs0 nl with "[//] Hta") as "[Hta Hph2]".
    iMod (ghost_map_update n' with "Hta Hf") as "[Hta Hf]".
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = i)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* =================================================================== *)
  (*  4.  THE RECEIPT BUNDLE'S SNOC                                       *)
  (* =================================================================== *)

  (* what the loop does with a fired chunk: append its receipt to the
     accumulator, at the index the bundle handed it out at *)
  Lemma wri_receipts_snoc (i : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ)
      (bss : list (list (bv 8))) (bs : list (bv 8))
      (av : aview) (off : nat) (bs0 : list (bv 8)) (nl : nat) :
    wri_pre av i off bs bs0 nl ->
    wri_receipts i Φ bss -∗ Φ (length bss) av off bs -∗
    wri_receipts i Φ (bss ++ [bs]).
  Proof.
    intros Hpre. iIntros "Hrs HΦ". rewrite /wri_receipts.
    rewrite big_sepL_app. iFrame "Hrs". simpl.
    rewrite Nat.add_0_r. iSplitL; [| done].
    iExists av, off, bs0, nl. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  Lemma wri_receipts_nil (i : Z)
      (Φ : nat -> aview -> nat -> list (bv 8) -> iProp Σ) :
    ⊢ wri_receipts i Φ [].
  Proof. rewrite /wri_receipts //. Qed.

End WriteFire.

(* the big-op bodies get the same seal [SpecSysWriteAU] gives its own *)
Global Typeclasses Opaque awrite_commits_at.
