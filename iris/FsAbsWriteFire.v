(* FsAbsWriteFire.v -- sys_write's PER-CHUNK FIRE POINT, DISCHARGED AGAINST
   THE INVARIANT, plus the reading bridge and the instant-count arithmetic
   the write contract's prover owes -- with the descriptor's OFFSET SHADOW
   folded into every commit (OffGv.v; design/file-table.md "The offset
   SHADOW").

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the write AU
   prover).  A NEW LEAF rather than an append to [FsAbsMknodFire.v] /
   [FsAbsOpenFire.v], for the mirror's reason every other campaign leaf
   records ([FsAbsNpar], [FsAbsPins], [FsAbsStart]): the build mirror forbids
   touching a tracked file.  Fuse the fire leaves when one of them is next
   edited.

   ==== WHY THE COMMITS ARE RESTATED AT THE AUTHORITY ===================

   [FsAbsMknodFire]'s FIRST FINDING, verbatim at the write delta, and it is
   the reason this file exists at all.  The astate-shaped commit the
   campaign first wrote was stated over [FsAbs.astate]:

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

   [awrite_full_at] below is therefore stated at the AUTHORITY, and it is
   the ONLY form the write contract carries.

   ==== THE OFFSET FOLD, AND WHY THE BUNDLE BECAME A CHAIN ==============

   Every commit LENDS the ONE half of the descriptor's offset shadow the
   kernel owns ([off_gv γo ½]): in at the chunk's offset, out at the SAME
   offset (the piece-shape rule -- the fire lemma does the advance, out of
   the row's [off_user_inv]).  So the client cannot pre-build [wchunks n]
   independent commits -- each would have to hold the half -- and the
   bundle is a CHAIN
   ([awrite_chain]): one node at a time, each node the PREFIX CURSOR [Q k]
   beside an [∧] of the FULL arm ([awrite_full_at], whose phase 2 returns
   the rest of the chain) and the PARTIAL arm ([awrite_part_at]: a SHORT
   chunk, whose row moved by the run that LANDED -- the counted bytes plus
   writei's disturbed tail -- while [f->off] advanced only by the count).
   The kernel picks the arm; the partial arm ends the loop, so it is spent
   at most once.  The caller reads the cursor off at the stop position
   ([awrite_chain_cursor]).
   Satisfiability is [awrite_chain_unit] / [FsAbsInvFire.fsabs_awrite_chain]:
   a client holding NOTHING but the application's step, since the shadow
   comes back unmoved.

   ==== THE FIRE POINT: ONE PER CHUNK, AT THAT CHUNK'S RETAG =============

   [wrf_awrite_fire] is [FsAbsMknodFire.mkf_acre_fire]'s /
   [FsAbsOpenFire.opf_atrunc_fire]'s two-phase mold at
   [FsAbsDelta.delta_write], FUSED WITH THE ROW RETAG: it replaces the
   [InodeRegion.ireg_top_retag_*] filewrite's inode arm performs after writei
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
   coming out of [FsAbsDelta.blk_splice_length_grow], which is exactly
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
   in [bss], and the fail arm's total falls short by exactly that much) --
   its bytes are NOT the splice of the caller's chunk -- but it is not
   silent either: the chain's PARTIAL arm fires at the run that really
   landed ([wrf_landed]), which is what ruling Q-i asked for.  The
   contract's honest silence is only about WHERE the loop died.

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
   [FsAbsMknodFire]'s) -- [fileG] is bound and [icacheG]/[icfg] resolve only
   through its fields. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import RiscvExtras.      (* [moi32_small]                           *)
Require Import DinodeEnc.
Require Import FsTree.           (* [file_bytes]                            *)
Require Import FsBlocks.         (* [blk_splice] and its three lookups      *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import BioDefs.          (* [BSIZE]                                 *)
Require Import InodeDefs.        (* [file_byte]                             *)
Require Import InodeInv.         (* [MAXFILE], [blk_holes_zero]             *)
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes the section list names, IMPORTED rather than
   inherited ([FsAbsMknodFire]'s header records why). *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import SpecWritei.       (* [wi_dinode]                             *)
Require Import SpecCopyin.       (* [ubytes_at]: the content seam           *)
Require Import FsAbsDelta.   (* [abs_view_insert]                       *)
Require Import SpecSysWriteAU.   (* [FW_MAX], [wri_pre], [wchunks]          *)
Require Import FsAbsOpenFire.    (* [opf_era_file_row], [opf_era_type]      *)
Require FsImg.                   (* [T_FILE_z] -- Require, NOT Import       *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import FsAbsDefs.            (* LAST (FsAbs's own rule)                 *)
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

(* ---- THE LANDED RUN: THE WRITTEN CHUNK PLUS THE VISIBLE DISTURBANCE ---

   writei's post admits a DISTURBED REGION of at most [BSIZE] bytes
   immediately after the written range ([SpecWritei]'s [dist]/[dstb]): the
   prefix of a chunk whose [either_copyin] faulted part-way, committed to
   the log rather than stranded in the cache.  Those bytes are NOT counted
   in [tot], but they ARE in the file -- as far as the new size reaches.
   The new size is [max (off + tot) sz], so exactly
   [min dist (sz - (off + tot))] of them are visible and the rest is past
   EOF.  [wrf_landed] is what the row really became at [off], and it is
   what makes the short chunk's state move STATABLE (round E2, ruling
   Q-i): the delta is non-deterministic in these bytes, never silent about
   them. *)
Definition wrf_landed (wrote dstb : nat -> bv 8) (sz off tot dist : nat)
    : list (bv 8) :=
  (wrf_run wrote tot ++ wrf_run dstb (Nat.min dist (sz - (off + tot))))%list.

Lemma wrf_run_0 (f : nat -> bv 8) : wrf_run f 0 = [].
Proof. reflexivity. Qed.

Lemma wrf_landed_length (wrote dstb : nat -> bv 8) (sz off tot dist : nat) :
  length (wrf_landed wrote dstb sz off tot dist)
  = (tot + Nat.min dist (sz - (off + tot)))%nat.
Proof. rewrite /wrf_landed length_app !wrf_run_length //. Qed.

(* the clean chunk's reading: no disturbance, so the landed run IS the
   written run -- which is why [wrf_write_row] below is this file's
   [_dist] form at [dist = 0] *)
Lemma wrf_landed_0 (wrote dstb : nat -> bv 8) (sz off tot : nat) :
  wrf_landed wrote dstb sz off tot 0 = wrf_run wrote tot.
Proof.
  rewrite /wrf_landed.
  assert (Hm : Nat.min 0 (sz - (off + tot))%nat = 0%nat) by lia.
  rewrite Hm wrf_run_0 app_nil_r //.
Qed.

(* ---- ITEM 2's PURE HEART: THE RANGE CLAUSE IS THE SPLICE ------------- *)

(* The hypothesis is BOUNDED ([k] below the new size) on purpose: at the era
   node the pointwise reading only transports below [MAXFILE * BSIZE], which
   the file cap makes exactly the range this lemma consults. *)
(* THE GENERAL FORM: writei's THREE-WAY range clause -- written run,
   disturbed tail, unchanged -- IS the splice of the LANDED RUN.  The
   hypothesis is BOUNDED ([k] below the new size) on purpose: at the era
   node the pointwise reading only transports below [MAXFILE * BSIZE],
   which the file cap makes exactly the range this lemma consults. *)
Lemma wrf_file_bytes_splice_dist (data data' : nat -> list (bv 8))
    (sz off tot dist : nat) (wrote dstb : nat -> bv 8) :
  (off <= sz)%nat ->
  (forall k : nat, (k < Nat.max (off + tot) sz)%nat ->
     file_byte data' k
     = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
       then wrote (k - off)%nat
       else if decide ((off + tot <= k)%nat /\ (k < off + tot + dist)%nat)
            then dstb (k - (off + tot))%nat
            else file_byte data k) ->
  file_bytes data' (Nat.max (off + tot) sz)
  = blk_splice off (wrf_landed wrote dstb sz off tot dist)
      (file_bytes data sz).
Proof.
  intros Hoff Hbytes.
  assert (Hsub : length (wrf_landed wrote dstb sz off tot dist)
                 = (tot + Nat.min dist (sz - (off + tot)))%nat)
    by apply wrf_landed_length.
  assert (Hbs : length (file_bytes data sz) = sz) by apply wrf_fb_length.
  assert (Hlen : length (blk_splice off (wrf_landed wrote dstb sz off tot dist)
                           (file_bytes data sz))
                 = Nat.max (off + tot) sz).
  { rewrite (blk_splice_length_grow off (wrf_landed wrote dstb sz off tot dist)
               (file_bytes data sz) ltac:(rewrite Hbs; exact Hoff)).
    rewrite Hsub Hbs. lia. }
  apply list_eq. intros j.
  destruct (decide (j < Nat.max (off + tot) sz)%nat) as [Hj | Hj];
    [| rewrite lookup_ge_None_2; [| rewrite wrf_fb_length; lia];
       symmetry; apply lookup_ge_None_2; rewrite Hlen; lia].
  rewrite (wrf_fb_lookup data' _ j Hj) (Hbytes j Hj).
  destruct (decide (j < off)%nat) as [Hlt | Hge].
  - rewrite (blk_splice_lookup_lt off (wrf_landed wrote dstb sz off tot dist)
               (file_bytes data sz) j ltac:(rewrite Hbs; exact Hoff) Hlt).
    rewrite (wrf_fb_lookup data sz j ltac:(lia)).
    destruct (decide ((off <= j)%nat /\ (j < off + tot)%nat)) as [[H1 _] | _];
      [lia |].
    destruct (decide ((off + tot <= j)%nat /\ (j < off + tot + dist)%nat))
      as [[H2 _] | _]; [lia | reflexivity].
  - destruct (decide (j < off + tot)%nat) as [Hmid | Hgi].
    + rewrite (blk_splice_lookup_mid off (wrf_landed wrote dstb sz off tot dist)
                 (file_bytes data sz) j ltac:(rewrite Hbs; exact Hoff)
                 ltac:(lia) ltac:(rewrite Hsub; lia)).
      rewrite /wrf_landed lookup_app_l;
        [| rewrite (wrf_run_length wrote tot); lia].
      rewrite (wrf_run_lookup wrote tot (j - off)%nat ltac:(lia)).
      destruct (decide ((off <= j)%nat /\ (j < off + tot)%nat)) as [_ | Hno];
        [reflexivity | exfalso; apply Hno; lia].
    + destruct (decide (j < off + tot
                          + Nat.min dist (sz - (off + tot)))%nat)
        as [Hmid2 | Hgi2].
      * rewrite (blk_splice_lookup_mid off
                   (wrf_landed wrote dstb sz off tot dist)
                   (file_bytes data sz) j ltac:(rewrite Hbs; exact Hoff)
                   ltac:(lia) ltac:(rewrite Hsub; lia)).
        rewrite /wrf_landed lookup_app_r;
          [| rewrite (wrf_run_length wrote tot); lia].
        rewrite (wrf_run_length wrote tot).
        replace (j - off - tot)%nat with (j - (off + tot))%nat by lia.
        rewrite (wrf_run_lookup dstb (Nat.min dist (sz - (off + tot)))
                   (j - (off + tot))%nat ltac:(lia)).
        destruct (decide ((off <= j)%nat /\ (j < off + tot)%nat))
          as [[_ H2] | _]; [lia |].
        destruct (decide ((off + tot <= j)%nat /\ (j < off + tot + dist)%nat))
          as [_ | Hno]; [reflexivity | exfalso; apply Hno; lia].
      * rewrite (blk_splice_lookup_ge off
                   (wrf_landed wrote dstb sz off tot dist)
                   (file_bytes data sz) j ltac:(rewrite Hbs; exact Hoff)
                   ltac:(rewrite Hsub; lia)).
        rewrite (wrf_fb_lookup data sz j ltac:(lia)).
        destruct (decide ((off <= j)%nat /\ (j < off + tot)%nat))
          as [[_ H2] | _]; [lia |].
        destruct (decide ((off + tot <= j)%nat /\ (j < off + tot + dist)%nat))
          as [[_ H3] | _]; [lia | reflexivity].
Qed.

(* ---- ITEM 2's PURE HEART: THE RANGE CLAUSE IS THE SPLICE ------------- *)

(* the CLEAN chunk's reading, the general form at [dist = 0]. *)
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
  rewrite -(wrf_landed_0 wrote wrote sz off tot).
  apply (wrf_file_bytes_splice_dist data data' sz off tot 0 wrote wrote Hoff).
  intros k Hk. rewrite (Hbytes k Hk).
  destruct (decide ((off <= k)%nat /\ (k < off + tot)%nat)) as [_ | _];
    [reflexivity |].
  destruct (decide ((off + tot <= k)%nat /\ (k < off + tot + 0)%nat))
    as [[H1 H2] | _]; [lia | reflexivity].
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
(* THE GENERAL FORM (round E2, lane E2-W): the row at ANY writei outcome,
   disturbed tail included.  [wrf_write_row] below is this at [dist = 0] --
   the clean chunk the loop continues on. *)
Lemma wrf_write_row_dist `{XI : TsoCtx.CurCtx} (dn dn' : dinode)
    (bm bm' : blkmap) (data data' : nat -> list (bv 8))
    (off tot dist : nat) (wrote dstb : nat -> bv 8) :
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
       else if decide ((off + tot <= k)%nat /\ (k < off + tot + dist)%nat)
            then dstb (k - (off + tot))%nat
            else file_byte data k) ->
  abs_row (era_node dn' bm' data')
  = MkAnode (AFile (blk_splice off
                      (wrf_landed wrote dstb
                         (Z.to_nat (bv_unsigned (di_size dn))) off tot dist)
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
               = blk_splice off
                   (wrf_landed wrote dstb
                      (Z.to_nat (bv_unsigned (di_size dn))) off tot dist)
                   (fn_file_bytes (era_node dn bm data))).
  { rewrite (wrf_era_bytes dn' bm' data') (wrf_era_bytes dn bm data) Hsz'.
    apply (wrf_file_bytes_splice_dist (fn_data (era_node dn bm data))
             (fn_data (era_node dn' bm' data'))
             (Z.to_nat (bv_unsigned (di_size dn))) off tot dist wrote dstb
             Hoff).
    intros k Hk.
    assert (Hkb : (k < MAXFILE * BSIZE)%nat) by lia.
    rewrite (wrf_era_file_byte dn' bm' data' k Hh' Hkb)
            (wrf_era_file_byte dn bm data k Hh Hkb).
    exact (Hrange k Hkb). }
  rewrite (opf_era_file_row dn' bm' data' Hty2) Hb Hnl //.
Qed.

(* The premises are exactly what filewrite's inode arm holds when writei
   returns on its success arm with a CLEAN chunk: the record's type is
   [T_FILE], the two payloads normalise their holes, the size grew to the
   [max], the range clause is writei's own at [dist = 0] (see the header),
   and the start is inside the old bytes. *)
Lemma wrf_write_row `{XI : TsoCtx.CurCtx} (dn dn' : dinode) (bm bm' : blkmap)
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
  abs_row (era_node dn' bm' data')
  = MkAnode (AFile (blk_splice off (wrf_run wrote tot)
                      (fn_file_bytes (era_node dn bm data))))
            (fn_nlink (era_node dn bm data)).
Proof.
  intros Hty Hty' Hnl' Hh Hh' Hsz' Hoff Hcap Hcap0 Hrange.
  rewrite -(wrf_landed_0 wrote wrote
              (Z.to_nat (bv_unsigned (di_size dn))) off tot).
  apply (wrf_write_row_dist dn dn' bm bm' data data' off tot 0 wrote wrote
           Hty Hty' Hnl' Hh Hh' Hsz' Hoff Hcap Hcap0).
  intros k Hk. rewrite (Hrange k Hk).
  destruct (decide ((off <= k)%nat /\ (k < off + tot)%nat)) as [_ | _];
    [reflexivity |].
  destruct (decide ((off + tot <= k)%nat /\ (k < off + tot + 0)%nat))
    as [[H1 H2] | _]; [lia | reflexivity].
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

  (* THE FULL-CHUNK COMMIT: the two-phase fire at the RAW MAP, with the very
     same [ghost_map_auth] handed back, so the invariant's row obligation
     survives; phase 2 is quantified over the POST map and constrained by its
     READING alone -- AND WITH THE OFFSET FOLDED IN (OffGv.v).  The kernel
     lends its half of the descriptor's offset shadow at the offset the chunk
     was written at (the box ties the half to [f->off]) and takes it back at
     phase 2 UNMOVED: the bytes and the offset are observed in the one fupd,
     inside [ip->lock], at the row's retag, and [wrf_awrite_fire] does the
     ADVANCE afterwards.  THE PIECE-SHAPE RULE
     (design/fs-syscall-specs.md section 4): a piece may not ask the client to
     return a kernel-owned ghost moved, because after the ARM the client is
     an arbitrary user process holding no [off_user_inv] at an arbitrary key.
     [REST] is what the client hands back at phase 2 -- the rest of the
     chain, below.

     THE PER-CHUNK BUFFER TIE IS PHASE 1'S.  Every chunk
     that reaches node [k] was FULL (a short one ends filewrite's loop), so
     chunk [k]'s source offset is [FW_MAX * k] and its bytes are the caller's
     own run there ([SpecCopyin.ubytes_at] at the image [M] the caller lent
     and the base [ua] it passed).  That is what lets the cursor [Q (S k)]
     built inside phase 2 say WHICH bytes landed; before the cursor the tie
     was stated once, on the concatenation, in the post.

     THE RECEIPT IS GONE.  Phase 2 used to return [Φ k (abs_view I) off bs]
     beside [REST]; the chain's PREFIX CURSOR subsumes it -- the caller
     builds node [k+1] inside this very phase 2, where the post-map witness
     is in hand, so whatever it wanted to record it records in [Q (S k)]. *)
  Definition awrite_full_at Γ (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (k : nat)
      (REST : iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       ⌜ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) bs⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I -∗ off_gv γo (1/2) (Z.of_nat off) ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         (* THE CALLER'S STEP (app-instances.md section 7): its claim about
            the pre-view survives the delta, at the RAW insert the mover
            performs ([AppInv.app_step]; the delta is its reading) *)
         app_step i I (delta_write i off bs (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗
            off_gv γo (1/2) (Z.of_nat off) ∗
            REST))%I.

  (* THE PARTIAL-CHUNK COMMIT (round E2, lane E2-W; ruling Q-i).  It used
     to move the OFFSET ONLY -- "those bytes are writei's DISTURBED tail,
     not the splice, so there is no delta this contract can receipt".  That
     was the hole: the machine DID move the row.  writei commits the
     partially copied block rather than stranding it, so after a short
     chunk the file holds the counted bytes AND up to one block of
     unspecified tail, as far as the new size reaches
     ([SpecWritei]'s [dist <= BSIZE]; [wrf_landed] is the run).

     So this is [awrite_full_at]'s two phases at a run the KERNEL picks --
     NON-DETERMINISTIC in the bytes, which is exactly what makes the clause
     statable -- with two things the full arm does not have: the KERNEL
     advances the offset by [r], the count writei RETURNED, which may be
     strictly less than the run that landed ([wrf_apart_fire]); and ONLY
     THE COUNTED PREFIX is
     the caller's ([take r bs]), the rest of [bs] being writei's disturbed
     tail, which no [ubytes_at] can claim. *)
  Definition awrite_part_at Γ (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (k : nat)
      (REST : iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off r : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       ⌜(r <= length bs)%nat⌝ -∗
       ⌜(length bs <= r + BSIZE)%nat⌝ -∗
       ⌜ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) (take r bs)⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I -∗ off_gv γo (1/2) (Z.of_nat off) ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         app_step i I (delta_write i off bs (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗
            off_gv γo (1/2) (Z.of_nat off) ∗
            REST))%I.

  (* THE CHAIN, AT A PREFIX CURSOR.  A bundle of
     independent commits cannot work: every commit moves the ONE half the
     client owns, so the client cannot pre-build [wchunks n] of them side by
     side.  The chain hands out one node at a time; each node offers the
     CURSOR [Q k] -- "what the caller knows after a prefix of [k] chunks" --
     beside BOTH arms, and the kernel picks ([∧], the kernel's choice).
     Either arm's phase 2 returns the next node, so the caller BUILDS node
     [k+1] where the post-map witness is in hand and [Q (S k)] can genuinely
     record that chunk [k] landed.

     THE KERNEL eliminates to an arm when it fires chunk [k] and returns the
     node when it stops; THE CALLER eliminates to [Q k] at the stop position
     ([awrite_chain_cursor]).  That is why the posts carry no per-chunk
     receipt bundle: their three returns collapse to "here is the node at
     the stop position".

     The partial arm ends filewrite's loop ([r != n1] breaks), so it is taken
     at most once, last -- the posts' [x <= 1] slack. *)
  Fixpoint awrite_chain Γ (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (k cnt : nat) : iProp Σ :=
    match cnt with
    | O => Q k
    | S cnt' =>
        (Q k
         ∧ (awrite_full_at Γ E i γo M ua k
              (awrite_chain Γ E i γo M ua Q (S k) cnt')
            ∧ awrite_part_at Γ E i γo M ua k
                (awrite_chain Γ E i γo M ua Q (S k) cnt')))%I
    end.

  Lemma awrite_chain_0 Γ E i γo M ua Q k :
    awrite_chain Γ E i γo M ua Q k 0 ⊣⊢ Q k.
  Proof. reflexivity. Qed.

  Lemma awrite_chain_S Γ E i γo M ua Q k cnt :
    awrite_chain Γ E i γo M ua Q k (S cnt) ⊣⊢
      Q k
      ∧ (awrite_full_at Γ E i γo M ua k
           (awrite_chain Γ E i γo M ua Q (S k) cnt)
         ∧ awrite_part_at Γ E i γo M ua k
             (awrite_chain Γ E i γo M ua Q (S k) cnt)).
  Proof. reflexivity. Qed.

  (* THE CALLER'S ELIMINATION, at any stop position and any remaining
     count: the node IS the cursor.  This is the whole of what the two
     exits of filewrite's loop read off. *)
  Lemma awrite_chain_cursor Γ E i γo M ua Q k cnt :
    awrite_chain Γ E i γo M ua Q k cnt -∗ Q k.
  Proof.
    destruct cnt as [| cnt'].
    - rewrite awrite_chain_0. iIntros "$".
    - rewrite awrite_chain_S. iIntros "[$ _]".
  Qed.

  (* satisfiability, WITHOUT A SHADOW OF THE CLIENT'S: every node returns
     the borrow unmoved, so the TRIVIAL-CURSOR chain of any length costs
     its client nothing but the application's step -- the seal cannot be
     vacuously blocked on the caller's side, and the chain is payable at
     every key.  [FsAbsInvFire.fsabs_awrite_chain] is the same lemma at the
     live Γ's dischargers. *)
  (* ...at the live Γ, since the full arm owes the caller's step, paid here
     out of the SUPPLY ([AppInv.app_step_acc]) *)
  Lemma awrite_chain_unit (γfs : fs_names) E i γo M ua k cnt :
    app_sup -∗
    awrite_chain (fs_gamma_L γfs) E i γo M ua (fun _ => True%I) k cnt.
  Proof.
    revert k. induction cnt as [| cnt IH]; intros k.
    { rewrite awrite_chain_0. by iIntros "_". }
    rewrite awrite_chain_S. iIntros "#Hsup". iSplit; [done |]. iSplit.
    - rewrite /awrite_full_at. iIntros (I off bs bs0 nl) "%Hpre %Hby Ha Hk".
      iDestruct (app_step_acc i I _ with "Hsup") as "Hstep".
      iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
      iFrame "Ha' Hk". iApply (IH with "Hsup").
    - rewrite /awrite_part_at.
      iIntros (I off r bs bs0 nl) "%Hpre %Hr %Hgap %Hby Ha Hk".
      iDestruct (app_step_acc i I _ with "Hsup") as "Hstep".
      iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
      iFrame "Ha' Hk". iApply (IH with "Hsup").
  Qed.

  (* =================================================================== *)
  (*  3.  ITEM 1: THE CHUNK FIRE, FUSED WITH THE ROW RETAG                *)
  (* =================================================================== *)

  (* Replaces the [InodeRegion.ireg_top_retag_*] filewrite's inode arm calls
     after writei returns: same [inode_local] premise, same payout (the
     moved fragment), plus the caller's two phases inside the one [ftopN]
     critical section, AND the offset's half in at the chunk's offset and
     out ADVANCED BY THIS LEMMA -- the client returns it unmoved (the
     piece-shape rule) and the advance comes off the descriptor row's own
     existential invariant ([OffGv.off_user_inv], persistent, carried by
     [FdSlots.foff_row] and threaded down from sys_write's descriptor
     bundle).  The receipt's pre-state row is the
     OBSERVED one -- the fragment read is the one the fire retags, so
     nothing can move between the observation and the update. *)
  Lemma wrf_awrite_fire (γfs : fs_names) (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (k : nat) (REST : iProp Σ)
      (off : nat) (bs bs0 : list (bv 8)) (nl : nat) (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local i n' ->
    (0 < length bs)%nat ->
    (off <= length bs0)%nat ->
    (off + length bs <= MAXFILE * BSIZE)%nat ->
    fn_type n <> 0 ->
    abs_row n = MkAnode (AFile bs0) nl ->
    fn_type n' <> 0 ->
    abs_row n' = MkAnode (AFile (blk_splice off bs bs0)) nl ->
    ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) bs ->
    ftop_inv γfs -∗ app_inv γfs -∗ off_user_inv γo -∗
    awrite_full_at (fs_gamma_L γfs) appE i γo M ua k REST -∗
    top_frag (fs_gamma_L γfs) i n -∗
    off_gv γo (1/2) (Z.of_nat off) ={E}=∗
      top_frag (fs_gamma_L γfs) i n'
      ∗ off_gv γo (1/2) (Z.of_nat (off + length bs))
      ∗ REST.
  Proof.
    intros HE Hloc Hpos Hoff Hcap Hnz Habs Hnz' Habs' Hby.
    iIntros "#Hi #Hai #Hoinv Hcm Hf Hg".
    assert (Hfoff : ↑foffN ⊆ E).
    { etrans; [| exact HE]. rewrite /foffN /appN. solve_ndisj. }
    (* the re-spelling [mkf_acre_fire] does, and for the same reason: the
       unifier cannot solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    (* the row is stated on the COUNT (E2-V2): the fd's inode may have
       been unlinked while open, and then the view has no row for it *)
    assert (Hrow : arow_at (abs_view I) i (MkAnode (AFile bs0) nl)).
    { rewrite -Habs. exact (abs_view_arow I i n Hlk Hnz). }
    assert (Hpre : wri_pre (abs_view I) i off bs bs0 nl).
    { rewrite /wri_pre. split_and!; [exact Hrow | exact Hpos | exact Hoff |
                                     exact Hcap]. }
    (* the delta collapses to the ONE-ROW counted insert: at a nonzero
       count the written record's own row, at zero nothing moves *)
    assert (Hdelta : abs_view (<[i := n']> I)
                     = delta_write i off bs (abs_view I)).
    { rewrite (abs_view_insert_row I i n' _ Hnz' Habs') /=.
      case_decide as Hz.
      - pose proof (arow_at_gone _ _ _ Hrow Hz) as Hnone.
        rewrite (delta_write_absent _ _ _ _ Hnone). exact (delete_notin _ _ Hnone).
      - by rewrite (delta_write_file (abs_view I) i off bs bs0 nl
                      (arow_at_live _ _ _ Hrow Hz)). }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I off bs bs0 nl with "[//] [//] Hta Hg") as "(Hta & Hstep & Hph2)".
    (* THE MOVE, at the whole authority: the application's half comes out
       of [appN] beside its claim, which the caller's step re-establishes
       under the later ([AppInv.app_top_update]) *)
    iMod (app_top_update appE γfs I i n n' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hf") as "[Hta Hf]".
    { iIntros (_) "_ Hp". iApply (app_step_at i I _ n' Hdelta with "Hstep Hp"). }
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "(Hta & Hg & Hrest)".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = i)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    (* THE ADVANCE IS THE KERNEL'S: the process's half comes out of the
       row's existential invariant and both halves move together. *)
    iMod (off_user_inv_move E γo (Z.of_nat off) (Z.of_nat (off + length bs))
            Hfoff with "Hoinv Hg") as "Hg".
    iModIntro. iFrame "Hf Hg Hrest".
  Qed.

  (* THE PARTIAL ARM'S FIRE (round E2, lane E2-W): [wrf_awrite_fire] at the
     partial commit.  Same critical section, same [inode_local] premise,
     same payout -- the ONE difference is the offset, which comes out
     advanced by the COUNT writei returned rather than by the run that
     landed.  ([wrf_partial_move], the offset-only move this replaces, is
     gone with the hole it papered over.) *)
  Lemma wrf_apart_fire (γfs : fs_names) (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (k : nat)
      (REST : iProp Σ) (off r : nat) (bs bs0 : list (bv 8)) (nl : nat)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local i n' ->
    (0 < length bs)%nat ->
    (off <= length bs0)%nat ->
    (off + length bs <= MAXFILE * BSIZE)%nat ->
    (r <= length bs)%nat ->
    (length bs <= r + BSIZE)%nat ->
    fn_type n <> 0 ->
    abs_row n = MkAnode (AFile bs0) nl ->
    fn_type n' <> 0 ->
    abs_row n' = MkAnode (AFile (blk_splice off bs bs0)) nl ->
    ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) (take r bs) ->
    ftop_inv γfs -∗ app_inv γfs -∗ off_user_inv γo -∗
    awrite_part_at (fs_gamma_L γfs) appE i γo M ua k REST -∗
    top_frag (fs_gamma_L γfs) i n -∗
    off_gv γo (1/2) (Z.of_nat off) ={E}=∗
      top_frag (fs_gamma_L γfs) i n'
      ∗ off_gv γo (1/2) (Z.of_nat (off + r))
      ∗ REST.
  Proof.
    intros HE Hloc Hpos Hoff Hcap Hr Hgap Hnz Habs Hnz' Habs' Hby.
    iIntros "#Hi #Hai #Hoinv Hcm Hf Hg".
    assert (Hfoff : ↑foffN ⊆ E).
    { etrans; [| exact HE]. rewrite /foffN /appN. solve_ndisj. }
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : arow_at (abs_view I) i (MkAnode (AFile bs0) nl)).
    { rewrite -Habs. exact (abs_view_arow I i n Hlk Hnz). }
    assert (Hpre : wri_pre (abs_view I) i off bs bs0 nl).
    { rewrite /wri_pre. split_and!; [exact Hrow | exact Hpos | exact Hoff |
                                     exact Hcap]. }
    assert (Hdelta : abs_view (<[i := n']> I)
                     = delta_write i off bs (abs_view I)).
    { rewrite (abs_view_insert_row I i n' _ Hnz' Habs') /=.
      case_decide as Hz.
      - pose proof (arow_at_gone _ _ _ Hrow Hz) as Hnone.
        rewrite (delta_write_absent _ _ _ _ Hnone). exact (delete_notin _ _ Hnone).
      - by rewrite (delta_write_file (abs_view I) i off bs bs0 nl
                      (arow_at_live _ _ _ Hrow Hz)). }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I off r bs bs0 nl with "[//] [//] [//] [//] Hta Hg")
      as "(Hta & Hstep & Hph2)".
    iMod (app_top_update appE γfs I i n n' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hf") as "[Hta Hf]".
    { iIntros (_) "_ Hp". iApply (app_step_at i I _ n' Hdelta with "Hstep Hp"). }
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "(Hta & Hg & Hrest)".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = i)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    (* THE ADVANCE IS THE KERNEL'S, at the COUNT writei returned. *)
    iMod (off_user_inv_move E γo (Z.of_nat off) (Z.of_nat (off + r))
            Hfoff with "Hoinv Hg") as "Hg".
    iModIntro. iFrame "Hf Hg Hrest".
  Qed.

End WriteFire.

(* the chain is SEALED: its nodes are [∧]-pairs and an [iFrame] near a
   consumer must not look inside *)
Global Typeclasses Opaque awrite_chain.