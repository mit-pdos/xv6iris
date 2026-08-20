(* ====================================================================== *)
(* FsBoot.v -- THE PER-ERA FS BOOT BUNDLE: the one ghost step that turns   *)
(* what every boot already mints -- the era's exclusive disk-image byte    *)
(* fragments over [0, ndisk) -- into exactly the material the FS block     *)
(* layer's constructors want ([BioInv.bio_init]'s pool bundles, and        *)
(* [SpecInitlog]'s FsBlocks material).                                     *)
(*                                                                        *)
(* This closes the gap recorded as future work since stage 1 of the        *)
(* fs-log project ("where do bio_init's pool inputs come from?" --         *)
(* claude-notes/design/fs-log.md).  The boot mint is flat and byte-        *)
(* granular ([RiscvAdequacy.wp_power_loop]'s PowerOn arm, re-exported by   *)
(* [BootShared.boot_shared_alloc] as                                        *)
(*   [disk_bytes γv 0 (disk_read dk 0 ndisk)]);                             *)
(* everything above the driver talks in 1024-byte BLOCKS.  The whole file  *)
(* is that change of granularity plus the [fs_alloc] handshake.            *)
(*                                                                        *)
(* THREE THINGS A FUTURE READER WOULD OTHERWISE RE-DERIVE.                 *)
(*                                                                        *)
(* (1) THE MINT'S LENGTH NEED NOT DIVIDE 1024, AND NOTHING HAS TO KNOW     *)
(*     THE FS'S DISK SIZE.  [fs_cov_in cov ndisk] says only: every covered *)
(*     block is positive and its last byte is inside the mint.  The carve  *)
(*     picks [nb := ndisk / 1024] internally ([fs_cov_blocks], the one     *)
(*     place any division happens), peels [nb] whole blocks off the front  *)
(*     of the mint and DROPS the tail -- the logic is affine, so the       *)
(*     leftover bytes simply vanish.  No premise ties [ndisk] to a block   *)
(*     count, so [SystemAdequacy.XV6_DISK_BYTES] stays where it is.        *)
(*                                                                        *)
(* (2) [0 ∉ cov] IS NOT A SEPARATE PREMISE.  [bio_init] needs it (binit    *)
(*     leaves all thirty buffers claiming blockno 0), and it FOLLOWS from  *)
(*     [fs_cov_in]'s [0 < b] clause -- [fs_cov_in_0].  Adding it as a      *)
(*     premise would be a redundant obligation at every boot client.       *)
(*                                                                        *)
(* (3) THE LOG REGION'S CLIENT HALVES COME OUT OF THE *SET* BIG-OP, WHICH  *)
(*     NEEDS THE SLOTS' PAIRWISE DISTINCTNESS.  [log_region_set] is a      *)
(*     [list_to_set] of [log_slot_bno logstart <$> seq 0 LOGBLOCKS] plus   *)
(*     the header, so getting the thirty slot halves back as a [∗ list]    *)
(*     over [seq 0 LOGBLOCKS] goes through [big_sepS_list_to_set], whose   *)
(*     [NoDup] side condition is exactly [log_slot_bno]'s injectivity in   *)
(*     [i] ([log_slot_bno_inj] below).  The header comes out AT A NAMED    *)
(*     CONTENT ([fs_blocks dk (log_hdr_bno logstart)]) rather than under   *)
(*     an existential: that is what lets a boot client discharge           *)
(*     [SpecInitlog]'s clean-image premise [hdr_n bs_hdr = 0] from a       *)
(*     hypothesis about the mkfs image [dk].  Under an existential the     *)
(*     premise would be unstatable.                                        *)
(*                                                                        *)
(* All the arithmetic lives in [mword]-free lemmas over plain [Z]/[nat]    *)
(* ([fs_cov_blocks], [disk_read_app], [seqZ_cons_nat]) -- durable-notes'   *)
(* rule, and here it is what keeps [lia] usable at all.                    *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import SleepLock.
Require Import BufOwn.
Require Import VirtioModel.
Require Import DiskImg.
Require Import DiskPtsto.
Require Import BcacheInv.
Require Import BioInv.
Require Import FsBlocks.
Require Import LogInv.
Require Import FsCrash.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. THE PURE VOCABULARY.                                                *)
(* ====================================================================== *)

(* "the covered block range lies inside the mint": every covered block is a
   real client block (0 is excluded -- binit's zeroed blockno cells claim
   it) and its last byte is one of the [ndisk] bytes the boot mint owns. *)
Definition fs_cov_in (cov : gset Z) (ndisk : nat) : Prop :=
  forall b : Z, b ∈ cov -> 0 < b /\ 1024 * (b + 1) <= Z.of_nat ndisk.

(* [bio_init]'s "0 is not a client block" premise is already in there *)
Lemma fs_cov_in_0 (cov : gset Z) (ndisk : nat) :
  fs_cov_in cov ndisk -> (0 : Z) ∉ cov.
Proof. intros Hc Hin. destruct (Hc 0 Hin) as [Hlt _]. lia. Qed.

(* the two halves of [log_geom_ok], for a caller that has the bundle and
   wants one of them.  [fs_boot_bundle] itself consumes only the second
   ([log_region_set logstart ⊆ cov]); it takes the whole [log_geom_ok]
   anyway because that is the premise [SpecInitlog] states, so a boot
   client proves it once and feeds it to both. *)
Lemma log_geom_cov_ok (cov : gset Z) (logstart : Z) :
  log_geom_ok cov logstart -> cov_ok cov.
Proof. by intros [? _]. Qed.

Lemma log_geom_region_sub (cov : gset Z) (logstart : Z) :
  log_geom_ok cov logstart -> log_region_set logstart ⊆ cov.
Proof. by intros [_ ?]. Qed.

(* THE ONE DIVISION IN THE FILE.  A block count whose blocks all fit in the
   mint and which covers every covered block.  Kept [mword]-free and over
   plain [Z]/[nat] so [lia] works (durable-notes). *)
Lemma fs_cov_blocks (cov : gset Z) (ndisk : nat) :
  fs_cov_in cov ndisk ->
  exists nb : nat,
    (1024 * nb <= ndisk)%nat /\
    (forall b : Z, b ∈ cov -> 0 <= b < Z.of_nat nb).
Proof.
  intros Hcov.
  pose (nb := (ndisk / 1024)%nat).
  pose (r := (ndisk mod 1024)%nat).
  assert (Hdm : ndisk = (1024 * nb + r)%nat)
    by (unfold nb, r; apply Nat.div_mod_eq).
  assert (Hr : (r < 1024)%nat)
    by (unfold r; apply Nat.mod_upper_bound; lia).
  clearbody nb r.
  exists nb. split; [lia|].
  intros b Hb. destruct (Hcov b Hb) as [Hpos Hub].
  assert (HZ : Z.of_nat ndisk = 1024 * Z.of_nat nb + Z.of_nat r) by lia.
  lia.
Qed.

(* the nat-indexed cons for stdpp's [seqZ], so the carve's induction never
   has to see [Z.succ]/[Z.pred] *)
Lemma seqZ_cons_nat (m : Z) (n : nat) :
  seqZ m (Z.of_nat (S n)) = m :: seqZ (m + 1) (Z.of_nat n).
Proof.
  rewrite seqZ_cons; [| lia]. f_equal. f_equal; lia.
Qed.

(* [log_slot_bno] is injective in the slot index -- the [NoDup] the log
   region's set-to-list conversion needs *)
Lemma log_slot_bno_inj (logstart : Z) (i j : nat) :
  log_slot_bno logstart i = log_slot_bno logstart j -> i = j.
Proof. rewrite /log_slot_bno. lia. Qed.

(* [base.NoDup] and not [NoDup]: this file imports [Stdlib.Lists.List],
   whose [NoDup] takes the bare name -- and [big_sepS_list_to_set] (like
   every stdpp lemma here) wants stdpp's. *)
Lemma log_slot_list_nodup (logstart : Z) :
  base.NoDup ((fun i => log_slot_bno logstart i) <$> seq 0 LOGBLOCKS).
Proof.
  apply NoDup_fmap_2; [| apply NoDup_seq ].
  intros i j Hij. exact (log_slot_bno_inj logstart i j Hij).
Qed.

(* the header is not one of the slots *)
Lemma log_hdr_not_slot (logstart : Z) :
  log_hdr_bno logstart ∉
    ((fun i => log_slot_bno logstart i) <$> seq 0 LOGBLOCKS).
Proof.
  intros Hin. apply elem_of_list_fmap in Hin as (i & Hi & _).
  rewrite /log_hdr_bno /log_slot_bno in Hi. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The initial content map and the all-false dirty map.                     *)
(*                                                                          *)
(* [map_imap] over [gset_to_gmap] rather than a [list_to_map] of            *)
(* [elements cov]: the lookup law then needs no [NoDup] bookkeeping, and     *)
(* the domain law is one [elem_of_dom] unfold.                              *)
(* ---------------------------------------------------------------------- *)

Definition fs_L0 (dk : Z -> bv 8) (cov : gset Z) : gmap Z (list (bv 8)) :=
  map_imap (fun b (_ : unit) => Some (fs_blocks dk b)) (gset_to_gmap () cov).

Definition fs_D0 (dk : Z -> bv 8) (cov : gset Z) : gmap Z bool :=
  (fun _ => false) <$> fs_L0 dk cov.

Lemma fs_L0_lookup (dk : Z -> bv 8) (cov : gset Z) (b : Z) :
  b ∈ cov -> fs_L0 dk cov !! b = Some (fs_blocks dk b).
Proof.
  intros Hb. rewrite /fs_L0 map_lookup_imap lookup_gset_to_gmap.
  rewrite option_guard_True; [reflexivity | exact Hb].
Qed.

Lemma fs_L0_lookup_Some (dk : Z -> bv 8) (cov : gset Z) (b : Z)
    (bs : list (bv 8)) :
  fs_L0 dk cov !! b = Some bs -> b ∈ cov /\ bs = fs_blocks dk b.
Proof.
  rewrite /fs_L0 map_lookup_imap lookup_gset_to_gmap.
  destruct (decide (b ∈ cov)) as [Hin|Hout].
  (* [cbn] with no delta list here is a 7 s trap: it unfolds [fs_blocks]
     into a [disk_read] of 1024 bytes.  Name the two constants. *)
  - rewrite option_guard_True; [| exact Hin]. cbn [mbind option_bind].
    intros Heq. injection Heq as <-. done.
  - rewrite option_guard_False; [| exact Hout]. cbn [mbind option_bind].
    discriminate.
Qed.

Lemma fs_L0_dom (dk : Z -> bv 8) (cov : gset Z) :
  dom (fs_L0 dk cov) = cov.
Proof.
  apply set_eq. intros b. rewrite elem_of_dom. split.
  - intros [bs Hbs]. exact (proj1 (fs_L0_lookup_Some dk cov b bs Hbs)).
  - intros Hb. exists (fs_blocks dk b). exact (fs_L0_lookup dk cov b Hb).
Qed.

Lemma fs_D0_lookup (dk : Z -> bv 8) (cov : gset Z) (b : Z) :
  b ∈ cov -> fs_D0 dk cov !! b = Some false.
Proof.
  intros Hb. rewrite /fs_D0 lookup_fmap (fs_L0_lookup dk cov b Hb) //.
Qed.

(* ====================================================================== *)
(* 2. PURE RANGE ALGEBRA over [disk_read].                                *)
(* ====================================================================== *)

Lemma disk_read_app (dk : Z -> bv 8) (o : Z) (n m : nat) :
  disk_read dk o (n + m)
  = (disk_read dk o n ++ disk_read dk (o + Z.of_nat n) m)%list.
Proof.
  revert o. induction n as [|n IH]; intros o.
  - assert (Hz : o + Z.of_nat 0%nat = o) by lia. rewrite Hz. reflexivity.
  - assert (Hs : (S n + m = S (n + m))%nat) by lia. rewrite Hs.
    rewrite !disk_read_cons IH.
    assert (Hz : o + 1 + Z.of_nat n = o + Z.of_nat (S n)) by lia.
    rewrite Hz. reflexivity.
Qed.

(* ====================================================================== *)
(* 3. THE CARVE: the flat byte mint -> per-block disk cells.              *)
(* ====================================================================== *)

Section FsBoot.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* the append/split law the whole carve rests on *)
  Lemma disk_bytes_app (γ : disk_names) (o : Z) (bs1 bs2 : list (bv 8)) :
    disk_bytes γ o ((bs1 ++ bs2)%list)
      ⊣⊢ disk_bytes γ o bs1 ∗ disk_bytes γ (o + Z.of_nat (length bs1)) bs2.
  Proof.
    revert o. induction bs1 as [|b bs1 IH]; intros o.
    - assert (Hz : o + Z.of_nat (length (@nil (bv 8))) = o) by (cbn; lia).
      rewrite Hz. cbn [app].
      rewrite /disk_bytes /disk_img_bytes big_sepL_nil left_id //.
    - cbn [app length].
      rewrite !disk_bytes_cons IH.
      assert (Hz : o + 1 + Z.of_nat (length bs1)
                   = o + Z.of_nat (S (length bs1))) by lia.
      rewrite Hz assoc //.
  Qed.

  (* one block's worth of the mint IS a [disk_block] *)
  Lemma disk_bytes_block (γ : disk_names) (dk : Z -> bv 8) (b : Z) :
    disk_bytes γ (1024 * b) (fs_blocks dk b) -∗ disk_block γ b (fs_blocks dk b).
  Proof.
    iIntros "H". rewrite /disk_block. iSplitR; [| iExact "H"].
    iPureIntro. rewrite fs_blocks_length //.
  Qed.

  (* the run: [nb] consecutive blocks starting at [b0] *)
  Lemma disk_bytes_blocks (γ : disk_names) (dk : Z -> bv 8)
      (b0 : Z) (nb : nat) :
    disk_bytes γ (1024 * b0) (disk_read dk (1024 * b0) (1024 * nb)%nat) -∗
    [∗ list] b ∈ seqZ b0 (Z.of_nat nb), disk_block γ b (fs_blocks dk b).
  Proof.
    revert b0. induction nb as [|nb IH]; intros b0.
    - iIntros "_". rewrite seqZ_nil; [| lia]. done.
    - iIntros "H". rewrite seqZ_cons_nat.
      assert (Hs : (1024 * S nb = 1024 + 1024 * nb)%nat) by lia.
      rewrite Hs disk_read_app disk_bytes_app.
      iDestruct "H" as "[Hhd Htl]".
      iSplitL "Hhd".
      + iApply (disk_bytes_block γ dk b0).
        rewrite /fs_blocks /BSIZE.
        assert (Hz : b0 * Z.of_nat 1024%nat = 1024 * b0) by lia.
        rewrite Hz. iExact "Hhd".
      + iApply (IH (b0 + 1)).
        assert (Hz : 1024 * b0 + Z.of_nat (length (disk_read dk (1024 * b0) 1024))
                     = 1024 * (b0 + 1)).
        { rewrite /disk_read length_fmap length_seq. lia. }
        rewrite Hz. iExact "Htl".
  Qed.

  (* THE CARVE.  Note the mint's tail (the bytes past the last whole block)
     is simply dropped -- the logic is affine. *)
  Lemma fs_boot_carve (γ : disk_names) (dk : Z -> bv 8) (ndisk : nat)
      (cov : gset Z) :
    fs_cov_in cov ndisk ->
    disk_bytes γ 0 (disk_read dk 0 ndisk) -∗
    [∗ set] b ∈ cov, disk_block γ b (fs_blocks dk b).
  Proof.
    intros Hcov.
    destruct (fs_cov_blocks cov ndisk Hcov) as (nb & Hle & Hin).
    assert (Hsub : cov ⊆ list_to_set (seqZ 0 (Z.of_nat nb))).
    { intros b Hb. apply elem_of_list_to_set, elem_of_seqZ.
      destruct (Hin b Hb). lia. }
    assert (Hsplit : ndisk = (1024 * nb + (ndisk - 1024 * nb))%nat) by lia.
    rewrite {1}Hsplit disk_read_app disk_bytes_app.
    iIntros "[Hpre _]".
    iDestruct (disk_bytes_blocks γ dk 0 nb with "Hpre") as "Hl".
    iApply (big_sepS_subseteq _ _ _ Hsub).
    rewrite (big_sepS_list_to_set (fun b => disk_block γ b (fs_blocks dk b))
               (seqZ 0 (Z.of_nat nb)) (NoDup_seqZ 0 (Z.of_nat nb))).
    iExact "Hl".
    (* [big_sepS_subseteq]'s [Affine] side condition is SHELVED, not solved:
       leaving it makes Qed report only "incomplete proof". *)
    Unshelve. intros ?. apply _.
  Qed.

(* ====================================================================== *)
(* 4. THE FsBlocks HANDSHAKE.                                             *)
(* ====================================================================== *)

  (* [fs_alloc]'s per-block bundle arrives as a [∗ map] over [fs_L0]; every
     consumer wants a [∗ set] over [cov].  One conversion, once. *)
  Lemma fs_L0_big (Φ : Z -> list (bv 8) -> iProp Σ) (dk : Z -> bv 8)
      (cov : gset Z) :
    ([∗ map] b ↦ bs ∈ fs_L0 dk cov, Φ b bs)
      ⊢ [∗ set] b ∈ cov, Φ b (fs_blocks dk b).
  Proof.
    etrans.
    { apply (big_sepM_mono _ (fun b (_ : list (bv 8)) => Φ b (fs_blocks dk b))).
      intros b bs Hb.
      destruct (fs_L0_lookup_Some dk cov b bs Hb) as [_ ->]. done. }
    rewrite big_sepM_dom fs_L0_dom //.
  Qed.

  (* THE GHOST STEP.  The era's byte mint in, the logged-view ghosts out,
     with the pool bundles [bio_init] wants and the FsBlocks material
     [initlog] wants. *)
  Lemma fs_boot_ghosts (γv : disk_names) (dk : Z -> bv 8) (ndisk : nat)
      (cov : gset Z) (dev : mword 32) (E : coPset) :
    fs_cov_in cov ndisk ->
    disk_bytes γv 0 (disk_read dk 0 ndisk) ={E}=∗
    ∃ γfs : fs_names,
      ([∗ set] b ∈ cov, pool_blk (fs_view γfs γv dev cov) b) ∗
      ghost_map_auth (fs_L γfs) 1 (fs_L0 dk cov) ∗
      ghost_map_auth (fs_dirty γfs) 1 (fs_D0 dk cov) ∗
      ([∗ set] b ∈ cov, b ↪[fs_dirty γfs]{#(1/2)} false) ∗
      ([∗ set] b ∈ cov, fsblock γfs b (fs_blocks dk b)) ∗
      ([∗ set] b ∈ cov, blk_own γfs b).
  Proof.
    iIntros (Hcov) "Hm".
    iDestruct (fs_boot_carve γv dk ndisk cov Hcov with "Hm") as "Hblk".
    iMod (fs_alloc (fs_L0 dk cov)) as (γfs) "(HaL & HaD & Hpm)".
    iDestruct (fs_L0_big with "Hpm") as "Hpm".
    (* SCOPE the split.  A bare [rewrite !big_sepS_sep] rewrites the whole
       [envs_entails] -- hypotheses AND the (existentially quantified)
       conclusion -- and does not come back. *)
    iEval (rewrite big_sepS_sep) in "Hpm".
    iDestruct "Hpm" as "[Hfsb Hpm]".
    iEval (rewrite big_sepS_sep) in "Hpm".
    iDestruct "Hpm" as "[Hmc Hpm]".
    iEval (rewrite big_sepS_sep) in "Hpm".
    iDestruct "Hpm" as "[Hdty Hown]".
    iModIntro. iExists γfs.
    iSplitL "Hblk Hmc".
    { iDestruct (big_sepS_sep_2 with "Hblk Hmc") as "H".
      iApply (big_sepS_mono with "H"). intros b Hb.
      iIntros "[Hd Hc]". rewrite /pool_blk /fs_view. cbn [bv_gd bv_clean].
      iExists (fs_blocks dk b). iFrame "Hd Hc". }
    rewrite /fs_D0. iFrame "HaL HaD Hdty Hfsb Hown".
  Qed.

(* ====================================================================== *)
(* 5. THE FULL BOOT BUNDLE.                                               *)
(* ====================================================================== *)

  (* a [∗ set] splits along any subset *)
  Lemma big_sepS_split_sub {A : Type} `{Countable A}
      (Φ : A -> iProp Σ) (X Y : gset A) :
    Y ⊆ X ->
    ([∗ set] x ∈ X, Φ x) ⊢ ([∗ set] x ∈ Y, Φ x) ∗ ([∗ set] x ∈ X ∖ Y, Φ x).
  Proof.
    intros Hsub. rewrite {1}(union_difference_L Y X Hsub).
    rewrite big_sepS_union; [done | set_solver].
  Qed.

  (* the log region's halves, taken apart into the header and the thirty
     slots.  The header keeps its NAMED content; the slots go existential
     (which is all [log_batch] records for them). *)
  Lemma fs_log_region_split (γfs : fs_names) (dk : Z -> bv 8) (logstart : Z) :
    ([∗ set] b ∈ log_region_set logstart, fsblock γfs b (fs_blocks dk b))
      ⊢ fsblock γfs (log_hdr_bno logstart)
                (fs_blocks dk (log_hdr_bno logstart)) ∗
        ([∗ list] i ∈ seq 0 LOGBLOCKS,
           ∃ bs : list (bv 8), fsblock γfs (log_slot_bno logstart i) bs).
  Proof.
    rewrite /log_region_set.
    rewrite big_sepS_union;
      [| apply disjoint_singleton_r;
         rewrite elem_of_list_to_set; apply log_hdr_not_slot ].
    rewrite big_sepS_singleton.
    rewrite (big_sepS_list_to_set
               (fun b => fsblock γfs b (fs_blocks dk b))
               ((fun i => log_slot_bno logstart i) <$> seq 0 LOGBLOCKS)
               (log_slot_list_nodup logstart)).
    rewrite big_sepL_fmap.
    iIntros "[Hslots Hhdr]". iFrame "Hhdr".
    iApply (big_sepL_mono with "Hslots"). intros k i _.
    iIntros "H". iExists (fs_blocks dk (log_slot_bno logstart i)). iExact "H".
  Qed.

  (* THE BUNDLE a boot client applies.  [bio_init]'s premises are copied
     verbatim, in order; the pool bundle it also wants is what this lemma
     manufactures out of the mint. *)
  Lemma fs_boot_bundle (γv : disk_names) (dk : Z -> bv 8) (ndisk : nat)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (E : coPset) :
    fs_cov_in cov ndisk ->
    log_geom_ok cov logstart ->
    bcache_addr ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name bcache_addr "bcache"%string -∗
    add_vec bcache_addr (sign_extend' 64 (mword_of_int 16 : mword 12)) ↦₈
      (zero_reg : mword 64) -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
    ([∗ list] k ∈ seq 0 NBUF,
       b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_disk (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_dev (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       b_blockno (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
       brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
       (∃ bs : list (bv 8), ⌜length bs = 1024%nat⌝ ∗
          [∗ list] j ↦ byte ∈ bs, pa_add (b_data (bpa k)) j ↦ₘ byte)) -∗
    bcache_lru bhead (blist 0 NBUF) -∗
    disk_bytes γv 0 (disk_read dk 0 ndisk) ={E}=∗
    ∃ (bn : bio_names) (γfs : fs_names),
      bio_ctx bn (fs_view γfs γv dev cov) ∗ bslots bn BSLOTS ∗
      ghost_map_auth (fs_L γfs) 1 (fs_L0 dk cov) ∗
      ghost_map_auth (fs_dirty γfs) 1 (fs_D0 dk cov) ∗
      ([∗ set] b ∈ cov, b ↪[fs_dirty γfs]{#(1/2)} false) ∗
      fsblock γfs (log_hdr_bno logstart)
              (fs_blocks dk (log_hdr_bno logstart)) ∗
      ([∗ list] i ∈ seq 0 LOGBLOCKS,
         ∃ bs : list (bv 8), fsblock γfs (log_slot_bno logstart i) bs) ∗
      ([∗ set] b ∈ cov ∖ log_region_set logstart,
         fsblock γfs b (fs_blocks dk b)) ∗
      (* the exclusive per-block tokens, whole and undivided: the log
         region's own blocks are owned by the log layer, everything else by
         whoever the (future) bitmap invariant hands them to.  Purely
         additive -- a consumer that ignores it is unaffected. *)
      ([∗ set] b ∈ cov, blk_own γfs b).
  Proof.
    iIntros (Hcov Hgeom) "Hlkw #Hnm Hcpu Hfresh Hbufs Hlru Hm".
    assert (Hnc0 : (0 : Z) ∉ cov) by (exact (fs_cov_in_0 cov ndisk Hcov)).
    destruct Hgeom as [Hcovok Hsub].
    iMod (fs_boot_ghosts γv dk ndisk cov dev E Hcov with "Hm")
      as (γfs) "(Hpool & HaL & HaD & Hdty & Hfsb & Hown)".
    iMod (bio_init (fs_view γfs γv dev cov) E Hnc0
            with "Hlkw Hnm Hcpu Hfresh Hbufs Hlru Hpool") as (bn) "[Hctx Hsl]".
    iModIntro. iExists bn, γfs.
    iDestruct (big_sepS_split_sub _ cov (log_region_set logstart) Hsub
                 with "Hfsb") as "[Hlog Hrest]".
    iDestruct (fs_log_region_split with "Hlog") as "[Hhdr Hslots]".
    iFrame "Hctx Hsl HaL HaD Hdty Hhdr Hslots Hrest Hown".
  Qed.

End FsBoot.
