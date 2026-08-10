(* IcacheBoot.v -- THE BOOT WIRING OF THE INODE CACHE (fs-icache C7).

   Everything in this file is RESOURCE CONSTRUCTION: pure decoding of the
   mkfs image's inode blocks, plus the ghost steps that turn what boot
   already owns -- the dinode blocks' [fsblock] halves, the fifty entries'
   raw cells, iinit's fifty [sl_fresh]es and the zeroed itable spinlock --
   into the four persistent things every icache contract takes:

       ireg_inv     (InodeRegion)   -- the dinode blocks' owner
       itable_inv   (IcacheInv)     -- the fifty [ref] words
       ic_escrows   (IcacheEscrow)  -- the fifty per-entry escrows
       is_itable2   (IcacheEscrow)  -- the itable spinlock's resource

   ...plus the fifty inode sleeplocks sealed over [ic_tok cn k], which is
   [SpecFileclose.ic_sleeplocks] verbatim (that name lives up in the file-
   close spec, which this file must not depend on, so the family is spelled
   out here and unifies with it by unfolding).

   THE FUNCTION PROOF IS ALREADY DONE.  iinit -- [initlock] plus a loop of
   [initsleeplock] over the fifty entries -- is proven ([ProofIinit.v]) and
   linked into main ([LinkMain], ProofMain.v +0x92).  So the boot wiring is
   NOT a proof obligation about instructions; it is exactly the ghost step
   between iinit's postcondition and the icache's precondition, and that is
   what [icache_boot] below is.

   ---- WHAT THE IMAGE LAYER OWES, AND WHAT IT DOES NOT (§13.3) ----------

   [ireg_alloc] needs NO hypothesis about the image at all.  A dinode is a
   fixed 64-byte little-endian record with THIRTEEN address words and no
   validity constraint ([DinodeEnc.dinode_wf] is a LENGTH condition), and
   16 * 64 = 1024 = BSIZE, so EVERY block of the image decodes: [∃ ds,
   diblk_wf ds /\ bs = diblk_bytes ds] holds for any 1024 bytes.  §1 proves
   that (the surjectivity companions of §12.3's [diblk_bytes_inj]) and §2
   spends it.

   THE POOL IS DIFFERENT.  [IcacheEscrow.ipool_shape]'s ALLOCATED arm carries
   [InodeLock.inode_ok] -- a well-formed block map inside [cov], the size cap
   (§13.5), [blk_holes_zero] and [inode_sized] -- together with the file's
   own [fsblock]s and its indirect block's [blk_own].  Nothing anywhere in
   this tree yet says that the mkfs image's allocated inodes have those
   properties, and no amount of decoding will produce them: they are a claim
   about which BLOCKS the image's inodes own and that those runs are
   disjoint from each other, from the log and from the bitmap.  That is an
   image-well-formedness layer, and it is the bitmap/[ialloc] effort's, not
   the icache's.

   So [ipool_alloc] takes the allocated inums' bundles as a PREMISE, split
   from the free ones -- the honest [FsBoot.fs_cov_in] shape: a hypothesis
   threaded from the boot client, never an axiom.  [ipool_alloc_all_free]
   discharges it outright for an image whose inodes are all type 0, which is
   what makes the premise demonstrably satisfiable rather than vacuous.

   ---- THE BOOT STATE IS ALL-EMPTY (§13.7-§13.9) ------------------------

   [M = ∅], [ci = ∅], every escrow at [ic_empty_arm], every table share at
   [islot_empty], the whole [iref_slots] supply parked in the lock's
   resource, and the pool holding EVERY inum of the region ([region_inums
   nib ∖ ci_inums ∅ = region_inums nib]).  That state is precisely what
   §13.8's empty arm was introduced to make satisfiable, and this file is
   where the claim is cashed.                                            *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import invariants own ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import ArrCursor.
Require Import WpLock.
Require Import SleepLock.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE DECODE: every 1024-byte block IS sixteen dinodes         *)
(* ===================================================================== *)

(* the exact converses of [InodeRegion]'s [*_inj] family.  The workhorse is
   [RiscvModelBytes.nth_byte_assemble_len]: assemble the bytes little-endian
   into a word of the right width and every byte comes back. *)

Lemma list_eta2 {A : Type} `{!Inhabited A} (l : list A) :
  length l = 2%nat -> l = [l !!! 0%nat; l !!! 1%nat].
Proof. destruct l as [|a [|b [|c l]]]; try discriminate. reflexivity. Qed.

Lemma list_eta4 {A : Type} `{!Inhabited A} (l : list A) :
  length l = 4%nat -> l = [l !!! 0%nat; l !!! 1%nat; l !!! 2%nat; l !!! 3%nat].
Proof.
  destruct l as [|a [|b [|c [|d [|e l]]]]]; try discriminate. reflexivity.
Qed.

Lemma half_bytes_surj (bs : list (bv 8)) :
  length bs = 2%nat -> exists w : bv 16, bs = half_bytes w.
Proof.
  intros Hl. exists (Z_to_bv 16 (assemble_bytes bs)).
  assert (Hw : (8 * Z.of_nat (length bs) <= Z.of_N 16)%Z) by (rewrite Hl; cbn; lia).
  rewrite /half_bytes.
  rewrite (nth_byte_assemble_len 16 bs 0%nat Hw ltac:(lia)).
  rewrite (nth_byte_assemble_len 16 bs 1%nat Hw ltac:(lia)).
  exact (list_eta2 bs Hl).
Qed.

Lemma word_bytes_surj (bs : list (bv 8)) :
  length bs = 4%nat -> exists w : bv 32, bs = word_bytes w.
Proof.
  intros Hl. exists (Z_to_bv 32 (assemble_bytes bs)).
  assert (Hw : (8 * Z.of_nat (length bs) <= Z.of_N 32)%Z) by (rewrite Hl; cbn; lia).
  rewrite /word_bytes.
  rewrite (nth_byte_assemble_len 32 bs 0%nat Hw ltac:(lia)).
  rewrite (nth_byte_assemble_len 32 bs 1%nat Hw ltac:(lia)).
  rewrite (nth_byte_assemble_len 32 bs 2%nat Hw ltac:(lia)).
  rewrite (nth_byte_assemble_len 32 bs 3%nat Hw ltac:(lia)).
  exact (list_eta4 bs Hl).
Qed.

Lemma ind_bytes_surj (n : nat) (bs : list (bv 8)) :
  length bs = (4 * n)%nat ->
  exists l : list (bv 32), length l = n /\ bs = ind_bytes l.
Proof.
  revert bs. induction n as [|n IH]; intros bs Hl.
  - exists []. split; [reflexivity |].
    rewrite ind_bytes_nil. destruct bs; [reflexivity | cbn in Hl; lia].
  - destruct (word_bytes_surj (take 4 bs)) as [w Hw];
      [rewrite length_take; lia |].
    destruct (IH (drop 4 bs)) as (l & Hlen & Hdrop);
      [rewrite length_drop; lia |].
    exists (w :: l). split; [cbn; lia |].
    rewrite ind_bytes_cons -Hw -Hdrop take_drop //.
Qed.

(* the six fields' byte windows, as nested take/drops so no [drop_drop]
   index arithmetic is ever needed *)
Lemma dinode_chain (bs : list (bv 8)) :
  bs = (take 2 bs ++ take 2 (drop 2 bs) ++ take 2 (drop 2 (drop 2 bs))
        ++ take 2 (drop 2 (drop 2 (drop 2 bs)))
        ++ take 4 (drop 2 (drop 2 (drop 2 (drop 2 bs))))
        ++ drop 4 (drop 2 (drop 2 (drop 2 (drop 2 bs)))))%list.
Proof.
  rewrite -{1}(take_drop 2 bs). f_equal.
  rewrite -{1}(take_drop 2 (drop 2 bs)). f_equal.
  rewrite -{1}(take_drop 2 (drop 2 (drop 2 bs))). f_equal.
  rewrite -{1}(take_drop 2 (drop 2 (drop 2 (drop 2 bs)))). f_equal.
  rewrite -{1}(take_drop 4 (drop 2 (drop 2 (drop 2 (drop 2 bs))))).
  reflexivity.
Qed.

Lemma dinode_bytes_surj (bs : list (bv 8)) :
  length bs = 64%nat ->
  exists d : dinode, dinode_wf d /\ bs = dinode_bytes d.
Proof.
  intros Hl.
  destruct (half_bytes_surj (take 2 bs)) as [ty Hty];
    [rewrite length_take; lia |].
  destruct (half_bytes_surj (take 2 (drop 2 bs))) as [mj Hmj];
    [rewrite length_take length_drop; lia |].
  destruct (half_bytes_surj (take 2 (drop 2 (drop 2 bs)))) as [mn Hmn];
    [rewrite length_take !length_drop; lia |].
  destruct (half_bytes_surj (take 2 (drop 2 (drop 2 (drop 2 bs))))) as [nl Hnl];
    [rewrite length_take !length_drop; lia |].
  destruct (word_bytes_surj (take 4 (drop 2 (drop 2 (drop 2 (drop 2 bs))))))
    as [sz Hsz]; [rewrite length_take !length_drop; lia |].
  destruct (ind_bytes_surj 13 (drop 4 (drop 2 (drop 2 (drop 2 (drop 2 bs))))))
    as (ad & Had & Hade); [rewrite !length_drop; lia |].
  exists (MkDinode ty mj mn nl sz ad).
  split; [exact Had |].
  rewrite /dinode_bytes.
  cbn [di_type di_major di_minor di_nlink di_size di_addrs].
  rewrite -Hty -Hmj -Hmn -Hnl -Hsz -Hade.
  exact (dinode_chain bs).
Qed.

Lemma diblk_bytes_surj_n (n : nat) (bs : list (bv 8)) :
  length bs = (64 * n)%nat ->
  exists ds : list dinode,
    length ds = n /\ Forall dinode_wf ds /\ bs = diblk_bytes ds.
Proof.
  revert bs. induction n as [|n IH]; intros bs Hl.
  - exists []. split; [reflexivity |]. split; [constructor |].
    rewrite diblk_bytes_nil. destruct bs; [reflexivity | cbn in Hl; lia].
  - destruct (dinode_bytes_surj (take 64 bs)) as (d & Hd & Hde);
      [rewrite length_take; lia |].
    destruct (IH (drop 64 bs)) as (ds & Hlen & Hwf & Hdrop);
      [rewrite length_drop; lia |].
    exists (d :: ds). split; [cbn; lia |]. split; [by constructor |].
    rewrite diblk_bytes_cons -Hde -Hdrop take_drop //.
Qed.

(* THE OBLIGATION [InodeRegion]'s header owes boot: the mkfs image's inode
   blocks decode, and there is no image hypothesis in sight. *)
Lemma diblk_bytes_surj (bs : list (bv 8)) :
  length bs = 1024%nat ->
  exists ds : list dinode, diblk_wf ds /\ bs = diblk_bytes ds.
Proof.
  intros Hl.
  destruct (diblk_bytes_surj_n 16 bs ltac:(lia)) as (ds & Hlen & Hwf & Hde).
  exists ds. split; [split; assumption | exact Hde].
Qed.

(* ...and the whole region's worth of it, as a LIST indexed by block.  Built
   from the front so [(d :: ds) !!! 0] and [(d :: ds) !!! S i] are both
   definitional and no [lookup_app] bookkeeping appears. *)
Lemma image_decode (nib : nat) (bss : nat -> list (bv 8)) :
  (forall bi : nat, (bi < nib)%nat -> length (bss bi) = 1024%nat) ->
  exists dss : list (list dinode),
    length dss = nib /\ Forall diblk_wf dss /\
    (forall bi : nat, (bi < nib)%nat -> bss bi = diblk_bytes (dss !!! bi)).
Proof.
  revert bss. induction nib as [|n IH]; intros bss Hlen.
  - exists []. split; [reflexivity |]. split; [constructor |]. intros; lia.
  - destruct (diblk_bytes_surj (bss 0%nat) (Hlen 0%nat ltac:(lia)))
      as (d0 & Hwf0 & He0).
    destruct (IH (fun bi => bss (S bi))) as (dss & Hl & Hwf & He);
      [intros bi Hbi; apply Hlen; lia |].
    exists (d0 :: dss). split; [cbn; lia |]. split; [by constructor |].
    intros [|bi] Hbi; [exact He0 | apply He; lia].
Qed.

(* ===================================================================== *)
(*  2.  THE REGION'S INITIAL MAP, AND [ireg_alloc]                         *)
(* ===================================================================== *)

(* the image's record for inum [z]: block [z/16], slot [z mod 16] *)
Definition image_dinode (dss : list (list dinode)) (z : Z) : dinode :=
  (dss !!! Z.to_nat (z / 16)) !!! Z.to_nat (z `mod` 16).

Lemma image_dinode_slot (dss : list (list dinode)) (bi i : nat) :
  (i < 16)%nat ->
  image_dinode dss (16 * Z.of_nat bi + Z.of_nat i)%Z = (dss !!! bi) !!! i.
Proof.
  intros Hi. rewrite /image_dinode.
  assert (Hd : ((16 * Z.of_nat bi + Z.of_nat i) / 16)%Z = Z.of_nat bi).
  { replace (16 * Z.of_nat bi + Z.of_nat i)%Z
      with (Z.of_nat i + Z.of_nat bi * 16)%Z by lia.
    rewrite Z.div_add; [| lia]. rewrite Z.div_small; lia. }
  assert (Hm : ((16 * Z.of_nat bi + Z.of_nat i) `mod` 16)%Z = Z.of_nat i).
  { replace (16 * Z.of_nat bi + Z.of_nat i)%Z
      with (Z.of_nat i + Z.of_nat bi * 16)%Z by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  rewrite Hd Hm !Nat2Z.id. reflexivity.
Qed.

(* [FsBoot.fs_L0]'s shape: an [map_imap] over [gset_to_gmap], so the lookup
   law needs no [NoDup] bookkeeping and the domain law is one unfold. *)
Definition ireg_M0 (dss : list (list dinode)) (nib : nat) : gmap Z dinode :=
  map_imap (fun z (_ : unit) => Some (image_dinode dss z))
           (gset_to_gmap () (region_inums nib)).

Lemma ireg_M0_lookup (dss : list (list dinode)) (nib : nat) (z : Z) :
  z ∈ region_inums nib -> ireg_M0 dss nib !! z = Some (image_dinode dss z).
Proof.
  intros Hz. rewrite /ireg_M0 map_lookup_imap lookup_gset_to_gmap.
  rewrite option_guard_True; [reflexivity | exact Hz].
Qed.

Lemma ireg_M0_lookup_Some (dss : list (list dinode)) (nib : nat) (z : Z)
    (dn : dinode) :
  ireg_M0 dss nib !! z = Some dn ->
  z ∈ region_inums nib /\ dn = image_dinode dss z.
Proof.
  rewrite /ireg_M0 map_lookup_imap lookup_gset_to_gmap.
  destruct (decide (z ∈ region_inums nib)) as [Hin|Hout].
  - rewrite option_guard_True; [| exact Hin]. cbn [mbind option_bind].
    intros Heq. injection Heq as <-. done.
  - rewrite option_guard_False; [| exact Hout]. cbn [mbind option_bind].
    discriminate.
Qed.

Lemma ireg_M0_dom (dss : list (list dinode)) (nib : nat) :
  dom (ireg_M0 dss nib) = region_inums nib.
Proof.
  apply set_eq. intros z. rewrite elem_of_dom. split.
  - intros [dn Hdn]. exact (proj1 (ireg_M0_lookup_Some dss nib z dn Hdn)).
  - intros Hz. exists (image_dinode dss z). exact (ireg_M0_lookup dss nib z Hz).
Qed.

Section IcacheBootRegion.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.

  (* [FsBoot.fs_L0_big], for this map *)
  Lemma ireg_M0_big (Phi : Z -> dinode -> iProp Σ)
      (dss : list (list dinode)) (nib : nat) :
    ([∗ map] z ↦ dn ∈ ireg_M0 dss nib, Phi z dn)
      ⊢ [∗ set] z ∈ region_inums nib, Phi z (image_dinode dss z).
  Proof.
    etrans.
    { apply (big_sepM_mono _ (fun z (_ : dinode) => Phi z (image_dinode dss z))).
      intros z dn Hz.
      destruct (ireg_M0_lookup_Some dss nib z dn Hz) as [_ ->]. done. }
    rewrite big_sepM_dom ireg_M0_dom //.
  Qed.

  (* THE REGION'S BOOT ALLOCATION.  In: the [nib] inode blocks' client halves,
     straight out of [FsBoot.fs_boot_bundle]'s [cov ∖ log_region_set] big-op.
     Out: the region invariant and one exclusive [dinode_at] per inum of the
     region, at the image's own record -- which is exactly the pool's input.

     The only premises are arithmetic: each block is a block, and the region's
     inums fit a [uint32] (so [mword_of_int] round-trips on the pool's keys,
     [IcacheEscrow.region_inum_faithful]). *)
  Lemma ireg_alloc (E : coPset) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (bss : nat -> list (bv 8)) :
    16 * Z.of_nat nib <= 2 ^ 32 ->
    (forall bi : nat, (bi < nib)%nat -> length (bss bi) = 1024%nat) ->
    ([∗ list] bi ∈ seq 0 nib,
       fsblock γfs (inodestart + Z.of_nat bi) (bss bi))
    ={E}=∗ ∃ (γi : gname) (dss : list (list dinode)),
      ⌜length dss = nib⌝ ∗ ⌜Forall diblk_wf dss⌝ ∗
      ⌜forall bi : nat, (bi < nib)%nat -> bss bi = diblk_bytes (dss !!! bi)⌝ ∗
      ireg_inv γi γfs inodestart nib ∗
      ([∗ set] z ∈ region_inums nib,
         dinode_at γi (mword_of_int z : mword 32) (image_dinode dss z)).
  Proof.
    intros Hnib Hlen.
    destruct (image_decode nib bss Hlen) as (dss & Hl & Hwf & He).
    iIntros "Hblks".
    iMod (ghost_map_alloc (ireg_M0 dss nib)) as (γi) "[Ha Hels]".
    iDestruct (ireg_M0_big (fun z dn => (z ↪[γi] dn)%I) dss nib with "Hels")
      as "Hels".
    iAssert (ireg_body γi γfs inodestart nib)%I with "[Ha Hblks]" as "Hbody".
    { iExists (ireg_M0 dss nib). iFrame "Ha".
      iApply (big_sepL_mono with "Hblks").
      intros idx bi Hbi. apply lookup_seq in Hbi as [-> Hidx].
      iIntros "H". rewrite /ireg_blk. iExists (dss !!! idx).
      iSplitR.
      { iPureIntro.
        apply (Forall_lookup_1 _ dss idx); [exact Hwf |].
        apply list_lookup_lookup_total_lt. lia. }
      iSplitR.
      { iPureIntro. intros i Hi.
        rewrite (ireg_M0_lookup dss nib _); last first.
        { apply region_inums_spec. lia. }
        rewrite (image_dinode_slot dss idx i Hi) //. }
      rewrite -(He idx Hidx). iExact "H". }
    iMod (inv_alloc iregN E (ireg_body γi γfs inodestart nib) with "[Hbody]")
      as "#Hinv"; [by iNext |].
    iModIntro. iExists γi, dss.
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [iPureIntro; exact He |].
    iFrame "Hinv".
    iApply (big_sepS_mono with "Hels"). intros z Hz.
    rewrite /dinode_at (region_inum_faithful nib z Hnib Hz). done.
  Qed.

End IcacheBootRegion.

(* ===================================================================== *)
(*  3.  STOCKING THE POOL (§13.3)                                         *)
(* ===================================================================== *)

Section IcacheBootPool.
  Context `{!riscvGS Σ, !lockG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId}.

  Lemma ipool_shape_free (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (dn : dinode) :
    bv_unsigned (di_type dn) = 0 ->
    dinode_at γi inum dn -∗ ipool_shape γfs γi cov logstart inum.
  Proof.
    iIntros (H0) "Hdn". rewrite /ipool_shape. iRight.
    iExists dn. iFrame "Hdn". done.
  Qed.

  Lemma ipool_shape_alloc (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    dinode_at γi inum dn -∗ ind_res γfs bm -∗ inode_blocks γfs bm data -∗
    ipool_shape γfs γi cov logstart inum.
  Proof.
    iIntros (Hok) "Hdn Hind Hblk". rewrite /ipool_shape. iLeft.
    iExists dn, bm, data. iFrame "Hdn Hind Hblk". done.
  Qed.

  (* the pool is a [∗ set], so it splits and rejoins along any subset *)
  Lemma ipool_split (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (R A : gset Z) :
    A ⊆ R ->
    ipool γfs γi cov logstart A ∗ ipool γfs γi cov logstart (R ∖ A)
      ⊢ ipool γfs γi cov logstart R.
  Proof.
    intros Hsub. rewrite /ipool -big_sepS_union; [| set_solver].
    rewrite -(union_difference_L A R Hsub) //.
  Qed.

  (* THE STOCKING, in the shape a boot client can actually supply: the
     ALLOCATED inums bring their bundles, everything else is free.  Both
     halves are premises -- see the file header for why the first one cannot
     be manufactured here and must not be axiomatized. *)
  Lemma ipool_alloc (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (R A : gset Z) :
    A ⊆ R ->
    ([∗ set] z ∈ A,
       ∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)),
         ⌜inode_ok cov logstart dn bm data⌝ ∗
         dinode_at γi (mword_of_int z : mword 32) dn ∗
         ind_res γfs bm ∗ inode_blocks γfs bm data) -∗
    ([∗ set] z ∈ R ∖ A,
       ∃ dn : dinode,
         ⌜bv_unsigned (di_type dn) = 0⌝ ∗ dinode_at γi (mword_of_int z : mword 32) dn) -∗
    ipool γfs γi cov logstart R.
  Proof.
    iIntros (Hsub) "Ha Hf".
    iApply (ipool_split γfs γi cov logstart R A Hsub).
    iSplitL "Ha".
    - rewrite /ipool. iApply (big_sepS_mono with "Ha"). intros z _.
      iIntros "(%dn & %bm & %data & %Hok & Hdn & Hind & Hblk)".
      iApply (ipool_shape_alloc _ _ _ _ _ dn bm data Hok with "Hdn Hind Hblk").
    - rewrite /ipool. iApply (big_sepS_mono with "Hf"). intros z _.
      iIntros "(%dn & %H0 & Hdn)".
      iApply (ipool_shape_free _ _ _ _ _ dn H0 with "Hdn").
  Qed.

  (* ...and the case that needs no image theory at all: an image whose inodes
     are ALL free.  This is what makes [ipool_alloc]'s first premise a real
     obligation rather than a vacuous one -- the shape is satisfiable, in one
     line, from [ireg_alloc]'s output alone. *)
  Lemma ipool_alloc_all_free (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (dss : list (list dinode)) (nib : nat) :
    (forall z : Z, z ∈ region_inums nib ->
       bv_unsigned (di_type (image_dinode dss z)) = 0) ->
    ([∗ set] z ∈ region_inums nib,
       dinode_at γi (mword_of_int z : mword 32) (image_dinode dss z)) -∗
    ipool γfs γi cov logstart (region_inums nib).
  Proof.
    iIntros (H0) "H". rewrite /ipool.
    iApply (big_sepS_mono with "H"). intros z Hz.
    iIntros "Hdn".
    iApply (ipool_shape_free _ _ _ _ _ (image_dinode dss z) (H0 z Hz) with "Hdn").
  Qed.

End IcacheBootPool.

(* ===================================================================== *)
(*  4.  THE FIFTY ENTRIES, THE ESCROWS, THE TABLE AND THE LOCK            *)
(* ===================================================================== *)

(* the pure boot state's two well-formedness facts *)
Lemma icM_wf_empty : icM_wf ∅.
Proof.
  split.
  - intros k [x Hx]. rewrite lookup_empty in Hx. discriminate.
  - intros k q n Hx. rewrite lookup_empty in Hx. discriminate.
Qed.

Lemma ic_ci_wf_empty (nib : nat) (dv : mword 32) : ic_ci_wf ∅ ∅ nib dv.
Proof.
  split; [reflexivity |]. split.
  - intros k1 k2 p1 p2 Hp1. rewrite lookup_empty in Hp1. discriminate.
  - split.
    + intros k p Hp. rewrite lookup_empty in Hp. discriminate.
    + intros k p Hp. rewrite lookup_empty in Hp. discriminate.
Qed.

Lemma ci_inums_empty : ci_inums ∅ = (∅ : gset Z).
Proof. rewrite /ci_inums map_to_list_empty //. Qed.

Section IcacheBootTable.
  Context `{!riscvGS Σ, !lockG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId}.

  (* ONE itable ENTRY'S RAW CELLS -- what the loader leaves and iinit does
     not touch: the two identity words at arbitrary contents, the [valid]
     flag likewise, the dinode mirror ([InodeLock.inode_raw]) -- and [ref]
     at CONCRETE ZERO, because [IcacheInv.iref_cells ∅] wants that exact
     word and nothing in the kernel ever writes it before the first iget.
     The .bss cell is zeroed by the loader; [SpecMain]'s [d_used_idx] and
     [kmem+24] conjuncts are the same claim and the precedent for it.
     The sleeplock at +16 is NOT here -- it is iinit's, and comes back as
     [sl_fresh]. *)
  (* stated at the ADDRESS, with the index form right below it: the boot
     byte-carve ([BootCarveMain.boot_inode_entries]) produces the entries as
     an [ArrCursor] family, whose per-element predicate is applied to the
     element's address and cannot mention the index at all. *)
  Definition ientry_raw_at (ip : mword 64) : iProp Σ :=
    ((∃ dev : mword 32, i_dev ip ↦₄ dev) ∗
     (∃ inum : mword 32, i_inum ip ↦₄ inum) ∗
     i_ref ip ↦₄ (mword_of_int 0 : mword 32) ∗
     (∃ w : mword 32, i_valid ip ↦₄ w) ∗
     inode_raw ip)%I.

  Definition ientry_raw (k : nat) : iProp Σ := ientry_raw_at (ientry k).

  (* [BioInv.tok_fun_alloc]'s trick in the other direction: a big-op of
     EXISTENTIALS over [seq j n] yields ONE function of the index.  The
     escrow's identification ghost ([ic_names_alloc]'s [dvs]) has to be
     allocated AT the values the cells already hold, and the cells arrive
     from the loader with those values existentially bound -- so they must
     be collected into a function before any gname exists. *)
  Lemma fun_of_big {A : Type} `{!Inhabited A} (Phi : nat -> A -> iProp Σ)
      (n j : nat) :
    ([∗ list] k ∈ seq j n, ∃ a : A, Phi k a) -∗
    ∃ f : nat -> A, [∗ list] k ∈ seq j n, Phi k (f k).
  Proof.
    iInduction n as [|n IH] forall (j).
    { iIntros "_". iExists (fun _ => inhabitant). cbn [seq]. done. }
    iIntros "H".
    replace (seq j (S n)) with (j :: seq (S j) n) by reflexivity.
    iDestruct "H" as "[Hhd Htl]".
    iDestruct "Hhd" as (a) "Hhd".
    iDestruct ("IH" $! (S j) with "Htl") as (f) "Htl".
    iExists (fun k => if decide (k = j) then a else f k).
    replace (seq j (S n)) with (j :: seq (S j) n) by reflexivity.
    iSplitL "Hhd".
    { case_decide as Hd; [iExact "Hhd" | congruence]. }
    iApply (big_sepL_mono with "Htl"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  Local Lemma ic_id_split_half (cn : ic_names) (k : nat) (v : bool)
      (d n : mword 32) :
    ic_id cn k 1 v d n -∗ ic_id cn k (1/2) v d n ∗ ic_id cn k (1/2) v d n.
  Proof.
    rewrite /ic_id. iIntros "H".
    iApply (ghost_var_split (icn_id cn k) (v, d, n) (1/2) (1/2)).
    rewrite Qp.half_half. iExact "H".
  Qed.

  (* the fifty entries' cells, split field by field.  Stepwise (never
     [rewrite !big_sepL_sep]): the repeated form goes on to split the
     BYTE big-op inside [word4_pointsto] and leaves a hypothesis nothing
     matches. *)
  Local Lemma ientry_raw_split :
    ([∗ list] k ∈ seq 0 NINODE, ientry_raw k)
    ⊢ ([∗ list] k ∈ seq 0 NINODE, ∃ dev : mword 32, i_dev (ientry k) ↦₄ dev) ∗
      ([∗ list] k ∈ seq 0 NINODE, ∃ inum : mword 32, i_inum (ientry k) ↦₄ inum) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         i_ref (ientry k) ↦₄ (mword_of_int 0 : mword 32)) ∗
      ([∗ list] k ∈ seq 0 NINODE, ∃ w : mword 32, i_valid (ientry k) ↦₄ w) ∗
      ([∗ list] k ∈ seq 0 NINODE, inode_raw (ientry k)).
  Proof.
    rewrite /ientry_raw /ientry_raw_at.
    rewrite big_sepL_sep. apply bi.sep_mono_r.
    rewrite big_sepL_sep. apply bi.sep_mono_r.
    rewrite big_sepL_sep. apply bi.sep_mono_r.
    rewrite big_sepL_sep. done.
  Qed.

  Local Lemma iref_cells_boot :
    ([∗ list] k ∈ seq 0 NINODE,
       i_ref (ientry k) ↦₄ (mword_of_int 0 : mword 32))
      ⊢ iref_cells ∅.
  Proof.
    rewrite /iref_cells. apply big_sepL_mono. intros idx k _.
    rewrite /iref_word lookup_empty //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE BOOT STEP                                                      *)
  (* ------------------------------------------------------------------ *)

  (* In: the itable spinlock as iinit leaves it (zeroed word, named, cpu
     field cleared), iinit's fifty [sl_fresh]es, the fifty entries' raw
     cells, the whole [iref_slots] supply, and the stocked pool.
     Out: everything every icache contract takes, at the ALL-EMPTY boot
     state (§13.7-§13.9): [M = ∅], [ci = ∅], fifty [ic_empty_arm]s, fifty
     [islot_empty]s, the pool covering the whole region.

     The last conjunct IS [SpecFileclose.ic_sleeplocks cn], spelled out
     because this file sits below the fileclose spec. *)
  Lemma icache_boot (E : coPset) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) :
    (* THE COUNT AUTHORITY, at the empty table.  A PREMISE rather than an
       allocation, because the authority's gname is CANONICAL -- it is
       [IcacheRef.icfg_iref] of the ambient cache, the same one every
       reference in the system is stated over -- so this lemma cannot mint
       it and then claim to have built THE itable.  [IcacheRef.icfg_alloc]
       is what discharges it. *)
    own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) -∗
    itable_lock ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name itable_lock "itable"%string -∗
    lock_cpu itable_lock ↦₈ (zero_reg : mword 64) -∗
    ([∗ list] k ∈ seq 0 NINODE, sl_fresh (i_lock (ientry k)) "inode"%string) -∗
    ([∗ list] k ∈ seq 0 NINODE, ientry_raw k) -∗
    iref_slots_auth -∗
    ipool γfs γi cov logstart (region_inums nib)
    ={E}=∗ ∃ (γl : gname) (cn : ic_names),
      is_itable2 γl cn γfs γi cov logstart nib dv ∗
      itable_inv ∗
      ic_escrows cn γfs γi cov logstart ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ γil γisl : gname,
           is_sleeplock γil γisl (i_lock (ientry k)) "inode"%string
                        (ic_tok cn k)).
  Proof.
    iIntros "Hauth Hlkw #Hnm Hcpu Hsl Hraw Hsupply Hpool".
    (* ---- take the fifty entries apart, and name the identity values ---- *)
    iDestruct (ientry_raw_split with "Hraw")
      as "(Hdev & Hinum & Href & Hvalid & Hmirror)".
    iDestruct (big_sepL_sep_2 with "Hdev Hinum") as "Hid".
    iAssert ([∗ list] k ∈ seq 0 NINODE,
               ∃ p : mword 32 * mword 32,
                 i_dev (ientry k) ↦₄ p.1 ∗ i_inum (ientry k) ↦₄ p.2)%I
      with "[Hid]" as "Hid".
    { iApply (big_sepL_mono with "Hid"). intros idx k _.
      iIntros "[(%d & Hd) (%n & Hn)]". iExists (d, n). cbn [fst snd]. iFrame. }
    iDestruct (fun_of_big
                 (fun k p => i_dev (ientry k) ↦₄ p.1 ∗ i_inum (ientry k) ↦₄ p.2)%I
                 NINODE 0 with "Hid") as (dvs) "Hid".
    (* ---- the count authority's two halves, and the escrow gnames ---- *)
    iDestruct (itable_half_split with "Hauth") as "[HhalfI HhalfL]".
    iMod (ic_names_alloc dvs) as (cn) "(Htok & Hmid & Hgid)".
    (* ---- the [ref]-word invariant ---- *)
    iMod (inv_alloc icacheN E itable_body
            with "[HhalfI Href]") as "#Hitinv".
    { iNext. iExists ∅. iFrame "HhalfI". iSplitR; [iPureIntro; exact icM_wf_empty |].
      iApply iref_cells_boot. iExact "Href". }
    (* ---- the fifty escrows, at the EMPTY arm, and the table's shares ---- *)
    iDestruct (big_sepL_sep_2 with "Hid Hvalid") as "H1".
    iDestruct (big_sepL_sep_2 with "H1 Hmirror") as "H2".
    iDestruct (big_sepL_sep_2 with "H2 Hmid") as "H3".
    iDestruct (big_sepL_sep_2 with "H3 Hgid") as "H4".
    iAssert ([∗ list] k ∈ seq 0 NINODE,
               |={E}=> ic_escrow cn γfs γi cov logstart k ∗ islot_empty cn k)%I
      with "[H4]" as "Hesc".
    { iApply (big_sepL_mono with "H4"). intros idx k _.
      iIntros "(((([Hd Hn] & (%w & Hv)) & Hmir) & Hmd) & Hgd)".
      iDestruct (ic_id_split_half with "Hgd") as "[Hgd1 Hgd2]".
      iDestruct (word4_pointsto_half_split with "Hn") as "[Hn1 Hn2]".
      iMod (inv_alloc icEscN E (ic_escrow_body cn γfs γi cov logstart k)
              with "[Hd Hn1 Hv Hmir Hmd Hgd1]") as "#Hinv".
      { iNext. rewrite /ic_escrow_body. iRight. iRight. iRight. iLeft.
        rewrite /ic_empty_arm. iExists (dvs k).1, (dvs k).2, w. iFrame. }
      iModIntro. iFrame "Hinv". rewrite /islot_empty.
      iExists (dvs k).1, (dvs k).2. iFrame. }
    iMod (big_sepL_fupd with "Hesc") as "Hesc".
    iEval (rewrite big_sepL_sep) in "Hesc".
    iDestruct "Hesc" as "[#Hescrows Hslots]".
    (* ---- the itable lock's resource, and the lock ---- *)
    iAssert (itable_res2 cn γfs γi cov logstart nib dv)%I
      with "[HhalfL Hsupply Hslots Hpool]" as "Hres".
    { iExists ∅, ∅. iFrame "HhalfL".
      iSplitR; [iPureIntro; exact icM_wf_empty |].
      iSplitR; [iPureIntro; exact (ic_ci_wf_empty nib dv) |].
      iFrame "Hsupply".
      iSplitL "Hslots".
      { iApply (big_sepL_mono with "Hslots"). intros idx k _.
        rewrite /islot2 !lookup_empty. done. }
      rewrite ci_inums_empty difference_empty_L. iExact "Hpool". }
    iMod (newlock E itable_lock "itable"%string
            (itable_res2 cn γfs γi cov logstart nib dv)
            with "Hnm Hlkw Hcpu Hres") as (γl) "#Hlock".
    (* ---- the fifty inode sleeplocks, sealed over the checkout tokens ---- *)
    iDestruct (big_sepL_sep_2 with "Hsl Htok") as "Hsl".
    iAssert ([∗ list] k ∈ seq 0 NINODE,
               |={E}=> ∃ γil γisl : gname,
                 is_sleeplock γil γisl (i_lock (ientry k)) "inode"%string
                              (ic_tok cn k))%I with "[Hsl]" as "Hsl".
    { iApply (big_sepL_mono with "Hsl"). intros idx k _.
      iIntros "[Hf Ht]". iApply (sl_fresh_new with "Hf Ht"). }
    iMod (big_sepL_fupd with "Hsl") as "Hsl".
    iModIntro. iExists γl, cn.
    rewrite /is_itable2. iFrame "Hlock Hitinv Hescrows Hsl".
  Qed.

End IcacheBootTable.

(* ===================================================================== *)
(*  5.  THE ONE ADDRESS BRIDGE main WILL NEED                             *)
(* ===================================================================== *)

(* iinit's loop cursor walks the SLEEPLOCKS at stride 136 from [itable+40]
   ([SpecIinit.inode_lock], which is [ArrCursor.acur inode_lock_base
   inode_stride]); this file's premises are keyed by the ENTRY.  They are
   the same address, and this is the only fact tying the two spellings.
   Stated over the raw literals rather than over [SpecIinit]'s constants so
   that nothing here depends on the iinit spec (whose own [NINODE] would
   shadow [IcacheRef]'s). *)
(* [RiscvExtras.avi_mword]'s proof, at the bare [add_vec] rather than the
   [add_vec_int] wrapper -- the displacement here arrives sign-extended from
   a 12-bit immediate, not as a [Z]. *)
Lemma addv_moi_moi (A B : Z) :
  add_vec (mword_of_int A : mword 64) (mword_of_int B : mword 64)
  = mword_of_int (A + B).
Proof.
  unfold add_vec, mword_of_int, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  apply bv_eq. rewrite bv_add_unsigned !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma inode_lock_is_ientry_lock (k : nat) :
  acur (KernelSyms.itable + 40) 136 k = i_lock (ientry k).
Proof.
  rewrite /acur /i_lock /ientry.
  assert (Hs : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
               = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hs addv_moi_moi.
  f_equal. unfold ISLOTSZ. lia.
Qed.
