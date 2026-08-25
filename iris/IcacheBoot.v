(* IcacheBoot.v -- THE BOOT WIRING OF THE INODE CACHE (fs-icache C7).

   Everything in this file is RESOURCE CONSTRUCTION: pure decoding of the
   mkfs image's inode blocks, plus the ghost steps that turn what boot
   already owns -- the dinode blocks' [fs_chalf] halves, the fifty entries'
   raw cells, iinit's fifty [sl_fresh]es and the zeroed itable spinlock --
   into the four persistent things every icache contract takes:

       ireg_inv     (InodeRegion)   -- the dinode blocks' owner
       itable_inv   (IcacheInv)     -- the fifty [ref] words
       ic_escrows   (IcacheEscrow)  -- the fifty per-entry escrows
       is_itable2   (IcacheEscrow)  -- the itable spinlock's resource

   ...plus the fifty inode sleeplocks sealed over [ic_tok cn k], which is
   [IcacheEscrow.ic_sleeplocks] verbatim.

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
   own byte runs, its indirect block's included.  Nothing anywhere in
   this tree yet says that the mkfs image's allocated inodes have those
   properties, and no amount of decoding will produce them: they are a claim
   about which BLOCKS the image's inodes own and that those runs are
   disjoint from each other, from the log and from the bitmap.  That is an
   image-well-formedness layer, and it is the bitmap/[ialloc] effort's, not
   the icache's.

   SINCE fs-icache.md §15(a) the allocated arm carries ONE MORE image-wf
   clause of exactly the same kind, [DirView.dir_ok icfg_nib]: if the inode
   is a DIRECTORY then every live record in its data names an inum the inode
   region covers.  It is a claim about the image's directory CONTENTS, not
   about decoding, so it joins the premise family here rather than being
   discharged -- mkfs images satisfy it, and the eventual ireclaim/fsinit
   mint (N5) will owe it alongside [inode_ok].

   [DirView.dir_dots_ix] joins that family on the same terms and for the
   same reason: a LIVE directory in the image has its [".."] at record 1.
   mkfs writes ["."] then [".."] into every directory it creates, in that
   order and nothing between, so the clause is true of any mkfs image -- and
   it is a claim about CONTENTS, so boot threads it and does not prove it.
   Zero proof obligation lands here: the two lemmas below take it and pass
   it on, exactly as they do [dir_ok].

   [DirView.dir_orphan_clean] -- the complement clause, an ORPHANED
   directory's live records are exactly ["."] and [".."] -- rides on the
   same terms again, and at boot it is the easiest of the three: mkfs
   writes NO orphan at all (every directory it creates is linked into its
   parent before the image is sealed), so the antecedent [nlink = 0] is
   false of every allocated record in the image and the clause is vacuous.
   It is still THREADED rather than discharged, because "the image contains
   no orphan" is a statement about contents that this file has no decoding
   fact for.

   So [ipool_alloc] takes the allocated inums' bundles as a PREMISE, split
   from the free ones -- the honest [FsBoot.fs_cov_in] shape: a hypothesis
   threaded from the boot client, never an axiom.  [ipool_alloc_all_free]
   discharges it outright for an image whose inodes are all type 0, which is
   what makes the premise demonstrably satisfiable rather than vacuous (and
   which needs no [dir_ok] clause at all: the free arm has no data).

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
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import invariants own ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvModelBytes.
Require Import ArrCursor.
Require Import WpLock.
Require Import WpLockAt.   (* [lock_free_tok] / [newlock_at]: the pre-minted
                              lock gname, for [icache_boot_at] below *)
Require Import SleepLock.
Require Import FsBlocks.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirView.
Require Import DirLinks.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
(* durable-disk 2b-inode-3: the pool's allocated arm is the era bundle.
   [FsState] for [top_frag], [FsBytesGamma] for [fs_gamma_L], [FsStateEra]
   for [era_node] / [inode_rec_local] / [inode_owned_era_era_node_of]. *)
Require Import FsState.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import FsTree.
Require Import DirViewG.   (* [dv_hold]/[dv_of] -- the pool's contents holds *)
Require Import DirViewLend. (* N-4 PHASE B: [dv_lcol] / [dv_lic], boot-stocked *)
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From iris.base_logic.lib Require Import mono_nat.
Require Import LogInv.  (* [logG]: the region's zero-receipt, fs-log.md G.17 *)
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

(* [FsBoot.fs_C0]'s shape: an [map_imap] over [gset_to_gmap], so the lookup
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

(* ---------------------------------------------------------------------- *)
(*  THE MARKER HALF OF THE MINT (§16.4)                                     *)
(* ---------------------------------------------------------------------- *)

(* The region's map carries a SECOND entry per inum, at [imark_key]'s
   negative shadow of it: [InodeRegion.imark], the per-inum token that says
   "this inum's record fragment is not in the region".  It is minted here,
   in the same [ghost_map_alloc] as the records, and after that it is only
   ever MOVED -- never updated, never created -- so its value is irrelevant
   and this is the constant it is minted at. *)
Definition dinode_mark : dinode :=
  MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32) [].

Definition mark_inums (nib : nat) : gset Z :=
  list_to_set ((fun j : nat => imark_key (Z.of_nat j)) <$> seq 0 (16 * nib)).

Lemma mark_inums_neg (nib : nat) (y : Z) : y ∈ mark_inums nib -> y < 0.
Proof.
  rewrite /mark_inums elem_of_list_to_set elem_of_list_fmap.
  intros (j & -> & _). rewrite /imark_key. lia.
Qed.

Definition ireg_MK (nib : nat) : gmap Z dinode :=
  gset_to_gmap dinode_mark (mark_inums nib).

Lemma ireg_M0_MK_disj (dss : list (list dinode)) (nib : nat) :
  ireg_M0 dss nib ##ₘ ireg_MK nib.
Proof.
  apply map_disjoint_spec. intros z d1 d2 H1 H2.
  destruct (ireg_M0_lookup_Some dss nib z d1 H1) as [Hz _].
  apply region_inums_spec in Hz.
  rewrite /ireg_MK lookup_gset_to_gmap in H2.
  destruct (decide (z ∈ mark_inums nib)) as [Hm|Hm].
  - pose proof (mark_inums_neg nib z Hm). lia.
  - rewrite option_guard_False in H2; [discriminate | exact Hm].
Qed.

(* the two index lists the region's [∗ set]s unfold to, both duplicate-free *)
Lemma region_list_nodup (nib : nat) :
  base.NoDup (Z.of_nat <$> seq 0 (16 * nib)).
Proof.
  apply NoDup_fmap_2_strong; [intros x y _ _ H; lia | apply NoDup_seq].
Qed.

Lemma mark_list_nodup (nib : nat) :
  base.NoDup ((fun j : nat => imark_key (Z.of_nat j)) <$> seq 0 (16 * nib)).
Proof.
  apply NoDup_fmap_2_strong;
    [intros x y _ _ H; rewrite /imark_key in H; lia | apply NoDup_seq].
Qed.

(* ===================================================================== *)
(*  1b.  THE LEDGER'S BOOT MINT AT THE IMAGE'S LINK COUNTS (§20.6 stage B) *)
(* ===================================================================== *)

(*  STAGE A minted the ledger ALL-PLAIN: [IcacheRef.link_boot_map] is one
    element [● lelem_boot ⋅ ◯ lelem_boot] per inum with every count at zero,
    so no [IcacheRef.ilink] fragment existed anywhere at boot and
    [DirLinks.dir_links] had no producer -- a live directory's records each
    want one.  THIS is the widening the [w = 0] note below [ireg_alloc]
    promised.

    IT IS A MINT, NOT A DIFFERENT BOOT MAP, and that is a measured decision.
    The obvious route -- widen [link_boot_map] to carry [● lelem_boot_w (W z)
    ⋅ ◯ lelem_boot_w (W z)] and CUT the fragment half into [W z] tickets --
    needs the equation

        lelem_boot_w n = lelemf 0 .. (Some (Excl FrzOff)) ⋅ lelem n ..

    and although that equation is DEFINITIONAL, deciding it by conversion
    over [linkElemUR]'s seven-deep nest does not terminate (>60 s at [n]
    abstract, measured on the lane -- the same blowup [IcacheRef]'s
    [lelemf_op_none] header records for [rewrite -!pair_op]).  So boot takes
    the all-plain map UNCHANGED, hands it to [IcacheRef.link_boot_split] as
    before, and then BUMPS each authority [W z] times with the landed
    [IcacheRef.link_mint_link] -- one [nat_local_update] per ticket, at the
    named atoms, where the algebra is already proven and instant.  No new
    camera literal, no new validity obligation, and [icfg_alloc]'s [LM]
    argument does not move.

    Stage A is the instance [W = fun _ => 0]: at it the mint is the identity
    and [ireg_alloc]'s three new image premises below are vacuous-or-zero.  *)

Section IcacheBootLedger.
  Context `{!xv6G Σ}.
  Context `{ICFG : icfg}.

  (* [n] tickets off one authority, by [n] applications of the landed
     one-ticket mint.  The index list starts at an arbitrary [j] so the
     induction peels from the FRONT (which is where [link_mint_link] puts
     its ticket); every caller instantiates [j = 0]. *)
  (* Stated at BOOT'S OWN COLUMNS rather than at nine binders: the general
     form would have to name [dfrac_agreeR], which this file does not
     import, and boot has no use for it. *)
  Lemma link_mint_pile (z : Z) (n j wl : nat) :
    link_auth z wl 0 0 0 None 0 None (Some (Excl FrzOff)) 0 ==∗
    link_auth z (n + wl) 0 0 0 None 0 None (Some (Excl FrzOff)) 0
    ∗ [∗ list] _ ∈ seq j n, ilink z.
  Proof.
    revert j wl. induction n as [| n IH]; intros j wl.
    { iIntros "Ha". iModIntro. iSplitL "Ha"; [iExact "Ha" | done]. }
    iIntros "Ha".
    iMod (link_mint_link with "Ha") as "[Ha Htk]".
    iMod (IH (S j) (S wl) with "Ha") as "[Ha Hpile]".
    iModIntro.
    replace (S n + wl)%nat with (n + S wl)%nat by lia.
    iSplitL "Ha"; [iExact "Ha" |].
    replace (seq j (S n)) with (j :: seq (S j) n) by reflexivity.
    rewrite big_sepL_cons.
    iSplitL "Htk"; [iExact "Htk" | iExact "Hpile"].
  Qed.

  (* **THE STAGE-B PAYOUT.**  In: [IcacheRef.link_boot_split]'s all-plain
     authorities, verbatim.  Out: the SAME authorities standing at the
     image's own per-inum ticket count, plus those tickets.  The authority
     goes to [ireg_alloc] (it parks one per slot); the tickets go to
     [DirLinks.dir_links] via [FsCfgBoot.dir_links_of_region]. *)
  Lemma link_boot_mint_w (W : Z -> nat) (P : gset Z) :
    ([∗ set] z ∈ P, link_auth z 0 0 0 0 None 0 None (Some (Excl FrzOff)) 0)
    ==∗ [∗ set] z ∈ P,
          (link_auth z (W z) 0 0 0 None 0 None (Some (Excl FrzOff)) 0
           ∗ [∗ list] _ ∈ seq 0 (W z), ilink z).
  Proof.
    iIntros "H". iApply big_sepS_bupd.
    iApply (big_sepS_mono with "H"). intros z _. iIntros "Ha".
    iMod (link_mint_pile z (W z) 0 with "Ha") as "[Ha Hpile]".
    rewrite Nat.add_0_r. iModIntro.
    iSplitL "Ha"; [iExact "Ha" | iExact "Hpile"].
  Qed.

End IcacheBootLedger.

Section IcacheBootRegion.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{ICFG : icfg}.

  (* [FsBoot.fs_C0_big], for this map *)
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

  (* THE REGION'S INUMS, RE-INDEXED AS (block, slot).  [ireg_M0] is a flat
     inum-keyed map and [ireg_body]'s per-block conjunct is a nested
     [seq 0 nib] / [seq 0 16]; this is the one bridge between them, and it
     is what §16.4's per-slot arm made necessary (before it, the blocks'
     conjunct held no ghost elements at all). *)
  Local Lemma seq16_flatten (n : nat) (Phi : nat -> iProp Σ) :
    ([∗ list] j ∈ seq 0 (16 * n), Phi j)
    ⊢ [∗ list] bi ∈ seq 0 n, [∗ list] i ∈ seq 0 16, Phi (16 * bi + i)%nat.
  Proof.
    revert Phi. induction n as [|n IH]; intros Phi.
    { cbn [seq]. iIntros "_". done. }
    replace (16 * S n)%nat with (16 + 16 * n)%nat by lia.
    rewrite seq_app big_sepL_app.
    iIntros "[Hhd Htl]".
    replace (seq 0 (S n)) with (0%nat :: seq 1 n) by reflexivity.
    rewrite big_sepL_cons.
    iSplitL "Hhd".
    { iApply (big_sepL_mono with "Hhd"). intros idx i Hi.
      apply lookup_seq in Hi as [-> _].
      replace (16 * 0 + (0 + idx))%nat with (0 + idx)%nat by lia. done. }
    assert (Hseq : seq (0 + 16) (16 * n) = Nat.add 16 <$> seq 0 (16 * n)).
    { rewrite fmap_add_seq.
      replace (0 + 16)%nat with (16 + 0)%nat by lia. reflexivity. }
    rewrite Hseq big_sepL_fmap.
    iPoseProof (IH (fun j => Phi (16 + j)%nat) with "Htl") as "Htl".
    assert (Hs1 : seq 1 n = S <$> seq 0 n) by (rewrite fmap_S_seq; reflexivity).
    rewrite Hs1 big_sepL_fmap.
    iApply (big_sepL_mono with "Htl"). intros idx bi Hbi.
    iIntros "H". iApply (big_sepL_mono with "H"). intros idx2 i Hi.
    replace (16 * S bi + i)%nat with (16 + (16 * bi + i))%nat by lia. done.
  Qed.

  (* ...and the same bridge for the MARKER half, whose keys are the negative
     shadows of the very same inums *)
  Lemma imark_of_marks (γi : gname) (nib : nat) :
    ([∗ map] y ↦ d ∈ ireg_MK nib, y ↪[γi] d)
    ⊢ [∗ set] z ∈ region_inums nib, imark γi z.
  Proof.
    rewrite /ireg_MK big_sepM_gset_to_gmap.
    rewrite /mark_inums (big_sepS_list_to_set _ _ (mark_list_nodup nib)).
    rewrite big_sepL_fmap.
    rewrite /region_inums (big_sepS_list_to_set _ _ (region_list_nodup nib)).
    rewrite big_sepL_fmap.
    iIntros "H". iApply (big_sepL_mono with "H"). intros idx j Hj.
    iIntros "H". rewrite /imark. iExists dinode_mark. iExact "H".
  Qed.

  Lemma ireg_slots_of_set (γfs : fs_names) (γi : gname)
      (dss : list (list dinode)) (nib : nat) :
    ([∗ set] z ∈ region_inums nib, ireg_slot γfs γi z (image_dinode dss z))
    ⊢ [∗ list] bi ∈ seq 0 nib,
        [∗ list] i ∈ seq 0 16,
          ireg_slot γfs γi (16 * Z.of_nat bi + Z.of_nat i)%Z ((dss !!! bi) !!! i).
  Proof.
    rewrite /region_inums (big_sepS_list_to_set _ _ (region_list_nodup nib)).
    rewrite big_sepL_fmap.
    iIntros "H".
    iPoseProof (seq16_flatten nib
                  (fun j => ireg_slot γfs γi (Z.of_nat j)
                              (image_dinode dss (Z.of_nat j))) with "H") as "H".
    iApply (big_sepL_mono with "H"). intros idx bi Hbi.
    iIntros "H". iApply (big_sepL_mono with "H"). intros idx2 i Hi.
    apply lookup_seq in Hi as [-> Hilt].
    assert (Hz : Z.of_nat (16 * bi + (0 + idx2))%nat
                 = (16 * Z.of_nat bi + Z.of_nat (0 + idx2))%Z) by lia.
    rewrite Hz (image_dinode_slot dss bi (0 + idx2) ltac:(lia)).
    done.
  Qed.

  (* THE REGION'S BOOT ALLOCATION.  In: the [nib] inode blocks' client halves,
     straight out of [FsBoot.fs_boot_bundle]'s [cov ∖ log_region_set] big-op.
     Out: the region invariant and one exclusive [dinode_at] per inum of the
     region, at the image's own record -- which is exactly the pool's input.

     The only premises are arithmetic: each block is a block, and the region's
     inums fit a [uint32] (so [mword_of_int] round-trips on the pool's keys,
     [IcacheEscrow.region_inum_faithful]). *)
  (* WHAT IT PAYS OUT IS NOW CONDITIONAL (§16.4).  A FREE inum's record
     fragment STAYS in the region -- that is the whole point of §16.3, and
     it is what gives ialloc's claim something to retag -- so what comes out
     for it is the MARKER; an ALLOCATED inum's fragment comes out as before.
     One [InodeRegion.ireg_out] covers both, and the pool's two arms consume
     exactly the two cases.  The mint is strictly CHEAPER than it was: an
     all-free image now needs no image-wf premise and no pool contents
     beyond markers ([ipool_alloc_all_free] below). *)
  (* THE LEDGER'S BOOT MINT (design §20.6's boot row, fs-sysfile S5f).  The
     region parks one link authority per inum, so the boot client owes them
     -- one per inum of the region, at the EMPTY ledger.  It is an honest
     image obligation of exactly [ipool_shape_alloc]'s kind: nothing in
     this file can manufacture a ghost the ambient [icfg_link] names.

     THEY ARE NOW STATED AT [w_z] -- STAGE B, the widening this note used to
     promise.  [W] is the image's per-inum count of ticket-bearing directory
     records ([FsImg.fs_link_count]), and the premise is exactly what
     [link_boot_mint_w] above hands over: the SAME authority
     [IcacheRef.link_boot_split] produces, bumped [W z] times, whose
     by-product is the [W z] [IcacheRef.ilink] fragments that stock
     [DirLinks.dir_links] (spent by [FsCfgBoot.dir_links_of_region]).
     Stage A is the instance [W = fun _ => 0]: at it the mint is the identity,
     the three new image premises below are vacuous-or-zero and this lemma is
     byte-for-byte what it was.  The authority's SHAPE did not change, only
     its value.

     AND (L3) IS AN IMAGE OBLIGATION (fs-sysfile S5g).  With the ledger's
     clauses landed, [ireg_slot] now says of every record that a ZERO TYPE
     forces a zero [nlink] -- true of every mkfs image, false of nothing
     this kernel can produce (the only writer that clears a type is iput's
     free, which runs behind [ip->nlink == 0]), and unprovable here: the
     bytes are the boot client's.  So it rides as a premise, in the same
     ∀-over-decodings form the payout's own image premises take, because
     [dss] is produced by [image_decode] inside the proof.  (L1) at [w = 0]
     needs nothing. *)
  Definition image_free_nlink (dss : list (list dinode)) (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib ->
      bv_unsigned (di_type (image_dinode dss z)) = 0 ->
      bv_unsigned (di_nlink (image_dinode dss z)) = 0.

  (* ...AND (L4) IS AN IMAGE OBLIGATION FOR THE SAME REASON (the twelfth
     stop).  [ireg_slot] now also says of every record that its link count
     is a NON-NEGATIVE short -- true of every mkfs image (mkfs writes 1 or
     2), false of nothing this kernel can produce (xv6 117c0e7 refuses the
     raise at 32767 and no path lowers below zero -- [sys_unlink] panics
     first), and unprovable here for the same reason (L3) is: the bytes are
     the boot client's and any 64 of them decode.  It rides in the SAME
     ∀-over-decodings premise slot rather than a new one, so [ireg_alloc]'s
     arity does not move. *)
  Definition image_nlink_short (dss : list (list dinode)) (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib ->
      bv_unsigned (di_nlink (image_dinode dss z)) <= 32767.

  (* ...AND (L5) IS AN IMAGE OBLIGATION FOR THE SAME REASON (durable-disk
     2b-inode-3).  [ireg_slot] now also says of every record that its TYPE
     is one of the four, which is [FsStateInode.inode_local]'s [inl_type]
     and has no other producer; at boot it is [FsImg.fio_type] at a live
     inode and type 0 everywhere else. *)
  Definition image_ty_ok (dss : list (list dinode)) (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib -> ireg_ty_ok (image_dinode dss z).

  (* ...AND (L1) BECOMES ONE TOO, for the first time.  At [w = 0] it was
     [0 <= nlink] and needed nothing; at [w = W z] it is the real ledger
     clause -- "no more tickets than links" -- and it is a fact about the
     image's directory CONTENTS, which is why it rides in the same
     ∀-over-decodings slot as (L3)/(L4) and the root clause. *)
  Definition image_link_le (W : Z -> nat) (dss : list (list dinode))
      (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib ->
      (W z <= Z.to_nat (bv_unsigned (di_nlink (image_dinode dss z))))%nat.

  (* ...AND THE LINK RA's OWN TIE (durable-disk 2b-inode-4).  The region
     parks one [FsStateLink.link_auth] per inum standing at the record's
     [nlink], with all its tokens still at home; the caller hands the
     family over indexed by a FUNCTION (the resource cannot mention [dss],
     which this lemma decodes internally), and this is the equation that
     lands it on the decoded record.  At the caller it is
     [FsCfgBoot]'s own [image_dinode_fs_dinode] and nothing more. *)
  Definition image_nlink_at (N : Z -> nat) (dss : list (list dinode))
      (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib -> N z = ireg_nl (image_dinode dss z).

  (* ...AND CONJUNCT (14) [FsCfgBoot.fs_region_bare] RESTATED AT THE DECODED
     RECORD (durable-disk C-3c).  [InodeRegion.ireg_top_park] parks a FREE
     inum's [FsState.top_frag] TIED to the record beside it, and the tie says
     the node is [InodeRegion.free_node] of that record -- which is only
     [FsStateInode.inode_local] if the record names no block and has size
     zero.  Every mkfs image satisfies it and every free record this kernel
     writes does ([EscrowDeposit.ireg_free_deposit_au]'s own premise, itrunc
     having run first); like (L3)/(L4)/(L5) it is unprovable here because the
     bytes are the boot client's, so it rides the same ∀-over-decodings slot
     and [ireg_alloc]'s premise list does not grow a second one. *)
  Definition image_bare (dss : list (list dinode)) (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib ->
      bv_unsigned (di_type (image_dinode dss z)) = 0 ->
      ireg_bare (image_dinode dss z).

  (* ...AND THE RECORD FUNCTION THE PARK IS INDEXED BY, for [image_nlink_at]'s
     reason verbatim: the resource cannot mention [dss], which [ireg_alloc]
     decodes internally, so the caller hands the family over indexed by a
     FUNCTION and this is the equation that lands it on the decoded record.
     At the caller it is [FsCfgBoot.image_dinode_fs_dinode]. *)
  Definition image_rec_at (D : Z -> dinode) (dss : list (list dinode))
      (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib -> D z = image_dinode dss z.

  (* ...AND SO DOES [InodeRegion.ireg_dir_wl0]: a record naming a DIRECTORY
     pays in the d-flavoured column ([ilinkd]/[ilinkdp]), never the plain
     one, so a directory's plain column must be EMPTY.  Boot mints no
     d-fragment at all ([DirLinks.dir_links_of_plain] is the all-plain
     stock), so the image owes exactly "no ticket names a directory" -- true
     of every mkfs image, whose one directory is the root and whose root's
     two dot records are both SELF records that bear no ticket. *)
  Definition image_dir_wl0 (W : Z -> nat) (dss : list (list dinode))
      (nib : nat) : Prop :=
    forall z : Z, z ∈ region_inums nib ->
      bv_unsigned (di_type (image_dinode dss z)) = ireg_dir_ty ->
      W z = 0%nat.

  (* OPTION A: the boot registry map.  Every inum maps to a DUMMY escrow gname
     pair -- at boot no inum is in escrow, and [ireg_claim_au]'s pending-arm
     refutation is value-agnostic (it collides fractions, not gnames).  The
     reordered-iput walk re-mints real (committedA, redeem) gnames and updates
     this map's entry when it actually deposits. *)
  Definition dummy_reg (nib : nat) : gmap Z (gname * gname) :=
    gset_to_gmap (1%positive, 1%positive) (region_inums nib).

  Lemma dummy_reg_cov (nib : nat) (z : Z) :
    (0 <= z < 16 * Z.of_nat nib)%Z -> is_Some (dummy_reg nib !! z).
  Proof.
    intros Hz. rewrite /dummy_reg. eexists.
    apply lookup_gset_to_gmap_Some. split; [apply region_inums_spec; lia | reflexivity].
  Qed.

  Lemma dummy_reg_key (nib : nat) (k : Z) (v : gname * gname) :
    dummy_reg nib !! k = Some v -> (0 <= k)%Z.
  Proof.
    rewrite /dummy_reg. intros Hk.
    apply lookup_gset_to_gmap_Some in Hk as [Hin _].
    apply region_inums_spec in Hin. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  N-4 PHASE B (E1-region): the LEND COLUMN's boot state              *)
  (* ------------------------------------------------------------------ *)

  (*  The region's per-inum lend column ([DirViewLend.dv_lcol], parked in
      [InodeRegion.ireg_registry]) is stocked here, in the NONE state at
      every inum, and it costs no boot map and no [icfg] field: the two
      [dviewUR] cell families are minted by two [own_alloc]s at the SAME
      [dview_boot_map] the contents ghost uses, and the two registry key
      families ride the [icfg_reg] AUTHORITY this lemma is already handed
      -- a ghost_map can grow a key, which is exactly why the lend's names
      live there and not in a bare [own] map.  The mint LICENCES leave with
      the caller (FsCfgBoot), where N-5.1's stocking mint will spend them.  *)

  (* the region-set / [seq] bridge: [ireg_lends] is indexed flat *)
  Lemma region_set_to_seq (nib : nat) (Phi : Z -> iProp Σ) :
    ([∗ set] z ∈ region_inums nib, Phi z) ⊣⊢
    ([∗ list] k ∈ seq 0 (16 * nib), Phi (Z.of_nat k)).
  Proof.
    rewrite /region_inums (big_sepS_list_to_set _ _ (region_list_nodup nib)).
    by rewrite big_sepL_fmap.
  Qed.

  Definition lend_slots (γc γv : gname) (nib : nat) : gmap Z (gname * gname) :=
    gset_to_gmap (γc, γv) (set_map dvl_k (region_inums nib)).
  Definition lend_lics (nib : nat) : gmap Z (gname * gname) :=
    gset_to_gmap (1%positive, 1%positive) (set_map dvl_l (region_inums nib)).
  Definition lend_reg (γc γv : gname) (nib : nat) : gmap Z (gname * gname) :=
    lend_slots γc γv nib ∪ lend_lics nib.

  Lemma lend_slots_key (γc γv : gname) (nib : nat) (k : Z) (v : gname * gname) :
    lend_slots γc γv nib !! k = Some v -> exists z, k = dvl_k z /\ (0 <= z)%Z.
  Proof.
    rewrite /lend_slots. intros Hk.
    apply lookup_gset_to_gmap_Some in Hk as [Hin _].
    apply elem_of_map in Hin as (z & -> & Hz).
    apply region_inums_spec in Hz. exists z. split; [reflexivity | lia].
  Qed.

  Lemma lend_lics_key (nib : nat) (k : Z) (v : gname * gname) :
    lend_lics nib !! k = Some v -> exists z, k = dvl_l z /\ (0 <= z)%Z.
  Proof.
    rewrite /lend_lics. intros Hk.
    apply lookup_gset_to_gmap_Some in Hk as [Hin _].
    apply elem_of_map in Hin as (z & -> & Hz).
    apply region_inums_spec in Hz. exists z. split; [reflexivity | lia].
  Qed.

  Lemma lend_slots_lics_disj (γc γv : gname) (nib : nat) :
    lend_slots γc γv nib ##ₘ lend_lics nib.
  Proof.
    apply map_disjoint_spec. intros k x y H1 H2.
    apply lend_slots_key in H1 as (z & -> & _).
    apply lend_lics_key in H2 as (w & Hw & _).
    exact (dvl_k_l_ne z w Hw).
  Qed.

  (* ---- N-5.2A: the fview column's two key families, side by side ------ *)

  Definition flend_slots (γc γv : gname) (nib : nat) : gmap Z (gname * gname) :=
    gset_to_gmap (γc, γv) (set_map fvl_k (region_inums nib)).
  Definition flend_lics (nib : nat) : gmap Z (gname * gname) :=
    gset_to_gmap (1%positive, 1%positive) (set_map fvl_l (region_inums nib)).
  Definition flend_reg (γc γv : gname) (nib : nat) : gmap Z (gname * gname) :=
    flend_slots γc γv nib ∪ flend_lics nib.

  (* all four families, as ONE insertion into the registry auth *)
  Definition lend_reg_all (γc γv γfc γfv : gname) (nib : nat)
    : gmap Z (gname * gname) :=
    lend_reg γc γv nib ∪ flend_reg γfc γfv nib.

  Lemma flend_slots_key (γc γv : gname) (nib : nat) (k : Z) (v : gname * gname) :
    flend_slots γc γv nib !! k = Some v -> exists z, k = fvl_k z /\ (0 <= z)%Z.
  Proof.
    rewrite /flend_slots. intros Hk.
    apply lookup_gset_to_gmap_Some in Hk as [Hin _].
    apply elem_of_map in Hin as (z & -> & Hz).
    apply region_inums_spec in Hz. exists z. split; [reflexivity | lia].
  Qed.

  Lemma flend_lics_key (nib : nat) (k : Z) (v : gname * gname) :
    flend_lics nib !! k = Some v -> exists z, k = fvl_l z /\ (0 <= z)%Z.
  Proof.
    rewrite /flend_lics. intros Hk.
    apply lookup_gset_to_gmap_Some in Hk as [Hin _].
    apply elem_of_map in Hin as (z & -> & Hz).
    apply region_inums_spec in Hz. exists z. split; [reflexivity | lia].
  Qed.

  Lemma flend_slots_lics_disj (γc γv : gname) (nib : nat) :
    flend_slots γc γv nib ##ₘ flend_lics nib.
  Proof.
    apply map_disjoint_spec. intros k x y H1 H2.
    apply flend_slots_key in H1 as (z & -> & _).
    apply flend_lics_key in H2 as (w & Hw & _).
    exact (fvl_k_l_ne z w Hw).
  Qed.

  (* THE COLLISION QUESTION, answered once: dview's two families and fview's
     two are pairwise disjoint by residue mod 4 ([DirViewLend] §0's six
     [lia]s), and all four are negative while every landed registry key is a
     region inum. *)
  Lemma lend_flend_disj (γc γv γfc γfv : gname) (nib : nat) :
    lend_reg γc γv nib ##ₘ flend_reg γfc γfv nib.
  Proof.
    apply map_disjoint_spec. intros k x y H1 H2.
    apply lookup_union_Some_raw in H1 as [H1|[_ H1]];
      apply lookup_union_Some_raw in H2 as [H2|[_ H2]].
    - apply lend_slots_key in H1 as (z & -> & _).
      apply flend_slots_key in H2 as (w & Hw & _). exact (dvl_k_fvl_k_ne z w Hw).
    - apply lend_slots_key in H1 as (z & -> & _).
      apply flend_lics_key in H2 as (w & Hw & _). exact (dvl_k_fvl_l_ne z w Hw).
    - apply lend_lics_key in H1 as (z & -> & _).
      apply flend_slots_key in H2 as (w & Hw & _). exact (dvl_l_fvl_k_ne z w Hw).
    - apply lend_lics_key in H1 as (z & -> & _).
      apply flend_lics_key in H2 as (w & Hw & _). exact (dvl_l_fvl_l_ne z w Hw).
  Qed.

  Lemma lend_reg_all_neg (γc γv γfc γfv : gname) (nib : nat)
      (k : Z) (v : gname * gname) :
    lend_reg_all γc γv γfc γfv nib !! k = Some v -> (k < 0)%Z.
  Proof.
    rewrite /lend_reg_all /lend_reg /flend_reg. intros Hk.
    apply lookup_union_Some_raw in Hk as [Hk|[_ Hk]];
      apply lookup_union_Some_raw in Hk as [Hk|[_ Hk]].
    - apply lend_slots_key in Hk as (z & -> & Hz). exact (dvl_k_neg z Hz).
    - apply lend_lics_key in Hk as (z & -> & Hz). exact (dvl_l_neg z Hz).
    - apply flend_slots_key in Hk as (z & -> & Hz). exact (fvl_k_neg z Hz).
    - apply flend_lics_key in Hk as (z & -> & Hz). exact (fvl_l_neg z Hz).
  Qed.

  Lemma lend_reg_dummy_disj (γc γv γfc γfv : gname) (nib : nat) :
    lend_reg_all γc γv γfc γfv nib ##ₘ dummy_reg nib.
  Proof.
    apply map_disjoint_spec. intros k x y H1 H2.
    apply dummy_reg_key in H2.
    pose proof (lend_reg_all_neg γc γv γfc γfv nib k x H1). lia.
  Qed.

  Lemma lend_reg_cov (γc γv γfc γfv : gname) (nib : nat) (z : Z) :
    (0 <= z < 16 * Z.of_nat nib)%Z ->
    is_Some ((lend_reg_all γc γv γfc γfv nib ∪ dummy_reg nib) !! z).
  Proof.
    intros Hz. destruct (dummy_reg_cov nib z Hz) as [v Hv].
    exists v. apply lookup_union_Some_raw. right. split; [| exact Hv].
    destruct (lend_reg_all γc γv γfc γfv nib !! z) as [u|] eqn:Hl;
      [exfalso | reflexivity].
    pose proof (lend_reg_all_neg γc γv γfc γfv nib z u Hl). lia.
  Qed.

  Lemma lend_slots_out (γc γv : gname) (nib : nat) :
    ([∗ map] k ↦ v ∈ lend_slots γc γv nib, k ↪[icfg_reg] v)
    ⊢ [∗ set] z ∈ region_inums nib, dvl_slot z (DfracOwn 1) (γc, γv).
  Proof.
    rewrite /lend_slots big_sepM_gset_to_gmap.
    rewrite (big_opS_set_map dvl_k (region_inums nib)
               (fun k => (k ↪[icfg_reg] ((γc, γv) : gname * gname))%I)
               dvl_k_inj).
    done.
  Qed.

  Lemma lend_lics_out (nib : nat) :
    ([∗ map] k ↦ v ∈ lend_lics nib, k ↪[icfg_reg] v)
    ⊢ [∗ set] z ∈ region_inums nib, dv_lic z.
  Proof.
    rewrite /lend_lics big_sepM_gset_to_gmap.
    rewrite (big_opS_set_map dvl_l (region_inums nib)
               (fun k => (k ↪[icfg_reg]
                            ((1%positive, 1%positive) : gname * gname))%I)
               dvl_l_inj).
    iIntros "H". iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite /dv_lic.
    iExists ((1%positive, 1%positive) : gname * gname). iExact "H".
  Qed.

  Lemma flend_slots_out (γc γv : gname) (nib : nat) :
    ([∗ map] k ↦ v ∈ flend_slots γc γv nib, k ↪[icfg_reg] v)
    ⊢ [∗ set] z ∈ region_inums nib, fvl_slot z (DfracOwn 1) (γc, γv).
  Proof.
    rewrite /flend_slots big_sepM_gset_to_gmap.
    rewrite (big_opS_set_map fvl_k (region_inums nib)
               (fun k => (k ↪[icfg_reg] ((γc, γv) : gname * gname))%I)
               fvl_k_inj).
    done.
  Qed.

  Lemma flend_lics_out (nib : nat) :
    ([∗ map] k ↦ v ∈ flend_lics nib, k ↪[icfg_reg] v)
    ⊢ [∗ set] z ∈ region_inums nib, fv_lic z.
  Proof.
    rewrite /flend_lics big_sepM_gset_to_gmap.
    rewrite (big_opS_set_map fvl_l (region_inums nib)
               (fun k => (k ↪[icfg_reg]
                            ((1%positive, 1%positive) : gname * gname))%I)
               fvl_l_inj).
    iIntros "H". iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite /fv_lic.
    iExists ((1%positive, 1%positive) : gname * gname). iExact "H".
  Qed.

  (* THE FREE INUMS' ABSTRACT VALUE, AS BOOT HANDS IT OVER (durable-disk
     C-3c).  [emp] at a live inum -- there the fragment rides TIED inside the
     pool's allocated bundle ([ipool_shape_alloc]) -- and at a free one it is
     the fragment at the node the record determines, which is exactly what
     [InodeRegion.ireg_top_park] parks. *)
  Definition ireg_top_boot (γfs : fs_names) (D : Z -> dinode) (z : Z)
    : iProp Σ :=
    (if decide (bv_unsigned (di_type (D z)) = 0)
     then top_frag (fs_gamma_L γfs) z (free_node (D z))
     else emp)%I.

  Lemma ireg_top_boot_live (γfs : fs_names) (D : Z -> dinode) (z : Z) :
    bv_unsigned (di_type (D z)) <> 0 -> ⊢ ireg_top_boot γfs D z.
  Proof.
    intros Hnz. rewrite /ireg_top_boot decide_False; [| exact Hnz]. done.
  Qed.

  Lemma ireg_alloc (E : coPset) (γfs : fs_names) (inodestart : Z) (nib : nat)
      (home : gset Z) (bss : nat -> list (bv 8)) (W N : Z -> nat)
      (D : Z -> dinode) :
    16 * Z.of_nat nib <= 2 ^ 32 ->
    (* THE REGION'S BLOCKS ARE HOME BLOCKS (durable-disk 1c-flip step 3):
       [ireg_blk] holds each one's EXCLUSIVE byte run now, so the region's
       readers cross into the byte view and [InodeRegion.ireg_bytes] is
       what carries the crossing.  No coverage premise: holding the run IS
       being a home block ([FsBlocks.fsblock_home]). *)
    (* N-4 PHASE B: the lend column family is indexed at [icfg_nib] (see
       [InodeRegion.ireg_lends] for why), and boot is the one place that has
       to know the two agree.  The caller is [FsCfgBoot], which calls this
       at [icfg_nib] literally. *)
    nib = icfg_nib ->
    (forall bi : nat, (bi < nib)%nat -> length (bss bi) = 1024%nat) ->
    (forall dss : list (list dinode),
       length dss = nib -> Forall diblk_wf dss ->
       (forall bi : nat, (bi < nib)%nat -> bss bi = diblk_bytes (dss !!! bi)) ->
       image_free_nlink dss nib /\ image_nlink_short dss nib /\
       image_link_le W dss nib
       /\ image_dir_wl0 W dss nib /\ image_ty_ok dss nib
       /\ image_nlink_at N dss nib
       (* durable-disk C-3c, LAST so no existing destructuring moves *)
       /\ image_bare dss nib /\ image_rec_at D dss nib) ->
    (* THE LEDGER AT BOOT, AT THE WIDENED [w] (V1's count-fact carrier;
       V4+V5's fused widening): the image's authorities are ALL-PLAIN,
       [wdu = wdt = 0] and [p = None] at every inum, so (T1), (T1') and
       [ireg_par_ok] are all vacuous-or-zero at every slot and the image
       owes NOTHING new -- (T1') in particular is not even an image fact
       ([wl = 0] closes it before the type is asked).  A d-flavoured
       fragment is only ever minted by a running kernel at create's mkdir
       arm; mkfs's records are handed to the region unflavoured.  The
       ROOT's own [nlink = 1] is nobody's business here any more: the
       region's keep-alive token ([InodeRegion.ireg_keep]) carries it, and
       the boot hands that token over with the rest of the pile. *)
    ([∗ set] z ∈ region_inums nib,
       link_auth z (W z) 0 0 0 None 0 None (Some (Excl FrzOff)) 0) -∗
    (* THE LINK RA's PER-INUM AUTHORITY AND ITS PILE OF TOKENS
       (durable-disk 2b-inode-4), one per inum at the record's own [nlink].
       A PREMISE for the ledger's reason: the family is
       [FsState.fs_boot_alloc_full]'s and only its [own_alloc] can hand it
       over.  Nothing is outstanding at boot, so the family's validity is
       free and no image sweep is spent on it. *)
    ([∗ set] z ∈ region_inums nib, ireg_lnk_at γfs z (N z)) -∗
    (* THE COUNT COUPLING's REGION HALVES (iclaim-ledger.md §2.2), one per
       inum and all at ZERO -- boot caches no inode.  A PREMISE for the
       ledger's own reason: the gname is the ambient class's, so only the
       [own_alloc] that minted it can hand the halves over
       ([IcacheRef.icfg_alloc] + [IcacheRef.icnt_split]). *)
    ([∗ set] z ∈ region_inums nib, icnt_half z 0) -∗
    (* THE FREEZE RECEIPTS (iclaim-ledger.md §3.14 as built), one exclusive
       unit per inum: boot freezes nothing, so every slot's receipt clause
       is on its [frzown] arm and the region parks the whole family.  A
       PREMISE for the count halves' reason -- the gname is the ambient
       class's ([IcacheRef.icfg_alloc] + [IcacheRef.frzo_boot_split]). *)
    ([∗ set] z ∈ region_inums nib, frzown z) -∗
    (* THE FREEZE MIRROR's REGION HALVES (iclaim-ledger.md §3.16 / A⁗), one
       per inum and all DOWN -- boot's f column is [FrzOff] everywhere, so
       [ireg_frzm_ok] holds at [false] at every slot.  A PREMISE for the
       receipts' reason ([IcacheRef.icfg_alloc] + [IcacheRef.frzm_boot_split];
       the OTHER half of each goes to the free pool's bundle). *)
    ([∗ set] z ∈ region_inums nib, frzm_h z false) -∗
    (* THE OBSERVATION COUNTERS (fs-log.md §G.17), one per inum and all at
       zero: nobody has ever observed a nonzero nlink, which is exactly the
       [⌜v = 0⌝] disjunct that carries the receipt over the mkfs image's
       free inodes.  A PREMISE for [icfg_iref]'s reason -- the gnames are
       the ambient class's, so only the [own_alloc] that minted them can
       hand them over ([IcacheRef.icfg_alloc]). *)
    ([∗ set] z ∈ region_inums nib, mono_nat_auth_own (icfg_iep z) 1 0) -∗
    (* THE FREE INUMS' ABSTRACT VALUE (durable-disk C-3c): one [top_frag] per
       FREE inum, at the node its record determines, parked region-side in
       [InodeRegion.ireg_top_park].  It used to go to the pool's marker arm
       UNTIED, which is what left the commit's collection unable to build a
       bundle at a free inum (FsCollect's supplier (D)). *)
    ([∗ set] z ∈ region_inums nib, ireg_top_boot γfs D z) -∗
    ([∗ list] bi ∈ seq 0 nib,
       fsblock (fs_bytes γfs) (inodestart + Z.of_nat bi) (bss bi)) -∗
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) home -∗
    (* THE ERA'S TOP-MAP AUTHORITY, AS ITS INVARIANT (durable-disk
       2b-inode-3).  [ireg_inv] carries it, so this lemma has to be handed
       one; the caller ([FsCfgBoot.fs_cfg_alloc]) allocates it with
       [InodeRegion.ftop_alloc] off the map [FsState.fs_boot_alloc] just
       minted.  Persistent, so it rides through untouched. *)
    ftop_inv γfs -∗
    (* the boot-shelter token rides through, from [icfg_alloc] to fsinit
       (fs-fragments.md §7.12) -- carried, never consumed here *)
    ireg_boot -∗
    (* OPTION A: the escrow registry's EMPTY auth ([icfg_alloc]'s new hand-out);
       populated here over every inum and parked inside [ireg_body]. *)
    ghost_map_auth icfg_reg 1 (∅ : gmap Z (gname * gname))
    ={E}=∗ ∃ (γi : gname) (dss : list (list dinode)),
      ⌜length dss = nib⌝ ∗ ⌜Forall diblk_wf dss⌝ ∗
      ⌜forall bi : nat, (bi < nib)%nat -> bss bi = diblk_bytes (dss !!! bi)⌝ ∗
      ireg_inv γi γfs inodestart nib ∗
      ireg_boot ∗
      (* N-4 PHASE B: one MINT LICENCE per inum, out with the caller.  The
         column itself stays inside the region, in its NONE state.
         N-5.2A: and the fview column's licence beside it, the same way and
         for the same consumer ([FsCfgBoot]'s stocking mint). *)
      ([∗ set] z ∈ region_inums nib, dv_lic z) ∗
      ([∗ set] z ∈ region_inums nib, fv_lic z) ∗
      ([∗ set] z ∈ region_inums nib,
         ireg_out γi (mword_of_int z : mword 32) (image_dinode dss z)).
  Proof.
    intros Hnib Hnibc Hlen Himg.
    destruct (image_decode nib bss Hlen) as (dss & Hl & Hwf & He).
    destruct (Himg dss Hl Hwf He)
      as (Hl3 & Hl4 & Hl1 & Hdw0 & Hl5 & Hlnkat & Hbare & Hrecat).
    iIntros "Hlk Hlnks Hcnts Hrcpts Hmirs Hepa Htops Hblks #Hbinv #Hftopi Hboot Hrauth".
    (* OPTION A: bulk-register every inum with a dummy escrow gname pair, then
       wrap as [ireg_registry] for the region body. *)
    iMod (ghost_map_insert_big (dummy_reg nib) with "Hrauth") as "[Hrauth Hfulls]".
    { apply map_disjoint_empty_r. }
    rewrite right_id_L.
    (* N-4 PHASE B (E1-region): stock the lend column, NONE at every inum.
       Two cell families at fresh gnames, two key families in the registry
       auth this lemma already holds -- no boot map and no [icfg] field. *)
    iMod (own_alloc (dview_boot_map (region_inums nib))) as (γlc) "Hlc";
      [apply dview_boot_map_valid |].
    iMod (own_alloc (dview_boot_map (region_inums nib))) as (γlv) "Hlv";
      [apply dview_boot_map_valid |].
    (* N-5.2A: the fview column's two cell families, at [fview_boot_map] and
       at two more fresh gnames.  Four [own_alloc]s and four key families in
       all, still no boot map widened and no [icfg] field added. *)
    iMod (own_alloc (fview_boot_map (region_inums nib))) as (γfc) "Hfc";
      [apply fview_boot_map_valid |].
    iMod (own_alloc (fview_boot_map (region_inums nib))) as (γfv) "Hfv";
      [apply fview_boot_map_valid |].
    iMod (ghost_map_insert_big (lend_reg_all γlc γlv γfc γfv nib) with "Hrauth")
      as "[Hrauth Hlend0]".
    { apply lend_reg_dummy_disj. }
    iDestruct (big_sepM_union with "Hlend0") as "[Hlend0 Hflend0]";
      [apply lend_flend_disj |].
    iDestruct (big_sepM_union with "Hlend0") as "[Hslots0 Hlics0]";
      [apply lend_slots_lics_disj |].
    iDestruct (big_sepM_union with "Hflend0") as "[Hfslots0 Hflics0]";
      [apply flend_slots_lics_disj |].
    iDestruct (lend_slots_out γlc γlv nib with "Hslots0") as "Hslots0".
    iDestruct (lend_lics_out nib with "Hlics0") as "Hlics".
    iDestruct (flend_slots_out γfc γfv nib with "Hfslots0") as "Hfslots0".
    iDestruct (flend_lics_out nib with "Hflics0") as "Hflics".
    iDestruct (dvl_boot_split γlc (region_inums nib) with "Hlc") as "Hlc".
    iDestruct (dvl_boot_split γlv (region_inums nib) with "Hlv") as "Hlv".
    iDestruct (fvl_boot_split γfc (region_inums nib) with "Hfc") as "Hfc".
    iDestruct (fvl_boot_split γfv (region_inums nib) with "Hfv") as "Hfv".
    iAssert ([∗ set] z ∈ region_inums nib, dv_lcol z)%I
      with "[Hslots0 Hlc Hlv]" as "Hcols".
    { iDestruct (big_sepS_sep_2 with "Hslots0 Hlc") as "H".
      iDestruct (big_sepS_sep_2 with "H Hlv") as "H".
      iApply (big_sepS_mono with "H"). intros z _.
      iIntros "[[Hsl Hc] Hv]".
      iApply (dv_lcol_boot z γlc γlv with "Hsl Hc Hv"). }
    iAssert ([∗ set] z ∈ region_inums nib, fv_lcol z)%I
      with "[Hfslots0 Hfc Hfv]" as "Hfcols".
    { iDestruct (big_sepS_sep_2 with "Hfslots0 Hfc") as "H".
      iDestruct (big_sepS_sep_2 with "H Hfv") as "H".
      iApply (big_sepS_mono with "H"). intros z _.
      iIntros "[[Hsl Hc] Hv]".
      iApply (fv_lcol_boot z γfc γfv with "Hsl Hc Hv"). }
    iDestruct (ireg_registry_from_map
                 (lend_reg_all γlc γlv γfc γfv nib ∪ dummy_reg nib) nib
                 (lend_reg_cov γlc γlv γfc γfv nib) with "Hrauth [Hcols Hfcols]")
      as "Hreg".
    { rewrite /ireg_lends -Hnibc -region_set_to_seq.
      iDestruct (big_sepS_sep_2 with "Hcols Hfcols") as "H".
      iApply (big_sepS_mono with "H"). intros z _.
      iIntros "[Hd Hf]". rewrite /ireg_lcols. iFrame. }
    (* OPTION A (walk reg-fold): the reg_full fragments no longer form a
       standalone big-op; distribute them into the per-inum slots below. *)
    iEval (rewrite /dummy_reg big_sepM_gset_to_gmap) in "Hfulls".
    iMod (ghost_map_alloc (ireg_M0 dss nib ∪ ireg_MK nib)) as (γi) "[Ha Hels]".
    iDestruct (big_sepM_union with "Hels") as "[Hels Hmks]";
      [apply ireg_M0_MK_disj |].
    iDestruct (ireg_M0_big (fun z dn => (z ↪[γi] dn)%I) dss nib with "Hels")
      as "Hels".
    iDestruct (imark_of_marks γi nib with "Hmks") as "Hmks".
    iDestruct (big_sepS_sep_2 with "Hels Hmks") as "Hall".
    iDestruct (big_sepS_sep_2 with "Hall Hlk") as "Hall".
    iAssert (|==> [∗ set] z ∈ region_inums nib,
                    ireg_ep z (image_dinode dss z))%I with "[Hepa]" as ">Hep".
    { iApply big_sepS_bupd. iApply (big_sepS_mono with "Hepa"). intros z Hz.
      iIntros "Ha". iApply (ireg_ep_intro z (image_dinode dss z) with "Ha"). }
    iDestruct (big_sepS_sep_2 with "Hall Hep") as "Hall".
    iDestruct (big_sepS_sep_2 with "Hall Hfulls") as "Hall".
    (* the count coupling's region halves ride in beside the rest (§2.2) *)
    iDestruct (big_sepS_sep_2 with "Hall Hcnts") as "Hall".
    (* ...and the freeze receipts (§3.14 as built) *)
    iDestruct (big_sepS_sep_2 with "Hall Hrcpts") as "Hall".
    iDestruct (big_sepS_sep_2 with "Hall Hmirs") as "Hall".
    (* ...and the link RA's per-inum pile (durable-disk 2b-inode-4) *)
    iDestruct (big_sepS_sep_2 with "Hall Hlnks") as "Hall".
    (* ...and the FREE inums' abstract value (durable-disk C-3c) *)
    iDestruct (big_sepS_sep_2 with "Hall Htops") as "Hall".
    (* per inum: one of the two ghost entries stays in the region's arm and
       the other one is the payout; the ledger authority stays with the
       slot on BOTH arms (design §20.2) *)
    iAssert ([∗ set] z ∈ region_inums nib,
               (ireg_slot γfs γi z (image_dinode dss z) ∗
                ireg_out γi (mword_of_int z : mword 32) (image_dinode dss z)))%I
      with "[Hall]" as "Hall".
    { iApply (big_sepS_mono with "Hall"). intros z Hz.
      iIntros "[[[[[[[[[Hfrag Hmk] Hla] Hep] Hrf] Hcnt] Hrcpt] Hmir] Hlnk] Htop]".
      iEval (rewrite /ireg_top_boot (Hrecat z Hz)) in "Htop".
      iDestruct (ireg_lnk_of_at γfs z (N z) (image_dinode dss z)
                   (Hlnkat z Hz) with "Hlnk") as "Hlnk".
      assert (Hok : ireg_link_ok (image_dinode dss z) (W z + 0 + 0)).
      { pose proof (Hl1 z Hz).
        split_and!;
          [lia | exact (Hl3 z Hz) | exact (Hl4 z Hz) | exact (Hl5 z Hz)]. }
      (* ...and the DIRECTORY clause, which stage A got for free at [wl = 0] *)
      assert (Hwl0 : ireg_dir_wl0 (image_dinode dss z) (W z))
        by exact (Hdw0 z Hz).
      rewrite /ireg_out /dinode_at (region_inum_faithful nib z Hnib Hz).
      case_decide as Hty.
      - iSplitR "Hmk"; [| iExact "Hmk"].
        iDestruct (ireg_rcol_intro z (W z) 0 0 0 None 0 None (Some (Excl FrzOff))
                     0%nat 0%nat (image_dinode dss z)
                     (ireg_ref_ok_zero 0%nat None (image_dinode dss z))
                     with "Hla") as "Hla".
        iApply (ireg_slot_intro γfs γi z (image_dinode dss z) (W z) 0 0 0 None 0 None
                  (Some (Excl FrzOff)) 0%nat
                  Hok (ireg_dir_ok_zero _) Hwl0
                  ireg_par_ok_none (ireg_claim_ok_none _ _) I
                  with "Hla Hep Hlnk [] Hcnt [] [Hrcpt Hmir]").
        (* boot's ledger is all-[None], so the boot-shelter clause's LEFT
           disjunct is free (fs-fragments.md §7.12) *)
        { iLeft; iPureIntro; reflexivity. }
        (* ...and the FREEZE's clause is vacuous at the UNFROZEN column,
           which is boot's everywhere (iclaim-ledger.md §2.3 / §6'' G') *)
        { iApply ireg_fsh_off. }
        (* ...and the RECEIPT's clause is on its [frzown] arm, because boot
           freezes nothing (iclaim-ledger.md §3.14 as built) *)
        { iApply (ireg_frzc_off_intro z (Some (Excl FrzOff))
                    ltac:(reflexivity) with "Hrcpt Hmir"). }
        iLeft. iSplitR "Hrf";
          [iLeft; iSplitR; [iPureIntro; left; exact Hty |];
           iSplitL "Hfrag"; [iExact "Hfrag" |];
           (* [case_decide] on [ireg_out]'s own test has already resolved
              the park's -- it is the same decidable proposition *)
           iApply (ireg_top_park_free γfs z (image_dinode dss z)
                     (Hbare z Hz Hty) with "Htop")
          | iExists (1%positive : gname), (1%positive : gname); iExact "Hrf"].
      - iSplitR "Hfrag"; [| iExact "Hfrag"].
        iDestruct (ireg_rcol_intro z (W z) 0 0 0 None 0 None (Some (Excl FrzOff))
                     0%nat 0%nat (image_dinode dss z)
                     (ireg_ref_ok_zero 0%nat None (image_dinode dss z))
                     with "Hla") as "Hla".
        iApply (ireg_slot_intro γfs γi z (image_dinode dss z) (W z) 0 0 0 None 0 None
                  (Some (Excl FrzOff)) 0%nat
                  Hok (ireg_dir_ok_zero _) Hwl0
                  ireg_par_ok_none (ireg_claim_ok_none _ _) I
                  with "Hla Hep Hlnk [] Hcnt [] [Hrcpt Hmir]").
        (* boot's ledger is all-[None], so the boot-shelter clause's LEFT
           disjunct is free (fs-fragments.md §7.12) *)
        { iLeft; iPureIntro; reflexivity. }
        (* ...and the FREEZE's clause is vacuous at the UNFROZEN column,
           which is boot's everywhere (iclaim-ledger.md §2.3 / §6'' G') *)
        { iApply ireg_fsh_off. }
        (* ...and the RECEIPT's clause is on its [frzown] arm, because boot
           freezes nothing (iclaim-ledger.md §3.14 as built) *)
        { iApply (ireg_frzc_off_intro z (Some (Excl FrzOff))
                    ltac:(reflexivity) with "Hrcpt Hmir"). }
        iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hty | reflexivity] | iExact "Hmk"] | iExists (1%positive : gname), (1%positive : gname); iExact "Hrf"]. }
    rewrite big_sepS_sep.
    iDestruct "Hall" as "[Hslots Hout]".
    iDestruct (ireg_slots_of_set γfs γi dss nib with "Hslots") as "Hslots".
    iAssert (ireg_body γi γfs inodestart nib)%I
      with "[Ha Hblks Hslots Hreg]" as "Hbody".
    { iExists (ireg_M0 dss nib ∪ ireg_MK nib). iFrame "Ha Hreg".
      iDestruct (big_sepL_sep_2 with "Hblks Hslots") as "H".
      iApply (big_sepL_mono with "H").
      intros idx bi Hbi. apply lookup_seq in Hbi as [-> Hidx].
      iIntros "[Hb Hsl]". rewrite /ireg_blk. iExists (dss !!! idx).
      assert (Hwfb : diblk_wf (dss !!! idx)).
      { apply (Forall_lookup_1 _ dss idx); [exact Hwf |].
        apply list_lookup_lookup_total_lt. lia. }
      iSplitR; [iPureIntro; exact Hwfb |].
      iSplitR.
      { iPureIntro. intros i Hi.
        apply lookup_union_Some_l.
        rewrite (ireg_M0_lookup dss nib _); last first.
        { apply region_inums_spec. lia. }
        rewrite (image_dinode_slot dss idx i Hi) //. }
      (* the image block's bytes, named as the decoded list's encoding --
         in the HYPOTHESIS now, since the goal no longer spells the block *)
      iEval (rewrite (He idx Hidx)) in "Hb".
      (* durable-disk 2b-inode-1: the image block's byte run is handed to the
         region as its SIXTEEN RECORD RUNS ([InodeRegion.ireg_recs_of_blk],
         i.e. [FsStateInode.rec_owned_at_diblk]'s split), which is the shape
         [ireg_blk] parks now. *)
      iSplitL "Hb";
        [iApply (ireg_recs_of_blk γfs inodestart idx (dss !!! idx) Hwfb
                   with "Hb")
        | iExact "Hsl"]. }
    iMod (inv_alloc iregN E (ireg_body γi γfs inodestart nib) with "[Hbody]")
      as "#Hinv"; [by iNext |].
    iAssert (ireg_inv γi γfs inodestart nib) as "#Hrinv".
    { rewrite /ireg_inv. iFrame "Hinv Hftopi". rewrite /fs_bytes_any.
      iExists home. iFrame "Hbinv". }
    iModIntro. iExists γi, dss.
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [iPureIntro; exact He |].
    iFrame "Hrinv Hboot Hlics Hflics". iExact "Hout".
  Qed.

End IcacheBootRegion.

(* ===================================================================== *)
(*  3.  STOCKING THE POOL (§13.3)                                         *)
(* ===================================================================== *)

Section IcacheBootPool.
  Context `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ}.
  Context `{GEN : GenId}.

  (* THE POOL'S KEYS ARE THE [mword] ROUND TRIP, and the ledger's are plain
     [Z]: [ipool] indexes [ipool_shape] at [mword_of_int z], so its [icnt] and
     [ifreeze] conjuncts sit at [bv_unsigned (mword_of_int z)], while
     [IcacheRef.icnt_boot_split] / [IcacheRef.link_boot_split] hand a boot
     client its big-ops at [z].  Over [region_inums] the two agree
     ([region_inum_faithful]) and this is the bridge -- stated once, over an
     arbitrary [Phi], so the two ledger columns and any future third share
     it. *)
  Lemma region_key_shift (nib : nat) (Phi : Z -> iProp Σ) :
    16 * Z.of_nat nib <= 2 ^ 32 ->
    ([∗ set] z ∈ region_inums nib, Phi z) -∗
    ([∗ set] z ∈ region_inums nib, Phi (bv_unsigned (mword_of_int z : mword 32))).
  Proof.
    iIntros (Hnib) "H". iApply (big_sepS_mono with "H"). intros z Hz.
    rewrite (region_inum_faithful nib z Hnib Hz) //.
  Qed.

  (* THE FREE ARM IS A BARE MARKER since §16.4 -- no record, no type premise.

     WHAT INCREMENT IIIa ADDS: the two UNCACHED LEDGER RESOURCES the pool now
     carries (iclaim-ledger.md §2.2/§2.3).  Both are PREMISES, and for
     [ireg_alloc]'s reason spelled at its own count-halves premise: the gnames
     are the ambient class's, so only the [own_alloc] that minted them can
     hand them over -- [IcacheRef.icnt_boot_split] for the count half (from
     [icfg_alloc]'s [CM := icnt_boot_map (region_inums nib)]) and
     [IcacheRef.link_boot_split] for the freeze token (from
     [LM := link_boot_map (region_inums nib)], whose auth half is the very
     [link_auth z .. (Some (Excl FrzOff))] big-op [ireg_alloc] already takes).
     Boot's count is the literal 0 and boot's phase is [FrzOff]: no inode is
     cached and no inum is in transition before userspace exists. *)
  Lemma ipool_shape_free (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) :
    icnt_half (bv_unsigned inum) 0%nat -∗
    (* ...and the FREEZE MIRROR's uncached half (iclaim-ledger.md §3.16), a
       PREMISE for the count half's reason verbatim: it comes out of
       [IcacheRef.frzm_boot_split] at [BM := frzm_boot_map (region_inums nib)],
       and boot's bit is DOWN everywhere because boot's phase is [FrzOff]. *)
    frzm_h (bv_unsigned inum) false -∗
    ifreeze_off (bv_unsigned inum) -∗
    (* ...and the CONTENTS HOLD, UNTIED (namei-pinned-lookup.md §9 W2): the
       marker arm carries no bytes, so boot's own [∅] is as good a value as
       any and the first fill sets it. *)
    (∃ e, dv_ride (bv_unsigned inum) e) -∗
    (∃ b, fv_ride (bv_unsigned inum) b) -∗
    (* THE ERA'S ABSTRACT VALUE IS NOT HERE (durable-disk C-3c): a FREE
       inum's [FsState.top_frag] parks WITH its record, region-side, in
       [InodeRegion.ireg_top_park] -- see [ireg_alloc]'s own premise. *)
    (* durable-disk B''-esc: boot stocks the pool with ORDINARY rows only --
       no inum is in transition before userspace exists -- so this builds
       [ipool_ord], which is what the pool INVARIANT holds. *)
    imark γi (bv_unsigned inum) -∗ ipool_ord γfs γi cov logstart inum.
  Proof.
    iIntros "Hcnt Hmir Hoff Hdv Hfv Hmk".
    rewrite /ipool_ord /ipool_shape_np.
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iSplitR "Hoff"; [| iExact "Hoff"].
    iRight. iSplitL "Hmk"; [iExact "Hmk" |].
    iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"].
  Qed.

  (* THE SECOND PREMISE IS §15(a)'S DIRECTORY-WF CLAUSE, and it joins the
     image-wf family for exactly the reason [inode_ok] did: it is a fact
     about the IMAGE ON DISK, so the boot client owes it and this lemma
     cannot manufacture it.  mkfs images satisfy it. *)

  (* WHAT V2's COUNT CLAUSE ADDS HERE, AND WHY IT IS NOT A NEW PREMISE.
     [DirLinks.dir_links] now carries [DirView.dlc_bound] over an
     existential flavour map, so the client's [dir_links] bundle below is
     one conjunct stronger than it was.  It costs the client ONE
     COMPUTATIONAL FACT about the image and nothing else -- every image
     directory has [nlink <= 1] -- because the region's boot authorities
     are ALL-PLAIN ([ireg_alloc] takes [link_auth z 0 0 0 0 None 0 None]), so
     the stock is built at [F = fun _ => false], where the clause's
     right-hand side is [1 + 0].  That is true of mkfs: it writes
     [nlink = 1] into the root and creates no subdirectory, so no image
     directory is ever named by a [".."] it did not write itself.
     [DirLinks.dir_links_of_plain] is the constructor
     ([DirView.dlc_bound_le1] discharges the clause from the fact), and it
     is why no signature here moves: the obligation lands inside a resource
     the client was already producing, exactly as (L3)/(L4) landed inside
     [ireg_alloc]'s ∀-over-decodings slot. *)
  Lemma ipool_shape_alloc (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    inode_ok cov logstart dn bm data ->
    (* the three record-only facts [inode_ok] does not carry
       (durable-disk 2b-inode-3): the type enumeration, the nlink bound and
       a directory's 16-divisible size.  At the image they are
       [FsImg.fio_type], [FsImg.fs_region_nlink_short] and [FsImg.fdo_gran];
       [FsStateEra.inode_local_of_ok_rec] takes them and derives the whole
       of [FsStateInode.inode_local]. *)
    inode_rec_local dn ->
    dir_ok icfg_nib dn data ->
    dir_dots_ix (bv_unsigned inum) dn data ->
    dir_orphan_clean dn data ->
    dir_uniq dn data ->
    icnt_half (bv_unsigned inum) 0%nat -∗
    frzm_h (bv_unsigned inum) false -∗
    ifreeze_off (bv_unsigned inum) -∗
    dlinks γfs (bv_unsigned inum) dn bm data -∗
    dinode_at γi inum dn -∗ ind_res γfs bm -∗ inode_blocks γfs bm data -∗
    (* ...AND THE ERA'S ABSTRACT VALUE, TIED to this arm's own node
       (durable-disk 2b-inode-3).  The four resources above are what
       [FsStateEra.inode_owned_era] is assembled OUT of, and this is its
       fourth piece. *)
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data) -∗
    (* ...and the CONTENTS HOLD, TIED to the image's own record and bytes
       (namei-pinned-lookup.md §9 W2/W3): the boot client sets the value with
       a free [dv_set] before it gets here, so nothing in this file has to
       compute it. *)
    dv_ride (bv_unsigned inum) (dv_of dn data) -∗
    (* ...and its PER-FILE twin (N-5.2A), beside it and for the same reason *)
    fv_ride (bv_unsigned inum) (fv_of dn data) -∗
    ipool_ord γfs γi cov logstart inum.
  Proof.
    iIntros (Hok Hrl Hdok Hddix Hdoc Hduq)
            "Hcnt Hmir Hoff Hdlk Hdn Hind Hblk Htop Hdv Hfv".
    pose proof (node_shape_ok_of_inode_ok cov logstart dn bm data Hok) as Hsh.
    pose proof (inode_local_of_ok_rec (bv_unsigned inum) cov logstart dn bm
                  data Hok Hrl Hduq Hddix) as Hloc.
    rewrite /ipool_ord /ipool_shape_np.
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitL "Hmir"; [iExact "Hmir" |].
    iSplitR "Hoff"; [| iExact "Hoff"]. iLeft.
    rewrite /ipool_alloc.
    iExists dn, bm, data.
    iSplitR; [iPureIntro; exact Hok |].
    iSplitR; [iPureIntro; exact Hdok |].
    iSplitR; [iPureIntro; exact Hddix |].
    iSplitR; [iPureIntro; exact Hdoc |].
    iSplitR; [iPureIntro; exact Hduq |].
    iSplitL "Hdlk"; [iExact "Hdlk" |].
    iSplitR "Hdv Hfv".
    { iApply (inode_owned_era_era_node_of γfs γi inum dn bm data Hsh Hloc
                with "Hdn Hind Hblk Htop"). }
    iFrame "Hdv Hfv".
  Qed.

  (* the stocked rows are a [∗ set], so they split and rejoin along any
     subset *)
  Lemma ipool_rows_split (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (R A : gset Z) :
    A ⊆ R ->
    ipool_rows γfs γi cov logstart A ∗ ipool_rows γfs γi cov logstart (R ∖ A)
      ⊢ ipool_rows γfs γi cov logstart R.
  Proof.
    intros Hsub. rewrite /ipool_rows -big_sepS_union; [| set_solver].
    rewrite -(union_difference_L A R Hsub) //.
  Qed.

  (* THE STOCKING, in the shape a boot client can actually supply: the
     ALLOCATED inums bring their bundles, everything else is free.  Both
     halves are premises -- see the file header for why the first one cannot
     be manufactured here and must not be axiomatized. *)
  Lemma ipool_alloc (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (R A : gset Z) :
    A ⊆ R ->
    (* the uncached ledger pair, one per POOLED inum and over the WHOLE of
       [R] -- both arms of the split need it, the allocated one no less than
       the free one, because §2.2's halves are about cachedness and not about
       allocatedness.  Keyed the way [ipool] keys its shapes; see
       [region_key_shift] for the bridge from the boot splits' plain [z]. *)
    ([∗ set] z ∈ R, icnt_half (bv_unsigned (mword_of_int z : mword 32)) 0%nat) -∗
    ([∗ set] z ∈ R, frzm_h (bv_unsigned (mword_of_int z : mword 32)) false) -∗
    ([∗ set] z ∈ R, ifreeze_off (bv_unsigned (mword_of_int z : mword 32))) -∗
    ([∗ set] z ∈ A,
       ∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)),
         ⌜inode_ok cov logstart dn bm data⌝ ∗
         ⌜inode_rec_local dn⌝ ∗
         ⌜dir_ok icfg_nib dn data⌝ ∗
         ⌜dir_dots_ix (bv_unsigned (mword_of_int z : mword 32)) dn data⌝ ∗
         ⌜dir_orphan_clean dn data⌝ ∗
         ⌜dir_uniq dn data⌝ ∗
         dlinks γfs (bv_unsigned (mword_of_int z : mword 32)) dn bm data ∗
         dinode_at γi (mword_of_int z : mword 32) dn ∗
         ind_res γfs bm ∗ inode_blocks γfs bm data ∗
         (* ...and the era's abstract value, TIED to this bundle's own node
            for the contents holds' reason verbatim (durable-disk
            2b-inode-3) *)
         top_frag (fs_gamma_L γfs) (bv_unsigned (mword_of_int z : mword 32))
                  (era_node dn bm data) ∗
         (* the CONTENTS HOLD rides INSIDE the allocated bundle, because the
            value it is tied to is this bundle's own [dn]/[data] and nothing
            outside the existential can name them (§9 W2). *)
         dv_ride (bv_unsigned (mword_of_int z : mword 32)) (dv_of dn data) ∗
         fv_ride (bv_unsigned (mword_of_int z : mword 32)) (fv_of dn data)) -∗
    ([∗ set] z ∈ R ∖ A,
       imark γi (bv_unsigned (mword_of_int z : mword 32))) -∗
    (* ...and the FREE inums' holds, untied and therefore outside any
       existential -- one big-op per ghost (N-5.2A) *)
    ([∗ set] z ∈ R ∖ A,
       ∃ e, dv_ride (bv_unsigned (mword_of_int z : mword 32)) e) -∗
    ([∗ set] z ∈ R ∖ A,
       ∃ b, fv_ride (bv_unsigned (mword_of_int z : mword 32)) b) -∗
    ipool_rows γfs γi cov logstart R.
  Proof.
    iIntros (Hsub) "Hcnts Hmirs Hoffs Ha Hf Hdvf Hfvf".
    (* the ledger pair splits along the same subset the pool does *)
    rewrite (union_difference_L A R Hsub) !big_sepS_union; [| set_solver ..].
    iDestruct "Hcnts" as "[HcA HcF]". iDestruct "Hoffs" as "[HoA HoF]".
    iDestruct "Hmirs" as "[HmA HmF]".
    rewrite -(union_difference_L A R Hsub).
    iApply (ipool_rows_split γfs γi cov logstart R A Hsub).
    iSplitL "Ha HcA HmA HoA".
    - rewrite /ipool_rows.
      iDestruct (big_sepS_sep_2 with "HcA HmA") as "Hlg0".
      iDestruct (big_sepS_sep_2 with "Hlg0 HoA") as "Hlg".
      iDestruct (big_sepS_sep_2 with "Hlg Ha") as "Ha".
      iApply (big_sepS_mono with "Ha"). intros z _.
      iIntros "[[[Hcnt Hmir] Hoff] (%dn & %bm & %data & %Hok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq
                & Hdlk & Hdn & Hind & Hblk & Htop & Hdv & Hfv)]".
      iApply (ipool_shape_alloc _ _ _ _ _ dn bm data Hok Hrl Hdok Hddix Hdoc Hduq
                with "Hcnt Hmir Hoff Hdlk Hdn Hind Hblk Htop Hdv Hfv").
    - rewrite /ipool_rows.
      iDestruct (big_sepS_sep_2 with "HcF HmF") as "Hlg0".
      iDestruct (big_sepS_sep_2 with "Hlg0 HoF") as "Hlg".
      iDestruct (big_sepS_sep_2 with "Hlg Hdvf") as "Hlg".
      iDestruct (big_sepS_sep_2 with "Hlg Hfvf") as "Hlg".
      iDestruct (big_sepS_sep_2 with "Hlg Hf") as "Hf".
      iApply (big_sepS_mono with "Hf"). intros z _.
      iIntros "[[[[[Hcnt Hmir] Hoff] Hdv] Hfv] Hmk]".
      iApply (ipool_shape_free with "Hcnt Hmir Hoff Hdv Hfv Hmk").
  Qed.

  (* ...and the case that needs no image theory at all: an image whose inodes
     are ALL free.  This is what makes [ipool_alloc]'s first premise a real
     obligation rather than a vacuous one -- the shape is satisfiable, in one
     line, from [ireg_alloc]'s output alone.  Since §16.4 it is even cheaper:
     what the free inums hand over is the MARKER, and their records never
     leave the region at all. *)
  Lemma ipool_alloc_all_free (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (dss : list (list dinode)) (nib : nat) :
    16 * Z.of_nat nib <= 2 ^ 32 ->
    (forall z : Z, z ∈ region_inums nib ->
       bv_unsigned (di_type (image_dinode dss z)) = 0) ->
    (* the uncached ledger pair, exactly as [IcacheRef.icnt_boot_split] and
       [IcacheRef.link_boot_split] hand it over at [P := region_inums nib] --
       so an all-free image's pool is still stocked in one line from the boot
       maps, with no key arithmetic at the client (that is what the [nib]
       range hypothesis buys, via [region_key_shift]) *)
    ([∗ set] z ∈ region_inums nib, icnt_half z 0%nat) -∗
    ([∗ set] z ∈ region_inums nib, frzm_h z false) -∗
    ([∗ set] z ∈ region_inums nib, ifreeze_off z) -∗
    ([∗ set] z ∈ region_inums nib, dv_ride z ∅) -∗
    ([∗ set] z ∈ region_inums nib, fv_ride z []) -∗
    ([∗ set] z ∈ region_inums nib,
       ireg_out γi (mword_of_int z : mword 32) (image_dinode dss z)) -∗
    ipool_rows γfs γi cov logstart (region_inums nib).
  Proof.
    iIntros (Hnib H0) "Hcnts Hmirs Hoffs Hdvs Hfvs H". rewrite /ipool_rows.
    iDestruct (region_key_shift nib (fun z => icnt_half z 0%nat) Hnib
                with "Hcnts") as "Hcnts".
    iDestruct (region_key_shift nib (fun z => frzm_h z false) Hnib
                with "Hmirs") as "Hmirs".
    iDestruct (region_key_shift nib (fun z => ifreeze_off z) Hnib
                with "Hoffs") as "Hoffs".
    iDestruct (region_key_shift nib (fun z => dv_ride z ∅) Hnib
                with "Hdvs") as "Hdvs".
    iDestruct (region_key_shift nib (fun z => fv_ride z []) Hnib
                with "Hfvs") as "Hfvs".
    iDestruct (big_sepS_sep_2 with "Hcnts Hmirs") as "Hlg0".
    iDestruct (big_sepS_sep_2 with "Hlg0 Hoffs") as "Hlg1".
    iDestruct (big_sepS_sep_2 with "Hlg1 Hdvs") as "Hlg2".
    iDestruct (big_sepS_sep_2 with "Hlg2 Hfvs") as "Hlg3".
    iDestruct (big_sepS_sep_2 with "Hlg3 H") as "H".
    iApply (big_sepS_mono with "H"). intros z Hz.
    iIntros "[[[[[Hcnt Hmir] Hoff] Hdv] Hfv] Hout]".
    iApply (ipool_shape_free with "Hcnt Hmir Hoff [Hdv] [Hfv]");
      [by iExists ∅ | by iExists [] |].
    iApply (ireg_out_free_inv γi (mword_of_int z : mword 32)
              (image_dinode dss z) (H0 z Hz) with "Hout").
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
  Context `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ}.
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
     be collected into a function before any gname exists.

     THIS IS WHY [icache_boot_at] EXISTS AND WHY IT DOES NOT NEED THIS TO
     HAPPEN FIRST.  The collection has to precede the [ghost_var_alloc], and
     the cells are only readable at iinit's post -- so an era fupd that must
     mint [fsc_ic] long before that cannot run [ic_names_alloc] at the right
     values.  It does not have to: [ic_id] is a plain [ghost_var], a WHOLE
     one updates to anything ([ic_id_set] below), so the era mints the family
     blind and [icache_boot_at] runs THIS lemma on the cells it is handed and
     then WRITES what it read.  [fun_of_big] therefore stays here, inside the
     [_at] lemma, and never becomes the caller's problem
     (claude-notes/projects/fs-cfg-boot.md, scout verdict on [fsc_ic]). *)
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

  (* THE ENTRY SLEEPLOCK FAMILY is [IcacheEscrow.ic_sleeplocks], with its
     accessor [IcacheEscrow.ic_sleeplocks_lookup].  It is stated there
     rather than here even though this is where [icache_boot] PRODUCES it:
     [IcacheEscrow.v] is strictly lower (it already requires [SleepLock] and
     owns [ic_tok]), so putting the family there is what keeps every
     consumer off this file.  There is exactly one copy; do not restate it
     in a caller. *)

  (* ------------------------------------------------------------------ *)
  (*  THE BOOT STEP                                                      *)
  (* ------------------------------------------------------------------ *)

  (* ---- the two facts that let the NAMES be minted before the VALUES ---- *)

  (* [ic_id] is a plain [ghost_var] ([IcacheEscrow.v] §13.8), so a WHOLE one
     is not merely flippable ([ic_id_flip], which needs both halves) but
     writable outright.  [icache_boot_at] spends exactly this: it is handed
     the era fupd's blind family and re-tags each slot at the dev/inum words
     [fun_of_big] just read off that slot's cells. *)
  Local Lemma ic_id_set (cn : ic_names) (k : nat) (v : bool) (d n : mword 32)
      (v' : bool) (d' n' : mword 32) :
    ic_id cn k 1 v d n ==∗ ic_id cn k 1 v' d' n'.
  Proof.
    rewrite /ic_id. iIntros "H".
    iApply (ghost_var_update (v', d', n') with "H").
  Qed.

  (* ...and the forgetful direction, which is all a caller holding
     [ic_names_alloc]'s output needs in order to meet [icache_boot_at]'s
     value-blind premise.  Spent by [icache_boot] just below. *)
  Local Lemma ic_id_forget (cn : ic_names) (v : bool)
      (dvs : nat -> mword 32 * mword 32) :
    ([∗ list] k ∈ seq 0 NINODE, ic_id cn k 1 v (dvs k).1 (dvs k).2)
    ⊢ ([∗ list] k ∈ seq 0 NINODE,
         ∃ (v' : bool) (d' n' : mword 32), ic_id cn k 1 v' d' n').
  Proof.
    apply big_sepL_mono. intros idx k _. iIntros "H".
    iExists v, (dvs k).1, (dvs k).2. iExact "H".
  Qed.

  (* the dummy identification values [icache_boot]'s own mint runs at -- any
     words will do, since [icache_boot_at] overwrites them. *)
  Local Definition ic_dv_dummy : nat -> mword 32 * mword 32 :=
    fun _ => ((mword_of_int 0 : mword 32), (mword_of_int 0 : mword 32)).

  (* THE BOOT STEP AT PRE-MINTED NAMES (fs-cfg-boot.md staging 1).

     In: the itable spinlock as iinit leaves it (zeroed word, named, cpu
     field cleared), iinit's fifty [sl_fresh]es, the fifty entries' raw
     cells, the whole [iref_slots] supply, and the stocked pool.
     Out: everything every icache contract takes, at the ALL-EMPTY boot
     state (§13.7-§13.9): [M = ∅], [ci = ∅], fifty [ic_empty_arm]s, fifty
     [islot_empty]s, the pool covering the whole region.

     The last conjunct IS [ic_sleeplocks cn], spelled out
     because this file sits below the fileclose spec.

     Same premises, same conclusion -- but the itable lock's gname and the
     whole escrow-name record are GIVEN rather than returned, so a caller
     that had to write [is_itable2 fsc_itlock fsc_ic ...] before this fupd
     ran (the era fupd of [FsCfgBoot.fs_cfg_alloc], whose whole reason to
     exist is that an ambient class field cannot be an existential) can.
     What replaces the two mints:
       - [newlock] becomes [newlock_at γl] against [lock_free_tok γl];
       - [ic_names_alloc] becomes the three families as PREMISES, with the
         identification one at ARBITRARY recorded values, re-tagged per slot
         by [ic_id_set].  [ic_tok] and [ic_mid] are value-free exclusive
         tokens ([ghost_var … DepNone], [lock_tok_excl]), so they pass
         straight through.
     [icache_boot] below is this lemma plus the two mints, so there is one
     body and the old signature is a corollary. *)
  Lemma icache_boot_at (E : coPset) (γl : gname) (cn : ic_names)
      (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) :
    (* THE COUNT AUTHORITY, at the empty table.  A PREMISE rather than an
       allocation, because the authority's gname is CANONICAL -- it is
       [IcacheRef.icfg_iref] of the ambient cache, the same one every
       reference in the system is stated over -- so this lemma cannot mint
       it and then claim to have built THE itable.  [IcacheRef.icfg_alloc]
       is what discharges it. *)
    own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) -∗
    (* THE LIVENESS POOL, at the all-free state: one whole unit per slot
       (design §14.6).  A PREMISE for [icfg_iref]'s reason -- the gname is
       [IcacheRef.icfg_live] of the AMBIENT cache, so this lemma may not
       mint it.  [IcacheRef.icfg_alloc] + [IcacheRef.live_boot_split] is
       what discharges it. *)
    (* RULING R-e: [live_boot_map] mints the RESERVED half of the keyspace
       ([NINODE + k], the per-slot freeze selector) in the same [own_alloc],
       so this premise simply runs to [NINODE + NINODE] and
       [live_pool_empty] retags the upper half to [false] on the way in. *)
    ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) -∗
    (* THE PER-SLOT SLEEPLOCK GHOSTS, as [IcacheRef.icfg_alloc] hands them
       over: an unbuilt lock's free arm, and the AUTHORITATIVE ZERO of its
       outstanding-share count.  A PREMISE for the same reason the count
       authority is one -- the gname is CANONICAL ([icfg_isl]), so this file
       must be given it rather than allocate it and then claim to have built
       THE itable's locks. *)
    ([∗ list] k ∈ seq 0 NINODE,
       sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) -∗
    itable_lock ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name itable_lock "itable"%string -∗
    lock_cpu itable_lock ↦₈ (zero_reg : mword 64) -∗
    ([∗ list] k ∈ seq 0 NINODE, sl_fresh (i_lock (ientry k)) "inode"%string) -∗
    ([∗ list] k ∈ seq 0 NINODE, ientry_raw k) -∗
    iref_slots_auth -∗
    (* THE STOCKED POOL, as ORDINARY ROWS (durable-disk B''-esc), beside the
       residency key WHOLE.  This lemma is what allocates the pool's own
       invariant out of the two: the rows and one half of the key go in, the
       other half stays under the itable lock inside [itable_res2]'s
       [ipool] conjunct, and [is_itable2] carries the invariant on. *)
    ipool_rows γfs γi cov logstart (region_inums nib) -∗
    ghost_var icfg_pool 1 (∅ : gset Z) -∗
    (* ...AND THE IN-TRANSITION KEY (durable-disk C-3b), whole and empty:
       at boot no walk is carrying an inum and no pending/await row exists,
       so the pool's partition is the two-way one. *)
    ghost_var icfg_pext 1 (∅ : gset Z) -∗
    (* THE ITABLE LOCK'S GHOST, unbuilt: the two [excl_auth] halves at
       [None], as [WpLockAt.lock_ghost_alloc] mints them.  A PREMISE for the
       reason every other ghost here is one -- the gname is the caller's
       (eventually [fsc_itlock]), so this lemma may not choose it. *)
    lock_free_tok γl -∗
    (* THE ESCROW LAYER'S THREE FAMILIES, as [IcacheEscrow.ic_names_alloc]
       hands them over.  The first two are value-free exclusive tokens; the
       third arrives at WHATEVER values it was minted at and is re-tagged
       below to the dev/inum words the entry cells actually hold. *)
    ([∗ list] k ∈ seq 0 NINODE, ic_tok cn k) -∗
    ([∗ list] k ∈ seq 0 NINODE, ic_mid cn k) -∗
    ([∗ list] k ∈ seq 0 NINODE,
       ∃ (v : bool) (d n : mword 32), ic_id cn k 1 v d n)
    ={E}=∗
      is_itable2 γl cn γfs γi cov logstart nib dv ∗
      itable_inv ∗
      ic_escrows cn γfs γi cov logstart ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ γil γisl : gname,
           is_sleeplock_gen γil γisl (i_lock (ientry k)) "inode"%string
                            (ic_tok cn k) (slh_tok (icfg_isl k))).
  Proof.
    iIntros "Hauth Hlive Hislg Hlkw #Hnm Hcpu Hsl Hraw Hsupply Hrows Hkey".
    iIntros "Hxkey Hfree Htok Hmid Hgid".
    (* THE POOL'S INVARIANT IS ALLOCATED AFTER THE ESCROWS (durable-disk
       C-3b), and it has to be: its body carries a QUARTER of every slot's
       [ic_id] beside the partition, and those quarters do not exist until
       the escrow loop below has re-tagged the fifty identities at the
       values the entry cells actually hold. *)
    (* only the ZEROS are used: they are what [itable_body] parks for a free
       slot.  The [sl_free_tok]s beside them belong to whoever wants to build
       a lock AT [icfg_isl k], and this cache does not -- its locks carry
       their own holder gname and only the DEPOSIT is slot-keyed. *)
    iDestruct (big_sepL_sep with "Hislg") as "[_ Hislauth]".
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
    (* ---- the count authority's two halves ---- *)
    iDestruct (itable_half_split with "Hauth") as "[HhalfI HhalfL]".
    (* ---- the [ref]-word invariant ---- *)
    iMod (live_pool_empty with "Hlive") as "Hpool0".
    iMod (inv_alloc icacheN E itable_body
            with "[HhalfI Href Hpool0]") as "#Hitinv".
    { iNext. iExists ∅. iFrame "HhalfI". iSplitR; [iPureIntro; exact icM_wf_empty |].
      iSplitL "Href"; [iApply iref_cells_boot; iExact "Href" |].
      iExact "Hpool0". }
    (* ---- the fifty escrows, at the EMPTY arm, and the table's shares ---- *)
    iDestruct (big_sepL_sep_2 with "Hid Hvalid") as "H1".
    iDestruct (big_sepL_sep_2 with "H1 Hmirror") as "H2".
    iDestruct (big_sepL_sep_2 with "H2 Hmid") as "H3".
    iDestruct (big_sepL_sep_2 with "H3 Hgid") as "H4".
    iAssert ([∗ list] k ∈ seq 0 NINODE,
               |={E}=> ic_escrow cn γfs γi cov logstart k ∗
                       (islot_empty cn k ∗
                        ic_id cn k (1/4) false (dvs k).1 (dvs k).2))%I
      with "[H4]" as "Hesc".
    { iApply (big_sepL_mono with "H4"). intros idx k _.
      iIntros "(((([Hd Hn] & (%w & Hv)) & Hmir) & Hmd) & Hgd)".
      (* the caller minted this variable blind; WRITE what the cells say.
         [Hd]/[Hn] are slot [k]'s dev/inum cells at [(dvs k).1]/[(dvs k).2],
         so this is the one place the recorded identity can be made true. *)
      iDestruct "Hgd" as (v0 d0 n0) "Hgd".
      iMod (ic_id_set _ _ _ _ _ false (dvs k).1 (dvs k).2 with "Hgd") as "Hgd".
      iDestruct (ic_id_split_half with "Hgd") as "[Hgd1 Hgd2]".
      (* THE TABLE'S HALF SPLITS AGAIN (durable-disk C-3b): a quarter stays
         with [islot_empty] and a quarter goes to the pool's invariant, where
         it is what makes the partition speak about this escrow. *)
      iDestruct (ic_id_quarters_split with "Hgd2") as "[Hgd2 Hgd3]".
      iDestruct (word4_pointsto_half_split with "Hn") as "[Hn1 Hn2]".
      iMod (inv_alloc (icEscN .@ k) E (ic_escrow_body cn γfs γi cov logstart k)
              with "[Hd Hn1 Hv Hmir Hmd Hgd1]") as "#Hinv".
      { iNext. rewrite /ic_escrow_body. iRight. iRight. iRight. iLeft.
        rewrite /ic_empty_arm. iExists (dvs k).1, (dvs k).2, w. iFrame. }
      iModIntro. iFrame "Hinv". iSplitR "Hgd3"; [| iExact "Hgd3"].
      rewrite /islot_empty. iExists (dvs k).1, (dvs k).2. iFrame. }
    iMod (big_sepL_fupd with "Hesc") as "Hesc".
    iEval (rewrite big_sepL_sep) in "Hesc".
    iDestruct "Hesc" as "[#Hescrows Hrest]".
    iEval (rewrite big_sepL_sep) in "Hrest".
    iDestruct "Hrest" as "[Hslots Hquarters]".
    (* the pool's own invariant, out of the stocked rows, the two keys and
       the fifty quarters (durable-disk C-3b) *)
    iDestruct (ic_ids_of_intro cn dvs with "Hquarters") as "Hids".
    iMod (ipool_alloc_inv E cn γfs γi cov logstart nib (ic_ids_of dvs)
            (ic_ids_of_length dvs) (ic_ids_of_live dvs)
            with "Hkey Hxkey Hids Hrows") as "[#Hpinv Hpool]".
    (* ---- the itable lock's resource, and the lock ---- *)
    iAssert (itable_res2 cn γfs γi cov logstart nib dv)%I
      with "[HhalfL Hsupply Hslots Hpool Hislauth]" as "Hres".
    { iExists ∅, ∅. iFrame "HhalfL".
      iSplitR; [iPureIntro; exact icM_wf_empty |].
      iSplitR; [iPureIntro; exact (ic_ci_wf_empty nib dv) |].
      iFrame "Hsupply".
      iSplitL "Hislauth"; [iApply isl_pool_empty; iExact "Hislauth" |].
      iSplitL "Hslots".
      { iApply (big_sepL_mono with "Hslots"). intros idx k _.
        rewrite /islot2 !lookup_empty. done. }
      rewrite ci_inums_empty difference_empty_L. iExact "Hpool". }
    iMod (newlock_at E γl itable_lock "itable"%string
            (itable_res2 cn γfs γi cov logstart nib dv)
            with "Hfree Hnm Hlkw Hcpu Hres") as "#Hlock".
    (* ---- the fifty inode sleeplocks, sealed over the checkout tokens ---- *)
    iDestruct (big_sepL_sep_2 with "Hsl Htok") as "Hsl".
    (* THE DEPOSIT IS KEYED BY THE SLOT, NOT BY THE LOCK.  What a holder
       leaves in the entry's sleeplock is [slh_tok (icfg_isl k) q] -- a share
       of somebody's REFERENCE to slot [k] -- which is what lets iput, holding
       the only reference, prove the lock free rather than block on it
       (claude-notes/projects/iput-acquiresleep.md).  The lock's OWN gname
       stays existential, so no consumer of [ic_sleeplocks] changes. *)
    iAssert ([∗ list] k ∈ seq 0 NINODE,
               |={E}=> ∃ γil γisl : gname,
                 is_sleeplock_gen γil γisl (i_lock (ientry k)) "inode"%string
                                  (ic_tok cn k) (slh_tok (icfg_isl k)))%I
      with "[Hsl]" as "Hsl".
    { iApply (big_sepL_mono with "Hsl"). intros idx k _.
      iIntros "[Hf Ht]".
      iMod (sl_fresh_new_gen E _ _ _ (fun _ q => slh_tok (icfg_isl k) q)
              with "Hf Ht") as (γil γisl) "[#Hlk _]".
      iModIntro. iExists γil, γisl. iExact "Hlk". }
    iMod (big_sepL_fupd with "Hsl") as "Hsl".
    iModIntro.
    (* structurally, NOT [iFrame "…"]: naming the four hypotheses fixes the
       context-side scan, but the GOAL still holds a fifty-slot big-op of
       sleeplocks over [ic_tok] and the whole [ic_escrows] family, and a
       named [iFrame] searches that once per name -- 98 s in this one
       sentence (optimization.md's BioInv rule). *)
    rewrite /is_itable2.
    iSplitR; [iSplitR; [iExact "Hlock" | iExact "Hpinv"] |].
    iSplitR; [iExact "Hitinv" |].
    iSplitR; [iExact "Hescrows" |].
    iExact "Hsl".
  Qed.

  (* THE ORIGINAL SIGNATURE, as a COROLLARY: mint the two names, then fill
     them.  One body, so nothing here is a copy of anything above.

     The dvs-collection order is NOT an obstruction to this direction:
     [icache_boot_at] overwrites the identification values, so the mint runs
     at [ic_dv_dummy] and [fun_of_big] never has to happen before it.  That
     is the same fact that makes the [_at] form possible at all. *)
  Lemma icache_boot (E : coPset) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dv : mword 32) :
    own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) -∗
    ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) -∗
    ([∗ list] k ∈ seq 0 NINODE,
       sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) -∗
    itable_lock ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name itable_lock "itable"%string -∗
    lock_cpu itable_lock ↦₈ (zero_reg : mword 64) -∗
    ([∗ list] k ∈ seq 0 NINODE, sl_fresh (i_lock (ientry k)) "inode"%string) -∗
    ([∗ list] k ∈ seq 0 NINODE, ientry_raw k) -∗
    iref_slots_auth -∗
    ipool_rows γfs γi cov logstart (region_inums nib) -∗
    ghost_var icfg_pool 1 (∅ : gset Z) -∗
    ghost_var icfg_pext 1 (∅ : gset Z)
    ={E}=∗ ∃ (γl : gname) (cn : ic_names),
      is_itable2 γl cn γfs γi cov logstart nib dv ∗
      itable_inv ∗
      ic_escrows cn γfs γi cov logstart ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ γil γisl : gname,
           is_sleeplock_gen γil γisl (i_lock (ientry k)) "inode"%string
                            (ic_tok cn k) (slh_tok (icfg_isl k))).
  Proof.
    iIntros "Hauth Hlive Hislg Hlkw #Hnm Hcpu Hsl Hraw Hsupply Hrows Hkey Hxkey".
    iMod lock_ghost_alloc as (γl) "Hfree".
    iMod (ic_names_alloc ic_dv_dummy) as (cn) "(Htok & Hmid & Hgid)".
    iDestruct (ic_id_forget cn false ic_dv_dummy with "Hgid") as "Hgid".
    iMod (icache_boot_at E γl cn γfs γi cov logstart nib dv with "Hauth Hlive Hislg Hlkw Hnm Hcpu Hsl Hraw Hsupply Hrows Hkey Hxkey Hfree Htok Hmid Hgid") as "H".
    iModIntro. iExists γl, cn. iExact "H".
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
