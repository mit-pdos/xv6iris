(* FsStateEra.v -- THE IN-ERA INODE BUNDLE, and the dictionary that turns
   the kernel's in-memory block model into an [FsStateInode.fs_node].

   Design of record: claude-notes/design/fs-state.md sections 2 and 4;
   stage 2b-inode-2 of claude-notes/projects/durable-disk.md.

   ---- WHAT THE BUNDLE IS ----------------------------------------------

   Under ruling (i) of 2b-inode-1 a checked-out inode does NOT carry its
   record's 64 bytes: those park REGION-side, because [ialloc]'s and
   [ireclaim]'s free-slot scans read OTHER slots' bytes out of a shared
   inode block while holding no per-slot resource.  What travels instead is
   [InodeRegion.dinode_at], the holder's EXCLUSIVE record proxy -- agreement
   pins the value, exclusivity confers the write permission, and the write
   itself is an AU that borrows the region's run for the linearization
   point.  So the in-era bundle is

     inode_owned_era gfs gi inum n :=
         dinode_at gi inum (fn_rec n)                    (* the proxy      *)
       * [* map] k -> bs in fn_blk n, blk_owned G (fn_naddr n k) bs
       * ind_owned G n                                   (* the indirect   *)
       * top_frag G (bv_unsigned inum) n                 (* the era's top  *)
       * |{ inode_local (bv_unsigned inum) n }|

   -- i.e. [FsStateInode.inode_owned] with [rec_owned] replaced by the
   proxy and with the LINK ghosts left out.  The links are NOT part of this
   bundle and are not going to be: since durable-disk 2b-inode-4 a
   directory's TOKENS ride beside it in the escrow payload
   ([FsStateInode.ent_toks], see the section at the end of this file) and
   the per-inum AUTHORITY lives with the record in the inode region.

   [fn_rec n] IS the value of [dinode_at] and [n] IS the value of the top
   fragment: the bundle names each once, so both ties are maintained BY
   CONSTRUCTION and neither is ever a clause.  A record write therefore
   moves all three together, which is what [inode_owned_era_retag] does.

   ---- THE DICTIONARY ---------------------------------------------------

   [InodeInv]'s pure block model ([blkmap], [blkmap_get], [bm_cells],
   [bm_covers], [blk_holes_zero], [inode_sized]) is KEPT as the bridge --
   the worklist's KEEP verdict -- because readi/writei/bmap/itrunc are
   stated over it and a wholesale restatement of those four is out of
   scope.  So the two models are related here, in BOTH directions:

     era_node dn bm data : fs_node        (blkmap + total data -> node)
     bm_of  n           : blkmap         (node -> blkmap)

   with [era_node (fn_rec n) (bm_of n) (fn_data n) = n] under
   [inode_local] ([era_node_bm_of]).  The direction a payload FLIP uses is
   [bm_of]: a payload whose [data] is EXISTENTIALLY bound (which is exactly
   what [IcacheEscrow.ic_loaded] has) picks the node first and reads the
   old model off it, so no extensionality between two [data] functions is
   ever needed.

   ---- WHAT [inode_local] DOES NOT GIVE BACK ----------------------------

   [InodeLock.inode_ok] is [blkmap_wf] + four record facts + the two data
   facts.  Of [blkmap_wf]'s five conjuncts, three are [inode_local]
   ([bmw_of_local]); the other two are NOT, by design (fs-state.md
   section 0):

     - INJECTIVITY is the [*].  [inode_owned_era_slot_inj] reads it off the
       block big-op through [FsStateDefs.blk_owned_ne], with no clause.
     - COVERAGE ([b in cov], [b not in log_region_set]) is a consequence of
       OWNING the run, produced by [FsBlocks.fsblock_home_open] against the
       log's byte invariant -- a fupd at [logN], not a pure fact.
       [inode_owned_era_home] is that reading for one slot.

   Two further facts a caller of [inode_ok] has that [inode_local] does NOT
   imply, recorded here because they are what any flip of a payload must
   supply from elsewhere:

     - [bv_unsigned (di_type dn) <> 0] -- "this inode is allocated".  It is
       the checked-out payload's own fact and stays a payload conjunct.
     - [inl_type] (the type is one of 0 / T_DIR / T_FILE / T_DEVICE) is
       STRONGER than [inode_ok]'s type conjunct, which only says "nonzero".
       Nothing in the in-memory chain produces the enumeration today: the
       image gives it ([FsImg.fio_type]) and [ialloc] re-establishes it,
       but no region or icache clause carries it in between.  Likewise
       [inl_dir_size] ("16 divides a directory's size") and the two dots
       clauses have no [inode_ok] counterpart -- the tree carries the
       latter two as [DirView.dir_dots_ix] / [FsTree.dir_uniq], which ARE
       payload conjuncts.  So [inode_local_of_ok] takes exactly the four
       facts [inode_ok] lacks, and closing the [inl_type] one is a ruling
       for the orchestrator. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map invariants.
(* The [FsState*] stack exports names with live twins ([byte_range],
   [fs_view]); the LAST import wins, so it goes FIRST and the block layer's
   spellings below shadow it back.  Every [FsStateDefs] run in this file is
   therefore written QUALIFIED. *)
Require Import FsStateLink.    (* [fsLinkG] -- capacity class, must be IMPORTed *)
Require Import FsStateInode.   (* [fs_node], [inode_local], [ind_owned], ... *)
Require Import FsState.        (* [fsTopG], [top_frag] -- ditto *)
Require Import FsBytesGamma.   (* [fs_gamma_L], [gamma_blk_owned]           *)
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import BioDefs.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsBlocks.
Require Import LogDefs.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  A SPARSE MAP BUILT OVER A RANGE                                   *)
(* ===================================================================== *)

(* [fn_blk] is PARTIAL -- that is what kills the 268-element framing hazard
   [InodeInv.inode_blocks] carries -- so the dictionary has to build a
   [gmap] out of a total function and a range.  Written as its own
   recursion rather than through [list_to_map . omap] so that the lookup
   law below is one ordinary induction and no [NoDup] side condition ever
   appears. *)
Fixpoint blk_of_seq (f : nat -> option (list (bv 8))) (b n : nat)
  : gmap nat (list (bv 8)) :=
  match n with
  | O => ∅
  | S n' => match f b with
            | Some v => <[b := v]> (blk_of_seq f (S b) n')
            | None => blk_of_seq f (S b) n'
            end
  end.

Lemma blk_of_seq_lookup (f : nat -> option (list (bv 8))) (n b k : nat) :
  blk_of_seq f b n !! k = if decide (b <= k < b + n)%nat then f k else None.
Proof.
  revert b. induction n as [| n IH]; intros b; simpl.
  - rewrite lookup_empty. destruct (decide _) as [Hc | _]; [lia | done].
  - destruct (f b) as [v |] eqn:Hb.
    + destruct (decide (k = b)) as [-> | Hne].
      * rewrite lookup_insert.
        destruct (decide (b <= b < b + S n)%nat) as [_ | Hc]; [| lia].
        by rewrite Hb.
      * rewrite lookup_insert_ne; [| done]. rewrite IH.
        destruct (decide (S b <= k < S b + n)%nat) as [H1 | H1];
          destruct (decide (b <= k < b + S n)%nat) as [H2 | H2];
          [done | lia | lia | done].
    + destruct (decide (k = b)) as [-> | Hne].
      * rewrite IH.
        destruct (decide (S b <= b < S b + n)%nat) as [Hc | _]; [lia |].
        destruct (decide (b <= b < b + S n)%nat) as [_ | Hc]; [| lia].
        by rewrite Hb.
      * rewrite IH.
        destruct (decide (S b <= k < S b + n)%nat) as [H1 | H1];
          destruct (decide (b <= k < b + S n)%nat) as [H2 | H2];
          [done | lia | lia | done].
Qed.

(* nothing ever needs the recursion itself; sealing it keeps a conversion
   check from unrolling 268 [match]es (durable-notes: a definition whose
   body is a fold over a literal-sized range) *)
Global Opaque blk_of_seq.

(* ===================================================================== *)
(*  1.  THE DICTIONARY                                                    *)
(* ===================================================================== *)

Definition node_blk (bm : blkmap) (data : nat -> list (bv 8))
  : gmap nat (list (bv 8)) :=
  blk_of_seq (fun j => if decide (bv_unsigned (blkmap_get bm j) = 0)
                       then None else Some (data j))
             0 MAXFILE.

Lemma node_blk_lookup (bm : blkmap) (data : nat -> list (bv 8)) (k : nat) :
  node_blk bm data !! k
  = if decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0)
    then Some (data k) else None.
Proof.
  rewrite /node_blk blk_of_seq_lookup.
  destruct (decide (0 <= k < 0 + MAXFILE)%nat) as [Hin | Hout].
  - destruct (decide (bv_unsigned (blkmap_get bm k) = 0)) as [Hz | Hnz].
    + destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
        as [[_ Hc] | _]; [done | done].
    + destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
        as [_ | Hc]; [done |].
      exfalso. apply Hc. split; [lia | exact Hnz].
  - destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
      as [[Hc _] | _]; [lia | done].
Qed.

(* a blkmap and a TOTAL data function, as a node *)
Definition era_node (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
  : fs_node := MkNode dn (bm_ent bm) (node_blk bm data).

(* ...and a node, as a blkmap.  [bm_cells] is [di_addrs] verbatim under
   [dinode_wf], which is why the split is [take 12] / entry 12. *)
Definition bm_of (n : fs_node) : blkmap :=
  MkBlkmap (take NDIRECT (di_addrs (fn_rec n)))
           (di_addrs (fn_rec n) !!! NDIRECT)
           (fn_ent n).

(* the two spellings of 12 / 256 / 268 / 1024 are different constants in
   two files and equal by conversion; naming the equations is what lets a
   [rewrite] line the two [decide]s up *)
Lemma NDIRECT_FS : NDIRECT = FS_NDIRECT.
Proof. reflexivity. Qed.
Lemma NINDIRECT_FS : NINDIRECT = FS_NINDIRECT.
Proof. reflexivity. Qed.
Lemma MAXFILE_FS : MAXFILE = FS_MAXFILE.
Proof. reflexivity. Qed.
Lemma BSIZE_BSIZEz : Z.of_nat BSIZE = BSIZE_z.
Proof. reflexivity. Qed.

(* ---- [bm_of]'s readings --------------------------------------------- *)

Lemma bm_of_dir_len (n : fs_node) :
  dinode_wf (fn_rec n) -> length (bm_dir (bm_of n)) = NDIRECT.
Proof.
  rewrite /dinode_wf /bm_of /=. intros Hl. rewrite length_take Hl.
  rewrite /NDIRECT. lia.
Qed.

Lemma bm_of_cells (n : fs_node) :
  dinode_wf (fn_rec n) -> bm_cells (bm_of n) = di_addrs (fn_rec n).
Proof.
  rewrite /dinode_wf /bm_cells /bm_of /=. intros Hl.
  assert (H12 : (NDIRECT < length (di_addrs (fn_rec n)))%nat)
    by (rewrite Hl; rewrite /NDIRECT; lia).
  destruct (lookup_lt_is_Some_2 _ _ H12) as [x Hx].
  rewrite (list_lookup_total_correct _ _ _ Hx).
  rewrite -{2}(take_drop NDIRECT (di_addrs (fn_rec n))).
  f_equal.
  assert (Hdl : length (drop NDIRECT (di_addrs (fn_rec n))) = 1%nat).
  { rewrite length_drop Hl. rewrite /NDIRECT. lia. }
  assert (Hd0 : drop NDIRECT (di_addrs (fn_rec n)) !! 0%nat = Some x).
  { rewrite lookup_drop Nat.add_0_r. exact Hx. }
  destruct (drop NDIRECT (di_addrs (fn_rec n))) as [| y l] eqn:Hdrop;
    [simpl in Hdl; lia |].
  simpl in Hd0. injection Hd0 as ->.
  destruct l as [| z l]; [reflexivity | simpl in Hdl; lia].
Qed.

Lemma bm_of_ind (n : fs_node) :
  bv_unsigned (bm_ind (bm_of n)) = fn_indb n.
Proof. reflexivity. Qed.

Lemma bm_of_ent (n : fs_node) : bm_ent (bm_of n) = fn_ent n.
Proof. reflexivity. Qed.

Lemma bm_of_get (n : fs_node) (k : nat) :
  dinode_wf (fn_rec n) -> (k < MAXFILE)%nat ->
  bv_unsigned (blkmap_get (bm_of n) k) = fn_naddr n k.
Proof.
  intros Hwf Hk. rewrite /blkmap_get /fn_naddr /bm_of /= -NDIRECT_FS.
  destruct (decide (k < NDIRECT)%nat) as [Hlt | Hge]; [| reflexivity].
  f_equal.
  assert (Hl : (k < length (di_addrs (fn_rec n)))%nat).
  { rewrite /dinode_wf in Hwf. rewrite Hwf. rewrite /NDIRECT in Hlt. lia. }
  destruct (lookup_lt_is_Some_2 _ _ Hl) as [x Hx].
  rewrite (list_lookup_total_correct _ _ _ Hx).
  apply list_lookup_total_correct.
  rewrite lookup_take; [exact Hx | lia].
Qed.

Lemma bm_of_slot (n : fs_node) (k : nat) :
  dinode_wf (fn_rec n) -> (k <= MAXFILE)%nat ->
  bv_unsigned (bm_slot (bm_of n) k)
  = (if decide (k = MAXFILE) then fn_indb n else fn_naddr n k).
Proof.
  intros Hwf Hk. rewrite /bm_slot.
  destruct (decide (k = MAXFILE)) as [-> | Hne]; [exact (bm_of_ind n) |].
  exact (bm_of_get n k Hwf ltac:(lia)).
Qed.

(* ---- [fn_*] of [era_node] --------------------------------------------- *)

Lemma era_node_rec dn bm data : fn_rec (era_node dn bm data) = dn.
Proof. reflexivity. Qed.
Lemma era_node_ent dn bm data : fn_ent (era_node dn bm data) = bm_ent bm.
Proof. reflexivity. Qed.
Lemma era_node_blk dn bm data : fn_blk (era_node dn bm data) = node_blk bm data.
Proof. reflexivity. Qed.

Lemma era_node_naddr dn bm data k :
  di_addrs dn = bm_cells bm -> length (bm_dir bm) = NDIRECT ->
  (k < MAXFILE)%nat ->
  fn_naddr (era_node dn bm data) k = bv_unsigned (blkmap_get bm k).
Proof.
  intros Haddr Hlen Hk. rewrite /fn_naddr /blkmap_get /era_node /= -NDIRECT_FS.
  destruct (decide (k < NDIRECT)%nat) as [Hlt | Hge]; [| reflexivity].
  rewrite Haddr /bm_cells lookup_total_app_l; [reflexivity |].
  rewrite Hlen. exact Hlt.
Qed.

Lemma era_node_indb dn bm data :
  di_addrs dn = bm_cells bm -> length (bm_dir bm) = NDIRECT ->
  fn_indb (era_node dn bm data) = bv_unsigned (bm_ind bm).
Proof.
  intros Haddr Hlen. rewrite /fn_indb /era_node /= Haddr /bm_cells.
  rewrite lookup_total_app_r;
    [| rewrite Hlen /FS_NDIRECT /NDIRECT; lia].
  rewrite Hlen /FS_NDIRECT /NDIRECT.
  assert (He : (12 - 12)%nat = 0%nat) by lia. rewrite He. reflexivity.
Qed.

Lemma era_node_data dn bm data k :
  blk_holes_zero bm data -> (k < MAXFILE)%nat ->
  fn_data (era_node dn bm data) k = data k.
Proof.
  intros Hh Hk. rewrite /fn_data /era_node /= node_blk_lookup.
  destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
    as [_ | Hc]; [reflexivity |].
  assert (Hz : bv_unsigned (blkmap_get bm k) = 0).
  { destruct (decide (bv_unsigned (blkmap_get bm k) = 0)) as [Hz | Hnz];
      [exact Hz |]. exfalso. apply Hc. split; [exact Hk | exact Hnz]. }
  rewrite (Hh k Hk Hz) //.
Qed.

(* ---- THE ROUNDTRIP --------------------------------------------------- *)

Lemma era_node_bm_of (i : Z) (n : fs_node) :
  inode_local i n -> era_node (fn_rec n) (bm_of n) (fn_data n) = n.
Proof.
  intros Hl.
  pose proof (inl_blk_dom Hl) as Hdom.
  pose proof (inl_blk_top Hl) as Htop.
  pose proof (inl_rec_wf Hl) as Hwf.
  rewrite /era_node. destruct n as [dn ent blk]; simpl in *.
  f_equal. apply map_eq. intros k. rewrite node_blk_lookup.
  destruct (decide (k < MAXFILE)%nat) as [Hk | Hk].
  - rewrite (bm_of_get (MkNode dn ent blk) k Hwf Hk).
    destruct (blk !! k) as [bs |] eqn:Hbs.
    + assert (Hnz : fn_naddr (MkNode dn ent blk) k <> 0).
      { apply (Hdom k ltac:(rewrite -MAXFILE_FS; exact Hk)).
        by exists bs. }
      destruct (decide ((k < MAXFILE)%nat
                        /\ fn_naddr (MkNode dn ent blk) k <> 0))
        as [_ | Hc]; [| exfalso; apply Hc; split; [exact Hk | exact Hnz]].
      rewrite /fn_data /= Hbs //.
    + assert (Hz : fn_naddr (MkNode dn ent blk) k = 0).
      { destruct (decide (fn_naddr (MkNode dn ent blk) k = 0)) as [Hz | Hnz];
          [exact Hz |]. exfalso.
        destruct (proj2 (Hdom k ltac:(rewrite -MAXFILE_FS; exact Hk)) Hnz)
          as [bs Hbs']. simpl in Hbs'. rewrite Hbs' in Hbs. discriminate. }
      destruct (decide ((k < MAXFILE)%nat
                        /\ fn_naddr (MkNode dn ent blk) k <> 0))
        as [[_ Hc] | _]; [exfalso; exact (Hc Hz) | reflexivity].
  - destruct (decide ((k < MAXFILE)%nat /\ _)) as [[Hc _] | _]; [lia |].
    rewrite (Htop k ltac:(rewrite -MAXFILE_FS; lia)) //.
Qed.

(* ===================================================================== *)
(*  2.  THE PURE HALF: [inode_local] AND [inode_ok], BOTH WAYS            *)
(* ===================================================================== *)

(* [FsTree]'s two constants and [DirView]'s spell the same bytes through
   [mword_of_int] and [Z_to_bv]; the two are convertible, so this is a
   conversion and not a [vm_compute]. *)
Lemma DOT_dot : DOT = dot_name.
Proof. reflexivity. Qed.

Lemma DOTDOT_dotdot : DOTDOT = dotdot_name.
Proof. reflexivity. Qed.

(* ---- the three [blkmap_wf] conjuncts [inode_local] DOES give back ---- *)

Lemma bmw_of_local (i : Z) (n : fs_node) :
  inode_local i n ->
  length (bm_dir (bm_of n)) = NDIRECT
  /\ length (bm_ent (bm_of n)) = NINDIRECT
  /\ (bv_unsigned (bm_ind (bm_of n)) = 0 ->
      bm_ent (bm_of n) = replicate NINDIRECT (bv_0 32)).
Proof.
  intros Hl. split; [exact (bm_of_dir_len n (inl_rec_wf Hl)) |].
  split; [rewrite bm_of_ent NINDIRECT_FS; exact (inl_ent_len Hl) |].
  rewrite bm_of_ind bm_of_ent NINDIRECT_FS. exact (inl_ind_zero Hl).
Qed.

Lemma bm_covers_of_local (i : Z) (n : fs_node) :
  inode_local i n -> bm_covers (bm_of n) (bv_unsigned (di_size (fn_rec n))).
Proof.
  intros Hl k Hk Hlt.
  rewrite (bm_of_get n k (inl_rec_wf Hl) Hk).
  apply (inl_covers Hl k ltac:(rewrite -MAXFILE_FS; exact Hk)).
  rewrite /fn_size -BSIZE_BSIZEz. exact Hlt.
Qed.

Lemma blk_holes_zero_of_local (i : Z) (n : fs_node) :
  inode_local i n -> blk_holes_zero (bm_of n) (fn_data n).
Proof.
  intros Hl k Hk Hz.
  rewrite (bm_of_get n k (inl_rec_wf Hl) Hk) in Hz.
  rewrite /fn_data.
  destruct (fn_blk n !! k) as [bs |] eqn:Hbs; [| reflexivity].
  exfalso.
  apply (proj1 (inl_blk_dom Hl k ltac:(rewrite -MAXFILE_FS; exact Hk))
               (mk_is_Some _ _ Hbs)). exact Hz.
Qed.

Lemma inode_sized_of_local (i : Z) (n : fs_node) :
  inode_local i n -> inode_sized (fn_data n).
Proof.
  intros Hl k Hk. rewrite /fn_data.
  destruct (fn_blk n !! k) as [bs |] eqn:Hbs.
  - exact (inl_blk_len Hl k bs Hbs).
  - apply length_replicate.
Qed.

(* THE FULL [inode_ok], from the era bundle's pure half plus the two facts
   OWNERSHIP -- not a clause -- produces (see the header): the
   coverage/log-disjointness pair and the injectivity, both supplied here
   as the last two conjuncts of [blkmap_wf].  A caller reads them off
   [inode_owned_era_home] and [inode_owned_era_slot_inj] below. *)
Lemma inode_ok_of_local (i : Z) (n : fs_node) (cov : gset Z) (ls : Z) :
  inode_local i n ->
  (forall k : nat, (k <= MAXFILE)%nat ->
     bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
     bv_unsigned (bm_slot (bm_of n) k) ∈ cov
     /\ ~ (bv_unsigned (bm_slot (bm_of n) k) ∈ log_region_set ls)) ->
  (forall k j : nat, (k <= MAXFILE)%nat -> (j <= MAXFILE)%nat ->
     bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
     bm_slot (bm_of n) k = bm_slot (bm_of n) j -> k = j) ->
  bv_unsigned (di_type (fn_rec n)) <> 0 ->
  inode_ok cov ls (fn_rec n) (bm_of n) (fn_data n).
Proof.
  intros Hl Hcov Hinj Hty.
  destruct (bmw_of_local i n Hl) as (Hd & He & Hi).
  rewrite /inode_ok /blkmap_wf.
  split.
  { split; [exact Hd |]. split; [exact He |]. split; [exact Hi |].
    split; [exact Hcov | exact Hinj]. }
  split; [exact (bm_covers_of_local i n Hl) |].
  split; [symmetry; exact (bm_of_cells n (inl_rec_wf Hl)) |].
  split; [exact Hty |].
  split.
  { pose proof (inl_size Hl) as [_ Hs]. rewrite /fn_size in Hs.
    rewrite BSIZE_BSIZEz MAXFILE_FS. exact Hs. }
  split; [exact (blk_holes_zero_of_local i n Hl) |].
  exact (inode_sized_of_local i n Hl).
Qed.

(* ---- ...AND THE OTHER WAY: [inode_local] of [era_node] ---------------- *)

(* THE FOUR FACTS [inode_ok] DOES NOT CARRY, as premises.  Three of them
   ARE payload conjuncts already ([FsTree.dir_uniq],
   [DirView.dir_dots_ix], and the "16 divides the size" fact every
   directory producer establishes); the fourth, the TYPE ENUMERATION, has
   no producer in the in-memory chain -- see the header.
   The directory clauses are read at [fn_data (era_node ..)], not at
   [data]: a payload whose [data] is existentially bound re-existentialises
   at the node's own reading, so nothing ever has to relate two [data]
   functions.  [era_node_data] is the transport for a caller that does hold
   [data] concretely. *)
Lemma inode_local_of_ok (i : Z) (cov : gset Z) (ls : Z)
    (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov ls dn bm data ->
  (bv_unsigned (di_type dn) = 0 \/ bv_unsigned (di_type dn) = T_DIR_z
   \/ bv_unsigned (di_type dn) = T_FILE_z
   \/ bv_unsigned (di_type dn) = T_DEVICE_z) ->
  bv_unsigned (di_nlink dn) <= 32767 ->
  (bv_unsigned (di_type dn) = T_DIR_z -> (16 | bv_unsigned (di_size dn))) ->
  dir_uniq dn (fn_data (era_node dn bm data)) ->
  dir_dots_ix i dn (fn_data (era_node dn bm data)) ->
  inode_local i (era_node dn bm data).
Proof.
  intros (Hwf & Hcov & Haddr & Hty0 & Hsz & Hholes & Hsized)
         Hty Hnl Hdsz Huniq Hdots.
  destruct Hwf as (Hdlen & Helen & Hindz & _ & _).
  assert (Hnaddr : forall k, (k < MAXFILE)%nat ->
                     fn_naddr (era_node dn bm data) k
                     = bv_unsigned (blkmap_get bm k))
    by (intros k Hk; exact (era_node_naddr dn bm data k Haddr Hdlen Hk)).
  assert (Hind : fn_indb (era_node dn bm data) = bv_unsigned (bm_ind bm))
    by exact (era_node_indb dn bm data Haddr Hdlen).
  (* the record's own well-formedness comes off [di_addrs = bm_cells] *)
  assert (Hrwf : dinode_wf dn).
  { rewrite /dinode_wf Haddr /bm_cells length_app Hdlen /NDIRECT /=. lia. }
  (* the two readings [fn_is_dir] / [fn_nrec] resolve to the record's *)
  assert (Hdirb : fn_is_dir (era_node dn bm data) = true
                  <-> bv_unsigned (di_type dn) = T_DIR_z).
  { rewrite /fn_is_dir. apply bool_decide_eq_true. }
  assert (Hnrec : fn_nrec (era_node dn bm data)
                  = dir_nrec (bv_unsigned (di_size dn))) by reflexivity.
  (* [nlink <> 0] as the record states it, which is the dots guard's form *)
  assert (Hnlz : fn_nlink (era_node dn bm data) <> 0%nat ->
                 bv_unsigned (di_nlink dn) <> 0).
  { intros Hnz Hc. apply Hnz.
    rewrite /fn_nlink era_node_rec Hc //. }
  constructor.
  - exact Hrwf.
  - rewrite -NINDIRECT_FS. exact Helen.
  - rewrite Hind -NINDIRECT_FS. exact Hindz.
  - intros k Hk. rewrite -MAXFILE_FS in Hk.
    rewrite era_node_blk node_blk_lookup (Hnaddr k Hk).
    destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
      as [[_ Hnz] | Hc].
    + split; [intros _; exact Hnz | intros _; by eexists].
    + split; [intros [x Hx]; discriminate |].
      intros Hnz. exfalso. apply Hc. split; [exact Hk | exact Hnz].
  - intros k Hk. rewrite -MAXFILE_FS in Hk.
    rewrite era_node_blk node_blk_lookup.
    destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
      as [[Hc _] | _]; [lia | done].
  - intros k bs Hk. rewrite era_node_blk node_blk_lookup in Hk.
    destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
      as [[Hlt _] | _]; [| discriminate].
    injection Hk as <-. exact (Hsized k Hlt).
  - exact Hty.
  - rewrite /fn_size era_node_rec. split.
    + pose proof (bv_unsigned_in_range _ (di_size dn)) as [Hge _]. exact Hge.
    + rewrite -BSIZE_BSIZEz -MAXFILE_FS. exact Hsz.
  - intros k Hk Hlt. rewrite -MAXFILE_FS in Hk.
    rewrite (Hnaddr k Hk). apply (Hcov k Hk).
    rewrite /fn_size era_node_rec -BSIZE_BSIZEz in Hlt. exact Hlt.
  - intros Hz. exfalso. exact (Hty0 Hz).
  - exact Hnl.
  - intros Hd. exact (Hdsz (proj1 Hdirb Hd)).
  - intros Hd. rewrite Hnrec. exact (Huniq (proj1 Hdirb Hd)).
  - (* "." -- record 0 of a LIVE directory, through [dir_view_live] *)
    intros Hd Hnz.
    destruct (Hdots (proj1 Hdirb Hd) (Hnlz Hnz))
      as (H2 & Hlive0 & Hinum0 & Hname0 & _ & _).
    assert (Hlt0 : (0 < dir_nrec (bv_unsigned (di_size dn)))%nat) by lia.
    assert (Hbn : dir_bname (fn_data (era_node dn bm data)) 0%nat = DOT).
    { rewrite /dir_bname Hname0 DOT_dot //. }
    rewrite /dir_entries Hd Hnrec -Hbn.
    rewrite (dir_view_live (fn_data (era_node dn bm data))
               (dir_nrec (bv_unsigned (di_size dn))) 0%nat
               (Huniq (proj1 Hdirb Hd)) Hlt0 Hlive0).
    by rewrite Hinum0.
  - (* ".." -- record 1, the same way *)
    intros Hd Hnz.
    destruct (Hdots (proj1 Hdirb Hd) (Hnlz Hnz))
      as (H2 & _ & _ & _ & Hlive1 & Hname1).
    assert (Hlt1 : (1 < dir_nrec (bv_unsigned (di_size dn)))%nat) by lia.
    assert (Hbn : dir_bname (fn_data (era_node dn bm data)) 1%nat = DOTDOT).
    { rewrite /dir_bname Hname1 DOTDOT_dotdot //. }
    rewrite /dir_entries Hd Hnrec -Hbn.
    rewrite (dir_view_live (fn_data (era_node dn bm data))
               (dir_nrec (bv_unsigned (di_size dn))) 1%nat
               (Huniq (proj1 Hdirb Hd)) Hlt1 Hlive1).
    by eexists.
Qed.

(* ===================================================================== *)
(*  2b. THE DIRENT READINGS ARE EXTENSIONAL BELOW THE RECORD COUNT       *)
(* ===================================================================== *)

(* [era_node]'s [fn_data] agrees with [data] BELOW MAXFILE and cannot agree
   above it -- the map is partial by design.  So a directory fact stated
   over the payload's own TOTAL [data] -- which is the shape
   [DirView.dir_dots_ix] and [FsTree.dir_uniq] come in, at the image and at
   every payload -- has to be transported onto the node's reading.  That
   transport is one extensionality law over the flat byte view, and the
   only bound it ever needs is the record count: every dirent reading of
   record [k] touches file bytes [16k .. 16k+15] and nothing else.

   HOME: these belong beside [DirView.dfirst_ext] / [bname_ext] /
   [bview_ext], which are their pieces.  They live here while this file is
   their only consumer; move them when the payload flips. *)

Definition fb_agree (data data' : nat -> list (bv 8)) (N : nat) : Prop :=
  forall i : nat, (i < N)%nat -> file_byte data i = file_byte data' i.

Lemma fb_agree_sym data data' N :
  fb_agree data data' N -> fb_agree data' data N.
Proof. intros H i Hi. symmetry. exact (H i Hi). Qed.

Lemma fb_agree_mono data data' N M :
  (M <= N)%nat -> fb_agree data data' N -> fb_agree data data' M.
Proof. intros Hle H i Hi. apply H. lia. Qed.

Lemma dir_inum_data_ext data data' N k :
  fb_agree data data' N -> (16 * k + 2 <= N)%nat ->
  dir_inum data k = dir_inum data' k.
Proof.
  intros Hag Hle. rewrite /dir_inum.
  rewrite (Hag (16 * k)%nat ltac:(lia)).
  rewrite (Hag (16 * k + 1)%nat ltac:(lia)) //.
Qed.

(* the PRIMITIVE is stated at the [bname 14 (dir_name ..)] spelling, which
   is what [DirView.dir_matchb] and [dir_dots_ix] write out; [dir_bname] is
   that term by delta, so its own reading is one [exact] and no [rewrite]
   ever has to bridge the two spellings *)
Lemma dir_name14_data_ext data data' N k :
  fb_agree data data' N -> (16 * k + 16 <= N)%nat ->
  bname 14 (dir_name data k) = bname 14 (dir_name data' k).
Proof.
  intros Hag Hle. apply bname_ext.
  intros j Hj. rewrite /dir_name. apply Hag. lia.
Qed.

Lemma dir_bname_data_ext data data' N k :
  fb_agree data data' N -> (16 * k + 16 <= N)%nat ->
  dir_bname data k = dir_bname data' k.
Proof. exact (dir_name14_data_ext data data' N k). Qed.

Lemma dir_liveb_data_ext data data' N k :
  fb_agree data data' N -> (16 * k + 16 <= N)%nat ->
  dir_liveb data k = dir_liveb data' k.
Proof.
  intros Hag Hle. rewrite /dir_liveb /dir_freeb.
  rewrite (dir_inum_data_ext data data' N k Hag ltac:(lia)) //.
Qed.

Lemma dir_matchb_data_ext data data' N k s :
  fb_agree data data' N -> (16 * k + 16 <= N)%nat ->
  dir_matchb data k s = dir_matchb data' k s.
Proof.
  intros Hag Hle. rewrite /dir_matchb.
  rewrite (dir_liveb_data_ext data data' N k Hag Hle).
  rewrite (dir_name14_data_ext data data' N k Hag Hle) //.
Qed.

Lemma dir_first_data_ext data data' n s :
  fb_agree data data' (16 * n) -> dir_first data n s = dir_first data' n s.
Proof.
  intros Hag. rewrite /dir_first. apply dfirst_ext.
  intros j Hj. apply (dir_matchb_data_ext data data' (16 * n) j s Hag). lia.
Qed.

Lemma dir_view_data_ext data data' nrec :
  fb_agree data data' (16 * nrec) ->
  dir_view data nrec = dir_view data' nrec.
Proof.
  intros Hag. apply map_eq. intros s. rewrite !dir_view_lookup.
  rewrite (dir_first_data_ext data data' nrec s Hag).
  destruct (dir_first data' nrec s) as [k |] eqn:Hf;
    cbn [fmap option_fmap option_map]; [| reflexivity].
  apply dir_first_Some in Hf as (Hk & _ & _).
  rewrite (dir_inum_data_ext data data' (16 * nrec) k Hag ltac:(lia)) //.
Qed.

Lemma dir_names_unique_data_ext data data' nrec :
  fb_agree data data' (16 * nrec) ->
  dir_names_unique data nrec -> dir_names_unique data' nrec.
Proof.
  intros Hag Hu j k Hj Hk Hlj Hlk Hn. apply (Hu j k Hj Hk).
  - rewrite /dir_live
      (dir_inum_data_ext data data' (16 * nrec) j Hag ltac:(lia)). exact Hlj.
  - rewrite /dir_live
      (dir_inum_data_ext data data' (16 * nrec) k Hag ltac:(lia)). exact Hlk.
  - rewrite (dir_bname_data_ext data data' (16 * nrec) j Hag ltac:(lia)).
    rewrite (dir_bname_data_ext data data' (16 * nrec) k Hag ltac:(lia)).
    exact Hn.
Qed.

Lemma dir_uniq_data_ext dn data data' :
  fb_agree data data' (16 * dir_nrec (bv_unsigned (di_size dn))) ->
  dir_uniq dn data -> dir_uniq dn data'.
Proof.
  intros Hag Hu Hty.
  exact (dir_names_unique_data_ext data data' _ Hag (Hu Hty)).
Qed.

Lemma dir_dots_ix_data_ext (self : Z) dn data data' :
  fb_agree data data' (16 * dir_nrec (bv_unsigned (di_size dn))) ->
  dir_dots_ix self dn data -> dir_dots_ix self dn data'.
Proof.
  intros Hag Hd Hty Hnl.
  destruct (Hd Hty Hnl) as (H2 & Hl0 & Hi0 & Hn0 & Hl1 & Hn1).
  assert (Hi : forall k, (k < 2)%nat ->
                 dir_inum data k = dir_inum data' k).
  { intros k Hk.
    apply (dir_inum_data_ext data data'
             (16 * dir_nrec (bv_unsigned (di_size dn))) k Hag). lia. }
  assert (Hb : forall k, (k < 2)%nat ->
                 bname 14 (dir_name data k) = bname 14 (dir_name data' k)).
  { intros k Hk.
    apply (dir_name14_data_ext data data'
             (16 * dir_nrec (bv_unsigned (di_size dn))) k Hag). lia. }
  split_and!.
  - exact H2.
  - rewrite /dir_live -(Hi 0%nat ltac:(lia)). exact Hl0.
  - rewrite -(Hi 0%nat ltac:(lia)). exact Hi0.
  - rewrite -(Hb 0%nat ltac:(lia)). exact Hn0.
  - rewrite /dir_live -(Hi 1%nat ltac:(lia)). exact Hl1.
  - rewrite -(Hb 1%nat ltac:(lia)). exact Hn1.
Qed.

(* ---- and the two facts that instantiate it at [era_node] ---------------- *)

Lemma dir_nrec_bound (sz : Z) :
  0 <= sz -> sz <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  (16 * dir_nrec sz <= MAXFILE * BSIZE)%nat.
Proof.
  intros H0 Hsz. rewrite /dir_nrec.
  apply Nat2Z.inj_le. rewrite !Nat2Z.inj_mul Z2Nat.id.
  - pose proof (Z.div_mod sz 16 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound sz 16 ltac:(lia)) as [Hm0 Hm1].
    change (Z.of_nat 16) with 16. lia.
  - apply Z.div_pos; lia.
Qed.

Lemma era_node_fb_agree dn bm data :
  blk_holes_zero bm data ->
  fb_agree (fn_data (era_node dn bm data)) data (MAXFILE * BSIZE).
Proof.
  intros Hh i Hi. rewrite /file_byte.
  assert (Hd : (i `div` BSIZE < MAXFILE)%nat).
  { apply Nat.Div0.div_lt_upper_bound. rewrite Nat.mul_comm. exact Hi. }
  rewrite (era_node_data dn bm data (i `div` BSIZE)%nat Hh Hd) //.
Qed.

(* THE PAYLOAD's ENTRY MAP, AT ITS OWN TOTAL [data].  [dir_entries] reads
   the node's [fn_data], which is partial above the allocated slots; below
   the record count the two agree ([era_node_fb_agree]), so a producer that
   knows the directory's bytes as a total function -- which is what the
   IMAGE hands boot, and what every payload carries -- can state the entry
   map without ever mentioning [fn_data]. *)
Lemma dir_entries_era_node dn bm data :
  blk_holes_zero bm data ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  dir_entries (era_node dn bm data)
  = if bool_decide (bv_unsigned (di_type dn) = T_DIR_z)
    then dir_view data (dir_nrec (bv_unsigned (di_size dn)))
    else ∅.
Proof.
  intros Hh Hsz.
  assert (Hb : (16 * dir_nrec (bv_unsigned (di_size dn)) <= MAXFILE * BSIZE)%nat).
  { apply dir_nrec_bound; [| exact Hsz].
    pose proof (bv_unsigned_in_range _ (di_size dn)) as [Hge _]. exact Hge. }
  assert (Hag : fb_agree (fn_data (era_node dn bm data)) data
                  (16 * dir_nrec (bv_unsigned (di_size dn)))).
  { apply (fb_agree_mono _ _ (MAXFILE * BSIZE) _ Hb).
    exact (era_node_fb_agree dn bm data Hh). }
  rewrite /dir_entries /fn_is_dir /fn_type /fn_nrec /fn_size !era_node_rec.
  destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z)); [| reflexivity].
  exact (dir_view_data_ext _ _ _ Hag).
Qed.

Lemma fn_orphan_era_node dn bm data :
  fn_orphan (era_node dn bm data)
  = bool_decide (Z.to_nat (bv_unsigned (di_nlink dn)) = 0%nat).
Proof. rewrite /fn_orphan /fn_nlink era_node_rec //. Qed.

(* [FsTree]'s ["."] and [DirView]'s are the same list; the walks are stated
   in [DirView]'s spelling and the token layer in [FsTree]'s *)
Lemma DOT_dot_name : DOT = dot_name.
Proof. reflexivity. Qed.

(* a LIVE record is not an orphan -- the form every walk holds *)
Lemma fn_orphan_era_nz dn bm data :
  bv_unsigned (di_nlink dn) <> 0 -> fn_orphan (era_node dn bm data) = false.
Proof.
  intros H. rewrite fn_orphan_era_node. apply bool_decide_eq_false_2.
  pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))). lia.
Qed.

Lemma fn_orphan_era_z dn bm data :
  bv_unsigned (di_nlink dn) = 0 -> fn_orphan (era_node dn bm data) = true.
Proof.
  intros H. rewrite fn_orphan_era_node. apply bool_decide_eq_true_2.
  rewrite H //.
Qed.

(* THE FORM A PAYLOAD ACTUALLY HAS: the two directory facts stated over the
   payload's own total [data], transported onto the node's reading.  This
   is what [inode_local_of_ok] is called through at every producer -- the
   image's [FsImgBridge.img_dir_uniq] / [FsImg.fs_dots_wf_ok], and a
   re-park's [ic_loaded] conjuncts, are both in this shape. *)
Lemma inode_local_of_ok_data (i : Z) (cov : gset Z) (ls : Z)
    (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov ls dn bm data ->
  (bv_unsigned (di_type dn) = 0 \/ bv_unsigned (di_type dn) = T_DIR_z
   \/ bv_unsigned (di_type dn) = T_FILE_z
   \/ bv_unsigned (di_type dn) = T_DEVICE_z) ->
  bv_unsigned (di_nlink dn) <= 32767 ->
  (bv_unsigned (di_type dn) = T_DIR_z -> (16 | bv_unsigned (di_size dn))) ->
  dir_uniq dn data ->
  dir_dots_ix i dn data ->
  inode_local i (era_node dn bm data).
Proof.
  intros Hok Hty Hnl Hdsz Huniq Hdots.
  pose proof Hok as (_ & _ & _ & _ & Hsz & Hholes & _).
  assert (Hb : (16 * dir_nrec (bv_unsigned (di_size dn)) <= MAXFILE * BSIZE)%nat).
  { apply dir_nrec_bound; [| exact Hsz].
    pose proof (bv_unsigned_in_range _ (di_size dn)) as [Hge _]. exact Hge. }
  assert (Hag : fb_agree data (fn_data (era_node dn bm data))
                  (16 * dir_nrec (bv_unsigned (di_size dn)))).
  { apply (fb_agree_mono _ _ (MAXFILE * BSIZE) _ Hb).
    apply fb_agree_sym. exact (era_node_fb_agree dn bm data Hholes). }
  apply (inode_local_of_ok i cov ls dn bm data Hok Hty Hnl Hdsz).
  - exact (dir_uniq_data_ext dn data _ Hag Huniq).
  - exact (dir_dots_ix_data_ext i dn data _ Hag Hdots).
Qed.

(* ===================================================================== *)
(*  2b.  THE PAYLOAD'S OWN SHAPE FACTS                                    *)
(* ===================================================================== *)

(* A PAYLOAD NAMES ITS RECORD, ITS BLOCK MAP AND ITS DATA SEPARATELY, AND
   THE NODE IS [era_node] OF THE THREE.  Reading the node's own [bm_of] /
   [fn_data] back at the payload's [bm] / [data] needs exactly these five
   representational equations -- every one of them a conjunct of
   [InodeLock.inode_ok], so a producer that had [inode_ok] has them and
   nothing new is owed.  They are what the EXPENSIVE half of [inode_ok]
   (the coverage sweep and the injectivity) is derived THROUGH: the
   payload keeps the cheap shape, the [*] and the byte view's auth supply
   the rest ([inode_owned_era_era_node_ok] below). *)
Definition node_shape_ok (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) : Prop :=
  di_addrs dn = bm_cells bm
  /\ length (bm_dir bm) = NDIRECT
  /\ length (bm_ent bm) = NINDIRECT
  /\ (bv_unsigned (bm_ind bm) = 0 -> bm_ent bm = replicate NINDIRECT (bv_0 32))
  /\ blk_holes_zero bm data.

Lemma node_shape_ok_of_inode_ok (cov : gset Z) (ls : Z)
    (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov ls dn bm data -> node_shape_ok dn bm data.
Proof.
  intros (Hbw & _ & Haddr & _ & _ & Hh & _).
  destruct Hbw as (Hd & He & Hi & _ & _).
  split_and!; [exact Haddr | exact Hd | exact He | exact Hi | exact Hh].
Qed.

Lemma node_shape_ok_holes (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  node_shape_ok dn bm data -> blk_holes_zero bm data.
Proof. intros (_ & _ & _ & _ & H). exact H. Qed.

(* the round trip the payload uses: [bm_of] of the node IS the payload's
   own block map *)
Lemma bm_of_era_node (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  node_shape_ok dn bm data -> bm_of (era_node dn bm data) = bm.
Proof.
  intros (Haddr & Hd & _ & _ & _).
  rewrite /bm_of /era_node /=. rewrite Haddr /bm_cells.
  destruct bm as [dir ind ent]; simpl in *.
  assert (Htk : take NDIRECT (dir ++ [ind]) = dir).
  { rewrite -Hd. apply take_app_length. }
  rewrite Htk. f_equal.
  rewrite lookup_total_app_r; [| rewrite Hd; lia].
  rewrite Hd Nat.sub_diag //.
Qed.

Lemma fn_data_era_node (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (k : nat) :
  node_shape_ok dn bm data -> (k < MAXFILE)%nat ->
  fn_data (era_node dn bm data) k = data k.
Proof.
  intros Hs Hk.
  exact (era_node_data dn bm data k (node_shape_ok_holes _ _ _ Hs) Hk).
Qed.

(* [inode_ok]'s two [data]-facing conjuncts stop at MAXFILE, so a [data]
   that agrees below MAXFILE satisfies exactly the same statement *)
Lemma inode_ok_data_ext (cov : gset Z) (ls : Z) (dn : dinode) (bm : blkmap)
    (data data' : nat -> list (bv 8)) :
  (forall k : nat, (k < MAXFILE)%nat -> data k = data' k) ->
  inode_ok cov ls dn bm data -> inode_ok cov ls dn bm data'.
Proof.
  intros Hext (Hbw & Hcov & Haddr & Hty & Hsz & Hh & Hsi).
  split_and!;
    [exact Hbw | exact Hcov | exact Haddr | exact Hty | exact Hsz | |].
  - intros k Hk Hz. rewrite -(Hext k Hk). exact (Hh k Hk Hz).
  - intros k Hk. rewrite -(Hext k Hk). exact (Hsi k Hk).
Qed.

(* THE THREE RECORD-ONLY FACTS [inode_ok] DOES NOT CARRY, as one premise.
   A re-park re-establishes exactly this of its new record; everything
   else [inode_local] wants comes out of [inode_ok]. *)
Definition inode_rec_local (dn : dinode) : Prop :=
  (bv_unsigned (di_type dn) = 0 \/ bv_unsigned (di_type dn) = T_DIR_z
   \/ bv_unsigned (di_type dn) = T_FILE_z
   \/ bv_unsigned (di_type dn) = T_DEVICE_z)
  /\ bv_unsigned (di_nlink dn) <= 32767
  /\ (bv_unsigned (di_type dn) = T_DIR_z -> (16 | bv_unsigned (di_size dn))).

Lemma inode_rec_local_of (i : Z) (n : fs_node) :
  inode_local i n -> inode_rec_local (fn_rec n).
Proof.
  intros Hl. split_and!.
  - exact (inl_type Hl).
  - exact (inl_nlink Hl).
  - intros Hd. apply (inl_dir_size Hl). rewrite /fn_is_dir /fn_type Hd.
    apply bool_decide_eq_true. reflexivity.
Qed.

(* HOW A WRITER RE-ESTABLISHES IT.  Every write in this kernel keeps the
   record's TYPE (an ordinary flush, a link/unlink count move, a size
   growth) -- [InodeRegion.di_type_stable]'s right disjunct -- so the
   enumeration rides, and what is left is the two facts the write itself
   decides: the new count is still a non-negative short, and a directory's
   size is still 16-divisible.  Both are one line at every site. *)
Lemma inode_rec_local_same_type (dn dn' : dinode) :
  inode_rec_local dn ->
  di_type dn' = di_type dn ->
  bv_unsigned (di_nlink dn') <= 32767 ->
  (bv_unsigned (di_type dn') = T_DIR_z -> (16 | bv_unsigned (di_size dn'))) ->
  inode_rec_local dn'.
Proof.
  intros (Hty & _ & _) Heq Hnl Hgr. split_and!; [| exact Hnl | exact Hgr].
  rewrite Heq. exact Hty.
Qed.

Lemma inode_local_of_ok_rec (i : Z) (cov : gset Z) (ls : Z)
    (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov ls dn bm data ->
  inode_rec_local dn ->
  dir_uniq dn data ->
  dir_dots_ix i dn data ->
  inode_local i (era_node dn bm data).
Proof.
  intros Hok (Hty & Hnl & Hgr) Hu Hd.
  exact (inode_local_of_ok_data i cov ls dn bm data Hok Hty Hnl Hgr Hu Hd).
Qed.

(* ===================================================================== *)
(*  3.  THE RESOURCE BRIDGE, AND THE BUNDLE                              *)
(* ===================================================================== *)

Section EraRes.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Local Lemma era_seq_cons (j n : nat) : seq j (S n) = j :: seq (S j) n.
  Proof. reflexivity. Qed.

  Local Lemma era_seq_nil (j : nat) : seq j 0 = [].
  Proof. reflexivity. Qed.

  (* A RANGE-INDEXED BIG-OP OVER A TOTAL READING IS THE SPARSE MAP'S.
     One induction, over an ABSTRACT map whose domain the range covers, so
     no 268-way case split ever happens at a use site. *)
  Lemma big_sepL_seq_map (Φ : nat -> list (bv 8) -> iProp Σ)
      (m : gmap nat (list (bv 8))) (n b : nat) :
    (forall k, is_Some (m !! k) -> (b <= k < b + n)%nat) ->
    ([∗ list] k ∈ seq b n, from_option (Φ k) emp (m !! k))
    ⊣⊢ ([∗ map] k ↦ v ∈ m, Φ k v).
  Proof.
    revert b m. induction n as [| n IH]; intros b m Hdom.
    - assert (Hemp : m = ∅).
      { apply map_eq. intros k. rewrite lookup_empty.
        destruct (m !! k) as [v |] eqn:Hk; [| done].
        exfalso. destruct (Hdom k (mk_is_Some _ _ Hk)). lia. }
      rewrite Hemp big_sepM_empty (era_seq_nil b) big_sepL_nil //.
    - rewrite (era_seq_cons b n) big_sepL_cons.
      destruct (m !! b) as [v |] eqn:Hb.
      + cbn [from_option].
        rewrite (big_sepM_delete Φ m b v Hb).
        apply bi.sep_proper; [done |].
        rewrite -(IH (S b) (delete b m)).
        * apply big_sepL_proper. intros k j Hk.
          apply lookup_seq in Hk as [-> Hlt].
          rewrite lookup_delete_ne; [done | lia].
        * intros k [w Hw]. rewrite lookup_delete_Some in Hw.
          destruct Hw as [Hne Hw].
          destruct (Hdom k (mk_is_Some _ _ Hw)). lia.
      + cbn [from_option]. rewrite left_id.
        apply (IH (S b) m). intros k Hk.
        destruct (Hdom k Hk) as [Hlo Hhi].
        assert (Hne : k <> b).
        { intros ->. destruct Hk as [w Hw]. rewrite Hb in Hw. discriminate. }
        lia.
  Qed.

  (* ---- the two content bridges -------------------------------------- *)

  (* [InodeInv.inode_blocks] is a 268-element [big_sepL] with [True] at the
     holes; the era's block big-op is a [big_sepM] over the ALLOCATED slots
     only.  They are the same resource: the holes are [emp] in an affine
     BI, and each allocated slot's [fsblock] IS its [blk_owned] at the
     logged view ([FsBytesGamma.gamma_blk_owned]). *)
  Lemma inode_blocks_era (γfs : fs_names) (i : Z) (n : fs_node) :
    inode_local i n ->
    inode_blocks γfs (bm_of n) (fn_data n)
    ⊣⊢ ([∗ map] k ↦ bs ∈ fn_blk n,
          FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n k) bs).
  Proof.
    intros Hl.
    rewrite /inode_blocks.
    rewrite -(big_sepL_seq_map
                (fun k bs => FsStateDefs.blk_owned (fs_gamma_L γfs)
                               (fn_naddr n k) bs)
                (fn_blk n) MAXFILE 0%nat); last first.
    { intros k [bs Hbs].
      destruct (inode_local_beyond_size i n k bs Hl Hbs) as (Hk & _ & _).
      rewrite -MAXFILE_FS in Hk. lia. }
    apply big_sepL_proper. intros j k Hj.
    apply lookup_seq in Hj as [Heq Hlt].
    assert (Hk : (k < MAXFILE)%nat) by lia.
    rewrite /blk_res (bm_of_get n k (inl_rec_wf Hl) Hk).
    destruct (fn_blk n !! k) as [bs |] eqn:Hbs; cbn [from_option].
    - assert (Hnz : fn_naddr n k <> 0).
      { apply (inl_blk_dom Hl k ltac:(rewrite -MAXFILE_FS; exact Hk)).
        by exists bs. }
      rewrite (decide_False _ _ Hnz).
      rewrite /fn_data Hbs gamma_blk_owned //.
    - assert (Hz : fn_naddr n k = 0).
      { destruct (decide (fn_naddr n k = 0)) as [Hz | Hnz]; [exact Hz |].
        exfalso.
        destruct (proj2 (inl_blk_dom Hl k
                           ltac:(rewrite -MAXFILE_FS; exact Hk)) Hnz)
          as [bs Hbs']. rewrite Hbs' in Hbs. discriminate. }
      rewrite (decide_True _ _ Hz) bi.True_emp //.
  Qed.

  Lemma ind_res_era (γfs : fs_names) (n : fs_node) :
    ind_res γfs (bm_of n) ⊣⊢ ind_owned (fs_gamma_L γfs) n.
  Proof.
    rewrite /ind_res /ind_blk /ind_owned bm_of_ind bm_of_ent.
    (* the two guards are the same proposition but reach the goal through
       two files' [Decision] instances, so they are peeled by [case_decide]
       rather than by a [decide_True] whose instance would have to match
       (durable-notes: two instance terms that print identically) *)
    repeat case_decide; try (exfalso; congruence).
    - rewrite bi.True_emp //.
    - rewrite gamma_blk_owned //.
  Qed.

  (* ---- THE BUNDLE ---------------------------------------------------- *)

  (* THE BYTE LEGS ALONE, AT A SHARE (durable-fs-plan.md sections 4, 6;
     lane B').  A read-locking [ilock] withdraws exactly this at a QUARTER
     and the escrow's "out for reading" arm keeps the bundle at three
     quarters -- which is what makes cross-inode block disjointness at the
     commit's collection pure separation logic (3/4 + 3/4 > 1,
     [FsStateDefs.blk_owned_ne_34]).  The record is NOT here: records park
     region-side at fraction 1 always (plan section 2, ruling (i)). *)
  Definition inode_bytes_era (γfs : fs_names) (dq : dfrac) (n : fs_node)
    : iProp Σ :=
    (([∗ map] k ↦ bs ∈ fn_blk n,
        FsStateDefs.blk_owned_q (fs_gamma_L γfs) dq (fn_naddr n k) bs)
     ∗ ind_owned_q (fs_gamma_L γfs) dq n)%I.

  Definition inode_owned_era_q (γfs : fs_names) (dq : dfrac) (γi : gname)
      (inum : bv 32) (n : fs_node) : iProp Σ :=
    (dinode_at γi inum (fn_rec n)
     ∗ ([∗ map] k ↦ bs ∈ fn_blk n,
          FsStateDefs.blk_owned_q (fs_gamma_L γfs) dq (fn_naddr n k) bs)
     ∗ ind_owned_q (fs_gamma_L γfs) dq n
     ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n
     ∗ ⌜inode_local (bv_unsigned inum) n⌝)%I.

  (* the [DfracOwn 1] reading: today's bundle, text unmoved *)
  Definition inode_owned_era (γfs : fs_names) (γi : gname) (inum : bv 32)
      (n : fs_node) : iProp Σ :=
    (dinode_at γi inum (fn_rec n)
     ∗ ([∗ map] k ↦ bs ∈ fn_blk n,
          FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n k) bs)
     ∗ ind_owned (fs_gamma_L γfs) n
     ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n
     ∗ ⌜inode_local (bv_unsigned inum) n⌝)%I.

  Lemma inode_owned_era_1 γfs γi inum n :
    inode_owned_era γfs γi inum n
    = inode_owned_era_q γfs (DfracOwn 1) γi inum n.
  Proof. reflexivity. Qed.

  Global Instance inode_bytes_era_timeless γfs dq n :
    Timeless (inode_bytes_era γfs dq n).
  Proof.
    rewrite /inode_bytes_era /ind_owned_q.
    destruct (decide (fn_indb n = 0)); apply _.
  Qed.

  Global Instance inode_owned_era_q_timeless γfs dq γi inum n :
    Timeless (inode_owned_era_q γfs dq γi inum n).
  Proof.
    rewrite /inode_owned_era_q /ind_owned_q /top_frag.
    destruct (decide (fn_indb n = 0)); apply _.
  Qed.

  Global Instance inode_owned_era_timeless γfs γi inum n :
    Timeless (inode_owned_era γfs γi inum n).
  Proof.
    rewrite /inode_owned_era /ind_owned /top_frag.
    destruct (decide (fn_indb n = 0)); apply _.
  Qed.

  (* ---- THE READER'S QUARTER, BOTH WAYS ------------------------------- *)

  Local Lemma blk_big_sepM_split γfs (q1 q2 : Qp) n :
    ([∗ map] k ↦ bs ∈ fn_blk n,
       FsStateDefs.blk_owned_q (fs_gamma_L γfs) (DfracOwn (q1 + q2))
         (fn_naddr n k) bs)
    ⊣⊢ ([∗ map] k ↦ bs ∈ fn_blk n,
          FsStateDefs.blk_owned_q (fs_gamma_L γfs) (DfracOwn q1)
            (fn_naddr n k) bs)
        ∗ ([∗ map] k ↦ bs ∈ fn_blk n,
             FsStateDefs.blk_owned_q (fs_gamma_L γfs) (DfracOwn q2)
               (fn_naddr n k) bs).
  Proof.
    rewrite -big_sepM_sep.
    apply big_sepM_proper. intros k bs _.
    apply (blk_owned_q_split _ (fs_gamma_L_frac γfs)).
  Qed.

  Lemma inode_bytes_era_split γfs (q1 q2 : Qp) n :
    inode_bytes_era γfs (DfracOwn (q1 + q2)) n
    ⊣⊢ inode_bytes_era γfs (DfracOwn q1) n ∗ inode_bytes_era γfs (DfracOwn q2) n.
  Proof.
    rewrite /inode_bytes_era blk_big_sepM_split.
    rewrite (ind_owned_q_split _ (fs_gamma_L_frac γfs)).
    iSplit.
    - iIntros "[[Hb1 Hb2] [Hi1 Hi2]]". iFrame.
    - iIntros "[[Hb1 Hi1] [Hb2 Hi2]]". iFrame.
  Qed.

  (* THE ESCROW'S DEPOSIT/WITHDRAW ARITHMETIC: the bundle at [dq1 ⋅ dq2] is
     the bundle at [dq1] beside the byte legs at [dq2].  [ilock] without a
     transaction runs it left to right at [3/4 ⋅ 1/4], [iunlock] right to
     left. *)
  Lemma inode_owned_era_q_split γfs (q1 q2 : Qp) γi inum n :
    inode_owned_era_q γfs (DfracOwn (q1 + q2)) γi inum n
    ⊣⊢ inode_owned_era_q γfs (DfracOwn q1) γi inum n
        ∗ inode_bytes_era γfs (DfracOwn q2) n.
  Proof.
    rewrite /inode_owned_era_q /inode_bytes_era blk_big_sepM_split.
    rewrite (ind_owned_q_split _ (fs_gamma_L_frac γfs)).
    iSplit.
    - iIntros "(Hd & [Hb1 Hb2] & [Hi1 Hi2] & Ht & %Hl)". iFrame. done.
    - iIntros "[(Hd & Hb1 & Hi1 & Ht & %Hl) [Hb2 Hi2]]". iFrame. done.
  Qed.

  Lemma inode_owned_era_shed γfs γi inum n :
    inode_owned_era γfs γi inum n
    ⊣⊢ inode_owned_era_q γfs (DfracOwn (3/4)) γi inum n
        ∗ inode_bytes_era γfs (DfracOwn (1/4)) n.
  Proof.
    rewrite inode_owned_era_1.
    rewrite -(inode_owned_era_q_split γfs (3/4) (1/4)).
    rewrite Qp.three_quarter_quarter //.
  Qed.

  Lemma inode_owned_era_local γfs γi inum n :
    inode_owned_era γfs γi inum n -∗ ⌜inode_local (bv_unsigned inum) n⌝.
  Proof. iIntros "(_ & _ & _ & _ & $)". Qed.

  (* the proxy, lent and returned at the same value: what every accessor
     that only needs to READ the record does *)
  Lemma inode_owned_era_rec γfs γi inum n :
    inode_owned_era γfs γi inum n -∗
      dinode_at γi inum (fn_rec n)
      ∗ (dinode_at γi inum (fn_rec n) -∗ inode_owned_era γfs γi inum n).
  Proof.
    iIntros "(H & Hb & Hi & Ht & %Hl)". iFrame "H". iIntros "H".
    rewrite /inode_owned_era. iFrame. done.
  Qed.

  (* ---- THE OLD PAYLOAD SHAPE, BOTH WAYS ------------------------------ *)

  (* [ic_loaded]/[ipool_alloc] hold [dinode_at] beside [ind_res] and
     [inode_blocks] over an EXISTENTIAL [data]; this is that bundle, at the
     node's own reading of both. *)
  Lemma inode_owned_era_of (γfs : fs_names) (γi : gname) (inum : bv 32)
      (n : fs_node) :
    inode_local (bv_unsigned inum) n ->
    dinode_at γi inum (fn_rec n) -∗
    ind_res γfs (bm_of n) -∗
    inode_blocks γfs (bm_of n) (fn_data n) -∗
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) n -∗
    inode_owned_era γfs γi inum n.
  Proof.
    intros Hl. iIntros "Hd Hi Hb Ht".
    rewrite /inode_owned_era.
    rewrite (inode_blocks_era γfs (bv_unsigned inum) n Hl) ind_res_era.
    iFrame. done.
  Qed.

  Lemma inode_owned_era_to (γfs : fs_names) (γi : gname) (inum : bv 32)
      (n : fs_node) :
    inode_owned_era γfs γi inum n -∗
      dinode_at γi inum (fn_rec n)
      ∗ ind_res γfs (bm_of n)
      ∗ inode_blocks γfs (bm_of n) (fn_data n)
      ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n.
  Proof.
    iIntros "(Hd & Hb & Hi & Ht & %Hl)".
    rewrite (inode_blocks_era γfs (bv_unsigned inum) n Hl) ind_res_era.
    iFrame.
  Qed.

  (* ---- INJECTIVITY IS THE [*] ---------------------------------------- *)

  (* two DIFFERENT owned slots name two DIFFERENT blocks -- [blkmap_wf]'s
     fifth conjunct, read off the ownership and not maintained anywhere.

     AT A SHARE (lane B'): the reading holds of ANY [dq] whose double is
     invalid, so it is available off the escrow's THREE-QUARTER residue of a
     read-locked inode as well as off a full bundle -- which is what the
     commit's collection needs (plan section 4, [blk_owned_ne_34]). *)
  Lemma inode_owned_era_q_slot_inj γfs dq γi inum n :
    ~ ✓ (dq ⋅ dq) ->
    inode_owned_era_q γfs dq γi inum n -∗
    ⌜forall k j : nat, (k <= MAXFILE)%nat -> (j <= MAXFILE)%nat ->
        bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
        bm_slot (bm_of n) k = bm_slot (bm_of n) j -> k = j⌝.
  Proof.
    intros Hnv.
    iIntros "(_ & Hb & Hi & _ & %Hl)".
    iAssert (⌜forall k j : nat, (k <= MAXFILE)%nat -> (j <= MAXFILE)%nat ->
               k <> j ->
               bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
               bv_unsigned (bm_slot (bm_of n) j) <> 0 ->
               bv_unsigned (bm_slot (bm_of n) k)
               <> bv_unsigned (bm_slot (bm_of n) j)⌝)%I as "%Hne".
    { iIntros (k j Hk Hj Hkj Hnk Hnj).
      rewrite (bm_of_slot n k (inl_rec_wf Hl) Hk) in Hnk |- *.
      rewrite (bm_of_slot n j (inl_rec_wf Hl) Hj) in Hnj |- *.
      destruct (decide (k = MAXFILE)) as [Hkm | Hkm];
        destruct (decide (j = MAXFILE)) as [Hjm | Hjm]; [lia | | |].
      - (* k is the indirect block, j a data slot *)
        rewrite /ind_owned_q (decide_False _ _ Hnk).
        destruct (proj2 (inl_blk_dom Hl j
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnj) as [bs Hbs].
        iDestruct (big_sepM_lookup _ _ j bs Hbs with "Hb") as "Hbj".
        iApply (FsStateDefs.blk_owned_q_ne _ (fs_gamma_L_excl γfs) dq dq
                  _ _ _ _ Hnv with "Hi Hbj").
      - (* j is the indirect block, k a data slot *)
        rewrite /ind_owned_q (decide_False _ _ Hnj).
        destruct (proj2 (inl_blk_dom Hl k
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnk) as [bs Hbs].
        iDestruct (big_sepM_lookup _ _ k bs Hbs with "Hb") as "Hbk".
        iApply (FsStateDefs.blk_owned_q_ne _ (fs_gamma_L_excl γfs) dq dq
                  _ _ _ _ Hnv with "Hbk Hi").
      - (* two data slots *)
        destruct (proj2 (inl_blk_dom Hl k
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnk) as [bsk Hbsk].
        destruct (proj2 (inl_blk_dom Hl j
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnj) as [bsj Hbsj].
        iDestruct (big_sepM_delete _ _ k bsk Hbsk with "Hb") as "[Hbk Hrest]".
        assert (Hbsj' : delete k (fn_blk n) !! j = Some bsj)
          by (rewrite lookup_delete_ne; [exact Hbsj | done]).
        iDestruct (big_sepM_lookup _ _ j bsj Hbsj' with "Hrest") as "Hbj".
        iApply (FsStateDefs.blk_owned_q_ne _ (fs_gamma_L_excl γfs) dq dq
                  _ _ _ _ Hnv with "Hbk Hbj"). }
    iPureIntro. intros k j Hk Hj Hnk Heq.
    destruct (decide (k = j)) as [-> | Hkj]; [done |].
    exfalso. apply (Hne k j Hk Hj Hkj Hnk); rewrite -Heq; [exact Hnk |].
    by rewrite Heq.
  Qed.

  Lemma inode_owned_era_slot_inj γfs γi inum n :
    inode_owned_era γfs γi inum n -∗
    ⌜forall k j : nat, (k <= MAXFILE)%nat -> (j <= MAXFILE)%nat ->
        bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
        bm_slot (bm_of n) k = bm_slot (bm_of n) j -> k = j⌝.
  Proof.
    rewrite inode_owned_era_1.
    iApply (inode_owned_era_q_slot_inj γfs (DfracOwn 1) γi inum n
              (dfrac_full_nvalid _)).
  Qed.

  (* the residue a READ-LOCKED inode leaves in its escrow is at three
     quarters, and that is exactly the share at which the reading above
     holds (3/4 + 3/4 > 1) *)
  Lemma inode_owned_era_34_slot_inj γfs γi inum n :
    inode_owned_era_q γfs (DfracOwn (3/4)) γi inum n -∗
    ⌜forall k j : nat, (k <= MAXFILE)%nat -> (j <= MAXFILE)%nat ->
        bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
        bm_slot (bm_of n) k = bm_slot (bm_of n) j -> k = j⌝.
  Proof.
    iApply (inode_owned_era_q_slot_inj γfs (DfracOwn (3/4)) γi inum n
              dfrac_34_nvalid).
  Qed.

  Lemma inode_owned_era_q_local γfs dq γi inum n :
    inode_owned_era_q γfs dq γi inum n -∗ ⌜inode_local (bv_unsigned inum) n⌝.
  Proof. iIntros "(_ & _ & _ & _ & $)". Qed.

  (* ---- THE DATA-BLOCK ACCESSOR AT A SHARE (plan section 3, lane B') ----

     A READ of one slot's bytes takes the caller's fraction and hands it
     straight back; a WRITE cannot use this at all, because
     [SpecLogWrite.wp_log_write_au_range] needs fraction 1 and the borrow
     comes out at whatever [dq] the bundle is at.  That is the resource
     reading of "a read-locker cannot write a data block". *)
  Lemma inode_owned_era_q_blk_read γfs dq γi inum n (k : nat) bs :
    fn_blk n !! k = Some bs ->
    inode_owned_era_q γfs dq γi inum n -∗
      FsStateDefs.blk_owned_q (fs_gamma_L γfs) dq (fn_naddr n k) bs
      ∗ (FsStateDefs.blk_owned_q (fs_gamma_L γfs) dq (fn_naddr n k) bs -∗
           inode_owned_era_q γfs dq γi inum n).
  Proof.
    intros Hbs. iIntros "(Hd & Hb & Hi & Ht & %Hl)".
    iDestruct (big_sepM_delete _ _ k bs Hbs with "Hb") as "[Hbk Hrest]".
    iFrame "Hbk". iIntros "Hbk".
    iDestruct (big_sepM_delete _ _ k bs Hbs) as "[_ Hback]".
    iFrame. iSplitL; [| done]. iApply "Hback". iFrame.
  Qed.

  Lemma inode_bytes_era_blk_read γfs dq n (k : nat) bs :
    fn_blk n !! k = Some bs ->
    inode_bytes_era γfs dq n -∗
      FsStateDefs.blk_owned_q (fs_gamma_L γfs) dq (fn_naddr n k) bs
      ∗ (FsStateDefs.blk_owned_q (fs_gamma_L γfs) dq (fn_naddr n k) bs -∗
           inode_bytes_era γfs dq n).
  Proof.
    intros Hbs. iIntros "[Hb Hi]".
    iDestruct (big_sepM_delete _ _ k bs Hbs with "Hb") as "[Hbk Hrest]".
    iFrame "Hbk". iIntros "Hbk".
    iDestruct (big_sepM_delete _ _ k bs Hbs) as "[_ Hback]".
    iFrame. iApply "Hback". iFrame.
  Qed.

  (* ---- COVERAGE IS A CONSEQUENCE OF OWNING THE RUN -------------------- *)

  (* [blkmap_wf]'s fourth conjunct at ONE slot: "the block is a home block",
     i.e. covered and outside the log's own storage.  It is a fupd at
     [logN] because only the byte view's auth knows the domain -- exactly
     [FsBlocks.fsblock_home_open], which is what the bitmap's allocator
     already uses for the same reason. *)
  Lemma inode_owned_era_home (E : coPset) (γfs : fs_names) (γi : gname)
      (inum : bv 32) (n : fs_node) (home : gset Z) (k : nat) :
    ↑logN ⊆ E ->
    (k <= MAXFILE)%nat ->
    bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) home -∗
    inode_owned_era γfs γi inum n ={E}=∗
      ⌜bv_unsigned (bm_slot (bm_of n) k) ∈ home⌝
      ∗ inode_owned_era γfs γi inum n.
  Proof.
    iIntros (HE Hk Hnz) "#Hinv Hn".
    iDestruct (inode_owned_era_local with "Hn") as %Hl.
    iDestruct (inode_owned_era_to with "Hn") as "(Hd & Hi & Hb & Ht)".
    rewrite (bm_of_slot n k (inl_rec_wf Hl) Hk) in Hnz |- *.
    destruct (decide (k = MAXFILE)) as [-> | Hkm].
    - iEval (rewrite /ind_res /ind_blk bm_of_ind bm_of_ent
                     (decide_False _ _ Hnz)) in "Hi".
      iMod (fsblock_home_open E (fs_bytes γfs) (fs_cache γfs) home
              (fn_indb n) (ind_bytes (fn_ent n)) HE with "Hinv Hi")
        as "[%Hin Hi]".
      iModIntro. iSplitR; [done |].
      iApply (inode_owned_era_of γfs γi inum n Hl with "Hd [Hi] Hb Ht").
      iEval (rewrite /ind_res /ind_blk bm_of_ind bm_of_ent
                     (decide_False _ _ Hnz)).
      iExact "Hi".
    - (* the arithmetic is done with the [bv]s cleared out of the context:
         with one in scope [lia] answers "Cannot find witness" *)
      assert (Hklt : (k < MAXFILE)%nat) by (clear - Hk Hkm; lia).
      assert (Hlk : seq 0 MAXFILE !! k = Some k).
      { clear - Hklt. apply lookup_seq. split; [reflexivity | exact Hklt]. }
      iEval (rewrite /inode_blocks) in "Hb".
      iDestruct (big_sepL_lookup_acc _ _ k k Hlk with "Hb")
        as "[Hbk Hback]".
      iEval (rewrite /blk_res (bm_of_get n k (inl_rec_wf Hl) Hklt)
                     (decide_False _ _ Hnz)) in "Hbk".
      iMod (fsblock_home_open E (fs_bytes γfs) (fs_cache γfs) home
              (fn_naddr n k) (fn_data n k) HE with "Hinv Hbk")
        as "[%Hin Hbk]".
      iModIntro. iSplitR; [done |].
      iApply (inode_owned_era_of γfs γi inum n Hl with "Hd Hi [Hbk Hback] Ht").
      iEval (rewrite /inode_blocks). iApply "Hback".
      iEval (rewrite /blk_res (bm_of_get n k (inl_rec_wf Hl) Hklt)
                     (decide_False _ _ Hnz)).
      iExact "Hbk".
  Qed.

  (* ALL THE SLOTS AT ONCE, IN ONE OPEN -- which is what makes the payload
     flip cheap for readi/writei/bmap/itrunc.  Each of those four takes
     [InodeLock.inode_ok] as a premise and every conjunct of it but this one
     is pure [inode_local] or the [*]; so a walk that holds the bundle pays
     ONE fupd and its callees' contracts do not move.  Opening the byte
     invariant once and reading every slot off the auth is strictly cheaper
     than 269 [fsblock_home_open]s, and it is the only shape that keeps the
     [Prop] a single quantified statement. *)
  Lemma inode_owned_era_home_all (E : coPset) (γfs : fs_names) (γi : gname)
      (inum : bv 32) (n : fs_node) (home : gset Z) :
    ↑logN ⊆ E ->
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) home -∗
    inode_owned_era γfs γi inum n ={E}=∗
      ⌜forall k : nat, (k <= MAXFILE)%nat ->
          bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
          bv_unsigned (bm_slot (bm_of n) k) ∈ home⌝
      ∗ inode_owned_era γfs γi inum n.
  Proof.
    iIntros (HE) "#Hinv Hn".
    iDestruct "Hn" as "(Hd & Hb & Hi & Ht & %Hl)".
    iMod (inv_acc E logN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (L C) ">(Ha & HC & %Hdom & %Hlens & %Htie & %Hdm)".
    iAssert (⌜forall k : nat, (k <= MAXFILE)%nat ->
               bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
               bv_unsigned (bm_slot (bm_of n) k) ∈ home⌝)%I as %Hall.
    { iIntros (k Hk Hnz).
      rewrite (bm_of_slot n k (inl_rec_wf Hl) Hk) in Hnz |- *.
      destruct (decide (k = MAXFILE)) as [-> | Hkm].
      - iEval (rewrite /ind_owned (decide_False _ _ Hnz) gamma_blk_owned)
          in "Hi".
        iApply (fsblock_home (fs_bytes γfs) L home (fn_indb n)
                  (ind_bytes (fn_ent n)) Hdm with "Ha Hi").
      - assert (Hklt : (k < MAXFILE)%nat) by (clear - Hk Hkm; lia).
        destruct (proj2 (inl_blk_dom Hl k
                    ltac:(rewrite -MAXFILE_FS; exact Hklt)) Hnz) as [bs Hbs].
        iDestruct (big_sepM_lookup _ _ k bs Hbs with "Hb") as "Hbk".
        iEval (rewrite gamma_blk_owned) in "Hbk".
        iApply (fsblock_home (fs_bytes γfs) L home (fn_naddr n k) bs Hdm
                  with "Ha Hbk"). }
    iMod ("Hclose" with "[Ha HC]") as "_".
    { iNext. iExists L, C. by iFrame. }
    iModIntro. iSplitR; [done |].
    rewrite /inode_owned_era. iFrame. done.
  Qed.

  (* ...AND THE WHOLE OF [InodeLock.inode_ok], WHICH IS THE POINT.  The
     home set IS [cov] minus the log's own storage ([LogDefs.fs_home_set]),
     so the coverage conjunct's two halves fall out of one [elem_of_difference]
     and nothing new is assumed.  The one fact left over is "this inode is
     allocated" ([di_type <> 0]), which is the payload's own conjunct and
     not a property of the node. *)
  Lemma inode_owned_era_ok (E : coPset) (γfs : fs_names) (γi : gname)
      (inum : bv 32) (n : fs_node) (cov : gset Z) (ls : Z) :
    ↑logN ⊆ E ->
    bv_unsigned (di_type (fn_rec n)) <> 0 ->
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov ls) -∗
    inode_owned_era γfs γi inum n ={E}=∗
      ⌜inode_ok cov ls (fn_rec n) (bm_of n) (fn_data n)⌝
      ∗ inode_owned_era γfs γi inum n.
  Proof.
    iIntros (HE Hty) "#Hinv Hn".
    iDestruct (inode_owned_era_local with "Hn") as %Hl.
    iDestruct (inode_owned_era_slot_inj with "Hn") as %Hinj.
    iMod (inode_owned_era_home_all E γfs γi inum n (fs_home_set cov ls) HE
            with "Hinv Hn") as "[%Hhome Hn]".
    iModIntro. iFrame "Hn". iPureIntro.
    apply (inode_ok_of_local (bv_unsigned inum) n cov ls Hl);
      [| exact Hinj | exact Hty].
    intros k Hk Hnz.
    pose proof (Hhome k Hk Hnz) as Hin.
    rewrite /fs_home_set elem_of_difference in Hin. exact Hin.
  Qed.

  (* ---- THE MOVERS -------------------------------------------------- *)

  (* the definition, as a wand pair, for a caller that wants the pieces *)
  Lemma inode_owned_era_split (γfs : fs_names) (γi : gname) (inum : bv 32)
      (n : fs_node) :
    inode_owned_era γfs γi inum n
    ⊣⊢ dinode_at γi inum (fn_rec n)
        ∗ ([∗ map] k ↦ bs ∈ fn_blk n,
             FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n k) bs)
        ∗ ind_owned (fs_gamma_L γfs) n
        ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n
        ∗ ⌜inode_local (bv_unsigned inum) n⌝.
  Proof. done. Qed.

  (* THE ONE MOVER.  Every change to a checked-out inode -- the record
     write, one data block's bytes, an appended block, a truncation -- is
     "hand back the new node's FOOTPRINT and retag the two ghosts", so it
     is one general lemma and not a family (the guiding principle's rule
     against a cross-product of near-duplicates).  The specialisations
     below are its readings.

     Both authorities are LENT: the region's ([γi]) lives inside [iregN]
     and the top's inside the log's parked payload, so a walk holds neither
     and both arrive at the AU.  [inode_local] of the TARGET is a premise
     -- which of its clauses a given arm has to re-establish is that arm's
     evidence, and writing the cross-product here would be the speculative
     family 2a deliberately did not write. *)
  Lemma inode_owned_era_retag (γfs : fs_names) (γi : gname) (inum : bv 32)
      (R : gmap Z dinode) (I : gmap Z fs_node) (n n' : fs_node) :
    inode_local (bv_unsigned inum) n' ->
    ghost_map_auth γi 1 R -∗
    ghost_map_auth (fs_top γfs) 1 I -∗
    dinode_at γi inum (fn_rec n) -∗
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) n -∗
    ([∗ map] k ↦ bs ∈ fn_blk n',
       FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n' k) bs) -∗
    ind_owned (fs_gamma_L γfs) n' ==∗
      ghost_map_auth γi 1 (<[bv_unsigned inum := fn_rec n']> R)
      ∗ ghost_map_auth (fs_top γfs) 1 (<[bv_unsigned inum := n']> I)
      ∗ inode_owned_era γfs γi inum n'.
  Proof.
    intros Hl'. iIntros "HaR HaI Hd Ht Hb Hi".
    rewrite /dinode_at.
    iMod (ghost_map_update (fn_rec n') with "HaR Hd") as "[HaR Hd]".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (ghost_map_update n' with "HaI Ht") as "[HaI Ht]".
    iModIntro. iFrame "HaR HaI".
    rewrite /inode_owned_era /dinode_at /top_frag /fs_gamma_L /=.
    iFrame "Hd Ht Hb Hi". done.
  Qed.

  (* (a) THE RECORD WRITE -- iupdate, ialloc's retag, the link moves.  The
     addresses may not move at a slot the node ALREADY owns
     ([FsStateInode.fn_addrs_kept]), which still allows attaching a freshly
     allocated block, exactly as [inode_phi_rec_move] does. *)
  Lemma inode_owned_era_rec_upd (γfs : fs_names) (γi : gname) (inum : bv 32)
      (R : gmap Z dinode) (I : gmap Z fs_node) (n n' : fs_node) :
    fn_blk n' = fn_blk n ->
    fn_ent n' = fn_ent n ->
    fn_indb n' = fn_indb n ->
    fn_addrs_kept n n' ->
    inode_local (bv_unsigned inum) n' ->
    ghost_map_auth γi 1 R -∗
    ghost_map_auth (fs_top γfs) 1 I -∗
    inode_owned_era γfs γi inum n ==∗
      ghost_map_auth γi 1 (<[bv_unsigned inum := fn_rec n']> R)
      ∗ ghost_map_auth (fs_top γfs) 1 (<[bv_unsigned inum := n']> I)
      ∗ inode_owned_era γfs γi inum n'.
  Proof.
    intros Hblk Hent Hind Hkept Hl'.
    iIntros "HaR HaI (Hd & Hb & Hi & Ht & %Hl)".
    iApply (inode_owned_era_retag γfs γi inum R I n n' Hl'
              with "HaR HaI Hd Ht [Hb] [Hi]").
    - rewrite Hblk. iApply (big_sepM_mono with "Hb").
      intros k bs Hk; simpl.
      assert (Hs : is_Some (fn_blk n !! k)) by (by exists bs).
      rewrite (Hkept k Hs) //.
    - rewrite /ind_owned Hind Hent. iExact "Hi".
  Qed.

  (* (a') ONE DATA BLOCK, CHECKED OUT AND BACK -- writei's and bmap's AU.
     The two ghosts come out UNTOUCHED (a block write moves neither the
     record nor, through [fn_set_blk], the addressing), so what the caller
     hands the AU is the block alone and what closes the step is
     [inode_owned_era_retag] at [fn_set_blk n k bs'].  Stated with the
     returner quantified over the NEW contents, because the writer does not
     know them until the log's update has run. *)
  Lemma inode_owned_era_blk_acc (γfs : fs_names) (γi : gname) (inum : bv 32)
      (n : fs_node) (k : nat) (bs : list (bv 8)) :
    fn_blk n !! k = Some bs ->
    inode_owned_era γfs γi inum n -∗
      FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n k) bs
      ∗ dinode_at γi inum (fn_rec n)
      ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n
      ∗ ind_owned (fs_gamma_L γfs) (fn_set_blk n k bs)
      ∗ (∀ bs' : list (bv 8),
           FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n k) bs' -∗
           [∗ map] j ↦ b ∈ fn_blk (fn_set_blk n k bs'),
             FsStateDefs.blk_owned (fs_gamma_L γfs)
               (fn_naddr (fn_set_blk n k bs') j) b).
  Proof.
    intros Hk. iIntros "(Hd & Hb & Hi & Ht & %Hl)".
    iDestruct (big_sepM_insert_acc _ _ k bs Hk with "Hb") as "[Hbk Hback]".
    iFrame "Hbk Hd Ht".
    iSplitL "Hi"; [rewrite /ind_owned /fn_set_blk /=; iExact "Hi" |].
    iIntros (bs') "Hbk'".
    rewrite /fn_set_blk /= fn_naddr_set_blk.
    iApply ("Hback" with "Hbk'").
  Qed.

  (* (b) THE TRUNCATION -- [SpecItrunc]'s post, as the [fn_blk = ∅] node.
     "Frees every owned block" is DEFINITIONAL here, which is the F3 ruling
     built into the representation: the blocks the caller gets back to hand
     [FsStateBitmap.bitmap_free] are exactly [fn_blk n]'s, INCLUDING the
     ones beyond the size, and the old indirect block comes with them. *)
  Lemma inode_owned_era_trunc (γfs : fs_names) (γi : gname) (inum : bv 32)
      (R : gmap Z dinode) (I : gmap Z fs_node) (n n' : fs_node) :
    fn_blk n' = ∅ ->
    fn_indb n' = 0 ->
    inode_local (bv_unsigned inum) n' ->
    ghost_map_auth γi 1 R -∗
    ghost_map_auth (fs_top γfs) 1 I -∗
    inode_owned_era γfs γi inum n ==∗
      ghost_map_auth γi 1 (<[bv_unsigned inum := fn_rec n']> R)
      ∗ ghost_map_auth (fs_top γfs) 1 (<[bv_unsigned inum := n']> I)
      ∗ ([∗ map] k ↦ bs ∈ fn_blk n,
           FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n k) bs)
      ∗ ind_owned (fs_gamma_L γfs) n
      ∗ inode_owned_era γfs γi inum n'.
  Proof.
    intros Hblk Hind Hl'.
    iIntros "HaR HaI (Hd & Hb & Hi & Ht & %Hl)".
    iMod (inode_owned_era_retag γfs γi inum R I n n' Hl'
            with "HaR HaI Hd Ht [] []") as "(HaR & HaI & Hn)".
    { rewrite Hblk big_sepM_empty. done. }
    { rewrite /ind_owned (decide_True _ _ Hind). done. }
    iModIntro. iFrame.
  Qed.

  (* ---- THE PAYLOAD'S SPELLING OF THE BUNDLE -------------------------- *)

  (* [IcacheEscrow]'s payloads name a record, a block map and a total
     [data] and the node is [era_node] of the three; these three lemmas are
     that spelling of [_to] / [_of] / [_ok], and they are what every
     consumer of a payload actually applies.  Each takes only
     [node_shape_ok], which every producer reads off its own
     [inode_ok]. *)

  Lemma inode_blocks_data_ext (γfs : fs_names) (bm : blkmap)
      (data data' : nat -> list (bv 8)) :
    (forall k : nat, (k < MAXFILE)%nat -> data k = data' k) ->
    inode_blocks γfs bm data ⊣⊢ inode_blocks γfs bm data'.
  Proof.
    intros Hext. rewrite /inode_blocks.
    apply big_sepL_proper. intros j k Hj.
    apply lookup_seq in Hj as [Heq Hlt].
    assert (Hk : (k < MAXFILE)%nat) by lia.
    rewrite (Hext k Hk) //.
  Qed.

  Lemma inode_owned_era_era_node_to (γfs : fs_names) (γi : gname) (inum : bv 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    node_shape_ok dn bm data ->
    inode_owned_era γfs γi inum (era_node dn bm data) -∗
      dinode_at γi inum dn
      ∗ ind_res γfs bm
      ∗ inode_blocks γfs bm data
      ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data).
  Proof.
    intros Hs. iIntros "Hn".
    iDestruct (inode_owned_era_to with "Hn") as "(Hd & Hi & Hb & Ht)".
    rewrite (bm_of_era_node dn bm data Hs).
    rewrite (inode_blocks_data_ext γfs bm (fn_data (era_node dn bm data)) data
               (fun k Hk => fn_data_era_node dn bm data k Hs Hk)).
    iFrame.
  Qed.

  Lemma inode_owned_era_era_node_of (γfs : fs_names) (γi : gname) (inum : bv 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    node_shape_ok dn bm data ->
    inode_local (bv_unsigned inum) (era_node dn bm data) ->
    dinode_at γi inum dn -∗
    ind_res γfs bm -∗
    inode_blocks γfs bm data -∗
    top_frag (fs_gamma_L γfs) (bv_unsigned inum) (era_node dn bm data) -∗
    inode_owned_era γfs γi inum (era_node dn bm data).
  Proof.
    intros Hs Hl. iIntros "Hd Hi Hb Ht".
    iApply (inode_owned_era_of γfs γi inum (era_node dn bm data) Hl
              with "[Hd] [Hi] [Hb] Ht").
    - iExact "Hd".
    - rewrite (bm_of_era_node dn bm data Hs). iExact "Hi".
    - rewrite (bm_of_era_node dn bm data Hs).
      rewrite (inode_blocks_data_ext γfs bm (fn_data (era_node dn bm data)) data
                 (fun k Hk => fn_data_era_node dn bm data k Hs Hk)).
      iExact "Hb".
  Qed.

  (* the whole of [InodeLock.inode_ok], at the payload's own spelling --
     one fupd at [logN], which is what keeps a payload from having to
     MAINTAIN the coverage sweep and the injectivity *)
  Lemma inode_owned_era_era_node_ok (E : coPset) (γfs : fs_names) (γi : gname)
      (inum : bv 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) (cov : gset Z) (ls : Z) :
    ↑logN ⊆ E ->
    node_shape_ok dn bm data ->
    bv_unsigned (di_type dn) <> 0 ->
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov ls) -∗
    inode_owned_era γfs γi inum (era_node dn bm data) ={E}=∗
      ⌜inode_ok cov ls dn bm data⌝
      ∗ inode_owned_era γfs γi inum (era_node dn bm data).
  Proof.
    iIntros (HE Hs Hty) "#Hinv Hn".
    assert (Hty' : bv_unsigned (di_type (fn_rec (era_node dn bm data))) <> 0)
      by exact Hty.
    iMod (inode_owned_era_ok E γfs γi inum (era_node dn bm data) cov ls HE Hty'
            with "Hinv Hn") as "[%Hok Hn]".
    iModIntro. iFrame "Hn". iPureIntro.
    rewrite (bm_of_era_node dn bm data Hs) in Hok.
    apply (inode_ok_data_ext cov ls dn bm (fn_data (era_node dn bm data)) data);
      [| exact Hok].
    intros k Hk. exact (fn_data_era_node dn bm data k Hs Hk).
  Qed.

  (* ==================================================================== *)
  (*  THE LINK TOKENS OF A CHECKED-OUT DIRECTORY (durable-disk 2b-inode-4) *)
  (* ==================================================================== *)

  (*  A holder owns the TOKENS its own directory records file against other
      inums -- [FsStateInode.ent_toks] at the payload's own node -- and it
      does NOT own the per-inum AUTHORITY.  That stays with the RECORD, i.e.
      in the inode region ([InodeRegion.ireg_slot], tied to [di_nlink] of
      the slot's own record), which is 2b-inode-1's ruling (i) applied to
      the ghost that mirrors a record FIELD.  Two things force it and
      neither is a placement preference:

      - [IgetLic]'s licence (a) is "a directory record names this inum and
        PAYS for it".  Reading allocatedness off it is the RA's law
        ([FsStateLink.link_auth_toks_le]) at the TARGET's authority, and the
        target is an inode the presenter does not hold.  With the authority
        in the target's own payload nothing in the tree can reach it, and
        the licence -- hence [SpecIget]'s premise -- has no discharge.
        Region-side, the reading is one [inv_acc] of [iregN], which is
        exactly where the pure clause (L1) it replaces was read.
      - Every move of a count is a FLUSH ([iupdate]), which already opens
        the region to write the record; [link_mint]/[link_return] are basic
        updates, so they compose into that AU at no mask cost.

      The tokens are [ent_toks] verbatim; this section only carries the two
      congruences a payload needs, since a payload binds its [data]
      existentially and re-parks at a different one. *)

  (* the two shapes a payload producer of a NON-directory (or of a record
     with no entries at all) discharges the conjunct with *)
  Lemma ent_toks_era_not_dir (Γ : fs_view_names Σ) (i : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) <> T_DIR_z ->
    ⊢ ent_toks Γ i (era_node dn bm data).
  Proof.
    intros Hne. apply ent_toks_not_dir.
    rewrite /fn_is_dir /fn_type era_node_rec.
    apply bool_decide_eq_false_2. exact Hne.
  Qed.

  Lemma ent_toks_era_nrec0 (Γ : fs_view_names Σ) (i : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    dir_nrec (bv_unsigned (di_size dn)) = 0%nat ->
    ⊢ ent_toks Γ i (era_node dn bm data).
  Proof.
    intros H. apply ent_toks_nrec0.
    rewrite /fn_nrec /fn_size era_node_rec H //.
  Qed.

  Lemma ent_toks_era_size0 (Γ : fs_view_names Σ) (i : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    bv_unsigned (di_size dn) = 0 ->
    ⊢ ent_toks Γ i (era_node dn bm data).
  Proof.
    intros Hsz. apply ent_toks_nrec0.
    rewrite /fn_nrec /fn_size era_node_rec Hsz /dir_nrec //.
  Qed.

  (* ---- THE DIRLINK MOVE, AT THE PAYLOAD'S OWN [data] ---------------- *)

  (*  A directory's tokens are keyed by NAME, so a [dirlink] moves exactly
      ONE of them: the entry map gains [s |-> inum] and nothing else.  The
      two lemmas below are the two arms [SpecDirlink]'s [tot = 0 \/ tot =
      16] offers, stated over the premises the walk actually holds (the
      record delta, the size max and the range clause), so that a call site
      is one [iDestruct] and no view equation is ever restated there.

      The record-count arithmetic is [DirView.dir_uniq_dirlink]'s verbatim:
      at [k0 < nrec] the write reuses a free record and the count is
      unmoved; at [k0 = nrec] it appends and the count grows by exactly
      one, which is what makes the "records the count grew over are dead"
      clause of [FsTree.dir_insert_at] vacuous. *)

  Lemma dir_view_dirlink (dn dn' : dinode) (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : fname) (nrec k0 : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    k0 = dir_slot data nrec ->
    (length s <= 14)%nat -> nonul s ->
    inum <> bv_0 16 ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + 16)) ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + 16)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    dir_first data nrec s = None ->
    dir_view data' (dir_nrec (bv_unsigned (di_size dn')))
    = <[s := bv_unsigned inum]> (dir_view data nrec).
  Proof.
    intros Hnrec Hk0 Hlen Hs Hnz Hsz Hrng Hnone.
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    assert (Hsznn' : 0 <= bv_unsigned (di_size dn'))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn'))).
    destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
    destruct (dir_nrec_range (bv_unsigned (di_size dn')) Hsznn')
      as [Hnr1' Hnr2'].
    rewrite <- Hnrec in Hnr1, Hnr2.
    assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
    set (nrec' := dir_nrec (bv_unsigned (di_size dn'))).
    assert (Hcle : (nrec <= nrec')%nat) by (unfold nrec'; lia).
    assert (Hk0lt : (k0 < nrec')%nat) by (unfold nrec'; lia).
    assert (Hwin : forall j : nat, (j < 16)%nat ->
              file_byte data' (16 * k0 + j)%nat
              = dirent_bytes (de_of_name inum s) !!! j).
    { intros j Hj. rewrite (Hrng (16 * k0 + j)%nat).
      rewrite decide_True; [| lia].
      replace (16 * k0 + j - 16 * k0)%nat with j by lia. reflexivity. }
    destruct (dir_record_of_name data' k0 inum s Hlen Hs Hwin) as [Hrin Hrnm].
    assert (Hwrit : dir_written_at data data' k0 s inum).
    { split; [exact Hrin | split].
      - unfold dir_bname. exact Hrnm.
      - intros q Hq j Hj. rewrite (Hrng (16 * q + j)%nat).
        rewrite decide_False; [reflexivity |].
        intros [Hlo Hhi]. apply Hq. lia. }
    assert (Hfree : (k0 < nrec)%nat -> ~ dir_live data k0).
    { intros Hlt Hlv. apply Hlv.
      rewrite Hk0. apply dir_slot_free. rewrite <- Hk0. exact Hlt. }
    assert (Hdead : forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 ->
                      ~ dir_live data' r).
    { intros r Hr Hrk. exfalso. unfold nrec' in Hr. lia. }
    apply (dir_view_insert data data' nrec nrec' k0 s inum Hnone).
    split; [exact Hcle | split; [exact Hk0lt | split; [exact Hfree |
      split; [exact Hdead | split; [exact Hnz | exact Hwrit]]]]].
  Qed.

  (* ...AND THE CORNER WHERE THE WRITTEN INUM IS ZERO.  [SpecDirlink]'s
     post does not say the linked inum is nonzero, and no walk in this
     tree carries that fact -- so the move has to be true anyway.  It is:
     a record whose two inum bytes are zero is DEAD, so the entry map does
     not gain the name and the token is simply dropped, exactly as
     [DirLinks.dir_link_at_dirlink] drops its ticket at the same corner. *)
  Lemma dir_view_dead_write (data data' : nat -> list (bv 8))
      (nrec nrec' k0 : nat) :
    (nrec <= nrec')%nat ->
    (forall r : nat, (nrec <= r < nrec')%nat -> r <> k0 -> ~ dir_live data' r) ->
    ~ dir_live data' k0 ->
    (forall q : nat, q <> k0 -> dir_win_agree data data' q) ->
    ((k0 < nrec)%nat -> ~ dir_live data k0) ->
    dir_view data' nrec' = dir_view data nrec.
  Proof.
    intros Hle Hdead Hk0dead Hagr Hfree.
    assert (Hf : forall x : fname,
              dir_first data' nrec' x = dir_first data nrec x).
    { intros x. unfold dir_first.
      rewrite (dfirst_trunc (fun k => dir_matchb data' k x) nrec nrec' Hle).
      2:{ intros r Hr. apply dir_matchb_false. intros [Hlv _].
          destruct (decide (r = k0)) as [-> | Hrk];
            [exact (Hk0dead Hlv) | exact (Hdead r Hr Hrk Hlv)]. }
      apply dfirst_ext. intros j Hj.
      destruct (decide (j = k0)) as [-> | Hjk].
      - rewrite (proj2 (dir_matchb_false data' k0 x)
                   ltac:(intros [Hlv _]; exact (Hk0dead Hlv))).
        symmetry. apply dir_matchb_false. intros [Hlv _]. exact (Hfree Hj Hlv).
      - exact (dir_matchb_agree data data' j x (Hagr j Hjk)). }
    apply map_eq. intros x. rewrite !dir_view_lookup Hf.
    destruct (dir_first data nrec x) as [k |] eqn:E;
      cbn [fmap option_fmap option_map]; [| reflexivity].
    apply dir_first_Some in E as (Hk & [Hlv _] & _).
    assert (Hkk : k <> k0) by (intros ->; exact (Hfree Hk Hlv)).
    rewrite (dir_inum_agree data data' k (Hagr k Hkk)) //.
  Qed.

  (* ...and the node-level move: one token IN, at the name the record now
     carries. *)
  Lemma ent_toks_dirlink (Γ : fs_view_names Σ) (i : Z)
      (dn dn' : dinode) (bm bm' : blkmap)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : fname) (nrec k0 : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    k0 = dir_slot data nrec ->
    (length s <= 14)%nat -> nonul s ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    di_type dn' = di_type dn ->
    di_nlink dn' = di_nlink dn ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + 16)) ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + 16)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    dir_first data nrec s = None ->
    blk_holes_zero bm data -> blk_holes_zero bm' data' ->
    bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    ent_toks Γ i (era_node dn bm data) -∗
    ent_tok Γ i (fn_orphan (era_node dn bm data)) s (bv_unsigned inum) -∗
    ent_toks Γ i (era_node dn' bm' data').
  Proof.
    intros Hnrec Hk0 Hlen Hs Hty Hty' Hnl Hsz Hrng Hnone Hh Hh' Hb Hb'.
    assert (Hents : dir_entries (era_node dn bm data) = dir_view data nrec).
    { rewrite (dir_entries_era_node dn bm data Hh Hb)
        (bool_decide_eq_true_2 _ Hty) Hnrec //. }
    assert (Hty2 : bv_unsigned (di_type dn') = T_DIR_z)
      by (rewrite Hty'; exact Hty).
    assert (Horph : fn_orphan (era_node dn' bm' data')
                    = fn_orphan (era_node dn bm data))
      by (rewrite /fn_orphan /fn_nlink !era_node_rec Hnl //).
    destruct (decide (inum = bv_0 16)) as [Hz | Hnz].
    - (* the written record is DEAD: nothing is inserted and the unit is
         dropped *)
      assert (Hsznn : 0 <= bv_unsigned (di_size dn))
        by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
      assert (Hsznn' : 0 <= bv_unsigned (di_size dn'))
        by exact (proj1 (bv_unsigned_in_range _ (di_size dn'))).
      destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
      destruct (dir_nrec_range (bv_unsigned (di_size dn')) Hsznn')
        as [Hnr1' Hnr2'].
      rewrite <- Hnrec in Hnr1, Hnr2.
      assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
      assert (Hwin : forall j : nat, (j < 16)%nat ->
                file_byte data' (16 * k0 + j)%nat
                = dirent_bytes (de_of_name inum s) !!! j).
      { intros j Hj. rewrite (Hrng (16 * k0 + j)%nat).
        rewrite decide_True; [| lia].
        replace (16 * k0 + j - 16 * k0)%nat with j by lia. reflexivity. }
      destruct (dir_record_of_name data' k0 inum s Hlen Hs Hwin) as [Hrin _].
      assert (Hk0dead : ~ dir_live data' k0)
        by (rewrite /dir_live Hrin Hz; intros Hc; exact (Hc eq_refl)).
      assert (Hagr : forall q : nat, q <> k0 -> dir_win_agree data data' q).
      { intros q Hq j Hj. rewrite (Hrng (16 * q + j)%nat).
        rewrite decide_False; [reflexivity |]. intros [Hlo Hhi]. apply Hq. lia. }
      assert (Hfree : (k0 < nrec)%nat -> ~ dir_live data k0).
      { intros Hlt Hlv. apply Hlv.
        rewrite Hk0. apply dir_slot_free. rewrite <- Hk0. exact Hlt. }
      assert (Hdead : forall r : nat,
                (nrec <= r < dir_nrec (bv_unsigned (di_size dn')))%nat ->
                r <> k0 -> ~ dir_live data' r)
        by (intros r Hr Hrk; exfalso; lia).
      assert (Hcle : (nrec <= dir_nrec (bv_unsigned (di_size dn')))%nat) by lia.
      assert (Hents' : dir_entries (era_node dn' bm' data')
                       = dir_view data nrec).
      { rewrite (dir_entries_era_node dn' bm' data' Hh' Hb')
          (bool_decide_eq_true_2 _ Hty2).
        exact (dir_view_dead_write data data' nrec
                 (dir_nrec (bv_unsigned (di_size dn'))) k0
                 Hcle Hdead Hk0dead Hagr Hfree). }
      rewrite /ent_toks Hents Hents' Horph. iIntros "H _"; iExact "H".
    - assert (Hents' : dir_entries (era_node dn' bm' data')
                       = <[s := bv_unsigned inum]> (dir_view data nrec)).
      { rewrite (dir_entries_era_node dn' bm' data' Hh' Hb')
          (bool_decide_eq_true_2 _ Hty2).
        exact (dir_view_dirlink dn dn' data data' inum s nrec k0
                 Hnrec Hk0 Hlen Hs Hnz Hsz Hrng Hnone). }
      assert (Hfresh : dir_view data nrec !! s = None)
        by (apply dir_view_lookup_None; exact Hnone).
      rewrite /ent_toks Hents Hents' Horph.
      rewrite big_sepM_insert; [| exact Hfresh].
      iIntros "H Ht". iFrame.
  Qed.

  (* THE NO-WRITE ARM ([tot = 0]): the bytes did not move and neither did
     the record count, so the entry map -- hence the token map -- is the
     same one.  The [then] branch of the range clause is a PARAMETER, so a
     caller passes its own without restating it. *)
  Lemma ent_toks_dirlink_nop (Γ : fs_view_names Σ) (i : Z)
      (dn dn' : dinode) (bm bm' : blkmap)
      (data data' : nat -> list (bv 8)) (f : nat -> bv 8)
      (nrec k0 tot : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    (k0 <= nrec)%nat -> tot = 0%nat ->
    di_type dn' = di_type dn ->
    di_nlink dn' = di_nlink dn ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then f (x - 16 * k0)%nat
         else file_byte data x) ->
    blk_holes_zero bm data -> blk_holes_zero bm' data' ->
    bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    ent_toks Γ i (era_node dn bm data) -∗
    ent_toks Γ i (era_node dn' bm' data').
  Proof.
    intros Hnrec Hk0le Htot Hty Hnl Hsz Hrng Hh Hh' Hb Hb'. subst tot.
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
    rewrite <- Hnrec in Hnr1, Hnr2.
    assert (Hszeq : bv_unsigned (di_size dn') = bv_unsigned (di_size dn))
      by (rewrite Hsz; lia).
    assert (Hbytes : forall x : nat, file_byte data' x = file_byte data x).
    { intros x. rewrite (Hrng x). rewrite decide_False; [reflexivity | lia]. }
    assert (Hents : dir_entries (era_node dn' bm' data')
                    = dir_entries (era_node dn bm data)).
    { rewrite (dir_entries_era_node dn bm data Hh Hb)
        (dir_entries_era_node dn' bm' data' Hh' Hb') Hty Hszeq.
      destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z));
        [| reflexivity].
      apply dir_view_data_ext. intros y _. exact (Hbytes y). }
    assert (Horph : fn_orphan (era_node dn' bm' data')
                    = fn_orphan (era_node dn bm data))
      by (rewrite /fn_orphan /fn_nlink !era_node_rec Hnl //).
    rewrite (ent_toks_cong_ent Γ i (era_node dn bm data)
               (era_node dn' bm' data') Horph Hents).
    iIntros "H"; iExact "H".
  Qed.

  (* ---- THE ORPHAN's OWN TOKENS ARE NONE (durable-disk 2b-inode-5) --- *)

  (*  An ORPHANED directory -- one whose count has reached zero -- owns no
      tokens at all, which is what lets create's [fail:] arm park the grey
      child it has just zeroed.  Two clauses pay for it and the walk holds
      both: [DirView.dir_orphan_clean]'s [dir_dots_only] (an orphan's live
      records are named ["."] or [".."]) and the ["."]-names-self fact the
      write that put it there established.  ["."] is exempt as a SELF
      record and [".."] as an orphan's; nothing else is live. *)
  Lemma ent_toks_era_dots_only (Γ : fs_view_names Σ) (i : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn) = 0 ->
    blk_holes_zero bm data ->
    bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    dir_dots_only dn data ->
    ⊢ ent_toks Γ i (era_node dn bm data).
  Proof.
    intros Hz Hh Hb Hdots.
    rewrite /ent_toks (fn_orphan_era_z dn bm data Hz).
    rewrite (dir_entries_era_node dn bm data Hh Hb).
    destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z));
      [| rewrite big_sepM_empty; done].
    iApply big_sepM_intro. iModIntro. iIntros (s t Hst).
    destruct (dv_lookup_some_inv _ data (dir_nrec (bv_unsigned (di_size dn)))
                s t eq_refl Hst) as (k & _ & Hk & Hlv & Hnm & Hin).
    rewrite /ent_tok /ent_tokenless.
    destruct (Hdots k Hk Hlv) as [Hd | Hdd].
    - (* ["."] -- the orphan's own *)
      assert (Hs : s = DOT) by (rewrite -Hnm; exact Hd).
      rewrite (bool_decide_eq_true_2 (s = DOT) Hs) orb_true_l andb_true_l
        orb_true_r //.
    - (* [".."] -- likewise *)
      assert (Hs : s = DOTDOT) by (rewrite -Hnm; exact Hdd).
      rewrite (bool_decide_eq_true_2 (s = DOTDOT) Hs) orb_true_r andb_true_l
        orb_true_r //.
  Qed.

  (* ---- THE COUNT-ONLY MOVE (durable-disk 2b-inode-5) ---------------- *)

  (*  A flush that moves ONLY [di_nlink] leaves the entry map alone, so the
      token map rides -- provided the record does not cross the ORPHAN
      boundary in either direction, which is what the two nonzero premises
      say.  This is what create's mkdir arm needs between the [dirlink] that
      appends the parent's record and the [dp->nlink++] fused with it. *)
  Lemma ent_toks_era_nlink (Γ : fs_view_names Σ) (i : Z)
      (dn dn' : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    di_type dn' = di_type dn -> di_size dn' = di_size dn ->
    bv_unsigned (di_nlink dn) <> 0 -> bv_unsigned (di_nlink dn') <> 0 ->
    ent_toks Γ i (era_node dn bm data) -∗
    ent_toks Γ i (era_node dn' bm data).
  Proof.
    intros Hty Hsz Hnz Hnz'.
    assert (Hents : dir_entries (era_node dn' bm data)
                    = dir_entries (era_node dn bm data))
      by (rewrite /dir_entries /fn_is_dir /fn_type /fn_nrec /fn_size /fn_data
            !era_node_rec Hty Hsz //).
    assert (Horph : fn_orphan (era_node dn' bm data)
                    = fn_orphan (era_node dn bm data))
      by (rewrite (fn_orphan_era_nz dn bm data Hnz)
                  (fn_orphan_era_nz dn' bm data Hnz') //).
    rewrite (ent_toks_cong_ent Γ i (era_node dn bm data)
               (era_node dn' bm data) Horph Hents).
    iIntros "H"; iExact "H".
  Qed.

  (* ---- THE ORPHAN MOVE, rmdir's (durable-disk 2b-inode-5) ----------- *)

  (*  When sys_unlink drops a DIRECTORY's name, the directory's own count
      reaches zero and its [".."] becomes TOKENLESS -- the parent takes that
      token back, which is exactly what pays for the parent's own
      [dp->nlink--].  What is left behind is this kernel's grey [".."]
      (fs-icache.md section 20), and in this design it is not a second
      colour but the ABSENCE of a token.

      [t <> i] is the SELF-PARENT exclusion: a directory whose [".."] names
      ITSELF is the root, which carries no token to hand back and which no
      kernel path orphans anyway.  sys_unlink has it as [dp <> ip]. *)
  Lemma ent_toks_era_orphan (Γ : fs_view_names Σ) (i : Z)
      (dn dn' : dinode) (bm : blkmap) (data : nat -> list (bv 8)) (t : Z) :
    di_type dn' = di_type dn -> di_size dn' = di_size dn ->
    bv_unsigned (di_nlink dn) <> 0 -> bv_unsigned (di_nlink dn') = 0 ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    blk_holes_zero bm data ->
    bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))) ->
    (1 < dir_nrec (bv_unsigned (di_size dn)))%nat ->
    dir_live data 1%nat ->
    dir_bname data 1%nat = DOTDOT ->
    bv_unsigned (dir_inum data 1%nat) = t ->
    t <> i ->
    ent_toks Γ i (era_node dn bm data) -∗
    link_tok Γ t ∗ ent_toks Γ i (era_node dn' bm data).
  Proof.
    intros Hty Hsz Hnz Hz Htyd Hh Hb Hu Hnr Hlv Hnm Hin Hne.
    assert (Hents : dir_entries (era_node dn' bm data)
                    = dir_entries (era_node dn bm data))
      by (rewrite /dir_entries /fn_is_dir /fn_type /fn_nrec /fn_size /fn_data
            !era_node_rec Hty Hsz //).
    assert (Hlk : dir_entries (era_node dn bm data) !! DOTDOT = Some t).
    { rewrite (dir_entries_era_node dn bm data Hh Hb)
        (bool_decide_eq_true_2 _ Htyd).
      rewrite -Hnm -Hin. exact (dir_view_live data _ 1%nat Hu Hnr Hlv). }
    exact (ent_toks_orphan Γ i (era_node dn bm data) (era_node dn' bm data) t
             Hents (fn_orphan_era_nz dn bm data Hnz)
             (fn_orphan_era_z dn' bm data Hz) Hlk Hne).
  Qed.

  (* ---- THE UNLINK MOVE (durable-disk 2b-inode-5) -------------------- *)

  (*  sys_unlink's [memset(&de,0,sizeof(de)); writei(...)] kills ONE record,
      so the entry map loses ONE name and the token that entry carried comes
      OUT -- to the [ip->nlink--] flush that pays for it
      ([InodeRegion.ireg_write_unlink_fl]).  The premise list is the one the
      walk already holds for [DirLinks.dir_links_unlink] and
      [DirView.dir_uniq_zero]: the zeroing delta, uniqueness, the record's
      index and liveness, and the record delta.

      [t <> i] is the SELF-record exclusion, and it is the walk's own: at a
      self record the entry is TOKENLESS ([FsStateInode.ent_tokenless]) and
      there would be nothing to hand back.  sys_unlink's two [namecmp]
      refusals leave it. *)
  Lemma ent_toks_unlink (Γ : fs_view_names Σ) (i : Z)
      (dn dn' : dinode) (bm bm' : blkmap)
      (data data' : nat -> list (bv 8)) (k0 : nat) :
    (k0 < dir_nrec (bv_unsigned (di_size dn)))%nat ->
    dir_live data k0 ->
    bv_unsigned (dir_inum data k0) <> i ->
    dir_bname data k0 <> DOT ->
    dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))) ->
    dir_zeroed_at data data' k0 ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    bv_unsigned (di_nlink dn) <> 0 ->
    bv_unsigned (di_nlink dn') <> 0 ->
    di_type dn' = di_type dn ->
    di_size dn' = di_size dn ->
    blk_holes_zero bm data -> blk_holes_zero bm' data' ->
    bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    ent_toks Γ i (era_node dn bm data) -∗
    link_tok Γ (bv_unsigned (dir_inum data k0))
    ∗ ent_toks Γ i (era_node dn' bm' data').
  Proof.
    intros Hk0 Hlive Hne Hnd Hu Hzer Hty Hnz Hnz' Hty' Hsz Hh Hh' Hb.
    assert (Hb' : bv_unsigned (di_size dn')
                  <= Z.of_nat MAXFILE * Z.of_nat BSIZE) by (rewrite Hsz; exact Hb).
    assert (Hty2 : bv_unsigned (di_type dn') = T_DIR_z)
      by (rewrite Hty'; exact Hty).
    assert (Hents : dir_entries (era_node dn bm data)
                    = dir_view data (dir_nrec (bv_unsigned (di_size dn)))).
    { rewrite (dir_entries_era_node dn bm data Hh Hb)
        (bool_decide_eq_true_2 _ Hty) //. }
    assert (Hents' : dir_entries (era_node dn' bm' data')
                     = delete (dir_bname data k0)
                         (dir_view data (dir_nrec (bv_unsigned (di_size dn))))).
    { rewrite (dir_entries_era_node dn' bm' data' Hh' Hb')
        (bool_decide_eq_true_2 _ Hty2) Hsz.
      exact (dir_view_zero data data' _ k0 Hu Hk0 Hlive Hzer). }
    assert (Horph : fn_orphan (era_node dn' bm' data')
                    = fn_orphan (era_node dn bm data))
      by (rewrite (fn_orphan_era_nz dn bm data Hnz)
                  (fn_orphan_era_nz dn' bm' data' Hnz') //).
    assert (Hlk : dir_view data (dir_nrec (bv_unsigned (di_size dn)))
                    !! dir_bname data k0
                  = Some (bv_unsigned (dir_inum data k0)))
      by exact (dir_view_live data _ k0 Hu Hk0 Hlive).
    iIntros "H".
    iDestruct (ent_toks_delete Γ i (era_node dn bm data) (era_node dn' bm' data')
                 (dir_bname data k0) (bv_unsigned (dir_inum data k0))
                 Horph ltac:(rewrite Hents; exact Hlk)
                 ltac:(rewrite Hents Hents'; reflexivity) with "H") as "[Ht $]".
    rewrite (ent_tok_ne Γ i (fn_orphan (era_node dn bm data))
               (dir_bname data k0) (bv_unsigned (dir_inum data k0)) Hne
               (fn_orphan_era_nz dn bm data Hnz)).
    iExact "Ht".
  Qed.

  (* **THE FORM A WALK APPLIES**, and its premise list is
     [DirView.dir_uniq_dirlink]'s verbatim: the two arms
     [SpecDirlink]'s relay of writei's single-block atomicity offers, the
     record delta, the size max and the range clause -- all at the walk's
     own [tot], so a call site restates nothing.  The token goes in at
     [tot = 16] and is dropped at [tot = 0], where nothing was written. *)
  Lemma ent_toks_dirlink_arm (Γ : fs_view_names Σ) (i : Z)
      (dn dn' : dinode) (bm bm' : blkmap)
      (data data' : nat -> list (bv 8))
      (inum : bv 16) (s : fname) (nrec k0 tot : nat) :
    nrec = dir_nrec (bv_unsigned (di_size dn)) ->
    k0 = dir_slot data nrec ->
    (tot = 0%nat \/ tot = 16%nat) ->
    (length s <= 14)%nat -> nonul s ->
    bv_unsigned (di_type dn) = T_DIR_z ->
    di_type dn' = di_type dn ->
    di_nlink dn' = di_nlink dn ->
    bv_unsigned (di_size dn')
      = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
    (forall x : nat,
       file_byte data' x
       = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
         then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
         else file_byte data x) ->
    dir_first data nrec s = None ->
    blk_holes_zero bm data -> blk_holes_zero bm' data' ->
    bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    ent_toks Γ i (era_node dn bm data) -∗
    ent_tok Γ i (fn_orphan (era_node dn bm data)) s (bv_unsigned inum) -∗
    ent_toks Γ i (era_node dn' bm' data').
  Proof.
    intros Hnrec Hk0 Hatom Hlen Hs Hty Hty' Hnl Hsz Hrng Hnone Hh Hh' Hb Hb'.
    destruct Hatom as [-> | ->].
    - assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
      iIntros "H _".
      iApply (ent_toks_dirlink_nop Γ i dn dn' bm bm' data data'
                (fun j => dirent_bytes (de_of_name inum s) !!! j)
                nrec k0 0%nat Hnrec Hk0le eq_refl Hty' Hnl Hsz Hrng
                Hh Hh' Hb Hb' with "H").
    - iApply (ent_toks_dirlink Γ i dn dn' bm bm' data data' inum s nrec k0
                Hnrec Hk0 Hlen Hs Hty Hty' Hnl Hsz Hrng Hnone Hh Hh' Hb Hb').
  Qed.

  Lemma ent_toks_cong (Γ : fs_view_names Σ) (i : Z) (n n' : fs_node) :
    fn_rec n' = fn_rec n ->
    dir_entries n' = dir_entries n ->
    ent_toks Γ i n ⊣⊢ ent_toks Γ i n'.
  Proof.
    intros Hrec Hent. rewrite /ent_toks /fn_orphan /fn_nlink Hrec Hent //.
  Qed.

  (* ...and at the payload's own spelling: two [era_node]s over data that
     agree BELOW THE RECORD COUNT carry the same tokens.  [fb_agree] is
     this file's own extensionality (see above); the record is the same, so
     the orphan flag and the record count are too. *)
  Lemma ent_toks_era_node_data_ext (Γ : fs_view_names Σ) (i : Z)
      (dn : dinode) (bm bm' : blkmap) (data data' : nat -> list (bv 8)) :
    fb_agree (fn_data (era_node dn bm data)) (fn_data (era_node dn bm' data'))
      (16 * dir_nrec (bv_unsigned (di_size dn))) ->
    ent_toks Γ i (era_node dn bm data)
    ⊣⊢ ent_toks Γ i (era_node dn bm' data').
  Proof.
    intros Hag.
    apply (ent_toks_cong Γ i (era_node dn bm data) (era_node dn bm' data'));
      [reflexivity |].
    rewrite /dir_entries /fn_is_dir /fn_type /fn_nrec /fn_size !era_node_rec.
    destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z));
      [| reflexivity].
    symmetry. exact (dir_view_data_ext _ _ _ Hag).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE BORROW AT A MATCHED RECORD -- where licence (a) comes from      *)
  (* ------------------------------------------------------------------ *)

  (*  [ProofDirlookup]'s found arm holds the home directory's tokens and
      needs the ONE unit at the record the scan stopped on.  Peel it with
      a [big_sepM_lookup_acc] at the name the scan matched --
      [FsTree.dir_view_lookup] says the map's value at a WINNING record's
      name is that record's inum -- and hand back the wand that re-seals.
      Nothing is spent: [iget] returns the licence at the same [l].

      The [dir_inum <> self] premise is the SELF exemption: at a self
      record there IS no unit ([ent_tokenless]), and the caller uses
      licence (c) instead.  That case split is not an accident of the
      proof -- it is the (a)-vs-(c) boundary, drawn where xv6 draws it.
      NOTHING IS OWED ABOUT THE NAME.  [ent_tokenless] exempts a dot name
      only at an ORPHAN, and this borrow already runs under a LIVE home
      ([di_nlink <> 0], which the found arm holds out of
      [SpecDirlookup.dl_lic_live]) -- which is exactly why that guard is
      on the definition. *)
  Lemma ent_toks_borrow (Γ : fs_view_names Σ) (self : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) (k : nat) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_first data (dir_nrec (bv_unsigned (di_size dn)))
      (dir_bname data k) = Some k ->
    bv_unsigned (dir_inum data k) <> self ->
    blk_holes_zero bm data ->
    bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
    ent_toks Γ self (era_node dn bm data) -∗
      FsStateLink.link_tok Γ (bv_unsigned (dir_inum data k))
      ∗ (FsStateLink.link_tok Γ (bv_unsigned (dir_inum data k))
         -∗ ent_toks Γ self (era_node dn bm data)).
  Proof.
    intros Hty Hnl Hfirst Hself Hh Hsz.
    assert (Hlk : dir_view data (dir_nrec (bv_unsigned (di_size dn)))
                    !! dir_bname data k
                  = Some (bv_unsigned (dir_inum data k))).
    { rewrite dir_view_lookup Hfirst //. }
    rewrite /ent_toks (dir_entries_era_node dn bm data Hh Hsz)
      (bool_decide_eq_true_2 (bv_unsigned (di_type dn) = T_DIR_z) Hty)
      (fn_orphan_era_nz dn bm data Hnl).
    iIntros "H".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hlk with "H") as "[Ht Hback]".
    iEval (rewrite (ent_tok_ne Γ self false (dir_bname data k)
                      (bv_unsigned (dir_inum data k)) Hself eq_refl)) in "Ht".
    iFrame "Ht". iIntros "Ht".
    iApply "Hback".
    iEval (rewrite (ent_tok_ne Γ self false (dir_bname data k)
                      (bv_unsigned (dir_inum data k)) Hself eq_refl)).
    iExact "Ht".
  Qed.

End EraRes.
