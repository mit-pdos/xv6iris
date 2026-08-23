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
   proxy and with the LINK ghosts left out.  The links are step 3's
   ([ent_toks] / [link_auth]); they are deliberately absent here so that
   this file lands without touching [DirLinks.v] or the ledger's link
   columns.

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

     bnode dn bm data : fs_node        (blkmap + total data -> node)
     bm_of  n           : blkmap         (node -> blkmap)

   with [bnode (fn_rec n) (bm_of n) (fn_data n) = n] under
   [inode_local] ([bnode_bm_of]).  The direction a payload FLIP uses is
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
From iris.algebra Require Import auth gmap numbers.
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
Definition bnode (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
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

(* ---- [fn_*] of [bnode] --------------------------------------------- *)

Lemma bnode_rec dn bm data : fn_rec (bnode dn bm data) = dn.
Proof. reflexivity. Qed.
Lemma bnode_ent dn bm data : fn_ent (bnode dn bm data) = bm_ent bm.
Proof. reflexivity. Qed.
Lemma bnode_blk dn bm data : fn_blk (bnode dn bm data) = node_blk bm data.
Proof. reflexivity. Qed.

Lemma bnode_naddr dn bm data k :
  di_addrs dn = bm_cells bm -> length (bm_dir bm) = NDIRECT ->
  (k < MAXFILE)%nat ->
  fn_naddr (bnode dn bm data) k = bv_unsigned (blkmap_get bm k).
Proof.
  intros Haddr Hlen Hk. rewrite /fn_naddr /blkmap_get /bnode /= -NDIRECT_FS.
  destruct (decide (k < NDIRECT)%nat) as [Hlt | Hge]; [| reflexivity].
  rewrite Haddr /bm_cells lookup_total_app_l; [reflexivity |].
  rewrite Hlen. exact Hlt.
Qed.

Lemma bnode_indb dn bm data :
  di_addrs dn = bm_cells bm -> length (bm_dir bm) = NDIRECT ->
  fn_indb (bnode dn bm data) = bv_unsigned (bm_ind bm).
Proof.
  intros Haddr Hlen. rewrite /fn_indb /bnode /= Haddr /bm_cells.
  rewrite lookup_total_app_r;
    [| rewrite Hlen /FS_NDIRECT /NDIRECT; lia].
  rewrite Hlen /FS_NDIRECT /NDIRECT.
  assert (He : (12 - 12)%nat = 0%nat) by lia. rewrite He. reflexivity.
Qed.

Lemma bnode_data dn bm data k :
  blk_holes_zero bm data -> (k < MAXFILE)%nat ->
  fn_data (bnode dn bm data) k = data k.
Proof.
  intros Hh Hk. rewrite /fn_data /bnode /= node_blk_lookup.
  destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
    as [_ | Hc]; [reflexivity |].
  assert (Hz : bv_unsigned (blkmap_get bm k) = 0).
  { destruct (decide (bv_unsigned (blkmap_get bm k) = 0)) as [Hz | Hnz];
      [exact Hz |]. exfalso. apply Hc. split; [exact Hk | exact Hnz]. }
  rewrite (Hh k Hk Hz) //.
Qed.

(* ---- THE ROUNDTRIP --------------------------------------------------- *)

Lemma bnode_bm_of (i : Z) (n : fs_node) :
  inode_local i n -> bnode (fn_rec n) (bm_of n) (fn_data n) = n.
Proof.
  intros Hl.
  pose proof (inl_blk_dom Hl) as Hdom.
  pose proof (inl_blk_top Hl) as Htop.
  pose proof (inl_rec_wf Hl) as Hwf.
  rewrite /bnode. destruct n as [dn ent blk]; simpl in *.
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

(* ---- ...AND THE OTHER WAY: [inode_local] of [bnode] ---------------- *)

(* THE FOUR FACTS [inode_ok] DOES NOT CARRY, as premises.  Three of them
   ARE payload conjuncts already ([FsTree.dir_uniq],
   [DirView.dir_dots_ix], and the "16 divides the size" fact every
   directory producer establishes); the fourth, the TYPE ENUMERATION, has
   no producer in the in-memory chain -- see the header.
   The directory clauses are read at [fn_data (bnode ..)], not at
   [data]: a payload whose [data] is existentially bound re-existentialises
   at the node's own reading, so nothing ever has to relate two [data]
   functions.  [bnode_data] is the transport for a caller that does hold
   [data] concretely. *)
Lemma inode_local_of_ok (i : Z) (cov : gset Z) (ls : Z)
    (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov ls dn bm data ->
  (bv_unsigned (di_type dn) = 0 \/ bv_unsigned (di_type dn) = T_DIR_z
   \/ bv_unsigned (di_type dn) = T_FILE_z
   \/ bv_unsigned (di_type dn) = T_DEVICE_z) ->
  bv_unsigned (di_nlink dn) <= 32767 ->
  (bv_unsigned (di_type dn) = T_DIR_z -> (16 | bv_unsigned (di_size dn))) ->
  dir_uniq dn (fn_data (bnode dn bm data)) ->
  dir_dots_ix i dn (fn_data (bnode dn bm data)) ->
  inode_local i (bnode dn bm data).
Proof.
  intros (Hwf & Hcov & Haddr & Hty0 & Hsz & Hholes & Hsized)
         Hty Hnl Hdsz Huniq Hdots.
  destruct Hwf as (Hdlen & Helen & Hindz & _ & _).
  assert (Hnaddr : forall k, (k < MAXFILE)%nat ->
                     fn_naddr (bnode dn bm data) k
                     = bv_unsigned (blkmap_get bm k))
    by (intros k Hk; exact (bnode_naddr dn bm data k Haddr Hdlen Hk)).
  assert (Hind : fn_indb (bnode dn bm data) = bv_unsigned (bm_ind bm))
    by exact (bnode_indb dn bm data Haddr Hdlen).
  (* the record's own well-formedness comes off [di_addrs = bm_cells] *)
  assert (Hrwf : dinode_wf dn).
  { rewrite /dinode_wf Haddr /bm_cells length_app Hdlen /NDIRECT /=. lia. }
  (* the two readings [fn_is_dir] / [fn_nrec] resolve to the record's *)
  assert (Hdirb : fn_is_dir (bnode dn bm data) = true
                  <-> bv_unsigned (di_type dn) = T_DIR_z).
  { rewrite /fn_is_dir. apply bool_decide_eq_true. }
  assert (Hnrec : fn_nrec (bnode dn bm data)
                  = dir_nrec (bv_unsigned (di_size dn))) by reflexivity.
  (* [nlink <> 0] as the record states it, which is the dots guard's form *)
  assert (Hnlz : fn_nlink (bnode dn bm data) <> 0%nat ->
                 bv_unsigned (di_nlink dn) <> 0).
  { intros Hnz Hc. apply Hnz.
    rewrite /fn_nlink bnode_rec Hc //. }
  constructor.
  - exact Hrwf.
  - rewrite -NINDIRECT_FS. exact Helen.
  - rewrite Hind -NINDIRECT_FS. exact Hindz.
  - intros k Hk. rewrite -MAXFILE_FS in Hk.
    rewrite bnode_blk node_blk_lookup (Hnaddr k Hk).
    destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
      as [[_ Hnz] | Hc].
    + split; [intros _; exact Hnz | intros _; by eexists].
    + split; [intros [x Hx]; discriminate |].
      intros Hnz. exfalso. apply Hc. split; [exact Hk | exact Hnz].
  - intros k Hk. rewrite -MAXFILE_FS in Hk.
    rewrite bnode_blk node_blk_lookup.
    destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
      as [[Hc _] | _]; [lia | done].
  - intros k bs Hk. rewrite bnode_blk node_blk_lookup in Hk.
    destruct (decide ((k < MAXFILE)%nat /\ bv_unsigned (blkmap_get bm k) <> 0))
      as [[Hlt _] | _]; [| discriminate].
    injection Hk as <-. exact (Hsized k Hlt).
  - exact Hty.
  - rewrite /fn_size bnode_rec. split.
    + pose proof (bv_unsigned_in_range _ (di_size dn)) as [Hge _]. exact Hge.
    + rewrite -BSIZE_BSIZEz -MAXFILE_FS. exact Hsz.
  - intros k Hk Hlt. rewrite -MAXFILE_FS in Hk.
    rewrite (Hnaddr k Hk). apply (Hcov k Hk).
    rewrite /fn_size bnode_rec -BSIZE_BSIZEz in Hlt. exact Hlt.
  - intros Hz. exfalso. exact (Hty0 Hz).
  - exact Hnl.
  - intros Hd. exact (Hdsz (proj1 Hdirb Hd)).
  - intros Hd. rewrite Hnrec. exact (Huniq (proj1 Hdirb Hd)).
  - (* "." -- record 0 of a LIVE directory, through [dir_view_live] *)
    intros Hd Hnz.
    destruct (Hdots (proj1 Hdirb Hd) (Hnlz Hnz))
      as (H2 & Hlive0 & Hinum0 & Hname0 & _ & _).
    assert (Hlt0 : (0 < dir_nrec (bv_unsigned (di_size dn)))%nat) by lia.
    assert (Hbn : dir_bname (fn_data (bnode dn bm data)) 0%nat = DOT).
    { rewrite /dir_bname Hname0 DOT_dot //. }
    rewrite /dir_entries Hd Hnrec -Hbn.
    rewrite (dir_view_live (fn_data (bnode dn bm data))
               (dir_nrec (bv_unsigned (di_size dn))) 0%nat
               (Huniq (proj1 Hdirb Hd)) Hlt0 Hlive0).
    by rewrite Hinum0.
  - (* ".." -- record 1, the same way *)
    intros Hd Hnz.
    destruct (Hdots (proj1 Hdirb Hd) (Hnlz Hnz))
      as (H2 & _ & _ & _ & Hlive1 & Hname1).
    assert (Hlt1 : (1 < dir_nrec (bv_unsigned (di_size dn)))%nat) by lia.
    assert (Hbn : dir_bname (fn_data (bnode dn bm data)) 1%nat = DOTDOT).
    { rewrite /dir_bname Hname1 DOTDOT_dotdot //. }
    rewrite /dir_entries Hd Hnrec -Hbn.
    rewrite (dir_view_live (fn_data (bnode dn bm data))
               (dir_nrec (bv_unsigned (di_size dn))) 1%nat
               (Huniq (proj1 Hdirb Hd)) Hlt1 Hlive1).
    by eexists.
Qed.

(* ===================================================================== *)
(*  2b. THE DIRENT READINGS ARE EXTENSIONAL BELOW THE RECORD COUNT       *)
(* ===================================================================== *)

(* [bnode]'s [fn_data] agrees with [data] BELOW MAXFILE and cannot agree
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

(* ---- and the two facts that instantiate it at [bnode] ---------------- *)

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

Lemma bnode_fb_agree dn bm data :
  blk_holes_zero bm data ->
  fb_agree (fn_data (bnode dn bm data)) data (MAXFILE * BSIZE).
Proof.
  intros Hh i Hi. rewrite /file_byte.
  assert (Hd : (i `div` BSIZE < MAXFILE)%nat).
  { apply Nat.Div0.div_lt_upper_bound. rewrite Nat.mul_comm. exact Hi. }
  rewrite (bnode_data dn bm data (i `div` BSIZE)%nat Hh Hd) //.
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
  inode_local i (bnode dn bm data).
Proof.
  intros Hok Hty Hnl Hdsz Huniq Hdots.
  pose proof Hok as (_ & _ & _ & _ & Hsz & Hholes & _).
  assert (Hb : (16 * dir_nrec (bv_unsigned (di_size dn)) <= MAXFILE * BSIZE)%nat).
  { apply dir_nrec_bound; [| exact Hsz].
    pose proof (bv_unsigned_in_range _ (di_size dn)) as [Hge _]. exact Hge. }
  assert (Hag : fb_agree data (fn_data (bnode dn bm data))
                  (16 * dir_nrec (bv_unsigned (di_size dn)))).
  { apply (fb_agree_mono _ _ (MAXFILE * BSIZE) _ Hb).
    apply fb_agree_sym. exact (bnode_fb_agree dn bm data Hholes). }
  apply (inode_local_of_ok i cov ls dn bm data Hok Hty Hnl Hdsz).
  - exact (dir_uniq_data_ext dn data _ Hag Huniq).
  - exact (dir_dots_ix_data_ext i dn data _ Hag Hdots).
Qed.

(* ===================================================================== *)
(*  3.  THE RESOURCE BRIDGE, AND THE BUNDLE                              *)
(* ===================================================================== *)

Section EraRes.
  Context `{!riscvGS Σ, !xv6G Σ, !fsLinkG Σ, !fsTopG Σ}.

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

  Definition inode_owned_era (γfs : fs_names) (γi : gname) (inum : bv 32)
      (n : fs_node) : iProp Σ :=
    (dinode_at γi inum (fn_rec n)
     ∗ ([∗ map] k ↦ bs ∈ fn_blk n,
          FsStateDefs.blk_owned (fs_gamma_L γfs) (fn_naddr n k) bs)
     ∗ ind_owned (fs_gamma_L γfs) n
     ∗ top_frag (fs_gamma_L γfs) (bv_unsigned inum) n
     ∗ ⌜inode_local (bv_unsigned inum) n⌝)%I.

  Global Instance inode_owned_era_timeless γfs γi inum n :
    Timeless (inode_owned_era γfs γi inum n).
  Proof.
    rewrite /inode_owned_era /ind_owned /top_frag.
    destruct (decide (fn_indb n = 0)); apply _.
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
     fifth conjunct, read off the ownership and not maintained anywhere *)
  Lemma inode_owned_era_slot_inj γfs γi inum n :
    inode_owned_era γfs γi inum n -∗
    ⌜forall k j : nat, (k <= MAXFILE)%nat -> (j <= MAXFILE)%nat ->
        bv_unsigned (bm_slot (bm_of n) k) <> 0 ->
        bm_slot (bm_of n) k = bm_slot (bm_of n) j -> k = j⌝.
  Proof.
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
        rewrite /ind_owned (decide_False _ _ Hnk).
        destruct (proj2 (inl_blk_dom Hl j
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnj) as [bs Hbs].
        iDestruct (big_sepM_lookup _ _ j bs Hbs with "Hb") as "Hbj".
        iApply (FsStateDefs.blk_owned_ne _ (fs_gamma_L_excl γfs)
                  with "Hi Hbj").
      - (* j is the indirect block, k a data slot *)
        rewrite /ind_owned (decide_False _ _ Hnj).
        destruct (proj2 (inl_blk_dom Hl k
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnk) as [bs Hbs].
        iDestruct (big_sepM_lookup _ _ k bs Hbs with "Hb") as "Hbk".
        iApply (FsStateDefs.blk_owned_ne _ (fs_gamma_L_excl γfs)
                  with "Hbk Hi").
      - (* two data slots *)
        destruct (proj2 (inl_blk_dom Hl k
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnk) as [bsk Hbsk].
        destruct (proj2 (inl_blk_dom Hl j
                    ltac:(rewrite -MAXFILE_FS; lia)) Hnj) as [bsj Hbsj].
        iDestruct (big_sepM_delete _ _ k bsk Hbsk with "Hb") as "[Hbk Hrest]".
        assert (Hbsj' : delete k (fn_blk n) !! j = Some bsj)
          by (rewrite lookup_delete_ne; [exact Hbsj | done]).
        iDestruct (big_sepM_lookup _ _ j bsj Hbsj' with "Hrest") as "Hbj".
        iApply (FsStateDefs.blk_owned_ne _ (fs_gamma_L_excl γfs)
                  with "Hbk Hbj"). }
    iPureIntro. intros k j Hk Hj Hnk Heq.
    destruct (decide (k = j)) as [-> | Hkj]; [done |].
    exfalso. apply (Hne k j Hk Hj Hkj Hnk); rewrite -Heq; [exact Hnk |].
    by rewrite Heq.
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

End EraRes.
