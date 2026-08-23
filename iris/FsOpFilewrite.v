(* FsOpFilewrite.v -- durable-disk stage G2, batch (1): the standalone
   per-op preservation lemma family for the FILEWRITE op family.

   ONE filewrite transaction's net effect on the committed view is a
   SEQUENCE of stage-F2 effects at a FIXED inode [i]:

     (eff_alloc_file_block | eff_alloc_ind_block | eff_write_file_data)*

   -- and under the beyond-size ruling (stage F3) the allocations carry
   NO size: writei installs the block, then moves ip->size, and the two
   are separate effects.  That is what makes a partial-failure commit --
   an allocation with no write after it -- a prefix of this same list.

   bmap's balloc at each slot (the NDIRECT crossing being TWO plain
   allocations, the indirect block and then the data block), then writei's
   per-block byte write.  The file has three parts.

   1. THE CHAIN COMBINATOR (section 2): a step datum [wstep], its
      application [ws_apply] / [ws_run] ([fold_left]), its step
      precondition [ws_pre] AT THE CURRENT VIEW and the sequential
      [ws_pre_chain]; [ws_run_wf] is the one induction.

   2. PRECONDITION TRANSPORT (sections 3-6): the real content.  A
      filewrite proof's facts are stated at the PRE-transaction view (the
      inode's decode) or at balloc time (a CLEARED bitmap bit), so each
      step's preconditions have to be carried across the earlier steps:
      the decode transport ([ws_apply_type] / [ws_apply_size] /
      [ws_apply_bit] and their run-level forms) and then the three
      [ws_pre_*_after] lemmas that rebuild a premise at the post-step
      view out of facts at the pre-step one.

   3. THE WORKED COROLLARY (section 7): [ws_appends_wf] -- starting at a
      size with [fs_nblk = n0], appending [k] blocks with data (crossing
      12 if the range does) preserves [fs_durable_wf_view].  That is the
      single lemma filewrite's end_op arm invokes.

   TWO ARMS THAT NEED NO LEMMA.  A [T_DEVICE] file's filewrite goes
   through [devsw[major].write] and never reaches writei, so it writes NO
   disk block: its net effect on the committed view is the IDENTITY and
   [fs_durable_wf_view] is preserved by assumption (the same holds of the
   FD_PIPE arm and of the up-front [-1] returns).  And the chunk loop can
   END EARLY -- writei short-writes, [r != n1] breaks out -- so the
   committed net is a PREFIX of the full step list; the combinator is
   stated at an arbitrary list, so every prefix is already covered
   ([ws_appends] at a smaller [k]).

   Preconditions stay DECODE-LEVEL throughout, exactly like the F2
   wrappers': facts about the VIEW (a bitmap bit, a record's size and
   type), never about a resource. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import BioDefs.
Require Import DirentEnc.
Require Import DinodeEnc.
Require Import BitmapEnc.
Require Import InodeDefs.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffBase.
Require Import FsEffAllocBlock.
Require Import FsEffAllocIndBlock.
Require Import FsEffWriteData.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THREE FACTS IN AN EMPTY CONTEXT                                    *)
(*                                                                         *)
(*  optimization.md's rule 1: a side condition that is the same at every   *)
(*  call site is proved where the context is empty.  [zify] does NOT       *)
(*  model [Z.div] in this build (it abstracts the quotient as an atom), so *)
(*  the one fact that needs the division is proved here, once, with the    *)
(*  euclidean equations posed by hand -- and every [lia] below sees        *)
(*  [fs_nblk] as an atom, which is all it ever needs.                      *)
(* ====================================================================== *)

Lemma fs_nblk_pos (sz : Z) : 0 < fs_nblk sz -> 0 < sz.
Proof.
  unfold fs_nblk. change (BSIZE_z - 1) with 1023. change BSIZE_z with 1024.
  intros H.
  pose proof (Z.div_mod (sz + 1023) 1024 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (sz + 1023) 1024 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma bv32_of_size (sz : Z) :
  0 <= sz <= Z.of_nat FS_MAXFILE * BSIZE_z -> bv_unsigned (Z_to_bv 32 sz) = sz.
Proof.
  intros H. assert (Hm : bv_modulus 32 = 4294967296) by reflexivity.
  apply Z_to_bv_small. unfold FS_MAXFILE, BSIZE_z in H. lia.
Qed.

(* the bitmap block AFTER an allocation, read one bit at a time: the old
   block's bit, or one of the freshly marked blocks *)
Lemma bit_of_union (bmb : list (bv 8)) (F : gset Z) (b : Z) :
  0 <= b < 8 * BSIZE_z ->
  fs_bit (bm_bytes BSIZE (fs_bmap_set BSIZE bmb ∪ F)) b
  = fs_bit bmb b || bool_decide (b ∈ F).
Proof.
  intros Hb. pose proof BSIZE_z_nat as Hn.
  rewrite fs_bit_bm_bytes by lia.
  destruct (decide (b ∈ F)) as [HF | HF].
  - rewrite (bool_decide_eq_true_2 (b ∈ F)) by exact HF.
    rewrite (bool_decide_eq_true_2 (b ∈ fs_bmap_set BSIZE bmb ∪ F))
      by (apply elem_of_union; right; exact HF).
    symmetry. apply orb_true_r.
  - rewrite (bool_decide_eq_false_2 (b ∈ F)) by exact HF.
    rewrite orb_false_r.
    destruct (fs_bit bmb b) eqn:Hbit.
    + apply bool_decide_eq_true_2, elem_of_union. left.
      apply fs_bmap_set_elem. split; [lia | exact Hbit].
    + apply bool_decide_eq_false_2. intros Hc.
      apply elem_of_union in Hc as [Hc | Hc]; [| exact (HF Hc)].
      apply fs_bmap_set_elem in Hc as (_ & Hc).
      rewrite Hbit in Hc. discriminate.
Qed.

Section OpFilewrite.
  (* ONE superblock and ONE inode for the whole transaction: filewrite
     writes a single file, and the superblock block is never written. *)
  Context (sb : fs_sb) (i : Z).

  Set Default Proof Using "All".

  (* ==================================================================== *)
  (*  2.  THE WRITE STEP, ITS APPLICATION AND ITS PRECONDITION            *)
  (* ==================================================================== *)

  (* filewrite's per-step net effect, as a datum.  The inode is fixed, so
     a step carries only the slot / the fresh block / the bytes.  THE
     ALLOCATIONS NO LONGER CARRY A SIZE (durable-disk F3.2): [writei]
     installs the block and only afterwards moves [ip->size], and keeping
     the two apart is what makes an allocation's precondition SLOT
     EMPTINESS.  It is also what makes writei's partial-failure commits --
     a block installed, the size left alone -- a chain of alloc steps with
     no write step after them, i.e. expressible here at all. *)
  Inductive wstep : Type :=
  | ws_alloc (fbn : nat) (fresh : Z)
  | ws_alloc_ind (fresh_ind : Z)
  | ws_write (fbn : nat) (bs : list (bv 8)) (sz' : Z).

  Definition ws_apply (s : wstep) (P : Z -> list (bv 8))
    : Z -> list (bv 8) :=
    match s with
    | ws_alloc fbn fresh => eff_alloc_file_block P sb i fbn fresh
    | ws_alloc_ind fi => eff_alloc_ind_block P sb i fi
    | ws_write fbn bs sz' => eff_write_file_data P sb i fbn bs sz'
    end.

  Definition ws_run (l : list wstep) (P : Z -> list (bv 8))
    : Z -> list (bv 8) :=
    fold_left (fun Q s => ws_apply s Q) l P.

  (* the size after the step: only a write moves it *)
  Definition ws_newsize (s : wstep) (P : Z -> list (bv 8)) : Z :=
    match s with
    | ws_write _ _ sz' => sz'
    | _ => bv_unsigned (di_size (fs_dinode P sb i))
    end.

  Definition ws_fresh (s : wstep) : gset Z :=
    match s with
    | ws_alloc _ f => {[f]}
    | ws_alloc_ind fi => {[fi]}
    | ws_write _ _ _ => ∅
    end.

  Fixpoint ws_freshs (l : list wstep) : gset Z :=
    match l with
    | [] => ∅
    | s :: l' => ws_fresh s ∪ ws_freshs l'
    end.

  (* the record the step installs at [i] *)
  Definition ws_dinode (P : Z -> list (bv 8)) (s : wstep) : dinode :=
    let dn := fs_dinode P sb i in
    match s with
    | ws_alloc fbn fresh =>
        if (fbn <? 12)%nat
        then di_set_size_addr dn (di_size dn) fbn (Z_to_bv 32 fresh)
        else dn
    | ws_alloc_ind fi =>
        di_set_size_addr dn (di_size dn) 12 (Z_to_bv 32 fi)
    | ws_write _ _ sz' => di_set_size dn (Z_to_bv 32 sz')
    end.

  (* filewrite's inode is a FILE (the FD_INODE arm) -- or a device record
     reached through writei, which the effect vocabulary also admits. *)
  Definition ws_file_type (P : Z -> list (bv 8)) : Prop :=
    bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
    \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z.

  (* THE STEP PRECONDITION, AT THE CURRENT VIEW.  Decode level throughout.
     An allocation asks only that the slot it fills is EMPTY (bmap's own
     test) and that the block balloc handed it has a cleared bit; a write
     asks that its target slot is allocated and that the size it installs
     is still covered. *)
  Definition ws_pre (s : wstep) (P : Z -> list (bv 8)) : Prop :=
    0 <= i < sb_ninodes sb
    /\ ws_file_type P
    /\ match s with
       | ws_alloc fbn fresh =>
           (fbn < FS_MAXFILE)%nat
           /\ fs_slot P (fs_dinode P sb i) fbn = 0
           /\ ((12 <= fbn)%nat ->
                 bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) <> 0)
           /\ fs_data_start sb <= fresh < sb_size sb
           /\ fs_bit (P (sb_bmapstart sb)) fresh = false
       | ws_alloc_ind fi =>
           bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) = 0
           /\ fs_data_start sb <= fi < sb_size sb
           /\ fs_bit (P (sb_bmapstart sb)) fi = false
       | ws_write fbn _ sz' =>
           (fbn < FS_MAXFILE)%nat
           /\ fs_blk_addr P (fs_dinode P sb i) fbn <> 0
           /\ 0 <= sz' <= Z.of_nat FS_MAXFILE * BSIZE_z
           /\ (forall k : nat, (k < FS_MAXFILE)%nat ->
                 Z.of_nat k < fs_nblk sz' ->
                 fs_blk_addr P (fs_dinode P sb i) k <> 0)
       end.

  (* SEQUENTIALLY: each step's precondition at the view the earlier steps
     produced. *)
  Fixpoint ws_pre_chain (l : list wstep) (P : Z -> list (bv 8)) : Prop :=
    match l with
    | [] => True
    | s :: l' => ws_pre s P /\ ws_pre_chain l' (ws_apply s P)
    end.

  Lemma ws_run_nil (P : Z -> list (bv 8)) : ws_run [] P = P.
  Proof. reflexivity. Qed.

  Lemma ws_run_cons (s : wstep) (l : list wstep) (P : Z -> list (bv 8)) :
    ws_run (s :: l) P = ws_run l (ws_apply s P).
  Proof. reflexivity. Qed.

  Lemma ws_run_app (l1 l2 : list wstep) (P : Z -> list (bv 8)) :
    ws_run (l1 ++ l2) P = ws_run l2 (ws_run l1 P).
  Proof. unfold ws_run. apply fold_left_app. Qed.

  Lemma ws_pre_chain_app (l1 l2 : list wstep) (P : Z -> list (bv 8)) :
    ws_pre_chain (l1 ++ l2) P
    <-> ws_pre_chain l1 P /\ ws_pre_chain l2 (ws_run l1 P).
  Proof.
    revert P. induction l1 as [| s l1 IH]; intros P; cbn [ws_pre_chain app].
    - rewrite ws_run_nil. tauto.
    - rewrite ws_run_cons, IH. tauto.
  Qed.

  (* ==================================================================== *)
  (*  3.  THE VIEW-LEVEL GEOMETRY THE TRANSPORT LEMMAS READ                *)
  (* ==================================================================== *)

  Lemma wfv_ok (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> fs_sb_ok sb.
  Proof.
    intros (sb0 & Hp0 & Hsw) Hp.
    assert (Hse : sb0 = sb) by congruence. subst sb0.
    destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
    exact (fs_sb_wf_ok sb Hsb).
  Qed.

  (* the block geometry, in one bundle: every distinctness side condition
     below is [lia] from these. *)
  Lemma wfv_geom (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    0 <= i < sb_ninodes sb ->
    SB_BNO < IBLOCK (fs_inum_bv i) (sb_inodestart sb)
    /\ IBLOCK (fs_inum_bv i) (sb_inodestart sb) < sb_bmapstart sb
    /\ SB_BNO < sb_bmapstart sb
    /\ sb_bmapstart sb < fs_data_start sb
    /\ fs_data_start sb < sb_size sb
    /\ sb_size sb <= 8 * BSIZE_z
    /\ 0 <= i < 16 * (sb_ninodes sb / 16 + 1).
  Proof.
    intros Hv Hp Hi.
    pose proof (wfv_ok P Hv Hp) as Hok.
    pose proof (iblk_z_range sb i Hi) as HiN.
    destruct (iblock_bounds sb Hok i HiN) as (Hb1 & Hb2 & Hb3).
    destruct (fs_sb_ok_geom sb Hok) as (Hg1 & Hg2 & Hg3 & _).
    pose proof (sbo_one_bitmap sb Hok) as Hone.
    unfold SB_BNO in *. repeat split; lia.
  Qed.

  Lemma wfv_dok (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    fs_inode_dok P sb (fs_dinode P sb i).
  Proof.
    intros Hv Hp Hi Hlive. destruct Hv as (sb0 & Hp0 & Hsw).
    assert (Hse : sb0 = sb) by congruence. subst sb0.
    destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
    exact (fs_inodes_dwf_spec P sb i HW3 Hi Hlive).
  Qed.

  Lemma wfv_size_cap (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    0 <= bv_unsigned (di_size (fs_dinode P sb i))
        <= Z.of_nat FS_MAXFILE * BSIZE_z.
  Proof.
    intros Hv Hp Hi Hlive.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size (fs_dinode P sb i)))).
    pose proof (fdi_size _ _ _ (wfv_dok P Hv Hp Hi Hlive)). lia.
  Qed.

  (* the indirect POINTER: zero, or a real data block -- either way it is
     neither the superblock, nor the bitmap block, nor the record's own
     inode block, which is all the footprint lemma wants of it.  (Under
     the beyond-size ruling it can be nonzero at ANY size, so this reads
     the ENTRY clause, not the size.) *)
  Lemma wfv_ind_ptr (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    SB_BNO <> bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat)
    /\ IBLOCK (fs_inum_bv i) (sb_inodestart sb)
       <> bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat)
    /\ sb_bmapstart sb
       <> bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat).
  Proof.
    intros Hv Hp Hi Hlive.
    destruct (wfv_geom P Hv Hp Hi) as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & _ & _).
    pose proof (wfv_dok P Hv Hp Hi Hlive) as Hd.
    destruct (decide (bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat)
                      = 0)) as [Hz | Hnz].
    - rewrite Hz. unfold SB_BNO in *. repeat split; lia.
    - pose proof (fdi_ind_ok _ _ _ Hd Hnz) as Hr.
      unfold SB_BNO in *. repeat split; lia.
  Qed.

  (* a COVERED content block is a real data block -- writei's destination *)
  Lemma wfv_blk_addr (P : Z -> list (bv 8)) (k : nat) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    Z.of_nat k < fs_nblk (bv_unsigned (di_size (fs_dinode P sb i))) ->
    fs_data_start sb <= fs_blk_addr P (fs_dinode P sb i) k < sb_size sb.
  Proof.
    intros Hv Hp Hi Hlive Hk.
    pose proof (wfv_size_cap P Hv Hp Hi Hlive) as Hcap.
    pose proof (fs_nblk_max _ (proj1 Hcap) (proj2 Hcap)) as Hmax.
    assert (HkM : (k < FS_MAXFILE)%nat) by lia.
    exact (fs_inode_dok_blk P sb (fs_dinode P sb i) k
             (wfv_dok P Hv Hp Hi Hlive) HkM Hk).
  Qed.

  (* [InodeInv.bm_covers] at the view: every below-size slot is allocated *)
  Lemma wfv_cov (P : Z -> list (bv 8)) (k : nat) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    (k < FS_MAXFILE)%nat ->
    Z.of_nat k < fs_nblk (bv_unsigned (di_size (fs_dinode P sb i))) ->
    fs_blk_addr P (fs_dinode P sb i) k <> 0.
  Proof.
    intros Hv Hp Hi Hlive HkM Hk.
    destruct (wfv_geom P Hv Hp Hi) as (_ & _ & Hg3 & Hg4 & _ & _ & _).
    pose proof (fs_inode_dok_blk P sb (fs_dinode P sb i) k
                  (wfv_dok P Hv Hp Hi Hlive) HkM Hk).
    unfold SB_BNO in *. lia.
  Qed.

  (* [InodeInv.blkmap_wf]'s injectivity, at the view *)
  Lemma wfv_slot_inj (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    fs_slot_inj P (fs_dinode P sb i).
  Proof.
    intros Hv Hp Hi Hlive.
    destruct Hv as (sb0 & Hp0 & Hsw).
    assert (Hse : sb0 = sb) by congruence. subst sb0.
    destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
    destruct HW45 as (u & Hu & Hbm).
    apply fs_slot_inj_of_ents.
    apply (fs_ent_blocks_nodup_inode P sb i
             (fs_ent_set_nodup P sb u Hu) Hi Hlive).
  Qed.

  (* the two readings of [ws_file_type] the effect wrappers ask for *)
  Lemma ws_type_live (P : Z -> list (bv 8)) :
    ws_file_type P -> bv_unsigned (di_type (fs_dinode P sb i)) <> 0.
  Proof.
    intros [H | H]; rewrite H; unfold T_FILE_z, T_DEVICE_z; discriminate.
  Qed.

  (* the decode at [i] from ONE block equation *)
  Lemma dinode_at (P Q : Z -> list (bv 8)) (dn' : dinode) :
    fs_sb_ok sb -> 0 <= i < 16 * (sb_ninodes sb / 16 + 1) -> dinode_wf dn' ->
    Q (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
      = eff_dinode P sb i dn' (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
    fs_dinode Q sb i = dn'.
  Proof.
    intros Hok HiN Hwf HQ.
    rewrite (fs_dinode_ext (eff_dinode P sb i dn') Q sb i HQ).
    rewrite (eff_dinode_dec sb Hok P i dn' i Hwf HiN HiN).
    rewrite decide_True by reflexivity. reflexivity.
  Qed.

  Lemma ws_dinode_wf (P : Z -> list (bv 8)) (s : wstep) :
    dinode_wf (ws_dinode P s).
  Proof.
    destruct s as [fbn f | fi | fbn bs sz']; cbn [ws_dinode].
    - destruct (fbn <? 12)%nat.
      + apply di_set_size_addr_wf, fs_dinode_wf.
      + apply fs_dinode_wf.
    - apply di_set_size_addr_wf, fs_dinode_wf.
    - apply di_set_size_wf, fs_dinode_wf.
  Qed.

  (* ==================================================================== *)
  (*  4.  PER-STEP DECODE TRANSPORT                                        *)
  (* ==================================================================== *)

  (* THE FOOTPRINT, per arm: the three blocks a precondition can name. *)
  Lemma ws_apply_blocks (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    ws_apply s P SB_BNO = P SB_BNO
    /\ fs_dinode (ws_apply s P) sb i = ws_dinode P s
    /\ ws_apply s P (sb_bmapstart sb)
       = match s with
         | ws_write _ _ _ => P (sb_bmapstart sb)
         | _ => bm_bytes BSIZE
                  (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ ws_fresh s)
         end.
  Proof.
    intros Hv Hp (Hi & Hty & Hs).
    pose proof (ws_type_live P Hty) as Hlive.
    pose proof (wfv_ok P Hv Hp) as Hok.
    destruct (wfv_geom P Hv Hp Hi)
      as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & HiN).
    destruct (wfv_ind_ptr P Hv Hp Hi Hlive) as (Hx1 & Hx2 & Hx3).
    destruct s as [fbn f | fi | fbn bs sz'].
    - destruct Hs as (HfbnM & Hslot & Hib & Hfr & Hbit).
      cbn [ws_apply ws_fresh].
      unfold eff_alloc_file_block. cbv zeta.
      repeat split.
      + rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        destruct (fbn <? 12)%nat.
        * apply (eff_dinode_out sb). unfold SB_BNO in *. lia.
        * rewrite fs_upd_ne by exact Hx1.
          apply (eff_dinode_out sb). unfold SB_BNO in *. lia.
      + apply (dinode_at P _ _ Hok HiN (ws_dinode_wf P (ws_alloc fbn f))).
        cbn [ws_dinode].
        rewrite fs_upd_ne by lia. rewrite fs_upd_ne by lia.
        destruct (fbn <? 12)%nat; [reflexivity |].
        rewrite fs_upd_ne by exact Hx2. reflexivity.
      + rewrite fs_upd_ne by lia. apply fs_upd_at.
    - destruct Hs as (Hibz & Hfr & Hbit).
      cbn [ws_apply ws_fresh].
      unfold eff_alloc_ind_block. cbv zeta.
      repeat split.
      + rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        apply (eff_dinode_out sb). unfold SB_BNO in *. lia.
      + apply (dinode_at P _ _ Hok HiN (ws_dinode_wf P (ws_alloc_ind fi))).
        cbn [ws_dinode].
        rewrite fs_upd_ne by lia. rewrite fs_upd_ne by lia. reflexivity.
      + rewrite fs_upd_ne by lia. apply fs_upd_at.
    - destruct Hs as (HfbnM & Hfbn & Hcap & Hcov).
      pose proof (fs_blk_addr_range P sb (fs_dinode P sb i) fbn
                    (wfv_dok P Hv Hp Hi Hlive) HfbnM Hfbn) as Ha.
      cbn [ws_apply].
      unfold eff_write_file_data.
      repeat split.
      + rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        apply (eff_dinode_out sb). unfold SB_BNO in *. lia.
      + apply (dinode_at P _ _ Hok HiN
                 (ws_dinode_wf P (ws_write fbn bs sz'))).
        cbn [ws_dinode]. rewrite fs_upd_ne by lia. reflexivity.
      + rewrite fs_upd_ne by lia.
        apply (eff_dinode_out sb). lia.
  Qed.

  (* (T0) THE SUPERBLOCK NEVER MOVES *)
  Lemma ws_apply_parse (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    fs_parse_sb (ws_apply s P) = Some sb.
  Proof.
    intros Hv Hp Hs.
    destruct (ws_apply_blocks s P Hv Hp Hs) as (Hsbb & _ & _).
    rewrite (fs_parse_sb_ext P (ws_apply s P) Hsbb). exact Hp.
  Qed.

  (* (T1) THE STEP PRESERVES THE FS INVARIANT *)
  Lemma ws_apply_wf (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    fs_durable_wf_view (ws_apply s P).
  Proof.
    intros Hv Hp (Hi & Hty & Hs).
    pose proof (ws_type_live P Hty) as Hlive.
    destruct s as [fbn f | fi | fbn bs sz'].
    - destruct Hs as (HfbnM & Hslot & Hib & Hfr & Hbit).
      exact (eff_alloc_file_block_wfv P sb i fbn f
               Hv Hp Hi Hlive HfbnM Hslot Hib Hfr Hbit).
    - destruct Hs as (Hibz & Hfr & Hbit).
      exact (eff_alloc_ind_block_wfv P sb i fi Hv Hp Hi Hlive Hibz Hfr Hbit).
    - destruct Hs as (HfbnM & Hfbn & Hcap & Hcov).
      exact (eff_write_file_data_wfv P sb i fbn bs sz'
               Hv Hp Hi Hty HfbnM Hfbn Hcap Hcov).
  Qed.

  (* (T2) THE TYPE IS INVARIANT *)
  Lemma ws_apply_type (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    di_type (fs_dinode (ws_apply s P) sb i) = di_type (fs_dinode P sb i).
  Proof.
    intros Hv Hp Hs.
    rewrite (proj1 (proj2 (ws_apply_blocks s P Hv Hp Hs))).
    destruct s as [fbn f | fi | fbn bs sz']; cbn [ws_dinode].
    - destruct (fbn <? 12)%nat; reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma ws_apply_file_type (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    ws_file_type (ws_apply s P).
  Proof.
    intros Hv Hp Hs. unfold ws_file_type.
    rewrite (ws_apply_type s P Hv Hp Hs).
    destruct Hs as (_ & Hty & _). exact Hty.
  Qed.

  (* (T3) THE SIZE AFTER THE STEP -- an allocation leaves it alone *)
  Lemma ws_apply_size (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    bv_unsigned (di_size (fs_dinode (ws_apply s P) sb i)) = ws_newsize s P.
  Proof.
    intros Hv Hp Hs.
    rewrite (proj1 (proj2 (ws_apply_blocks s P Hv Hp Hs))).
    destruct Hs as (Hi & Hty & Hs).
    destruct s as [fbn f | fi | fbn bs sz']; cbn [ws_newsize ws_dinode].
    - destruct (fbn <? 12)%nat; reflexivity.
    - reflexivity.
    - destruct Hs as (HfbnM & Hfbn & Hcap & Hcov).
      cbn [di_size di_set_size]. apply bv32_of_size. lia.
  Qed.

  (* (T3b) THE BLOCK MAP AFTER THE STEP -- the transport bundle
     (durable-disk F3.5): an allocation fills its own slot and leaves
     every other one alone; a write leaves the whole map alone. *)
  Lemma ws_apply_slot (s : wstep) (P : Z -> list (bv 8)) (k : nat) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    (k <= FS_MAXFILE)%nat ->
    fs_slot (ws_apply s P) (fs_dinode (ws_apply s P) sb i) k
    = match s with
      | ws_alloc fbn fresh =>
          if decide (k = fbn) then fresh else fs_slot P (fs_dinode P sb i) k
      | ws_alloc_ind fi =>
          if decide (k = FS_MAXFILE) then fi
          else fs_slot P (fs_dinode P sb i) k
      | ws_write _ _ _ => fs_slot P (fs_dinode P sb i) k
      end.
  Proof.
    intros Hv Hp Hpre Hk.
    destruct Hpre as (Hi & Hty & Hs).
    pose proof (ws_type_live P Hty) as Hlive.
    destruct (wfv_geom P Hv Hp Hi)
      as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & HiN).
    destruct (wfv_ind_ptr P Hv Hp Hi Hlive) as (Hx1 & Hx2 & Hx3).
    destruct s as [fbn f | fi | fbn bs sz'].
    - destruct Hs as (HfbnM & Hslot & Hib & Hfr & Hbit).
      exact (eff_alloc_file_block_slot P sb i fbn f k
               Hv Hp Hi Hlive HfbnM Hslot Hib Hfr Hbit Hk).
    - destruct Hs as (Hibz & Hfr & Hbit).
      exact (eff_alloc_ind_block_slot P sb i fi k
               Hv Hp Hi Hlive Hibz Hfr Hbit Hk).
    - destruct Hs as (HfbnM & Hfbn & Hcap & Hcov).
      pose proof (wfv_dok P Hv Hp Hi Hlive) as Hd.
      pose proof (fs_blk_addr_range P sb (fs_dinode P sb i) fbn
                    Hd HfbnM Hfbn) as Ha.
      assert (Hdin : fs_dinode (ws_apply (ws_write fbn bs sz') P) sb i
                     = ws_dinode P (ws_write fbn bs sz')).
      { exact (proj1 (proj2 (ws_apply_blocks (ws_write fbn bs sz') P Hv Hp
                               (conj Hi (conj Hty
                                  (conj HfbnM (conj Hfbn
                                     (conj Hcap Hcov)))))))). }
      rewrite Hdin.
      assert (Hind : fs_ind_ents (ws_apply (ws_write fbn bs sz') P)
                       (ws_dinode P (ws_write fbn bs sz'))
                     = fs_ind_ents P (fs_dinode P sb i)).
      { transitivity (fs_ind_ents (ws_apply (ws_write fbn bs sz') P)
                        (fs_dinode P sb i)).
        - apply fs_ind_ents_meta12.
          cbn [ws_dinode di_set_size di_addrs]. reflexivity.
        - apply fs_ind_ents_ext. intros Hnz12.
          cbn [ws_apply]. unfold eff_write_file_data.
          rewrite fs_upd_ne.
          + apply (eff_dinode_out sb). exact (fun Hc => Hx2 (eq_sym Hc)).
          + intros Hc.
            pose proof (wfv_slot_inj P Hv Hp Hi Hlive) as Hinj.
            assert (Hkeq : FS_MAXFILE = fbn).
            { apply (Hinj FS_MAXFILE fbn ltac:(lia) ltac:(lia));
                [rewrite fs_slot_max; exact Hnz12 |].
              rewrite fs_slot_max,
                (fs_slot_lt P (fs_dinode P sb i) fbn HfbnM).
              exact Hc. }
            lia. }
      apply (fs_slot_det P (ws_apply (ws_write fbn bs sz') P)
               (fs_dinode P sb i) (ws_dinode P (ws_write fbn bs sz')) k).
      + cbn [ws_dinode di_set_size di_addrs]. reflexivity.
      + exact Hind.
  Qed.

  (* (T4) THE BITMAP ACCUMULATES EXACTLY THE STEP'S OWN FRESH BLOCKS *)
  Lemma ws_apply_bit (s : wstep) (P : Z -> list (bv 8)) (b : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    0 <= b < 8 * BSIZE_z ->
    fs_bit (ws_apply s P (sb_bmapstart sb)) b
    = fs_bit (P (sb_bmapstart sb)) b || bool_decide (b ∈ ws_fresh s).
  Proof.
    intros Hv Hp Hs Hb.
    rewrite (proj2 (proj2 (ws_apply_blocks s P Hv Hp Hs))).
    destruct s as [fbn f | fi | fbn bs sz'].
    - apply bit_of_union, Hb.
    - apply bit_of_union, Hb.
    - cbn [ws_fresh].
      rewrite (bool_decide_eq_false_2 (b ∈ (∅ : gset Z)))
        by (rewrite elem_of_empty; tauto).
      rewrite orb_false_r. reflexivity.
  Qed.

  Lemma ws_apply_bit_false (s : wstep) (P : Z -> list (bv 8)) (b : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    0 <= b < 8 * BSIZE_z ->
    fs_bit (P (sb_bmapstart sb)) b = false -> b ∉ ws_fresh s ->
    fs_bit (ws_apply s P (sb_bmapstart sb)) b = false.
  Proof.
    intros Hv Hp Hs Hb Hfalse Hnin.
    rewrite (ws_apply_bit s P b Hv Hp Hs Hb), Hfalse.
    rewrite (bool_decide_eq_false_2 (b ∈ ws_fresh s)) by exact Hnin.
    reflexivity.
  Qed.

  (* ==================================================================== *)
  (*  5.  THE CHAIN LEMMA, AND THE RUN-LEVEL TRANSPORT                     *)
  (* ==================================================================== *)

  Lemma ws_run_ok (l : list wstep) :
    forall P : Z -> list (bv 8),
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre_chain l P ->
    fs_durable_wf_view (ws_run l P)
    /\ fs_parse_sb (ws_run l P) = Some sb
    /\ di_type (fs_dinode (ws_run l P) sb i) = di_type (fs_dinode P sb i)
    /\ (forall b : Z, 0 <= b < 8 * BSIZE_z -> b ∉ ws_freshs l ->
          fs_bit (ws_run l P (sb_bmapstart sb)) b
          = fs_bit (P (sb_bmapstart sb)) b).
  Proof.
    induction l as [| s l IH]; intros P Hv Hp Hc.
    - rewrite ws_run_nil.
      split; [exact Hv |]. split; [exact Hp |]. split; [reflexivity |].
      intros b _ _. reflexivity.
    - destruct Hc as (Hs & Hc). rewrite ws_run_cons.
      destruct (IH (ws_apply s P) (ws_apply_wf s P Hv Hp Hs)
                  (ws_apply_parse s P Hv Hp Hs) Hc)
        as (Hv' & Hp' & Hty' & Hbit').
      split; [exact Hv' |]. split; [exact Hp' |]. split.
      + rewrite Hty'. exact (ws_apply_type s P Hv Hp Hs).
      + intros b Hb Hnin. cbn [ws_freshs] in Hnin.
        assert (Hn1 : b ∉ ws_fresh s)
          by (intros Hc1; apply Hnin, elem_of_union; left; exact Hc1).
        assert (Hn2 : b ∉ ws_freshs l)
          by (intros Hc2; apply Hnin, elem_of_union; right; exact Hc2).
        rewrite (Hbit' b Hb Hn2).
        rewrite (ws_apply_bit s P b Hv Hp Hs Hb).
        rewrite (bool_decide_eq_false_2 (b ∈ ws_fresh s)) by exact Hn1.
        apply orb_false_r.
  Qed.

  Lemma ws_run_wf (l : list wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre_chain l P ->
    fs_durable_wf_view (ws_run l P).
  Proof. intros Hv Hp Hc. exact (proj1 (ws_run_ok l P Hv Hp Hc)). Qed.

  Lemma ws_run_parse (l : list wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre_chain l P ->
    fs_parse_sb (ws_run l P) = Some sb.
  Proof.
    intros Hv Hp Hc. exact (proj1 (proj2 (ws_run_ok l P Hv Hp Hc))).
  Qed.

  Lemma ws_run_type (l : list wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre_chain l P ->
    di_type (fs_dinode (ws_run l P) sb i) = di_type (fs_dinode P sb i).
  Proof.
    intros Hv Hp Hc.
    exact (proj1 (proj2 (proj2 (ws_run_ok l P Hv Hp Hc)))).
  Qed.

  Lemma ws_run_file_type (l : list wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre_chain l P ->
    ws_file_type P -> ws_file_type (ws_run l P).
  Proof.
    intros Hv Hp Hc Hty. unfold ws_file_type.
    rewrite (ws_run_type l P Hv Hp Hc). exact Hty.
  Qed.

  Lemma ws_run_bit (l : list wstep) (P : Z -> list (bv 8)) (b : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre_chain l P ->
    0 <= b < 8 * BSIZE_z -> b ∉ ws_freshs l ->
    fs_bit (ws_run l P (sb_bmapstart sb)) b = fs_bit (P (sb_bmapstart sb)) b.
  Proof.
    intros Hv Hp Hc Hb Hnin.
    exact (proj2 (proj2 (proj2 (ws_run_ok l P Hv Hp Hc))) b Hb Hnin).
  Qed.

  (* ==================================================================== *)
  (*  6.  THE WORKED COROLLARY: filewrite's CHUNK LOOP                     *)
  (*                                                                       *)
  (*  file.c's loop writes MAXOPBLOCKS-sized chunks; each chunk's writei   *)
  (*  appends whole blocks (bmap allocates, then the block's bytes are     *)
  (*  written) and raises the size.  The net per appended block is one     *)
  (*  alloc step -- TWO at the NDIRECT crossing, the indirect block and    *)
  (*  then the data block, which is no longer a fused pair (F3.2) --       *)
  (*  followed by one write step that carries the size move.               *)
  (* ==================================================================== *)

  (* the crossing's EXTRA step: at [fbn = NDIRECT] bmap allocates the
     indirect block before the data block *)
  Definition ws_alloc_pre (fi : Z) (fbn : nat) : list wstep :=
    if decide (fbn = 12%nat) then [ws_alloc_ind fi] else [].

  Definition ws_append (fi : Z) (fr : nat -> Z)
      (bsf : nat -> list (bv 8)) (szf : nat -> Z) (fbn : nat)
    : list wstep :=
    (ws_alloc_pre fi fbn
     ++ [ws_alloc fbn (fr fbn); ws_write fbn (bsf fbn) (szf fbn)])%list.

  Fixpoint ws_appends (fi : Z) (fr : nat -> Z)
      (bsf : nat -> list (bv 8)) (szf : nat -> Z) (n0 k : nat)
    : list wstep :=
    match k with
    | 0%nat => []
    | S k' => ws_append fi fr bsf szf n0 ++ ws_appends fi fr bsf szf (S n0) k'
    end.

  (* ONE APPENDED BLOCK: its step preconditions chain, the size lands one
     block further on, and every OTHER slot is where it was. *)
  Lemma ws_append_ok (fi : Z) (fr : nat -> Z) (bsf : nat -> list (bv 8))
      (szf : nat -> Z) (n0 : nat) (Q : Z -> list (bv 8)) :
    fs_durable_wf_view Q -> fs_parse_sb Q = Some sb ->
    0 <= i < sb_ninodes sb -> ws_file_type Q ->
    fs_nblk (bv_unsigned (di_size (fs_dinode Q sb i))) = Z.of_nat n0 ->
    fs_slot Q (fs_dinode Q sb i) n0 = 0 ->
    fs_nblk (szf n0) = Z.of_nat n0 + 1 ->
    0 <= szf n0 <= Z.of_nat FS_MAXFILE * BSIZE_z ->
    fs_data_start sb <= fr n0 < sb_size sb ->
    fs_bit (Q (sb_bmapstart sb)) (fr n0) = false ->
    (n0 = 12%nat ->
       bv_unsigned (di_addrs (fs_dinode Q sb i) !!! 12%nat) = 0
       /\ fs_data_start sb <= fi < sb_size sb
       /\ fs_bit (Q (sb_bmapstart sb)) fi = false
       /\ fi <> fr n0) ->
    ws_pre_chain (ws_append fi fr bsf szf n0) Q
    /\ fs_nblk (bv_unsigned (di_size (fs_dinode
                  (ws_run (ws_append fi fr bsf szf n0) Q) sb i)))
       = Z.of_nat (S n0)
    /\ (forall j : nat, (j <= FS_MAXFILE)%nat -> j <> n0 ->
          (n0 = 12%nat -> j <> FS_MAXFILE) ->
          fs_slot (ws_run (ws_append fi fr bsf szf n0) Q)
            (fs_dinode (ws_run (ws_append fi fr bsf szf n0) Q) sb i) j
          = fs_slot Q (fs_dinode Q sb i) j).
  Proof.
    intros Hv Hp Hi Hty Hnblk Hslot0 Hszn Hcap Hfrr Hbit Hcross.
    assert (HDM : (FS_NDIRECT + FS_NINDIRECT)%nat = FS_MAXFILE)
      by reflexivity.
    assert (HND : FS_NDIRECT = 12%nat) by reflexivity.
    pose proof (ws_type_live Q Hty) as Hlive.
    destruct (wfv_geom Q Hv Hp Hi)
      as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hone & HiN).
    pose proof (wfv_size_cap Q Hv Hp Hi Hlive) as Hszc.
    assert (Hds : 0 < fs_data_start sb) by (unfold SB_BNO in *; lia).
    assert (Hn0M : (n0 < FS_MAXFILE)%nat).
    { pose proof (fs_nblk_max (szf n0) (proj1 Hcap) (proj2 Hcap)). lia. }
    assert (Hfr0 : fr n0 <> 0) by (lia).
    (* --- the ALLOCATION prefix ---------------------------------------- *)
    (* the view the data-block allocation runs at is
       [ws_run (ws_alloc_pre fi n0) Q] -- [Q] itself away from the
       crossing *)
    assert (HLA : ws_pre_chain (ws_alloc_pre fi n0) Q
                  /\ fs_durable_wf_view (ws_run (ws_alloc_pre fi n0) Q)
                  /\ fs_parse_sb (ws_run (ws_alloc_pre fi n0) Q) = Some sb
                  /\ ws_file_type (ws_run (ws_alloc_pre fi n0) Q)
                  /\ bv_unsigned (di_size (fs_dinode (ws_run (ws_alloc_pre fi n0) Q) sb i))
                     = bv_unsigned (di_size (fs_dinode Q sb i))
                  /\ (forall j : nat, (j <= FS_MAXFILE)%nat ->
                        (n0 = 12%nat -> j <> FS_MAXFILE) ->
                        fs_slot (ws_run (ws_alloc_pre fi n0) Q) (fs_dinode (ws_run (ws_alloc_pre fi n0) Q) sb i) j
                        = fs_slot Q (fs_dinode Q sb i) j)
                  /\ ((12 <= n0)%nat ->
                        bv_unsigned (di_addrs (fs_dinode (ws_run (ws_alloc_pre fi n0) Q) sb i) !!! 12%nat)
                        <> 0)
                  /\ fs_bit ((ws_run (ws_alloc_pre fi n0) Q) (sb_bmapstart sb)) (fr n0) = false).
    { unfold ws_alloc_pre.
      destruct (decide (n0 = 12%nat)) as [Hn12 | Hne].
      - destruct (Hcross Hn12) as (Hibz & Hfir & Hfib & Hfine).
        assert (Hpa : ws_pre (ws_alloc_ind fi) Q).
        { split; [exact Hi |]. split; [exact Hty |].
          split; [exact Hibz |]. split; [exact Hfir | exact Hfib]. }
        cbn [ws_pre_chain ws_run fold_left].
        split; [split; [exact Hpa | exact I] |].
        assert (HvR : fs_durable_wf_view (ws_apply (ws_alloc_ind fi) Q))
          by exact (ws_apply_wf _ Q Hv Hp Hpa).
        assert (HpR : fs_parse_sb (ws_apply (ws_alloc_ind fi) Q) = Some sb)
          by exact (ws_apply_parse _ Q Hv Hp Hpa).
        assert (HtyR : ws_file_type (ws_apply (ws_alloc_ind fi) Q))
          by exact (ws_apply_file_type _ Q Hv Hp Hpa).
        assert (HszR : bv_unsigned (di_size (fs_dinode (ws_apply (ws_alloc_ind fi) Q) sb i))
                       = bv_unsigned (di_size (fs_dinode Q sb i)))
          by exact (ws_apply_size _ Q Hv Hp Hpa).
        assert (HslR : forall j : nat, (j <= FS_MAXFILE)%nat ->
                  j <> FS_MAXFILE ->
                  fs_slot (ws_apply (ws_alloc_ind fi) Q) (fs_dinode (ws_apply (ws_alloc_ind fi) Q) sb i) j
                  = fs_slot Q (fs_dinode Q sb i) j).
        { intros j Hj Hjm.
          rewrite (ws_apply_slot (ws_alloc_ind fi) Q j Hv Hp Hpa Hj).
          rewrite decide_False by exact Hjm. reflexivity. }
        assert (HibR : bv_unsigned (di_addrs (fs_dinode (ws_apply (ws_alloc_ind fi) Q) sb i) !!! 12%nat)
                       = fi).
        { rewrite <- (fs_slot_max (ws_apply (ws_alloc_ind fi) Q) (fs_dinode (ws_apply (ws_alloc_ind fi) Q) sb i)).
          rewrite (ws_apply_slot (ws_alloc_ind fi) Q FS_MAXFILE
                     Hv Hp Hpa ltac:(lia)).
          rewrite decide_True by reflexivity. reflexivity. }
        split; [exact HvR |]. split; [exact HpR |]. split; [exact HtyR |].
        split; [exact HszR |].
        (* the [j <> FS_MAXFILE] side condition is the caller's *)
        split; [intros j Hj Hjm; exact (HslR j Hj (Hjm Hn12)) |].
        split.
        + intros _. rewrite HibR. lia.
        + apply (ws_apply_bit_false (ws_alloc_ind fi) Q (fr n0)
                   Hv Hp Hpa ltac:(lia) Hbit).
          cbn [ws_fresh]. rewrite elem_of_singleton.
          intros Hc. exact (Hfine (eq_sym Hc)).
      - cbn [ws_pre_chain ws_run fold_left].
        split; [exact I |].
        split; [exact Hv |]. split; [exact Hp |]. split; [exact Hty |].
        split; [reflexivity |].
        split; [intros j _ _; reflexivity |].
        split; [| exact Hbit].
        intros Hge.
        assert (Hgt : (12 < n0)%nat) by lia.
        rewrite <- (fs_slot_max Q (fs_dinode Q sb i)).
        pose proof (wfv_cov Q FS_NDIRECT Hv Hp Hi Hlive ltac:(lia)
                      ltac:(lia)) as Hc.
        pose proof (wfv_dok Q Hv Hp Hi Hlive) as Hd.
        intros Hz. apply Hc.
        unfold fs_blk_addr.
        rewrite (proj2 (Nat.ltb_ge FS_NDIRECT FS_NDIRECT) ltac:(lia)).
        rewrite Nat.sub_diag. unfold fs_ind_ents.
        rewrite fs_slot_max in Hz. rewrite Hz.
        apply lookup_total_replicate_2. unfold FS_NINDIRECT. lia. }
    destruct HLA as (HcA & HvQ1 & HpQ1 & HtyQ1 & HszQ1 & HslQ1 & HibQ1 & HbQ1).
    set (Q1 := ws_run (ws_alloc_pre fi n0) Q) in *.
    (* --- the DATA-BLOCK allocation ------------------------------------ *)
    assert (Hslot1 : fs_slot Q1 (fs_dinode Q1 sb i) n0 = 0).
    { rewrite (HslQ1 n0 ltac:(lia) ltac:(lia)). exact Hslot0. }
    assert (Hpa1 : ws_pre (ws_alloc n0 (fr n0)) Q1).
    { split; [exact Hi |]. split; [exact HtyQ1 |].
      split; [lia |]. split; [exact Hslot1 |].
      split; [exact HibQ1 |]. split; [exact Hfrr | exact HbQ1]. }
    set (Q2 := ws_apply (ws_alloc n0 (fr n0)) Q1).
    assert (HvQ2 : fs_durable_wf_view Q2)
      by exact (ws_apply_wf _ Q1 HvQ1 HpQ1 Hpa1).
    assert (HpQ2 : fs_parse_sb Q2 = Some sb)
      by exact (ws_apply_parse _ Q1 HvQ1 HpQ1 Hpa1).
    assert (HtyQ2 : ws_file_type Q2)
      by exact (ws_apply_file_type _ Q1 HvQ1 HpQ1 Hpa1).
    assert (HszQ2 : bv_unsigned (di_size (fs_dinode Q2 sb i))
                    = bv_unsigned (di_size (fs_dinode Q sb i))).
    { transitivity (ws_newsize (ws_alloc n0 (fr n0)) Q1).
      - exact (ws_apply_size _ Q1 HvQ1 HpQ1 Hpa1).
      - cbn [ws_newsize]. exact HszQ1. }
    assert (HslQ2 : forall j : nat, (j <= FS_MAXFILE)%nat ->
              fs_slot Q2 (fs_dinode Q2 sb i) j
              = if decide (j = n0) then fr n0
                else fs_slot Q1 (fs_dinode Q1 sb i) j).
    { intros j Hj.
      exact (ws_apply_slot (ws_alloc n0 (fr n0)) Q1 j HvQ1 HpQ1 Hpa1 Hj). }
    (* --- the WRITE ------------------------------------------------------ *)
    assert (Hblk2 : fs_blk_addr Q2 (fs_dinode Q2 sb i) n0 <> 0).
    { rewrite <- (fs_slot_lt Q2 (fs_dinode Q2 sb i) n0 ltac:(lia)).
      rewrite (HslQ2 n0 ltac:(lia)), decide_True by reflexivity.
      exact Hfr0. }
    assert (Hcov2 : forall k0 : nat, (k0 < FS_MAXFILE)%nat ->
              Z.of_nat k0 < fs_nblk (szf n0) ->
              fs_blk_addr Q2 (fs_dinode Q2 sb i) k0 <> 0).
    { intros k0 Hk0 Hlt.
      rewrite <- (fs_slot_lt Q2 (fs_dinode Q2 sb i) k0 ltac:(lia)).
      rewrite (HslQ2 k0 ltac:(lia)).
      destruct (decide (k0 = n0)) as [-> | Hne0]; [exact Hfr0 |].
      rewrite (HslQ1 k0 ltac:(lia) ltac:(lia)).
      rewrite (fs_slot_lt Q (fs_dinode Q sb i) k0 ltac:(lia)).
      apply (wfv_cov Q k0 Hv Hp Hi Hlive Hk0). lia. }
    assert (Hpw : ws_pre (ws_write n0 (bsf n0) (szf n0)) Q2).
    { split; [exact Hi |]. split; [exact HtyQ2 |].
      split; [lia |]. split; [exact Hblk2 |].
      split; [exact Hcap | exact Hcov2]. }
    (* --- the three conclusions ------------------------------------------ *)
    assert (Hrun : ws_run (ws_append fi fr bsf szf n0) Q
                   = ws_apply (ws_write n0 (bsf n0) (szf n0)) Q2).
    { unfold ws_append. rewrite ws_run_app.
      cbn [ws_run fold_left]. reflexivity. }
    split.
    { unfold ws_append. apply ws_pre_chain_app.
      split; [exact HcA |].
      cbn [ws_pre_chain]. split; [exact Hpa1 |].
      split; [exact Hpw | exact I]. }
    split.
    { rewrite Hrun.
      rewrite (ws_apply_size (ws_write n0 (bsf n0) (szf n0)) Q2
                 HvQ2 HpQ2 Hpw).
      cbn [ws_newsize]. lia. }
    intros j Hj Hjn Hjm.
    rewrite Hrun.
    rewrite (ws_apply_slot (ws_write n0 (bsf n0) (szf n0)) Q2 j
               HvQ2 HpQ2 Hpw Hj).
    rewrite (HslQ2 j Hj), decide_False by exact Hjn.
    exact (HslQ1 j Hj Hjm).
  Qed.

  (* THE LEMMA THE FILEWRITE ARM INVOKES.  Every premise is read at the
     PRE-transaction view [Q].  A SHORT WRITE is this lemma at a smaller
     [k]; a PARTIAL FAILURE (writei's [break]) is the prefix of the step
     list that stops after an allocation, which [ws_run_wf] covers
     directly (durable-disk F3.3). *)
  Lemma ws_appends_wf (fi : Z) (fr : nat -> Z)
      (bsf : nat -> list (bv 8)) (szf : nat -> Z) (k : nat) :
    forall (n0 : nat) (Q : Z -> list (bv 8)),
    fs_durable_wf_view Q -> fs_parse_sb Q = Some sb ->
    0 <= i < sb_ninodes sb ->
    ws_file_type Q ->
    fs_nblk (bv_unsigned (di_size (fs_dinode Q sb i))) = Z.of_nat n0 ->
    (forall j : nat, (n0 <= j < n0 + k)%nat ->
       fs_slot Q (fs_dinode Q sb i) j = 0) ->
    (forall j : nat, (n0 <= j < n0 + k)%nat ->
       fs_nblk (szf j) = Z.of_nat j + 1
       /\ 0 <= szf j <= Z.of_nat FS_MAXFILE * BSIZE_z
       /\ fs_data_start sb <= fr j < sb_size sb
       /\ fs_bit (Q (sb_bmapstart sb)) (fr j) = false) ->
    (forall j j' : nat, (n0 <= j < n0 + k)%nat -> (n0 <= j' < n0 + k)%nat ->
       fr j = fr j' -> j = j') ->
    ((n0 <= 12 < n0 + k)%nat ->
       bv_unsigned (di_addrs (fs_dinode Q sb i) !!! 12%nat) = 0
       /\ fs_data_start sb <= fi < sb_size sb
       /\ fs_bit (Q (sb_bmapstart sb)) fi = false
       /\ (forall j : nat, (n0 <= j < n0 + k)%nat -> fi <> fr j)) ->
    fs_durable_wf_view (ws_run (ws_appends fi fr bsf szf n0 k) Q).
  Proof.
    induction k as [| k IH];
      intros n0 Q Hv Hp Hi Hty Hnblk Hslots Hblk Hinj Hcross.
    - rewrite ws_run_nil. exact Hv.
    - pose proof (ws_type_live Q Hty) as Hlive.
      destruct (wfv_geom Q Hv Hp Hi)
        as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hone & HiN).
      assert (Hds : 0 < fs_data_start sb) by (unfold SB_BNO in *; lia).
      destruct (Hblk n0 ltac:(lia)) as (Hsz0 & Hcap0 & Hfrr0 & Hbit0).
      destruct (ws_append_ok fi fr bsf szf n0 Q Hv Hp Hi Hty Hnblk
                  (Hslots n0 ltac:(lia)) Hsz0 Hcap0 Hfrr0 Hbit0
                  ltac:(intros Hn12;
                        destruct (Hcross ltac:(lia))
                          as (Ha & Hb & Hc & Hd);
                        split; [exact Ha |]; split; [exact Hb |];
                        split; [exact Hc |]; exact (Hd n0 ltac:(lia))))
        as (Hchain & Hnblk' & Hslot').
      assert (Hv' : fs_durable_wf_view (ws_run (ws_append fi fr bsf szf n0) Q))
        by exact (ws_run_wf _ Q Hv Hp Hchain).
      assert (Hp' : fs_parse_sb (ws_run (ws_append fi fr bsf szf n0) Q)
                    = Some sb)
        by exact (ws_run_parse _ Q Hv Hp Hchain).
      assert (Hty' : ws_file_type (ws_run (ws_append fi fr bsf szf n0) Q))
        by exact (ws_run_file_type _ Q Hv Hp Hchain Hty).
      (* every LATER block's bit is still what [Q] said it was *)
      assert (Hlater : forall b : Z,
                fs_data_start sb <= b < sb_size sb ->
                b <> fr n0 -> (n0 = 12%nat -> b <> fi) ->
                fs_bit (ws_run (ws_append fi fr bsf szf n0) Q
                          (sb_bmapstart sb)) b
                = fs_bit (Q (sb_bmapstart sb)) b).
      { intros b Hb Hbne Hbfi.
        apply (ws_run_bit _ Q b Hv Hp Hchain);
          [lia |].
        unfold ws_append, ws_alloc_pre.
        destruct (decide (n0 = 12%nat)) as [Hn12 | Hne];
          cbn [ws_freshs ws_fresh app]; intros Hc.
        - apply elem_of_union in Hc as [Hc | Hc].
          + apply elem_of_singleton in Hc. exact (Hbfi Hn12 Hc).
          + apply elem_of_union in Hc as [Hc | Hc].
            * apply elem_of_singleton in Hc. exact (Hbne Hc).
            * rewrite elem_of_union, !elem_of_empty in Hc. tauto.
        - apply elem_of_union in Hc as [Hc | Hc].
          + apply elem_of_singleton in Hc. exact (Hbne Hc).
          + rewrite elem_of_union, !elem_of_empty in Hc. tauto. }
      assert (HjM : forall j : nat, (n0 <= j < n0 + S k)%nat ->
                (j < FS_MAXFILE)%nat).
      { intros j Hj. destruct (Hblk j Hj) as (H1 & H2 & _).
        pose proof (fs_nblk_max (szf j) (proj1 H2) (proj2 H2)). lia. }
      cbn [ws_appends]. rewrite ws_run_app.
      apply (IH (S n0) _ Hv' Hp' Hi Hty' Hnblk').
      + intros j Hj.
        assert (HjL : (j < FS_MAXFILE)%nat) by (apply HjM; lia).
        assert (Hj1 : (j <= FS_MAXFILE)%nat) by lia.
        assert (Hj2 : j <> n0) by lia.
        assert (Hj3 : n0 = 12%nat -> j <> FS_MAXFILE) by (intros _; lia).
        rewrite (Hslot' j Hj1 Hj2 Hj3). exact (Hslots j ltac:(lia)).
      + intros j Hj. destruct (Hblk j ltac:(lia)) as (H1 & H2 & H3 & H4).
        split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
        assert (Hb1 : fr j <> fr n0).
        { intros Hc.
          assert (Hje : j = n0) by (apply Hinj; [lia | lia | exact Hc]).
          lia. }
        assert (Hb2 : n0 = 12%nat -> fr j <> fi).
        { intros Hn12 Hc.
          destruct (Hcross ltac:(lia)) as (_ & _ & _ & Hfine).
          exact (Hfine j ltac:(lia) (eq_sym Hc)). }
        rewrite (Hlater (fr j) H3 Hb1 Hb2). exact H4.
      + intros j j' Hj Hj'. apply Hinj; lia.
      + intros Hc12.
        assert (Hn0lt : (n0 < 12)%nat) by lia.
        destruct (Hcross ltac:(lia)) as (Hibz & Hfri & Hbii & Hfine).
        assert (Hj1 : (FS_MAXFILE <= FS_MAXFILE)%nat) by lia.
        assert (Hj2 : FS_MAXFILE <> n0)
          by (unfold FS_MAXFILE in *; lia).
        assert (Hj3 : n0 = 12%nat -> FS_MAXFILE <> FS_MAXFILE)
          by (intros Hc; exfalso; lia).
        split.
        * rewrite <- (fs_slot_max
                        (ws_run (ws_append fi fr bsf szf n0) Q)
                        (fs_dinode (ws_run (ws_append fi fr bsf szf n0) Q)
                           sb i)).
          rewrite (Hslot' FS_MAXFILE Hj1 Hj2 Hj3), fs_slot_max. exact Hibz.
        * split; [exact Hfri |]. split.
          -- assert (Hb1 : fi <> fr n0) by exact (Hfine n0 ltac:(lia)).
             assert (Hb2 : n0 = 12%nat -> fi <> fi)
               by (intros Hc; exfalso; lia).
             rewrite (Hlater fi Hfri Hb1 Hb2). exact Hbii.
          -- intros j Hj. apply Hfine. lia.
  Qed.

End OpFilewrite.
