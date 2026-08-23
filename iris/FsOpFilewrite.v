(* FsOpFilewrite.v -- durable-disk stage G2, batch (1): the standalone
   per-op preservation lemma family for the FILEWRITE op family.

   ONE filewrite transaction's net effect on the committed view is a
   SEQUENCE of stage-F2 effects at a FIXED inode [i]:

     (eff_alloc_file_block | eff_alloc_ind_block | eff_write_file_data)*

   -- bmap's balloc at each append slot (the [fbn = 12] crossing being the
   fused two-block effect), then writei's per-block byte write.  The file
   has three parts.

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
     a step carries only the append slot / the fresh blocks / the bytes,
     and -- in every arm -- the size the record moves to. *)
  Inductive wstep : Type :=
  | ws_alloc (fbn : nat) (fresh sz' : Z)
  | ws_alloc_ind (fresh_ind fresh_data sz' : Z)
  | ws_write (fbn : nat) (bs : list (bv 8)) (sz' : Z).

  Definition ws_apply (s : wstep) (P : Z -> list (bv 8))
    : Z -> list (bv 8) :=
    match s with
    | ws_alloc fbn fresh sz' => eff_alloc_file_block P sb i fbn fresh sz'
    | ws_alloc_ind fi fd sz' => eff_alloc_ind_block P sb i fi fd sz'
    | ws_write fbn bs sz' => eff_write_file_data P sb i fbn bs sz'
    end.

  Definition ws_run (l : list wstep) (P : Z -> list (bv 8))
    : Z -> list (bv 8) :=
    fold_left (fun Q s => ws_apply s Q) l P.

  (* the size the step installs, and the blocks it marks in the bitmap *)
  Definition ws_size (s : wstep) : Z :=
    match s with
    | ws_alloc _ _ sz' => sz'
    | ws_alloc_ind _ _ sz' => sz'
    | ws_write _ _ sz' => sz'
    end.

  Definition ws_fresh (s : wstep) : gset Z :=
    match s with
    | ws_alloc _ f _ => {[f]}
    | ws_alloc_ind fi fd _ => {[fi]} ∪ {[fd]}
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
    | ws_alloc fbn fresh sz' =>
        if (fbn <? 12)%nat
        then di_set_size_addr dn (Z_to_bv 32 sz') fbn (Z_to_bv 32 fresh)
        else di_set_size dn (Z_to_bv 32 sz')
    | ws_alloc_ind fi _ sz' =>
        di_set_size_addr dn (Z_to_bv 32 sz') 12 (Z_to_bv 32 fi)
    | ws_write _ _ sz' => di_set_size dn (Z_to_bv 32 sz')
    end.

  (* filewrite's inode is a FILE (the FD_INODE arm) -- or a device record
     reached through writei, which the effect vocabulary also admits.
     Either way it is not a directory, which is what the alloc effects'
     directory side conditions ask. *)
  Definition ws_file_type (P : Z -> list (bv 8)) : Prop :=
    bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
    \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z.

  (* THE STEP PRECONDITION, AT THE CURRENT VIEW.  Decode level throughout:
     the record's type and size as this view decodes them, and the fresh
     blocks' bits as this view's bitmap block reads them (balloc's own
     postcondition). *)
  Definition ws_pre (s : wstep) (P : Z -> list (bv 8)) : Prop :=
    0 <= i < sb_ninodes sb
    /\ ws_file_type P
    /\ match s with
       | ws_alloc fbn fresh sz' =>
           Z.of_nat fbn = fs_nblk (bv_unsigned (di_size (fs_dinode P sb i)))
           /\ fbn <> 12%nat
           /\ fs_nblk sz' = Z.of_nat fbn + 1
           /\ sz' <= Z.of_nat FS_MAXFILE * BSIZE_z
           /\ fs_data_start sb <= fresh < sb_size sb
           /\ fs_bit (P (sb_bmapstart sb)) fresh = false
       | ws_alloc_ind fi fd sz' =>
           Z.of_nat 12 = fs_nblk (bv_unsigned (di_size (fs_dinode P sb i)))
           /\ fs_nblk sz' = 13
           /\ sz' <= Z.of_nat FS_MAXFILE * BSIZE_z
           /\ fs_data_start sb <= fi < sb_size sb
           /\ fs_data_start sb <= fd < sb_size sb
           /\ fi <> fd
           /\ fs_bit (P (sb_bmapstart sb)) fi = false
           /\ fs_bit (P (sb_bmapstart sb)) fd = false
       | ws_write fbn _ sz' =>
           Z.of_nat fbn < fs_nblk (bv_unsigned (di_size (fs_dinode P sb i)))
           /\ fs_nblk sz'
              = fs_nblk (bv_unsigned (di_size (fs_dinode P sb i)))
           /\ 0 <= sz' <= Z.of_nat FS_MAXFILE * BSIZE_z
       end.

  (* SEQUENTIALLY: each step's precondition at the view the earlier steps
     produced.  This is the shape a transaction proof can actually
     discharge -- see section 6 for how. *)
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

  (* the indirect POINTER: zero while the file is direct-only, a real data
     block once it is not.  Either way it is neither the superblock, nor
     the bitmap block, nor the record's own inode block -- which is all the
     footprint lemma wants of it. *)
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
    destruct (Z.le_gt_cases
                (fs_nblk (bv_unsigned (di_size (fs_dinode P sb i))))
                (Z.of_nat FS_NDIRECT)) as [Hle | Hgt].
    - pose proof (fdi_ind_zero _ _ _ Hd Hle) as Hz.
      rewrite Hz. unfold SB_BNO in *. repeat split; lia.
    - pose proof (fdi_ind _ _ _ Hd Hgt) as Hr.
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
    destruct Hv as (sb0 & Hp0 & Hsw).
    assert (Hse : sb0 = sb) by congruence. subst sb0.
    destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
    destruct HW45 as (u & Hu & Hbm).
    destruct Hregx as (nib & Hnibz & Hreg).
    destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
    exact (blk_addr_covered P sb Hp0 Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg
             rd Hrd Hdok Hlkg Horph i k Hi Hlive HkM Hk).
  Qed.

  (* the two readings of [ws_file_type] the effect wrappers ask for *)
  Lemma ws_type_live (P : Z -> list (bv 8)) :
    ws_file_type P -> bv_unsigned (di_type (fs_dinode P sb i)) <> 0.
  Proof.
    intros [H | H]; rewrite H; unfold T_FILE_z, T_DEVICE_z; discriminate.
  Qed.

  Lemma ws_type_nondir (P : Z -> list (bv 8)) (X : Prop) :
    ws_file_type P ->
    bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z -> X.
  Proof.
    intros [H | H] Hd; rewrite H in Hd;
      unfold T_FILE_z, T_DEVICE_z, T_DIR_z in Hd; discriminate.
  Qed.

  (* the decode at [i] from ONE block equation -- [eff_dinode_dec] with
     the surrounding [fs_upd]s already stripped *)
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
    destruct s as [fbn f sz' | fi fd sz' | fbn bs sz']; cbn [ws_dinode].
    - destruct (fbn <? 12)%nat.
      + apply di_set_size_addr_wf, fs_dinode_wf.
      + apply di_set_size_wf, fs_dinode_wf.
    - apply di_set_size_addr_wf, fs_dinode_wf.
    - apply di_set_size_wf, fs_dinode_wf.
  Qed.

  (* ==================================================================== *)
  (*  4.  PER-STEP DECODE TRANSPORT                                        *)
  (*                                                                       *)
  (*  What one step does to the three things the NEXT step's precondition  *)
  (*  reads: the superblock (nothing), the record at [i], and the bitmap   *)
  (*  block.  Everything below is read off the effect definitions.         *)
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
    destruct s as [fbn f sz' | fi fd sz' | fbn bs sz'].
    - (* ws_alloc: the record block, the bitmap block, the fresh block,
         and -- on the indirect-ENTRY arm -- the indirect block *)
      destruct Hs as (Hfbn & Hne12 & Hnb & Hcap & Hfr & Hbit).
      cbn [ws_apply ws_fresh].
      unfold eff_alloc_file_block. cbv zeta.
      repeat split.
      + rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        destruct (fbn <? 12)%nat.
        * apply (eff_dinode_out sb). unfold SB_BNO in *. lia.
        * rewrite fs_upd_ne by exact Hx1.
          apply (eff_dinode_out sb). unfold SB_BNO in *. lia.
      + apply (dinode_at P _ _ Hok HiN (ws_dinode_wf P (ws_alloc fbn f sz'))).
        cbn [ws_dinode].
        rewrite fs_upd_ne by lia. rewrite fs_upd_ne by lia.
        destruct (fbn <? 12)%nat; [reflexivity |].
        rewrite fs_upd_ne by exact Hx2. reflexivity.
      + rewrite fs_upd_ne by lia. apply fs_upd_at.
    - (* ws_alloc_ind: the record block, the bitmap block, the two fresh
         blocks; the indirect block IS one of the two fresh blocks *)
      destruct Hs as (Hfbn & Hnb & Hcap & Hfri & Hfrd & Hne & Hbi & Hbd).
      cbn [ws_apply ws_fresh].
      unfold eff_alloc_ind_block. cbv zeta.
      repeat split.
      + rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        rewrite fs_upd_ne by (unfold SB_BNO in *; lia).
        apply (eff_dinode_out sb). unfold SB_BNO in *. lia.
      + apply (dinode_at P _ _ Hok HiN
                 (ws_dinode_wf P (ws_alloc_ind fi fd sz'))).
        cbn [ws_dinode].
        rewrite fs_upd_ne by lia. rewrite fs_upd_ne by lia.
        rewrite fs_upd_ne by lia. reflexivity.
      + rewrite fs_upd_ne by lia. rewrite fs_upd_ne by lia.
        rewrite fs_upd_at. f_equal. symmetry. apply union_assoc_L.
    - (* ws_write: the record block and the destination content block *)
      destruct Hs as (Hfbn & Hnbe & Hcap).
      pose proof (wfv_blk_addr P fbn Hv Hp Hi Hlive Hfbn) as Ha.
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

  (* (T0) THE SUPERBLOCK NEVER MOVES -- so the whole chain reads its
     preconditions at ONE [sb]. *)
  Lemma ws_apply_parse (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    fs_parse_sb (ws_apply s P) = Some sb.
  Proof.
    intros Hv Hp Hs.
    destruct (ws_apply_blocks s P Hv Hp Hs) as (Hsbb & _ & _).
    rewrite (fs_parse_sb_ext P (ws_apply s P) Hsbb). exact Hp.
  Qed.

  (* (T1) THE STEP PRESERVES THE FS INVARIANT -- the F2 wrappers, with
     [ws_pre]'s decode-level premises handed over as they stand. *)
  Lemma ws_apply_wf (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    fs_durable_wf_view (ws_apply s P).
  Proof.
    intros Hv Hp (Hi & Hty & Hs).
    pose proof (ws_type_live P Hty) as Hlive.
    destruct s as [fbn f sz' | fi fd sz' | fbn bs sz'].
    - destruct Hs as (Hfbn & Hne12 & Hnb & Hcap & Hfr & Hbit).
      apply (eff_alloc_file_block_wfv P sb i fbn f sz'
               Hv Hp Hi Hlive Hfbn Hne12 Hnb Hcap
               (fun Hd => ws_type_nondir P _ Hty Hd) Hfr Hbit).
    - destruct Hs as (Hfbn & Hnb & Hcap & Hfri & Hfrd & Hne & Hbi & Hbd).
      apply (eff_alloc_ind_block_wfv P sb i fi fd sz'
               Hv Hp Hi Hlive Hfbn Hnb Hcap
               (fun Hd => ws_type_nondir P _ Hty Hd) Hfri Hfrd Hne Hbi Hbd).
    - destruct Hs as (Hfbn & Hnbe & Hcap).
      apply (eff_write_file_data_wfv P sb i fbn bs sz'
               Hv Hp Hi Hty Hfbn Hnbe Hcap).
  Qed.

  (* (T2) THE TYPE IS INVARIANT -- every step moves size and addrs only *)
  Lemma ws_apply_type (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    di_type (fs_dinode (ws_apply s P) sb i) = di_type (fs_dinode P sb i).
  Proof.
    intros Hv Hp Hs.
    rewrite (proj1 (proj2 (ws_apply_blocks s P Hv Hp Hs))).
    destruct Hs as (_ & _ & Hs).
    destruct s as [fbn f sz' | fi fd sz' | fbn bs sz']; cbn [ws_dinode].
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

  (* (T3) THE SIZE AFTER THE STEP IS THE STEP'S OWN [sz'] -- which is what
     makes the append arithmetic below chain: [fs_nblk (ws_size s)] is the
     next slot. *)
  Lemma ws_apply_size (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    bv_unsigned (di_size (fs_dinode (ws_apply s P) sb i)) = ws_size s.
  Proof.
    intros Hv Hp Hs.
    rewrite (proj1 (proj2 (ws_apply_blocks s P Hv Hp Hs))).
    destruct Hs as (Hi & Hty & Hs).
    destruct s as [fbn f sz' | fi fd sz' | fbn bs sz'];
      cbn [ws_size ws_dinode].
    - destruct Hs as (Hfbn & Hne12 & Hnb & Hcap & _).
      assert (Hpos : 0 < sz') by (apply fs_nblk_pos; lia).
      destruct (fbn <? 12)%nat;
        cbn [di_size di_set_size_addr di_set_size];
        apply bv32_of_size; lia.
    - destruct Hs as (Hfbn & Hnb & Hcap & _).
      assert (Hpos : 0 < sz') by (apply fs_nblk_pos; lia).
      cbn [di_size di_set_size_addr]. apply bv32_of_size. lia.
    - destruct Hs as (Hfbn & Hnbe & Hcap).
      cbn [di_size di_set_size]. apply bv32_of_size. lia.
  Qed.

  (* (T4) THE BITMAP ACCUMULATES EXACTLY THE STEP'S OWN FRESH BLOCKS --
     so a block distinct from them keeps the bit balloc read. *)
  Lemma ws_apply_bit (s : wstep) (P : Z -> list (bv 8)) (b : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    0 <= b < 8 * BSIZE_z ->
    fs_bit (ws_apply s P (sb_bmapstart sb)) b
    = fs_bit (P (sb_bmapstart sb)) b || bool_decide (b ∈ ws_fresh s).
  Proof.
    intros Hv Hp Hs Hb.
    rewrite (proj2 (proj2 (ws_apply_blocks s P Hv Hp Hs))).
    destruct Hs as (_ & _ & Hs).
    destruct s as [fbn f sz' | fi fd sz' | fbn bs sz'].
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

  (* THE ONE INDUCTION.  [fs_parse_sb] rides along because the chain's
     preconditions are all stated at ONE [sb] -- the four clauses are what
     the induction needs of itself, and the named corollaries below are
     what a caller uses. *)
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

  (* THE CHAIN LEMMA: a well-formed view and sequentially-satisfied step
     preconditions give a well-formed view of the fold. *)
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

  (* (a) A FRESH BLOCK DISTINCT FROM THE EARLIER-ALLOCATED ONES STILL HAS
     A CLEARED BIT: the bitmap accumulates exactly the earlier steps'
     fresh blocks, so balloc's postcondition -- read at the PRE-
     transaction view -- survives the prefix. *)
  Lemma ws_run_bit (l : list wstep) (P : Z -> list (bv 8)) (b : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre_chain l P ->
    0 <= b < 8 * BSIZE_z -> b ∉ ws_freshs l ->
    fs_bit (ws_run l P (sb_bmapstart sb)) b = fs_bit (P (sb_bmapstart sb)) b.
  Proof.
    intros Hv Hp Hc Hb Hnin.
    exact (proj2 (proj2 (proj2 (ws_run_ok l P Hv Hp Hc))) b Hb Hnin).
  Qed.

  (* (b) THE SIZE AFTER A RUN IS THE LAST STEP'S OWN [sz'] *)
  Lemma ws_run_size (l : list wstep) (s : wstep) (P : Z -> list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    ws_pre_chain (l ++ [s]) P ->
    bv_unsigned (di_size (fs_dinode (ws_run (l ++ [s]) P) sb i)) = ws_size s.
  Proof.
    intros Hv Hp Hc.
    apply ws_pre_chain_app in Hc as (Hc1 & Hc2).
    destruct Hc2 as (Hs & _).
    rewrite ws_run_app, ws_run_cons, ws_run_nil.
    exact (ws_apply_size s (ws_run l P)
             (ws_run_wf l P Hv Hp Hc1) (ws_run_parse l P Hv Hp Hc1) Hs).
  Qed.

  (* ==================================================================== *)
  (*  6.  PRECONDITION TRANSPORT ACROSS ONE STEP                           *)
  (*                                                                       *)
  (*  The lemmas an arm actually invokes: the next step's premises are     *)
  (*  ARITHMETIC on the previous step's [ws_size], plus a bitmap bit read  *)
  (*  at the PREVIOUS view and a distinctness from that step's own fresh   *)
  (*  blocks.  Nothing here reads the post-step view.                      *)
  (* ==================================================================== *)

  (* (d) THE APPEND POSITION CHAINS: [fs_nblk (ws_size s)] is the next
     slot, so consecutive appends are [fbn], [fbn + 1], ... *)
  Lemma ws_pre_alloc_after (s : wstep) (P : Z -> list (bv 8))
      (fbn : nat) (fresh sz' : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    Z.of_nat fbn = fs_nblk (ws_size s) ->
    fbn <> 12%nat ->
    fs_nblk sz' = Z.of_nat fbn + 1 ->
    sz' <= Z.of_nat FS_MAXFILE * BSIZE_z ->
    fs_data_start sb <= fresh < sb_size sb ->
    fs_bit (P (sb_bmapstart sb)) fresh = false ->
    fresh ∉ ws_fresh s ->
    ws_pre (ws_alloc fbn fresh sz') (ws_apply s P).
  Proof.
    intros Hv Hp Hs Hfbn Hne12 Hnb Hcap Hfr Hbit Hnin.
    destruct (wfv_geom P Hv Hp (proj1 Hs))
      as (_ & _ & Hg3 & Hg4 & _ & Hone & _).
    assert (Hrng : 0 <= fresh < 8 * BSIZE_z)
      by (unfold SB_BNO in *; lia).
    split; [exact (proj1 Hs) |].
    split; [exact (ws_apply_file_type s P Hv Hp Hs) |].
    rewrite (ws_apply_size s P Hv Hp Hs).
    repeat split; try assumption; try lia.
    exact (ws_apply_bit_false s P fresh Hv Hp Hs Hrng Hbit Hnin).
  Qed.

  Lemma ws_pre_alloc_ind_after (s : wstep) (P : Z -> list (bv 8))
      (fi fd sz' : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    Z.of_nat 12 = fs_nblk (ws_size s) ->
    fs_nblk sz' = 13 ->
    sz' <= Z.of_nat FS_MAXFILE * BSIZE_z ->
    fs_data_start sb <= fi < sb_size sb ->
    fs_data_start sb <= fd < sb_size sb ->
    fi <> fd ->
    fs_bit (P (sb_bmapstart sb)) fi = false ->
    fs_bit (P (sb_bmapstart sb)) fd = false ->
    fi ∉ ws_fresh s -> fd ∉ ws_fresh s ->
    ws_pre (ws_alloc_ind fi fd sz') (ws_apply s P).
  Proof.
    intros Hv Hp Hs Hfbn Hnb Hcap Hfri Hfrd Hne Hbi Hbd Hni Hnd.
    destruct (wfv_geom P Hv Hp (proj1 Hs))
      as (_ & _ & Hg3 & Hg4 & _ & Hone & _).
    assert (Hri : 0 <= fi < 8 * BSIZE_z) by (unfold SB_BNO in *; lia).
    assert (Hrd : 0 <= fd < 8 * BSIZE_z) by (unfold SB_BNO in *; lia).
    split; [exact (proj1 Hs) |].
    split; [exact (ws_apply_file_type s P Hv Hp Hs) |].
    rewrite (ws_apply_size s P Hv Hp Hs).
    repeat split; try assumption; try lia.
    - exact (ws_apply_bit_false s P fi Hv Hp Hs Hri Hbi Hni).
    - exact (ws_apply_bit_false s P fd Hv Hp Hs Hrd Hbd Hnd).
  Qed.

  Lemma ws_pre_write_after (s : wstep) (P : Z -> list (bv 8))
      (fbn : nat) (bs : list (bv 8)) (sz' : Z) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb -> ws_pre s P ->
    Z.of_nat fbn < fs_nblk (ws_size s) ->
    fs_nblk sz' = fs_nblk (ws_size s) ->
    0 <= sz' <= Z.of_nat FS_MAXFILE * BSIZE_z ->
    ws_pre (ws_write fbn bs sz') (ws_apply s P).
  Proof.
    intros Hv Hp Hs Hfbn Hnbe Hcap.
    split; [exact (proj1 Hs) |].
    split; [exact (ws_apply_file_type s P Hv Hp Hs) |].
    rewrite (ws_apply_size s P Hv Hp Hs).
    repeat split; try assumption; try lia.
  Qed.

  (* (c) A WRITE TO THE JUST-ALLOCATED BLOCK: the append made the slot
     covered and left the size where the write wants it, so the write's
     premises hold with NO further hypothesis. *)
  Lemma ws_pre_write_after_alloc (P : Z -> list (bv 8))
      (fbn : nat) (fresh sz' : Z) (bs : list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    ws_pre (ws_alloc fbn fresh sz') P ->
    ws_pre (ws_write fbn bs sz') (ws_apply (ws_alloc fbn fresh sz') P).
  Proof.
    intros Hv Hp Hs.
    assert (Hnb : fs_nblk sz' = Z.of_nat fbn + 1)
      by (destruct Hs as (_ & _ & _ & _ & H & _); exact H).
    assert (Hcap : sz' <= Z.of_nat FS_MAXFILE * BSIZE_z)
      by (destruct Hs as (_ & _ & _ & _ & _ & H & _); exact H).
    assert (Hpos : 0 < sz') by (apply fs_nblk_pos; lia).
    apply (ws_pre_write_after (ws_alloc fbn fresh sz') P fbn bs sz'
             Hv Hp Hs); cbn [ws_size]; lia.
  Qed.

  Lemma ws_pre_write_after_alloc_ind (P : Z -> list (bv 8))
      (fi fd sz' : Z) (bs : list (bv 8)) :
    fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
    ws_pre (ws_alloc_ind fi fd sz') P ->
    ws_pre (ws_write 12 bs sz') (ws_apply (ws_alloc_ind fi fd sz') P).
  Proof.
    intros Hv Hp Hs.
    assert (H12 : Z.of_nat 12 = 12) by reflexivity.
    assert (Hnb : fs_nblk sz' = 13)
      by (destruct Hs as (_ & _ & _ & H & _); exact H).
    assert (Hcap : sz' <= Z.of_nat FS_MAXFILE * BSIZE_z)
      by (destruct Hs as (_ & _ & _ & _ & H & _); exact H).
    assert (Hpos : 0 < sz') by (apply fs_nblk_pos; lia).
    apply (ws_pre_write_after (ws_alloc_ind fi fd sz') P 12%nat bs sz'
             Hv Hp Hs); cbn [ws_size]; lia.
  Qed.

  (* ==================================================================== *)
  (*  7.  THE WORKED COROLLARY: filewrite's CHUNK LOOP                     *)
  (*                                                                       *)
  (*  file.c's loop writes MAXOPBLOCKS-sized chunks; each chunk's writei    *)
  (*  appends whole blocks (bmap allocates, then the block's bytes are     *)
  (*  written) and raises the size.  The net per appended block is one     *)
  (*  alloc step (the fused two-block effect at the 12-crossing) followed  *)
  (*  by one write step at the same size.                                  *)
  (* ==================================================================== *)

  Definition ws_alloc_at (fi : Z) (fr : nat -> Z) (szf : nat -> Z)
      (fbn : nat) : wstep :=
    if decide (fbn = 12%nat)
    then ws_alloc_ind fi (fr fbn) (szf fbn)
    else ws_alloc fbn (fr fbn) (szf fbn).

  Definition ws_append (fi : Z) (fr : nat -> Z)
      (bsf : nat -> list (bv 8)) (szf : nat -> Z) (fbn : nat)
    : list wstep :=
    [ws_alloc_at fi fr szf fbn; ws_write fbn (bsf fbn) (szf fbn)].

  Fixpoint ws_appends (fi : Z) (fr : nat -> Z)
      (bsf : nat -> list (bv 8)) (szf : nat -> Z) (n0 k : nat)
    : list wstep :=
    match k with
    | 0%nat => []
    | S k' => ws_append fi fr bsf szf n0 ++ ws_appends fi fr bsf szf (S n0) k'
    end.

  (* THE LEMMA THE FILEWRITE ARM INVOKES.  Every premise is read at the
     PRE-transaction view [Q]: the record's type and block count, each
     appended block's target size and balloc's cleared bit, that the
     allocator never hands out one block twice, and -- only when the range
     crosses 12 -- the indirect block.  A SHORT WRITE is this lemma at a
     smaller [k]. *)
  Lemma ws_appends_wf (fi : Z) (fr : nat -> Z)
      (bsf : nat -> list (bv 8)) (szf : nat -> Z) (k : nat) :
    forall (n0 : nat) (Q : Z -> list (bv 8)),
    fs_durable_wf_view Q -> fs_parse_sb Q = Some sb ->
    0 <= i < sb_ninodes sb ->
    ws_file_type Q ->
    fs_nblk (bv_unsigned (di_size (fs_dinode Q sb i))) = Z.of_nat n0 ->
    (forall j : nat, (n0 <= j < n0 + k)%nat ->
       fs_nblk (szf j) = Z.of_nat j + 1
       /\ szf j <= Z.of_nat FS_MAXFILE * BSIZE_z
       /\ fs_data_start sb <= fr j < sb_size sb
       /\ fs_bit (Q (sb_bmapstart sb)) (fr j) = false) ->
    (forall j j' : nat, (n0 <= j < n0 + k)%nat -> (n0 <= j' < n0 + k)%nat ->
       fr j = fr j' -> j = j') ->
    ((n0 <= 12 < n0 + k)%nat ->
       fs_data_start sb <= fi < sb_size sb
       /\ fs_bit (Q (sb_bmapstart sb)) fi = false
       /\ (forall j : nat, (n0 <= j < n0 + k)%nat -> fi <> fr j)) ->
    fs_durable_wf_view (ws_run (ws_appends fi fr bsf szf n0 k) Q).
  Proof.
    induction k as [| k IH];
      intros n0 Q Hv Hp Hi Hty Hnblk Hblk Hinj Hcross.
    - rewrite ws_run_nil. exact Hv.
    - assert (H12 : Z.of_nat 12 = 12) by reflexivity.
      destruct (wfv_geom Q Hv Hp Hi)
        as (_ & _ & Hg3 & Hg4 & Hg5 & Hone & _).
      destruct (Hblk n0 ltac:(lia)) as (Hsz0 & Hcap0 & Hfr0 & Hbit0).
      (* the two steps of block [n0], and their preconditions *)
      assert (Hboth : ws_pre (ws_alloc_at fi fr szf n0) Q
                      /\ ws_pre (ws_write n0 (bsf n0) (szf n0))
                           (ws_apply (ws_alloc_at fi fr szf n0) Q)).
      { unfold ws_alloc_at.
        destruct (decide (n0 = 12%nat)) as [Hn12 | Hne].
        - assert (Hpa : ws_pre (ws_alloc_ind fi (fr n0) (szf n0)) Q).
          { destruct (Hcross ltac:(lia)) as (Hfri & Hbii & Hfine).
            split; [exact Hi |]. split; [exact Hty |].
            repeat split; try assumption; try lia.
            exact (Hfine n0 ltac:(lia)). }
          split; [exact Hpa |].
          rewrite Hn12 in Hpa |- *.
          exact (ws_pre_write_after_alloc_ind Q fi (fr 12%nat) (szf 12%nat)
                   (bsf 12%nat) Hv Hp Hpa).
        - assert (Hpa : ws_pre (ws_alloc n0 (fr n0) (szf n0)) Q).
          { split; [exact Hi |]. split; [exact Hty |].
            repeat split; try assumption; try lia. }
          split; [exact Hpa |].
          exact (ws_pre_write_after_alloc Q n0 (fr n0) (szf n0)
                   (bsf n0) Hv Hp Hpa). }
      destruct Hboth as (Hpa & Hpw).
      assert (Hchain : ws_pre_chain (ws_append fi fr bsf szf n0) Q).
      { unfold ws_append. cbn [ws_pre_chain].
        split; [exact Hpa | split; [exact Hpw | exact I]]. }
      (* the invariant, re-established after the block *)
      assert (Hv' : fs_durable_wf_view (ws_run (ws_append fi fr bsf szf n0) Q))
        by exact (ws_run_wf _ Q Hv Hp Hchain).
      assert (Hp' : fs_parse_sb (ws_run (ws_append fi fr bsf szf n0) Q)
                    = Some sb)
        by exact (ws_run_parse _ Q Hv Hp Hchain).
      assert (Hty' : ws_file_type (ws_run (ws_append fi fr bsf szf n0) Q))
        by exact (ws_run_file_type _ Q Hv Hp Hchain Hty).
      assert (Hnblk' :
                fs_nblk (bv_unsigned
                           (di_size (fs_dinode
                                       (ws_run (ws_append fi fr bsf szf n0) Q)
                                       sb i)))
                = Z.of_nat (S n0)).
      { unfold ws_append. rewrite ws_run_cons, ws_run_cons, ws_run_nil.
        rewrite (ws_apply_size (ws_write n0 (bsf n0) (szf n0))
                   (ws_apply (ws_alloc_at fi fr szf n0) Q)
                   (ws_apply_wf _ Q Hv Hp Hpa)
                   (ws_apply_parse _ Q Hv Hp Hpa) Hpw).
        cbn [ws_size]. lia. }
      (* every LATER block's bit is still what [Q] said it was *)
      assert (Hlater : forall b : Z,
                fs_data_start sb <= b < sb_size sb ->
                b <> fr n0 -> ((n0 = 12%nat) -> b <> fi) ->
                fs_bit (ws_run (ws_append fi fr bsf szf n0) Q
                          (sb_bmapstart sb)) b
                = fs_bit (Q (sb_bmapstart sb)) b).
      { intros b Hb Hbne Hbfi.
        apply (ws_run_bit _ Q b Hv Hp Hchain);
          [unfold SB_BNO in *; lia |].
        unfold ws_append, ws_alloc_at. cbn [ws_freshs].
        intros Hc. apply elem_of_union in Hc as [Hc | Hc].
        - destruct (decide (n0 = 12%nat)) as [Hn12 | Hne];
            cbn [ws_fresh] in Hc.
          + apply elem_of_union in Hc as [Hc | Hc];
              apply elem_of_singleton in Hc.
            * exact (Hbfi Hn12 Hc).
            * exact (Hbne Hc).
          + apply elem_of_singleton in Hc. exact (Hbne Hc).
        - cbn [ws_freshs ws_fresh] in Hc.
          apply elem_of_union in Hc as [Hc | Hc];
            rewrite elem_of_empty in Hc; exact Hc. }
      cbn [ws_appends]. rewrite ws_run_app.
      apply (IH (S n0) _ Hv' Hp' Hi Hty' Hnblk').
      + intros j Hj. destruct (Hblk j ltac:(lia)) as (H1 & H2 & H3 & H4).
        split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
        rewrite (Hlater (fr j) H3); [exact H4 | | ].
        * intros Hc.
          assert (Hje : j = n0) by (apply Hinj; [lia | lia | exact Hc]).
          lia.
        * intros Hn12 Hc.
          destruct (Hcross ltac:(lia)) as (_ & _ & Hfine).
          exact (Hfine j ltac:(lia) (eq_sym Hc)).
      + intros j j' Hj Hj'. apply Hinj; lia.
      + intros Hc12. destruct (Hcross ltac:(lia)) as (Hfri & Hbii & Hfine).
        split; [exact Hfri |]. split.
        * rewrite (Hlater fi Hfri); [exact Hbii | | ].
          -- exact (Hfine n0 ltac:(lia)).
          -- intros Hn12. lia.
        * intros j Hj. apply Hfine. lia.
  Qed.

End OpFilewrite.
