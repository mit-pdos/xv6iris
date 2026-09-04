(* ProofSysUnlinkAUParts.v -- the AU walk's SHARED layer: the AU return
   continuation, the four per-slot / per-record projections the blocks
   want, and the name tie.

   THE AU WALK IS sys_unlink's WALK AGAIN, at [SpecSysUnlinkAU]'s contract
   instead of [SpecSysUnlink]'s.  The blocks are copy-adapts of
   [ProofSysUnlink]'s ([ProofSysMknodAU] is the family's template: the AU
   proof of a syscall is its landed proof with the walk premise swapped for
   the era one and the fire points fused in).  Three things are REUSED
   VERBATIM rather than copied, and each has a reason:

     - [ProofSysUnlinkParts.v] -- the pure/frame/register layer.  Nothing
       in it mentions the contract at all.
     - [ProofSysUnlinkTails.v] -- EVERY exit block.  The tails conclude
       ABSTRACTLY ([wp_next b pj (fun _ => ∀ mf, ⌜callee_saved⌝ -∗
       ⌜mf a0 = -1⌝ -∗ ...)]), so the caller supplies the continuation and
       the AU caller supplies one that pays [unlink_arms] at [-1].  Not one
       line of the exit blocks moves.
     - [ProofSysUnlink.v] itself, for its TOP-LEVEL pure lemmas (the two
       name literals, the isdirempty index arithmetic, the zeroing's cost
       figures).  A whole-function proof file is not a dependency ANOTHER
       function's proof may take -- this is the SAME function's second
       contract, which is the one case the rule does not cover, and the
       alternative is 330 duplicated lines that must then be kept in step.

   What this file adds is what the blocks cannot share through those three:

     - [su_au_closer], the AU return continuation.  It is
       [SpecSysUnlink.sys_unlink_closer] with [ARMS] on the returned a0 in
       place of the pure ⌜sys_unlink_ret⌝ -- i.e. exactly the block
       [SpecSysUnlinkAU.wp_sys_unlink_au_frame] inlines, named once for the
       same reason the landed closer is named once (optimization.md: it was
       879 printed characters at EVERY step of the walk).  TRANSPARENT, so
       the tails' [iApply ("Hcont" $! ...)] unifies through it.
     - the module-internal projections of [ProofSysUnlink]'s walk, hoisted:
       they live inside that file's functor and are therefore invisible,
       but none of them mentions a functor parameter.
     - [su_last_of_npar], the name tie ([ProofCreateAU.cr_last_of_npar]'s
       shape): nameiparent's landed name clause is [nameiparent_of pl es e]
       and the AU's arms speak of [last (path_elems pl)], which is one
       [last_snoc]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import CalleeSaved KernelDataInv.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import WpUart.
Require Import ByteBuf.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioDefs.
(* the payload's own vocabulary, IMPORTED BEFORE [FsBlocks] on purpose --
   ProofSysUnlink's banner: the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins. *)
Require Import FsStateInode.
Require Import FsStateEra.
Require Import LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import SleepLock.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecReadi.        (* [rd_delivered]                         *)
Require Import PathElems.        (* [path_elems], [nameiparent_of]         *)
Require Import SpecSysUnlink.
Require Import ProofSysUnlink.   (* the top-level pure layer; see header   *)
Require Import FsAbsMknodFire.
Require Import SpecSysUnlinkAU.
Require Import FsAbsUnlinkFire.
Require Import FsAbs.
From Kernel Require KernelSyms KernelData.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Local Open Scope Z_scope.
Require Import TsoCtx.

Set Printing Depth 40.

(* ===================================================================== *)
(*  THE AU RETURN CONTINUATION                                            *)
(* ===================================================================== *)

(* [SpecSysUnlink.sys_unlink_closer]'s rows VERBATIM, with [ARMS] on the
   returned a0 in place of ⌜sys_unlink_ret⌝ -- the block
   [SpecSysUnlinkAU.wp_sys_unlink_au_frame] inlines, named.  THE IMAGE DOES
   NOT MOVE (the statement's banner): binders [(mf, P')], no [M'].

   TRANSPARENT on purpose, for the landed closer's own reason: the exit
   sites apply it with [iApply ("Hcont" $! ...)], which unifies through a
   transparent constant and fails through an opaque one. *)
Definition su_au_closer
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gf : gname) (pj : mword 64) (pid : mword 32) (U : ustate)
    (m : regfile) (ret_tgt : mword 64) (K : nat) (eb b : bool)
    (lks : gset string) (dqb dqs dqbs : dfrac)
    (ARMS : mword 64 -> iProp Σ)
 : iProp Σ :=
  (∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      iref_slots SpecSysUnlink.sys_unlink_slots -∗
      proc_priv gf pj pid (us_upt U P') -∗
      ARMS (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang))%I.

(* ===================================================================== *)
(*  THE NAME TIE                                                          *)
(* ===================================================================== *)

(* nameiparent's landed name clause is [nameiparent_of pl es e], i.e.
   [path_elems pl = es ++ [e]]; the AU's arms speak of
   [last (path_elems pl)].  One [last_snoc].  Hoisted to the top level
   rather than spelled at the sites that want it: it is a pure list fact
   and the proofmode context there is the syscall-altitude one. *)
Lemma su_last_of_npar (pl : list (bv 8)) (nf : nat -> bv 8) :
  (exists es e, nameiparent_of pl es e /\ bname 14 nf = e) ->
  list_basics.last (path_elems pl) = Some (bname 14 nf).
Proof.
  intros (es & e & Hnp & Hb). rewrite /nameiparent_of in Hnp.
  rewrite Hnp Hb. apply last_snoc.
Qed.

(* ===================================================================== *)
(*  THE FIRE SITES' PURE SIDE CONDITIONS                                  *)
(*                                                                        *)
(*  Eight one-liners, hoisted rather than spelled at the four fire sites   *)
(*  (durable-notes' rule about pure obligations inside a large proofmode   *)
(*  goal).  Each is an [abs_of] reading of a fact the landed walk already  *)
(*  has in hand at the retag it replaces.                                  *)
(* ===================================================================== *)

(* a non-directory target: its row is neither an [ADir] -- so [unl_pre]'s
   dots-only clause is VACUOUS on the FILE arm -- nor counted by [unl_dec],
   so the parent's own count does not move.  This is the whole of what
   makes ONE fire lemma serve both W5 arms. *)
Lemma su_au_era_not_dir (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z -> fn_is_dir (era_node dn bm data) = false.
Proof.
  intro H. rewrite /fn_is_dir /fn_type era_node_rec.
  by apply bool_decide_eq_false_2.
Qed.

Lemma su_au_nondir_node (n : fs_node) :
  fn_is_dir n = false ->
  forall es, an_node (abs_of n) = ADir es -> dots_only es.
Proof.
  intros Hd es Heq. exfalso. revert Heq.
  rewrite /abs_of /abs_node /= Hd. case_decide; discriminate.
Qed.

Lemma su_au_nondir_dec (n : fs_node) :
  fn_is_dir n = false -> unl_dec (an_node (abs_of n)) = 0%nat.
Proof.
  intros Hd. rewrite /abs_of /abs_node /= Hd. case_decide; reflexivity.
Qed.

Lemma su_au_dir_dec (n : fs_node) :
  fn_is_dir n = true -> unl_dec (an_node (abs_of n)) = 1%nat.
Proof. intros Hd. by rewrite /abs_of /abs_node /= Hd. Qed.

(* the walked liveness facts, as [fn_nlink] bounds *)
Lemma su_au_nl1 (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  bv_unsigned (di_nlink dn) <> 0 -> (1 <= fn_nlink (era_node dn bm data))%nat.
Proof.
  intro H. rewrite /fn_nlink era_node_rec.
  pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))). lia.
Qed.

Lemma su_au_nlink_down (dn dn' : dinode) (bm bm' : blkmap)
    (data data' : nat -> list (bv 8)) :
  bv_unsigned (di_nlink dn) <> 0 ->
  bv_unsigned (di_nlink dn') = bv_unsigned (di_nlink dn) - 1 ->
  (fn_nlink (era_node dn' bm' data')
   = fn_nlink (era_node dn bm data) - 1)%nat.
Proof.
  intros Hnz Hd. rewrite /fn_nlink !era_node_rec Hd.
  pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))). lia.
Qed.

(* the parent's row at the zeroed record, [uf_parent_row] with the era
   node's type reading supplied *)
Lemma su_au_parent_row_era (dn dn' : dinode) (bm bm' : blkmap)
    (data data' : nat -> list (bv 8)) (nm : fname) (dec : nat) :
  bv_unsigned (di_type dn) = T_DIR_z ->
  di_type dn' = di_type dn ->
  (fn_nlink (era_node dn' bm' data')
   = fn_nlink (era_node dn bm data) - dec)%nat ->
  dir_entries (era_node dn' bm' data')
    = delete nm (dir_entries (era_node dn bm data)) ->
  abs_of (era_node dn' bm' data')
  = MkAnode (ADir (delete nm (dir_entries (era_node dn bm data))))
            (fn_nlink (era_node dn bm data) - dec)%nat.
Proof.
  intros Hty Hty' Hnl Hents.
  apply (uf_parent_row _ _ nm dec); [| exact Hnl | exact Hents].
  apply mkf_era_is_dir. by rewrite Hty'.
Qed.

(* the ret-0 arm's LOWER region bound: a live record's inum is nonzero *)
Lemma su_au_inum_pos (data : nat -> list (bv 8)) (k : nat) :
  dir_live data k -> 0 < bv_unsigned (dir_inum data k).
Proof.
  intro Hl.
  pose proof (proj1 (bv_unsigned_in_range _ (dir_inum data k))) as Hnn.
  destruct (decide (bv_unsigned (dir_inum data k) = 0)) as [Hz | Hnz];
    [| lia].
  exfalso. apply Hl. apply bv_eq. rewrite Hz. by vm_compute.
Qed.

(* the DIR arm's dots-only reading: [unl_pre]'s last conjunct at a target
   that IS a directory, out of the isdirempty loop's harvest. *)
Lemma su_au_dir_dots (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  blk_holes_zero bm data ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  bv_unsigned (di_type dn) = T_DIR_z ->
  dir_dots_only dn data ->
  forall es, an_node (abs_of (era_node dn bm data)) = ADir es -> dots_only es.
Proof.
  intros Hh Hb Hty Hdo es Heq.
  rewrite (abs_of_dir _ (mkf_era_is_dir dn bm data Hty)) in Heq.
  injection Heq as <-. exact (uf_dots_only dn bm data Hh Hb Hty Hdo).
Qed.

Section ProofSysUnlinkAUParts.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  (* ================================================================== *)
  (*  THE FOUR SPLITS AND THE TWO PER-SLOT PROJECTIONS W2 NEEDS          *)
  (* ================================================================== *)

  (* the two per-slot projections out of the boot families, at the copies
     THIS contract names ([ic_escrows] is IcacheEscrow's, [ic_sleeplocks]
     SpecDirlink's). *)
  Lemma su_esc_acc `{XI : CurCtx} `{GEN : GenId}
      (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗ ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H".
    iApply (ic_escrows_lookup fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k Hk with "H").
  Qed.

  Lemma su_slk_acc `{XI : CurCtx} `{GEN : GenId} (k : nat) :
    (k < NINODE)%nat ->
    (ic_sleeplocks fsc_ic -∗
     ∃ gil gisl : gname,
       is_sleeplock_genl gil gisl (i_lock (ientry k)) "inode"%string
                        (ic_slp fsc_ic k) (slh_tok (icfg_isl k))
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma su_bs3 `{XI : CurCtx} :
    (bslots 3 : iProp Σ) ⊣⊢ bslot ∗ bslots 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* THE GENERATION-NAMED SHED.  [IcacheRef.inode_ref_shed] loses the
     generation, and nameiparent's [inode_held_ty] payout is exactly the
     claim that the share handed to ilock names the SAME generation as the
     type one-shot beside it -- which is what turns the parent's promised
     T_DIR into [di_type dnd = T_DIR] at the record ilock returns.  Pure
     resource algebra; its home is [IcacheRef.v] and it is here for that
     file's rebuild-cone reason. *)
  Lemma su_carve_gen `{XI : CurCtx} (k : nat) (q s : Qp) (dv inum : mword 32) (gy : gname) :
    inode_ref_gen k (q + s)%Qp dv inum gy ⊣⊢
    inode_ref_short_gen k (q + s)%Qp q dv inum gy ∗ inode_shr_gen k s dv inum gy.
  Proof. apply inode_ref_carve_gen. Qed.

  Lemma su_shed_gen `{XI : CurCtx} (k : nat) (q : Qp) (dv inum : mword 32) (gy : gname) :
    inode_ref_gen k q dv inum gy ⊣⊢
    inode_ref_short_gen k (q/2 + q/2)%Qp (q/2)%Qp dv inum gy ∗
    inode_shr_gen k (q/2)%Qp dv inum gy.
  Proof.
    pose proof (su_carve_gen k (q/2)%Qp (q/2)%Qp dv inum gy) as Hc.
    by rewrite {1}(Qp.div_2 q) in Hc.
  Qed.

  Lemma su_dot_window `{XI : CurCtx} `{GEN : GenId} (a : mword 64) :
    a = mword_of_int su_dot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ su_dot_f j).
  Proof.
    intros ->. iApply (kernel_data_bytes su_dot_addr 14 su_dot_f _ eq_refl
                         ltac:(unfold text_end, su_dot_addr; lia)
                         ltac:(vm_compute; discriminate)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
  Qed.

  Lemma su_dotdot_window `{XI : CurCtx} `{GEN : GenId} (a : mword 64) :
    a = mword_of_int su_dotdot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ su_dotdot_f j).
  Proof.
    intros ->. iApply (kernel_data_bytes su_dotdot_addr 14 su_dotdot_f _ eq_refl
                         ltac:(unfold text_end, su_dotdot_addr; lia)
                         ltac:(vm_compute; discriminate)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
  Qed.

  (* ================================================================== *)
  (*  THE isdirempty [de] RECORD'S BYTE VIEWS -- two bytes as the [lhu]'s *)
  (*  halfword, fourteen riding.  [ProofDirlookupParts]' shapes, restated *)
  (*  for that file's whole-function reason.                             *)
  (* ================================================================== *)

  Lemma su_del_split `{XI : CurCtx} (a : Arch.pa) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ[KT1] f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ[KT1] f j)
       ∗ ([∗ list] j ∈ seq 0 14, pa_add (pa_add a 2) j ↦ₘ[KT1] f (2 + j)%nat).
  Proof. exact (bb_split a 2 14 f). Qed.

  Lemma su_half_acc `{XI : CurCtx} (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ[KT1] file_byte data (16 * i + j)%nat)
    ⊣⊢ a ↦₂[KT1] dir_inum data i.
  Proof.
    intro Hal.
    rewrite (bb_ext (KTR := KT1) a 2 (fun j => file_byte data (16 * i + j)%nat)
                        (fun j => nth_byte (dir_inum data i) j)
               (fun j Hj => eq_sym (su_half_bytes_eq data i j Hj))).
    iSplit.
    - iIntros "H".
      iApply (ctx_word2_pointsto_intro (KTR := KT1) cur_ctx a (DfracOwn 1) (dir_inum data i) Hal).
      iExact "H".
    - iIntros "H". iApply (ctx_word2_pointsto_bytes (KTR := KT1) with "H").
  Qed.

  Lemma su_name_acc `{XI : CurCtx} (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] file_byte data (16 * i + (2 + j))%nat)
    ⊣⊢ ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] dir_name data i j).
  Proof.
    apply (bb_ext (KTR := KT1) a 14 (fun j => file_byte data (16 * i + (2 + j))%nat)
                       (dir_name data i)
             (fun j _ => su_name_shift data i j)).
  Qed.

  (* the whole record, split for the [lhu] and put back *)
  Lemma su_de_view `{XI : CurCtx} (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] jj ∈ seq 0 16, pa_add a jj ↦ₘ[KT1] file_byte data (16 * i + jj)%nat)
    ⊣⊢ a ↦₂[KT1] dir_inum data i
       ∗ ([∗ list] jj ∈ seq 0 14, pa_add (pa_add a 2) jj ↦ₘ[KT1] dir_name data i jj).
  Proof.
    intro Hal.
    rewrite -(su_half_acc data i a Hal).
    rewrite -(su_name_acc data i (pa_add a 2)).
    exact (su_del_split a (fun jj => file_byte data (16 * i + jj)%nat)).
  Qed.

  (* readi's sixteen delivered bytes ARE the record's bytes at [tot = 16] *)
  Lemma su_rdd_view `{XI : CurCtx} (data : nat -> list (bv 8)) (olds : nat -> bv 8)
      (i : nat) (a : Arch.pa) :
    ([∗ list] jj ∈ seq 0 16,
       pa_add a jj ↦ₘ[KT1] rd_delivered data olds (16 * i)%nat 16 jj)
    ⊣⊢ ([∗ list] jj ∈ seq 0 16,
          pa_add a jj ↦ₘ[KT1] file_byte data (16 * i + jj)%nat).
  Proof.
    apply (bb_ext (KTR := KT1) a 16
             (fun jj => rd_delivered data olds (16 * i)%nat 16 jj)
             (fun jj => file_byte data (16 * i + jj)%nat)
             (fun jj Hj => su_rdd_eq data olds (16 * i)%nat jj Hj)).
  Qed.

End ProofSysUnlinkAUParts.
