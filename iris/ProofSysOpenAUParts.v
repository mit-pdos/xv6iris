(* ProofSysOpenAUParts.v -- the AU walk's parts layer: the exit
   continuations at the ARMED post, the payload peeled AT AN EXPLICIT
   [data], the field accessors the landed walk keeps [Local], and the two
   arm builders.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  Everything here is either copied verbatim out of
   [ProofSysOpen]'s section (the four [Local] accessors, which are
   inaccessible from another file and are needed by every block below) or
   is the AU walk's own.

   ==== WHY THE PAYLOAD IS THREADED PEELED ([so_flat]) ==================

   THE OBSERVED-ROW TIE IS A DATA TIE.  [SpecSysOpenAU]'s FILE arm shares
   ONE [bs0] between the terminal observation and the O_TRUNC receipt, and
   both read it off the locked node's [top_frag].  The observation has to
   fire EARLY -- every post-walk failure (the T_DIR refusal, the bad major,
   the two table-full arms) must deliver a fired receipt, and they all sit
   above the store block -- while the trunc fires LATE, at the retag.  A
   peel-and-reseal in between would lose the tie: [IcacheEscrow.ic_loaded]
   binds its [data] EXISTENTIALLY, so a second peel's witness is not the
   first's and the two [fn_file_bytes] are two terms.

   So the blocks below the fire carry [so_flat] -- [ic_loaded_flat_body]
   with [data] EXPOSED -- and close it back to [ic_loaded] exactly where a
   failure tail's [iunlockput] or ARM S's [iunlock] wants the sealed form.
   [so_flat_open] / [so_flat_close] are the two directions, and they are
   [IcacheEscrow]'s own pair with the existential moved out.

   BINDERS: [ProofSysOpen]'s [ProofSysOpenBody] list verbatim. *)

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
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioDefs.
(* the payload's own vocabulary, IMPORTED BEFORE [FsBlocks] on purpose --
   ProofSysOpen's rule, and its reason (the last import wins). *)
Require Import FsStateEra.
Require Import LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRefDefs.
Require Import IcacheEscrow.
Require Import DirView.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecItrunc.
Require Import ConsoleInv.
Require Import PathElems.
Require Import FsTree.
Require Import FsBytesGamma.
Require Import SpecSysOpenAU.
Require Import FsAbsOpenFire.
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import FsAbsDefs.            (* LAST (FsAbs's own rule) *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Require Import TsoCtx.

Local Open Scope Z_scope.

Set Printing Depth 40.

Section ProofSysOpenAUParts.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* ================================================================== *)
  (*  1.  THE PAYLOAD, PEELED AT AN EXPLICIT [data]                      *)
  (* ================================================================== *)

  Definition so_flat (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) : iProp Σ :=
    (⌜inode_ok fsc_cov fsc_logst dn bm data⌝ ∗
     ⌜inode_rec_local dn⌝ ∗
     ⌜dir_ok icfg_nib dn data⌝ ∗
     ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
     ⌜dir_orphan_clean dn data⌝ ∗
     ⌜dir_uniq dn data⌝ ∗
     dlinks fsc_fs (bv_unsigned inum) dn bm data ∗
     dinode_at fsc_ireg inum dn ∗
     inode_meta (ientry k) dn ∗
     inode_addrs (ientry k) (bm_cells bm) ∗
     ind_res fsc_fs bm ∗
     inode_blocks fsc_fs bm data ∗
     top_frag (fs_gamma_L fsc_fs) (bv_unsigned inum) (era_node dn bm data))%I.

  Lemma so_flat_open (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap) :
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn bm -∗
    ∃ data : nat -> list (bv 8), so_flat k inum dn bm data.
  Proof.
    iIntros "H". iDestruct (ic_loaded_open with "H") as "H".
    rewrite /ic_loaded_flat_body. iDestruct "H" as (data) "H".
    iExists data. iExact "H".
  Qed.

  Lemma so_flat_close (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    so_flat k inum dn bm data -∗
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn bm.
  Proof.
    iIntros "H". iApply ic_loaded_flat. rewrite /ic_loaded_flat_body.
    iExists data. iExact "H".
  Qed.

  (* the six pure facts, read without spending the payload -- the type
     enumeration ([inode_rec_local]) is what tells the arm builder that a
     locked inode is a DIRECTORY, a FILE or a DEVICE and nothing else. *)
  Lemma so_flat_pure (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    so_flat k inum dn bm data -∗
    ⌜inode_ok fsc_cov fsc_logst dn bm data /\ inode_rec_local dn⌝.
  Proof.
    rewrite /so_flat.
    iIntros "(%H1 & %H2 & _)". iPureIntro. by split.
  Qed.

  (* the era fragment, out and back: the ONE thing the terminal observation
     borrows.  [aopen_commit_at] only reads, so the payload is untouched. *)
  Lemma so_flat_top (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    so_flat k inum dn bm data -∗
    top_frag (fs_gamma_L fsc_fs) (bv_unsigned inum) (era_node dn bm data)
    ∗ (top_frag (fs_gamma_L fsc_fs) (bv_unsigned inum) (era_node dn bm data)
       -∗ so_flat k inum dn bm data).
  Proof.
    rewrite /so_flat.
    iIntros "(%H1 & %H2 & %H3 & %H4 & %H5 & %H6 & Ha & Hb & Hc & Hd & He &
              Hf & Ht)".
    iFrame "Ht". iIntros "Ht".
    iSplitR; [iPureIntro; assumption |]. iSplitR; [iPureIntro; assumption |].
    iSplitR; [iPureIntro; assumption |]. iSplitR; [iPureIntro; assumption |].
    iSplitR; [iPureIntro; assumption |]. iSplitR; [iPureIntro; assumption |].
    iFrame "Ha Hb Hc Hd He Hf Ht".
  Qed.

  (* ================================================================== *)
  (*  2.  THE FOUR ACCESSORS [ProofSysOpen] KEEPS [Local]                *)
  (* ================================================================== *)

  Lemma so_meta_acc
      (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap) :
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn bm -∗
    inode_meta (ientry k) dn ∗
    (inode_meta (ientry k) dn -∗ ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn bm).
  Proof.
    iIntros "H".
    iDestruct (ic_loaded_open with "H") as (data)
      "(%Hok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hl & Hd & Hm & Ha & Hr &
        Hb & Ht)".
    iFrame "Hm". iIntros "Hm".
    iApply (ic_mk_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn bm data Hok Hrl Hdok Hddix
              Hdoc Hduq with "Hl Hd Hm Ha Hr Hb Ht").
  Qed.

  (* ...and the same accessor at the PEELED payload, which is what the AU
     walk actually holds between the fire and the stores. *)
  Lemma so_flat_meta
      (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    so_flat k inum dn bm data -∗
    inode_meta (ientry k) dn ∗
    (inode_meta (ientry k) dn -∗ so_flat k inum dn bm data).
  Proof.
    rewrite /so_flat.
    iIntros "(%H1 & %H2 & %H3 & %H4 & %H5 & %H6 & Ha & Hb & Hc & Hd & He &
              Hf & Ht)".
    iFrame "Hc". iIntros "Hc".
    iSplitR; [iPureIntro; assumption |]. iSplitR; [iPureIntro; assumption |].
    iSplitR; [iPureIntro; assumption |]. iSplitR; [iPureIntro; assumption |].
    iSplitR; [iPureIntro; assumption |]. iSplitR; [iPureIntro; assumption |].
    iFrame "Ha Hb Hc Hd He Hf Ht".
  Qed.

  Lemma so_type_acc (ip : mword 64) (dn : dinode) :
    inode_meta ip dn -∗
    i_type ip ↦₂ di_type dn ∗ (i_type ip ↦₂ di_type dn -∗ inode_meta ip dn).
  Proof.
    iIntros "(Hty & Hmaj & Hmin & Hnl & Hsz)". iFrame "Hty".
    iIntros "Hty". iFrame "Hty Hmaj Hmin Hnl Hsz".
  Qed.

  Lemma so_maj_acc (ip : mword 64) (dn : dinode) :
    inode_meta ip dn -∗
    i_major ip ↦₂ di_major dn ∗ (i_major ip ↦₂ di_major dn -∗ inode_meta ip dn).
  Proof.
    iIntros "(Hty & Hmaj & Hmin & Hnl & Hsz)". iFrame "Hmaj".
    iIntros "Hmaj". iFrame "Hty Hmaj Hmin Hnl Hsz".
  Qed.

  Lemma so_esc_acc (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗ ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H".
    iApply (ic_escrows_lookup fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k Hk with "H").
  Qed.

  Lemma so_slk_acc (k : nat) :
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

  Lemma so_bs3 :
    (bslots 3 : iProp Σ) ⊣⊢ bslot ∗ bslots 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  Lemma so_upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
  Proof. destruct V; reflexivity. Qed.

  Lemma so_ip_split (a w : mword 64) :
    a ↦₈ w -∗ a ↦₈{DfracOwn (1/2)} w ∗ a ↦₈{DfracOwn (1/2)} w.
  Proof.
    iIntros "H".
    iDestruct (bi.equiv_entails_1_1 _ _
                 (ctx_word_pointsto_frac_split _ a (1/2) (1/2) w) with "[H]")
      as "[$ $]".
    { iEval (rewrite Qp.div_2). iExact "H". }
  Qed.

  Lemma so_iref_take (n : nat) :
    (1 <= n)%nat -> iref_slots n -∗ iref_slot ∗ iref_slots (n - 1).
  Proof.
    intros Hn. rewrite /iref_slot.
    replace n with (1 + (n - 1))%nat at 1 by lia.
    iIntros "H". iApply (iref_slots_split with "H").
  Qed.

  (* ================================================================== *)
  (*  3.  THE TWO EXIT CONTINUATIONS, AT THE ARMED POST                  *)
  (* ================================================================== *)

  (* [ProofSysOpen.so_cont] with [SpecSysOpen.sys_open_post] replaced by
     [SpecSysOpenAU.open_arms_plain] -- and that is the ONLY difference.
     The abstract state is read at the LIVE Γ, as the contract states it. *)
  Definition so_cont_au `{GEN : GenId}
      (gf : gname)
      (nsj : nat) (dqb dqs : dfrac)
      (pj : mword 64) (pidv : mword 32) (vom : mword 64) (U : ustate)
      (sts : list fdstate)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string)
      : CpuId -> iProp Σ :=
    fun (CIDx : CpuId) =>
      (∀ (mf : regfile) (ns' : nat),
         ⌜callee_saved m mf⌝ -∗
         ⌜ns' = S nsj⌝ -∗
         sie_cap_gpr KT1 mf K b pj -∗
         cpu_own 0 eb pj b lks -∗
         trap_csrs_ext KT1 eb -∗
         cpu_claim_ext eb pj -∗
         pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
         sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
         bslots 3 -∗
         iref_slots ns' -∗
         open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
           P Pmiss Φo Φt sts U (mf !!! Regidx Ra0 : mword 64) -∗
         WP (Loop : expr riscv_lang))%I.

  Definition so_cont0_au `{GEN : GenId}
      (gf : gname)
      (ns : nat) (dqb dqs dqbs dqn : dfrac)
      (pj : mword 64) (pidv : mword 32) (vom : mword 64) (U : ustate)
      (sts : list fdstate)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string)
      : CpuId -> iProp Σ :=
    fun (CIDx : CpuId) =>
      (∀ (mf : regfile) (ns' : nat),
         ⌜callee_saved m mf⌝ -∗
         ⌜ns' = ns⌝ -∗
         sie_cap_gpr KT1 mf K b pj -∗
         cpu_own 0 eb pj b lks -∗
         trap_csrs_ext KT1 eb -∗
         cpu_claim_ext eb pj -∗
         pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
         sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
         sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
         sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
         bslots 3 -∗
         iref_slots ns' -∗
         open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
           P Pmiss Φo Φt sts U (mf !!! Regidx Ra0 : mword 64) -∗
         WP (Loop : expr riscv_lang))%I.

  (* ================================================================== *)
  (*  4.  THE ARM BUILDERS                                               *)
  (* ================================================================== *)

  (* THE RESIDUE the blocks below the fire carry: the cursor at the end of
     the walk, the FIRED terminal observation (at the whole row the locked
     node reads as), and the trunc commit still in hand. *)
  Definition so_obs (Φo : aview -> Z -> anode -> iProp Σ) (i : Z)
      (n : fs_node) : iProp Σ :=
    (∃ av : aview, ⌜av !! i = Some (abs_of n)⌝ ∗ Φo av i (abs_of n))%I.

  (* the post-walk FAILURE arm (ARMs C-FAIL / D-FAIL / E-FAIL / F-FAIL):
     the observation HAS fired and its receipt is delivered, the trunc
     commit comes back ([SpecSysOpenAU]'s third fold arm). *)
  Lemma so_arm_fail `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate)
      (r : mword 64) (pl : list (bv 8)) (i : Z) (n : fs_node) :
    r = (mword_of_int (-1) : mword 64) ->
    proc_priv gf pj pidv U -∗
    fd_frags (pv_fdg (us_V U)) sts -∗
    fd_slot -∗
    P (length (path_elems pl)) i -∗
    so_obs Φo i n -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) appE Φt -∗
    open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
      P Pmiss Φo Φt sts U r.
  Proof.
    intros Hr. iIntros "Hpriv Hfrag Hfds HP Hobs Htc".
    rewrite /open_arms_plain. iFrame "Hfds". iLeft.
    iSplitR; [by iPureIntro |]. iFrame "Hpriv Hfrag".
    rewrite /open_post_fail_plain. iRight. iExists pl. iRight.
    iExists i. iFrame "HP Htc".
    rewrite /so_obs. iDestruct "Hobs" as (av) "[%Hav HΦ]".
    iExists av, (abs_of n). iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* ...and the WALK-DEAD arm (ARM B-FAIL): nothing was observed, the era
     refund comes back with both commits. *)
  Lemma so_arm_dead `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate) (r : mword 64) (pl : list (bv 8)) :
    r = (mword_of_int (-1) : mword 64) ->
    proc_priv gf pj pidv U -∗
    fd_frags (pv_fdg (us_V U)) sts -∗
    fd_slot -∗
    open_walk_dead_era fsc_fs P Pmiss pl -∗
    aopen_commit_at (fs_gamma_L fsc_fs) appE Φo -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) appE Φt -∗
    open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
      P Pmiss Φo Φt sts U r.
  Proof.
    intros Hr. iIntros "Hpriv Hfrag Hfds Hdead Hoc Htc".
    rewrite /open_arms_plain. iFrame "Hfds". iLeft.
    iSplitR; [by iPureIntro |]. iFrame "Hpriv Hfrag".
    rewrite /open_post_fail_plain. iRight. iExists pl. iLeft.
    iFrame "Hdead Hoc Htc".
  Qed.

  (* ...and the ARGSTR arm (ARM 0): nothing fs-visible happened at all. *)
  Lemma so_arm_unspent `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate) (r : mword 64) :
    r = (mword_of_int (-1) : mword 64) ->
    proc_priv gf pj pidv U -∗
    fd_frags (pv_fdg (us_V U)) sts -∗
    fd_slot -∗
    open_au_pre_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) P Pmiss Φo Φt -∗
    open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
      P Pmiss Φo Φt sts U r.
  Proof.
    intros Hr. iIntros "Hpriv Hfrag Hfds Hpre".
    rewrite /open_arms_plain. iFrame "Hfds". iLeft.
    iSplitR; [by iPureIntro |]. iFrame "Hpriv Hfrag".
    rewrite /open_post_fail_plain. by iLeft.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4a.  THE THREE SUCCESS ARMS, as wands from the descriptor receipt   *)
  (*                                                                     *)
  (*  Which arm fires is decided by [ip->type], which the STORE block     *)
  (*  reads and the publication block does not -- so the arm travels down *)
  (*  as a wand and the publication only earns its antecedent.            *)
  (* ------------------------------------------------------------------ *)

  Lemma so_arm_dev `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate)
      (pl : list (bv 8)) (i ma mi : Z) (nl : nat) :
    0 <= ma <= NDEV_max ->
    P (length (path_elems pl)) i -∗
    (∃ av : aview, ⌜av !! i = Some (MkAnode (ADev ma mi) nl)⌝
                   ∗ Φo av i (MkAnode (ADev ma mi) nl)) -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) appE Φt -∗
    (∀ r : mword 64,
       open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
         (FdDevice ma) sts r -∗
       open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv vom P Φo Φt sts U r).
  Proof.
    intros Hma. iIntros "HP Hobs Htc".
    iDestruct "Hobs" as (av) "[%Hav HΦ]".
    iIntros (r) "Hfd". rewrite /open_post_ok_plain.
    iExists pl, av, i. iFrame "HP". iLeft.
    iExists ma, mi, nl. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iFrame "HΦ Htc Hfd".
  Qed.

  Lemma so_arm_file `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate)
      (pl : list (bv 8)) (i : Z) (bs0 : list (bv 8)) (nl : nat) (γo : gname) :
    om_trunc vom = false ->
    P (length (path_elems pl)) i -∗
    (∃ av : aview, ⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝
                   ∗ Φo av i (MkAnode (AFile bs0) nl)) -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) appE Φt -∗
    (∀ r : mword 64,
       open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
         (FdInode i γo) sts r -∗
       open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv vom P Φo Φt sts U r).
  Proof.
    intros Hnt. iIntros "HP Hobs Htc".
    iDestruct "Hobs" as (av) "[%Hav HΦ]".
    iIntros (r) "Hfd". rewrite /open_post_ok_plain.
    iExists pl, av, i. iFrame "HP". iRight. iLeft.
    iExists bs0, nl. iSplitR; [by iPureIntro |]. iFrame "HΦ".
    rewrite Hnt. iFrame "Htc". iExists γo. iFrame "Hfd".
  Qed.

  (* ...and the ONE arm that spends the trunc commit: the O_TRUNC file. *)
  Lemma so_arm_file_tr `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate)
      (pl : list (bv 8)) (i : Z) (bs0 : list (bv 8)) (nl : nat) (γo : gname) :
    om_trunc vom = true ->
    P (length (path_elems pl)) i -∗
    (∃ av : aview, ⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝
                   ∗ Φo av i (MkAnode (AFile bs0) nl)) -∗
    (∃ av' : aview, ⌜av' !! i = Some (MkAnode (AFile bs0) nl)⌝
                    ∗ Φt av' i bs0) -∗
    (∀ r : mword 64,
       open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
         (FdInode i γo) sts r -∗
       open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv vom P Φo Φt sts U r).
  Proof.
    intros Ht. iIntros "HP Hobs Htr".
    iDestruct "Hobs" as (av) "[%Hav HΦ]".
    iIntros (r) "Hfd". rewrite /open_post_ok_plain.
    iExists pl, av, i. iFrame "HP". iRight. iLeft.
    iExists bs0, nl. iSplitR; [by iPureIntro |]. iFrame "HΦ".
    rewrite Ht. iFrame "Htr". iExists γo. iFrame "Hfd".
  Qed.

  (* the DIRECTORY arm, at O_RDONLY exactly -- and its own key is what pays
     the writable-fd-is-not-a-directory theorem here ([om_rdonly_modes]). *)
  Lemma so_arm_dir `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate)
      (pl : list (bv 8)) (i : Z) (ents : gmap fname Z) (nl : nat) (γo : gname) :
    om_arg vom = 0 ->
    P (length (path_elems pl)) i -∗
    (∃ av : aview, ⌜av !! i = Some (MkAnode (ADir ents) nl)⌝
                   ∗ Φo av i (MkAnode (ADir ents) nl)) -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) appE Φt -∗
    (∀ r : mword 64,
       open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
         (FdInode i γo) sts r -∗
       open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv vom P Φo Φt sts U r).
  Proof.
    intros H0. iIntros "HP Hobs Htc".
    iDestruct "Hobs" as (av) "[%Hav HΦ]".
    iIntros (r) "Hfd". rewrite /open_post_ok_plain.
    destruct (om_rdonly_modes vom H0) as [Hrd Hwr].
    rewrite Hrd Hwr.
    iExists pl, av, i. iFrame "HP". iRight. iRight.
    iExists ents, nl. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iFrame "HΦ Htc". iExists γo. iFrame "Hfd".
  Qed.

  (* ...and the ONE the two non-trunc exits use: the arm read straight off
     [di_type dn]'s enumeration, with the trunc commit handed back.  The
     FILE case's [om_trunc = false] is forced by the exit's own key (either
     the mask was empty or the type test failed). *)
  Lemma so_arm_notr `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate) (pl : list (bv 8)) (i : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) (t : fdtype)
      (γo : gname) :
    (om_trunc vom = false \/ bv_unsigned (di_type dn) <> FsImg.T_FILE_z) ->
    (bv_unsigned (di_type dn) = T_DIR_z -> om_arg vom = 0) ->
    (bv_unsigned (di_type dn) = FsImg.T_DEVICE_z ->
       0 <= bv_unsigned (di_major dn) <= NDEV_max
       /\ t = FdDevice (bv_unsigned (di_major dn))) ->
    (bv_unsigned (di_type dn) <> FsImg.T_DEVICE_z -> t = FdInode i γo) ->
    (bv_unsigned (di_type dn) = T_DIR_z
     \/ bv_unsigned (di_type dn) = FsImg.T_FILE_z
     \/ bv_unsigned (di_type dn) = FsImg.T_DEVICE_z) ->
    P (length (path_elems pl)) i -∗
    so_obs Φo i (era_node dn bm data) -∗
    atrunc_commit_at (fs_gamma_L fsc_fs) appE Φt -∗
    (∀ r : mword 64,
       open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom) t sts r -∗
       open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv vom P Φo Φt sts U r).
  Proof.
    intros Hnt Hdirk Hdev Hino Hen. rewrite /so_obs.
    destruct Hen as [Hd | [Hf | Hv]].
    - rewrite (opf_era_dir_row dn bm data Hd)
              (Hino ltac:(rewrite Hd; vm_compute; discriminate)).
      iIntros "HP Hobs Htc".
      iApply (so_arm_dir gf pj pidv vom P Φo Φt U sts pl i
                (dir_entries (era_node dn bm data))
                (fn_nlink (era_node dn bm data)) γo (Hdirk Hd)
                with "HP Hobs Htc").
    - rewrite (opf_era_file_row dn bm data Hf)
              (Hino ltac:(rewrite Hf; vm_compute; discriminate)).
      assert (Hntf : om_trunc vom = false)
        by (destruct Hnt as [H | H]; [exact H | exfalso; exact (H Hf)]).
      iIntros "HP Hobs Htc".
      iApply (so_arm_file gf pj pidv vom P Φo Φt U sts pl i
                (fn_file_bytes (era_node dn bm data))
                (fn_nlink (era_node dn bm data)) γo Hntf with "HP Hobs Htc").
    - destruct (Hdev Hv) as [Hmb Ht].
      rewrite (opf_era_dev_row dn bm data
                 ltac:(rewrite Hv; vm_compute; discriminate)
                 ltac:(rewrite Hv; vm_compute; discriminate)) Ht.
      iIntros "HP Hobs Htc".
      iApply (so_arm_dev gf pj pidv vom P Φo Φt U sts pl i
                (bv_unsigned (di_major dn)) (bv_unsigned (di_minor dn))
                (fn_nlink (era_node dn bm data)) Hmb with "HP Hobs Htc").
  Qed.

End ProofSysOpenAUParts.

Global Typeclasses Opaque so_flat so_obs.
