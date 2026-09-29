(* ===================================================================== *)
(* UkTreeWrite.v -- THE WRITE SIDE OF AN OWNED SUBTREE.                   *)
(*                                                                       *)
(* design/user-tree.md section 7.3, lane TL-3W deliverables 4 and 5.      *)
(* [UkTreeRead.v] is the read twin: there a FROZEN deed buys open and     *)
(* read; here a LIVE deed buys the one write-kind member whose U-tier     *)
(* leaf can carry a receipt home, and the deed COMES BACK MOVED.          *)
(*                                                                       *)
(*   [tree_write_sup]           the deposit, out of the deed:             *)
(*                              [UkWriteFile.udepwf_st_write_file] with   *)
(*                              the chain paid by [TreeMove] instead of   *)
(*                              by [AppInv.app_sup];                      *)
(*   [wp_uk_tree_write_moves]   THE CONSUMER TEST: a program that owns a  *)
(*                              subtree and holds a descriptor on a file  *)
(*                              of it writes its bytes, learns the bytes  *)
(*                              the kernel committed are its own, AND     *)
(*                              gets its DEED back at the moved tree.     *)
(*                                                                       *)
(* WHAT THE TEST IS NOT YET (TL-3W's STOP rule, AMENDED BY TL-3R): the    *)
(* brief asked for "own -> mkdir -> create -> write -> read-learns".      *)
(* TL-3W could not land the first two steps for three reasons             *)
(* ([TreeMove.v] section 4), and TL-3R has closed the last of them --     *)
(* create's parent leg is payable at every child kind and all three       *)
(* create-family BUNDLES are supplied from one live deed at a parent      *)
(* prefix of length zero ([TreeMove.tree_mknod_au] / [tree_mkdir_au] /    *)
(* [tree_open_create_au], design/user-tree.md section 7.9).  What the     *)
(* extended test still waits on is U-TIER ASSEMBLY ONLY -- the deposit    *)
(* at rows 17 / 20 / 15 out of [mknod_arms] and its twins, which is       *)
(* [UInitCons]'s mknod step's shape -- so the test below still runs the   *)
(* steps that are landed HERE: own -> write -> (the deed, moved), and     *)
(* section 3 states how it meets [UkTreeRead.wp_uk_tree_read_learns] at   *)
(* the other end.                                                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import ghost_map ghost_var invariants.
From transfinite.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import UexecSlot UexecRet.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.
Require Import UkReadRows.
Require Import UkWriteLeaf.
Require Import UkWriteFile.        (* the file arm of the write leaf *)
Require Import SpecFilewrite.
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import SysWriteDefs.       (* [wchunks] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import TreeView.
Require Import AppTree.
Require Import TreeMove.           (* the owner's move at the write fire *)
Require Import FsAbsDefs.
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkTreeWrite.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!treeG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE DEPOSIT, OUT OF THE DEED                                    *)
  (* =================================================================== *)

  (* [UkWriteFile.udepwf_st_write_file]'s one premise is the CHUNK CHAIN,
     and that is the whole of what an owner pays: [TreeMove]'s chain needs
     nothing from the heap the deposit lends, so the wand is a constant. *)
  Lemma tree_write_sup (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (rb : bool) (i : Z) (γo : gname) (n : Z)
      (c : tree_fixed) (r : tree_names) (g : gname) (root : Z) (t : ttree) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    sys_rw_count (m !!! Regidx a2_idx) = n ->
    app_inv fsc_fs -∗
    tree_wq c r g root i t -∗
    udepwf_st N m pc 16
      (write_file_fam (fun _ : nat => tree_wq c r g root i t) (ukn_pay N))
      (FdOpen rb true (FdInode i γo OffParked)).
  Proof using .
    intros Heq Hcnt. iIntros "#Hinv Hq".
    iApply (udepwf_st_write_file N m pc rb i γo
              (fun _ : nat => tree_wq c r g root i t) n Hcnt with "[Hq]").
    iIntros (M pm sz) "Hheap". iFrame "Hheap".
    iApply (tree_awrite_chain fsc_fs c r g root i t γo M
              (m !!! Regidx a1_idx) n (wchunks n) 0%nat Heq with "Hinv Hq").
  Qed.

  (* =================================================================== *)
  (*  2.  THE CONSUMER TEST: THE BYTES LAND AND THE DEED MOVES            *)
  (* =================================================================== *)

  (* [UkWriteFile.wp_uk_write_file_lands] with the application's SUPPLY
     replaced by the OWNER'S DEED.  The two arms are the kernel's own and
     unchanged; what is new is the THIRD thing the caller is handed -- its
     deed, at a tree that differs from the one it started with only at the
     file it wrote (and the taint arm, for a move somebody else did not
     pay).  That is design section 4 item 1's "write moves [t_P] by the
     tree op", at the granularity the kernel actually moves it: one splice
     per chunk, at offsets and bytes the KERNEL picks. *)
  Lemma wp_uk_tree_write_moves (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fd : nat) (rb : bool) (i : Z)
      (γo : gname) (dq : dfrac) (nb : nat) (f : nat -> bv 8)
      (c : tree_fixed) (r : tree_names) (g : gname) (root : Z) (t : ttree)
      (bs : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* THE PURE FACT THE DEED CASHES: my tree records a FILE at the node
       my descriptor is on *)
    tv_nodes t !! i = Some (AFile bs) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE: "fd is open for writing on inode i" *)
    UserFd.ufd (ukn_fd N) fd (FdOpen rb true (FdInode i γo OffParked)) -∗
    (* THE BYTES *)
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (* THE DEED, LIVE (not frozen: this call moves it) *)
    tree_own r g root t -∗
    app_inv fsc_fs -∗
    (∀ (h' : CpuId) (rv : mword 64),
       UserFd.ufd (ukn_fd N) fd (FdOpen rb true (FdInode i γo OffParked)) -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       ((⌜rv = (mword_of_int (Z.of_nat nb) : mword 64)⌝ ∗
         ⌜∃ bss : list (bv 8), length bss = nb /\
            forall j : nat, (j < nb)%nat -> bss !!! j = f j⌝)
        ∨ (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗
           ⌜∃ bss : list (bv 8), (length bss < nb)%nat /\
              forall j : nat, (j < length bss)%nat -> bss !!! j = f j⌝)) -∗
       (* ...AND THE DEED, MOVED *)
       ((∃ t' : ttree, tree_own r g root t' ∗ ⌜twrote i t t'⌝)
        ∨ tree_taint c) -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hfdv Hfdlt Hcnt Hal4 Hti.
    iIntros "#Hi Hrun Hufdh Hbuf Hown #Hinv Hcont".
    iAssert (tree_wq c r g root i t) with "[Hown]" as "Hq".
    { rewrite /tree_wq. iLeft. iExists t. iFrame "Hown". iPureIntro.
      exact (twrote_refl i t bs Hti). }
    iDestruct (tree_write_sup N m pc rb i γo (Z.of_nat nb) c r g root t
                 Heq Hcnt with "Hinv Hq") as "Hsb".
    iApply (wp_uk_ecall_write_file N h m pc avail
              (write_file_fam (fun _ : nat => tree_wq c r g root i t)
                 (ukn_pay N)) fd
              (FdOpen rb true (FdInode i γo OffParked))
              (ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f)
              nb f Hn Hfdv Hfdlt Hal4
              (fun M pmv sz =>
                 usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                   (m !!! Regidx a1_idx) nb f)
              with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' rv W cw' cs')
      "%Hk0 %Hk1 %Hk2 %Hkey %Hlz %Hsrc Hufdh Hbuf Hpost Hrun".
    iDestruct (spost_at_write_elim_at uslot
                 (write_file_fam (fun _ : nat => tree_wq c r g root i t)
                    (ukn_pay N)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                 rv (uvis_M W) (uvis_fd W) cw' cs'
                 Hk0 Hk1 Hk2 eq_refl eq_refl with "Hpost")
      as "(_ & %P & _ & _ & _ & Hp)".
    iEval (rewrite Hkey Hcnt;
           cbn [write_file_fam xfam_wr wf_Q];
           rewrite /filewrite_extra /=) in "Hp".
    iDestruct (write_arms_file_learn i γo P nb rv (uvis_M W)
                 (m !!! Regidx a1_idx) f
                 (fun _ : nat => tree_wq c r g root i t)
                 (proj1 Hsrc) with "Hp") as "Harm".
    iDestruct "Harm" as "[[%Hr H] | [%Hr H]]".
    - iDestruct "H" as (bss) "(%Hlen & %Hby & Hq)".
      iApply ("Hcont" $! h' rv with "Hufdh Hbuf [] [Hq] Hrun").
      + iLeft. iSplitR; [ by iPureIntro | ]. iPureIntro. by exists (concat bss).
      + rewrite /tree_wq. iExact "Hq".
    - iDestruct "H" as (bss p) "(%Hlen & %Hby & Hq)".
      iApply ("Hcont" $! h' rv with "Hufdh Hbuf [] [Hq] Hrun").
      + iRight. iSplitR; [ by iPureIntro | ]. iPureIntro. by exists (concat bss).
      + rewrite /tree_wq. iExact "Hq".
  Qed.

End UkTreeWrite.

(* ===================================================================== *)
(*  3.  WHERE THE TEST MEETS THE READ SIDE, AND WHAT IS STILL OWED        *)
(*                                                                       *)
(*  THE COMPOSITION THAT IS AVAILABLE TODAY.                              *)
(*  [UkTreeRead.wp_uk_ecall_open_own] hands the caller a descriptor       *)
(*  [FdOpen _ _ (FdInode i γo OffParked)] on a node its TREE records --   *)
(*  which is exactly the handle [wp_uk_tree_write_moves] takes -- and     *)
(*  [UkTreeRead.wp_uk_tree_read_learns] takes the same handle back.  So a *)
(*  verified program's own-subtree run is                                 *)
(*                                                                       *)
(*    own -> open (read side) -> WRITE (here, the deed moves)             *)
(*                            -> freeze -> read-learns (read side)        *)
(*                                                                       *)
(*  and THE SEAM BETWEEN THE TWO HALVES IS LANDED:                        *)
(*  [TreeMove.twrote_read_back] turns the write's own post -- the moved   *)
(*  tree [t'] with [twrote i t t'] -- into exactly the read corollary's   *)
(*  premises at the SAME path ([d ∈ dom (tv_nodes t')] and                *)
(*  [resolves_from t' d pl = Some (i, AFile bs')]).  It needs no          *)
(*  induction of its own: a walk reads DIRECTORY entries, a write moves a *)
(*  FILE's content, and a file's [nents] is [None] in both trees, so      *)
(*  [TreeView.npath_nents_cong] closes it in one line.  So the caller of  *)
(*  [wp_uk_tree_write_moves] can [AppTree.tree_freeze] the deed it gets   *)
(*  back and hand it straight to [UkTreeRead.wp_uk_tree_read_learns] --   *)
(*  "read back what I wrote, off my own tree", with no whole-fs pin       *)
(*  anywhere in the run.                                                  *)
(*                                                                       *)
(*  WHAT THE WRITE POST DOES NOT SAY, and it is the same wall             *)
(*  [UkWriteFile.v]'s header records one tier down: not WHICH bytes the   *)
(*  file ends with.  The kernel picks the offset of every chunk (the      *)
(*  descriptor's own [f->off], which the program does not hold at this    *)
(*  member -- design/user-read.md's OFF-OWN lane is where a held offset   *)
(*  would come from), so the honest post is the RELATION [twrote]: my     *)
(*  subtree is the one I had, except at the file I wrote.  With a HELD    *)
(*  offset ([OffGv]'s [uoff], RD-1) the chain's cursor could name the     *)
(*  splice itself, and then the write corollary would read “my tree       *)
(*  records exactly the bytes I sent”.  That is the one upgrade this      *)
(*  member is waiting for, and it is additive.                            *)
(* ===================================================================== *)
