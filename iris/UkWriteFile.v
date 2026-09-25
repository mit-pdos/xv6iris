(* ===================================================================== *)
(* UkWriteFile.v -- THE FILE ARM OF THE GENERIC WRITE LEAF.               *)
(*                                                                        *)
(* design/user-write.md section 3's INODE row.  [UkReadFile.v] cut the     *)
(* inode member out of the one read walk; this cuts it out of the one      *)
(* write walk ([UkRunSys.wp_uk_ecall_write_at]), and the three differences *)
(* from the console member are exactly [UkReadFile]'s three, one syscall   *)
(* over:                                                                   *)
(*                                                                        *)
(*   - the DEPOSIT is fixed at the STATE the caller's HANDLE names          *)
(*     ([UkReadRows.udepwf_st], which is syscall-generic) and not at the    *)
(*     low [NSTD] LEDGER, because an opened file is never a standard        *)
(*     stream ([UserFd.ufd] carries [NSTD <= fd]).  THIS IS WHY NO U-TIER   *)
(*     WRITE COULD REACH THE INODE ARM BEFORE: every write leaf in the      *)
(*     tree was ledger-fixed, and the ledger cannot name an opened file.    *)
(*   - what goes down and comes back is one [UserFd.ufd] handle, not the    *)
(*     whole [UserFd.ustd];                                                 *)
(*   - what the caller is TOLD about the key is the arm itself.             *)
(*                                                                        *)
(* THE FAMILY IS THE CONSOLE MEMBER'S, and that is not an accident: row 16 *)
(* reads ONE family field ([UexecExecInst.wf_Q], the caller's PREFIX        *)
(* CURSOR) and BOTH heavy arms of [SpecFilewrite.filewrite_in] are a CHAIN  *)
(* over it -- one node per CHUNK on the inode arm, one per BYTE on the      *)
(* console arm.  The read side needed two families ([UkReadRows.xfam_rd] /  *)
(* [xfam_rdf]) because its two arms report through different fields; the    *)
(* write side needs one.                                                    *)
(*                                                                        *)
(* ==== WHAT THE CONTENT POST IS, AND WHAT IT IS NOT ==================== *)
(*                                                                        *)
(* [SpecFilewrite.write_post_ok_at] already names everything section 3     *)
(* asks for on the success arm:                                            *)
(*                                                                        *)
(*     ∃ bss, |concat bss| = n  ∧  |bss| ≤ wchunks n                       *)
(*          ∧  ubytes_at M ua (concat bss)                                 *)
(*          ∧  awrite_chain … Q |bss| (wchunks n − |bss|)                   *)
(*                                                                        *)
(* -- and the chain at the stop position IS the cursor                     *)
(* ([FsAbsWriteFire.awrite_chain_cursor]).  What was missing at the U tier  *)
(* is the bridge that makes [ubytes_at M ua] mean anything to a program:    *)
(* [M] is the TRAPPING KEY'S image, which [UkRun.urun] binds                *)
(* existentially, so no caller could tie it to the run it owns.  The one    *)
(* write walk hands that row out ([UkRunSys.usrc_ok]'s first conjunct), and *)
(* with it the success arm reads: THE BYTES THE FILE RECEIVED ARE THE       *)
(* BYTES THE PROGRAM HAD AT a1, all [n] of them.  That is the write         *)
(* analogue of [UkReadFile.read_arms_file_learn]'s “the bytes the program   *)
(* holds ARE the file's”, and it is [write_arms_file_learn] below.          *)
(*                                                                        *)
(* WHAT IT IS NOT, and the wall is one level below this file: the post      *)
(* does NOT say what the file's abstract CONTENT became, and no U-tier      *)
(* statement can make it.  A cat-shaped dual -- “the program pins the file  *)
(* and reads its new contents off its own pin” -- is not merely missing,    *)
(* it is VACUOUS, because a pin cannot be held across a write:              *)
(*                                                                        *)
(*   the kernel's own mover updates the row for [i] at the γtop map, which  *)
(*   needs the WHOLE [ghost_map] element ([FsState.top_frag] at             *)
(*   [DfracOwn 1]) -- and that is exactly what the cache's loaded payload   *)
(*   holds while the inode is ilock'd ([IcacheEscrow.ic_loaded];            *)
(*   [FsAbs.top_frag_1_nview_excl] is the algebra).  So a client holding    *)
(*   ANY [FsAbs.nview] share of the file it is writing contradicts the      *)
(*   chain node's own premises, and every cursor it could build would be    *)
(*   proved by [False].  The read side has no such wall because the read    *)
(*   arm leaves a client share outstanding on purpose.                      *)
(*                                                                        *)
(* The channel that IS open is the one the chain was built for: the         *)
(* caller's step on the delta ([AppInv.app_step] inside                     *)
(* [FsAbsWriteFire.awrite_full_at]'s phase 1) and whatever it records in    *)
(* [Q] at each node, where [FsAbsWriteFire.wri_pre] hands it the PRE-row    *)
(* and phase 2 the post-map's reading.  This file states the member at an   *)
(* ARBITRARY [Q] so that channel is open, and instantiates it at the        *)
(* trivial one for the consumer test, which is what a program that only     *)
(* wants its bytes to land pays.                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
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
Require Import UserPerm.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkReadRows.         (* [udepwf_st] / [ufd_key_agree] *)
Require Import UkWriteLeaf.        (* row 16's family, and its two key rows *)
Require Import SpecFilewrite.      (* [filewrite_in] / [filewrite_extra] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import SpecCopyin.         (* [ubytes_at] -- the content seam *)
Require Import SysWriteDefs.       (* [wchunks] *)
Require Import UserPtTree.         (* [uptd]: the partial arm's table *)
Require Import AppInv.             (* [appE] / [app_sup] *)
Require Import FsBytesGamma.       (* [fs_gamma_L] *)
Require Import FsAbsWriteFire.     (* [awrite_chain] and its cursor *)
Require Import FsAbsInvFire.       (* [fsabs_awrite_chain] *)
Require Import FsCfg.
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkWriteFile.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY -- the console member's, see the header              *)
  (* =================================================================== *)
  Definition write_file_fam (Q : nat -> iProp Σ) (Xp : Z -> iProp Σ) : sfam :=
    xfam_wr Q Xp.

  (* =================================================================== *)
  (*  2.  THE DEPOSIT'S SUPPLIER: ONE CHUNK CHAIN, NOTHING ELSE           *)
  (* =================================================================== *)
  (* What the console arm needs is an output chain; what the file arm needs
     is the CHUNK chain the kernel's own AU spec already takes, and nothing
     at all beside it -- design/user-read.md section 1's "the per-arm
     payment is a resource the PROGRAM owns and understands", at the write
     side.  The chain is over the image [UkRun.udepwf]'s forall binds, so it
     enters as a wand over the heap the deposit lends, exactly as
     [UkWriteLeaf.uwrite_chain_sup]'s does. *)
  Lemma udepwf_st_write_file (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (rb : bool) (i : Z) (γo : gname) (Q : nat -> iProp Σ) (n : Z) :
    sys_rw_count (m !!! Regidx a2_idx) = n ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       awrite_chain (fs_gamma_L fsc_fs) appE i γo M (m !!! Regidx a1_idx) n
         Q 0%nat (wchunks n)) -∗
    udepwf_st N m pc 16 (write_file_fam Q (ukn_pay N))
      (FdOpen rb true (FdInode i γo OffParked)).
  Proof using .
    intros Hcnt. iIntros "Hch". rewrite /udepwf_st.
    iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "[Hheap Hch]".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_file_fam Q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite Hkey. cbn [write_file_fam xfam_wr wf_Q].
    rewrite /filewrite_in Hcnt. iExact "Hch".
  Qed.

  (* =================================================================== *)
  (*  3.  THE MEMBER                                                      *)
  (* =================================================================== *)
  Lemma wp_uk_ecall_write_file (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fdep : sfam) (fd : nat) (st : fdstate)
      (S : iProp Σ) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    (* THE DESCRIPTOR ARGUMENT IS THE ONE THE HANDLE NAMES.  a0 carries it
       as a C [int], so the reading is the signed low word -- the same one
       [FdSlots.fd_st_of_key] takes. *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗ S -∗
       ⌜usrc_ok M pmv sz (m !!! Regidx a1_idx) nb f⌝) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_st N m pc 16 fdep st -∗
    UserFd.ufd (ukn_fd N) fd st -∗
    S -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       (* THE ARM IS THE ONE THE HANDLE NAMES -- the console leaf's
          [take NSTD (uvis_fd W) = l], at a descriptor no ledger reaches *)
       ⌜fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) = st⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜usrc_ok (uvis_M W) (uvis_perm W) (uvis_sz W)
          (m !!! Regidx a1_idx) nb f⌝ -∗
       UserFd.ufd (ukn_fd N) fd st -∗
       S -∗
       spost_at uslot 16 fdep W r (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hfdv Hfdlt Hal4 Hsrc.
    iIntros "#Hi Hrun Hsb Hufdh Hbuf Hcont".
    iApply (wp_uk_ecall_write_at N h m pc avail fdep
              (UserFd.ufd (ukn_fd N) fd st) S
              (fun fdv => fd_st_of_key (m !!! Regidx a0_idx) fdv = st)
              nb f Hn Hal4
              (ufd_key_agree N fd st (m !!! Regidx a0_idx) Hfdv Hfdlt)
              Hsrc
              with "Hi Hrun [Hsb] Hufdh Hbuf Hcont").
    rewrite /udepwf_st /udepwf_K. iExact "Hsb".
  Qed.

  (* =================================================================== *)
  (*  4.  THE CONTENT ROW, READ OFF THE POST                              *)
  (* =================================================================== *)
  (* THE BRIDGE the U tier owed: the run the kernel says it committed IS the
     run the program owns.  [SpecCopyin.ubytes_at] is stated at the trapping
     key's IMAGE and the program's run at a SOURCE FUNCTION; the one write
     walk's image row ([UkRunSys.usrc_ok]'s first conjunct) is what joins
     them, and it can only come from there. *)
  Lemma ubytes_at_src (M : gmap Z (bv 8)) (ua : mword 64) (bs : list (bv 8))
      (nb : nat) (f : nat -> bv 8) :
    ubytes_at M ua bs ->
    (length bs <= nb)%nat ->
    (forall j : nat, (j < nb)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (f j)) ->
    forall j : nat, (j < length bs)%nat -> bs !!! j = f j.
  Proof using .
    intros Hat Hlen Himg j Hj.
    destruct (lookup_lt_is_Some_2 bs j Hj) as [c Hc].
    pose proof (Hat j c Hc) as HM.
    pose proof (Himg j ltac:(lia)) as HI.
    assert (Hfc : f j = c) by congruence.
    rewrite Hfc. exact (list_lookup_total_correct bs j c Hc).
  Qed.

  (* design/user-write.md section 3's Inode row, assembled.  The two arms
     are the kernel's own and both are honest:

       r = n   -- every byte landed, and the bytes ARE the caller's;
       r = -1  -- a PREFIX of chunks landed (possibly empty), those bytes
                  are the caller's too, and the cursor stands at the stop.

     There is no third arm: filewrite's inode loop answers [n] or [-1] and
     nothing between ([SpecFilewrite]'s decode note 3).  A writer that wants
     the left arm tests [r >= 0], which is what any real loop does. *)
  Lemma write_arms_file_learn (Γ := fs_gamma_L fsc_fs)
      (i : Z) (γo : gname) (P : uptd) (nb : nat) (r : mword 64)
      (M : gmap Z (bv 8)) (ua : mword 64) (f : nat -> bv 8)
      (Q : nat -> iProp Σ) :
    (forall j : nat, (j < nb)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (f j)) ->
    write_arms_at Γ i γo P (Z.of_nat nb) M ua Q r -∗
    ((⌜r = (mword_of_int (Z.of_nat nb) : mword 64)⌝ ∗
      ∃ bss : list (list (bv 8)),
        ⌜length (concat bss) = nb⌝ ∗
        ⌜forall j : nat, (j < nb)%nat -> concat bss !!! j = f j⌝ ∗
        Q (length bss))
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
        ∃ (bss : list (list (bv 8))) (p : nat),
          ⌜(length (concat bss) < nb)%nat⌝ ∗
          ⌜forall j : nat, (j < length (concat bss))%nat ->
             concat bss !!! j = f j⌝ ∗
          Q p)).
  Proof using .
    intros Himg. rewrite /write_arms_at /write_post_ok_at /write_post_fail_at.
    iIntros "[[%Hok Hp] | [%Hm1 Hp]]".
    - destruct Hok as [Hr _]. iLeft. iSplitR; [ by iPureIntro | ].
      iDestruct "Hp" as (bss) "(%Hlen & %Hchk & %Hat & Hch)".
      iExists bss.
      iSplitR; [ iPureIntro; lia | ].
      iSplitR.
      { iPureIntro.
        pose proof (ubytes_at_src M ua (concat bss) nb f Hat
                      ltac:(lia) Himg) as Hby.
        intros j Hj. apply Hby. lia. }
      iApply (awrite_chain_at_cursor with "Hch").
    - iRight. iSplitR; [ by iPureIntro | ].
      iDestruct "Hp" as (bss x) "(%Hlt & %Hchk & %Hx & %Hat & Hch)".
      assert (Hlen : (length (concat bss) < nb)%nat) by (destruct Hlt; lia).
      iExists bss, (length bss + x)%nat.
      iSplitR; [ by iPureIntro | ].
      iSplitR.
      { iPureIntro.
        exact (ubytes_at_src M ua (concat bss) nb f Hat ltac:(lia) Himg). }
      iApply (awrite_chain_at_cursor with "Hch").
  Qed.

  (* =================================================================== *)
  (*  5.  THE CONSUMER TEST -- A PROGRAM'S BYTES LAND IN ITS FILE          *)
  (* =================================================================== *)
  (* THE TEST THE LANE OWES, at the strength the tree supports (header): a
     program holding a descriptor open for WRITING on a known inode, and a
     run of its own bytes, writes them and LEARNS that the run the kernel
     committed is exactly its own.  It falls out of the member with nothing
     new: the only thing it builds is the chain, and it builds it at the
     trivial cursor out of the application's supply
     ([FsAbsInvFire.fsabs_awrite_chain]) -- which is what a program that
     only wants its bytes to land pays.

     WHAT IT DOES NOT SAY is in the header: not what the file's abstract
     content became, because a pin cannot be held across a write. *)
  Lemma wp_uk_write_file_lands (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fd : nat) (rb : bool) (i : Z)
      (γo : gname) (dq : dfrac) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE: "fd is open for writing on inode i" *)
    UserFd.ufd (ukn_fd N) fd (FdOpen rb true (FdInode i γo OffParked)) -∗
    (* THE BYTES *)
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (* the application's supply, which is what the chain costs at the
       trivial cursor *)
    app_sup -∗
    (∀ (h' : CpuId) (r : mword 64),
       UserFd.ufd (ukn_fd N) fd (FdOpen rb true (FdInode i γo OffParked)) -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       ((⌜r = (mword_of_int (Z.of_nat nb) : mword 64)⌝ ∗
         ⌜∃ bs : list (bv 8), length bs = nb /\
            forall j : nat, (j < nb)%nat -> bs !!! j = f j⌝)
        ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
           ⌜∃ bs : list (bv 8), (length bs < nb)%nat /\
              forall j : nat, (j < length bs)%nat -> bs !!! j = f j⌝)) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hfdv Hfdlt Hcnt Hal4.
    iIntros "#Hi Hrun Hufdh Hbuf #Hsup Hcont".
    iDestruct (udepwf_st_write_file N m pc rb i γo (fun _ => True%I)
                 (Z.of_nat nb) Hcnt with "[]") as "Hsb".
    { iIntros (M pm sz) "Hheap". iFrame "Hheap".
      iApply (fsabs_awrite_chain fsc_fs i γo M (m !!! Regidx a1_idx)
                (Z.of_nat nb) 0%nat (wchunks (Z.of_nat nb)) with "Hsup"). }
    iApply (wp_uk_ecall_write_file N h m pc avail
              (write_file_fam (fun _ => True%I) (ukn_pay N)) fd
              (FdOpen rb true (FdInode i γo OffParked))
              (ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f)
              nb f Hn Hfdv Hfdlt Hal4
              (fun M pmv sz =>
                 usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                   (m !!! Regidx a1_idx) nb f)
              with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' r W cw' cs')
      "%Hk0 %Hk1 %Hk2 %Hkey %Hlz %Hsrc Hufdh Hbuf Hpost Hrun".
    iDestruct (spost_at_write_elim_at uslot
                 (write_file_fam (fun _ => True%I) (ukn_pay N)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                 r (uvis_M W) (uvis_fd W) cw' cs'
                 Hk0 Hk1 Hk2 eq_refl eq_refl with "Hpost")
      as "(_ & %P & _ & _ & _ & Hp)".
    iEval (rewrite Hkey Hcnt;
           cbn [write_file_fam xfam_wr wf_Q];
           rewrite /filewrite_extra /=) in "Hp".
    iDestruct (write_arms_file_learn i γo P nb r (uvis_M W)
                 (m !!! Regidx a1_idx) f (fun _ => True%I)
                 (proj1 Hsrc) with "Hp") as "Harm".
    iApply ("Hcont" $! h' r with "Hufdh Hbuf [Harm] Hrun").
    iDestruct "Harm" as "[[%Hr H] | [%Hr H]]".
    - iDestruct "H" as (bss) "(%Hlen & %Hby & _)". iLeft.
      iSplitR; [ by iPureIntro | ]. iPureIntro. by exists (concat bss).
    - iDestruct "H" as (bss p) "(%Hlen & %Hby & _)". iRight.
      iSplitR; [ by iPureIntro | ]. iPureIntro. by exists (concat bss).
  Qed.

  (* =================================================================== *)
  (*  6.  THE LEDGER SLOT (lane OFF-LINK, L5)                             *)
  (*                                                                     *)
  (*  echo writes fd 1, which is BELOW [NSTD]: its descriptor knowledge   *)
  (*  is the whole ledger ([UserFd.ustd]) and its deposit is fixed at the  *)
  (*  ledger ([UkRun.udepwf_std]), while section 3's member is            *)
  (*  handle-fixed at [NSTD <= fd].  These two are that member's ledger    *)
  (*  twins and nothing else: same walk, same family, same post; the      *)
  (*  descriptor knowledge and the deposit's reading are what change.     *)
  (* =================================================================== *)

  (* THE ARM, OUT OF THE CALLER'S OWN LEDGER, at ANY state -- the general
     form of [UkWriteLeaf.uwr_fd_st_dev], whose proof this is verbatim.  A
     ledger slot is below [NSTD] and [NSTD <= NOFILE], so the key's total
     lookup is the ledger's own entry. *)
  Lemma uwr_fd_st_std (v0 : mword 64) (fdv l : list fdstate)
      (i : nat) (st : fdstate) :
    bv_signed (trunc32 v0) = Z.of_nat i ->
    (i < NSTD)%nat ->
    take NSTD fdv = l ->
    l !! i = Some st ->
    fd_st_of_key v0 fdv = st.
  Proof using .
    intros H0 Hi Htake Hli. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= Z.of_nat i < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; unfold NOFILE, NSTD in *; lia ].
    rewrite <- Htake in Hli.
    rewrite lookup_take in Hli; [ | exact Hi ].
    rewrite Nat2Z.id Hli. reflexivity.
  Qed.

  (* THE DEPOSIT AT LEDGER SLOT 1, [udepwf_st_write_file]'s twin: the chain
     enters as a wand over the heap the deposit lends (the same shape
     [UkWriteLeaf.uwrite_chain_sup] uses), and the arm is computed from the
     ledger rather than from a handle.  The state's OFFSET MODE is free:
     [SpecFilewrite.filewrite_in]'s inode arm is mode-blind, which is what
     lets a HELD descriptor use this deposit unchanged. *)
  Lemma udepwf_std_write_file (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (l : list fdstate) (rb : bool) (i : Z) (γo : gname)
      (Q : nat -> iProp Σ) (n : Z) :
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffParked)) ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 1%Z ->
    sys_rw_count (m !!! Regidx a2_idx) = n ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       awrite_chain (fs_gamma_L fsc_fs) appE i γo M (m !!! Regidx a1_idx) n
         Q 0%nat (wchunks n)) -∗
    udepwf_std N m pc 16 (write_file_fam Q (ukn_pay N)) l.
  Proof using .
    intros Hl1 H0 Hcnt. iIntros "Hch".
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "[Hheap Hch]".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_file_fam Q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite (uwr_fd_st_std (m !!! Regidx a0_idx) fdv l 1%nat
               (FdOpen rb true (FdInode i γo OffParked))
               H0 ltac:(unfold NSTD; lia) Htake Hl1).
    cbn [write_file_fam xfam_wr wf_Q].
    rewrite /filewrite_in Hcnt. iExact "Hch".
  Qed.

  (* ...AND THE HELD LEDGER SLOT (lanes OFF-LINK-4/5, L5): echo's fd 1 on
     [f] is HELD, so what it hands in is the LINK -- the CLIENT-ADVANCED
     chain ([SpecFilewrite.filewrite_in_held]), whose nodes keep the
     program's own half of the offset shadow in their closure and hand the
     box's arm back advanced.  The half is therefore NOT a separate premise
     of this leaf: it is inside the chain the caller builds, which is where
     echo keeps it between calls.  Everything else is the parked twin
     above, verbatim. *)
  Lemma udepwf_std_write_file_held (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (l : list fdstate) (rb : bool) (i : Z) (γo : gname)
      (Q : nat -> iProp Σ) (n : Z) :
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 1%Z ->
    sys_rw_count (m !!! Regidx a2_idx) = n ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       (* the chain, under the write guard at the key's own three values
          (RULING WR-TB) -- and NOTHING beside it: one cursor, once. *)
       (∀ P : uptd, ⌜wr_tb pm sz false P⌝ -∗
          awrite_chain_adv (fs_gamma_L fsc_fs) appE i γo M
            (m !!! Regidx a1_idx) P n Q 0%nat (wchunks n))) -∗
    udepwf_std N m pc 16 (write_file_fam Q (ukn_pay N)) l.
  Proof using .
    intros Hl1 H0 Hcnt. iIntros "Hch".
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "[Hheap Hch]".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_file_fam Q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite (uwr_fd_st_std (m !!! Regidx a0_idx) fdv l 1%nat
               (FdOpen rb true (FdInode i γo OffHeld))
               H0 ltac:(unfold NSTD; lia) Htake Hl1).
    cbn [write_file_fam xfam_wr wf_Q].
    rewrite /filewrite_in Hcnt /filewrite_in_held.
    iLeft. iExact "Hch".
  Qed.

  (* THE LEDGER-SLOT WRITE LEAF, [wp_uk_ecall_write_file]'s twin: the one
     write walk at [K fdv := take NSTD fdv = l], with [UserFd.ustd] in
     place of [UserFd.ufd] and [UkRun.udepwf_std] in place of [udepwf_st].
     Nothing about the file is in it -- it is
     [UkRunSys.wp_uk_ecall_write_chain_buf] with the buffer replaced by an
     abstract [S] and its source-run row, which is the shape a program that
     owns its output as a claim (rather than as [ubytesq]) needs. *)
  Lemma wp_uk_ecall_write_std (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fdep : sfam) (l : list fdstate)
      (S : iProp Σ) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 1%Z ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗ S -∗
       ⌜usrc_ok M pmv sz (m !!! Regidx a1_idx) nb f⌝) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_std N m pc 16 fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    S -∗
    (∀ (h' : CpuId) (rv : mword 64) (W : uvis) (cw' : Z)
       (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜usrc_ok (uvis_M W) (uvis_perm W) (uvis_sz W)
          (m !!! Regidx a1_idx) nb f⌝ -∗
       UserFd.ustd (ukn_fd N) l -∗
       S -∗
       spost_at uslot 16 fdep W rv (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn H0 Hal4 Hsrc.
    iIntros "#Hi Hrun Hsb Hstd Hbuf Hcont".
    iApply (wp_uk_ecall_write_at N h m pc avail fdep
              (UserFd.ustd (ukn_fd N) l) S
              (fun fdv => take NSTD fdv = l) nb f Hn Hal4
              (fun fdv => ustd_agree (ukn_fd N) fdv l)
              Hsrc
              with "Hi Hrun [Hsb] Hstd Hbuf Hcont").
    iApply (udepwf_K_std N m pc 16 fdep l with "Hsb").
  Qed.

End UkWriteFile.
