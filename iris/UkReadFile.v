(* ===================================================================== *)
(* UkReadFile.v -- THE FILE ARM OF THE GENERIC READ LEAF.                  *)
(*                                                                        *)
(* design/user-read.md section 3 is one leaf whose ARM is chosen by the    *)
(* caller's own descriptor knowledge and whose CONTENT post comes from the *)
(* kernel's AU spec at every arm.  [UkRunSys.wp_uk_ecall_read_recv] built  *)
(* the mechanism -- the window walk with the kernel's [spost_at] KEPT --   *)
(* and cut its CONSOLE member; this file cuts the INODE member out of the  *)
(* same walk.  What is shared is everything that made the receipt          *)
(* READABLE, and section 5 is right that it is arm-independent: the        *)
(* resume-image bytes, the destination's linearity, the writable-mapped    *)
(* row, the three trapframe-argument ties, the lazy bit and the live row   *)
(* are copied here unchanged.                                             *)
(*                                                                        *)
(* WHAT IS DIFFERENT IS THE DEPOSIT, and only the deposit.  A console read *)
(* is about a STANDARD stream, so [UkRun.udepwf_std] fixes the low [NSTD]  *)
(* slots and the leaf reads the arm off the caller's LEDGER.  A file read  *)
(* is about a descriptor the program OPENED, which is never a standard     *)
(* stream ([UserFd.ufd] carries [NSTD <= fd]), so the ledger says nothing  *)
(* about it: what fixes the arm here is the caller's own HANDLE, and the   *)
(* deposit is fixed at the STATE that handle names ([udepwf_st] below).    *)
(* That is section 3's [udepwf_at (kind)], at the one name still free --   *)
(* [UkRun.udepwf_at] is the CWD-fixed form and [udepwf_std] the            *)
(* ledger-fixed one, so this is the STATE-fixed third.                     *)
(*                                                                        *)
(* THE OFFSET IS REPORTED, NOT OWNED -- design/user-read.md section 3's    *)
(* R-c.  The RULED mode-in-state (a descriptor that records parked vs      *)
(* held) is not implementable without a parked-table discipline through    *)
(* the generic-safety tier; that finding, and the three routes out, are    *)
(* written up in that section's RD-2 AS-LANDED block.  What survives it    *)
(* untouched is the CONTENT row, because [FsAbsReadFire.read_post_ok]      *)
(* already names the offset EXISTENTIALLY and ties everything else to it:  *)
(*                                                                        *)
(*    exists av off a d,  ard_pre av i off a  /\  0 <= n                   *)
(*                     /\  ard_ret_tie n a off r                           *)
(*                     /\  Z.of_nat d = bv_unsigned r                      *)
(*                     /\  (on an AFile row) the d bytes at the            *)
(*                         destination ARE bs[off .. off+d)                *)
(*                     /\  the caller's own receipt at (av, off, a, d)     *)
(*                                                                        *)
(* So a program that pins its file learns exactly what it read, at a       *)
(* position the call TELLS it rather than one it predicted.  When R-a      *)
(* lands, this leaf's statement gains the [uoff] conjuncts and LOSES the   *)
(* [off] existential; nothing else about it moves.                         *)
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
Require Import UserPerm.           (* [perm_of] / [lazy_free] *)
Require Import ProcPtOwn.          (* [uptd] / [ud_um] / [proc_pt_wf] *)
Require Import UserPtTree.         (* [uva_wmapped] / [umem_write] *)
Require Import UmodeArith.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import PieceFam.           (* [pfam] / [pf_at] / [pfam_triv] *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UkReadRows.         (* the read leaf's SHARED key-level rows:
                                      [xfam_rdf], the intro/elim pair, the
                                      two [fd_st_of_key] readings *)
Require Import SpecFileread.       (* [fileread_in] / [fileread_extra_core] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import AppInv.             (* [appE] -- the commit mask *)
Require Import BioDefs.            (* [BSIZE] *)
Require Import InodeInv.           (* [MAXFILE] -- the row size cap *)
Require Import SysReadDefs.        (* [ard_count] / [ard_pre] *)
Require Import FsAbsDefs.          (* [aview] / [anode] / [abs_row] *)
Require Import FsBytesGamma.       (* [fs_gamma_L] *)
Require Import FsAbsReadFire.      (* [aread_commit_at] / [read_arms] *)
Require Import FsAbs.              (* [nview] -- LAST (FsAbs's own rule) *)
Require Import FsCfg.
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkReadFile.
  (* [UShLine]'s binder list, minus the echo application's own cameras:
     nothing here is about an application, which is the point. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* GENERIC IN THE PROGRAM-DEPOSIT INSTANCE (PROGRAM-STREAM stretch 13,
     defect 4): with no binder every [urun] here was at the ambient
     [uprogSG_gen], whose [udep] only an out-of-spec run supplies, so a
     verified shell (at [uprogSG_free]) could not exec cat.  A caller that
     resolves ambiently still gets [uprogSG_gen], exactly as before. *)
  (* SPELLED [UexecSG.uprogSG]: with the class not imported here, a bare
     [uprogSG] under the backtick is silently GENERALISED into a fresh
     variable and [PS] gets the wrong type (measured 2026-09-22). *)
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* [UkReadRows.xfam_rdf] is the record ([UexecExecInst.xfam] at the ONE
     field the inode arm's rows look at, [rf_F]); it MOVED to that file
     beside its console twin [xfam_rd], which is what the two arms'
     difference actually is. *)
  (* AT THE CLASS'S OWN FAMILY TYPE ([UShLine.ush_read_fam_at]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument
     is checked before the instance evar is resolved and so does not
     convert. *)
  Definition read_file_fam (Q : Z -> iProp Σ)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) : sfam :=
    xfam_rdf Q F.

  (* =================================================================== *)
  (*  2.  THE STATE-FIXED DEPOSIT -- MOVED (lane RD-6)                     *)
  (* =================================================================== *)
  (* [udepwf_st], [udepwf_st_K] and [ufd_key_agree] now live in
     [UkReadRows.v], at their exact former statements.  They are
     ARM-independent (this "file" leaf is really the HANDLE leaf) and
     SYSCALL-independent, and the write side's file arm reaches its own row
     through the same two -- which is the housekeeping item
     design/user-read.md section 3 recorded and lane RD-6 could take for
     free, since the one write walk invalidates that cone anyway.  Every
     name still resolves here: this file imports [UkReadRows]. *)

  (* =================================================================== *)
  (*  4.  THE LEAF                                                        *)
  (* =================================================================== *)
  (* [UkRunSys.wp_uk_ecall_read_at]'s walk, at the FILE arm -- and since
     lane RD-4 it IS that walk and no longer a second copy of it: section
     5's "the rows the recv leaf hands out are ARM-INDEPENDENT" is not only
     true, it is the generalization the duplication was in disguise, so the
     rows below are handed out by the one walk and this leaf only names the
     descriptor.  The three differences are all in the descriptor:

       - the DEPOSIT is fixed at the STATE the caller's handle names
         ([udepwf_st]) rather than at the low [NSTD] ledger, because an
         opened file is never a standard stream;
       - what goes down and comes back is [UserFd.ufd] (one handle), not
         [UserFd.ustd] (the whole ledger);
       - what the caller is TOLD about the key is the arm itself --
         [fd_st_of_key (a0) (uvis_fd W) = st] -- which is what makes the
         post's inode arm readable: without it, row 5's receipt is about
         a descriptor the caller cannot identify with its own.

     A program spends this leaf's post through [spost_at_read_elim]
     above and lands in [SpecFileread.fileread_extra_core] at its own
     [st]; at [FdOpen true _ (FdInode i γo OffParked)] that IS
     [FsAbsReadFire.read_arms], and section 3's whole File row is inside
     it. *)
  Lemma wp_uk_ecall_read_file (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8)
      (avail : nat) (fdep : sfam) (fd : nat) (st : fdstate) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    (* THE DESCRIPTOR ARGUMENT IS THE ONE THE HANDLE NAMES.  a0 carries it
       as a C [int], so the reading is the signed low word -- the same one
       [FdSlots.fd_st_of_key] takes. *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_st N m pc USYS_read fdep st -∗
    UserFd.ufd (ukn_fd N) fd st -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (W : uvis) (M' : gmap Z (bv 8))
       (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
       ⌜ (d <= Z.to_nat cnt)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       (* the destination run is linear, and the resume image holds the
          bytes -- the two rows that turn a receipt stated at [M'] into a
          fact about the buffer the program owns at a source function *)
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat i))
           = (uint (m !!! Regidx a1_idx) + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (g j) ⌝ -∗
       (* ...and every byte of it is writable-mapped in any table the
          key's projection admits *)
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < k)%nat ->
           UserPtTree.uva_wmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       (* the trapping key's three argument words are the caller's own *)
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       (* ...AND THE ARM IS THE ONE THE HANDLE NAMES.  The console leaf's
          [take NSTD (uvis_fd W) = l], at a descriptor no ledger can
          reach. *)
       ⌜fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) = st⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜uexec_live_ok USYS_read (uvis_tf W) (uvis_fd W) r cs'⌝ -∗
       (* the handle comes straight back: read moves no descriptor *)
       UserFd.ufd (ukn_fd N) fd st -∗
       (* THE POST, AT THE TRAPPING KEY AND THE RESUME IMAGE *)
       spost_at uslot USYS_read fdep W r M' fdv' cw' cs' -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hcnt Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hsb Hufdh Hbuf Hcont".
    iApply (wp_uk_ecall_read_at N h m pc cnt k f avail fdep
              (UserFd.ufd (ukn_fd N) fd st)
              (fun fdv => fd_st_of_key (m !!! Regidx a0_idx) fdv = st)
              Hn Hcnt Hcapk Hal4
              (ufd_key_agree N fd st (m !!! Regidx a0_idx) Hfdv Hfdlt)
              with "Hi Hrun [Hsb] Hufdh Hbuf Hcont").
    rewrite /udepwf_st /udepwf_K. iExact "Hsb".
  Qed.

  (* =================================================================== *)
  (*  5.  THE DEPOSIT'S SUPPLIER: ONE OBSERVATION COMMIT, NOTHING ELSE     *)
  (* =================================================================== *)
  (* What the console arm needs is a LEASE and an input licence; what the
     file arm needs is the commit the kernel's AU spec already takes, and
     nothing at all beside it.  That is the whole content of "the per-arm
     payment is a resource the PROGRAM owns and understands"
     (design/user-read.md section 1): a file read costs its caller the AU
     it chose, and a caller that wants to be told nothing pays
     [FsAbsInvFire.fsabs_aread] from thin air. *)
  Lemma udepwf_st_read_file (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (wb : bool) (i : Z) (γo : gname)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) :
    pf_at (aread_commit_at (fs_gamma_L fsc_fs) appE i γo) F -∗
    udepwf_st N m pc USYS_read (read_file_fam (ukn_pay N) F)
      (FdOpen true wb (FdInode i γo OffParked)).
  Proof using .
    iIntros "Hau". rewrite /udepwf_st.
    iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot (xfam_rdf (ukn_pay N) F)
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a2_idx) fdv
              (tf_of_arg0 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)).
    rewrite Hkey. rewrite /fileread_in /=. iIntros "$". iExact "Hau".
  Qed.

  (* ...AND THE HELD ROW'S (kernel stream, item 2): the same deposit at the
     CLIENT-ADVANCED commit, which is the LINK arm of [SpecFileread]'s
     held reading.  Nothing else about the leaf changes -- the mode is read
     off the descriptor's own state and the arm is keyed on it. *)
  Lemma udepwf_st_read_file_held (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (wb : bool) (i : Z) (γo : gname)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) :
    pf_at (aread_commit_adv (fs_gamma_L fsc_fs) appE i γo) F -∗
    udepwf_st N m pc USYS_read (read_file_fam (ukn_pay N) F)
      (FdOpen true wb (FdInode i γo OffHeld)).
  Proof using .
    iIntros "Hau". rewrite /udepwf_st.
    iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot (xfam_rdf (ukn_pay N) F)
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a2_idx) fdv
              (tf_of_arg0 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)).
    rewrite Hkey. rewrite /fileread_in /=. iIntros "$".
    rewrite /aread_in_om. by iLeft.
  Qed.

  (* =================================================================== *)
  (*  6.  THE FILE ROW, READ OFF THE POST                                 *)
  (* =================================================================== *)
  (* design/user-read.md section 3's Inode arm, assembled: at a PINNED
     file the receipt's own row IS the content post, and the leaf's
     resume-image bridge is what carries it into the buffer the program
     holds. *)
  (* THE CALLER'S RECEIPT FAMILY: the pin goes in, the pin comes back, and
     the observed row is named.  Named once because three lemmas below and
     the test at the end of the file all speak it. *)
  Definition file_read_fam (i : Z) (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Γ := fs_gamma_L fsc_fs)
      : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ) :=
    MkPfam (fun (av : aview) (_ : nat) (_ : anode) (_ : nat) =>
              (⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
               nview Γ q i (MkAnode (AFile bs0) nl))%I)
           (nview Γ q i (MkAnode (AFile bs0) nl)).

  Lemma read_post_ok_file_learn (Γ := fs_gamma_L fsc_fs)
      (i : Z) (n : Z) (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_post_ok Γ i n (file_read_fam i q bs0 nl) r M' addr -∗
    nview Γ q i (MkAnode (AFile bs0) nl) ∗
    (∃ off : nat,
       (* the COUNT: exactly design section 3's [min (cnt, |bs| - off)] *)
       ⌜Z.to_nat (bv_unsigned r)
        = ard_count (Z.to_nat n) off (length bs0)⌝ ∗
       (* ...AND THE BYTES THE PROGRAM HOLDS ARE THE FILE'S *)
       ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
          g j = bs0 !!! (off + j)%nat⌝).
  Proof using .
    intros Hlin Himg Hnk. rewrite /read_post_ok /file_read_fam.
    cbn [pf_recv pf_refund].
    iIntros "Hok".
    iDestruct "Hok" as (av off a d) "(%Hpre & %Hn & %Htie & %Hdr & %Hbytes & [%Hav Hn2])".
    (* the pin collapses the observed row onto the caller's value *)
      destruct Hpre as (Hrow & _ & Hsz).
      assert (Hab : a = MkAnode (AFile bs0) nl)
        by exact (arow_at_pinned _ _ _ _ Hrow Hav).
      subst a. cbn [an_node] in Htie, Hbytes.
      (* the cap at [Z], factor by factor: a [/=] here computes
         [MAXFILE * BSIZE] as a 274432-deep unary [nat] and overflows *)
      cbn [anode_size_ok an_node] in Hsz.
      apply Nat2Z.inj_le in Hsz. rewrite Nat2Z.inj_mul in Hsz.
      change (Z.of_nat MAXFILE) with 268 in Hsz.
      change (Z.of_nat BSIZE) with 1024 in Hsz.
      iFrame "Hn2". iExists off.
      (* the return value IS the clamped count, so [d] is it too.  The
         count fits a 64-bit word because the row's own SIZE CAP is what
         [ard_pre] carries: a file is at most [MAXFILE * BSIZE] bytes, so
         nothing here has to be assumed about how big a file can be. *)
      assert (Hdc : d = ard_count (Z.to_nat n) off (length bs0)).
      { assert (Hbu : bv_unsigned r
                      = Z.of_nat (ard_count (Z.to_nat n) off (length bs0))).
        { rewrite Htie. apply moi_small.
          pose proof (ard_count_sub (Z.to_nat n) off (length bs0)) as Hle.
          unfold Z64. lia. }
        lia. }
      iPureIntro. split.
      { rewrite -Hdr Nat2Z.id. exact Hdc. }
      intros j Hj.
      assert (Hjd : (j < d)%nat) by (rewrite -Hdr Nat2Z.id in Hj; lia).
      (* the delivered run sits inside the one the caller owns, so the
         two pure rows are about the same bytes *)
      assert (Hdk : (d <= k)%nat).
      { pose proof (ard_count_le (Z.to_nat n) off (length bs0)) as Hle. lia. }
      pose proof (Hbytes ltac:(intros i0 Hi0; apply Hlin; lia) j Hjd) as HM.
      pose proof (Himg j ltac:(lia)) as HG.
      rewrite HM in HG. by injection HG.
  Qed.

  (* ...AND THE ARMS.  The disjunction is honest and it is the kernel's,
     not a weakening: readi answers -1 when a copyout faults, and this
     statement says only THAT it did.  Since lane READ-RELAY the arm also
     says WHY, which is what [read_arms_file_learn_mapped] below spends;
     a caller that does not own its buffer keeps this form and tests
     [r >= 0], which is what cat's loop does. *)
  Lemma read_arms_file_learn (Γ := fs_gamma_L fsc_fs)
      (i : Z) (γo : gname) (P : uptd) (n : Z) (q : Qp) (bs0 : list (bv 8))
      (nl : nat)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_arms Γ i γo P n (file_read_fam i q bs0 nl) r M' addr -∗
    nview Γ q i (MkAnode (AFile bs0) nl) ∗
    (⌜r = (mword_of_int (-1) : mword 64)⌝
     ∨ (∃ off : nat,
          ⌜Z.to_nat (bv_unsigned r)
           = ard_count (Z.to_nat n) off (length bs0)⌝ ∗
          ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
             g j = bs0 !!! (off + j)%nat⌝)).
  Proof using .
    intros Hlin Himg Hnk. rewrite /read_arms /read_post_fail.
    iIntros "[Hok | [%Hm1 Hfail]]".
    - iDestruct (read_post_ok_file_learn i n q bs0 nl r M' addr k g
                   Hlin Himg Hnk with "Hok") as "[$ H]".
      iRight. iExact "H".
    - (* the sign guard hands the piece back unfired; the fault arm fires
         at advance 0.  Either way the pin comes home and nothing is
         claimed about the buffer. *)
      rewrite /file_read_fam. cbn [pf_recv pf_refund].
      iSplitL "Hfail"; [ | iLeft; by iPureIntro ].
      iDestruct "Hfail" as "[[_ Hpf] | [_ [_ Hrec]]]".
      + iApply (pf_at_refund with "Hpf").
      + iDestruct "Hrec" as (av off a) "[_ [_ $]]".
  Qed.

  (* ...AND AT A MAPPED DESTINATION THERE IS NO -1 ARM (lane READ-RELAY,
     deliverable 2).  The premise is the row the leaf below already hands
     out -- "every byte of the run I own is writable-mapped in any table the
     trapping key admits" -- and it is the read's twin of the mapped row
     with which [UkRunSys.usrc_ok] refutes the console write's short arm.
     ONE LINE: the relay carried the copyout's reason all the way here, so
     the arm dies at [FsAbsReadFire.read_arms_mapped] and what is left is
     the ok arm this file already reads. *)
  Lemma read_arms_file_learn_mapped (Γ := fs_gamma_L fsc_fs)
      (i : Z) (γo : gname) (P : uptd) (n : Z) (q : Qp) (bs0 : list (bv 8))
      (nl : nat)
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (0 <= n)%Z ->
    (Z.to_nat n <= k)%nat ->
    (forall j : nat, (j < k)%nat ->
       uva_wmapped P (uint (add_vec_int addr (Z.of_nat j)))) ->
    read_arms Γ i γo P n (file_read_fam i q bs0 nl) r M' addr -∗
    nview Γ q i (MkAnode (AFile bs0) nl) ∗
    (∃ off : nat,
       ⌜Z.to_nat (bv_unsigned r)
        = ard_count (Z.to_nat n) off (length bs0)⌝ ∗
       ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
          g j = bs0 !!! (off + j)%nat⌝).
  Proof using .
    intros Hlin Himg Hn Hnk Hmap. iIntros "H".
    iApply (read_post_ok_file_learn i n q bs0 nl r M' addr k g
              Hlin Himg Hnk).
    iApply (read_arms_mapped Γ i γo P n (file_read_fam i q bs0 nl) r M' addr k
              Hn Hnk Hmap with "H").
  Qed.

  (* =================================================================== *)
  (*  7.  THE CONSUMER TEST -- cat, AT A CONCRETE FILE                     *)
  (* =================================================================== *)
  (* THE TEST THE LANE OWES (design/user-read.md section 3, RD-2's brief
     deliverable 5): a program holding a descriptor on a KNOWN file reads
     and LEARNS the bytes, and it has to fall out of the leaf with no new
     machinery.  It does: the only things this lemma builds are the
     caller's own receipt family (its pin, handed back) and the leaf's
     premises.  The file is a concrete four-byte one, spelled as a list,
     because the point of a test is that nothing about it is general. *)
  Definition cat_file : list (bv 8) :=
    [ Z_to_bv 8 104%Z;   (* 'h'  *)
      Z_to_bv 8 105%Z;   (* 'i'  *)
      Z_to_bv 8 33%Z;    (* '!'  *)
      Z_to_bv 8 10%Z ].  (* '\n' *)

  (* the caller's receipt family IS [file_read_fam] at the test's own file:
     the pin goes in, the pin comes back, and the observed row is named. *)

  (* the caller's ONE piece, out of its pin and nothing else *)
  Lemma cat_piece (Γ := fs_gamma_L fsc_fs) (q : Qp) (i : Z) (γo : gname)
      (nl : nat) :
    nview Γ q i (MkAnode (AFile cat_file) nl) -∗
    pf_at (aread_commit_at Γ appE i γo) (file_read_fam i q cat_file nl).
  Proof using .
    iIntros "Hn". rewrite /pf_at /file_read_fam /=. iSplit; [ | iExact "Hn" ].
    iApply (aread_commit_at_pinned_self Γ appE i γo q
              (MkAnode (AFile cat_file) nl) with "Hn").
    iIntros (av off d) "%Hav Hn". iSplitR; [ by iPureIntro | iExact "Hn" ].
  Qed.

  Lemma wp_uk_cat_read_learns (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname) (q : Qp) (nl : nat)
      (Γ := fs_gamma_L fsc_fs) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE: "fd is open for reading on inode i" -- the caller's own
       knowledge of its descriptor, which is what selects the arm *)
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
    (* THE PIN: "that inode is this file" *)
    nview Γ q i (MkAnode (AFile cat_file) nl) -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
       nview Γ q i (MkAnode (AFile cat_file) nl) -∗
       (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∨ (∃ off : nat,
             ⌜Z.to_nat (bv_unsigned r)
              = ard_count (Z.to_nat cnt) off (length cat_file)⌝ ∗
             ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
                g j = cat_file !!! (off + j)%nat⌝)) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hcnt Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh Hpin Hbuf Hcont".
    iDestruct (cat_piece q i γo nl with "Hpin") as "Hau".
    iDestruct (udepwf_st_read_file N m pc wb i γo (file_read_fam i q cat_file nl)
                 with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_file N h m pc cnt k f avail
              (read_file_fam (ukn_pay N) (file_read_fam i q cat_file nl)) fd
              (FdOpen true wb (FdInode i γo OffParked))
              Hn Hcnt Hcapk Hfdv Hfdlt Hal4 with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (xfam_rdf (ukn_pay N) (file_read_fam i q cat_file nl)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W)
                 r M' fdv' cw' cs' H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(_ & _ & _ & Hcore)".
    rewrite Hkey.
    (* the arm, at the state the handle named *)
    rewrite /fileread_extra_core /=.
    (* the count the receipt is stated at IS the caller's own *)
    assert (Hc2 : sys_rw_count (m !!! Regidx a2_idx) = cnt)
      by (rewrite /sys_rw_count /trunc32; exact Hcnt).
    rewrite Hc2.
    iDestruct (read_arms_file_learn i γo P cnt q cat_file nl r M'
                 (m !!! Regidx a1_idx) k g Hlin Himg ltac:(lia)
                 with "Hcore") as "[Hpin Hlearn]".
    iApply ("Hcont" $! h' r g with "Hufdh Hpin Hlearn Hrun Hbuf").
  Qed.

  (* ...AND THE SAME TEST WITH THE -1 ARM GONE (lane READ-RELAY,
     deliverable 2).  The program pays NOTHING new for it: the mapped row
     is one the leaf already hands out beside the resume image (it owns the
     whole destination run, so every byte of it is writable-mapped in any
     table the trapping key admits), and the only premise this adds is that
     the request is not negative -- which is fileread's own sign guard and
     the one -1 the relay does not speak to.  The refutation itself is one
     [read_arms_file_learn_mapped]. *)
  Lemma wp_uk_cat_read_learns_mapped (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname) (q : Qp) (nl : nat)
      (Γ := fs_gamma_L fsc_fs) :
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (0 <= cnt)%Z ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
    nview Γ q i (MkAnode (AFile cat_file) nl) -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
       nview Γ q i (MkAnode (AFile cat_file) nl) -∗
       (∃ off : nat,
          ⌜Z.to_nat (bv_unsigned r)
           = ard_count (Z.to_nat cnt) off (length cat_file)⌝ ∗
          ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
             g j = cat_file !!! (off + j)%nat⌝) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hcnt Hcnt0 Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh Hpin Hbuf Hcont".
    iDestruct (cat_piece q i γo nl with "Hpin") as "Hau".
    iDestruct (udepwf_st_read_file N m pc wb i γo (file_read_fam i q cat_file nl)
                 with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_file N h m pc cnt k f avail
              (read_file_fam (ukn_pay N) (file_read_fam i q cat_file nl)) fd
              (FdOpen true wb (FdInode i γo OffParked))
              Hn Hcnt Hcapk Hfdv Hfdlt Hal4 with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (xfam_rdf (ukn_pay N) (file_read_fam i q cat_file nl)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W)
                 r M' fdv' cw' cs' H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(%Hperm & %Hwf & %Hlazy & Hcore)".
    (* THE MAPPED ROW, out of the leaf's own hand *)
    assert (Hmap : forall j : nat, (j < k)%nat ->
              uva_wmapped P
                (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))))
      by (intros j Hj; exact (Hnf P j Hwf Hperm (Hlazy Hlz) Hj)).
    rewrite Hkey.
    rewrite /fileread_extra_core /=.
    assert (Hc2 : sys_rw_count (m !!! Regidx a2_idx) = cnt)
      by (rewrite /sys_rw_count /trunc32; exact Hcnt).
    rewrite Hc2.
    iDestruct (read_arms_file_learn_mapped i γo P cnt q cat_file nl r M'
                 (m !!! Regidx a1_idx) k g Hlin Himg Hcnt0 ltac:(lia) Hmap
                 with "Hcore") as "[Hpin Hlearn]".
    iApply ("Hcont" $! h' r g with "Hufdh Hpin Hlearn Hrun Hbuf").
  Qed.

End UkReadFile.
