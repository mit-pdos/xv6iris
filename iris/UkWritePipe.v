(* ===================================================================== *)
(* UkWritePipe.v -- THE PIPE ARM OF THE GENERIC WRITE LEAF.               *)
(*                                                                        *)
(* [UkReadPipe.v]'s twin one syscall over, and the byte queue changed both *)
(* the same way (design/pipe.md, "The byte queue").  The first version of  *)
(* this file recorded two things as owed -- “the bytes the writer pushed   *)
(* are the reader's next bytes” and row 16's missing return blanket -- and *)
(* the first of them is now paid in full:                                  *)
(*                                                                        *)
(*  - THE PAYMENT IS THE WRITE CHAIN.  [SpecFilewrite.filewrite_in] at     *)
(*    [FdOpen _ true (FdPipe γp)] is [PipeQueue.pipe_wpay]: one write link *)
(*    per byte of the caller's run, at its own PREFIX CURSOR [Q], with the *)
(*    byte pinned to the image the call runs at, and an OBSERVATION [Qe]   *)
(*    fired where the loop stops because the read end is shut -- or the    *)
(*    taint.  The image is bound by the trapping key, so the chain enters  *)
(*    as a WAND OVER THE HEAP the deposit lends, exactly as the console    *)
(*    member's output chain does ([UkWriteCons]).                          *)
(*  - AND THE POST TELLS SOMETHING.  [filewrite_extra]'s pipe arm is       *)
(*    [PipeQueue.pipe_wpost]: the chain at the STOP CURSOR [k], and the    *)
(*    answer with its reason -- [k] itself (the whole request, or copyin's *)
(*    fault at byte [k]), or -1 with the shut read end observed at node    *)
(*    [k], or -1 by kill.  A caller that paid links reads the count off    *)
(*    its own post; a caller that paid the TAINT reads row 16's RETURN     *)
(*    BLANKET (lane NIL-RET: [UexecExecInst.xv6_spost]'s 16 arm carries    *)
(*    [SpecFilewrite.filewrite_ret], as row 5 carries read's), which the   *)
(*    members hand over in the program's own reading -- the answer is -1  *)
(*    or a count no larger than the request.                              *)
(*                                                                        *)
(* WHAT IS STILL OWED: nothing at this tier.                               *)
(*                                                                        *)
(* AND WHO A PIPE WRITER IS.  Holding a pipe row costs a process its       *)
(* [UkRun.urun_nopipe] pure arm, so as the tree stands every pipe writer   *)
(* is TAINTED and pays its own tear-down's closes out of the credential    *)
(* ([UkReadPipe.wp_uk_pipe_read_end]'s premise, whose comment has the      *)
(* detail).  design/app-pipe.md SS2 rules that out for an application: the *)
(* pipe's fragment goes into a PER-PIPE INVARIANT and the run carries the  *)
(* invariant's persistent handle, one registration per pipe row, so a      *)
(* verified program holds a pipe without the credential and the taint      *)
(* survives only as one intro lemma.  Lane PIPE-REG lands it; NOTHING IN   *)
(* THIS FILE moves when it does -- the payments here ([pipe_wpay]) and the  *)
(* exit row are different rows, and a caller that pays links never named   *)
(* the credential.                                                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
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
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkReadRows.         (* [udepwf_st] / [ufd_key_agree] *)
Require Import UkWriteLeaf.        (* row 16's family and its two key rows *)
Require Import SpecFilewrite.      (* [filewrite_in] / [filewrite_extra] *)
Require Import SpecSysRead.        (* [sys_rw_count] -- the count the key carries *)
Require Import PipeNames.          (* [pipe_names] / [pipe_st] *)
Require Import PipeQueue.          (* [pipe_wpay] / [pipe_wpost] *)
Require Import ChildTok.           (* [kill_shot] -- the -1-by-kill arm *)
Require Import UserPtTree.         (* [uptd] -- what the post is stated at *)
Require Import UserPerm.           (* [uperm] -- the key's permission map *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkWritePipe.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* Row 16 reads TWO family fields at a pipe descriptor now (design/
     pipe.md, "The byte queue"): [wf_Q], the caller's PREFIX CURSOR over
     the bytes it pushed, and [wf_Qe], its observation at a stop on a shut
     read end.  Everything else is [UkWriteLeaf.xfam_wr] at the trivial
     readings. *)
  Definition write_pipe_fam (Q : nat -> iProp Σ)
      (Qe : nat -> pipe_st -> iProp Σ) (Xp : Z -> iProp Σ) : sfam :=
    let f0 := xfam_wr Q Xp in
    {| xf_P      := xf_P f0;
       xf_Pmiss  := xf_Pmiss f0;
       xf_Fo     := xf_Fo f0;
       xf_Rs     := xf_Rs f0;
       rf_F      := rf_F f0;
       cf_P      := cf_P f0;
       cf_Pmiss  := cf_Pmiss f0;
       cf_Fo     := cf_Fo f0;
       of_P      := of_P f0;
       of_Pmiss  := of_Pmiss f0;
       of_Farm   := of_Farm f0;
       of_Fun    := of_Fun f0;
       of_Fok    := of_Fok f0;
       of_Fex    := of_Fex f0;
       of_Fo     := of_Fo f0;
       of_Ft     := of_Ft f0;
       of_om    := OffParked;
       wf_Q      := wf_Q f0;
       nf_P      := nf_P f0;
       nf_Pmiss  := nf_Pmiss f0;
       nf_Farm   := nf_Farm f0;
       nf_Fun    := nf_Fun f0;
       nf_Fok    := nf_Fok f0;
       nf_Fex    := nf_Fex f0;
       uf_P      := uf_P f0;
       uf_Pmiss  := uf_Pmiss f0;
       uf_Fent   := uf_Fent f0;
       uf_Ftgt   := uf_Ftgt f0;
       uf_Fex    := uf_Fex f0;
       uf_Fmiss  := uf_Fmiss f0;
       lf_Ftgt   := lf_Ftgt f0;
       lf_Fent   := lf_Fent f0;
       lf_Funt   := lf_Funt f0;
       df_P      := df_P f0;
       df_Pmiss  := df_Pmiss f0;
       df_Farm   := df_Farm f0;
       df_Fdots  := df_Fdots f0;
       df_Fun    := df_Fun f0;
       df_Fok    := df_Fok f0;
       df_Fex    := df_Fex f0;
       kf_pay    := kf_pay f0;
       kf_lend   := kf_lend f0;
       kf_xpay   := kf_xpay f0;
       rf_ret    := rf_ret f0;
       rf_in     := rf_in f0;
       rf_pq     := rf_pq f0;
       rf_pqe    := rf_pqe f0;
       wf_Qe     := Qe;
       cl_P      := cl_P f0 |}.

  (* =================================================================== *)
  (*  2.  THE DEPOSIT'S SUPPLIER: THE PIPE'S REAL PAYMENT                  *)
  (* =================================================================== *)
  (* [SpecFilewrite.filewrite_in] at [FdOpen _ true (FdPipe γp)] is
     [PipeQueue.pipe_wpay]: one write link per byte of the caller's run, at
     its own cursor and with the byte pinned to the image the call runs at
     -- or the taint.  The image is bound by [udepwf_st]'s own forall, so
     the chain enters as a WAND OVER THE HEAP the deposit lends, exactly as
     the console member's output chain does
     ([UkWriteCons.wp_uk_ecall_write_cons]). *)
  Lemma udepwf_st_write_pipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (rb : bool) (γp : pipe_names) (Q : nat -> iProp Σ)
      (Qe : nat -> pipe_st -> iProp Σ) (nb : nat) :
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       pipe_wpay (pn_queue γp) M (m !!! Regidx a1_idx) Q Qe nb) -∗
    udepwf_st N m pc 16 (write_pipe_fam Q Qe (ukn_pay N))
      (FdOpen rb true (FdPipe γp)).
  Proof using .
    intros Hcnt. iIntros "Hch".
    rewrite /udepwf_st. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "[Hheap Hpay]".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_pipe_fam Q Qe (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite Hkey. rewrite /filewrite_in /= Hcnt Nat2Z.id. iExact "Hpay".
  Qed.

  (* ...AND THE POST'S PIPE ARM, at a state the walk holds through an
     equation.  [SpecFilewrite.filewrite_extra_pipe] is the introduction;
     this is the elimination, and it is the match at one constructor. *)
  Lemma uwrite_pipe_extra (gn : gname) (Pt : uptd) (st : fdstate) (rb : bool)
      (γp : pipe_names) (n : Z) (Mv : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) (r : mword 64) :
    st = FdOpen rb true (FdPipe γp) ->
    filewrite_extra gn Pt st n Mv ua Q Qe r -∗
    pipe_wpost Pt (pn_queue γp) Mv ua Q Qe (ChildTok.kill_shot gn ∗ app_taint)%I
      (Z.to_nat n) r.
  Proof using . intros ->. by iIntros "$". Qed.

  (* =================================================================== *)
  (*  3.  THE MEMBER                                                      *)
  (* =================================================================== *)
  (* [UkRunSys.wp_uk_ecall_write_at]'s walk at the pipe handle, taken
     DIRECTLY rather than through [UkWriteFile.wp_uk_ecall_write_file] for
     [UkReadPipe]'s reason: a pipe end is a descriptor a program was GIVEN
     by [sys_pipe] rather than one any ledger can reach, so the reading is
     the handle's ([UkReadRows.ufd_key_agree]).

     WHAT COMES BACK is the handle, the source run, and -- unlike before --
     THE PIPE'S OWN POST: the chain at the stop cursor [k], the answer's
     reason (the whole request, copyin's fault, the read end observed shut,
     or the writer's kill shot), or the taint with the payment back --
     and, in front of it, row 16's blanket in the program's reading: [r]
     is -1 or a count no larger than [nb] (lane NIL-RET), which is what a
     caller that paid the taint learns.  At a caller that paid links the
     post says everything: [k] IS the count on the two non-negative
     arms.  The image [Mv] and the page-table view [Pt] the post is stated
     at are bound by the trapping key, so they come out under the
     continuation's own binders, with the row that says the caller's own
     bytes are what the chain's nodes were pinned to. *)
  Lemma wp_uk_ecall_write_pipe (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fd : nat) (rb : bool)
      (dq : dfrac) (nb : nat) (f : nat -> bv 8) (γp : pipe_names)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    (* THE COUNT THE CALLER ASKED FOR IS THE RUN IT OWNS *)
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE *)
    UserFd.ufd (ukn_fd N) fd (FdOpen rb true (FdPipe γp)) -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (* ...AND THE PAYMENT: the caller's write chain over the byte queue at
       the image the call runs at, or the taint *)
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       pipe_wpay (pn_queue γp) M (m !!! Regidx a1_idx) Q Qe nb) -∗
    (∀ (h' : CpuId) (r : mword 64) (Pt : uptd) (Mv : gmap Z (bv 8))
       (Rk : iProp Σ),
       (* WHAT IT ANSWERED, off row 16's blanket (lane NIL-RET): -1, or a
          count no larger than the one asked for *)
       ⌜bv_signed r = -1 \/ (0 <= bv_signed r <= Z.of_nat nb)%Z⌝ -∗
       (* the chain's nodes were pinned to the caller's OWN bytes *)
       ⌜ forall j : nat, (j < nb)%nat ->
           Mv !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (f j) ⌝ -∗
       pipe_wpost Pt (pn_queue γp) Mv (m !!! Regidx a1_idx) Q Qe Rk nb r -∗
       UserFd.ufd (ukn_fd N) fd (FdOpen rb true (FdPipe γp)) -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hfdv Hfdlt Hcnt Hal4.
    iIntros "#Hi Hrun Hufdh Hbuf Hch Hcont".
    iPoseProof (udepwf_st_write_pipe N m pc rb γp Q Qe nb Hcnt with "Hch")
      as "Hsb".
    iApply (wp_uk_ecall_write_at N h m pc avail
              (write_pipe_fam Q Qe (ukn_pay N))
              (UserFd.ufd (ukn_fd N) fd (FdOpen rb true (FdPipe γp)))
              (ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f)
              (fun fdv => fd_st_of_key (m !!! Regidx a0_idx) fdv
                          = FdOpen rb true (FdPipe γp))
              nb f Hn Hal4
              (ufd_key_agree N fd (FdOpen rb true (FdPipe γp))
                 (m !!! Regidx a0_idx) Hfdv Hfdlt)
              (fun M pmv sz =>
                 usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                   (m !!! Regidx a1_idx) nb f)
              with "Hi Hrun [Hsb] Hufdh Hbuf").
    { rewrite /udepwf_st /udepwf_K. iExact "Hsb". }
    iIntros (h' r W cw' cs')
      "%Hk0 %Hk1 %Hk2 %Hkey %Hlz %Hsrc Hufdh Hbuf Hpost Hrun".
    iDestruct (spost_at_write_elim_at uslot (write_pipe_fam Q Qe (ukn_pay N)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                 r (uvis_M W) (uvis_fd W) cw' cs'
                 Hk0 Hk1 Hk2 eq_refl eq_refl with "Hpost")
      as "(%Hfwret & %Pt & %Hpmp & %Hwfp & %Hlzp & Hextra)".
    iDestruct (uwrite_pipe_extra (uvis_gen W) Pt
                 (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) rb γp
                 (sys_rw_count (m !!! Regidx a2_idx)) (uvis_M W)
                 (m !!! Regidx a1_idx) Q Qe r Hkey with "Hextra") as "Hwp".
    rewrite Hcnt Nat2Z.id.
    iApply ("Hcont" $! h' r Pt (uvis_M W) ((ChildTok.kill_shot (uvis_gen W) ∗ app_taint)%I)
              with "[%] [%] Hwp Hufdh Hbuf Hrun").
    { (* the blanket, at the count the caller named; a 32-bit count is
         below the sign boundary *)
      rewrite Hcnt in Hfwret. apply (filewrite_ret_nat nb r); [ | exact Hfwret ].
      pose proof (sys_rw_count_lt (m !!! Regidx a2_idx)) as Hlt31. rewrite Hcnt in Hlt31.
      assert (E : (2 ^ 31 < 2 ^ 63)%Z) by (vm_compute; reflexivity). lia. }
    (* the source row's first component: the chain's nodes were pinned to
       the caller's own bytes, which is exactly [usrc_ok]'s reading, and
       the walk already states it at the caller's own [a1] *)
    exact (proj1 Hsrc).
  Qed.

  (* ...AND AT THE STATE [sys_pipe] ACTUALLY HANDS BACK.  RD-5's
     [UkReadPipe.wp_uk_pipe_read_end] reads the pipe leaf's post one step
     into the two members' own premises and gives out
     [ufd a (FdOpen true false (FdPipe γp))] and
     [ufd b (FdOpen false true (FdPipe γp))] beside the byte queue's exact
     fragment; this is the second of those at the write member's premise,
     which is the join the brief asked to be checked rather than assumed. *)
  Lemma wp_uk_pipe_write_end (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fd : nat)
      (dq : dfrac) (nb : nat) (f : nat -> bv 8) (γp : pipe_names)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen false true (FdPipe γp)) -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       pipe_wpay (pn_queue γp) M (m !!! Regidx a1_idx) Q Qe nb) -∗
    (∀ (h' : CpuId) (r : mword 64) (Pt : uptd) (Mv : gmap Z (bv 8))
       (Rk : iProp Σ),
       (* WHAT IT ANSWERED, off row 16's blanket (lane NIL-RET): -1, or a
          count no larger than the one asked for *)
       ⌜bv_signed r = -1 \/ (0 <= bv_signed r <= Z.of_nat nb)%Z⌝ -∗
       ⌜ forall j : nat, (j < nb)%nat ->
           Mv !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (f j) ⌝ -∗
       pipe_wpost Pt (pn_queue γp) Mv (m !!! Regidx a1_idx) Q Qe Rk nb r -∗
       UserFd.ufd (ukn_fd N) fd (FdOpen false true (FdPipe γp)) -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hfdv Hfdlt Hcnt Hal4.
    iIntros "#Hi Hrun Hufdh Hbuf Hch Hcont".
    iApply (wp_uk_ecall_write_pipe N h m pc avail fd false dq nb f γp Q Qe
              Hn Hfdv Hfdlt Hcnt Hal4 with "Hi Hrun Hufdh Hbuf Hch Hcont").
  Qed.


  (* =================================================================== *)
  (*  4.  THE LEDGER SLOT (design/app-pipe.md SS5.4; lane PIPE-STD)        *)
  (*                                                                      *)
  (*  echo writes fd 1 and cat reads fd 0, and both are BELOW [NSTD]:      *)
  (*  their descriptor knowledge is the whole LEDGER ([UserFd.ustd]) and   *)
  (*  their deposit is fixed at it ([UkRun.udepwf_std]), while section 3's *)
  (*  member is handle-fixed ([UserFd.ufd] carries [NSTD <= fd]).  These   *)
  (*  two are that member's ledger twins and nothing else: same walk, same *)
  (*  family, same payment, same post -- only the descriptor knowledge and *)
  (*  the deposit's reading change.  The mould is upstream's file leaf     *)
  (*  ([UkWriteFile.udepwf_std_write_file] / [wp_uk_ecall_write_std]).     *)
  (*                                                                      *)
  (*  THE SLOT IS NOT PINNED AT 1.  The file twin fixes [a0 = 1] because   *)
  (*  echo is its only caller; there is no reason for it -- the ledger      *)
  (*  reading is uniform in the slot ([UkReadRows.std_fd_st_of_key]) --     *)
  (*  and the pipe application needs slot 1 (echo's write end) and slot 0   *)
  (*  (cat's read end) out of one statement each.  So both leaves take the  *)
  (*  slot as a parameter with [fd < NSTD] and the ledger's row at it.      *)
  (*                                                                      *)
  (*  THERE IS NO OFFSET MODE TO LEAVE FREE.  The file twin's statement     *)
  (*  quantifies the state's [offmode] because [FdInode] carries one and    *)
  (*  [SpecFilewrite.filewrite_in]'s inode arm is blind to it; a PIPE row    *)
  (*  is [FdOpen rb true (FdPipe γp)] and has no offset field at all, so     *)
  (*  the corresponding freedom here is the READ flag [rb] -- which end's    *)
  (*  descriptor this is says nothing about whether it may also be read      *)
  (*  from, and [pipe_wpay] does not look.                                   *)
  (* =================================================================== *)

  (* THE DEPOSIT AT A LEDGER SLOT, [udepwf_st_write_pipe]'s twin: the chain
     still enters as a wand over the heap the deposit lends, and the arm is
     computed from the caller's own ledger rather than from a handle. *)
  Lemma udepwf_std_write_pipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (l : list fdstate) (fd : nat) (rb : bool) (γp : pipe_names)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) (nb : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe γp)) ->
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       pipe_wpay (pn_queue γp) M (m !!! Regidx a1_idx) Q Qe nb) -∗
    udepwf_std N m pc 16 (write_pipe_fam Q Qe (ukn_pay N)) l.
  Proof using .
    intros H0 Hlt Hl Hcnt. iIntros "Hch".
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake _ Hheap Hufd".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "[Hheap Hpay]".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_pipe_fam Q Qe (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite (std_fd_st_of_key (m !!! Regidx a0_idx) fdv l fd
               (FdOpen rb true (FdPipe γp)) H0 Hlt Htake Hl).
    rewrite /filewrite_in /= Hcnt Nat2Z.id. iExact "Hpay".
  Qed.

  (* THE LEDGER-SLOT PIPE WRITE LEAF, [wp_uk_ecall_write_pipe]'s twin.  The
     one write walk at [K fdv := take NSTD fdv = l] with [UserFd.ustd] for
     [UserFd.ufd] and [UkRun.udepwf_std] for [udepwf_st]
     ([UserFd.ustd_agree] is the reading); EVERYTHING ELSE IS THE HANDLE
     LEAF'S -- the same [pipe_wpay] goes in, the same [pipe_wpost] and the
     same source-image row come back, and the ledger comes home unmoved
     (16 moves no descriptor). *)
  Lemma wp_uk_ecall_write_pipe_std (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (l : list fdstate) (fd : nat) (rb : bool)
      (dq : dfrac) (nb : nat) (f : nat -> bv 8) (γp : pipe_names)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (* THE DESCRIPTOR IS A LEDGER SLOT, and the ledger says it is this
       pipe's WRITE end *)
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe γp)) ->
    (* THE COUNT THE CALLER ASKED FOR IS THE RUN IT OWNS *)
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE LEDGER, in place of the handle-fixed leaf's [UserFd.ufd] *)
    UserFd.ustd (ukn_fd N) l -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (* ...AND THE PAYMENT: the caller's write chain over the byte queue at
       the image the call runs at, or the taint *)
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       pipe_wpay (pn_queue γp) M (m !!! Regidx a1_idx) Q Qe nb) -∗
    (∀ (h' : CpuId) (r : mword 64) (Pt : uptd) (Mv : gmap Z (bv 8))
       (Rk : iProp Σ),
       (* WHAT IT ANSWERED, off row 16's blanket (lane NIL-RET): -1, or a
          count no larger than the one asked for *)
       ⌜bv_signed r = -1 \/ (0 <= bv_signed r <= Z.of_nat nb)%Z⌝ -∗
       (* the chain's nodes were pinned to the caller's OWN bytes *)
       ⌜ forall j : nat, (j < nb)%nat ->
           Mv !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))
           = Some (f j) ⌝ -∗
       pipe_wpost Pt (pn_queue γp) Mv (m !!! Regidx a1_idx) Q Qe Rk nb r -∗
       UserFd.ustd (ukn_fd N) l -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn H0 Hlt Hl Hcnt Hal4.
    iIntros "#Hi Hrun Hstd Hbuf Hch Hcont".
    iPoseProof (udepwf_std_write_pipe N m pc l fd rb γp Q Qe nb
                  H0 Hlt Hl Hcnt with "Hch") as "Hsb".
    iApply (wp_uk_ecall_write_at N h m pc avail
              (write_pipe_fam Q Qe (ukn_pay N))
              (UserFd.ustd (ukn_fd N) l)
              (ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f)
              (fun fdv => take NSTD fdv = l)
              nb f Hn Hal4
              (fun fdv => ustd_agree (ukn_fd N) fdv l)
              (fun M pmv sz =>
                 usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                   (m !!! Regidx a1_idx) nb f)
              with "Hi Hrun [Hsb] Hstd Hbuf").
    { iApply (udepwf_K_std N m pc 16 (write_pipe_fam Q Qe (ukn_pay N)) l
                with "Hsb"). }
    iIntros (h' r W cw' cs')
      "%Hk0 %Hk1 %Hk2 %Htake %Hlz %Hsrc Hstd Hbuf Hpost Hrun".
    iDestruct (spost_at_write_elim_at uslot (write_pipe_fam Q Qe (ukn_pay N)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                 r (uvis_M W) (uvis_fd W) cw' cs'
                 Hk0 Hk1 Hk2 eq_refl eq_refl with "Hpost")
      as "(%Hfwret & %Pt & %Hpmp & %Hwfp & %Hlzp & Hextra)".
    (* THE ARM, OUT OF THE CALLER'S OWN LEDGER: the key's low [NSTD] slots
       ARE the ledger ([Htake], the walk's row), so the row at [fd] is the
       state the call ran on. *)
    iDestruct (uwrite_pipe_extra (uvis_gen W) Pt
                 (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) rb γp
                 (sys_rw_count (m !!! Regidx a2_idx)) (uvis_M W)
                 (m !!! Regidx a1_idx) Q Qe r
                 (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l fd
                    (FdOpen rb true (FdPipe γp)) H0 Hlt Htake Hl)
                 with "Hextra") as "Hwp".
    rewrite Hcnt Nat2Z.id.
    iApply ("Hcont" $! h' r Pt (uvis_M W) ((ChildTok.kill_shot (uvis_gen W) ∗ app_taint)%I)
              with "[%] [%] Hwp Hstd Hbuf Hrun").
    { rewrite Hcnt in Hfwret. apply (filewrite_ret_nat nb r); [ | exact Hfwret ].
      pose proof (sys_rw_count_lt (m !!! Regidx a2_idx)) as Hlt31. rewrite Hcnt in Hlt31.
      assert (E : (2 ^ 31 < 2 ^ 63)%Z) by (vm_compute; reflexivity). lia. }
    exact (proj1 Hsrc).
  Qed.

End UkWritePipe.
