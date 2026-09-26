(* ===================================================================== *)
(* UkCat.v -- the `cat` program's SYSCALL STUB layer.                      *)
(*                                                                        *)
(* usys.S's three-instruction bodies: the number into a7, [ecall],         *)
(* return.  Five of them, and the row each takes is the whole of what      *)
(* distinguishes them:                                                    *)
(*                                                                        *)
(*   open, close, write   the QUIET row -- none of the three writes a user *)
(*                        byte, so the heap comes back as it went in.      *)
(*                        write READS the buffer, but the row does not     *)
(*                        make the caller own it: nothing the kernel does  *)
(*                        to its own copy is visible here.                 *)
(*   exit                 the arm with no continuation                     *)
(*   read                 THE ONE THAT WRITES.  The caller hands in the    *)
(*                        whole count as a run it owns and gets the whole  *)
(*                        count back at SOME contents; see                 *)
(*                        [UkRunSys.wp_uk_ecall_read] for why owning less  *)
(*                        would not do.                                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith.
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UCodeCat.
Require Import CtxIdDefs.
Require User.CatSyms User.CatInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Local Open Scope Z_scope.
Import Defs.

Require Import FdSlots.   (* [fdstate]/[fdtype] -- what a handle names *)
Require Import ProcGeom.  (* [NOFILE] -- how many slots a table has *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UexecSlot UexecRet.  (* [uslot] / [spost_at] / [sfam] *)
Require Import UserPerm.    (* [perm_of] / [lazy_free] *)
Require Import ProcPtOwn.   (* [proc_pt_wf] *)
Require Import UserPtTree.  (* [uva_rmapped] *)

Section UkCat.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THE PROGRAM'S PAYLOAD, as a section hypothesis: the entry constructor
     is what fixes it ([UkRun.uslot_of_urun*] mint the record at the
     payload the kernel handed them).  A SECTION hypothesis rather than a
     premise on the exit stub, so that every lemma between the entry and
     the ecall is generalized over it automatically.

     STATUS-INDEPENDENT AND NOT TRIVIAL (lane CAT-WALK, W2).  It used to
     be [UkRun.ukn_triv] -- [ukn_pay N = fun _ => True] -- and that is the
     whole reason cat could not be entered at the file application: an
     entry constructor mints the record at [ukn_pay N = Q]
     ([UkRun.uslot_of_urun_ro]), so a walk carrying [ukn_triv] forces
     [Q = fun _ => True] and cat's exit can hand the shell NOTHING.  What
     the walk actually needs is only that cat's two exits -- 0 on the
     content arm, 1 on the diagnostic arm -- owe the same thing, which is
     [UkRun.ukn_const]. *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  (* THE DEPOSITS cat OWES (lane SUPPLY-SPLIT, P4): read(5), open(15) and
     write(16), the three CLAIM numbers it calls.  cat is in no theorem --
     nothing outside [UkCat*.v] requires this file -- so nobody discharges
     these yet; naming them is what keeps cat off the generic supplier
     ([AppInv.app_sup], the taint) along with init, sh and echo. *)
  (* ...AND close(21) IS NOT IN THE LIST (survey R4, lane SUP-ONE).  A
     pipe descriptor's close steps the pipe's exact ghost state, so 21
     left [UexecSG.free_num] and cat used to name a deposit for it -- on
     the reading that "the TYPE [UsysMemOk.usys_fd_ok]'s open row returns
     is existential".  The row pins [FdSlots.fdst_nopipe] and the open
     leaves EXPORT it now, so cat closes the descriptor its own [open]
     returned on the FREE route ([UkRun.udepw_cl_nopipe]) and owes
     nothing.  That matters beyond tidiness: the only producer of
     [udepw_law 21] at a claim-bearing instance is the taint
     ([UexecExecMint.udepw_law_of_sup_close]), so naming it here forced a
     TAINTED entry on a verified cat. *)
  Definition cat_deps : iProp Σ :=
    (udepw_law 5 ∗ udepw_law 15 ∗ udepw_law 16)%I.

  Global Instance cat_deps_persistent : Persistent cat_deps.
  Proof using . rewrite /cat_deps. apply _. Qed.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).


  (* CAT OPENS ABOVE ITS STANDARD STREAMS, and the ledger is what says so.
     [fdalloc] returns the LOWEST free descriptor, so "the open returns a
     descriptor cat may close" is a fact about slots 0..2 -- cat is exec'd
     with all three open (its own [fprintf(2, ...)] assumes as much) and
     therefore never opens onto one.  The ledger goes in and comes straight
     back: cat's open does not touch it, and neither does its close. *)
  (* ...AT THE ONE LAW IT SPENDS (lane CAT-WALK, W1). *)
  Lemma wp_kcat_open (h : CpuId) (m : regfile) (l : list fdstate)
      (avail : nat) :
    fd_lowest_closed l = None ->
    udepw_law 15 -∗
    cat_code γt -∗
    urun N h m (mword_of_int CatSyms.open) avail -∗
    ustd γfd l -∗
    (∀ (h' : CpuId) (ret : mword 64),
       (* THE HANDLE FOR WHAT WAS OPENED, forwarded rather than dropped --
          it is what cat's own [close] will spend. *)
       ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
           ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat
            (* ...AND IT IS NOT A PIPE (survey R4), forwarded from
               [UkRunSys.wp_uk_ecall_open]: cat's own close is FREE at
               this fact ([UkRun.udepw_cl_nopipe]), which is why 21 is
               not in [cat_deps]. *)
            /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
           ufd γfd fd (FdOpen rd wr t))
        ∨ ⌜ret = (mword_of_int (-1) : mword 64)⌝) -∗
       ustd γfd l -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hnone. iIntros "#Hdp #Hcode Hrun Hstd Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwrite & Hopen & Hclose & _).
    rewrite Hopen.
    (* ---- 0x3ec  c.li a7,15 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ec)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3ec with "Hcode"). }
    assert (E0open : add_vec_int (mword_of_int 0x3ec : mword 64) 2
                   = mword_of_int 0x3ee)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emopen : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 15 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0open Emopen.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    (* ---- 0x3ee  ecall -- the QUIET row ---- *)
    (* open moves the table: the dedicated leaf, whose handle cat does not
       yet carry *)
    iApply (wp_uk_ecall_open N h1 m1 (mword_of_int 0x3ee) l avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd").
    { iApply (uis_cat_3ee with "Hcode"). }
    (* THE FLAGGED DEPOSIT: open(15) (P4) *)
    { iApply (udepw_of_law N m1 (mword_of_int 0x3ee) 15 with "Hdp"). }
    assert (E1open : add_vec_int (mword_of_int 0x3ee : mword 64) 4
                   = mword_of_int 0x3f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1open.
    iIntros (h2 ret) "Hal Hrun".
    (* the allocation landed ABOVE the standard streams, because none of them
       is closed -- so it is a handle, and the ledger did not move *)
    iAssert (((∃ (fd : nat) (rd wr : bool) (t : fdtype),
                 ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
                  /\ (fd < NOFILE)%nat
                  /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
                 ufd γfd fd (FdOpen rd wr t))
              ∨ ⌜ret = (mword_of_int (-1) : mword 64)⌝) ∗ ustd γfd l)%I
      with "[Hal]" as "[Hfdh Hstd]".
    { iDestruct "Hal" as "[Hal | [%Hrm Hstd]]";
        [| iSplitR; [ by iRight | iExact "Hstd" ]].
      iDestruct "Hal" as (fd rd wr t) "[%Hr Hal]".
      iDestruct (ualloc_hi γfd l fd (FdOpen rd wr t) Hnone with "Hal")
        as "(_ & Hstd & Hh)".
      iFrame "Hstd". iLeft. iExists fd, rd, wr, t. iFrame "Hh".
      iPureIntro. exact Hr. }
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f2  c.jr ra ---- *)
    assert (Hraopen : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraopen; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3f2 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hfdh Hstd Hrun").
  Qed.

  (* close SPENDS THE HANDLE cat's own open produced.  The premise says the
     descriptor in a0 IS the one the handle is for -- read as [argfd] reads
     it -- which is what the caller establishes from open's own return
     equation. *)
  (* THE CLOSE ROW, ABSTRACTLY (lane CAT-WALK, W1/W3).  design/pipe.md
     makes close(21) a claim number: a pipe descriptor's last close steps
     the pipe's ghost state.  Whether cat's row is free is a fact about
     the TYPE its own open returned, and the two arms differ:
     [wp_kcat_open]'s U-tier row and [UkFileOpen.wp_uk_ecall_open_read_
     deed]'s BOTH say the descriptor is not a pipe now (survey R4: the
     free leaf exports [FdSlots.fdst_nopipe], the deed leaf hands back
     [FdInode i γo OffParked]), so both arms take the FREE route and
     [kcat_cldep_nopipe] is the only instance left.  [kcat_cldep_of_law]
     -- the flagged deposit at 21, whose only claim-bearing producer is
     the taint -- is GONE with it, and so is [udepw_law 21] from
     [cat_deps]. *)
  Definition kcat_cldep (st : fdstate) : iProp Σ :=
    (□ ∀ (m : regfile) (pc : mword 64), udepw_cl N m pc st)%I.

  (* AT THE SHAPE THE OPEN LEAVES EXPORT (survey R4, lane SUP-ONE).  ONE
     instance, not two: the ∀-form ([UkRun.udepw_cl_nonpipe]) and
     [FdSlots.fdst_nopipe] say the same thing, and the fact travels in the
     latter's spelling. *)
  Lemma kcat_cldep_nopipe (st : fdstate) :
    fdst_nopipe st -> ⊢ kcat_cldep st.
  Proof using .
    intros Hnp. iIntros "!>" (m pc).
    iApply (udepw_cl_nopipe N m pc st Hnp).
  Qed.

  Lemma wp_kcat_close (h : CpuId) (m : regfile) (fd : nat) (st : fdstate)
      (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    kcat_cldep st -∗
    cat_code γt -∗
    urun N h m (mword_of_int CatSyms.close) avail -∗
    ufd γfd fd st -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Harg. iIntros "#Hdp #Hcode Hrun Hfdh Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwrite & Hopen & Hclose & _).
    rewrite Hclose.
    (* ---- 0x3d4  c.li a7,21 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3d4)
              (mword_of_int 21 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3d4 with "Hcode"). }
    assert (E0close : add_vec_int (mword_of_int 0x3d4 : mword 64) 2
                   = mword_of_int 0x3d6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emclose : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 21 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0close Emclose.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    (* ---- 0x3d6  ecall -- close, SPENDING the handle ---- *)
    iApply (wp_uk_ecall_close N h1 m1 (mword_of_int 0x3d6) fd st avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 21 : mword 64));
                    vm_compute; reflexivity)
              (* a0 is untouched by the [c.li a7,21] just executed *)
              ltac:(unfold m1;
                    rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                               (mword_of_int 21 : mword 64)
                               ltac:(vm_compute; discriminate));
                    exact Harg)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hfdh").
    { iApply (uis_cat_3d6 with "Hcode"). }
    { iApply "Hdp". }
    assert (E1close : add_vec_int (mword_of_int 0x3d6 : mword 64) 4
                   = mword_of_int 0x3da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1close.
    (* close of an OPEN descriptor returns 0; cat does not read it *)
    iIntros (h2 ret) "_ Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3da  c.jr ra ---- *)
    assert (Hraclose : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 21 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3da) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraclose; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3da with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* ...AT THE ONE LAW IT SPENDS (lane CAT-WALK, W1).  It used to take the
     whole of [cat_deps]; it only ever used the 16 conjunct, and narrowing
     it is what lets [kcat_w_of_law] below build the free instance of the
     per-call obligation out of the single law an entry constructor holds
     ([UEchoKernel.echo_uexec_slot]'s [udepw_law 16]) rather than out of a
     four-way bundle nothing at the file application can produce. *)
  Lemma wp_kcat_write (h : CpuId) (m : regfile) (avail : nat) :
    udepw_law 16 -∗
    cat_code γt -∗
    urun N h m (mword_of_int CatSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hdp #Hcode Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwrite & Hopen & Hclose & _).
    rewrite Hwrite.
    (* ---- 0x3cc  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3cc)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3cc with "Hcode"). }
    assert (E0write : add_vec_int (mword_of_int 0x3cc : mword 64) 2
                   = mword_of_int 0x3ce)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emwrite : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 16 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0write Emwrite.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x3ce  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet N h1 m1 (mword_of_int 0x3ce) 16 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              (* ...and the three descriptor-moving numbers, and chdir *)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate)
              (* ...and a number the full mask passes, not seccomp's *)
              ltac:(lia) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun []").
    { iApply (uis_cat_3ce with "Hcode"). }
    (* THE FLAGGED DEPOSIT: write(16) (P4) *)
    { iApply (udepw_of_law N m1 (mword_of_int 0x3ce) 16 with "Hdp"). }
    assert (E1write : add_vec_int (mword_of_int 0x3ce : mword 64) 4
                   = mword_of_int 0x3d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1write.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3d2  c.jr ra ---- *)
    assert (Hrawrite : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3d2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrawrite; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3d2 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.


  (* ===================================================================== *)
  (* THE CHAIN-PAYING WRITE (lane CAT-WALK, W1).                            *)
  (*                                                                       *)
  (* [wp_kcat_write] above pays row 16 out of [cat_deps]'s flagged deposit  *)
  (* ([UkRun.udepw_law] 16) and throws the post away.  That deposit is the  *)
  (* TAINT at the file application -- its one claim-bearing producer is     *)
  (* [UexecExecMint.udepw_law_of_sup_write], whose [app_sup] is what        *)
  (* [AppFile.file_taint_of_sup] burns -- so a cat entry that supplied it   *)
  (* would prove nothing about the wire.  This is the same three            *)
  (* instructions with the deposit taken at cat's OWN cursor family and the *)
  (* post handed back, so that the bytes of the file and the bytes of the   *)
  (* `cannot open` diagnostic can justify themselves.  It does NOT replace  *)
  (* [wp_kcat_write]: the two live side by side, exactly as                 *)
  (* [UkEcho.wp_kecho_write] and [UkEcho.wp_kecho_write_chain] do.          *)
  (*                                                                       *)
  (* [cat_deps] is not a premise here: a named deposit and a flagged one    *)
  (* are alternatives, not a pair, and this leaf takes the named one.       *)
  (*                                                                       *)
  (* THERE IS NO TEXT-HALF TWIN, and cat needs none: every byte cat writes  *)
  (* leaves WRITABLE memory it owns -- the read buffer [CatSyms.buf] on the *)
  (* content path and putc's own frame byte on the diagnostic path -- so    *)
  (* [UkRunSys.wp_uk_ecall_write_chain_buf]'s row answers both.  echo needs *)
  (* [wp_kecho_write_chain_txt] because it writes its .rodata separator     *)
  (* straight out of the text half; cat's ulib prints a literal ONE BYTE AT *)
  (* A TIME THROUGH THE STACK ([UkCatPutc]), so no literal is ever a write  *)
  (* argument.                                                             *)
  (* ===================================================================== *)
  Lemma wp_kcat_write_chain (h : CpuId) (m : regfile) (avail : nat)
      (fdep : sfam) (l : list fdstate)
      (dq : dfrac) (nb : nat) (fb : nat -> bv 8) :
    cat_code γt -∗
    urun N h m (mword_of_int CatSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int CatSyms.write : mword 64) 2) 16 fdep l -∗
    ustd γfd l -∗
    ubytesq γd dq (uint (m !!! Regidx a1_idx)) nb fb -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       ustd γfd l -∗
       ubytesq γd dq (uint (m !!! Regidx a1_idx)) nb fb -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hsb Hstd Hbuf Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwrite & _ & _ & _).
    rewrite Hwrite.
    (* ---- 0x3cc  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3cc)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3cc with "Hcode"). }
    assert (E0wc : add_vec_int (mword_of_int 0x3cc : mword 64) 2
                   = mword_of_int 0x3ce)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emwc : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 16 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0wc Emwc.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x3ce  ecall -- THE CHAIN-PAYING WRITE ---- *)
    assert (Ha1m1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                  (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)).
    rewrite <- Ha1m1.
    iApply (wp_uk_ecall_write_chain_buf N h1 m1 (mword_of_int 0x3ce) avail
              fdep l dq nb fb
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd Hbuf").
    { iApply (uis_cat_3ce with "Hcode"). }
    assert (E1wc : add_vec_int (mword_of_int 0x3ce : mword 64) 4
                   = mword_of_int 0x3d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1wc.
    iIntros (h2 ret W cw' cs')
      "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hnf Hstd Hbuf Hpost Hrun".
    rewrite Ha1m1.
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3d2  c.jr ra ---- *)
    assert (Hrawc : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3d2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrawc; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3d2 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret W cw' cs'
              with "[%] [%] [%] [%] [%] [%] Hstd Hbuf Hpost Hrun").
    { rewrite Ha0 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha1 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha2 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { exact Htk. }
    { exact Hlz. }
    { rewrite <- Ha1m1. exact Hnf. }
  Qed.

  (* ===================================================================== *)
  (* WHAT THE WALK SPENDS PER WRITE (lane CAT-WALK, W1).                    *)
  (*                                                                       *)
  (* [UkSh.ksh_w]'s shape verbatim, and per CALL rather than per byte for   *)
  (* the same reason: cat's content path is [write(1, buf, n)] with [n] the *)
  (* read's own return, while its diagnostic path is an [fprintf] whose     *)
  (* putc writes one byte at a time, so the obligation has to be statable   *)
  (* at any count.  THE DESCRIPTOR IS A PARAMETER, as sh's is and echo's is *)
  (* not: cat writes the file's bytes to fd 1 and its diagnostics to fd 2.  *)
  (*                                                                       *)
  (* It names nothing but the program tier's own vocabulary -- the three    *)
  (* argument registers, the run, [Ci], [Co].  The BYTES ARE NOT IN IT:     *)
  (* they ride in [Ci] and come back in [Co], which is what lets one shape  *)
  (* serve both the buffer the loop owns and the frame byte putc owns       *)
  (* ([kcat_wb] below is that instance).  The CONCRETE discharge -- the     *)
  (* console chain, the era's write link, the file claim's cursor -- is     *)
  (* proved above [UkWriteLeaf] and reaches this walk as a premise.         *)
  (* ===================================================================== *)
  Definition kcat_w (fdw ua : mword 64) (nb : nat) (Ci Co : iProp Σ)
    : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜m !!! Regidx a0_idx = fdw⌝ -∗
       ⌜m !!! Regidx a1_idx = ua⌝ -∗
       ⌜m !!! Regidx a2_idx = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
       cat_code γt -∗
       Ci -∗
       urun N h m (mword_of_int CatSyms.write) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          Co -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...AND THE FREE ONE: the flagged deposit pays row 16 and the post is
     thrown away, which is what every write of cat's did before this lane.
     This is the ONE place the free law enters the walk, and it is what
     makes the old (claim-free) statements of every lemma below
     corollaries at the free chain rather than separate proofs --
     [UEchoKernel.echo_uexec_slot]'s pattern. *)
  Lemma kcat_w_of_law (fdw ua : mword 64) (nb : nat) (Ci Co : iProp Σ) :
    (Ci ⊢ Co) -> udepw_law 16 -∗ kcat_w fdw ua nb Ci Co.
  Proof using .
    intros Hm. iIntros "#Hwr" (h m avail) "_ _ _ #Hcode HCi Hrun Hcont".
    iApply (wp_kcat_write h m avail with "Hwr Hcode Hrun").
    iIntros (h' ret) "Hrun".
    iApply ("Hcont" $! h' ret with "[HCi] Hrun"). by iApply Hm.
  Qed.

  (* ...and the output side is MONOTONE, which is what lets the LAST write
     of a chain hand its cursor straight to the exit's payload. *)
  Lemma kcat_w_mono (fdw ua : mword 64) (nb : nat) (Ci Co Co' : iProp Σ) :
    (Co -∗ Co') -∗ kcat_w fdw ua nb Ci Co -∗ kcat_w fdw ua nb Ci Co'.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode HCi Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "HCo Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HCo] Hrun").
    iApply ("Hm" with "HCo").
  Qed.

  (* ...and the INPUT side is anti-monotone, which is what lets a chain be
     re-cut at a point where the caller holds a stronger cursor. *)
  Lemma kcat_w_mono_in (fdw ua : mword 64) (nb : nat) (Ci Ci' Co : iProp Σ) :
    (Ci' -∗ Ci) -∗ kcat_w fdw ua nb Ci Co -∗ kcat_w fdw ua nb Ci' Co.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail
              with "[%] [%] [%] Hcode [Hm HCi] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iApply ("Hm" with "HCi").
  Qed.

  (* ...AND IT FRAMES: a caller that HOLDS the input half a payment asks
     for hands it over once and is left with the obligation at the rest.
     This is how the WRITTEN BYTES reach the payment -- the buffer is
     linear and the conversion is not, so the two travel separately and
     meet here. *)
  Lemma kcat_w_frame (fdw ua : mword 64) (nb : nat) (Ci Co C : iProp Σ) :
    C -∗ kcat_w fdw ua nb (Ci ∗ C) Co -∗ kcat_w fdw ua nb Ci Co.
  Proof using .
    iIntros "HC Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode [$HCi $HC] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 ].
  Qed.

  (* ===================================================================== *)
  (* ...AND THE SAME WRITE WITH ITS OUTPUT READ AT THE RETURNED WORD        *)
  (* (lane CAT-ENTRY-2, RULING (g)).                                        *)
  (*                                                                       *)
  (* [kcat_w]'s [Co] cannot mention the value [write] returned, and cat's   *)
  (* loop branches on exactly that: [beq a0,s1] compares the write's return *)
  (* against the read's.  While the payment says nothing about the return,  *)
  (* the `cat: write error` tail is an ARM the payer has to fund; once the  *)
  (* payment may SPEAK about the return, a payer whose destination run it   *)
  (* owns refutes the tail instead ([UkWriteLeaf.uwrite_no_short] --        *)
  (* READ-RELAY's move one syscall over).                                   *)
  (*                                                                       *)
  (* It is a SECOND definition and not a restatement of [kcat_w]: every     *)
  (* other write of the walk (putc's byte, every run of [kcat_pay_seq])     *)
  (* wants the ret-free shape, and a chain whose every node quantified a    *)
  (* return value it does not read would cost each of them an argument.     *)
  (* [kcat_wr_of_w] is the inclusion, so a caller with the ret-free         *)
  (* obligation still has this one.                                        *)
  (* ===================================================================== *)
  Definition kcat_wr (fdw ua : mword 64) (nb : nat) (Ci : iProp Σ)
      (Co : mword 64 -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜m !!! Regidx a0_idx = fdw⌝ -∗
       ⌜m !!! Regidx a1_idx = ua⌝ -∗
       ⌜m !!! Regidx a2_idx = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
       cat_code γt -∗
       Ci -∗
       urun N h m (mword_of_int CatSyms.write) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          Co ret -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* the ret-free obligation IS the constant instance of this one -- which
     is what lets the FREE chain keep funding cat's loop unchanged *)
  Lemma kcat_wr_of_w (fdw ua : mword 64) (nb : nat) (Ci Co : iProp Σ) :
    kcat_w fdw ua nb Ci Co -∗ kcat_wr fdw ua nb Ci (fun _ => Co).
  Proof using .
    iIntros "Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode HCi Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 ].
  Qed.

  Lemma kcat_wr_mono (fdw ua : mword 64) (nb : nat) (Ci : iProp Σ)
      (Co Co' : mword 64 -> iProp Σ) :
    (∀ r : mword 64, Co r -∗ Co' r) -∗
    kcat_wr fdw ua nb Ci Co -∗ kcat_wr fdw ua nb Ci Co'.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode HCi Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "HCo Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HCo] Hrun").
    iApply ("Hm" with "HCo").
  Qed.

  Lemma kcat_wr_mono_in (fdw ua : mword 64) (nb : nat) (Ci Ci' : iProp Σ)
      (Co : mword 64 -> iProp Σ) :
    (Ci' -∗ Ci) -∗ kcat_wr fdw ua nb Ci Co -∗ kcat_wr fdw ua nb Ci' Co.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail
              with "[%] [%] [%] Hcode [Hm HCi] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iApply ("Hm" with "HCi").
  Qed.

  Lemma kcat_wr_frame (fdw ua : mword 64) (nb : nat) (Ci C : iProp Σ)
      (Co : mword 64 -> iProp Σ) :
    C -∗ kcat_wr fdw ua nb (Ci ∗ C) Co -∗ kcat_wr fdw ua nb Ci Co.
  Proof using .
    iIntros "HC Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode [$HCi $HC] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 ].
  Qed.

  (* ===================================================================== *)
  (* ...AND THE ONE-BYTE FORM ulib's putc SPENDS.                           *)
  (*                                                                       *)
  (* putc's [write] argument is a byte in putc's OWN FRAME ([sb a1,-17(s0)] *)
  (* then [addi a1,s0,-17]), so the ADDRESS is not anything a caller can    *)
  (* name -- it is one frame below wherever the caller's sp happens to be.  *)
  (* The obligation is therefore quantified over it, and the byte's         *)
  (* OWNERSHIP travels with the payment: putc lends it in and takes it back *)
  (* ([kcat_w]'s [Ci]/[Co] carry it), which is exactly what the buffer      *)
  (* leaf underneath needs to refute the short arm                          *)
  (* ([UkRunSys.wp_uk_ecall_write_chain_buf]).  The BYTE VALUE is not       *)
  (* quantified: it is the low byte of the caller's a1, and naming it is    *)
  (* the whole point -- a payment that did not could not say which byte     *)
  (* the call filed.                                                       *)
  (* ===================================================================== *)
  Definition kcat_wb (fdw : mword 64) (b : bv 8) (Ci Co : iProp Σ) : iProp Σ :=
    (∀ ua : mword 64,
       kcat_w fdw ua 1%nat
         (Ci ∗ ubyte γd (uint ua) b) (Co ∗ ubyte γd (uint ua) b))%I.

  Lemma kcat_wb_of_law (fdw : mword 64) (b : bv 8) (Ci Co : iProp Σ) :
    (Ci ⊢ Co) -> udepw_law 16 -∗ kcat_wb fdw b Ci Co.
  Proof using .
    intros Hm. iIntros "#Hwr" (ua h m avail)
      "_ _ _ #Hcode [HCi Hb] Hrun Hcont".
    iApply (wp_kcat_write h m avail with "Hwr Hcode Hrun").
    iIntros (h' ret) "Hrun".
    iApply ("Hcont" $! h' ret with "[HCi $Hb] Hrun"). by iApply Hm.
  Qed.

  Lemma kcat_wb_mono (fdw : mword 64) (b : bv 8) (Ci Co Co' : iProp Σ) :
    (Co -∗ Co') -∗ kcat_wb fdw b Ci Co -∗ kcat_wb fdw b Ci Co'.
  Proof using .
    iIntros "Hm Hw" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! ua h m avail with "[%] [%] [%] Hcode HCi Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "[HCo Hb] Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HCo $Hb] Hrun").
    iApply ("Hm" with "HCo").
  Qed.

  Lemma kcat_wb_mono_in (fdw : mword 64) (b : bv 8) (Ci Ci' Co : iProp Σ) :
    (Ci' -∗ Ci) -∗ kcat_wb fdw b Ci Co -∗ kcat_wb fdw b Ci' Co.
  Proof using .
    iIntros "Hm Hw" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [HCi Hb] Hrun Hcont".
    iApply ("Hw" $! ua h m avail
              with "[%] [%] [%] Hcode [Hm HCi $Hb] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iApply ("Hm" with "HCi").
  Qed.

  Lemma kcat_wb_frame (fdw : mword 64) (b : bv 8) (Ci Co C : iProp Σ) :
    C -∗ kcat_wb fdw b (Ci ∗ C) Co -∗ kcat_wb fdw b Ci Co.
  Proof using .
    iIntros "HC Hw" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [HCi Hb] Hrun Hcont".
    iApply ("Hw" $! ua h m avail
              with "[%] [%] [%] Hcode [$HCi $HC $Hb] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 ].
  Qed.


  (* ...AND THE BYTE A CALLER PUTS IN a1.  Every putc call site loads the
     character as a full word whose value is the byte's, so this is the one
     step that reads it back, and it is what lets a caller state its
     payment at the CHARACTER rather than at the word. *)
  Lemma nth_byte0_moi (b : bv 8) :
    nth_byte (mword_of_int (bv_unsigned b) : mword 64) 0%nat = b.
  Proof using .
    pose proof (bv_unsigned_in_range 8 b) as Hr.
    assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite Em8 in Hr.
    assert (Hs : bv_unsigned (mword_of_int (bv_unsigned b) : mword 64)
                 = bv_unsigned b)
      by (apply moi_small; unfold Z64; clear -Hr; lia).
    apply bv_eq. rewrite nth_byte_unsigned.
    replace (Z.of_N (8 * N.of_nat 0)) with 0 by (vm_compute; reflexivity).
    rewrite Z.shiftr_0_r Hs.
    apply Z.mod_small. clear -Hr. lia.
  Qed.

  (* ...and a word IS its own signed reading put back, which is how a
     count the kernel returned reaches a syscall argument again. *)
  Lemma moi_of_sint (r : mword 64) :
    (mword_of_int (bv_signed r) : mword 64) = r.
  Proof using .
    apply bv_eq. rewrite moi64_unsigned.
    change (bv_signed r) with (bv_swrap 64 (bv_unsigned r)).
    unfold bv_swrap, bv_wrap.
    rewrite Zminus_mod_idemp_l.
    replace (bv_unsigned r + bv_half_modulus 64 - bv_half_modulus 64)
      with (bv_unsigned r) by lia.
    apply Z.mod_small. exact (bv_unsigned_in_range 64 r).
  Qed.

  (* ...and the same at a zero-extended byte, which is how a character
     LOADED from memory reaches a1 ([lbu] zero-extends). *)
  Lemma nth_byte0_zext (b : mword 8) :
    nth_byte (zero_extend' 64 b : mword 64) 0%nat = b.
  Proof using . rewrite zext8_moi. apply nth_byte0_moi. Qed.

  (* ===================================================================== *)
  (* A RUN OF BYTES THROUGH putc (lane CAT-WALK, W1).                       *)
  (*                                                                       *)
  (* [UkEcho.kecho_pay]'s shape at cat's output: [k] characters still to    *)
  (* print, starting at index [i] of [fb], recursive on the SAME [k]        *)
  (* ulib's vprintf loop inducts on, so the loop's invariant is the chain's *)
  (* tail and nothing has to be re-derived at the head.                     *)
  (*                                                                       *)
  (* THE BASE CASE IS A WAND AND NOT A WRITE, which echo's is not: echo's   *)
  (* chain always ends with the newline, while cat's ends wherever the      *)
  (* format string does -- and a run of length zero has to be satisfiable   *)
  (* because [%s] can splice an empty string in the middle of one.          *)
  (* ===================================================================== *)
  Fixpoint kcat_pay_seq (fdw : mword 64) (fb : nat -> bv 8) (i k : nat)
      (Ci Cend : iProp Σ) : iProp Σ :=
    match k with
    | O => (Ci -∗ Cend)%I
    | S k' => (∃ Cm : iProp Σ,
                 kcat_wb fdw (fb i) Ci Cm
                 ∗ kcat_pay_seq fdw fb (S i) k' Cm Cend)%I
    end.

  (* the free chain: every write paid from the flagged deposit, nothing
     carried.  [UEchoKernel.echo_uexec_slot]'s one instance at cat.

     THE EXIT PAYLOAD IS A PERSISTENT RESOURCE AND NOT A COQ ENTAILMENT
     (lane CAT-GEOM-4).  It used to be [(⊢ Cend)], which is satisfiable
     only at the TRIVIAL payload -- and that is what made this chain
     unusable to a payer whose payload is a CLAIM: at a tainted era cat's
     own output cursor is persistent (its right disjunct IS
     [AppFile.file_taint]) but it is a HYPOTHESIS, not derivable from
     nothing.  [□ Cend] is strictly weaker as a premise -- [⊢ P] gives
     [⊢ □ P] in an affine BI, because [□ emp ⊣⊢ emp] -- so every caller
     that had the old one still has this one, by [iModIntro]. *)
  Lemma kcat_pay_seq_of_law (fdw : mword 64) (fb : nat -> bv 8)
      (k : nat) (Cend : iProp Σ) :
    forall i : nat,
      □ Cend -∗ udepw_law 16 -∗ kcat_pay_seq fdw fb i k emp%I Cend.
  Proof using .
    induction k as [| k IH]; intros i; iIntros "#HC #Hwr".
    - iIntros "_". iExact "HC".
    - iExists emp%I. iSplitR.
      + iApply (kcat_wb_of_law _ _ _ _ ltac:(reflexivity) with "Hwr").
      + iApply (IH (S i) with "HC Hwr").
  Qed.

  (* the output side is MONOTONE, as one write's is *)
  Lemma kcat_pay_seq_mono (fdw : mword 64) (fb : nat -> bv 8) (k : nat) :
    forall (i : nat) (Ci Cend Cend' : iProp Σ),
      (Cend -∗ Cend') -∗
      kcat_pay_seq fdw fb i k Ci Cend -∗ kcat_pay_seq fdw fb i k Ci Cend'.
  Proof using .
    induction k as [| k IH]; intros i Ci Cend Cend'; iIntros "Hm Hc".
    - cbn [kcat_pay_seq]. iIntros "HCi".
      iApply "Hm". iApply ("Hc" with "HCi").
    - cbn [kcat_pay_seq]. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. iFrame "Hw". iApply (IH (S i) with "Hm Hc").
  Qed.

  (* ...AND IT FRAMES AT THE HEAD, which is how a caller holding the
     resource the first write wants hands it over once. *)
  Lemma kcat_pay_seq_frame (fdw : mword 64) (fb : nat -> bv 8) (k : nat)
      (i : nat) (Ci Cend C : iProp Σ) :
    C -∗ kcat_pay_seq fdw fb i k (Ci ∗ C) Cend -∗
    kcat_pay_seq fdw fb i k Ci Cend.
  Proof using .
    destruct k as [| k]; iIntros "HC Hc".
    - cbn [kcat_pay_seq]. iIntros "HCi". iApply ("Hc" with "[$HCi $HC]").
    - cbn [kcat_pay_seq]. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. iFrame "Hc". iApply (kcat_wb_frame with "HC Hw").
  Qed.

  (* ...AND IT SPLITS AND JOINS AT ANY POINT, which is what a format string
     with a [%s] in it needs: the literal before the directive, the
     argument's own bytes and the literal after it are three runs of one
     chain. *)
  Lemma kcat_pay_seq_in (fdw : mword 64) (fb : nat -> bv 8) (k : nat) :
    forall (i : nat) (Ci Ci' Cend : iProp Σ),
      (Ci' -∗ Ci) -∗
      kcat_pay_seq fdw fb i k Ci Cend -∗ kcat_pay_seq fdw fb i k Ci' Cend.
  Proof using .
    induction k as [| k IH]; intros i Ci Ci' Cend; iIntros "Hm Hc".
    - cbn [kcat_pay_seq]. iIntros "HCi".
      iApply "Hc". iApply ("Hm" with "HCi").
    - cbn [kcat_pay_seq]. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. iFrame "Hc". iApply (kcat_wb_mono_in with "Hm Hw").
  Qed.

  Lemma kcat_pay_seq_split (fdw : mword 64) (fb : nat -> bv 8) (k1 : nat) :
    forall (i k2 : nat) (Ci Cend : iProp Σ),
      kcat_pay_seq fdw fb i (k1 + k2) Ci Cend -∗
      ∃ Cm : iProp Σ,
        kcat_pay_seq fdw fb i k1 Ci Cm
        ∗ kcat_pay_seq fdw fb (i + k1) k2 Cm Cend.
  Proof using .
    induction k1 as [| k1 IH]; intros i k2 Ci Cend.
    - rewrite Nat.add_0_r. cbn [Nat.add]. iIntros "Hc".
      iExists Ci. iSplitR "Hc"; [ cbn [kcat_pay_seq]; by iIntros "$" | ].
      iExact "Hc".
    - cbn [Nat.add]. iIntros "Hc". cbn [kcat_pay_seq].
      iDestruct "Hc" as (Cn) "[Hw Hc]".
      iDestruct (IH (S i) k2 Cn Cend with "Hc") as (Cm) "[H1 H2]".
      iExists Cm. iSplitR "H2".
      + iExists Cn. iFrame "Hw H1".
      + replace (i + S k1)%nat with (S i + k1)%nat by lia. iExact "H2".
  Qed.

  Lemma kcat_pay_seq_join (fdw : mword 64) (fb : nat -> bv 8) (k1 : nat) :
    forall (i k2 : nat) (Ci Cm Cend : iProp Σ),
      kcat_pay_seq fdw fb i k1 Ci Cm -∗
      kcat_pay_seq fdw fb (i + k1) k2 Cm Cend -∗
      kcat_pay_seq fdw fb i (k1 + k2) Ci Cend.
  Proof using .
    induction k1 as [| k1 IH]; intros i k2 Ci Cm Cend.
    - rewrite Nat.add_0_r. cbn [Nat.add]. iIntros "H1 H2".
      iApply (kcat_pay_seq_in fdw fb k2 i Cm Ci Cend with "[H1] H2").
      cbn [kcat_pay_seq]. iExact "H1".
    - cbn [Nat.add]. iIntros "H1 H2". cbn [kcat_pay_seq] in *.
      iDestruct "H1" as (Cn) "[Hw H1]".
      iExists Cn. iFrame "Hw".
      iApply (IH (S i) k2 Cn Cm Cend with "H1 [H2]").
      replace (S i + k1)%nat with (i + S k1)%nat by lia. iExact "H2".
  Qed.

  (* ...AND IT ONLY READS THE BYTES IT COVERS. *)
  Lemma kcat_pay_seq_ext (fdw : mword 64) (fb fb' : nat -> bv 8) (k : nat) :
    forall (i : nat) (Ci Cend : iProp Σ),
      (forall j : nat, (i <= j)%nat -> (j < i + k)%nat -> fb j = fb' j) ->
      kcat_pay_seq fdw fb i k Ci Cend -∗ kcat_pay_seq fdw fb' i k Ci Cend.
  Proof using .
    induction k as [| k IH]; intros i Ci Cend Heq; iIntros "Hc".
    - cbn [kcat_pay_seq] in *. iExact "Hc".
    - cbn [kcat_pay_seq] in *. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. rewrite <- (Heq i ltac:(lia) ltac:(lia)). iFrame "Hw".
      iApply (IH (S i) Cm Cend ltac:(intros j H1 H2; apply Heq; lia)
                with "Hc").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* exit @0x3ac -- no continuation.                                        *)
  (* --------------------------------------------------------------------- *)
  (* ...AND ITS PAYLOAD IS A PREMISE NOW (lane CAT-WALK, W2).  At
     [UkRun.ukn_triv] the exit's one payment was free and the stub took
     nothing; at a status-independent payload it is a RESOURCE, and the
     walk's write chain is what produces it -- [kcat_pay_all]'s [Cend] is
     exactly [ukn_pay N (-1)].  The status a0 carries does not matter
     ([UkRun.ukn_const_eq]), which is what lets cat's 0-exit and its
     1-exit pay the same thing. *)
  Lemma wp_kcat_exit (h : CpuId) (m : regfile) (avail : nat) :
    cat_code γt -∗
    ukn_pay N (-1) -∗
    urun N h m (mword_of_int CatSyms.exit) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    iIntros "#Hcode Hpayv Hrun".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    rewrite Hexit.
    iApply (wp_uk_cli N h m (mword_of_int 0x3ac)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3ac with "Hcode"). }
    assert (E0e : add_vec_int (mword_of_int 0x3ac : mword 64) 2
                  = mword_of_int 0x3ae)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eme : <[Regidx a7_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 2 : mword 6)
                          : mword 64)]> m
                  = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0e Eme.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    iApply (wp_uk_ecall_exit N h1 m1 (mword_of_int 0x3ae) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "[] [Hpayv] Hrun").
    { iApply (uis_cat_3ae with "Hcode"). }
    (* THE ONE PAYMENT, at the status a0 carries -- which is the payload
       the caller handed in, because cat's record is status-independent. *)
    { by rewrite (ukn_const_eq (N := N) (uexitst m1) (-1)). }
  Qed.

  (* ...AND THE EXIT AS AN OBLIGATION AT ITS STATUS (program-specs cut 3).
     The walk's exits used to spend [ukn_pay N (-1)] directly, which ties
     every payer to the payload; this is the hole instead -- the rest of
     the process at the stub's entry, with a0 read as the C [int] status --
     and it is definitionally [UkTree.ex_obl] at cat's instance.  The
     payload is ONE instance of it ([kcat_exit_of_pay]). *)
  Definition kcat_exit (status : Z) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜bv_signed (trunc32 (m !!! Regidx a0_idx)) = status⌝ -∗
       cat_code γt -∗
       urun N h m (mword_of_int CatSyms.exit) avail -∗
       mWP (Loop : expr riscv_lang))%I.

  Lemma kcat_exit_of_pay (s : Z) : ukn_pay N (-1) -∗ kcat_exit s.
  Proof using Hpay.
    iIntros "Hpayv" (h m avail) "_ #Hcode Hrun".
    iApply (wp_kcat_exit h m avail with "Hcode Hpayv Hrun").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* read @0x3c4 -- THE STUB THAT WRITES.  The caller hands in the whole    *)
  (* count as a run it owns and gets the whole count back at SOME contents; *)
  (* the row does not say which bytes moved, does not say how many, and     *)
  (* does not tie either to the value returned.                             *)
  (* --------------------------------------------------------------------- *)
  (* ...AT THE ONE LAW IT SPENDS (lane CAT-WALK, W1), for
     [wp_kcat_write]'s reason. *)
  Lemma wp_kcat_read (a : Z) (cnt : nat) (f : nat -> bv 8)
      (h : CpuId) (m : regfile) (avail : nat) :
    m !!! Regidx a1_idx = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32)
      = Z.of_nat cnt ->
    udepw_law 5 -∗
    cat_code γt -∗
    ubytes γd a cnt f -∗
    urun N h m (mword_of_int CatSyms.read) avail -∗
    (∀ (h' : CpuId) (ret : mword 64) (g : nat -> bv 8),
       ubytes γd a cnt g -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha1 Hcnt. iIntros "#Hdp #Hcode Hbs Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hread & _ & _ & _ & _).
    rewrite Hread.
    (* ---- 0x3c4  c.li a7,5 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3c4)
              (mword_of_int 5 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3c4 with "Hcode"). }
    assert (E0r : add_vec_int (mword_of_int 0x3c4 : mword 64) 2
                  = mword_of_int 0x3c6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emr : <[Regidx a7_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 5 : mword 6)
                          : mword 64)]> m
                  = <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0r Emr.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    (* the buffer pointer and the count survive the write to a7 *)
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int a : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcntr : bv_signed (subrange_vec_dec (m1 !!! Regidx a2_idx) 31 0
                               : mword 32) = Z.of_nat cnt).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hcnt. }
    (* ---- 0x3c6  ecall -- the row that MOVES THE IMAGE ---- *)
    iApply (wp_uk_ecall_read N h1 m1 (mword_of_int 0x3c6) a cnt f avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 5 : mword 64));
                    vm_compute; reflexivity)
              Ha1r Hcntr ltac:(vm_compute; reflexivity)
              with "[] Hbs Hrun []").
    { iApply (uis_cat_3c6 with "Hcode"). }
    (* THE FLAGGED DEPOSIT: read(5) (P4) *)
    { iApply (udepw_of_law N m1 (mword_of_int 0x3c6) 5 with "Hdp"). }
    assert (E1r : add_vec_int (mword_of_int 0x3c6 : mword 64) 4
                  = mword_of_int 0x3ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1r.
    iIntros (h2 ret g) "_ Hbs Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3ca  c.jr ra ---- *)
    assert (Hrar : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 5 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3ca) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3ca with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret g with "Hbs Hrun").
  Qed.

  (* ===================================================================== *)
  (* WHAT THE LOOP SPENDS PER READ (lane CAT-WALK, W1).                     *)
  (*                                                                       *)
  (* [kcat_w]'s twin at read(5), and cat's loop needs it for a reason its   *)
  (* writes do not have: the loop's writes cannot be a FINITE chain -- the  *)
  (* counts are the read's own returns and the number of rounds is the      *)
  (* file's length -- and the bytes they write are the bytes the read just  *)
  (* delivered.  So the read has to be abstract too: what a caller hands    *)
  (* in is an obligation whose OUTPUT reads the return value and the        *)
  (* contents, and the deed-aware instance                                  *)
  (* ([UkFileOpen.wp_uk_read_deed_learns]) is simply one whose output says  *)
  (* those bytes are the deed's.  The free instance ([kcat_r_of_law])       *)
  (* says nothing about them, which is exactly what the landed stub said.   *)
  (* ===================================================================== *)
  Definition kcat_r (fdv : mword 64) (a : Z) (cnt : nat) (Ri : iProp Σ)
      (Ro : mword 64 -> (nat -> bv 8) -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat) (f : nat -> bv 8),
       ⌜m !!! Regidx a0_idx = fdv⌝ -∗
       ⌜m !!! Regidx a1_idx = (mword_of_int a : mword 64)⌝ -∗
       ⌜bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32)
        = Z.of_nat cnt⌝ -∗
       cat_code γt -∗
       Ri -∗
       ubytes γd a cnt f -∗
       urun N h m (mword_of_int CatSyms.read) avail -∗
       (∀ (h' : CpuId) (ret : mword 64) (g : nat -> bv 8),
          Ro ret g -∗
          ubytes γd a cnt g -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...and its output side is MONOTONE, which is what lets a caller
     REFINE what a read told it -- at a held descriptor row, "the bytes at
     SOME offset" into "the bytes at the offset I expected". *)
  Lemma kcat_r_mono_out (fdv : mword 64) (a : Z) (cnt : nat) (Ri : iProp Σ)
      (Ro Ro' : mword 64 -> (nat -> bv 8) -> iProp Σ) :
    (∀ (ret : mword 64) (g : nat -> bv 8), Ro ret g -∗ Ro' ret g) -∗
    kcat_r fdv a cnt Ri Ro -∗ kcat_r fdv a cnt Ri Ro'.
  Proof using .
    iIntros "Hm Hr" (h m avail f)
      "%Ha0 %Ha1 %Ha2 #Hcode HRi Hbs Hrun Hcont".
    iApply ("Hr" $! h m avail f with "[%] [%] [%] Hcode HRi Hbs Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret g) "HRo Hbs Hrun".
    iApply ("Hcont" $! h' ret g with "[Hm HRo] Hbs Hrun").
    iApply ("Hm" with "HRo").
  Qed.

  Lemma kcat_r_of_law (fdv : mword 64) (a : Z) (cnt : nat) (Ri : iProp Σ)
      (Ro : mword 64 -> (nat -> bv 8) -> iProp Σ) :
    (forall (ret : mword 64) (g : nat -> bv 8), Ri ⊢ Ro ret g) ->
    udepw_law 5 -∗ kcat_r fdv a cnt Ri Ro.
  Proof using .
    intros Hm. iIntros "#Hrd" (h m avail f)
      "_ %Ha1 %Ha2 #Hcode HRi Hbs Hrun Hcont".
    iApply (wp_kcat_read a cnt f h m avail Ha1 Ha2
              with "Hrd Hcode Hbs Hrun").
    iIntros (h' ret g) "Hbs Hrun".
    iApply ("Hcont" $! h' ret g with "[HRi] Hbs Hrun"). by iApply Hm.
  Qed.

  (* ===================================================================== *)
  (* WHAT main's TURN SPENDS PER open AND PER close (lane CAT-WALK, W1/W3). *)
  (*                                                                       *)
  (* [kcat_w]'s and [kcat_r]'s twins at open(15) and close(21), and they    *)
  (* exist for W3's reason: the FREE leaf's post leaves the descriptor's    *)
  (* TYPE existential and ties it to nothing, while                         *)
  (* [UkFileOpen.wp_uk_ecall_open_read_deed] hands back a handle ON THE     *)
  (* DEED'S OWN INUM and [wp_uk_ecall_open_miss_deed] refutes the success   *)
  (* arm outright.  The two leaves take DIFFERENT deposits, so no single    *)
  (* stub can be both: what the walk names is the obligation, and each      *)
  (* leaf is one instance of it.  THE LEDGER RIDES IN [Oi]/[Oo] for the     *)
  (* same reason -- the free arm gives [ustd] back untouched and the deed   *)
  (* arm gives [ualloc] -- which is why the walk above no longer mentions   *)
  (* [UserFd.ustd] at all.                                                 *)
  (* ===================================================================== *)
  Definition kcat_o (pv : mword 64) (Oi : iProp Σ)
      (Oo : mword 64 -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜m !!! Regidx a0_idx = pv⌝ -∗
       ⌜m !!! Regidx a1_idx = (mword_of_int 0 : mword 64)⌝ -∗
       cat_code γt -∗
       Oi -∗
       urun N h m (mword_of_int CatSyms.open) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          Oo ret -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* THE FREE INSTANCE: the landed stub's own post, with the LEDGER coming
     in and going back out through the obligation's two halves.  A caller
     that wants to attach more to it -- a diagnostic run, a round for the
     file it just opened -- does so with [kcat_o_mono], which takes an
     IRIS wand and can therefore use the laws the caller holds. *)
  Lemma kcat_o_of_law (pv : mword 64) (l : list fdstate) :
    fd_lowest_closed l = None ->
    udepw_law 15 -∗
    kcat_o pv (ustd γfd l)
      (fun ret : mword 64 =>
         (((∃ (fd : nat) (rd wr : bool) (t : fdtype),
              ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)
               /\ (fd < NOFILE)%nat
               /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗
              ufd γfd fd (FdOpen rd wr t))
           ∨ ⌜ret = (mword_of_int (-1) : mword 64)⌝)
          ∗ ustd γfd l)%I).
  Proof using .
    intros Hnone. iIntros "#Hop" (h m avail) "_ _ #Hcode Hstd Hrun Hcont".
    iApply (wp_kcat_open h m l avail Hnone with "Hop Hcode Hrun Hstd").
    iIntros (h' ret) "Hfdh Hstd Hrun".
    iApply ("Hcont" $! h' ret with "[Hfdh Hstd] Hrun"). iFrame "Hfdh Hstd".
  Qed.

  Definition kcat_cl (fd : nat) (Ci Co : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd⌝ -∗
       cat_code γt -∗
       Ci -∗
       urun N h m (mword_of_int CatSyms.close) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          Co -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...and the open's output side is MONOTONE.  The wand is an IRIS one
     and not a Coq entailment, because what a caller wants to attach to
     the raw post -- the diagnostic run, a round for the file -- is itself
     built out of the laws it holds. *)
  Lemma kcat_o_mono (pv : mword 64) (Oi : iProp Σ)
      (Oo Oo' : mword 64 -> iProp Σ) :
    (∀ ret : mword 64, Oo ret -∗ Oo' ret) -∗
    kcat_o pv Oi Oo -∗ kcat_o pv Oi Oo'.
  Proof using .
    iIntros "Hm Ho" (h m avail) "%Ha0 %Ha1 #Hcode HOi Hrun Hcont".
    iApply ("Ho" $! h m avail with "[%] [%] Hcode HOi Hrun");
      [ exact Ha0 | exact Ha1 | ].
    iIntros (h' ret) "HOo Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HOo] Hrun").
    iApply ("Hm" with "HOo").
  Qed.

  Lemma kcat_cl_of_dep (fd : nat) (st : fdstate) (Ci Co : iProp Σ) :
    kcat_cldep st -∗ ufd γfd fd st -∗ (Ci -∗ Co) -∗ kcat_cl fd Ci Co.
  Proof using .
    iIntros "#Hdp Hfdh Hm" (h m avail) "%Ha0 #Hcode HCi Hrun Hcont".
    iApply (wp_kcat_close h m fd st avail Ha0 with "Hdp Hcode Hrun Hfdh").
    iIntros (h' ret) "Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HCi] Hrun").
    iApply ("Hm" with "HCi").
  Qed.

End UkCat.
