(* ===================================================================== *)
(* UShLine.v -- SH-LINE 2b PHASE 2: SH'S CONSOLE READ, SUPPLIED.          *)
(*                                                                        *)
(* [UConsLine.ush_read_recv_leaf] is the read leaf sh's [gets] wants: the  *)
(* one that KEEPS the kernel's receipt, so the shell learns that the byte  *)
(* it was handed is the next one after the byte it was handed last.  Two   *)
(* things have to happen for that leaf to exist, and both need the         *)
(* CONCRETE deposit bundle ([UexecExecInst]'s instance of                  *)
(* [UexecSG.uexecSG]) in scope -- which is why this file is here and not   *)
(* beside [UkSh.v] or [UShKernel.v], where the class is abstract           *)
(* (SH-LINE 2b phase 1's finding).                                        *)
(*                                                                        *)
(*  S1  THE FAMILY.  read's deposit and read's post are read at the SAME   *)
(*      [UexecSG.sfam], so a program that wants to be told something about *)
(*      its window has to NAME the family it deposited.  [xfam_rd] is      *)
(*      [UexecExecInst.xfam]'s point at two fields: the process's own exit *)
(*      payload ([kf_xpay], which [UkRun.udepwf_std]'s pure row demands)   *)
(*      and [rf_ret] -- WHAT THE CALLER ASKS TO BE TOLD.                   *)
(*                                                                        *)
(*  S2  THE ACCESS LEMMA ([ush_read_sup]) -- the design-bearing piece.     *)
(*      THE CONSOLE ARM'S SUPPLY IS LINEAR AND PER CALL, and it is NOT     *)
(*      [UkSh.sh_deps]' read law: [UkRun.udepw_law 5] is a [□] over every  *)
(*      key, and what the console arm of [SpecFileread.fileread_in] wants  *)
(*      is [ConsoleInv.cons_acc] at the EXCLUSIVE reader token.  Where the *)
(*      token is: inside the process's own exit payload                    *)
(*      ([UserConsole.ucons_pay], the LEASE ruling), which the kernel      *)
(*      hands BACK to the deposit -- read's bundle is a wand from          *)
(*      [kf_xpay f (-1)] (app-echo.md, "SH-LINE RULING", R1).  So the      *)
(*      program supplies nothing but the half of the position pair it      *)
(*      holds in its hand ([UserConsole.upos]), and the wand does the      *)
(*      rest: agree the payload's position with it ([upos_agree]), hand    *)
(*      the token in ([cons_acc_reader]), take it back at the new cursor   *)
(*      ([ConsoleInv.cons_out]), move BOTH halves ([upos_update]) and      *)
(*      rebuild the payload.  No escrow is opened and no mask is needed:   *)
(*      the payload arrives at the wand.                                   *)
(*                                                                        *)
(*      WHAT IT COSTS BESIDE THE TOKEN: the reading of the kernel's DIRTY  *)
(*      CREDENTIAL.  A read taken without the token is paid for with       *)
(*      [ConsoleInv.cons_dirty_cred app_sup], and for a CONSTRAINING       *)
(*      application that credential IS the taint ([AppEcho.               *)
(*      echo_taint_of_sup] / [echo_sup_of_taint]).  Neither direction is   *)
(*      provable at this altitude -- [T] is a parameter here -- so both    *)
(*      are named Coq-level premises and E2 pays them.                     *)
(*                                                                        *)
(*  S3  THE DISCHARGE ([ush_read_recv_leaf_holds]).  [UkRunSys.            *)
(*      wp_uk_ecall_read_recv] at the family of S1 and the deposit of S2,  *)
(*      with the post read back through the two key-level rows below.      *)
(*      The copy-out swallow is eliminated on the way                      *)
(*      ([UConsLine.ush_swallow_nofault] out of the leaf's own no-fault    *)
(*      row), which is why the leaf hands out [ucons_swallow] at [False].  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes ObsTrace.
Require Import RegFile.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required --
   naming a class without its defining module in scope introduces a FRESH
   Type variable and the kernel's [uexecSG] instance becomes invisible to
   resolution ([UInitSh.v]'s header). *)
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
Require Import UserPtTree.         (* [uva_wmapped] *)
Require Import UserCwd UserChildren.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import VcGen.              (* [trunc32] *)
Require Import PieceFam.
Require Import FsTree.
Require Import ChildTok.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import SpecArgfd.          (* [fd_st_of_key] *)
Require Import SpecFileread.       (* [fileread_in] / [console_receipt] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import AppCfg AppInv.      (* [app_sup] *)
Require Import FsCfg.
Require Import FsAbsDefs.
Require Import ConsoleInv.         (* [cons_acc] / [cons_out] / [CONSOLE] *)
Require Import UartNames.          (* [cons_names] *)
Require Import UserConsole.        (* [upos] / [ucons_pay] *)
Require Import UkSh.               (* [ush_narrow_count_le] *)
Require Import UConsLine.          (* [ush_read_recv_leaf] / [ush_std_cons] *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UShLine.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s header): no local
     [Context {SG}] / [Context {PS}], and NO separate [uartGhostG] either
     -- [Xv6G.xv6_uart] is the one path from the bundle to the console
     ring's cameras, and it is what makes the program's spelling of the
     reader token and the ring's own ONE proposition
     ([UserConsole.ucons_reader_eq]). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  S1  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* [UexecExecInst.xfam] at the two fields read's rows look at, and the
     trivial ones everywhere else: a deposit is read at ONE number
     ([UexecExecInst.xv6_sbundle] is a match on it), so the rest of the
     record is inert.  [UInitConsK.xfam_mknod] is the mold. *)
  Definition xfam_rd (Q : Z -> iProp Σ) (Rd : nat -> nat -> iProp Σ) : xfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := pfam_triv (fun _ _ _ _ => True%I);
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_P     := fun _ _ => True%I;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := pfam_triv (fun _ _ => True%I);
       of_Fun   := pfam_triv (fun _ _ => True%I);
       of_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       wf_Q     := fun _ => True%I;
       wf_tr0   := [];
       nf_P     := fun _ _ => True%I;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := pfam_triv (fun _ _ => True%I);
       nf_Fun   := pfam_triv (fun _ _ => True%I);
       nf_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       nf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_P     := fun _ _ => True%I;
       uf_Pmiss := fun _ _ => True%I;
       uf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       uf_Ftgt  := pfam_triv (fun _ _ => True%I);
       uf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_Fmiss := pfam_triv (fun _ _ _ => True%I);
       lf_Ftgt  := pfam_triv (fun _ _ _ => True%I);
       lf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       lf_Funt  := pfam_triv (fun _ _ => True%I);
       df_P     := fun _ _ => True%I;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := pfam_triv (fun _ _ => True%I);
       df_Fdots := pfam_triv (fun _ _ _ _ => True%I);
       df_Fun   := pfam_triv (fun _ _ => True%I);
       df_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := fun _ => True%I;
       kf_xpay  := Q;
       rf_ret   := Rd |}.

  (* WHAT SH ASKS TO BE TOLD.  A lease holder's choice: the window it was
     handed begins at ITS OWN position and its half of the pair comes back
     at the new one -- or the ring's marker moved behind its back
     ([ConsoleInv.cons_out]'s second disjunct), which for a constraining
     application is the taint, and then the number means nothing any more.
     THE TWO DISJUNCTS ARE NOT THE CALLER'S CHOICE: which one it gets is
     decided by whether a tokenless reader popped while the call slept. *)
  Definition ush_rd_ret (γp : gname) (T : iProp Σ) (n : nat)
      : nat -> nat -> iProp Σ :=
    fun cur dc =>
      ((⌜cur = n⌝ ∗ upos γp (n + dc)%nat)
       ∨ (T ∗ ∃ n' : nat, upos γp n'))%I.

  (* AT THE CLASS'S OWN FAMILY TYPE, not at [xfam] ([UConsOpen.v]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument is
     checked before the instance evar is resolved and so does not
     convert. *)
  Definition ush_read_fam (γp : gname) (T : iProp Σ) (n : nat)
      (Q : Z -> iProp Σ) : sfam :=
    xfam_rd Q (ush_rd_ret γp T n).

  (* =================================================================== *)
  (*  S1b  THE TWO KEY-LEVEL ROWS, IN THE PROCESS'S DIRECTION             *)
  (*                                                                      *)
  (*  [UexecExecInst] states the deposit's ELIM and the post's INTRO --    *)
  (*  the DISPATCHER's two directions.  A process needs the other two, at  *)
  (*  readings it can name, so each takes the key's own projections as     *)
  (*  pure premises.  [UConsOpen]'s two are the mold; the proofs are the   *)
  (*  same three lines, the match at one literal.                          *)
  (* =================================================================== *)
  Local Ltac xv6_skip :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [Hc | _]; [ exfalso; by vm_compute in Hc | ]
    end.
  Local Ltac xv6_take :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [_ | Hc]; [ | exfalso; by apply Hc ]
    end.

  Lemma sbundle_at_read_intro_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 : mword 64) (sts : list fdstate) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 -> uvis_fd W = sts ->
    fileread_in (fd_st_of_key v0 sts) (rf_F f) (rf_ret f) (kf_xpay f (-1)) -∗
    sbundle_at X USYS_read f W.
  Proof.
    intros H0 Hfd. iIntros "H".
    (* the REWRITE GOES FIRST, against the lemma's own variables
       ([UConsOpen.sbundle_at_open_intro_at]'s note) *)
    rewrite -H0 -Hfd.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_read_elim_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 v1 v2 : mword 64) (sts : list fdstate)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = v1 ->
    tf_w (uvis_tf W) (tf_arg_idx 2) = v2 ->
    uvis_fd W = sts ->
    spost_at X USYS_read f W r M' fdv' cw' cs' -∗
    ∃ P : uptd,
      ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
      ⌜proc_pt_wf P⌝ ∗
      ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
      fileread_extra_core P (fd_st_of_key v0 sts) (sys_rw_count v2)
        (rf_F f) (rf_ret f) r M' v1.
  Proof.
    intros H0 H1 H2 Hfd. iIntros "H".
    rewrite -H0 -H1 -H2 -Hfd.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_take. iExact "H".
  Qed.

  (* THE DESCRIPTOR THE CALL RAN ON, out of the caller's own ledger: the
     arm [SpecFileread.fileread_in] takes is selected by the KEY's table,
     and what a program holds is the low [NSTD] slots of it. *)
  Lemma ush_fd_st_console (v0 : mword 64) (fdv l : list fdstate) (wr : bool) :
    bv_signed (trunc32 v0) = 0 ->
    take NSTD fdv = l ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    fd_st_of_key v0 fdv = FdOpen true wr (FdDevice CONSOLE).
  Proof.
    intros H0 Htake Hl0. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= 0 < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; unfold NOFILE; lia ].
    rewrite <- Htake in Hl0.
    rewrite lookup_take in Hl0; [ | unfold NSTD; lia ].
    change (Z.to_nat 0) with 0%nat. rewrite Hl0. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  S2  THE ACCESS LEMMA (header)                                       *)
  (* =================================================================== *)
  Lemma ush_read_sup (N : uk_names Σ) (γp : gname) (T : iProp Σ)
      (m : regfile) (pc : mword 64) (l : list fdstate) (n : nat) (wr : bool) :
    (* the token sits in THIS record's exit payload *)
    ukn_pay N = ucons_pay fsc_cons γp T ->
    (* the descriptor is fd 0, and fd 0 is the console *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    (* E2's two readings of the supply (header, S2) *)
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    Persistent T ->
    upos γp n -∗
    udepwf_std N m pc USYS_read (ush_read_fam γp T n (ukn_pay N)) l.
  Proof.
    intros Hpay Ha0 Hl0 Hst Hts HPT. iIntros "Hpos".
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro_at uslot
              (ush_read_fam γp T n (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) fdv
              (tf_of_arg0 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)).
    rewrite (ush_fd_st_console (m !!! Regidx a0_idx) fdv l wr Ha0 Htake Hl0).
    cbn [ush_read_fam xfam_rd rf_F rf_ret kf_xpay].
    rewrite /fileread_in.
    destruct (decide (CONSOLE = CONSOLE)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iIntros "HP".
    iEval (rewrite Hpay /ucons_pay) in "HP".
    iDestruct "HP" as "[Hl | #HT]".
    - (* THE LEASE HOLDER'S ARM: the payload's token, at the position the
         program holds ([UserConsole.upos_agree]) *)
      iDestruct "Hl" as (n') "[Hrd Hpa]".
      iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
      iEval (rewrite ucons_reader_eq) in "Hrd".
      iApply (cons_acc_reader fsc_cons app_sup n with "Hrd [Hpos Hpa]").
      iIntros (cur dc) "Hout". rewrite /cons_out.
      iDestruct "Hout" as "[Hrd' [%Hcur | #Hdirty]]".
      + (* nobody read behind its back: the window is at its own position,
           and BOTH halves move ([upos_update]) *)
        subst cur.
        iMod (upos_update γp n (n + dc)%nat with "Hpos Hpa") as "[Hpos Hpa]".
        iModIntro. iSplitR "Hpos".
        * rewrite Hpay /ucons_pay. iLeft. iExists (n + dc)%nat.
          iEval (rewrite ucons_reader_eq). iFrame "Hrd' Hpa".
        * rewrite /ush_rd_ret. iLeft. iSplitR; [ done | ]. iExact "Hpos".
      + (* a tokenless reader popped while the call slept: what is left is
           the credential, which for a constraining application is the
           taint ([AppEcho.echo_taint_of_sup]) *)
        iAssert T as "#HT"; [ iApply Hst; iExact "Hdirty" | ].
        iModIntro. iSplitR "Hpos".
        * rewrite Hpay /ucons_pay. iRight. iExact "HT".
        * rewrite /ush_rd_ret. iRight. iFrame "HT". iExists n. iExact "Hpos".
    - (* THE TAINTED ARM: the payload holds no token any more, so the call
         is paid for with the credential like anyone else's
         ([AppEcho.echo_sup_of_taint] read forwards) *)
      iApply (cons_acc_cred fsc_cons app_sup with "[] [Hpos]").
      + rewrite /cons_dirty_cred. iModIntro. iApply Hts. iExact "HT".
      + iIntros (cur dc). iModIntro. iSplitR.
        * rewrite Hpay /ucons_pay. iRight. iExact "HT".
        * rewrite /ush_rd_ret. iRight. iFrame "HT". iExists n. iExact "Hpos".
  Qed.

  (* =================================================================== *)
  (*  S3  THE DISCHARGE (header)                                          *)
  (* =================================================================== *)
  (* the ledger comes back the way it went in: read moves no descriptor *)
  Lemma ush_std_cons_of (γfd : gname) (l : list fdstate) (wr : bool) :
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    ustd γfd l -∗ ush_std_cons γfd l.
  Proof.
    intro Hl0. iIntros "H". rewrite /ush_std_cons. iFrame "H".
    iPureIntro. exists wr. exact Hl0.
  Qed.

  Lemma ush_read_recv_leaf_holds (N : uk_names Σ) (γp : gname) (T : iProp Σ)
      (l : list fdstate) :
    ukn_pay N = ucons_pay fsc_cons γp T ->
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    Persistent T ->
    ⊢ UConsLine.ush_read_recv_leaf N fsc_cons γp T l.
  Proof.
    intros Hpay Hst Hts HPT.
    rewrite /UConsLine.ush_read_recv_leaf.
    iIntros (h m pc a k cap n f avail)
      "%Hn %Ha0 %Ha1 %Ha2 %Hcapk %Hal #Hi Hbuf Hstd Hpos Hrun Hcont".
    iDestruct "Hstd" as "[Hstd %Hrow]". destruct Hrow as [wr Hl0].
    iDestruct (ush_read_sup N γp T m pc l n wr Hpay Ha0 Hl0 Hst Hts HPT
                 with "Hpos") as "Hsb".
    subst a.
    pose proof (UkSh.ush_narrow_count_le (m !!! Regidx a2_idx) cap Ha2) as Hbnd.
    iApply (wp_uk_ecall_read_recv N h m pc
              (bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                          : mword 32))
              k f avail (ush_read_fam γp T n (ukn_pay N)) l
              Hn eq_refl ltac:(lia) Hal
              with "Hi Hrun Hsb Hstd Hbuf").
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %HM %Hnf %Harg0 %Harg1 %Harg2 %Htake %Hlz Hstd Hpost Hrun Hbuf".
    (* the post, at the key's own projections *)
    iDestruct (spost_at_read_elim_at uslot (ush_read_fam γp T n (ukn_pay N)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                 Harg0 Harg1 Harg2 eq_refl with "Hpost")
      as (P) "(%Hperm & %Hwf & %Hlazy & Hrec)".
    iEval (rewrite (ush_fd_st_console (m !!! Regidx a0_idx) (uvis_fd W) l wr
                      Ha0 Htake Hl0) /fileread_extra_core;
           cbn [ush_read_fam xfam_rd rf_F rf_ret kf_xpay]) in "Hrec".
    destruct (decide (CONSOLE = CONSOLE)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iAssert (ush_std_cons (ukn_fd N) l) with "[Hstd]" as "Hstd";
      [ iApply (ush_std_cons_of (ukn_fd N) l wr Hl0 with "Hstd") | ].
    (* the lazy flag, cashed on the key the call ran at *)
    pose proof (Hlazy Hlz) as Hlf.
    iEval (rewrite /console_receipt) in "Hrec".
    iDestruct "Hrec" as "[[%Hm1 Hrd] | Hw]".
    - (* THE KILLED ARM: the token comes back somewhere and there is no
         window ([UConsLine.ush_read_recv_leaf]'s second disjunct) *)
      iDestruct "Hrd" as (cur dc) "Hrd".
      iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hrd] Hbuf Hrun");
        [ lia | exact Hgf | ].
      iRight. iLeft. iSplitR; [ by iPureIntro | ].
      rewrite /ush_rd_ret.
      iDestruct "Hrd" as "[[_ Hp] | [_ Hp]]";
        [ iExists (n + dc)%nat; iExact "Hp" | iExact "Hp" ].
    - (* THE RECEIPT *)
      iDestruct "Hw" as (dd dc cur hs sl)
        "(%Hdr & %Hhl & %Hled & #Htags & #Hlb & Hwin & Hrd)".
      rewrite /ush_rd_ret.
      iDestruct "Hrd" as "[[%Hcur Hp] | [#HT Hp]]"; last first.
      { (* the caller's own [Rd] came back tainted *)
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ lia | exact Hgf | ]. iRight. iRight. iFrame "HT Hp". }
      subst cur.
      iDestruct "Hwin" as "[(%Hwj & %Hsl & %Hch & #Hsw) | #Hdirty]"; last first.
      { (* a tokenless reader popped while the call slept *)
        iAssert T as "#HT"; [ iApply Hst; iExact "Hdirty" | ].
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ lia | exact Hgf | ].
        iRight. iRight. iFrame "HT". iExists (n + dc)%nat. iExact "Hp". }
      iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
        [ lia | exact Hgf | ].
      iLeft. iExists dd, dc, hs, sl.
      iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      iSplitR; [ rewrite ucons_stored_lb_eq; iExact "Hlb" | ].
      iSplitR; [ iExact "Htags" | ].
      iSplitR "Hp"; [ | iExact "Hp" ].
      iIntros "%Hddc".
      (* THE WINDOW, over the caller's OWN byte function: the receipt's
         per-byte ledger is at the resume image, and the leaf's own row
         reads that image back at [g] *)
      iSplitR.
      { iPureIntro. split_and!; [ lia | exact Hhl | ].
        intros j Hj.
        destruct (Hwj j Hj) as (hj & bj & Hhj & Hej & Hsj).
        exists hj, bj. split_and!; [ exact Hsj | exact Hhj | exact Hej | ].
        destruct (Hled ltac:(intros i Hi; apply Hlin; lia) j Hj)
          as (hj' & bj' & Hhj' & Hej' & Hmj').
        assert (Hhe : hj' = hj)
          by (rewrite Hhj in Hhj'; by injection Hhj' as Hhj'').
        subst hj'.
        assert (Hbe : bj' = bj)
          by exact (proj2 (obs_ends_in_inj _ _ hj bj' bj Hej' Hej)).
        subst bj'.
        rewrite (HM j ltac:(lia)) in Hmj'. by injection Hmj' as Hmj''. }
      (* ...AND THE SWALLOW, WITH THE COPY-OUT ARM ELIMINATED *)
      iApply (ucons_swallow_mono fsc_cons
                (~ uva_wmapped P (uint (add_vec_int (m !!! Regidx a1_idx)
                                          (Z.of_nat dd)))) False sl dd dc
                ltac:(intro Hno;
                      exact (Hno (Hnf P dd Hwf Hperm Hlf ltac:(lia))))
                with "[]").
      rewrite ucons_swallow_eq. iExact "Hsw".
  Qed.

End UShLine.
