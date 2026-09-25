(* UexecExecMint.v -- THE GENERIC MINT: the U-mode trap loop's own slot at
   every key, and it costs the kernel nothing.

   WHAT IT COSTS: THE SUPPLY, AND NOTHING ELSE.  Since the ARM the returning
   arm demands the process's bundle for the number it is at
   ([UexecSG.sbundle]).  At the kernel's instance ([UexecExecInst]) the only
   number with a bundle is exec, and exec's is
   [SpecSysExec.sys_exec_au_pre] at the trapping key: open's walk premise
   and open's commit -- both handed back at [True] receipts by
   [FsAbsInvFire.fsabs_exec_half], which is a closed fact -- beside the slot
   wand the kernel fires for the NEW image.  A generic slot family pays that
   wand at every key, so exec's bundle spends nothing.  What the two lemmas
   below take is the class's [ssupply] itself ([AppInv.app_sup]): a generic
   process may make ANY syscall, and the numbers whose bundles move the
   abstract state are paid out of that credential.  It is a PREMISE and not
   a closed fact -- see [UexecSG.v]'s "[ssupply] IS NOT IN [uvb]" and
   [AppInv]'s [app_sup_raw]: it is born at boot as a Coq hypothesis of the
   generic system theorem and handed to each mint site.

   SO THERE IS NO LIFT LEFT.  The exec channel was once a SECOND parallel
   fixpoint and this file's work was carrying a plain slot up to it by Loeb.
   The two tiers are one: what remains is [UexecCond.cond_entry_slot] with
   its two premises discharged from the instance -- [psok] is [True] at every
   number, and [UkRun.udep]'s key-free law is the class's
   [UexecSG.sbundle_of_supply_ne]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import Xv6Cameras.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UexecSlot.
Require Import UexecWp.
Require Import UexecRet.
Require Import UexecCond.       (* [cond_entry_slot] -- the plain generic slot *)
Require Import UexecExecInst.   (* the class INSTANCE: [uexecSG_xv6] / [uprogSG_gen] *)
Require Import FsAbsInvFire.    (* [fsabs_open_in] / [fsabs_mknod_pre]: the two
                                   branches the supply pays update-free *)
Require Import UserPerm.   (* [uperm], [perm_of] -- RULING WR-TB *)
Require Import SpecFilewrite.    (* [filewrite_in]: row 16's keyed input, for
                                    [filewrite_in_of_sup] (lane EXEC-SEAM, (D)) *)
Require Import SpecConsolewrite. (* [cons_out_chain_of_licence]: its console arm *)
Require Import SpecFileclose.    (* [fileclose_cpay_taint]: close's pipe row, paid
                                    out of the application's taint *)
Require Import PipeQueue.        (* [pipe_wpay_taint]: write's pipe arm, likewise *)
Require Import PipeNames.        (* [pipe_names] -- the row the registry pays at *)
Require Import PipeReg.          (* [pipe_reg]: the UNTAINTED payer of a pipe
                                    row's close (design/app-pipe.md SS4.3aa) *)
Require Import UsysMemOk.       (* [USYS_exec] *)
Require Import RegFile.         (* [regfile] -- [udepw]'s register argument *)
Require Import UkRun.           (* [udep] -- the supplier and its key-free law *)
Require Import WpUart.         (* [cons_licence] -- the OUTPUT LICENCE the
                                  generic supply carries (lane OUT-FUPD) *)
Require Import AppInv.          (* [app_sup] -- the credential both mints take *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Import Defs.
Require Import CtxIdDefs.

Local Open Scope Z_scope.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UexecExecMint.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* THE PROGRAM-SIDE DEPOSIT DATA the generic slot runs on: the supplier IS
     the supply ([UexecExecInst.uprogSG_gen]'s [Dsup]) and the key-free
     minting law is the class's own [sbundle_of_supply_ne], which admits
     every number but exec. *)
  (* ...AND THE KILL CREDENTIAL BESIDE IT (lane KILL-PAY §1c): the generic
     instance's supply is the PAIR ([UexecExecInst.xv6_ssupply]), because
     the generic slot runs an unverified program -- which may call kill(2)
     and may trap with a cause the kernel cannot rule out.  THE OUTPUT
     LICENCE IS NOT A THIRD HALF (lane SUP-ONE): an unverified [write(2)]
     on the console still costs one, but the application's kill price BUYS
     it ([RiscvPtsto.ai_lic], read as [WpUart.cons_licence_of_taint]), so
     the taint below is the whole of what that arm needs. *)
  Lemma udep_gen :
    app_sup -∗ app_taint -∗ udep.
  Proof using .
    rewrite /udep /Dsup /= /xv6_ssupply.
    iIntros "#Hsup #Hkc".
    iSplitR;
      [ iModIntro; iSplit; [ iExact "Hsup" | iExact "Hkc" ] | ].
    iSplitR; [ iPureIntro; intros n W Q _ Hne;
               exact (sbundle_of_supply_ne uslot n W Q Hne) | ].
    iSplit; [ iPureIntro | iSplit; iPureIntro ].
    - (* close's key-guarded row: at the generic instance every number is
         admitted, so it is the same law read at 21 (design/pipe.md) *)
      intros W Q _.
      exact (sbundle_of_supply_ne uslot 21 W Q ltac:(vm_compute; discriminate)).
    - (* ...and exit's, for the same reason -- and the row's own
         REGISTRATIONS (lane PIPE-REG) are not even looked at: at the
         generic instance every number's bundle comes off the supply *)
      intros W Q. iIntros "#Hs _".
      iApply (sbundle_of_supply_ne uslot USYS_exit W Q
                ltac:(vm_compute; discriminate)).
      iExact "Hs".
    - (* ...and exit's out of the TAINT, which the generic instance does
         not even need to look at (design/pipe.md, "The exit path") *)
      intros W Q. iIntros "#Hs _".
      iApply (sbundle_of_supply_ne uslot USYS_exit W Q
                ltac:(vm_compute; discriminate)).
      iExact "Hs".
  Qed.

  (* ===================================================================== *)
  (* ...AND THE VERIFIED PROGRAM'S SUPPLY, WHICH IS NOTHING (lane            *)
  (* SUPPLY-SPLIT, P2).  At [UexecExecInst.uprogSG_free] the supplier is     *)
  (* [True] and the admitted numbers are [xv6_free] -- every number whose    *)
  (* branch of [xv6_sbundle] is [emp], plus 9 (chdir), whose branch is       *)
  (* discharged by a closed fact.  So a program that calls only those        *)
  (* numbers builds its [udep] from nothing, and its entry slot is no        *)
  (* longer a function of [AppInv.app_sup] -- which for the echo application *)
  (* IS the taint ([AppEcho.echo_taint_of_sup]).                             *)
  (*                                                                        *)
  (* THE LAW'S OWN PREMISES DO THE WORK: it is guarded on [psok n] and       *)
  (* [n <> USYS_exec], and [xv6_free n] is the former.                       *)
  (* ===================================================================== *)
  Lemma udep_free : ⊢ udep (PS := uprogSG_free).
  Proof using .
    rewrite /udep /Dsup /=.
    iSplit; [ iModIntro; done | ].
    iSplitR; [ iPureIntro; intros n W Q Hok _; iIntros "_";
               rewrite /sbundle_pay /sbundle_at /sexit_pay /=;
               iApply (xv6_sbundle_free uslot n W Q Hok) | ].
    iSplit; [ iPureIntro | iSplit; iPureIntro ].
    - (* ...AND CLOSE'S ROW, which left the free set with the byte queue
         (design/pipe.md, "The byte queue") and is [emp] at every
         descriptor that is not a pipe end. *)
      intros W Q Hnp.
      iIntros "_".
      rewrite /sbundle_pay /sbundle_at /sexit_pay /=.
      iApply (xv6_sbundle_close_nonpipe uslot W Q Hnp).
    - (* ...AND EXIT'S, which left it for the same reason one table over
         (design/pipe.md, "The exit path") -- AND OFF THE ROW'S OWN
         REGISTRATIONS now (design/app-pipe.md SS2, lane PIPE-REG), which
         is what lets a VERIFIED program hold a pipe: at a pipe row the
         registration is one instance of the row's [□]-guarded close
         payment, and at every other row it is [emp], so the pipe-free
         reading this arm used to take is the same law read at a table of
         self-registering rows. *)
      intros W Q. iIntros "_ Hregs".
      rewrite /sbundle_pay /sbundle_at /sexit_pay /=.
      iApply (xv6_sbundle_exit_regs uslot W Q with "Hregs").
    - (* ...AND THE SAME ROW OUT OF THE TAINT, at any table at all: a pipe
         row's close payment is a link OR the credential
         ([PipeQueue.pipe_cpay]), and this is the arm a program that
         called pipe(2) exits by. *)
      intros W Q. iIntros "_ #Ht".
      rewrite /sbundle_pay /sbundle_at /sexit_pay /=.
      iApply (xv6_sbundle_exit_taint uslot W Q with "Ht").
  Qed.

  (* ...and what a generic-route LEAF takes, at the free instance: the
     program-side premise every [udepw_of_psok] site becomes under the
     sweep ([UkRun.udepw_of_psok] at [psok := xv6_free]). *)
  Lemma udepw_free (N : uk_names Σ) (m : regfile) (pc : mword 64) (n : Z) :
    xv6_free n -> ⊢ udepw (PS := uprogSG_free) N m pc n.
  Proof using .
    intros Hn.
    exact (udepw_of_psok (PS := uprogSG_free) N m pc n Hn
             (proj1 Hn)).
  Qed.

  (* ===================================================================== *)
  (* ...AND THE DEPOSIT FOR ONE NUMBER THE FREE INSTANCE DOES NOT ADMIT,     *)
  (* OUT OF THE SUPPLY (lane E2).  [UkInit.init_deps] is three named         *)
  (* deposits, and two of them -- open(15) and mknod(17) -- are owed only ON *)
  (* THE TAINT ARMS: with its credential in hand /init walks both calls      *)
  (* through the PINNED leaves, and the arms where it has none walk the      *)
  (* generic stub, which is exactly what the application's supply pays for.  *)
  (* So what the era owes is [□ (T -∗ udepw_law n)], and this is its         *)
  (* second half ([AppEcho.echo_sup_of_taint] is the first).                 *)
  (*                                                                        *)
  (* WHY IT IS NOT [UkRun.udepw_of_psok] AND NOT [udep_dep]: the first needs *)
  (* [psok n], and at the verified instance [UexecSG.free_num] excludes 15   *)
  (* and 17 by construction (their branches move the abstract state); the    *)
  (* second produces the bundle UNDER A BASIC UPDATE, and [UkRun.udepw]'s    *)
  (* explicit disjunct is update-free.  Both branches are in fact update-    *)
  (* free at the supply ([UexecExecInst.xv6_sbundle_of_supply_ne] introduces *)
  (* the [==∗] on them and on nothing else), so the two are read straight    *)
  (* off [FsAbsInvFire].                                                     *)
  (*                                                                        *)
  (* THE PROGRAM'S INSTANCE IS A PARAMETER: the law is about the RIGHT       *)
  (* disjunct, which mentions no [psok], so it holds at whichever [uprogSG]  *)
  (* the taking program runs at ([uprogSG_free] for /init).                  *)
  (* ===================================================================== *)
  Lemma udepw_of_sup `{PSx : uprogSG Σ} (N : uk_names Σ) (m : regfile)
      (pc : mword 64) (n : Z) :
    n = 15 \/ n = 17 -> app_sup -∗ udepw (PS := PSx) N m pc n.
  Proof using .
    intros Hn. iIntros "#Hsup".
    rewrite /udepw. iIntros (M pm sz fdv cw gn cs pidv) "#Hmp Hheap Hufd".
    iFrame "Hheap Hufd". iRight.
    rewrite /sbundle_pay. iExists (xfam_at (ukn_pay N) xfam_pt).
    iSplitR; [ done | ].
    rewrite /sbundle_at /= /xv6_sbundle /xfam_at /xfam_pt /xfam_exec /=.
    destruct Hn as [-> | ->].
    - destruct (decide ((15 : Z) = UsysMemOk.USYS_exec)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((15 : Z) = 5)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((15 : Z) = 9)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((15 : Z) = 15)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      iApply (fsabs_open_in with "Hsup").
    - destruct (decide ((17 : Z) = UsysMemOk.USYS_exec)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((17 : Z) = 5)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((17 : Z) = 9)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((17 : Z) = 15)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((17 : Z) = 16)) as [He | _];
        [ exfalso; discriminate He | ].
      destruct (decide ((17 : Z) = 17)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      iApply (fsabs_mknod_pre with "Hsup").
  Qed.

  Lemma udepw_law_of_sup `{PSx : uprogSG Σ} (n : Z) :
    n = 15 \/ n = 17 -> app_sup -∗ udepw_law (PS := PSx) n.
  Proof using .
    intros Hn. iIntros "#Hsup". rewrite /udepw_law.
    iIntros "!>" (N m pc). iApply (udepw_of_sup N m pc n Hn with "Hsup").
  Qed.

  (* ...AND READ'S (lane CAT-GEOM-3).  The twin of [udepw_law_of_sup_write]
     at row 5, and it is not a new idea: [xv6_sbundle_of_supply_ne] has
     always paid row 5 with [FsAbsInvFire.fsabs_fileread_in] out of
     exactly this pair, and [fsabs_fileread_in] is stated at ANY [P] --
     the inode arm is [fsabs_aread], the pipe arm the taint, the console
     arm the DIRTY credential a tokenless reader pays.  Row 5 was never
     "excluded"; it simply had no consumer, because [udepw_of_sup]'s
     [n = 15 \/ n = 17] made its own [decide (n = 5)] branch unreachable
     and nothing else asked.  THE FREE READ WRITES THE CALLER'S BUFFER,
     which is what makes it honest here: at a TAINTED era that is exactly
     what the generic tier does for every process, and the caller gets
     its own [P] back at the one position the read landed on. *)
  Lemma udepw_of_sup_read `{PSx : uprogSG Σ} (N : uk_names Σ) (m : regfile)
      (pc : mword 64) :
    app_sup -∗ app_taint -∗ udepw (PS := PSx) N m pc 5.
  Proof using .
    iIntros "#Hsup #Hkc".
    rewrite /udepw. iIntros (M pm sz fdv cw gn cs pidv) "#Hmp Hheap Hufd".
    iFrame "Hheap Hufd". iRight.
    rewrite /sbundle_pay. iExists (xfam_at (ukn_pay N) xfam_pt).
    iSplitR; [ done | ].
    rewrite /sbundle_at /= /xv6_sbundle /xfam_at /xfam_pt /xfam_exec /=.
    destruct (decide ((5 : Z) = UsysMemOk.USYS_exec)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide ((5 : Z) = 5)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iApply (fsabs_fileread_in with "Hsup Hkc").
  Qed.

  Lemma udepw_law_of_sup_read `{PSx : uprogSG Σ} :
    app_sup -∗ app_taint -∗ udepw_law (PS := PSx) 5.
  Proof using .
    iIntros "#Hsup #Hkc". rewrite /udepw_law.
    iIntros "!>" (N m pc). iApply (udepw_of_sup_read N m pc with "Hsup Hkc").
  Qed.

  (* ...AND WRITE'S, WITH NO UPDATE MODALITY (lane EXEC-SEAM, (D)).
     [FsAbsInvFire.fsabs_filewrite_in] is stated under [|==>], but every arm
     of its proof is [iModIntro]: the inode arm is the supply's own chain,
     the console arm is the licence's, and nothing is minted.  Restated
     without the modality it fits [UkRun.udepw]'s shape, whose conclusion
     has none -- which is what lets a program's write deposit be paid
     UNDER THE TAINT ([T -∗ app_sup], [T -∗ cons_licence]) instead of being
     admitted at the top as a free law. *)
  (* ...AND THE PIPE ARM IS THE TAINT (design/pipe.md, "The byte queue"):
     a generic write at a pipe descriptor disconnects the pipe's exact
     ghost state, and its price is the application's kill credential --
     which the generic supply carries beside [app_sup] and the output
     licence ([UexecExecInst.xv6_ssupply]), so every caller already has it.
     [FsAbsInvFire.fsabs_filewrite_in] took the same argument. *)
  Lemma filewrite_in_of_sup (st : fdstate) (n : Z) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z) (lz : bool)
      (ua : mword 64) :
    app_sup -∗ app_taint -∗
    filewrite_in pmv sz lz st n M ua (fun _ => True%I) (fun _ _ => True%I).
  Proof using .
    iIntros "#Hsup #Hkc".
    iDestruct (cons_licence_of_taint with "Hkc") as "#Hlic".
    rewrite /filewrite_in.
    destruct st as [| rb wb ty]; [ iEmpIntro | ].
    destruct wb; [| iEmpIntro ].
    destruct ty as [i γo om | γp | ma].
    - (* the inode arm at the row's mode (lane OFF-LINK-4): a held row's
         payment is the same chain beside the taint the supply holds *)
      destruct om as [|].
      + iApply (fsabs_awrite_chain _ i γo M ua n 0%nat _ with "Hsup").
      + rewrite /filewrite_in_held. iRight. iSplitR; [| iExact "Hkc"].
        iApply (fsabs_awrite_chain _ i γo M ua n 0%nat _ with "Hsup").
    - iApply (pipe_wpay_taint with "Hkc").
    - iApply (cons_out_chain_of_licence with "Hlic").
  Qed.

  Lemma udepw_of_sup_write `{PSx : uprogSG Σ} (N : uk_names Σ) (m : regfile)
      (pc : mword 64) :
    app_sup -∗ app_taint -∗ udepw (PS := PSx) N m pc 16.
  Proof using .
    iIntros "#Hsup #Hkc".
    rewrite /udepw. iIntros (M pm sz fdv cw gn cs pidv) "#Hmp Hheap Hufd".
    iFrame "Hheap Hufd". iRight.
    rewrite /sbundle_pay. iExists (xfam_at (ukn_pay N) xfam_pt).
    iSplitR; [ done | ].
    rewrite /sbundle_at /= /xv6_sbundle /xfam_at /xfam_pt /xfam_exec /=.
    destruct (decide ((16 : Z) = UsysMemOk.USYS_exec)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide ((16 : Z) = 5)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide ((16 : Z) = 9)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide ((16 : Z) = 15)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide ((16 : Z) = 16)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iApply (filewrite_in_of_sup with "Hsup Hkc").
  Qed.

  Lemma udepw_law_of_sup_write `{PSx : uprogSG Σ} :
    app_sup -∗ app_taint -∗ udepw_law (PS := PSx) 16.
  Proof using .
    iIntros "#Hsup #Hkc". rewrite /udepw_law.
    iIntros "!>" (N m pc). iApply (udepw_of_sup_write N m pc with "Hsup Hkc").
  Qed.

  (* ...AND CLOSE'S, AT EVERY KEY, OUT OF THE TAINT (design/pipe.md, "The
     byte queue").  A caller that does NOT know its descriptor's type --
     [UsysMemOk.usys_fd_ok]'s open row leaves it existential -- cannot take
     [UkRun.udepw_cl_nonpipe]'s free route, so its close deposit is a
     flagged one like write's, and the pipe arm of
     [SpecFileclose.fileclose_cpay] is payable out of the application's
     kill credential ([fileclose_cpay_taint]) and out of nothing else. *)
  Lemma udepw_of_sup_close `{PSx : uprogSG Σ} (N : uk_names Σ) (m : regfile)
      (pc : mword 64) :
    app_taint -∗ udepw (PS := PSx) N m pc 21.
  Proof using .
    iIntros "#Hkc".
    rewrite /udepw. iIntros (M pm sz fdv cw gn cs pidv) "#Hmp Hheap Hufd".
    iFrame "Hheap Hufd". iRight.
    rewrite /sbundle_pay. iExists (xfam_at (ukn_pay N) xfam_pt).
    iSplitR; [ done | ].
    rewrite /sbundle_at /= /xv6_sbundle /xfam_at /xfam_pt /xfam_exec /=.
    destruct (decide ((21 : Z) = UsysMemOk.USYS_exec)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 5)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 9)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 15)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 16)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 17)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 18)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 19)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 20)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 6)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide ((21 : Z) = 21)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iApply (fileclose_cpay_taint with "Hkc").
  Qed.

  Lemma udepw_law_of_sup_close `{PSx : uprogSG Σ} :
    app_taint -∗ udepw_law (PS := PSx) 21.
  Proof using .
    iIntros "#Hkc". rewrite /udepw_law.
    iIntros "!>" (N m pc). iApply (udepw_of_sup_close N m pc with "Hkc").
  Qed.

  (* ...AND CLOSE'S ROW AT A REGISTERED PIPE END, OUT OF THE REGISTRY AND
     NOT OUT OF THE TAINT (design/app-pipe.md SS4.3aa, lane
     SH-PIPE-ROUND-13).  This is the producer the ROW-AWARE deposit
     ([UkRun.udepw_row]) exists for: the generic [udepw] quantifies the
     descriptor table universally, so its payer owes the close of ANY
     table's argument-0 row -- a bill only [app_taint] can settle, which is
     why no verified program could close a pipe end on the good path.  The
     row-aware deposit hands the payer the one fact the close leaf already
     derives from the caller's own handle ([UkRun.udepw_cl_mint]'s
     [fd_st_of_key a0 fdv = st]), and at a row that IS this pipe the
     payment is one instance of [PipeReg.pipe_reg]'s [pipe_cpay] at the
     POINT family's [True] payload ([UexecExecInst.xv6_sbundle_close_of_reg]).

     [pipe_reg] is PERSISTENT, so one registration pays every close of
     either end in every process that inherits it -- which is exactly what
     sh's PIPE arm needs (four pipe closes per round, in three processes at
     three different [uk_names] records). *)
  Lemma udepw_row_of_reg_close `{PSx : uprogSG Σ} (N : uk_names Σ)
      (m : regfile) (pc : mword 64) (rb wb : bool) (γp : pipe_names) :
    pipe_reg γp -∗
    udepw_row (PS := PSx) N m pc 21 (FdOpen rb wb (FdPipe γp)).
  Proof using .
    iIntros "#Hr". rewrite /udepw_row.
    iIntros (M pm sz fdv cw gn cs pidv) "%Hst #Hmp Hheap Hufd".
    iFrame "Hheap Hufd". iRight.
    iApply (xv6_sbundle_close_of_reg _
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (ukn_pay N) rb wb γp ltac:(exact Hst) with "Hr").
  Qed.

  (* ...and the shape the close leaves take ([UkRun.udepw_cl]) *)
  Lemma udepw_cl_of_reg_close `{PSx : uprogSG Σ} (N : uk_names Σ)
      (m : regfile) (pc : mword 64) (rb wb : bool) (γp : pipe_names) :
    pipe_reg γp -∗
    udepw_cl (PS := PSx) N m pc (FdOpen rb wb (FdPipe γp)).
  Proof using .
    iIntros "#Hr". iApply udepw_cl_of_row.
    iApply (udepw_row_of_reg_close N m pc rb wb γp with "Hr").
  Qed.

  (* ...AND EXIT'S, AT EVERY KEY, OUT OF THE TAINT (design/pipe.md, "The
     exit path").  Exit's row is the close payment of EVERY row of the
     key's table, and a verified program cannot read that table today:
     [UsysMemOk.usys_fd_ok]'s open row leaves a descriptor's type
     existential and the slots above [NSTD] are untracked, so "my table
     holds no pipe" -- true of init, sh, cat, echo and sync -- is not
     statable at the U tier.  The five programs therefore name this
     deposit and it is paid, like write's, out of the application's
     credential. *)
  Lemma udepw_of_sup_exit `{PSx : uprogSG Σ} (N : uk_names Σ) (m : regfile)
      (pc : mword 64) :
    app_taint -∗ udepw (PS := PSx) N m pc USYS_exit.
  Proof using .
    iIntros "#Hkc".
    rewrite /udepw. iIntros (M pm sz fdv cw gn cs pidv) "#Hmp Hheap Hufd".
    iFrame "Hheap Hufd". iRight.
    rewrite /sbundle_pay. iExists (xfam_at (ukn_pay N) xfam_pt).
    iSplitR; [ done | ].
    rewrite /sbundle_at /= /xv6_sbundle /xfam_at /xfam_pt /xfam_exec /=.
    destruct (decide (USYS_exit = UsysMemOk.USYS_exec)) as [He | _];
      [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 5)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 9)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 15)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 16)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 17)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 18)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 19)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 20)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 6)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = 21)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (USYS_exit = USYS_exit)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iApply (fileclose_cpays_taint with "Hkc").
  Qed.

  Lemma udepw_law_of_sup_exit `{PSx : uprogSG Σ} :
    app_taint -∗ udepw_law (PS := PSx) USYS_exit.
  Proof using .
    iIntros "#Hkc". rewrite /udepw_law.
    iIntros "!>" (N m pc). iApply (udepw_of_sup_exit N m pc with "Hkc").
  Qed.

  (* the loop's mint: the generic slot at every key, out of the supply.
     [UexecCond.cond_entry_slot]'s [psok] premise is the instance's own
     (every number is admitted); its [□ ssupply] is the credential. *)
  (* THE FAMILY IS INDEXED BY THE PAY FACT ([UexecCond.cond_entry_slot]'s
     own premise): a slot at EVERY key is a slot that may trap at exit at
     every key, and exit's deposit is a payment.  At the trivial payload,
     which is the only one a generic process has. *)
  (* THE FAMILY IS NARROWED TO ALL-PARKED KEYS (design/user-read.md SS8.1,
     SS8.3; lane OFF-HAND-2).  A generic process knows nothing about its
     descriptors, so the only offset supplier its fires can ever present is
     the weak one -- [OffGv.off_user_inv], which [FdSlots.foff_row] carries
     at a PARKED inode row and at no other.  A key with a HELD row would
     leave those fires with no supplier at all, and a persistent supply can
     never present an exclusive [UserOff.uoff] in its place.  So the mint
     asks its key for the discipline, in the PURE form the tier can carry
     across its own Loeb step ([UsysMemOk.usys_fd_ok_parked] is the row
     that maintains it); the exec crossing is where the fact enters, off
     [SpecKexec.exec_slot_pre]'s wands. *)
  Lemma uslot_mint :
    app_sup -∗ app_taint -∗ □ uexec_wp -∗
    □ (∀ W : uvis, my_pay (uvis_gen W) (fun _ => True)%I -∗ uslot W).
  Proof using ghost_varG0 ufdG0.
    iIntros "#Hsup #Hkc #Hgen".
    iDestruct (udep_gen with "Hsup Hkc") as "#Hdep".
    iIntros "!>" (W) "#Hpay".
    (* AT THE GENERIC INSTANCE, EXPLICITLY (lane SUPPLY-SPLIT).  The chain
       is now parametric in which [uprogSG] its two verified arms run at,
       because a verified program's is NOT this one; the generic mint is
       the caller that instantiates it here, where every number is admitted
       and echo's flagged deposit is therefore free as well. *)
    iApply (UexecCond.cond_entry_slot uprogSG_gen W ltac:(intros k _; exact I)
              with "[] Hdep [] Hkc Hgen Hpay").
    { iApply (udepw_law_of_psok (PS := uprogSG_gen) 16
                ltac:(exact I) ltac:(vm_compute; discriminate)). }
    { rewrite /ssupply /= /xv6_ssupply. iModIntro.
      iSplit; [ iExact "Hsup" | iExact "Hkc" ]. }
  Qed.

  (* ...AND THE MINT AT A CONSTANT PAYLOAD (GENERIC-PAY): the same generic
     slot, at a process that HOLDS one resource [R] between its traps and
     pays it at exit and at every kill check.  It is what a TAINTED
     process runs on -- the reclaimed lease is its [R] -- and what
     [PinnedExec.pex_slot]'s taint arm is discharged from.
     UNGATED, and that is the difference from [uslot_mint]: a process
     carrying a real payload is the TAINTED one, and the two verified
     gates [UexecCond.cond_entry_slot] tries hold only at the trivial
     payload ([USyncKernel.sync_uexec_slot], [UEchoKernel.echo_uexec_slot]),
     so [uslot_mint] stays THE entry decider and this is its sibling. *)
  (* ...AND THE PAYLOAD IS THE PERSISTENT CARRIER (lane SELF-KILL, P6b):
     the family runs on [□ (app_taint -∗ R)], the process's own
     published payment wand, because a single LINEAR [R] cannot serve both
     legs of a return.  It costs nothing HERE and nowhere else: this mint
     is the tainted route and takes [app_taint] already. *)
  Lemma uslot_mint_pay (R : iProp Σ) :
    app_sup -∗ app_taint -∗ □ uexec_wp -∗
    □ (∀ W : uvis, my_pay (uvis_gen W) (fun _ => R)%I -∗
                   □ (app_taint -∗ R) -∗ uslot W).
  Proof using .
    iIntros "#Hsup #Hkc #Hgen".
    iIntros "!>" (W) "#Hpay #HR".
    iApply (UexecCond.cond_entry_slot_pay R W with "[] Hkc Hgen Hpay HR").
    rewrite /ssupply /= /xv6_ssupply. iModIntro.
    iSplit; [ iExact "Hsup" | iExact "Hkc" ].
  Qed.

  (* ...AND THE SAME WITH THE PAYLOAD UNDER THE BOX.  An application that
     hands a constraining entry constructor its TAINT ARM cannot fix the
     payload first: the arm is persistent and is spent at whatever payload
     the round chose ([UInitSh.init_sh_slot]'s third conjunct, at the
     console reader token of the round's own position pair), so the
     resource has to be bound inside the [□].  Nothing about the proof
     changes -- the generic slot is built per call. *)
  Lemma uslot_mint_all :
    app_sup -∗ app_taint -∗ □ uexec_wp -∗
    □ (∀ (R : iProp Σ) (W : uvis),
         my_pay (uvis_gen W) (fun _ => R)%I -∗
         □ (app_taint -∗ R) -∗ uslot W).
  Proof using .
    iIntros "#Hsup #Hkc #Hgen".
    iIntros "!>" (R W) "#Hpay #HR".
    iApply (UexecCond.cond_entry_slot_pay R W with "[] Hkc Hgen Hpay HR").
    rewrite /ssupply /= /xv6_ssupply. iModIntro.
    iSplit; [ iExact "Hsup" | iExact "Hkc" ].
  Qed.
End UexecExecMint.
