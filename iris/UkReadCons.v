(* ===================================================================== *)
(* UkReadCons.v -- THE CONSOLE ARM OF THE GENERIC READ LEAF.              *)
(*                                                                        *)
(* design/user-read.md section 3's CONSOLE row, application-neutral.       *)
(* [UkReadFile.v] cut the inode member out of the read walk; this cuts the *)
(* console one, and the two are the same walk                              *)
(* ([UkRunSys.wp_uk_ecall_read_at]) at two descriptor readings.            *)
(*                                                                        *)
(* WHAT THE PAYMENT IS, AND WHY IT IS ALREADY NEUTRAL.  Section 3 asks for *)
(* "an AU on the merged IO claim, NOT echo's era ledger", and the tree     *)
(* already has exactly that -- one level BELOW the merged claim, at the    *)
(* kernel's own console boundary.  [SpecFileread.fileread_in]'s console    *)
(* arm is two payments side by side:                                       *)
(*                                                                        *)
(*   - THE RING's, [ConsoleInv.cons_acc fsc_cons app_rdcred Rd] -- the     *)
(*     reader token at the caller's own cursor, or the credential a        *)
(*     tainted or generic caller already holds;                            *)
(*   - THE CONSOLE HISTORY's, [WpUart.cons_read_pay (S gen_id) Rin], which *)
(*     is [∀ ws, WpUart.cons_link (S gen_id) ws (Rin ws)] -- and           *)
(*     [read_link] IS ConsLog's [EvRead] EVENT, spelled as an atomic       *)
(*     update: it takes the port's input resource at [(pops, dl)], the     *)
(*     kernel's pure premise [ConsLog.read_ok pops dl ws] (which is        *)
(*     literally [ConsLog.cons_ev_ok H (EvRead ws)]), and gives it back at *)
(*     [(pops, dl ++ ws)] (which is [ConsLog.cons_step H (EvRead ws)]).    *)
(*                                                                        *)
(* Neither mentions an application: the first is keyed by the ring's       *)
(* committed sequence and the second by the CONSOLE HISTORY -- the log and *)
(* the delivered list of [ConsLog.v].  Echo enters only as the caller's    *)
(* CHOICE of [Rd] and [Rin], exactly the way it enters the file arm as the *)
(* caller's choice of the observation commit's receipt.  So this file      *)
(* states the arm at those public lemmas and factors nothing: there was    *)
(* nothing echo-keyed on the input side to factor out.  (The merged claim  *)
(* [EchoOut.ecl] and its read step [EchoOut.ecl_step_read] are ONE ANSWER  *)
(* to this AU -- [EchoOut.ecl_step_read]'s premise is [ConsLog.read_ok]    *)
(* and its conclusion is [ConsLog.cons_step _ (EvRead ws)] -- and they are *)
(* wired to nothing yet; the arm does not wait on them.)                   *)
(*                                                                        *)
(* WHAT THE CONTENT POST IS.  [uread_cons_ans] below: the delivered bytes  *)
(* are the ring's committed sequence at the cursor the call ran at, and    *)
(* the window the call CONSUMED -- [ws], the claim's next input segment -- *)
(* is that same sequence read to the bound [ConsoleInv.cons_swallow]       *)
(* extends to, with [Rin ws] the caller's own reading of it.  Everything   *)
(* echo-specific ([EchoDisc.echo_line] at sh's count, the era's bounds)    *)
(* is derived from [Rin ws] by the caller and lives in [UShLine].          *)
(*                                                                        *)
(* THE DEPOSIT STAYS LEDGER-FIXED ([UkRun.udepwf_std]): a console read is  *)
(* about a STANDARD stream, so the arm is readable off the caller's own    *)
(* record of the low [NSTD] slots -- which is the one place the file arm   *)
(* differs (an opened file is never a standard stream, so it fixes the     *)
(* STATE its handle names instead).  The descriptor INDEX is a parameter   *)
(* and not 0: nothing about this arm is about fd 0, and sh instantiates.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes ObsTrace.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPtTree.         (* [uva_wmapped] *)
Require Import UmodeArith.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkReadRows.         (* the shared key-level rows *)
Require Import SpecFileread.       (* [fileread_in] / [console_receipt] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import AppInv.             (* [app_rdcred] *)
Require Import FsCfg.              (* [fsc_cons] *)
Require Import ConsoleInv.         (* [cons_acc] / [cons_window] / [CONSOLE] *)
Require Import WpUart.             (* [cons_read_pay] -- the console history's AU *)
Require Import UartNames.          (* [cons_names] *)
Require Import UserConsole.        (* [ucons_stored_lb] / [ucons_swallow] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkReadCons.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* THE PROGRAM'S SUPPLY CLASS IS GENERALIZED and not resolved here: the
     kernel's own instance is [UexecExecInst.uprogSG_gen] and a program
     whose numbers are free runs at [uprogSG_free], and the two are NOT
     convertible ([UShLine.v]'s header, the two-instances wedge).  A leaf
     that fixes one cannot be applied by a program at the other. *)
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* AT THE CLASS'S OWN FAMILY TYPE, not at [xfam] ([UkReadRows]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument is
     checked before the instance evar is resolved and so does not
     convert. *)
  Definition read_cons_fam (Q : Z -> iProp Σ) (Rd : nat -> nat -> iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ) : sfam :=
    xfam_rd Q Rd Rin.

  (* =================================================================== *)
  (*  2.  THE DEPOSIT'S SUPPLIER: THE RING, AND THE INPUT QUEUE'S AU       *)
  (* =================================================================== *)
  (* The kernel threads the caller's exit payload [P] through every arm of
     [SpecFileread.fileread_in] and the console arm returns it INSIDE what
     the caller asked to be told; at this leaf [P] is [True], so the one
     step between the caller's own [cons_acc] and the arm's is framing a
     unit. *)
  Lemma cons_acc_triv (cn : cons_names) (Wd : iProp Σ)
      (Rd : nat -> nat -> iProp Σ) :
    cons_acc cn Wd Rd -∗ cons_acc cn Wd (fun cur dc => True ∗ Rd cur dc).
  Proof using .
    rewrite /cons_acc. iIntros "[Hl | Hr]".
    - iDestruct "Hl" as (n) "[Hrd Hw]". iLeft. iExists n. iFrame "Hrd".
      iIntros (cur dc) "Hout". iMod ("Hw" with "Hout") as "HR".
      iModIntro. by iFrame "HR".
    - iDestruct "Hr" as "[#Hc HR]". iRight. iFrame "Hc".
      iIntros (cur dc). iMod ("HR" $! cur dc) as "HR". iModIntro.
      by iFrame "HR".
  Qed.

  (* THE WHOLE PRICE OF A CONSOLE READ, and it is two resources the PROGRAM
     owns and understands (design/user-read.md section 1): its console
     position, and one atomic update on the console history's input queue.
     A caller that wants to be told nothing supplies the generic pair
     ([ConsoleInv.cons_acc_cred] and [WpUart.cons_read_pay_triv]) and is
     told nothing. *)
  Lemma udepwf_std_read_cons (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (l : list fdstate) (fd : nat) (wr : bool)
      (Rd : nat -> nat -> iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    cons_acc fsc_cons app_rdcred Rd -∗
    cons_read_pay (S gen_id) Rin -∗
    udepwf_std N m pc USYS_read (read_cons_fam (ukn_pay N) Rd Rin) l.
  Proof using .
    intros Ha0 Hlt Hl0. iIntros "Hacc Hlink".
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot (read_cons_fam (ukn_pay N) Rd Rin)
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a2_idx) fdv
              (tf_of_arg0 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)).
    rewrite (std_fd_st_of_key (m !!! Regidx a0_idx) fdv l fd
               (FdOpen true wr (FdDevice CONSOLE)) Ha0 Hlt Htake Hl0).
    cbn [read_cons_fam xfam_rd rf_F rf_ret rf_in kf_xpay].
    rewrite /fileread_in.
    destruct (decide (CONSOLE = CONSOLE)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iIntros "_". iSplitL "Hacc";
      [ iApply (cons_acc_triv with "Hacc") | iExact "Hlink" ].
  Qed.

  (* =================================================================== *)
  (*  3.  THE CONTENT POST                                                *)
  (* =================================================================== *)
  (* THE WINDOW ARM, with the receipt's two guarded rows already
     DISCHARGED: the per-byte ledger's linearity guard by the leaf's own
     resume-image bridge, and [ConsoleInv.cons_swallow]'s copy-out-fault
     disjunct by the leaf's writable-mapped row (the caller owns its
     buffer, so the destination cannot fault) -- which is why the reason is
     at [False] here and at [~ uva_wmapped ...] in the kernel's own. *)
  Definition uread_cons_win (cnm : cons_names)
      (Rin : list (list mobs * bv 8) -> iProp Σ)
      (cur dd dc : nat) (g : nat -> bv 8) (hs : list (list mobs)) : iProp Σ :=
    (∃ sl : list (list mobs * bv 8),
       ⌜cons_chain sl⌝ ∗ ucons_stored_lb cnm sl ∗
       ⌜cons_window sl cur dd g hs⌝ ∗
       ucons_swallow cnm False sl dd dc ∗ ⌜(dd <= dc)%nat⌝ ∗
       (* THE INPUT SEGMENT THE CALL CONSUMED -- the claim's [ws], read out
          of the ring at the same cursor, [dc] entries with the [dd]
          delivered ones a prefix of them. *)
       ∃ sl' ws : list (list mobs * bv 8),
         ucons_stored_lb cnm sl' ∗ ⌜sl `prefix_of` sl'⌝ ∗
         ⌜length sl' = (cur + dc)%nat⌝ ∗ ⌜length ws = dc⌝ ∗
         ⌜forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (cur + j)%nat⌝ ∗
         Rin ws)%I.

  (* ...AND THE ANSWER.  [cur] is EXISTENTIAL and [Rd cur dc] is what pins
     it: a lease holder's [Rd] returns [⌜cur = its own n⌝], a caller that
     tracks nothing returns [True] and the window is just a window
     ([SpecFileread.console_receipt]'s own note).  The RIGHT disjunct is
     the ring's credential -- a tokenless reader popped while the call
     slept -- which is the kernel's arm and not a weakening.  It still
     says WHERE THE BYTES CAME FROM (lane seccomp S2k, the kernel's
     [SpecFileread.console_receipt] relayed): a bound [sl] on the ring's
     stored sequence, its order, and for each delivered byte a stored
     position at or after [cur] with that byte's history -- no window, and
     no promise that the positions increase. *)
  Definition uread_cons_ans (cnm : cons_names)
      (Rd : nat -> nat -> iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ)
      (r : mword 64) (cap : nat) (g : nat -> bv 8) : iProp Σ :=
    (∃ (dd dc cur : nat) (hs : list (list mobs)),
       ⌜Z.of_nat dd = bv_unsigned r⌝ ∗ ⌜(dd <= cap)%nat⌝ ∗
       (* THE CURSOR'S TWO CONTROL-FLOW ROWS, at the caller's own count *)
       ⌜dd = cap -> dc = dd⌝ ∗
       ⌜dd = 0%nat -> (0 < cap)%nat -> dc = (dd + 1)%nat⌝ ∗
       ([∗ list] hh ∈ hs, riscv_rx_tag hh) ∗
       Rd cur dc ∗
       (uread_cons_win cnm Rin cur dd dc g hs
        ∨ cons_dirty_cred app_rdcred
          ∗ ∃ sl : list (list mobs * bv 8),
              ucons_stored_lb cnm sl ∗ ⌜cons_chain sl⌝ ∗
              ⌜cons_placed sl cur dd hs⌝))%I.

  (* =================================================================== *)
  (*  4.  THE LEAF                                                        *)
  (* =================================================================== *)
  Lemma wp_uk_ecall_read_cons (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (a : Z) (k cap : nat) (f : nat -> bv 8) (avail : nat)
      (l : list fdstate) (fd : nat) (wr : bool)
      (Rd : nat -> nat -> iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ) :
    usysno m = USYS_read ->
    (* THE DESCRIPTOR IS A STANDARD STREAM THE CALLER'S LEDGER NAMES, and
       the ledger says it is the console *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    uint (m !!! Regidx a1_idx) = a ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (* the kernel answers the SIGNED 32-bit count, so the request the caller
       made is the request file.c read only below the sign boundary *)
    (Z.of_nat cap < 2 ^ 31)%Z ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    ustd (ukn_fd N) l -∗
    ubytes (ukn_d N) a k f -∗
    (* THE PAYMENT: the ring's, and ONE ATOMIC UPDATE ON THE CONSOLE
       HISTORY'S INPUT QUEUE *)
    cons_acc fsc_cons app_rdcred Rd -∗
    cons_read_pay (S gen_id) Rin -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ustd (ukn_fd N) l -∗
       uread_cons_ans fsc_cons Rd Rin r cap g -∗
       ubytes (ukn_d N) a k g -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hfdlt Hl0 Ha1 Ha2 Hcapk Hcap31 Hal.
    iIntros "#Hi Hrun Hstd Hbuf Hacc Hlink Hcont".
    subst a.
    pose proof (uread_count_le (m !!! Regidx a2_idx) cap Ha2) as Hbnd.
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap)
      by exact (uread_count_is_cap (m !!! Regidx a2_idx) cap Ha2 Hcap31).
    change (2 ^ 31)%Z with 2147483648%Z in Hcap31.
    iDestruct (udepwf_std_read_cons N m pc l fd wr Rd Rin Ha0 Hfdlt Hl0
                 with "Hacc Hlink") as "Hsb".
    iApply (wp_uk_ecall_read_recv N h m pc
              (bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                          : mword 32))
              k f avail (read_cons_fam (ukn_pay N) Rd Rin) l
              Hn eq_refl ltac:(lia) Hal
              with "Hi Hrun Hsb Hstd Hbuf").
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %HM %Hnf %Harg0 %Harg1 %Harg2 %Htake %Hlz %Hlive
       Hstd Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot (read_cons_fam (ukn_pay N) Rd Rin) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                 Harg0 Harg1 Harg2 eq_refl with "Hpost")
      as "[%Hfrret Hpost']".
    iDestruct "Hpost'" as (P) "(%Hperm & %Hwf & %Hlazy & Hrec)".
    rewrite Hcnt in Hfrret.
    (* THE ANSWER IS NOT -1 AT AN OPEN READABLE CONSOLE DESCRIPTOR
       (lane TRAP-ROWS, T2(iii)) *)
    assert (Hfdw : uvis_fd W !! fd
                   = Some (FdOpen true wr (FdDevice CONSOLE))).
    { pose proof Hl0 as Hl0'. rewrite <- Htake in Hl0'.
      rewrite lookup_take in Hl0'; [ exact Hl0' | lia ]. }
    assert (Hcgz : (0 <= bv_signed
                      (trunc32 (tf_w (uvis_tf W) (tf_arg_idx 2))))%Z).
    { rewrite Harg2. rewrite /sys_rw_count in Hcnt. lia. }
    assert (Hargfd : usys_argfd (uvis_tf W) = Z.of_nat fd).
    { rewrite /usys_argfd.
      replace (uvis_tf W !!! tf_arg_idx 0) with (m !!! Regidx a0_idx)
        by (symmetry; exact Harg0).
      exact Ha0. }
    assert (Hne1 : r <> (mword_of_int (-1) : mword 64)).
    { apply (proj1 Hlive eq_refl Hcgz wr).
      - rewrite Hargfd. unfold NSTD, NOFILE in *. lia.
      - rewrite Hargfd Nat2Z.id. exact Hfdw. }
    iEval (rewrite (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l fd
                      (FdOpen true wr (FdDevice CONSOLE)) Ha0 Hfdlt Htake Hl0)
                   /fileread_extra_core;
           cbn [read_cons_fam xfam_rd rf_F rf_ret rf_in kf_xpay]) in "Hrec".
    destruct (decide (CONSOLE = CONSOLE)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    pose proof (Hlazy Hlz) as Hlf.
    iEval (rewrite /console_receipt) in "Hrec".
    iDestruct "Hrec" as "[(%Hm1 & _ & _) | Hw]";
      [ exfalso; exact (Hne1 Hm1) | ].
    iDestruct "Hw" as (dd dc cur hs sl)
      "(%Hdr & %Hdmax & %Hb1 & %Hb4 & %Hhl & %Hled & #Htags & #Hlb
        & Hwin & Hrd)".
    destruct Hfrret as [Hm1 | (i0 & Hri & Hi0)];
      [ exfalso; exact (Hne1 Hm1) | ].
    assert (Hi0u : bv_unsigned r = i0).
    { rewrite Hri. rewrite <- uint_unsigned.
      apply uint_moi. unfold Z64. lia. }
    assert (Hddcap : (dd <= cap)%nat) by lia.
    iDestruct "Hwin"
      as "[(%Hwj & %Hsl & %Hch & #Hsw & Hbnd) | (#Hdirty & %Hchd & %Hpld)]";
      last first.
    { (* a tokenless reader popped while the call slept: the ring's
         credential is the answer, and nothing is claimed about the
         window *)
      iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hrd] Hbuf Hrun");
        [ lia | exact Hgf | ].
      rewrite /uread_cons_ans. iExists dd, dc, cur, hs.
      iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      iSplitR; [ iPureIntro; intros Hdc; apply Hb1;
                 rewrite Hcnt Hdc; lia | ].
      iSplitR; [ iPureIntro; intros Hd0 Hc0; apply Hb4;
                 [ exact Hd0 | rewrite Hcnt; lia ] | ].
      iSplitR; [ iExact "Htags" | ]. iFrame "Hrd".
      iRight. iSplitR; [ iExact "Hdirty" | ]. iExists sl.
      iSplitR; [ rewrite ucons_stored_lb_eq; iExact "Hlb" | ].
      iSplitR; [ by iPureIntro | by iPureIntro ]. }
    iDestruct "Hbnd" as (sl2 ws)
      "(#Hlb2 & %Hpre2 & %Hlen2 & %Hlws & %Hwsj & Hrin)".
    (* THE WINDOW, ASSEMBLED: the receipt's ORDER clause and its per-byte
       LEDGER are about the same bytes, joined by [obs_ends_in_inj] (a
       history names at most one byte) and by the leaf's resume-image
       bridge. *)
    assert (Hwinf : cons_window sl cur dd g hs).
    { split_and!; [ lia | exact Hhl | ].
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
    assert (Hddc : (dd <= dc)%nat).
    { pose proof (prefix_length _ _ Hpre2) as Hle. lia. }
    iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hrd Hrin] Hbuf Hrun");
      [ lia | exact Hgf | ].
    rewrite /uread_cons_ans. iExists dd, dc, cur, hs.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ iPureIntro; intros Hdc; apply Hb1; rewrite Hcnt Hdc; lia | ].
    iSplitR; [ iPureIntro; intros Hd0 Hc0; apply Hb4;
               [ exact Hd0 | rewrite Hcnt; lia ] | ].
    iSplitR; [ iExact "Htags" | ]. iFrame "Hrd".
    iLeft. rewrite /uread_cons_win. iExists sl.
    iSplitR; [ by iPureIntro | ].
    iSplitR; [ rewrite ucons_stored_lb_eq; iExact "Hlb" | ].
    iSplitR; [ by iPureIntro | ].
    iSplitR "Hrin"; last first.
    { iSplitR; [ by iPureIntro | ]. iExists sl2, ws.
      iSplitR; [ rewrite ucons_stored_lb_eq; iExact "Hlb2" | ].
      iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
      iExact "Hrin". }
    (* THE SWALLOW'S COPY-OUT REASON IS REFUTED HERE, off the leaf's
       writable-mapped row: the caller owns the byte one past the run. *)
    destruct (Nat.eq_dec dd cap) as [Hde | Hdne].
    { assert (Hdcdd : dc = dd) by (apply Hb1; rewrite Hcnt Hde; lia).
      rewrite Hdcdd. iApply ucons_swallow_refl. }
    iApply (ucons_swallow_mono fsc_cons
              (~ uva_wmapped P (uint (add_vec_int (m !!! Regidx a1_idx)
                                        (Z.of_nat dd)))) False sl dd dc
              ltac:(intro Hno;
                    exact (Hno (Hnf P dd Hwf Hperm Hlf ltac:(lia))))
              with "[]").
    rewrite ucons_swallow_eq. iExact "Hsw".
  Qed.

End UkReadCons.
