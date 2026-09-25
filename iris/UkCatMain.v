(* ===================================================================== *)
(* UkCatMain.v -- cat's main() and start().                               *)
(*                                                                        *)
(*   main(argc, argv)                                                     *)
(*     if (argc <= 1) { cat(0); exit(0); }                                *)
(*     for (i = 1; i < argc; i++) {                                       *)
(*       if ((fd = open(argv[i], O_RDONLY)) < 0) {                        *)
(*         fprintf(2, "cat: cannot open %s\n", argv[i]); exit(1); }       *)
(*       cat(fd); close(fd);                                              *)
(*     }                                                                  *)
(*     exit(0);                                                           *)
(*                                                                        *)
(* Every path out of main is an [exit], so main has NO continuation and    *)
(* never restores the five registers it spilled -- which is why the loop   *)
(* invariant here names three registers and not a callee-saved set.        *)
(*                                                                        *)
(* The walk over argv is the [addiw]/[slli]/[srli] idiom the compiler uses *)
(* for `&argv[argc]`, the same one echo's main has: s2 runs from &argv[1]  *)
(* to s3 = &argv[argc], eight bytes a turn.                                *)
(*                                                                        *)
(* One precondition is not derivable from [uargv] and has to be asked for: *)
(* that no argv pointer is null.  vprintf's '%s' arm has a "(null)" branch *)
(* that reads its replacement out of .rodata rather than the data half,    *)
(* and that branch is excluded here rather than walked.                    *)
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
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeCat.
Require Import CtxIdDefs.
Require User.CatSyms User.CatInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkCat.
Require Import UkCatLit.
Require Import UkCatFprintf.
Require Import UkCatCat.
Require Import UkRunBr.

Require Import FdSlots.   (* [fdstate] -- what a handle names *)
Require Import VcGen.     (* [trunc32_mword_of_int] -- a0 read as a C [int] *)
Require Import RiscvExtras. (* [moi32_unsigned]/[bvw32_small] *)
Require Import ProcGeom.  (* [NOFILE] *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkCatMain.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT PAYLOAD DOES NOT READ ITS STATUS (lane CAT-WALK,
     W2), as a CLASS so that it reaches the exit ecall without an argument
     at every call site ([UkRun.ukn_const]).  It used to be [ukn_triv] --
     "cat owes its parent nothing" -- which pinned the payload at [True]
     and so made cat's exit incapable of handing the shell the deed
     fraction, the advanced console credential or the filed alternative.
     What cat actually needs of
     its own payload is only that its two exits -- 0 on the content arm,
     1 on the diagnostic arm -- owe the SAME thing, which is exactly this
     class; echo's walk is stated at it for the same reason. *)
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

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).

  (* the "cat: cannot open %s\n" literal, and everything the '%s' walk
     wants to know about it -- all of it decided by [vm_compute]. *)
  Definition cm_msg : Z := 0x9e0.
  Definition cm_msg_len : nat := 20%nat.
  Definition cm_msg_q : nat := 17%nat.
  Definition cm_lit : nat -> mword 8 := cat_lit cm_msg.

  (* --------------------------------------------------------------------- *)
  (* WHAT SURVIVES A TURN OF THE LOOP.  Three registers: the frame pointer  *)
  (* main never moves, the cursor into argv, and the end it stops at.       *)
  (* --------------------------------------------------------------------- *)
  Definition cm_inv (sp0 : mword 64) (av : Z) (nargs i : nat)
      (m : regfile) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6)) /\
    m !!! Regidx s2_idx = mword_of_int (av + 8 * Z.of_nat i) /\
    m !!! Regidx s3_idx = mword_of_int (av + 8 * Z.of_nat nargs).

  (* which registers a step may write without disturbing it *)
  Definition cm_writable (r : mword 5) : bool :=
    negb (Z.eqb (uint r) 2 || Z.eqb (uint r) 18 || Z.eqb (uint r) 19).

  Lemma cm_writable_ne (r : mword 5) (z : Z) :
    cm_writable r = true -> (z = 2 \/ z = 18 \/ z = 19) -> uint r <> z.
  Proof using .
    unfold cm_writable. intro H. apply negb_true_iff in H.
    rewrite !orb_false_iff in H. destruct H as [[H1 H2] H3].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2. apply Z.eqb_neq in H3.
    intros Hz He. rewrite He in H1, H2, H3. lia.
  Qed.

  Lemma cm_inv_upd (sp0 : mword 64) (av : Z) (nargs i : nat) (m : regfile)
      (r : mword 5) (v : mword 64) :
    cm_writable r = true ->
    cm_inv sp0 av nargs i m ->
    cm_inv sp0 av nargs i (<[Regidx r := regval_into_reg v]> m).
  Proof using .
    intros Hw (Hsp & Hs2 & Hs3). unfold cm_inv.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cm_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cm_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cm_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    repeat (split; [ assumption | ]). assumption.
  Qed.

  Lemma cm_inv_call (sp0 : mword 64) (av : Z) (nargs i : nat) (m m' : regfile) :
    ucallee_saved m m' ->
    cm_inv sp0 av nargs i m -> cm_inv sp0 av nargs i m'.
  Proof using .
    intros Hcs (Hsp & Hs2 & Hs3). unfold cm_inv.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]). assumption.
  Qed.

  (* ===================================================================== *)
  (* THE LITERAL "cat: cannot open %s\n" -- twenty bytes at 0x9e0, with a  *)
  (* '%' at 17 and an 's' at 18.  [cat_lit_ok] cannot be used on it: that   *)
  (* predicate says a literal has NO directive in it, which is exactly what *)
  (* this one is not.  What the '%s' walk wants instead is the same NUL     *)
  (* discipline plus the three byte values, and all of it is decided.       *)
  (* ===================================================================== *)
  Definition cm_ok : bool :=
    forallb (fun j => match cat_ro !! (cm_msg + Z.of_nat j)%Z with
                      | Some b => negb (Z.eqb (bv_unsigned b) 0)
                      | None => false
                      end)
            (seq 0 cm_msg_len)
    && match cat_ro !! (cm_msg + Z.of_nat cm_msg_len)%Z with
       | Some b => Z.eqb (bv_unsigned b) 0
       | None => false
       end.

  Definition cm_nopct : bool :=
    forallb (fun j => Nat.eqb j cm_msg_q
                      || negb (Z.eqb (bv_unsigned (cm_lit j)) 37))
            (seq 0 cm_msg_len).

  Lemma cm_nopct_ok (j : nat) :
    (j < cm_msg_len)%nat -> j <> cm_msg_q -> bv_unsigned (cm_lit j) <> 37.
  Proof using .
    intros Hj Hne.
    assert (H : cm_nopct = true) by (vm_compute; reflexivity).
    unfold cm_nopct in H. rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    apply orb_true_iff in H as [H | H].
    - apply Nat.eqb_eq in H. exfalso. exact (Hne H).
    - apply negb_true_iff, Z.eqb_neq in H. exact H.
  Qed.

  Lemma cm_str : cat_rodata γt -∗ utext_str γt cm_msg cm_msg_len cm_lit.
  Proof using .
    assert (Hok : cm_ok = true) by (vm_compute; reflexivity).
    unfold cm_ok in Hok. apply andb_true_iff in Hok as [Hbody Hnul].
    rewrite forallb_forall in Hbody.
    iIntros "#Hro". rewrite /cat_rodata.
    iApply (utext_str_of_img γt cat_ro cm_msg cm_msg_len cm_lit).
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold cm_lit, cat_lit.
      destruct (cat_ro !! (cm_msg + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply negb_true_iff, Z.eqb_neq in Hbody.
      intro He. apply Hbody.
      assert (Hbe : b = ubyte0) by (rewrite <- He; reflexivity).
      rewrite Hbe. vm_compute. reflexivity.
    - unfold cm_msg_len. lia.
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold cm_lit, cat_lit.
      destruct (cat_ro !! (cm_msg + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      reflexivity.
    - destruct (cat_ro !! (cm_msg + Z.of_nat cm_msg_len)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply Z.eqb_eq in Hnul. f_equal. apply bv_eq. rewrite Hnul.
      vm_compute. reflexivity.
    - iExact "Hro".
  Qed.

  (* where the heap's own bounds come from *)
  Local Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun N h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(_ & _ & _ & _ & Hh & _ & _ & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_uword_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (w : mword 64) :
    urun N h m pc avail -∗ uwordq γd dq a w -∗
    ⌜ 0 <= a /\ a + 8 <= 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hw". rewrite /uwordq /ubytesq.
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 0%nat 0%nat ltac:(reflexivity)
                 with "Hw") as "[H0 Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun H0") as %Hb0.
    iDestruct ("Hcl" with "H0") as "Hw".
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 7%nat 7%nat ltac:(reflexivity)
                 with "Hw") as "[H7 _]".
    iDestruct (urun_ubyte_bnd with "Hrun H7") as %Hb7.
    iPureIntro. lia.
  Qed.

  (* ===================================================================== *)
  (* WHAT main SPENDS (lane CAT-WALK, W1).                                  *)
  (*                                                                       *)
  (* main's turn is open -> cat -> close, or open -> diagnostic -> exit,    *)
  (* and the payment has that shape exactly: an OPEN obligation whose       *)
  (* output is an additive pair of the two arms the [bltz] at 0xb2 chooses  *)
  (* between.  The success arm names the descriptor, which is what lets a   *)
  (* deed-aware payer hand over a round for the file's own content          *)
  (* ([UkCatCat.kcat_round]) and the close that spends its handle.          *)
  (* ===================================================================== *)

  (* THE `cat: cannot open %s` RUN, at fd 2, ending in the exit hole at
     status 1 (program-specs cut 3; it used to end in the payload).
     Three runs and not one, because that is what
     [UkCatFprintf.wp_kcat_fprintf_s] prints: the format up to the
     directive, the argument's own bytes, and the format after it. *)
  Definition kcat_dg_open (g : uarg) : iProp Σ :=
    (∃ Cm1 Cm2 : iProp Σ,
       UkCat.kcat_pay_seq N (mword_of_int 2) cm_lit 0%nat cm_msg_q emp%I Cm1
       ∗ UkCat.kcat_pay_seq N (mword_of_int 2) (ua_bytes g) 0%nat (ua_len g)
           Cm1 Cm2
       ∗ UkCat.kcat_pay_seq N (mword_of_int 2) cm_lit (S (S cm_msg_q))
           (cm_msg_len - S (S cm_msg_q))%nat Cm2 (UkCat.kcat_exit N 1))%I.

  (* ONE CALL OF cat(fd): a round law, the cursor it starts at, and what
     the round's normal exit leaves. *)
  Definition kcat_run0 (fdv : mword 64) (Co : iProp Σ) : iProp Σ :=
    (∃ I Cend : iProp Σ,
       kcat_round N fdv I Cend ∗ I ∗ (Cend -∗ Co))%I.

  (* ONE TURN OF main's LOOP. *)
  Definition kcat_file (g : uarg) (Ci Co : iProp Σ) : iProp Σ :=
    UkCat.kcat_o N (mword_of_int (ua_ptr g)) Ci
      (fun ret : mword 64 =>
         ((⌜bv_signed ret < 0⌝ -∗ kcat_dg_open g)
          ∧ (⌜0 <= bv_signed ret⌝ -∗
               ∃ (fd : nat) (Cm : iProp Σ),
                 ⌜ret = (mword_of_int (Z.of_nat fd) : mword 64)⌝
                 ∗ ⌜(fd < NOFILE)%nat⌝
                 ∗ kcat_run0 (mword_of_int (Z.of_nat fd)) Cm
                 ∗ UkCat.kcat_cl N fd Cm Co))%I).

  (* ...and the run of turns the loop takes, [UkEcho.kecho_pay]'s shape at
     argv. *)
  Fixpoint kcat_pay (args : list uarg) (i k : nat) (Ci Cend : iProp Σ)
    : iProp Σ :=
    match k with
    | O => (Ci -∗ Cend)%I
    | S k' => (∃ (g : uarg) (Cm : iProp Σ),
                 ⌜args !! i = Some g⌝ ∗ kcat_file g Ci Cm
                 ∗ kcat_pay args (S i) k' Cm Cend)%I
    end.

  (* ...at main's own entry, where [argc <= 1] cats the standard input
     instead.  An ADDITIVE conjunction and not a match on the count: main
     decides the arm by a branch and the supplier answers both, one of
     them vacuously ([UkEcho.kecho_pay_all]'s shape). *)
  Definition kcat_pay_all (args : list uarg) (Ci Cend : iProp Σ) : iProp Σ :=
    ((⌜(length args <= 1)%nat⌝ -∗
        ∃ Cm : iProp Σ, kcat_run0 (mword_of_int 0) Cm ∗ (Ci ∗ Cm -∗ Cend))
     ∧ (⌜(2 <= length args)%nat⌝ -∗
          kcat_pay args 1%nat (length args - 1)%nat Ci Cend))%I.

  (* ===================================================================== *)
  (* THE FREE CHAIN (lane CAT-WALK, W1).                                    *)
  (*                                                                       *)
  (* [UEchoKernel.echo_uexec_slot]'s pattern: the whole of what the landed,
     claim-free walk said is ONE corollary at the four free laws, so a
     program entering on the generic path instantiates the restated walk
     in a line and gets the old statement back.  NOTHING OUTSIDE
     [UkCat*.v] requires cat's walk today, so there is no caller to fix --
     but this is also the VACUITY GUARD: it witnesses that the payments
     [wp_kcat_start] now asks for are satisfiable, and hence that the
     restated walk is not vacuously true.                                  *)
  (* ===================================================================== *)
  Lemma kcat_file_of_law (g : uarg) (l : list fdstate) :
    fd_lowest_closed l = None ->
    (* NO [udepw_law 21] (survey R4, lane SUP-ONE): cat closes the
       descriptor its own open returned, and the leaf exports
       [FdSlots.fdst_nopipe] for it, so the close is FREE. *)
    □ (ukn_pay N (-1)) -∗
    udepw_law 5 -∗ udepw_law 15 -∗ udepw_law 16 -∗
    kcat_file g (ustd γfd l) (ustd γfd l).
  Proof using Hpay.
    intros Hnone. iIntros "#HC #Hrd #Hop #Hwr".
    iAssert (□ UkCat.kcat_exit N 1)%I as "#HC1".
    { iModIntro. iApply (UkCat.kcat_exit_of_pay with "HC"). }
    assert (Hm1s : bv_signed (mword_of_int (-1) : mword 64) = -1)
      by (vm_compute; reflexivity).
    rewrite /kcat_file.
    iApply (UkCat.kcat_o_mono N (mword_of_int (ua_ptr g)) (ustd γfd l)
              with "[] []"); last first.
    { iApply (UkCat.kcat_o_of_law N (mword_of_int (ua_ptr g)) l Hnone
                with "Hop"). }
    iIntros (ret) "[Harm Hstd]". iSplit.
    - (* the open failed: the diagnostic run, then the exit *)
      iIntros "_". rewrite /kcat_dg_open.
      iExists emp%I, emp%I. iSplitR; [| iSplitR ].
      + iApply (UkCat.kcat_pay_seq_of_law N (mword_of_int 2) cm_lit
                  cm_msg_q emp%I 0%nat with "[] Hwr"). by iIntros "!>".
      + iApply (UkCat.kcat_pay_seq_of_law N (mword_of_int 2) (ua_bytes g)
                  (ua_len g) emp%I 0%nat with "[] Hwr"). by iIntros "!>".
      + iApply (UkCat.kcat_pay_seq_of_law N (mword_of_int 2) cm_lit
                  (cm_msg_len - S (S cm_msg_q))%nat (UkCat.kcat_exit N 1)
                  (S (S cm_msg_q)) with "HC1 Hwr").
    - (* it succeeded: a round for the content, then the close *)
      iIntros "%Hpos".
      iDestruct "Harm" as "[Hok | %Hm1]"; last first.
      { exfalso. rewrite Hm1 Hm1s in Hpos. lia. }
      iDestruct "Hok" as (fd rd wr t) "[(%Hr & %Hlt & %Hnp) Hh]".
      iExists fd, emp%I. iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iSplitR "Hh Hstd".
      + rewrite /kcat_run0. iExists emp%I, emp%I. iSplitR; [| iSplitR ].
        * iApply (kcat_round_of_law N (mword_of_int (Z.of_nat fd))
                    with "HC Hrd Hwr").
        * done.
        * by iIntros "_".
      + iApply (UkCat.kcat_cl_of_dep N fd (FdOpen rd wr t) emp%I
                  (ustd γfd l) with "[] Hh [Hstd]").
        { iApply (UkCat.kcat_cldep_nopipe N (FdOpen rd wr t) Hnp). }
        { iIntros "_". iExact "Hstd". }
  Qed.

  Lemma kcat_pay_of_law (args : list uarg) (l : list fdstate) (k : nat) :
    fd_lowest_closed l = None ->
    forall i : nat, (i + k <= length args)%nat ->
      □ (ukn_pay N (-1)) -∗
      udepw_law 5 -∗ udepw_law 15 -∗ udepw_law 16 -∗
      kcat_pay args i k (ustd γfd l) (ukn_pay N (-1)).
  Proof using Hpay.
    intros Hnone. induction k as [| k IH]; intros i Hik;
      iIntros "#HC #Hrd #Hop #Hwr".
    - cbn [kcat_pay]. iIntros "_". iExact "HC".
    - cbn [kcat_pay].
      destruct (lookup_lt_is_Some_2 args i ltac:(lia)) as [g Hg].
      iExists g, (ustd γfd l). iSplitR; [ by iPureIntro | ]. iSplitR.
      + iApply (kcat_file_of_law g l Hnone with "HC Hrd Hop Hwr").
      + iApply (IH (S i) ltac:(lia) with "HC Hrd Hop Hwr").
  Qed.

  Lemma kcat_pay_all_of_law (args : list uarg) (l : list fdstate) :
    fd_lowest_closed l = None ->
    □ (ukn_pay N (-1)) -∗
    udepw_law 5 -∗ udepw_law 15 -∗ udepw_law 16 -∗
    kcat_pay_all args (ustd γfd l) (ukn_pay N (-1)).
  Proof using Hpay.
    intros Hnone. iIntros "#HC #Hrd #Hop #Hwr".
    rewrite /kcat_pay_all. iSplit.
    - iIntros "_". iExists emp%I. iSplitR.
      + rewrite /kcat_run0. iExists emp%I, emp%I. iSplitR; [| iSplitR ].
        * iApply (kcat_round_of_law N (mword_of_int 0) with "HC Hrd Hwr").
        * done.
        * by iIntros "_".
      + iIntros "_". iExact "HC".
    - iIntros "%Hge".
      iApply (kcat_pay_of_law args l (length args - 1)%nat Hnone
                1%nat ltac:(lia) with "HC Hrd Hop Hwr").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE OPEN-FAILURE ARM, 0xde -> exit.                                    *)
  (*                                                                        *)
  (*   ld a2,0(s2) ; auipc/addi a1,<msg> ; li a0,2 ; jal fprintf            *)
  (*   li a0,1 ; jal exit                                                   *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_main_die (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (i : nat) (g : uarg) (n : nat) :
    args !! i = Some g ->
    ua_ptr g <> 0 ->
    m !!! Regidx s2_idx = mword_of_int (av + 8 * Z.of_nat i) ->
    kcat_dg_open g -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    urun N h m (mword_of_int 0xde) (10 + (12 + (4 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hi Hnz Hs2.
    iIntros "Hdg #Hcode #Hro #Hargv Hrun".
    iDestruct "Hdg" as (Cm1 Cm2) "(Hdg1 & Hdg2 & Hdg3)".
    iDestruct (cm_str with "Hro") as "#Hstr".
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc].
    iDestruct (uargv_acc γd av args i g Hi with "Hargv") as "[[#Hw #Hsstr] _]".
    iDestruct (urun_uword_bnd with "Hrun Hw") as %[Hlo0 Hhi0].
    destruct cat_syms_pins
      as (_ & _ & _ & Hfprintf & _ & _ & _ & _ & _ & _ & Hexit).
    (* ---- 0xde  ld a2,0(s2) -- argv[i] ---- *)
    assert (Haddr : (av + 8 * Z.of_nat i)%Z
                    = uint (m !!! Regidx s2_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs2 (uint_moi (av + 8 * Z.of_nat i)
                     ltac:(unfold Z64; lia)).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    assert (Hal8 : (av + 8 * Z.of_nat i) mod 8 = 0).
    { rewrite Z.add_mod; [ | lia ]. rewrite Hal Z.mul_comm Z_mod_mult.
      reflexivity. }
    iApply (wp_uk_ld N h m (mword_of_int 0xde)
              (mword_of_int 0 : mword 12) s2_idx a2_idx DfracDiscarded
              (av + 8 * Z.of_nat i) (mword_of_int (ua_ptr g))
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hal8 ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_cat_de with "Hcode"). }
    assert (Ede : add_vec_int (mword_of_int 0xde : mword 64) 4
                  = mword_of_int 0xe2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ede.
    iIntros "_" (h1) "Hrun".
    set (m1 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr g) : mword 64)]> m).
    (* ---- 0xe2  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc N h1 m1 (mword_of_int 0xe2)
              (mword_of_int 1 : mword 20) a1_idx (mword_of_int 0x10e2)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_e2 with "Hcode"). }
    assert (Ee2 : add_vec_int (mword_of_int 0xe2 : mword 64) 4
                  = mword_of_int 0xe6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee2.
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0x10e2 : mword 64)]> m1).
    (* ---- 0xe6  addi a1,a1,-1794 -- &"cat: cannot open %s\n" ---- *)
    assert (Ea1 : add_vec (m2 !!! Regidx a1_idx)
                    (sign_extend' 64 (mword_of_int 2302 : mword 12))
                  = mword_of_int cm_msg).
    { rewrite (upd_eq m1 (Regidx a1_idx) (regval_into_reg _)).
      apply bv_eq. vm_compute. reflexivity. }
    iApply (wp_uk_addi N h2 m2 (mword_of_int 0xe6)
              (mword_of_int 2302 : mword 12) a1_idx a1_idx
              (mword_of_int cm_msg) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea1))
              with "[] Hrun").
    { iApply (uis_cat_e6 with "Hcode"). }
    assert (Ee6 : add_vec_int (mword_of_int 0xe6 : mword 64) 4
                  = mword_of_int 0xea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee6.
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int cm_msg : mword 64)]> m2).
    (* ---- 0xea  c.li a0,2 ---- *)
    iApply (wp_uk_cli N h3 m3 (mword_of_int 0xea)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_cat_ea with "Hcode"). }
    assert (Eea : add_vec_int (mword_of_int 0xea : mword 64) 2
                  = mword_of_int 0xec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eea.
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 2 : mword 6)
                       : mword 64)]> m3).
    (* ---- 0xec  jal ra,0x7d0 <fprintf> ---- *)
    iApply (wp_uk_jal N h4 m4 (mword_of_int 0xec)
              (mword_of_int 1764 : mword 21) ra_idx
              (mword_of_int CatSyms.fprintf) (mword_of_int 0xf0)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_ec with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xf0 : mword 64)]> m4).
    assert (Hra5 : m5 !!! Regidx ra_idx = (mword_of_int 0xf0 : mword 64))
      by exact (upd_eq m4 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1_5 : m5 !!! Regidx a1_idx = mword_of_int cm_msg).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3. exact (upd_eq m2 (Regidx a1_idx) (regval_into_reg _)). }
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int (ua_ptr g)).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1. exact (upd_eq m (Regidx a2_idx) (regval_into_reg _)). }
    (* ---- fprintf(2, "cat: cannot open %s\n", argv[i]) ---- *)
    (* the format's ten side conditions are PROVED HERE.  As [ltac:]s in the
       argument list every pass the elaborator made over this application
       re-ran all ten. *)
    assert (Hcm0 : 0 <= cm_msg) by (unfold cm_msg; lia).
    assert (Hcmhi : cm_msg + Z.of_nat cm_msg_len + 2 < 2 ^ 31)
      by (unfold cm_msg, cm_msg_len; lia).
    assert (Hcmq2 : (S (S cm_msg_q) < cm_msg_len)%nat)
      by (unfold cm_msg_len, cm_msg_q; lia).
    assert (Hcmpq : bv_unsigned (cm_lit cm_msg_q) = 37)
      by (unfold cm_lit, cm_msg, cm_msg_q; vm_compute; reflexivity).
    assert (Hcmps : bv_unsigned (cm_lit (S cm_msg_q)) = 115)
      by (unfold cm_lit, cm_msg, cm_msg_q; vm_compute; reflexivity).
    assert (Hcm1d : bv_unsigned (cm_lit (S (S cm_msg_q))) <> 100)
      by (unfold cm_lit, cm_msg, cm_msg_q; vm_compute; discriminate).
    assert (Hcm1u : bv_unsigned (cm_lit (S (S cm_msg_q))) <> 117)
      by (unfold cm_lit, cm_msg, cm_msg_q; vm_compute; discriminate).
    assert (Hcm1x : bv_unsigned (cm_lit (S (S cm_msg_q))) <> 120)
      by (unfold cm_lit, cm_msg, cm_msg_q; vm_compute; discriminate).
    assert (Hcm2set : (S (S (S cm_msg_q)) < cm_msg_len)%nat ->
              bv_unsigned (cm_lit (S (S (S cm_msg_q)))) <> 100 /\
              bv_unsigned (cm_lit (S (S (S cm_msg_q)))) <> 117 /\
              bv_unsigned (cm_lit (S (S (S cm_msg_q)))) <> 120)
      by (unfold cm_msg_len, cm_msg_q; intros HH; exfalso; lia).
    assert (Ha0_5d : m5 !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_eq m3 (Regidx a0_idx) (regval_into_reg _)).
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_kcat_fprintf_s N cm_msg cm_msg_len cm_msg_q cm_lit
              (ua_ptr g) (ua_len g) (ua_bytes g) h5 m5 n
              emp%I Cm1 Cm2 (UkCat.kcat_exit N 1)
              Hcm0 Hcmhi Hcmq2 Hcmpq Hcmps
              (fun j Hj Hne => cm_nopct_ok j Hj Hne)
              Hcm1d Hcm1u Hcm1x Hcm2set
              Hnz Ha1_5 Ha2_5
              with "[Hdg1] [Hdg2] [Hdg3] Hcode Hstr Hsstr [] Hrun").
    { rewrite Ha0_5d. iExact "Hdg1". }
    { rewrite Ha0_5d. iExact "Hdg2". }
    { rewrite Ha0_5d. iExact "Hdg3". }
    { done. }
    iIntros (h6 m6) "_ Hpayv Hrun".
    assert (Eret : ret_pc (m5 !!! Regidx ra_idx)
                   = (mword_of_int 0xf0 : mword 64))
      by (rewrite Hra5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* ---- 0xf0  c.li a0,1 ---- *)
    iApply (wp_uk_cli N h6 m6 (mword_of_int 0xf0)
              (mword_of_int 1 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_cat_f0 with "Hcode"). }
    assert (Ef0 : add_vec_int (mword_of_int 0xf0 : mword 64) 2
                  = mword_of_int 0xf2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ef0.
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 6)
                       : mword 64)]> m6).
    (* ---- 0xf2  jal ra,0x3ac <exit> ---- *)
    iApply (wp_uk_jal N h7 m7 (mword_of_int 0xf2)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int CatSyms.exit) (mword_of_int 0xf6)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_f2 with "Hcode"). }
    iIntros (h8) "Hrun".
    (* THE EXIT HOLE, at the status [c.li a0,1] left in a0 *)
    iApply ("Hpayv" $! h8 _ (10 + (12 + (4 + n)))%nat with "[%] Hcode Hrun").
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
    vm_compute. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* ONE FILE, 0xa6 -> 0xc2:                                                *)
  (*                                                                        *)
  (*   li a1,0 ; ld a0,0(s2) ; jal open ; mv s1,a0 ; bltz a0,<die>          *)
  (*   jal cat ; mv a0,s1 ; jal close ; addi s2,s2,8                        *)
  (*                                                                        *)
  (* [open]'s return value is unconstrained, so BOTH arms of the [bltz] are *)
  (* walked; the failing one ends in the diagnostic above and never comes   *)
  (* back, which is why it simply drops the continuation.                   *)
  (* --------------------------------------------------------------------- *)
  (* THE LEDGER RIDES THROUGH THE BODY UNCHANGED.  cat's open lands above
     the standard streams (none of them is closed, which is [Hnone]) and its
     close spends the handle that open minted, so neither touches the ledger
     -- it goes in, is spent on the open, comes back, and is handed to the
     next iteration.  It is in the statement because the OPEN needs it, not
     because the body does anything to it. *)
  (* THE LEDGER IS NOT IN THE STATEMENT ANY MORE (lane CAT-WALK, W1/W3):
     the free open gives [UserFd.ustd] back untouched and the deed-aware
     one gives [UserFd.ualloc], so which it is belongs to the payment
     ([UkCat.kcat_o]'s [Oi]/[Oo]) and not to the walk. *)
  Lemma wp_kcat_main_body (sp0 : mword 64) (av : Z) (args : list uarg)
      (i : nat) (g : uarg) (h : CpuId) (m : regfile)
      (f : nat -> bv 8) (n : nat) (Ci Co : iProp Σ) :
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    (forall (j : nat) (g0 : uarg), args !! j = Some g0 -> ua_ptr g0 <> 0) ->
    args !! i = Some g ->
    cm_inv sp0 av (length args) i m ->
    kcat_file g Ci Co -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    Ci -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int 0xa6) (8 + (10 + (12 + (4 + n)))) -∗
    (∀ (h' : CpuId) (m' : regfile) (f' : nat -> bv 8),
       ⌜ cm_inv sp0 av (length args) (S i) m' ⌝ -∗
       Co -∗
       ubytes γd CatSyms.buf 512 f' -∗
       urun N h' m' (mword_of_int 0xc2) (8 + (10 + (12 + (4 + n)))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hav0 Havhi Hptr Hg Hinv.
    assert (Hilt : (i < length args)%nat)
      by exact (lookup_lt_Some args i g Hg).
    iIntros "Hfile #Hcode #Hro #Hargv HCi Hbuf Hrun Hcont".
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc].
    iDestruct (uargv_acc γd av args i g Hg with "Hargv") as "[[#Hw _] _]".
    destruct cat_syms_pins
      as (_ & _ & Hcat & _ & _ & _ & _ & _ & Hopen & Hclose & _).
    pose proof Hinv as Hd. destruct Hd as (Hsp & Hs2 & Hs3).
    assert (Hb64 : 0 <= av + 8 * Z.of_nat i < Z64) by (unfold Z64; lia).
    assert (Hmod : (av + 8 * Z.of_nat i) mod 8 = 0).
    { rewrite Z.add_mod; [ | lia ].
      rewrite Hal Z.mul_comm Z_mod_mult. reflexivity. }
    (* ---- 0xa6  c.li a1,0 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xa6)
              (mword_of_int 0 : mword 6) a1_idx (8 + (10 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_cat_a6 with "Hcode"). }
    assert (Ea6 : add_vec_int (mword_of_int 0xa6 : mword 64) 2
                  = mword_of_int 0xa8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea6.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m).
    assert (Hinv1 : cm_inv sp0 av (length args) i m1)
      by exact (cm_inv_upd sp0 av (length args) i m a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    pose proof Hinv1 as Hd1. destruct Hd1 as (Hsp1 & Hs2_1 & Hs3_1).
    (* ---- 0xa8  ld a0,0(s2) -- argv[i] ---- *)
    assert (Haddr : (av + 8 * Z.of_nat i)%Z
                    = uint (m1 !!! Regidx s2_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs2_1 (uint_moi (av + 8 * Z.of_nat i) Hb64).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_ld N h1 m1 (mword_of_int 0xa8)
              (mword_of_int 0 : mword 12) s2_idx a0_idx DfracDiscarded
              (av + 8 * Z.of_nat i) (mword_of_int (ua_ptr g))
              (8 + (10 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hmod ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_cat_a8 with "Hcode"). }
    assert (Ea8 : add_vec_int (mword_of_int 0xa8 : mword 64) 4
                  = mword_of_int 0xac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea8.
    iIntros "_" (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr g) : mword 64)]> m1).
    assert (Hinv2 : cm_inv sp0 av (length args) i m2)
      by exact (cm_inv_upd sp0 av (length args) i m1 a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    (* ---- 0xac  jal ra,0x3ec <open> ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0xac)
              (mword_of_int 832 : mword 21) ra_idx
              (mword_of_int CatSyms.open) (mword_of_int 0xb0)
              (8 + (10 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hopen; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hopen; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_ac with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xb0 : mword 64)]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = (mword_of_int 0xb0 : mword 64))
      by exact (upd_eq m2 (Regidx ra_idx) (regval_into_reg _)).
    assert (Hinv3 : cm_inv sp0 av (length args) i m3)
      by exact (cm_inv_upd sp0 av (length args) i m2 ra_idx _
                  ltac:(vm_compute; reflexivity) Hinv2).
    assert (Ha0_3 : m3 !!! Regidx a0_idx
                    = (mword_of_int (ua_ptr g) : mword 64)).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2. exact (upd_eq m1 (Regidx a0_idx) (regval_into_reg _)). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_eq m (Regidx a1_idx) (regval_into_reg _)).
      apply bv_eq; vm_compute; reflexivity. }
    (* THE TURN'S OWN OBLIGATION.  What comes back is the additive pair
       the [bltz] below chooses between. *)
    iApply ("Hfile" $! h3 m3 (8 + (10 + (12 + (4 + n))))%nat
              with "[%] [%] Hcode HCi Hrun");
      [ exact Ha0_3 | exact Ha1_3 | ].
    iIntros (h4 ret) "Hpick Hrun".
    assert (Eopen : ret_pc (m3 !!! Regidx ra_idx)
                    = (mword_of_int 0xb0 : mword 64))
      by (rewrite Hra3; apply bv_eq; vm_compute; reflexivity).
    rewrite Eopen.
    set (m4 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m3)).
    assert (Hinv4 : cm_inv sp0 av (length args) i m4).
    { apply (cm_inv_upd _ _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
      apply (cm_inv_upd _ _ _ _ _ a7_idx _ ltac:(vm_compute; reflexivity)).
      exact Hinv3. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = ret)
      by exact (upd_eq _ (Regidx a0_idx) ret).
    (* ---- 0xb0  c.mv s1,a0 -- the descriptor ---- *)
    iApply (wp_uk_cmv N h4 m4 (mword_of_int 0xb0) s1_idx a0_idx
              (add_vec zero_reg (m4 !!! Regidx a0_idx))
              (8 + (10 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_b0 with "Hcode"). }
    assert (Eb0 : add_vec_int (mword_of_int 0xb0 : mword 64) 2
                  = mword_of_int 0xb2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eb0.
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx s1_idx
                 := regval_into_reg
                      (add_vec zero_reg (m4 !!! Regidx a0_idx))]> m4).
    assert (Hinv5 : cm_inv sp0 av (length args) i m5)
      by exact (cm_inv_upd sp0 av (length args) i m4 s1_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    pose proof Hinv5 as Hd5. destruct Hd5 as (Hsp5 & Hs2_5 & Hs3_5).
    assert (Ha0_5 : m5 !!! Regidx a0_idx = ret).
    { rewrite <- Ha0_4.
      exact (upd_ne m4 (Regidx s1_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hs1_5 : m5 !!! Regidx s1_idx
                    = add_vec zero_reg (m4 !!! Regidx a0_idx))
      by exact (upd_eq m4 (Regidx s1_idx) (regval_into_reg _)).
    (* ---- 0xb2  bltz a0,0xde -- did open fail? ---- *)
    assert (Hsz : sint (zero_reg : mword 64) = 0)
      by (vm_compute; reflexivity).
    assert (Hbltz : uv_btaken BLT (m5 !!! Regidx a0_idx) zero_reg
                    = Z.ltb (bv_signed ret) 0).
    { rewrite Ha0_5. cbn [uv_btaken]. unfold zopz0zI_s. rewrite Hsz.
      reflexivity. }
    destruct (Z.ltb (bv_signed ret) 0) eqn:Hbt.
    - (* IT FAILED: the diagnostic, and no return *)
      assert (Etgtde : add_vec (mword_of_int 0xb2 : mword 64)
                         (sign_extend' 64 (mword_of_int 44 : mword 13))
                       = mword_of_int 0xde)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype0 N h5 m5 (mword_of_int 0xb2)
                (mword_of_int 44 : mword 13) a0_idx BLT true
                (mword_of_int 0xde) (8 + (10 + (12 + (4 + n))))
                (eq_sym Hbltz) (eq_sym Etgtde)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_b2 with "Hcode"). }
      iIntros (h6) "Hrun".
      replace (8 + (10 + (12 + (4 + n))))%nat
        with (10 + (12 + (4 + (8 + n))))%nat by lia.
      iDestruct "Hpick" as "[Hdg _]".
      iApply (wp_kcat_main_die h6 m5 av args i g (8 + n)%nat
                Hg (Hptr i g Hg) Hs2_5 with "[Hdg] Hcode Hro Hargv Hrun").
      iApply "Hdg". iPureIntro. apply Z.ltb_lt. exact Hbt.
    - (* IT SUCCEEDED: cat(fd), close(fd) *)
      iApply (wp_uk_btype0 N h5 m5 (mword_of_int 0xb2)
                (mword_of_int 44 : mword 13) a0_idx BLT false
                (add_vec (mword_of_int 0xb2 : mword 64)
                   (sign_extend' 64 (mword_of_int 44 : mword 13)))
                (8 + (10 + (12 + (4 + n)))) (eq_sym Hbltz) eq_refl
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_b2 with "Hcode"). }
      assert (Eb2 : add_vec_int (mword_of_int 0xb2 : mword 64) 4
                    = mword_of_int 0xb6)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eb2.
      iIntros (h6) "Hrun".
      iDestruct "Hpick" as "[_ Hok]".
      iDestruct ("Hok" with "[%]") as (fd Cm) "(%Hretfd & %Hfdlt & Hrun0 & Hcl)";
        [ apply Z.ltb_ge; exact Hbt | ].
      (* ---- 0xb6  jal ra,0x0 <cat> ---- *)
      iApply (wp_uk_jal N h6 m5 (mword_of_int 0xb6)
                (mword_of_int 2096970 : mword 21) ra_idx
                (mword_of_int CatSyms.cat) (mword_of_int 0xba)
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hcat; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hcat; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_b6 with "Hcode"). }
      iIntros (h7) "Hrun".
      set (m6 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0xba : mword 64)]> m5).
      assert (Hra6 : m6 !!! Regidx ra_idx = (mword_of_int 0xba : mword 64))
        by exact (upd_eq m5 (Regidx ra_idx) (regval_into_reg _)).
      assert (Ha0_6 : m6 !!! Regidx a0_idx = ret).
      { rewrite <- Ha0_5.
        exact (upd_ne m5 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). }
      assert (Hinv6 : cm_inv sp0 av (length args) i m6)
        by exact (cm_inv_upd sp0 av (length args) i m5 ra_idx _
                    ltac:(vm_compute; reflexivity) Hinv5).
      assert (Hs1_6 : m6 !!! Regidx s1_idx
                      = add_vec zero_reg (m4 !!! Regidx a0_idx)).
      { rewrite <- Hs1_5.
        exact (upd_ne m5 (Regidx ra_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). }
      (* ---- cat(fd) ---- *)
      iDestruct "Hrun0" as (I Cend) "(#Hround & HI & Hend)".
      assert (Ha0_6f : m6 !!! Regidx a0_idx
                       = (mword_of_int (Z.of_nat fd) : mword 64))
        by (rewrite Ha0_6; exact Hretfd).
      iApply (wp_kcat_cat N (mword_of_int (Z.of_nat fd)) f h7 m6 n I Cend
                Ha0_6f with "Hround Hcode Hro HI Hbuf Hrun").
      iIntros (h8 m7 f') "%Hcs HCend Hbuf Hrun".
      assert (Ecat : ret_pc (m6 !!! Regidx ra_idx)
                     = (mword_of_int 0xba : mword 64))
        by (rewrite Hra6; apply bv_eq; vm_compute; reflexivity).
      rewrite Ecat.
      assert (Hinv7 : cm_inv sp0 av (length args) i m7)
        by exact (cm_inv_call sp0 av (length args) i m6 m7 Hcs Hinv6).
      assert (Hs1_7 : m7 !!! Regidx s1_idx
                      = add_vec zero_reg (m4 !!! Regidx a0_idx)).
      { rewrite (Hcs s1_idx ltac:(vm_compute; reflexivity)). exact Hs1_6. }
      (* ---- 0xba  c.mv a0,s1 ---- *)
      iApply (wp_uk_cmv N h8 m7 (mword_of_int 0xba) a0_idx s1_idx
                (add_vec zero_reg (m7 !!! Regidx s1_idx))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl
                with "[] Hrun").
      { iApply (uis_cat_ba with "Hcode"). }
      assert (Eba : add_vec_int (mword_of_int 0xba : mword 64) 2
                    = mword_of_int 0xbc)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eba.
      iIntros (h9) "Hrun".
      set (m8 := <[Regidx a0_idx
                   := regval_into_reg
                        (add_vec zero_reg (m7 !!! Regidx s1_idx))]> m7).
      assert (Hinv8 : cm_inv sp0 av (length args) i m8)
        by exact (cm_inv_upd sp0 av (length args) i m7 a0_idx _
                    ltac:(vm_compute; reflexivity) Hinv7).
      (* ---- 0xbc  jal ra,0x3d4 <close> ---- *)
      iApply (wp_uk_jal N h9 m8 (mword_of_int 0xbc)
                (mword_of_int 792 : mword 21) ra_idx
                (mword_of_int CatSyms.close) (mword_of_int 0xc0)
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hclose; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hclose; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_bc with "Hcode"). }
      iIntros (h10) "Hrun".
      set (m9 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0xc0 : mword 64)]> m8).
      assert (Hra9 : m9 !!! Regidx ra_idx = (mword_of_int 0xc0 : mword 64))
        by exact (upd_eq m8 (Regidx ra_idx) (regval_into_reg _)).
      assert (Hinv9 : cm_inv sp0 av (length args) i m9)
        by exact (cm_inv_upd sp0 av (length args) i m8 ra_idx _
                    ltac:(vm_compute; reflexivity) Hinv8).
      (* THE HANDLE IS SPENT HERE, and it rides inside the payment's own
         close obligation: its descriptor is the one a0 holds, because cat
         saved the open's result in s1 (callee-saved across [cat], hence
         [Hs1_7]) and moved it back into a0 at 0xba. *)
      assert (Ha0_9 : bv_signed (trunc32 (m9 !!! Regidx a0_idx))
                      = Z.of_nat fd).
      { assert (Ea0 : m9 !!! Regidx a0_idx = ret).
        { rewrite /m9 (upd_ne m8 (Regidx ra_idx) (Regidx a0_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /m8 upd_eq Hs1_7 Ha0_4 !add_vec_zero_l. reflexivity. }
        rewrite Ea0 Hretfd trunc32_mword_of_int.
        assert (Hr31 : (0 <= Z.of_nat fd < 2 ^ 31)%Z).
        { unfold NOFILE in Hfdlt.
          assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
          lia. }
        (* hoisted out of argument position: an [ltac:] there would run
           before the width was known *)
        assert (Hbw : bv_wrap 32 (Z.of_nat fd) = Z.of_nat fd)
          by (apply bvw32_small; lia).
        unfold bv_signed. rewrite moi32_unsigned Hbw.
        apply bv_swrap_small.
        assert (Hh32 : bv_half_modulus 32 = 2147483648%Z)
          by (vm_compute; reflexivity).
        rewrite Hh32. lia. }
      iApply ("Hcl" $! h10 m9 (8 + (10 + (12 + (4 + n))))%nat
                with "[%] Hcode [Hend HCend] Hrun");
        [ exact Ha0_9 | iApply ("Hend" with "HCend") | ].
      iIntros (h11 ret2) "HCo Hrun".
      assert (Eclose : ret_pc (m9 !!! Regidx ra_idx)
                       = (mword_of_int 0xc0 : mword 64))
        by (rewrite Hra9; apply bv_eq; vm_compute; reflexivity).
      rewrite Eclose.
      set (m10 := <[Regidx a0_idx := ret2]>
                    (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m9)).
      assert (Hinv10 : cm_inv sp0 av (length args) i m10).
      { apply (cm_inv_upd _ _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
        apply (cm_inv_upd _ _ _ _ _ a7_idx _ ltac:(vm_compute; reflexivity)).
        exact Hinv9. }
      pose proof Hinv10 as Hd10.
      destruct Hd10 as (Hsp10 & Hs2_10 & Hs3_10).
      (* ---- 0xc0  c.addi s2,s2,8 -- on to the next file ---- *)
      assert (E8i : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                    = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Ebump : add_vec (m10 !!! Regidx s2_idx)
                        (sign_extend' 64 (mword_of_int 8 : mword 6))
                      = mword_of_int (av + 8 * Z.of_nat (S i))).
      { rewrite Hs2_10 E8i moi_add. f_equal. lia. }
      iApply (wp_uk_caddi N h11 m10 (mword_of_int 0xc0)
                (mword_of_int 8 : mword 6) s2_idx
                (mword_of_int (av + 8 * Z.of_nat (S i)))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(exact (eq_sym Ebump))
                with "[] Hrun").
      { iApply (uis_cat_c0 with "Hcode"). }
      assert (Ec0 : add_vec_int (mword_of_int 0xc0 : mword 64) 2
                    = mword_of_int 0xc2)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ec0.
      iIntros (h12) "Hrun".
      set (m11 := <[Regidx s2_idx
                    := regval_into_reg
                         (mword_of_int (av + 8 * Z.of_nat (S i))
                          : mword 64)]> m10).
      iApply ("Hcont" $! h12 m11 f' with "[] HCo Hbuf Hrun").
      iPureIntro. unfold cm_inv.
      rewrite /m11 (upd_ne m10 (Regidx s2_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m10 (Regidx s2_idx) (regval_into_reg _)).
      rewrite /m11 (upd_ne m10 (Regidx s2_idx) (Regidx s3_idx) _
                      ltac:(vm_compute; discriminate)).
      split; [ exact Hsp10 | ]. split; [ reflexivity | ]. exact Hs3_10.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE LOOP, by induction on the files LEFT.  [k+1] of them remain; the    *)
  (* [bne s2,s3] at 0xc2 is what decides, and at [k = 0] the cursor has      *)
  (* reached the end of argv and main falls into its exit.                   *)
  (*                                                                        *)
  (* An ordinary induction, not a Löb: argc bounds the count and [uargv]     *)
  (* carries it.                                                             *)
  (* --------------------------------------------------------------------- *)
  (* ...AT ANY END (program-specs cut 3): the chain ends in [Cend] and the
     normal exit [exit(0)] spends it through the exit hole at status 0, so
     the walk names no payload and needs no [Hpay]. *)
  Lemma wp_kcat_main_loop_at (sp0 : mword 64) (av : Z) (args : list uarg)
      (Cend : iProp Σ) (k : nat) :
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    forall (i : nat) (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat)
           (Ci : iProp Σ),
      (i + S k)%nat = length args ->
      cm_inv sp0 av (length args) i m ->
      kcat_pay args i (S k) Ci Cend -∗
      (Cend -∗ UkCat.kcat_exit N 0) -∗
      cat_code γt -∗
      cat_rodata γt -∗
      uargv γd av args -∗
      Ci -∗
      ubytes γd CatSyms.buf 512 f -∗
      urun N h m (mword_of_int 0xa6) (8 + (10 + (12 + (4 + n)))) -∗
      mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hav0 Havhi Hptr.
    induction k as [| k IH ];
      intros i h m f n Ci Hik Hinv;
      iIntros "Hpay Hex #Hcode #Hro #Hargv HCi Hbuf Hrun";
      destruct cat_syms_pins
        as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit);
      cbn [kcat_pay];
      iDestruct "Hpay" as (g Cm) "(%Hg & Hfile & Hpay)";
      iApply (wp_kcat_main_body sp0 av args i g h m f n Ci Cm Hav0 Havhi Hptr
                Hg Hinv with "Hfile Hcode Hro Hargv HCi Hbuf Hrun");
      iIntros (h1 m1 f1) "%Hinv1 HCm Hbuf Hrun";
      pose proof Hinv1 as Hd1;
      destruct Hd1 as (Hsp1 & Hs2_1 & Hs3_1);
      assert (Hlo2 : 0 <= av + 8 * Z.of_nat (S i) < Z64) by (unfold Z64; lia);
      assert (Hlo3 : 0 <= av + 8 * Z.of_nat (length args) < Z64)
        by (unfold Z64; lia).
    - (* the LAST file: s2 has caught s3 ---- *)
      assert (Heq : (S i)%nat = length args) by lia.
      assert (Hnt : false
                    = uv_btaken BNE (m1 !!! Regidx s2_idx)
                        (m1 !!! Regidx s3_idx)).
      { rewrite Hs2_1 Hs3_1 Heq. cbn [uv_btaken].
        rewrite (moi_neq_vec (av + 8 * Z.of_nat (length args))
                   (av + 8 * Z.of_nat (length args)) Hlo3 Hlo3).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype N h1 m1 (mword_of_int 0xc2)
                (mword_of_int 8164 : mword 13) s3_idx s2_idx BNE false
                (add_vec (mword_of_int 0xc2 : mword 64)
                   (sign_extend' 64 (mword_of_int 8164 : mword 13)))
                (8 + (10 + (12 + (4 + n)))) Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_c2 with "Hcode"). }
      assert (Ec2 : add_vec_int (mword_of_int 0xc2 : mword 64) 4
                    = mword_of_int 0xc6)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ec2.
      iIntros (h2) "Hrun".
      (* ---- 0xc6  c.li a0,0 ; 0xc8  jal exit ---- *)
      iApply (wp_uk_cli N h2 m1 (mword_of_int 0xc6)
                (mword_of_int 0 : mword 6) a0_idx (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_cat_c6 with "Hcode"). }
      assert (Ec6 : add_vec_int (mword_of_int 0xc6 : mword 64) 2
                    = mword_of_int 0xc8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ec6.
      iIntros (h3) "Hrun".
      iApply (wp_uk_jal N h3 _ (mword_of_int 0xc8)
                (mword_of_int 740 : mword 21) ra_idx
                (mword_of_int CatSyms.exit) (mword_of_int 0xcc)
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hexit; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_c8 with "Hcode"). }
      iIntros (h4) "Hrun".
      cbn [kcat_pay] in *.
      iDestruct ("Hex" with "[Hpay HCm]") as "Hx".
      { iApply ("Hpay" with "HCm"). }
      (* THE EXIT HOLE, at the status [c.li a0,0] left in a0 *)
      iApply ("Hx" $! h4 _ (8 + (10 + (12 + (4 + n))))%nat
                with "[%] Hcode Hrun").
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
      vm_compute. reflexivity.
    - (* more files to come ---- *)
      assert (Hne : (S i)%nat <> length args) by lia.
      assert (Ht : true
                   = uv_btaken BNE (m1 !!! Regidx s2_idx)
                       (m1 !!! Regidx s3_idx)).
      { rewrite Hs2_1 Hs3_1. cbn [uv_btaken].
        rewrite (moi_neq_vec (av + 8 * Z.of_nat (S i))
                   (av + 8 * Z.of_nat (length args)) Hlo2 Hlo3).
        destruct (Z.eqb_spec (av + 8 * Z.of_nat (S i))
                    (av + 8 * Z.of_nat (length args))) as [He | _];
          [ exfalso; apply Hne; lia | reflexivity ]. }
      assert (Etgt : add_vec (mword_of_int 0xc2 : mword 64)
                       (sign_extend' 64 (mword_of_int 8164 : mword 13))
                     = mword_of_int 0xa6)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype N h1 m1 (mword_of_int 0xc2)
                (mword_of_int 8164 : mword 13) s3_idx s2_idx BNE true
                (mword_of_int 0xa6) (8 + (10 + (12 + (4 + n)))) Ht
                (eq_sym Etgt) ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_c2 with "Hcode"). }
      iIntros (h2) "Hrun".
      iApply (IH (S i) h2 m1 f1 n Cm ltac:(lia) Hinv1
                with "Hpay Hex Hcode Hro Hargv HCm Hbuf Hrun").
  Qed.

  (* the landed statement: the end is the payload *)
  Lemma wp_kcat_main_loop (sp0 : mword 64) (av : Z) (args : list uarg)
      (k : nat) :
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    forall (i : nat) (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat)
           (Ci : iProp Σ),
      (i + S k)%nat = length args ->
      cm_inv sp0 av (length args) i m ->
      kcat_pay args i (S k) Ci (ukn_pay N (-1)) -∗
      cat_code γt -∗
      cat_rodata γt -∗
      uargv γd av args -∗
      Ci -∗
      ubytes γd CatSyms.buf 512 f -∗
      urun N h m (mword_of_int 0xa6) (8 + (10 + (12 + (4 + n)))) -∗
      mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    intros Hav0 Havhi Hptr i h m f n Ci Hik Hinv. iIntros "Hpay".
    iApply (wp_kcat_main_loop_at sp0 av args (ukn_pay N (-1)) k Hav0 Havhi
              Hptr i h m f n Ci Hik Hinv with "Hpay []").
    iIntros "H". iApply (UkCat.kcat_exit_of_pay with "H").
  Qed.

  (* ===================================================================== *)
  (* main(argc, argv) @0x7e.                                                *)
  (*                                                                        *)
  (* The frame is six words; ra and s0 go in unconditionally and s1..s3     *)
  (* only on the paths that use them -- which is why the [bge] at 0x88 has  *)
  (* two spill sequences after it and not one.  Neither path returns, so    *)
  (* nothing is ever loaded back and main has no continuation.              *)
  (* ===================================================================== *)
  Lemma wp_kcat_main_at (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) (Ci Cend : iProp Σ) :
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx a1_idx = mword_of_int av ->
    kcat_pay_all args Ci Cend -∗
    (Cend -∗ UkCat.kcat_exit N 0) -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    Ci -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int CatSyms.main)
      (6 + (8 + (10 + (12 + (4 + n))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hptr Ha0 Ha1.
    iIntros "Hpay Hex #Hcode #Hro #Hargv HCi Hbuf Hrun".
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc].
    change (2 ^ 31) with 2147483648 in Hargc.
    destruct cat_syms_pins
      as (_ & Hmain & Hcat & _ & _ & _ & _ & _ & _ & _ & Hexit).
    rewrite Hmain.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 48 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                   = bv_unsigned sp0 - 48).
    { replace (- (8 * Z.of_nat 6)) with (-48) by lia.
      exact (uv_avi_neg sp0 48 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp48 : uint (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                    = uint sp0 - 48)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    (* ---- 0x7e  c.addi16sp sp,sp,-48 ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x7e)
              (mword_of_int 61 : mword 6) 6 (8 + (10 + (12 + (4 + n))))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7e with "Hcode"). }
    iIntros "Hframe".
    assert (E7e : add_vec_int (mword_of_int 0x7e : mword 64) 2
                  = mword_of_int 0x80)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E7e.
    iIntros (h0) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg
                      (add_vec_int sp0 (- (8 * Z.of_nat 6)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_6_open with "Hframe")
      as "(_ & [%w1 Hw1] & [%w2 Hw2] & [%w3 Hw3] & [%w4 Hw4] & [%w5 Hw5]
            & [%w6 Hw6])".
    (* ---- 0x80  c.sdsp ra,40(sp) ---- *)
    iApply (wp_uk_csdsp N h0 m1 (mword_of_int 0x80)
              (mword_of_int 5 : mword 6) ra_idx (uint sp0 - 8) w1
              (8 + (10 + (12 + (4 + n))))
              ltac:(rewrite Hsp1 Hsp48 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_cat_80 with "Hcode"). }
    iIntros "Hw1".
    assert (E80 : add_vec_int (mword_of_int 0x80 : mword 64) 2
                  = mword_of_int 0x82)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E80.
    iIntros (h1) "Hrun".
    (* ---- 0x82  c.sdsp s0,32(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x82)
              (mword_of_int 4 : mword 6) s0_idx (uint sp0 - 16) w2
              (8 + (10 + (12 + (4 + n))))
              ltac:(rewrite Hsp1 Hsp48 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_cat_82 with "Hcode"). }
    iIntros "Hw2".
    assert (E82 : add_vec_int (mword_of_int 0x82 : mword 64) 2
                  = mword_of_int 0x84)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E82.
    iIntros (h2) "Hrun".
    (* ---- 0x84  c.addi4spn s0,sp,48 -- the frame pointer ---- *)
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x84)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))
              (8 + (10 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_84 with "Hcode"). }
    assert (E84 : add_vec_int (mword_of_int 0x84 : mword 64) 2
                  = mword_of_int 0x86)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E84.
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 12 : mword 8))))]> m1).
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite <- Hsp1.
      exact (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha0_2 : m2 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat (length args))).
    { rewrite <- Ha0.
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1. exact (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)). }
    assert (Ha1_2 : m2 !!! Regidx a1_idx = mword_of_int av).
    { rewrite <- Ha1.
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1. exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                            ltac:(vm_compute; discriminate)). }
    (* ---- 0x86  c.li a5,1 ---- *)
    iApply (wp_uk_cli N h3 m2 (mword_of_int 0x86)
              (mword_of_int 1 : mword 6) a5_idx (8 + (10 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_cat_86 with "Hcode"). }
    assert (E86 : add_vec_int (mword_of_int 0x86 : mword 64) 2
                  = mword_of_int 0x88)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E86.
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 6)
                       : mword 64)]> m2).
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int 1).
    { rewrite (upd_eq m2 (Regidx a5_idx) (regval_into_reg _)).
      apply bv_eq. vm_compute. reflexivity. }
    assert (Ha0_3 : m3 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat (length args))).
    { rewrite <- Ha0_2.
      exact (upd_ne m2 (Regidx a5_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int av).
    { rewrite <- Ha1_2.
      exact (upd_ne m2 (Regidx a5_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hsp3 : m3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite <- Hsp2.
      exact (upd_ne m2 (Regidx a5_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x88  bge a5,a0,0xcc -- is there a file named at all? ---- *)
    assert (Hge : uv_btaken BGE (m3 !!! Regidx a5_idx) (m3 !!! Regidx a0_idx)
                  = Z.geb 1 (Z.of_nat (length args))).
    { rewrite Ha5_3 Ha0_3. cbn [uv_btaken].
      apply (moi_ge_s 1 (Z.of_nat (length args)));
        unfold Z63; lia. }
    destruct (Nat.le_gt_cases (length args) 1) as [Hle | Hgt].
    - (* NO FILE NAMED: cat(0) reads the console ---- *)
      assert (Ht : true
                   = uv_btaken BGE (m3 !!! Regidx a5_idx)
                       (m3 !!! Regidx a0_idx))
        by (rewrite Hge; symmetry; apply Z.geb_le; lia).
      assert (Etgtcc : add_vec (mword_of_int 0x88 : mword 64)
                         (sign_extend' 64 (mword_of_int 68 : mword 13))
                       = mword_of_int 0xcc)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype N h4 m3 (mword_of_int 0x88)
                (mword_of_int 68 : mword 13) a0_idx a5_idx BGE true
                (mword_of_int 0xcc) (8 + (10 + (12 + (4 + n)))) Ht
                (eq_sym Etgtcc) ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_88 with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0xcc/0xce/0xd0  the three extra spills ---- *)
      iApply (wp_uk_csdsp N h5 m3 (mword_of_int 0xcc)
                (mword_of_int 3 : mword 6) s1_idx (uint sp0 - 24) w3
                (8 + (10 + (12 + (4 + n))))
                ltac:(rewrite Hsp3 Hsp48 Ho24; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                with "[] Hw3 Hrun").
      { iApply (uis_cat_cc with "Hcode"). }
      iIntros "Hw3".
      rewrite (_ : add_vec_int (mword_of_int 0xcc : mword 64) 2
                   = mword_of_int 0xce);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h6) "Hrun".
      iApply (wp_uk_csdsp N h6 m3 (mword_of_int 0xce)
                (mword_of_int 2 : mword 6) s2_idx (uint sp0 - 32) w4
                (8 + (10 + (12 + (4 + n))))
                ltac:(rewrite Hsp3 Hsp48 Ho16; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                with "[] Hw4 Hrun").
      { iApply (uis_cat_ce with "Hcode"). }
      iIntros "Hw4".
      rewrite (_ : add_vec_int (mword_of_int 0xce : mword 64) 2
                   = mword_of_int 0xd0);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h7) "Hrun".
      iApply (wp_uk_csdsp N h7 m3 (mword_of_int 0xd0)
                (mword_of_int 1 : mword 6) s3_idx (uint sp0 - 40) w5
                (8 + (10 + (12 + (4 + n))))
                ltac:(rewrite Hsp3 Hsp48 Ho8; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                with "[] Hw5 Hrun").
      { iApply (uis_cat_d0 with "Hcode"). }
      iIntros "Hw5".
      rewrite (_ : add_vec_int (mword_of_int 0xd0 : mword 64) 2
                   = mword_of_int 0xd2);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h8) "Hrun".
      (* ---- 0xd2  c.li a0,0 ; 0xd4  jal cat ---- *)
      iApply (wp_uk_cli N h8 m3 (mword_of_int 0xd2)
                (mword_of_int 0 : mword 6) a0_idx (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_cat_d2 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0xd2 : mword 64) 2
                   = mword_of_int 0xd4);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h9) "Hrun".
      set (m4 := <[Regidx a0_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)]> m3).
      iApply (wp_uk_jal N h9 m4 (mword_of_int 0xd4)
                (mword_of_int 2096940 : mword 21) ra_idx
                (mword_of_int CatSyms.cat) (mword_of_int 0xd8)
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hcat; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hcat; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_d4 with "Hcode"). }
      iIntros (h10) "Hrun".
      set (m5 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0xd8 : mword 64)]> m4).
      assert (Hra5 : m5 !!! Regidx ra_idx = (mword_of_int 0xd8 : mword 64))
        by exact (upd_eq m4 (Regidx ra_idx) (regval_into_reg _)).
      assert (Ha0_5 : m5 !!! Regidx a0_idx
                      = (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)).
      { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m4. exact (upd_eq m3 (Regidx a0_idx) (regval_into_reg _)). }
      assert (Ha0_5z : m5 !!! Regidx a0_idx = (mword_of_int 0 : mword 64)).
      { rewrite Ha0_5. apply bv_eq; vm_compute; reflexivity. }
      iDestruct "Hpay" as "[Hp0 _]".
      iDestruct ("Hp0" with "[%]") as (Cm) "[Hrun0 Hfin]"; [ exact Hle | ].
      iDestruct "Hrun0" as (I Cend0) "(#Hround & HI & Hend)".
      iApply (wp_kcat_cat N (mword_of_int 0) f h10 m5 n I Cend0 Ha0_5z
                with "Hround Hcode Hro HI Hbuf Hrun").
      iIntros (h11 m6 f') "_ HCend Hbuf Hrun".
      rewrite (_ : ret_pc (m5 !!! Regidx ra_idx)
                   = (mword_of_int 0xd8 : mword 64));
        [ | rewrite Hra5; apply bv_eq; vm_compute; reflexivity ].
      (* ---- 0xd8  c.li a0,0 ; 0xda  jal exit ---- *)
      iApply (wp_uk_cli N h11 m6 (mword_of_int 0xd8)
                (mword_of_int 0 : mword 6) a0_idx (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_cat_d8 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0xd8 : mword 64) 2
                   = mword_of_int 0xda);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h12) "Hrun".
      iApply (wp_uk_jal N h12 _ (mword_of_int 0xda)
                (mword_of_int 722 : mword 21) ra_idx
                (mword_of_int CatSyms.exit) (mword_of_int 0xde)
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hexit; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_da with "Hcode"). }
      iIntros (h13) "Hrun".
      iDestruct ("Hex" with "[HCi Hend HCend Hfin]") as "Hx".
      { iApply "Hfin". iFrame "HCi". iApply ("Hend" with "HCend"). }
      (* THE EXIT HOLE, at the status [c.li a0,0] left in a0 *)
      iApply ("Hx" $! h13 _ (8 + (10 + (12 + (4 + n))))%nat
                with "[%] Hcode Hrun").
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
      vm_compute. reflexivity.
    - (* AT LEAST ONE FILE: set up the walk over argv ---- *)
      assert (Hnt : false
                    = uv_btaken BGE (m3 !!! Regidx a5_idx)
                        (m3 !!! Regidx a0_idx)).
      { rewrite Hge. symmetry. apply not_true_is_false. intro HH.
        apply Z.geb_le in HH. lia. }
      iApply (wp_uk_btype N h4 m3 (mword_of_int 0x88)
                (mword_of_int 68 : mword 13) a0_idx a5_idx BGE false
                (add_vec (mword_of_int 0x88 : mword 64)
                   (sign_extend' 64 (mword_of_int 68 : mword 13)))
                (8 + (10 + (12 + (4 + n)))) Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_88 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x88 : mword 64) 4
                   = mword_of_int 0x8c);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h5) "Hrun".
      (* the argv vector's extent, off the heap *)
      destruct (lookup_lt_is_Some_2 args 0%nat ltac:(lia)) as [g0 Hg0].
      destruct (lookup_lt_is_Some_2 args (length args - 1)%nat ltac:(lia))
        as [gl Hgl].
      iDestruct (uargv_acc γd av args 0%nat g0 Hg0 with "Hargv")
        as "[[#Hwa _] _]".
      iDestruct (urun_uword_bnd with "Hrun Hwa") as %[Hav0 _].
      iDestruct (uargv_acc γd av args (length args - 1)%nat gl Hgl
                   with "Hargv") as "[[#Hwb _] _]".
      iDestruct (urun_uword_bnd with "Hrun Hwb") as %[_ Havhi].
      assert (Hav0' : 0 <= av) by lia.
      assert (Havhi' : av + 8 * Z.of_nat (length args) <= 2 ^ 38) by lia.
      (* ---- 0x8c/0x8e/0x90  the three extra spills ---- *)
      iApply (wp_uk_csdsp N h5 m3 (mword_of_int 0x8c)
                (mword_of_int 3 : mword 6) s1_idx (uint sp0 - 24) w3
                (8 + (10 + (12 + (4 + n))))
                ltac:(rewrite Hsp3 Hsp48 Ho24; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                with "[] Hw3 Hrun").
      { iApply (uis_cat_8c with "Hcode"). }
      iIntros "Hw3".
      rewrite (_ : add_vec_int (mword_of_int 0x8c : mword 64) 2
                   = mword_of_int 0x8e);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h6) "Hrun".
      iApply (wp_uk_csdsp N h6 m3 (mword_of_int 0x8e)
                (mword_of_int 2 : mword 6) s2_idx (uint sp0 - 32) w4
                (8 + (10 + (12 + (4 + n))))
                ltac:(rewrite Hsp3 Hsp48 Ho16; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                with "[] Hw4 Hrun").
      { iApply (uis_cat_8e with "Hcode"). }
      iIntros "Hw4".
      rewrite (_ : add_vec_int (mword_of_int 0x8e : mword 64) 2
                   = mword_of_int 0x90);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h7) "Hrun".
      iApply (wp_uk_csdsp N h7 m3 (mword_of_int 0x90)
                (mword_of_int 1 : mword 6) s3_idx (uint sp0 - 40) w5
                (8 + (10 + (12 + (4 + n))))
                ltac:(rewrite Hsp3 Hsp48 Ho8; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                with "[] Hw5 Hrun").
      { iApply (uis_cat_90 with "Hcode"). }
      iIntros "Hw5".
      rewrite (_ : add_vec_int (mword_of_int 0x90 : mword 64) 2
                   = mword_of_int 0x92);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h8) "Hrun".
      (* ---- 0x92  addi s2,a1,8 -- &argv[1] ---- *)
      assert (E8i : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                    = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_addi N h8 m3 (mword_of_int 0x92)
                (mword_of_int 8 : mword 12) a1_idx s2_idx
                (mword_of_int (av + 8 * Z.of_nat 1))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_3 E8i moi_add; f_equal; lia)
                with "[] Hrun").
      { iApply (uis_cat_92 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x92 : mword 64) 4
                   = mword_of_int 0x96);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h9) "Hrun".
      set (m4 := <[Regidx s2_idx
                   := regval_into_reg
                        (mword_of_int (av + 8 * Z.of_nat 1)
                         : mword 64)]> m3).
      assert (Ha0_4 : m4 !!! Regidx a0_idx
                      = mword_of_int (Z.of_nat (length args))).
      { rewrite <- Ha0_3.
        exact (upd_ne m3 (Regidx s2_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). }
      (* ---- 0x96  addiw s3,a0,-2 ---- *)
      assert (Em2 : (sign_extend' 64 (mword_of_int 4094 : mword 12)
                     : mword 64)
                    = mword_of_int (-2))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_addiw N h9 m4 (mword_of_int 0x96)
                (mword_of_int 4094 : mword 12) a0_idx s3_idx
                (mword_of_int (Z.of_nat (length args) - 2))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_4 Em2
                        (moi_addw (Z.of_nat (length args)) (-2)
                           ltac:(unfold Z31; lia));
                      f_equal; lia)
                with "[] Hrun").
      { iApply (uis_cat_96 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x96 : mword 64) 4
                   = mword_of_int 0x9a);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h10) "Hrun".
      set (m5 := <[Regidx s3_idx
                   := regval_into_reg
                        (mword_of_int (Z.of_nat (length args) - 2)
                         : mword 64)]> m4).
      assert (Hs3_5 : m5 !!! Regidx s3_idx
                      = mword_of_int (Z.of_nat (length args) - 2))
        by exact (upd_eq m4 (Regidx s3_idx) (regval_into_reg _)).
      (* ---- 0x9a  slli a5,s3,32 ---- *)
      iApply (wp_uk_slli N h10 m5 (mword_of_int 0x9a)
                (mword_of_int 32 : mword 6) s3_idx a5_idx
                (shift_bits_left
                   (mword_of_int (Z.of_nat (length args) - 2) : mword 64)
                   (subrange_vec_dec (mword_of_int 32 : mword 6)
                      (Z.sub log2_xlen 1) 0))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_5; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_9a with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x9a : mword 64) 4
                   = mword_of_int 0x9e);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h11) "Hrun".
      set (m6 := <[Regidx a5_idx
                   := regval_into_reg
                        (shift_bits_left
                           (mword_of_int (Z.of_nat (length args) - 2)
                            : mword 64)
                           (subrange_vec_dec (mword_of_int 32 : mword 6)
                              (Z.sub log2_xlen 1) 0))]> m5).
      assert (Ha5_6 : m6 !!! Regidx a5_idx
                      = shift_bits_left
                          (mword_of_int (Z.of_nat (length args) - 2)
                           : mword 64)
                          (subrange_vec_dec (mword_of_int 32 : mword 6)
                             (Z.sub log2_xlen 1) 0))
        by exact (upd_eq m5 (Regidx a5_idx) (regval_into_reg _)).
      (* ---- 0x9e  srli s3,a5,29 : s3 := 8 * (argc - 2) ---- *)
      iApply (wp_uk_srli N h11 m6 (mword_of_int 0x9e)
                (mword_of_int 29 : mword 6) a5_idx s3_idx
                (mword_of_int ((Z.of_nat (length args) - 2) * 8))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5_6; symmetry;
                      exact (moi_shl32_shr29 (Z.of_nat (length args) - 2)
                               ltac:(unfold Z32; lia)))
                with "[] Hrun").
      { iApply (uis_cat_9e with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x9e : mword 64) 4
                   = mword_of_int 0xa2);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h12) "Hrun".
      set (m7 := <[Regidx s3_idx
                   := regval_into_reg
                        (mword_of_int ((Z.of_nat (length args) - 2) * 8)
                         : mword 64)]> m6).
      assert (Ha1_7 : m7 !!! Regidx a1_idx = mword_of_int av).
      { rewrite <- Ha1_3.
        rewrite /m7 (upd_ne m6 (Regidx s3_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6 (upd_ne m5 (Regidx a5_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m5 (upd_ne m4 (Regidx s3_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m4. exact (upd_ne m3 (Regidx s2_idx) (Regidx a1_idx) _
                              ltac:(vm_compute; discriminate)). }
      (* ---- 0xa2  c.addi a1,a1,16 ---- *)
      assert (E16 : (sign_extend' 64 (mword_of_int 16 : mword 6) : mword 64)
                    = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi N h12 m7 (mword_of_int 0xa2)
                (mword_of_int 16 : mword 6) a1_idx (mword_of_int (av + 16))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_7 E16 moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_a2 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0xa2 : mword 64) 2
                   = mword_of_int 0xa4);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h13) "Hrun".
      set (m8 := <[Regidx a1_idx
                   := regval_into_reg
                        (mword_of_int (av + 16) : mword 64)]> m7).
      assert (Hs3_8 : m8 !!! Regidx s3_idx
                      = mword_of_int ((Z.of_nat (length args) - 2) * 8)).
      { rewrite /m8 (upd_ne m7 (Regidx a1_idx) (Regidx s3_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7. exact (upd_eq m6 (Regidx s3_idx) (regval_into_reg _)). }
      assert (Ha1_8 : m8 !!! Regidx a1_idx = mword_of_int (av + 16))
        by exact (upd_eq m7 (Regidx a1_idx) (regval_into_reg _)).
      (* ---- 0xa4  c.add s3,s3,a1 : s3 := &argv[argc] ---- *)
      iApply (wp_uk_cadd N h13 m8 (mword_of_int 0xa4) s3_idx a1_idx
                (mword_of_int (av + 8 * Z.of_nat (length args)))
                (8 + (10 + (12 + (4 + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_8 Ha1_8 moi_add; f_equal; lia)
                with "[] Hrun").
      { iApply (uis_cat_a4 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0xa4 : mword 64) 2
                   = mword_of_int 0xa6);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h14) "Hrun".
      set (m9 := <[Regidx s3_idx
                   := regval_into_reg
                        (mword_of_int (av + 8 * Z.of_nat (length args))
                         : mword 64)]> m8).
      iDestruct "Hpay" as "[_ Hp1]".
      iDestruct ("Hp1" with "[%]") as "Hpay"; [ lia | ].
      assert (Hkeq : (length args - 1)%nat = S (length args - 2)%nat)
        by lia.
      iEval (rewrite Hkeq) in "Hpay".
      iApply (wp_kcat_main_loop_at sp0 av args Cend (length args - 2)%nat
                Hav0' Havhi' Hptr 1%nat h14 m9 f n Ci ltac:(lia)
                with "Hpay Hex Hcode Hro Hargv HCi Hbuf Hrun").
      unfold cm_inv.
      split.
      { rewrite /m9 (upd_ne m8 (Regidx s3_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m8 (upd_ne m7 (Regidx a1_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_ne m6 (Regidx s3_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6 (upd_ne m5 (Regidx a5_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m5 (upd_ne m4 (Regidx s3_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m4 (upd_ne m3 (Regidx s2_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        exact Hsp3. }
      split.
      { rewrite /m9 (upd_ne m8 (Regidx s3_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m8 (upd_ne m7 (Regidx a1_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_ne m6 (Regidx s3_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6 (upd_ne m5 (Regidx a5_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m5 (upd_ne m4 (Regidx s3_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m4. exact (upd_eq m3 (Regidx s2_idx) (regval_into_reg _)). }
      exact (upd_eq m8 (Regidx s3_idx) (regval_into_reg _)).
  Qed.

  (* the landed statement: the end is the payload *)
  Lemma wp_kcat_main (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) (Ci : iProp Σ) :
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx a1_idx = mword_of_int av ->
    kcat_pay_all args Ci (ukn_pay N (-1)) -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    Ci -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int CatSyms.main)
      (6 + (8 + (10 + (12 + (4 + n))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    intros Hptr Ha0 Ha1.
    iIntros "Hpay #Hcode #Hro #Hargv HCi Hbuf Hrun".
    iApply (wp_kcat_main_at h m av args f n Ci (ukn_pay N (-1)) Hptr Ha0 Ha1
              with "Hpay [] Hcode Hro Hargv HCi Hbuf Hrun").
    iIntros "H". iApply (UkCat.kcat_exit_of_pay with "H").
  Qed.

  (* ===================================================================== *)
  (* start(argc, argv) @0xf6 -- the wrapper that makes it safe for main not *)
  (* to call exit.  main always does, so the [jal exit] at 0x102 is never   *)
  (* reached and nothing here has to say what it would do.                  *)
  (* ===================================================================== *)
  Lemma wp_kcat_start_at (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) (Ci Cend : iProp Σ) :
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx a1_idx = mword_of_int av ->
    kcat_pay_all args Ci Cend -∗
    (Cend -∗ UkCat.kcat_exit N 0) -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    Ci -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int CatSyms.start)
      (2 + (6 + (8 + (10 + (12 + (4 + n)))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hptr Ha0 Ha1.
    iIntros "Hpay Hex #Hcode #Hro #Hargv HCi Hbuf Hrun".
    destruct cat_syms_pins
      as (Hstart & Hmain & _ & _ & _ & _ & _ & _ & _ & _ & _).
    rewrite Hstart.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 16 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0xf6  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0xf6)
              (mword_of_int 48 : mword 6) 2
              (6 + (8 + (10 + (12 + (4 + n)))))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_f6 with "Hcode"). }
    iIntros "Hframe".
    rewrite Hsp.
    rewrite (_ : add_vec_int (mword_of_int 0xf6 : mword 64) 2
                 = mword_of_int 0xf8);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h0) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg
                      (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_2_open with "Hframe")
      as "(_ & [%w1 Hw1] & [%w2 Hw2])".
    (* ---- 0xf8  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp N h0 m1 (mword_of_int 0xf8)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) w1
              (6 + (8 + (10 + (12 + (4 + n)))))
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_cat_f8 with "Hcode"). }
    iIntros "Hw1".
    rewrite (_ : add_vec_int (mword_of_int 0xf8 : mword 64) 2
                 = mword_of_int 0xfa);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    (* ---- 0xfa  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0xfa)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) w2
              (6 + (8 + (10 + (12 + (4 + n)))))
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_cat_fa with "Hcode"). }
    iIntros "Hw2".
    rewrite (_ : add_vec_int (mword_of_int 0xfa : mword 64) 2
                 = mword_of_int 0xfc);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    (* ---- 0xfc  c.addi4spn s0,sp,16 ---- *)
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0xfc)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))
              (6 + (8 + (10 + (12 + (4 + n)))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_fc with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0xfc : mword 64) 2
                 = mword_of_int 0xfe);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    (* ---- 0xfe  jal ra,0x7e <main> ---- *)
    iApply (wp_uk_jal N h3 m2 (mword_of_int 0xfe)
              (mword_of_int 2097024 : mword 21) ra_idx
              (mword_of_int CatSyms.main) (mword_of_int 0x102)
              (6 + (8 + (10 + (12 + (4 + n)))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmain; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hmain; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_fe with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x102 : mword 64)]> m2).
    iApply (wp_kcat_main_at h4 m3 av args f n Ci Cend Hptr
              ltac:(rewrite <- Ha0;
                    rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                                   ltac:(vm_compute; discriminate));
                    rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                                   ltac:(vm_compute; discriminate));
                    rewrite /m1;
                    exact (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
                             ltac:(vm_compute; discriminate)))
              ltac:(rewrite <- Ha1;
                    rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                                   ltac:(vm_compute; discriminate));
                    rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                                   ltac:(vm_compute; discriminate));
                    rewrite /m1;
                    exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                             ltac:(vm_compute; discriminate)))
              with "Hpay Hex Hcode Hro Hargv HCi Hbuf Hrun").
  Qed.

  (* the landed statement: the end is the payload *)
  Lemma wp_kcat_start (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) (Ci : iProp Σ) :
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx a1_idx = mword_of_int av ->
    kcat_pay_all args Ci (ukn_pay N (-1)) -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    Ci -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int CatSyms.start)
      (2 + (6 + (8 + (10 + (12 + (4 + n)))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    intros Hptr Ha0 Ha1.
    iIntros "Hpay #Hcode #Hro #Hargv HCi Hbuf Hrun".
    iApply (wp_kcat_start_at h m av args f n Ci (ukn_pay N (-1)) Hptr Ha0 Ha1
              with "Hpay [] Hcode Hro Hargv HCi Hbuf Hrun").
    iIntros "H". iApply (UkCat.kcat_exit_of_pay with "H").
  Qed.

End UkCatMain.
