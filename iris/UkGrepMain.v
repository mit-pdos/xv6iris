(* ===================================================================== *)
(* UkGrepMain.v -- grep's main(), walked against grep's interaction tree  *)
(* [GrepTree.grep_tree] (design: claude-notes/design/grep.md).            *)
(*                                                                        *)
(*   main(argc, argv)                                                     *)
(*     if (argc <= 1) { fprintf(2, "usage: grep pattern [file ...]\n");   *)
(*                      exit(1); }                                        *)
(*     pattern = argv[1];                                                 *)
(*     if (argc <= 2) { grep(pattern, 0); exit(0); }                      *)
(*     for (i = 2; i < argc; i++) {                                       *)
(*       if ((fd = open(argv[i], O_RDONLY)) < 0) {                        *)
(*         printf("grep: cannot open %s\n", argv[i]); exit(1); }          *)
(*       grep(pattern, fd); close(fd); }                                  *)
(*     exit(0);                                                           *)
(*                                                                        *)
(* Stated DIRECTLY AT THE TREE, with no intermediate payment: main        *)
(* consumes [tree_pay (grep_tree (map uarg_bytes args))] one node per     *)
(* syscall.  The diagnostics are the tree's [write_bytes] runs, one       *)
(* [EWrite fd [b]] node per putc ([kgrep_wb_tree]); the open/close are    *)
(* the tree's op/cl holes; grep() is [UkGrepLoop.wp_kgrep_grep] at the    *)
(* tree [grep_go]; every exit is the tree's exit hole.                    *)
(*                                                                        *)
(* As in cat's main, every path ends in [exit], so main never restores    *)
(* what it spilled and its loop invariant names only the frame pointer,   *)
(* the argv cursor s2, the end s3 -- and the pattern pointer s4, which    *)
(* every turn hands grep().                                               *)
(*                                                                        *)
(* THE STACK is a function of the arguments ([grep_main_words]): main's   *)
(* six-word frame, then the deepest callee on the path argc selects --    *)
(* fprintf's chain for the usage line (10 + 12 + 4), grep()'s             *)
(* pattern-dependent [grep_words], and printf's chain for the open        *)
(* failure (12 + 12 + 4), which only the files path can reach.            *)
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
Require Import UCodeGrep.
Require Import CtxIdDefs.
Require User.GrepSyms User.GrepInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkGrepPutc.
Require Import UkGrepFprintf.
Require Import UkRunBr.

Require Import FdSlots.   (* [fdstate] -- what a handle names *)
Require Import VcGen.     (* [trunc32_mword_of_int] -- a0 read as a C [int] *)
Require Import RiscvExtras. (* [moi32_unsigned]/[bvw32_small] *)
Require Import ProcGeom.  (* [NOFILE] *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import StringBytes LineWords ProgTree GrepTree.
Require Import UkTree.
Require Import UkGrepLoop.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  0.  PURE: the tree at main's three arms, the literals, the stack      *)
(* ===================================================================== *)

Lemma gwrite_bytes_app (fd : Z) (a b : bytes) (rest : proc) :
  write_bytes fd (a ++ b) rest = write_bytes fd a (write_bytes fd b rest).
Proof. induction a as [| x a IH]; simpl; [ reflexivity | by rewrite IH ]. Qed.

Lemma grep_tree_usage (argv : list bytes) :
  (length argv <= 1)%nat -> grep_tree argv = write_bytes 2 grep_usage (exit_ 1).
Proof. intros H. unfold grep_tree. rewrite drop_ge; [ reflexivity | lia ]. Qed.

Lemma grep_tree_stdin (args : list uarg) (g : uarg) :
  length args = 2%nat -> args !! 1%nat = Some g ->
  grep_tree (map uarg_bytes args) = grep_go (uarg_bytes g) 0 false [] [] (exit_ 0).
Proof.
  intros Hl Hg. destruct args as [| a [| b [| c r]]]; simpl in Hl; try lia.
  simpl in Hg. injection Hg as ->. reflexivity.
Qed.

Lemma grep_tree_files (args : list uarg) (g : uarg) :
  (3 <= length args)%nat -> args !! 1%nat = Some g ->
  grep_tree (map uarg_bytes args)
  = grep_files (uarg_bytes g) (map uarg_bytes (drop 2 args)) (exit_ 0).
Proof.
  intros Hl Hg. destruct args as [| a [| b [| c r]]]; simpl in Hl; try lia.
  simpl in Hg. injection Hg as ->. reflexivity.
Qed.

(* the two literals, as grep's .rodata spells them *)
Lemma grep_usage_lit :
  @map nat (bv 8) (grep_lit 0xb20) (seq 0 31) = grep_usage.
Proof. vm_compute. reflexivity. Qed.
Lemma grep_dg_pre_lit :
  @map nat (bv 8) (grep_lit 0xb40) (seq 0 18) = sb "grep: cannot open ".
Proof. vm_compute. reflexivity. Qed.
Lemma grep_dg_nl_lit :
  @map nat (bv 8) (grep_lit 0xb40) (seq 20 1) = [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* "grep: cannot open %s\n": the NUL discipline and the '%'-freedom off
   the directive, both decided ([UkCatMain.cm_ok]/[cm_nopct]'s shape) *)
Definition gm_ok : bool :=
  forallb (fun j => match grep_ro !! (0xb40 + Z.of_nat j)%Z with
                    | Some b => negb (Z.eqb (bv_unsigned b) 0)
                    | None => false
                    end)
          (seq 0 21)
  && match grep_ro !! (0xb40 + Z.of_nat 21)%Z with
     | Some b => Z.eqb (bv_unsigned b) 0
     | None => false
     end.

Definition gm_nopct : bool :=
  forallb (fun j => Nat.eqb j 18
                    || negb (Z.eqb (bv_unsigned (grep_lit 0xb40 j)) 37))
          (seq 0 21).

Lemma gm_nopct_ok (j : nat) :
  (j < 21)%nat -> j <> 18%nat -> bv_unsigned (grep_lit 0xb40 j) <> 37.
Proof.
  intros Hj Hne.
  assert (H : gm_nopct = true) by (vm_compute; reflexivity).
  unfold gm_nopct in H. rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  apply orb_true_iff in H as [H | H].
  - apply Nat.eqb_eq in H. exfalso. exact (Hne H).
  - apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma guarg_bytes_of (g : uarg) : bytes_of (uarg_bytes g) (ua_bytes g).
Proof.
  intros j Hj. rewrite uarg_bytes_length in Hj. by apply map_seq_lookup.
Qed.

Lemma gbytes_of_one (b : bv 8) : bytes_of [b] (fun _ => b).
Proof. intros j Hj. simpl in Hj. by destruct j; [| lia]. Qed.

(* THE WORDS main NEEDS BELOW ITS OWN ENTRY: its frame, then the deepest
   callee on the path argc selects.  [argc <= 1]: fprintf's chain (the
   usage line); [argc = 2]: grep() alone; otherwise grep() and printf's
   chain (the open failure), whichever is deeper. *)
Definition grep_main_words (args : list uarg) : nat :=
  match args with
  | [] | [_] => (6 + (10 + (12 + 4)))%nat
  | [_; p] => (6 + grep_words (uarg_bytes p))%nat
  | _ :: p :: _ => (6 + Nat.max (grep_words (uarg_bytes p)) (12 + (12 + 4)))%nat
  end.

Lemma grep_main_words_usage (args : list uarg) :
  (length args <= 1)%nat -> grep_main_words args = 32%nat.
Proof. intros Hl. destruct args as [| a [| b r]]; simpl in *; [ done | done | lia ]. Qed.

Lemma grep_main_words_stdin (args : list uarg) (g : uarg) :
  length args = 2%nat -> args !! 1%nat = Some g ->
  grep_main_words args = (6 + grep_words (uarg_bytes g))%nat.
Proof.
  intros Hl Hg. destruct args as [| a [| b [| c r]]]; simpl in Hl; try lia.
  simpl in Hg. injection Hg as ->. reflexivity.
Qed.

Lemma grep_main_words_files (args : list uarg) (g : uarg) :
  (3 <= length args)%nat -> args !! 1%nat = Some g ->
  grep_main_words args = (6 + Nat.max (grep_words (uarg_bytes g)) 28)%nat.
Proof.
  intros Hl Hg. destruct args as [| a [| b [| c r]]]; simpl in Hl; try lia.
  simpl in Hg. injection Hg as ->. reflexivity.
Qed.

Section UkGrepMain.
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
     fraction, the advanced console credential or the filed alternative
     ([UCatOut.catq_filed] / [catq_unfiled]).  What cat actually needs of
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
  Local Notation s4_idx := (mword_of_int 20 : mword 5).

  Local Notation tp := (tree_pay N (grep_prog N)).

  (* ===================================================================== *)
  (* §1  THE TREE'S HOLES AT grep's CODE                                    *)
  (* ===================================================================== *)

  Lemma gtree_pay_exit (s : Z) : tp (exit_ s) ⊢ ex_obl N (grep_prog N) s.
  Proof using . rewrite /exit_ tree_pay_vis. reflexivity. Qed.

  Lemma gusrc_at_data (dq : dfrac) (a : Z) (n : nat) (f : nat -> bv 8) :
    usrc_at N false dq a n f = ubytesq γd dq a n f.
  Proof using . reflexivity. Qed.

  (* one putc byte is one node [EWrite fd [b]] -- [UkCatTree.kcat_wb_tree]
     at any descriptor the word in a0 reads as *)
  Lemma kgrep_wb_tree (fdw : mword 64) (fd : Z) (b : bv 8) (T : proc) :
    bv_signed (trunc32 fdw) = fd ->
    ⊢ kgrep_wb N fdw b (tp (Vis (EWrite fd [b]) (fun _ => T))) (tp T).
  Proof using .
    intros Hfd.
    iIntros (ua h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Ht Hb] Hrun Hcont".
    iEval (rewrite tree_pay_vis; cbn [ev_obl]) in "Ht".
    iApply ("Ht" $! h m avail (uint ua) false (DfracOwn 1) (fun _ => b)
              with "[%] [%] [%] [%] Hcode [Hb] Hrun [Hcont]").
    { exact (gbytes_of_one b). }
    { rewrite Ha0. exact Hfd. }
    { rewrite Ha1. symmetry. apply mword_of_int_uint. }
    { exact Ha2. }
    { rewrite gusrc_at_data /ubytesq /=. rewrite Z.add_0_r. by iFrame "Hb". }
    iIntros (h' ret) "HK Hs Hrun".
    iApply ("Hcont" $! h' ret with "[HK Hs] Hrun").
    rewrite gusrc_at_data /ubytesq /=. rewrite Z.add_0_r.
    iDestruct "Hs" as "[Hb _]". iFrame "HK Hb".
  Qed.

  Lemma kgrep_pay_seq_tree (fdw : mword 64) (fd : Z) (fb : nat -> bv 8) (k : nat) :
    bv_signed (trunc32 fdw) = fd ->
    forall (i : nat) (rest : proc),
      ⊢ kgrep_pay_seq N fdw fb i k
          (tp (write_bytes fd (map fb (seq i k)) rest)) (tp rest).
  Proof using .
    intros Hfd. induction k as [| k IH]; intros i rest.
    - cbn [kgrep_pay_seq seq map write_bytes]. by iIntros "H".
    - cbn [kgrep_pay_seq seq map write_bytes].
      iExists (tp (write_bytes fd (map fb (seq (S i) k)) rest)).
      iSplitR.
      + iApply (kgrep_wb_tree fdw fd _ _ Hfd).
      + iApply IH.
  Qed.

  (* the "grep: cannot open %s\n" literal as the resource vprintf reads *)
  Lemma gm_str : grep_rodata γt -∗ utext_str γt 0xb40 21 (grep_lit 0xb40).
  Proof using .
    assert (Hok : gm_ok = true) by (vm_compute; reflexivity).
    unfold gm_ok in Hok. apply andb_true_iff in Hok as [Hbody Hnul].
    rewrite forallb_forall in Hbody.
    iIntros "#Hro". rewrite /grep_rodata.
    iApply (utext_str_of_img γt grep_ro 0xb40 21 (grep_lit 0xb40)).
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold grep_lit.
      destruct (grep_ro !! (0xb40 + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply negb_true_iff, Z.eqb_neq in Hbody.
      intro He. apply Hbody.
      assert (Hbe : b = ubyte0) by (rewrite <- He; reflexivity).
      rewrite Hbe. vm_compute. reflexivity.
    - lia.
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold grep_lit.
      destruct (grep_ro !! (0xb40 + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      reflexivity.
    - destruct (grep_ro !! (0xb40 + Z.of_nat 21)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply Z.eqb_eq in Hnul. f_equal. apply bv_eq. rewrite Hnul.
      vm_compute. reflexivity.
    - iExact "Hro".
  Qed.

  (* where the heap's own bounds come from ([UkCatMain]'s) *)
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

  (* --------------------------------------------------------------------- *)
  (* WHAT SURVIVES A TURN OF THE LOOP: the frame pointer, the argv cursor, *)
  (* the end it stops at, and the pattern pointer.                          *)
  (* --------------------------------------------------------------------- *)
  Definition gm_inv (sp0 : mword 64) (av : Z) (nargs i : nat) (pv : Z)
      (m : regfile) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6)) /\
    m !!! Regidx s2_idx = mword_of_int (av + 8 * Z.of_nat i) /\
    m !!! Regidx s3_idx = mword_of_int (av + 8 * Z.of_nat nargs) /\
    m !!! Regidx s4_idx = mword_of_int pv.

  Definition gm_writable (r : mword 5) : bool :=
    negb (Z.eqb (uint r) 2 || Z.eqb (uint r) 18 || Z.eqb (uint r) 19
          || Z.eqb (uint r) 20).

  Lemma gm_writable_ne (r : mword 5) (z : Z) :
    gm_writable r = true -> (z = 2 \/ z = 18 \/ z = 19 \/ z = 20) -> uint r <> z.
  Proof using .
    unfold gm_writable. intro H. apply negb_true_iff in H.
    rewrite !orb_false_iff in H. destruct H as [[[H1 H2] H3] H4].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2. apply Z.eqb_neq in H3.
    apply Z.eqb_neq in H4.
    intros Hz He. rewrite He in H1, H2, H3, H4. lia.
  Qed.

  Lemma gm_inv_upd (sp0 : mword 64) (av : Z) (nargs i : nat) (pv : Z)
      (m : regfile) (r : mword 5) (v : mword 64) :
    gm_writable r = true ->
    gm_inv sp0 av nargs i pv m ->
    gm_inv sp0 av nargs i pv (<[Regidx r := regval_into_reg v]> m).
  Proof using .
    intros Hw (Hsp & Hs2 & Hs3 & Hs4). unfold gm_inv.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (gm_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (gm_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (gm_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s4_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (gm_writable_ne r _ Hw);
                     replace (uint s4_idx) with 20
                       by (vm_compute; reflexivity); lia)).
    repeat (split; [ assumption | ]). assumption.
  Qed.

  Lemma gm_inv_call (sp0 : mword 64) (av : Z) (nargs i : nat) (pv : Z)
      (m m' : regfile) :
    ucallee_saved m m' ->
    gm_inv sp0 av nargs i pv m -> gm_inv sp0 av nargs i pv m'.
  Proof using .
    intros Hcs (Hsp & Hs2 & Hs3 & Hs4). unfold gm_inv.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]). assumption.
  Qed.

  (* ===================================================================== *)
  (* §2  THE USAGE ARM, 0x22e -> exit.                                      *)
  (*                                                                       *)
  (*   auipc/addi a1,<usage> ; li a0,2 ; jal fprintf ; li a0,1 ; jal exit  *)
  (* ===================================================================== *)
  Lemma wp_kgrep_main_usage (h : CpuId) (m : regfile) (na : nat) :
    (26 <= na)%nat ->
    tp (write_bytes 2 grep_usage (exit_ 1)) -∗
    grep_code γt -∗
    grep_rodata γt -∗
    urun N h m (mword_of_int 0x22e) na -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hna. iIntros "Ht #Hcode #Hro Hrun".
    destruct grep_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & Hfprintf & _ & _ & _ & _ & _ & _ & _ & Hexit).
    replace na with (10 + (12 + (4 + (na - 26))))%nat by lia.
    set (n := (na - 26)%nat).
    (* ---- 0x22e  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc N h m (mword_of_int 0x22e)
              (mword_of_int 1 : mword 20) a1_idx (mword_of_int 0x122e)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_22e with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x22e : mword 64) 4
                 = mword_of_int 0x232);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0x122e : mword 64)]> m).
    (* ---- 0x232  addi a1,a1,-1806 -- &"usage: ..." ---- *)
    assert (Ea1 : add_vec (m1 !!! Regidx a1_idx)
                    (sign_extend' 64 (mword_of_int 2290 : mword 12))
                  = mword_of_int 0xb20).
    { rewrite (upd_eq m (Regidx a1_idx) (regval_into_reg _)).
      apply bv_eq. vm_compute. reflexivity. }
    iApply (wp_uk_addi N h1 m1 (mword_of_int 0x232)
              (mword_of_int 2290 : mword 12) a1_idx a1_idx
              (mword_of_int 0xb20) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea1))
              with "[] Hrun").
    { iApply (uis_grep_232 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x232 : mword 64) 4
                 = mword_of_int 0x236);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0xb20 : mword 64)]> m1).
    (* ---- 0x236  c.li a0,2 ---- *)
    iApply (wp_uk_cli N h2 m2 (mword_of_int 0x236)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_236 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x236 : mword 64) 2
                 = mword_of_int 0x238);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 2 : mword 6)
                       : mword 64)]> m2).
    (* ---- 0x238  jal ra,0x940 <fprintf> ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x238)
              (mword_of_int 1800 : mword 21) ra_idx
              (mword_of_int GrepSyms.fprintf) (mword_of_int 0x23c)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_238 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x23c : mword 64)]> m3).
    assert (Hra4 : m4 !!! Regidx ra_idx = (mword_of_int 0x23c : mword 64))
      by exact (upd_eq m3 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1_4 : m4 !!! Regidx a1_idx = mword_of_int 0xb20).
    { rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2. exact (upd_eq m1 (Regidx a1_idx) (regval_into_reg _)). }
    assert (Hfd4 : bv_signed (trunc32 (m4 !!! Regidx a0_idx)) = 2).
    { rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_eq m2 (Regidx a0_idx) (regval_into_reg _)).
      vm_compute. reflexivity. }
    (* ---- fprintf(2, "usage: grep pattern [file ...]\n") ---- *)
    assert (Hlen : 0xb20 + Z.of_nat 31 + 2 < 2 ^ 31) by lia.
    assert (Hb0 : 0 <= 0xb20) by lia.
    assert (Hl31 : (0 < 31)%nat) by lia.
    assert (Hl31' : Z.of_nat 31 < 2 ^ 31) by lia.
    iPoseProof (kgrep_pay_seq_tree (m4 !!! Regidx a0_idx) 2 (grep_lit 0xb20) 31
                  Hfd4 0 (exit_ 1)) as "Hseq".
    iEval (rewrite grep_usage_lit) in "Hseq".
    iApply (wp_kgrep_fprintf N 0xb20 31 (grep_lit 0xb20) h4 m4 n
              (tp (write_bytes 2 grep_usage (exit_ 1))) (tp (exit_ 1))
              Hb0 Hlen Hl31
              (fun j Hj => grep_lit_nopct 0xb20 31 j grep_lit_usage_ok Hj)
              Ha1_4
              with "Hseq Hcode [] Ht Hrun").
    { iApply (grep_lit_str γt 0xb20 31 grep_lit_usage_ok Hl31' with "Hro"). }
    iIntros (h5 m5) "_ Hx Hrun".
    rewrite (_ : ret_pc (m4 !!! Regidx ra_idx)
                 = (mword_of_int 0x23c : mword 64));
      [ | rewrite Hra4; apply bv_eq; vm_compute; reflexivity ].
    (* ---- 0x23c  c.li a0,1 ; 0x23e  jal exit ---- *)
    iApply (wp_uk_cli N h5 m5 (mword_of_int 0x23c)
              (mword_of_int 1 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_23c with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x23c : mword 64) 2
                 = mword_of_int 0x23e);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h6) "Hrun".
    iApply (wp_uk_jal N h6 _ (mword_of_int 0x23e)
              (mword_of_int 734 : mword 21) ra_idx
              (mword_of_int GrepSyms.exit) (mword_of_int 0x242)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_23e with "Hcode"). }
    iIntros (h7) "Hrun".
    (* THE EXIT HOLE, at the status [c.li a0,1] left in a0 *)
    iDestruct (gtree_pay_exit with "Hx") as "Hx".
    iApply ("Hx" $! h7 _ (10 + (12 + (4 + n)))%nat with "[%] Hcode Hrun").
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
    vm_compute. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §3  THE OPEN-FAILURE ARM, 0x250 -> exit.                               *)
  (*                                                                       *)
  (*   ld a1,0(s2) ; auipc/addi a0,<msg> ; jal printf ; li a0,1 ; jal exit *)
  (* ===================================================================== *)
  Lemma wp_kgrep_main_die (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (i : nat) (g : uarg) (na : nat) :
    (28 <= na)%nat ->
    args !! i = Some g ->
    ua_ptr g <> 0 ->
    m !!! Regidx s2_idx = mword_of_int (av + 8 * Z.of_nat i) ->
    tp (write_bytes 1 (grep_dg_open (uarg_bytes g)) (exit_ 1)) -∗
    grep_code γt -∗
    grep_rodata γt -∗
    uargv γd av args -∗
    urun N h m (mword_of_int 0x250) na -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hna Hi Hnz Hs2.
    iIntros "Ht #Hcode #Hro #Hargv Hrun".
    replace na with (12 + (12 + (4 + (na - 28))))%nat by lia.
    set (n := (na - 28)%nat).
    iDestruct (gm_str with "Hro") as "#Hstr".
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc].
    iDestruct (uargv_acc γd av args i g Hi with "Hargv") as "[[#Hw #Hsstr] _]".
    iDestruct (urun_uword_bnd with "Hrun Hw") as %[Hlo0 Hhi0].
    destruct grep_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hprintf & _ & _ & _ & _ & _ & _ & Hexit).
    (* the tree's three runs: the literal before the directive, the path,
       the newline *)
    iEval (rewrite /grep_dg_open !gwrite_bytes_app -grep_dg_pre_lit
             -grep_dg_nl_lit /uarg_bytes) in "Ht".
    (* ---- 0x250  ld a1,0(s2) -- argv[i] ---- *)
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
    iApply (wp_uk_ld N h m (mword_of_int 0x250)
              (mword_of_int 0 : mword 12) s2_idx a1_idx DfracDiscarded
              (av + 8 * Z.of_nat i) (mword_of_int (ua_ptr g))
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hal8 ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_grep_250 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x250 : mword 64) 4
                 = mword_of_int 0x254);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros "_" (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr g) : mword 64)]> m).
    (* ---- 0x254  auipc a0,0x1 ---- *)
    iApply (wp_uk_auipc N h1 m1 (mword_of_int 0x254)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x1254)
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_254 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x254 : mword 64) 4
                 = mword_of_int 0x258);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0x1254 : mword 64)]> m1).
    (* ---- 0x258  addi a0,a0,-1812 -- &"grep: cannot open %s\n" ---- *)
    assert (Ea0 : add_vec (m2 !!! Regidx a0_idx)
                    (sign_extend' 64 (mword_of_int 2284 : mword 12))
                  = mword_of_int 0xb40).
    { rewrite (upd_eq m1 (Regidx a0_idx) (regval_into_reg _)).
      apply bv_eq. vm_compute. reflexivity. }
    iApply (wp_uk_addi N h2 m2 (mword_of_int 0x258)
              (mword_of_int 2284 : mword 12) a0_idx a0_idx
              (mword_of_int 0xb40) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea0))
              with "[] Hrun").
    { iApply (uis_grep_258 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x258 : mword 64) 4
                 = mword_of_int 0x25c);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0xb40 : mword 64)]> m2).
    (* ---- 0x25c  jal ra,0x96a <printf> ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x25c)
              (mword_of_int 1806 : mword 21) ra_idx
              (mword_of_int GrepSyms.printf) (mword_of_int 0x260)
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_25c with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x260 : mword 64)]> m3).
    assert (Hra4 : m4 !!! Regidx ra_idx = (mword_of_int 0x260 : mword 64))
      by exact (upd_eq m3 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int 0xb40).
    { rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3. exact (upd_eq m2 (Regidx a0_idx) (regval_into_reg _)). }
    assert (Ha1_4 : m4 !!! Regidx a1_idx = mword_of_int (ua_ptr g)).
    { rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1. exact (upd_eq m (Regidx a1_idx) (regval_into_reg _)). }
    (* ---- printf("grep: cannot open %s\n", argv[i]) ---- *)
    assert (Hgm0 : 0 <= 0xb40) by lia.
    assert (Hgmhi : 0xb40 + Z.of_nat 21 + 2 < 2 ^ 31) by lia.
    assert (Hgmq2 : (S (S 18) < 21)%nat) by lia.
    assert (Hgmpq : bv_unsigned (grep_lit 0xb40 18) = 37)
      by (vm_compute; reflexivity).
    assert (Hgmps : bv_unsigned (grep_lit 0xb40 (S 18)) = 115)
      by (vm_compute; reflexivity).
    assert (Hgm1d : bv_unsigned (grep_lit 0xb40 (S (S 18))) <> 100)
      by (vm_compute; discriminate).
    assert (Hgm1u : bv_unsigned (grep_lit 0xb40 (S (S 18))) <> 117)
      by (vm_compute; discriminate).
    assert (Hgm1x : bv_unsigned (grep_lit 0xb40 (S (S 18))) <> 120)
      by (vm_compute; discriminate).
    assert (Hgm2set : (S (S (S 18)) < 21)%nat ->
              bv_unsigned (grep_lit 0xb40 (S (S (S 18)))) <> 100 /\
              bv_unsigned (grep_lit 0xb40 (S (S (S 18)))) <> 117 /\
              bv_unsigned (grep_lit 0xb40 (S (S (S 18)))) <> 120)
      by (intros HH; exfalso; lia).
    assert (Hfd1 : bv_signed (trunc32 (mword_of_int 1 : mword 64)) = 1)
      by (vm_compute; reflexivity).
    iApply (wp_kgrep_printf_s N 0xb40 21 18 (grep_lit 0xb40)
              (ua_ptr g) (ua_len g) (ua_bytes g) h4 m4 n
              (tp (write_bytes 1 (map (grep_lit 0xb40) (seq 0 18))
                     (write_bytes 1 (map (ua_bytes g) (seq 0 (ua_len g)))
                        (write_bytes 1 (map (grep_lit 0xb40) (seq 20 1)) (exit_ 1)))))
              (tp (write_bytes 1 (map (ua_bytes g) (seq 0 (ua_len g)))
                     (write_bytes 1 (map (grep_lit 0xb40) (seq 20 1)) (exit_ 1))))
              (tp (write_bytes 1 (map (grep_lit 0xb40) (seq 20 1)) (exit_ 1)))
              (tp (exit_ 1))
              Hgm0 Hgmhi Hgmq2 Hgmpq Hgmps
              (fun j Hj Hne => gm_nopct_ok j Hj Hne)
              Hgm1d Hgm1u Hgm1x Hgm2set
              Hnz Ha0_4 Ha1_4
              with "[] [] [] Hcode Hstr Hsstr Ht Hrun").
    { iApply (kgrep_pay_seq_tree (mword_of_int 1) 1 (grep_lit 0xb40) 18 Hfd1). }
    { iApply (kgrep_pay_seq_tree (mword_of_int 1) 1 (ua_bytes g) (ua_len g) Hfd1). }
    { iApply (kgrep_pay_seq_tree (mword_of_int 1) 1 (grep_lit 0xb40) 1 Hfd1). }
    iIntros (h5 m5) "_ Hx Hrun".
    rewrite (_ : ret_pc (m4 !!! Regidx ra_idx)
                 = (mword_of_int 0x260 : mword 64));
      [ | rewrite Hra4; apply bv_eq; vm_compute; reflexivity ].
    (* ---- 0x260  c.li a0,1 ; 0x262  jal exit ---- *)
    iApply (wp_uk_cli N h5 m5 (mword_of_int 0x260)
              (mword_of_int 1 : mword 6) a0_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_260 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x260 : mword 64) 2
                 = mword_of_int 0x262);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h6) "Hrun".
    iApply (wp_uk_jal N h6 _ (mword_of_int 0x262)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int GrepSyms.exit) (mword_of_int 0x266)
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_262 with "Hcode"). }
    iIntros (h7) "Hrun".
    iDestruct (gtree_pay_exit with "Hx") as "Hx".
    iApply ("Hx" $! h7 _ (12 + (12 + (4 + n)))%nat with "[%] Hcode Hrun").
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
    vm_compute. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §4  THE STANDARD-INPUT ARM, 0x242 -> exit.                             *)
  (*                                                                       *)
  (*   li a1,0 ; mv a0,s4 ; jal grep ; li a0,0 ; jal exit                  *)
  (* ===================================================================== *)
  Lemma wp_kgrep_main_stdin (h : CpuId) (m : regfile) (g : uarg)
      (f : nat -> bv 8) (na : nat) :
    (grep_words (uarg_bytes g) <= na)%nat ->
    m !!! Regidx s4_idx = mword_of_int (ua_ptr g) ->
    tp (grep_go (uarg_bytes g) 0 false [] [] (exit_ 0)) -∗
    grep_code γt -∗
    ustr γd DfracDiscarded (ua_ptr g) (ua_len g) (ua_bytes g) -∗
    ubytes γd GrepSyms.buf 1024 f -∗
    urun N h m (mword_of_int 0x242) na -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hna Hs4.
    iIntros "Ht #Hcode #Hpat Hbuf Hrun".
    destruct grep_syms_pins
      as (_ & _ & Hgrep & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    (* ---- 0x242  c.li a1,0 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x242)
              (mword_of_int 0 : mword 6) a1_idx na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_242 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x242 : mword 64) 2
                 = mword_of_int 0x244);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m).
    (* ---- 0x244  c.mv a0,s4 -- the pattern ---- *)
    iApply (wp_uk_cmv N h1 m1 (mword_of_int 0x244) a0_idx s4_idx
              (add_vec zero_reg (m1 !!! Regidx s4_idx)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_grep_244 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x244 : mword 64) 2
                 = mword_of_int 0x246);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m1 !!! Regidx s4_idx))]> m1).
    (* ---- 0x246  jal ra,0xf8 <grep> ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0x246)
              (mword_of_int 2096818 : mword 21) ra_idx
              (mword_of_int GrepSyms.grep) (mword_of_int 0x24a) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hgrep; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hgrep; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_246 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x24a : mword 64)]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = (mword_of_int 0x24a : mword 64))
      by exact (upd_eq m2 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int (ua_ptr g)).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_eq m1 (Regidx a0_idx) (regval_into_reg _)).
      rewrite /m1 (upd_ne m (Regidx a1_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite Hs4. apply add_vec_zero_l. }
    assert (Hfd3 : bv_signed (trunc32 (m3 !!! Regidx a1_idx)) = 0).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_eq m (Regidx a1_idx) (regval_into_reg _)).
      vm_compute. reflexivity. }
    (* ---- grep(pattern, 0) ---- *)
    iApply (wp_kgrep_grep N h3 m3 (ua_ptr g) (ua_len g) (ua_bytes g)
              (m3 !!! Regidx a1_idx) 0 f (exit_ 0) na
              Ha0_3 eq_refl Hfd3 Hna
              with "Hcode Hpat Hbuf Ht Hrun").
    iIntros (h4 m4 f') "_ _ Hx Hrun".
    rewrite (_ : ret_pc (m3 !!! Regidx ra_idx)
                 = (mword_of_int 0x24a : mword 64));
      [ | rewrite Hra3; apply bv_eq; vm_compute; reflexivity ].
    (* ---- 0x24a  c.li a0,0 ; 0x24c  jal exit ---- *)
    iApply (wp_uk_cli N h4 m4 (mword_of_int 0x24a)
              (mword_of_int 0 : mword 6) a0_idx na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_24a with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x24a : mword 64) 2
                 = mword_of_int 0x24c);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h5) "Hrun".
    iApply (wp_uk_jal N h5 _ (mword_of_int 0x24c)
              (mword_of_int 720 : mword 21) ra_idx
              (mword_of_int GrepSyms.exit) (mword_of_int 0x250) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_24c with "Hcode"). }
    iIntros (h6) "Hrun".
    iDestruct (gtree_pay_exit with "Hx") as "Hx".
    iApply ("Hx" $! h6 _ na with "[%] Hcode Hrun").
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
    vm_compute. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §5  ONE FILE, 0x204 -> 0x224: one node of [grep_files].                *)
  (*                                                                       *)
  (*   li a1,0 ; ld a0,0(s2) ; jal open ; mv s1,a0 ; bltz a0,<die>         *)
  (*   mv a1,a0 ; mv a0,s4 ; jal grep ; mv a0,s1 ; jal close ; addi s2,8   *)
  (* ===================================================================== *)
  Lemma wp_kgrep_main_body (sp0 : mword 64) (av : Z) (args : list uarg)
      (i : nat) (g g1 : uarg) (h : CpuId) (m : regfile)
      (f : nat -> bv 8) (na : nat) (ps : list bytes) (rest : proc) :
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    (forall (j : nat) (g0 : uarg), args !! j = Some g0 -> ua_ptr g0 <> 0) ->
    args !! i = Some g ->
    args !! 1%nat = Some g1 ->
    (grep_words (uarg_bytes g1) <= na)%nat ->
    (28 <= na)%nat ->
    gm_inv sp0 av (length args) i (ua_ptr g1) m ->
    tp (grep_files (uarg_bytes g1) (uarg_bytes g :: ps) rest) -∗
    grep_code γt -∗
    grep_rodata γt -∗
    uargv γd av args -∗
    ubytes γd GrepSyms.buf 1024 f -∗
    urun N h m (mword_of_int 0x204) na -∗
    (∀ (h' : CpuId) (m' : regfile) (f' : nat -> bv 8),
       ⌜ gm_inv sp0 av (length args) (S i) (ua_ptr g1) m' ⌝ -∗
       tp (grep_files (uarg_bytes g1) ps rest) -∗
       ubytes γd GrepSyms.buf 1024 f' -∗
       urun N h' m' (mword_of_int 0x224) na -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hav0 Havhi Hptr Hg Hg1 Hwn H28 Hinv.
    assert (Hilt : (i < length args)%nat)
      by exact (lookup_lt_Some args i g Hg).
    iIntros "Ht #Hcode #Hro #Hargv Hbuf Hrun Hcont".
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc].
    iDestruct (uargv_acc γd av args i g Hg with "Hargv") as "[[#Hw #Hstr] _]".
    iDestruct (uargv_acc γd av args 1%nat g1 Hg1 with "Hargv") as "[[_ #Hpat] _]".
    destruct grep_syms_pins
      as (_ & _ & Hgrep & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hopen & Hclose & _).
    pose proof Hinv as Hd. destruct Hd as (Hsp & Hs2 & Hs3 & Hs4).
    assert (Hb64 : 0 <= av + 8 * Z.of_nat i < Z64) by (unfold Z64; lia).
    assert (Hmod : (av + 8 * Z.of_nat i) mod 8 = 0).
    { rewrite Z.add_mod; [ | lia ].
      rewrite Hal Z.mul_comm Z_mod_mult. reflexivity. }
    (* ---- 0x204  c.li a1,0 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x204)
              (mword_of_int 0 : mword 6) a1_idx na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_204 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x204 : mword 64) 2
                 = mword_of_int 0x206);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m).
    assert (Hinv1 : gm_inv sp0 av (length args) i (ua_ptr g1) m1)
      by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    pose proof Hinv1 as Hd1. destruct Hd1 as (Hsp1 & Hs2_1 & Hs3_1 & Hs4_1).
    (* ---- 0x206  ld a0,0(s2) -- argv[i] ---- *)
    assert (Haddr : (av + 8 * Z.of_nat i)%Z
                    = uint (m1 !!! Regidx s2_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs2_1 (uint_moi (av + 8 * Z.of_nat i) Hb64).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_ld N h1 m1 (mword_of_int 0x206)
              (mword_of_int 0 : mword 12) s2_idx a0_idx DfracDiscarded
              (av + 8 * Z.of_nat i) (mword_of_int (ua_ptr g)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hmod ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_grep_206 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x206 : mword 64) 4
                 = mword_of_int 0x20a);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros "_" (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr g) : mword 64)]> m1).
    assert (Hinv2 : gm_inv sp0 av (length args) i (ua_ptr g1) m2)
      by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m1 a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    (* ---- 0x20a  jal ra,0x55c <open> ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0x20a)
              (mword_of_int 850 : mword 21) ra_idx
              (mword_of_int GrepSyms.open) (mword_of_int 0x20e) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hopen; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hopen; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_20a with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x20e : mword 64)]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = (mword_of_int 0x20e : mword 64))
      by exact (upd_eq m2 (Regidx ra_idx) (regval_into_reg _)).
    assert (Hinv3 : gm_inv sp0 av (length args) i (ua_ptr g1) m3)
      by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m2 ra_idx _
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
    (* THE TREE'S OPEN NODE *)
    iEval (cbn [grep_files]; rewrite tree_pay_vis; cbn [ev_obl]) in "Ht".
    iApply ("Ht" $! h3 m3 na (ua_ptr g) false (ua_bytes g)
              with "[%] [%] [%] Hcode [] Hrun").
    { apply guarg_bytes_of. }
    { exact Ha0_3. }
    { exact Ha1_3. }
    { rewrite uarg_bytes_length. iExact "Hstr". }
    iIntros (h4 ret) "%Hok HK _ Hrun".
    rewrite (_ : ret_pc (m3 !!! Regidx ra_idx)
                 = (mword_of_int 0x20e : mword 64));
      [ | rewrite Hra3; apply bv_eq; vm_compute; reflexivity ].
    rewrite /stub_ret.
    set (m4 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m3)).
    assert (Hinv4 : gm_inv sp0 av (length args) i (ua_ptr g1) m4).
    { apply (gm_inv_upd _ _ _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
      apply (gm_inv_upd _ _ _ _ _ _ a7_idx _ ltac:(vm_compute; reflexivity)).
      exact Hinv3. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = ret)
      by exact (upd_eq _ (Regidx a0_idx) ret).
    (* ---- 0x20e  c.mv s1,a0 -- the descriptor ---- *)
    iApply (wp_uk_cmv N h4 m4 (mword_of_int 0x20e) s1_idx a0_idx
              (add_vec zero_reg (m4 !!! Regidx a0_idx)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_grep_20e with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x20e : mword 64) 2
                 = mword_of_int 0x210);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx s1_idx
                 := regval_into_reg
                      (add_vec zero_reg (m4 !!! Regidx a0_idx))]> m4).
    assert (Hinv5 : gm_inv sp0 av (length args) i (ua_ptr g1) m5)
      by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m4 s1_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    pose proof Hinv5 as Hd5. destruct Hd5 as (Hsp5 & Hs2_5 & Hs3_5 & Hs4_5).
    assert (Ha0_5 : m5 !!! Regidx a0_idx = ret).
    { rewrite <- Ha0_4.
      exact (upd_ne m4 (Regidx s1_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hs1_5 : m5 !!! Regidx s1_idx = ret).
    { rewrite /m5 (upd_eq m4 (Regidx s1_idx) (regval_into_reg _)).
      rewrite Ha0_4. apply add_vec_zero_l. }
    (* ---- 0x210  bltz a0,0x250 -- did open fail? ---- *)
    assert (Hsz : sint (zero_reg : mword 64) = 0)
      by (vm_compute; reflexivity).
    assert (Hbltz : uv_btaken BLT (m5 !!! Regidx a0_idx) zero_reg
                    = Z.ltb (bv_signed ret) 0).
    { rewrite Ha0_5. cbn [uv_btaken]. unfold zopz0zI_s. rewrite Hsz.
      reflexivity. }
    iEval (cbv beta) in "HK".
    destruct (Z.ltb (bv_signed ret) 0) eqn:Hbt.
    - (* IT FAILED: the diagnostic, and no return *)
      assert (Hneg : bv_signed ret < 0) by (apply Z.ltb_lt; exact Hbt).
      assert (Etgt : add_vec (mword_of_int 0x210 : mword 64)
                       (sign_extend' 64 (mword_of_int 64 : mword 13))
                     = mword_of_int 0x250)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype0 N h5 m5 (mword_of_int 0x210)
                (mword_of_int 64 : mword 13) a0_idx BLT true
                (mword_of_int 0x250) na
                (eq_sym Hbltz) (eq_sym Etgt)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_210 with "Hcode"). }
      iIntros (h6) "Hrun".
      iEval (rewrite (decide_True _ _ Hneg)) in "HK".
      iApply (wp_kgrep_main_die h6 m5 av args i g na H28
                Hg (Hptr i g Hg) Hs2_5 with "HK Hcode Hro Hargv Hrun").
    - (* IT SUCCEEDED: grep(pattern, fd), close(fd) *)
      assert (Hnn : 0 <= bv_signed ret) by (apply Z.ltb_ge; exact Hbt).
      destruct Hok as [Hm1 | [Hrng Hret]]; [ lia | ].
      set (s := bv_signed ret) in *.
      assert (Hs31 : 0 <= s < 2 ^ 31).
      { assert (E : Z.of_nat NOFILE = 16) by reflexivity.
        rewrite E in Hrng.
        assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
        lia. }
      assert (Hnlt : ~ (s < 0)) by lia.
      iEval (rewrite (decide_False _ _ Hnlt)) in "HK".
      iApply (wp_uk_btype0 N h5 m5 (mword_of_int 0x210)
                (mword_of_int 64 : mword 13) a0_idx BLT false
                (add_vec (mword_of_int 0x210 : mword 64)
                   (sign_extend' 64 (mword_of_int 64 : mword 13)))
                na (eq_sym Hbltz) eq_refl
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_grep_210 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x210 : mword 64) 4
                   = mword_of_int 0x214);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h6) "Hrun".
      (* ---- 0x214  c.mv a1,a0 ---- *)
      iApply (wp_uk_cmv N h6 m5 (mword_of_int 0x214) a1_idx a0_idx
                (add_vec zero_reg (m5 !!! Regidx a0_idx)) na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl
                with "[] Hrun").
      { iApply (uis_grep_214 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x214 : mword 64) 2
                   = mword_of_int 0x216);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h7) "Hrun".
      set (m6 := <[Regidx a1_idx
                   := regval_into_reg
                        (add_vec zero_reg (m5 !!! Regidx a0_idx))]> m5).
      assert (Hinv6 : gm_inv sp0 av (length args) i (ua_ptr g1) m6)
        by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m5 a1_idx _
                    ltac:(vm_compute; reflexivity) Hinv5).
      (* ---- 0x216  c.mv a0,s4 -- the pattern ---- *)
      iApply (wp_uk_cmv N h7 m6 (mword_of_int 0x216) a0_idx s4_idx
                (add_vec zero_reg (m6 !!! Regidx s4_idx)) na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl
                with "[] Hrun").
      { iApply (uis_grep_216 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x216 : mword 64) 2
                   = mword_of_int 0x218);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h8) "Hrun".
      set (m7 := <[Regidx a0_idx
                   := regval_into_reg
                        (add_vec zero_reg (m6 !!! Regidx s4_idx))]> m6).
      assert (Hinv7 : gm_inv sp0 av (length args) i (ua_ptr g1) m7)
        by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m6 a0_idx _
                    ltac:(vm_compute; reflexivity) Hinv6).
      (* ---- 0x218  jal ra,0xf8 <grep> ---- *)
      iApply (wp_uk_jal N h8 m7 (mword_of_int 0x218)
                (mword_of_int 2096864 : mword 21) ra_idx
                (mword_of_int GrepSyms.grep) (mword_of_int 0x21c) na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hgrep; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hgrep; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_218 with "Hcode"). }
      iIntros (h9) "Hrun".
      set (m8 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x21c : mword 64)]> m7).
      assert (Hra8 : m8 !!! Regidx ra_idx = (mword_of_int 0x21c : mword 64))
        by exact (upd_eq m7 (Regidx ra_idx) (regval_into_reg _)).
      assert (Hinv8 : gm_inv sp0 av (length args) i (ua_ptr g1) m8)
        by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m7 ra_idx _
                    ltac:(vm_compute; reflexivity) Hinv7).
      assert (Ha0_8 : m8 !!! Regidx a0_idx = mword_of_int (ua_ptr g1)).
      { rewrite /m8 (upd_ne m7 (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_eq m6 (Regidx a0_idx) (regval_into_reg _)).
        destruct Hinv6 as (_ & _ & _ & Hs4_6). rewrite Hs4_6.
        apply add_vec_zero_l. }
      assert (Hfd8 : bv_signed (trunc32 (m8 !!! Regidx a1_idx)) = s).
      { rewrite /m8 (upd_ne m7 (Regidx ra_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_ne m6 (Regidx a0_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6 (upd_eq m5 (Regidx a1_idx) (regval_into_reg _)).
        rewrite Ha0_5 add_vec_zero_l Hret.
        exact (cint_moi_small' s Hs31). }
      assert (Hs1_8 : m8 !!! Regidx s1_idx = ret).
      { rewrite /m8 (upd_ne m7 (Regidx ra_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_ne m6 (Regidx a0_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6 (upd_ne m5 (Regidx a1_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        exact Hs1_5. }
      (* ---- grep(pattern, fd) ---- *)
      iApply (wp_kgrep_grep N h9 m8 (ua_ptr g1) (ua_len g1) (ua_bytes g1)
                (m8 !!! Regidx a1_idx) s f
                (Vis (EClose s) (fun _ => grep_files (uarg_bytes g1) ps rest)) na
                Ha0_8 eq_refl Hfd8 Hwn
                with "Hcode Hpat Hbuf HK Hrun").
      iIntros (h10 m9 f') "%Hcs Hbuf HK Hrun".
      rewrite (_ : ret_pc (m8 !!! Regidx ra_idx)
                   = (mword_of_int 0x21c : mword 64));
        [ | rewrite Hra8; apply bv_eq; vm_compute; reflexivity ].
      assert (Hinv9 : gm_inv sp0 av (length args) i (ua_ptr g1) m9)
        by exact (gm_inv_call sp0 av (length args) i (ua_ptr g1) m8 m9 Hcs Hinv8).
      assert (Hs1_9 : m9 !!! Regidx s1_idx = ret).
      { rewrite (Hcs s1_idx ltac:(vm_compute; reflexivity)). exact Hs1_8. }
      (* ---- 0x21c  c.mv a0,s1 ---- *)
      iApply (wp_uk_cmv N h10 m9 (mword_of_int 0x21c) a0_idx s1_idx
                (add_vec zero_reg (m9 !!! Regidx s1_idx)) na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl
                with "[] Hrun").
      { iApply (uis_grep_21c with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x21c : mword 64) 2
                   = mword_of_int 0x21e);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h11) "Hrun".
      set (m10 := <[Regidx a0_idx
                    := regval_into_reg
                         (add_vec zero_reg (m9 !!! Regidx s1_idx))]> m9).
      assert (Hinv10 : gm_inv sp0 av (length args) i (ua_ptr g1) m10)
        by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m9 a0_idx _
                    ltac:(vm_compute; reflexivity) Hinv9).
      (* ---- 0x21e  jal ra,0x544 <close> ---- *)
      iApply (wp_uk_jal N h11 m10 (mword_of_int 0x21e)
                (mword_of_int 806 : mword 21) ra_idx
                (mword_of_int GrepSyms.close) (mword_of_int 0x222) na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hclose; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hclose; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_21e with "Hcode"). }
      iIntros (h12) "Hrun".
      set (m11 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x222 : mword 64)]> m10).
      assert (Hra11 : m11 !!! Regidx ra_idx = (mword_of_int 0x222 : mword 64))
        by exact (upd_eq m10 (Regidx ra_idx) (regval_into_reg _)).
      assert (Hinv11 : gm_inv sp0 av (length args) i (ua_ptr g1) m11)
        by exact (gm_inv_upd sp0 av (length args) i (ua_ptr g1) m10 ra_idx _
                    ltac:(vm_compute; reflexivity) Hinv10).
      assert (Ha0_11 : bv_signed (trunc32 (m11 !!! Regidx a0_idx)) = s).
      { rewrite /m11 (upd_ne m10 (Regidx ra_idx) (Regidx a0_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /m10 (upd_eq m9 (Regidx a0_idx) (regval_into_reg _)).
        rewrite Hs1_9 add_vec_zero_l Hret.
        exact (cint_moi_small' s Hs31). }
      (* THE TREE'S CLOSE NODE *)
      iEval (rewrite tree_pay_vis; cbn [ev_obl]) in "HK".
      iApply ("HK" $! h12 m11 na with "[%] Hcode Hrun"); [ exact Ha0_11 | ].
      iIntros (h13 r) "HK Hrun".
      iEval (cbv beta) in "HK".
      rewrite (_ : ret_pc (m11 !!! Regidx ra_idx)
                   = (mword_of_int 0x222 : mword 64));
        [ | rewrite Hra11; apply bv_eq; vm_compute; reflexivity ].
      rewrite /stub_ret.
      set (m12 := <[Regidx a0_idx := r]>
                    (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m11)).
      assert (Hinv12 : gm_inv sp0 av (length args) i (ua_ptr g1) m12).
      { apply (gm_inv_upd _ _ _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
        apply (gm_inv_upd _ _ _ _ _ _ a7_idx _ ltac:(vm_compute; reflexivity)).
        exact Hinv11. }
      pose proof Hinv12 as Hd12.
      destruct Hd12 as (Hsp12 & Hs2_12 & Hs3_12 & Hs4_12).
      (* ---- 0x222  c.addi s2,s2,8 -- on to the next file ---- *)
      assert (E8i : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                    = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Ebump : add_vec (m12 !!! Regidx s2_idx)
                        (sign_extend' 64 (mword_of_int 8 : mword 6))
                      = mword_of_int (av + 8 * Z.of_nat (S i))).
      { rewrite Hs2_12 E8i moi_add. f_equal. lia. }
      iApply (wp_uk_caddi N h13 m12 (mword_of_int 0x222)
                (mword_of_int 8 : mword 6) s2_idx
                (mword_of_int (av + 8 * Z.of_nat (S i))) na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(exact (eq_sym Ebump))
                with "[] Hrun").
      { iApply (uis_grep_222 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x222 : mword 64) 2
                   = mword_of_int 0x224);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h14) "Hrun".
      set (m13 := <[Regidx s2_idx
                    := regval_into_reg
                         (mword_of_int (av + 8 * Z.of_nat (S i))
                          : mword 64)]> m12).
      iApply ("Hcont" $! h14 m13 f' with "[] HK Hbuf Hrun").
      iPureIntro. unfold gm_inv.
      rewrite /m13 (upd_ne m12 (Regidx s2_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m12 (Regidx s2_idx) (regval_into_reg _)).
      rewrite /m13 (upd_ne m12 (Regidx s2_idx) (Regidx s3_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /m13 (upd_ne m12 (Regidx s2_idx) (Regidx s4_idx) _
                      ltac:(vm_compute; discriminate)).
      split; [ exact Hsp12 | ]. split; [ reflexivity | ].
      split; [ exact Hs3_12 | exact Hs4_12 ].
  Qed.

  (* ===================================================================== *)
  (* §6  THE LOOP, by induction on the files LEFT.  The [bne s2,s3] at      *)
  (* 0x224 decides; at the last file main falls into [exit(0)], which is    *)
  (* the tree's exit hole at the end of [grep_files].                       *)
  (* ===================================================================== *)
  Lemma wp_kgrep_main_loop (sp0 : mword 64) (av : Z) (args : list uarg)
      (g1 : uarg) (k : nat) :
    0 <= av -> av + 8 * Z.of_nat (length args) <= 2 ^ 38 ->
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    args !! 1%nat = Some g1 ->
    forall (i : nat) (h : CpuId) (m : regfile) (f : nat -> bv 8) (na : nat),
      (i + S k)%nat = length args ->
      (grep_words (uarg_bytes g1) <= na)%nat ->
      (28 <= na)%nat ->
      gm_inv sp0 av (length args) i (ua_ptr g1) m ->
      tp (grep_files (uarg_bytes g1) (map uarg_bytes (drop i args)) (exit_ 0)) -∗
      grep_code γt -∗
      grep_rodata γt -∗
      uargv γd av args -∗
      ubytes γd GrepSyms.buf 1024 f -∗
      urun N h m (mword_of_int 0x204) na -∗
      mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hav0 Havhi Hptr Hg1.
    induction k as [| k IH ];
      intros i h m f na Hik Hwn H28 Hinv;
      iIntros "Ht #Hcode #Hro #Hargv Hbuf Hrun";
      destruct grep_syms_pins
        as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit);
      destruct (lookup_lt_is_Some_2 args i ltac:(lia)) as [g Hg];
      rewrite (drop_S args g i Hg); cbn [List.map];
      iApply (wp_kgrep_main_body sp0 av args i g g1 h m f na
                (map uarg_bytes (drop (S i) args)) (exit_ 0)
                Hav0 Havhi Hptr Hg Hg1 Hwn H28 Hinv
                with "Ht Hcode Hro Hargv Hbuf Hrun");
      iIntros (h1 m1 f1) "%Hinv1 Ht Hbuf Hrun";
      pose proof Hinv1 as Hd1;
      destruct Hd1 as (Hsp1 & Hs2_1 & Hs3_1 & Hs4_1);
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
      iApply (wp_uk_btype N h1 m1 (mword_of_int 0x224)
                (mword_of_int 8160 : mword 13) s3_idx s2_idx BNE false
                (add_vec (mword_of_int 0x224 : mword 64)
                   (sign_extend' 64 (mword_of_int 8160 : mword 13)))
                na Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_grep_224 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x224 : mword 64) 4
                   = mword_of_int 0x228);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h2) "Hrun".
      (* ---- 0x228  c.li a0,0 ; 0x22a  jal exit ---- *)
      iApply (wp_uk_cli N h2 m1 (mword_of_int 0x228)
                (mword_of_int 0 : mword 6) a0_idx na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_grep_228 with "Hcode"). }
      rewrite (_ : add_vec_int (mword_of_int 0x228 : mword 64) 2
                   = mword_of_int 0x22a);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h3) "Hrun".
      iApply (wp_uk_jal N h3 _ (mword_of_int 0x22a)
                (mword_of_int 754 : mword 21) ra_idx
                (mword_of_int GrepSyms.exit) (mword_of_int 0x22e) na
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hexit; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_22a with "Hcode"). }
      iIntros (h4) "Hrun".
      rewrite (drop_ge args (S i)); [ | lia ].
      cbn [List.map grep_files].
      iDestruct (gtree_pay_exit with "Ht") as "Hx".
      (* THE EXIT HOLE, at the status [c.li a0,0] left in a0 *)
      iApply ("Hx" $! h4 _ na with "[%] Hcode Hrun").
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
      assert (Etgt : add_vec (mword_of_int 0x224 : mword 64)
                       (sign_extend' 64 (mword_of_int 8160 : mword 13))
                     = mword_of_int 0x204)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype N h1 m1 (mword_of_int 0x224)
                (mword_of_int 8160 : mword 13) s3_idx s2_idx BNE true
                (mword_of_int 0x204) na Ht
                (eq_sym Etgt) ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_224 with "Hcode"). }
      iIntros (h2) "Hrun".
      iApply (IH (S i) h2 m1 f1 na ltac:(lia) Hwn H28 Hinv1
                with "Ht Hcode Hro Hargv Hbuf Hrun").
  Qed.

  (* ===================================================================== *)
  (* §7  main(argc, argv) @0x1d0, AT THE TREE.                              *)
  (*                                                                       *)
  (* The six-word frame takes all six spills up front (ra, s0..s4); the    *)
  (* two [bge]s at 0x1e2 and 0x1ec pick the arm, and nothing is ever       *)
  (* loaded back: every arm ends in [exit].                                *)
  (* ===================================================================== *)
  Lemma wp_kgrep_main_tree (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) :
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx a1_idx = mword_of_int av ->
    (grep_main_words args <= n)%nat ->
    tp (grep_tree (map uarg_bytes args)) -∗
    grep_code γt -∗
    grep_rodata γt -∗
    uargv γd av args -∗
    ubytes γd GrepSyms.buf 1024 f -∗
    urun N h m (mword_of_int GrepSyms.main) n -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hptr Ha0 Ha1 Hneed.
    assert (H6 : (6 <= n)%nat)
      by (destruct args as [| ? [| ? [| ? ?]]]; simpl in Hneed; lia).
    assert (Hna : exists na : nat, n = (6 + na)%nat)
      by (exists (n - 6)%nat; lia).
    destruct Hna as [na ->].
    iIntros "Ht #Hcode #Hro #Hargv Hbuf Hrun".
    iDestruct (uargv_align with "Hargv") as %[Hal Hargc].
    change (2 ^ 31) with 2147483648 in Hargc.
    destruct grep_syms_pins
      as (_ & Hmain & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
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
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x1d0  c.addi16sp sp,sp,-48 ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x1d0)
              (mword_of_int 61 : mword 6) 6 na
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_1d0 with "Hcode"). }
    iIntros "Hframe".
    rewrite Hsp.
    rewrite (_ : add_vec_int (mword_of_int 0x1d0 : mword 64) 2
                 = mword_of_int 0x1d2);
      [ | apply bv_eq; vm_compute; reflexivity ].
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
    (* ---- 0x1d2..0x1dc  the six spills ---- *)
    iApply (wp_uk_csdsp N h0 m1 (mword_of_int 0x1d2)
              (mword_of_int 5 : mword 6) ra_idx (uint sp0 - 8) w1 na
              ltac:(rewrite Hsp1 Hsp48 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_grep_1d2 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x1d2 : mword 64) 2
                 = mword_of_int 0x1d4);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x1d4)
              (mword_of_int 4 : mword 6) s0_idx (uint sp0 - 16) w2 na
              ltac:(rewrite Hsp1 Hsp48 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_grep_1d4 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x1d4 : mword 64) 2
                 = mword_of_int 0x1d6);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0x1d6)
              (mword_of_int 3 : mword 6) s1_idx (uint sp0 - 24) w3 na
              ltac:(rewrite Hsp1 Hsp48 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_grep_1d6 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x1d6 : mword 64) 2
                 = mword_of_int 0x1d8);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    iApply (wp_uk_csdsp N h3 m1 (mword_of_int 0x1d8)
              (mword_of_int 2 : mword 6) s2_idx (uint sp0 - 32) w4 na
              ltac:(rewrite Hsp1 Hsp48 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_grep_1d8 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x1d8 : mword 64) 2
                 = mword_of_int 0x1da);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h4) "Hrun".
    iApply (wp_uk_csdsp N h4 m1 (mword_of_int 0x1da)
              (mword_of_int 1 : mword 6) s3_idx (uint sp0 - 40) w5 na
              ltac:(rewrite Hsp1 Hsp48 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_grep_1da with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x1da : mword 64) 2
                 = mword_of_int 0x1dc);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h5) "Hrun".
    iApply (wp_uk_csdsp N h5 m1 (mword_of_int 0x1dc)
              (mword_of_int 0 : mword 6) s4_idx (uint sp0 - 48) w6 na
              ltac:(rewrite Hsp1 Hsp48 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_grep_1dc with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x1dc : mword 64) 2
                 = mword_of_int 0x1de);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h6) "Hrun".
    (* ---- 0x1de  c.addi4spn s0,sp,48 -- the frame pointer ---- *)
    iApply (wp_uk_caddi4spn N h6 m1 (mword_of_int 0x1de)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))
              na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_grep_1de with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1de : mword 64) 2
                 = mword_of_int 0x1e0);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h7) "Hrun".
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
    (* ---- 0x1e0  c.li a5,1 ---- *)
    iApply (wp_uk_cli N h7 m2 (mword_of_int 0x1e0)
              (mword_of_int 1 : mword 6) a5_idx na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_1e0 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1e0 : mword 64) 2
                 = mword_of_int 0x1e2);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h8) "Hrun".
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
    (* ---- 0x1e2  bge a5,a0,0x22e -- a pattern at all? ---- *)
    assert (Hge : uv_btaken BGE (m3 !!! Regidx a5_idx) (m3 !!! Regidx a0_idx)
                  = Z.geb 1 (Z.of_nat (length args))).
    { rewrite Ha5_3 Ha0_3. cbn [uv_btaken].
      apply (moi_ge_s 1 (Z.of_nat (length args)));
        unfold Z63; lia. }
    destruct (Nat.le_gt_cases (length args) 1) as [Hle | Hgt].
    { (* NO PATTERN: the usage line ---- *)
      assert (Ht : true
                   = uv_btaken BGE (m3 !!! Regidx a5_idx)
                       (m3 !!! Regidx a0_idx))
        by (rewrite Hge; symmetry; apply Z.geb_le; lia).
      assert (Etgt : add_vec (mword_of_int 0x1e2 : mword 64)
                       (sign_extend' 64 (mword_of_int 76 : mword 13))
                     = mword_of_int 0x22e)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype N h8 m3 (mword_of_int 0x1e2)
                (mword_of_int 76 : mword 13) a0_idx a5_idx BGE true
                (mword_of_int 0x22e) na Ht
                (eq_sym Etgt) ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_1e2 with "Hcode"). }
      iIntros (h9) "Hrun".
      rewrite (grep_main_words_usage args Hle) in Hneed.
      assert (Hlm : (length (map uarg_bytes args) <= 1)%nat)
        by (rewrite length_map; lia).
      iEval (rewrite (grep_tree_usage (map uarg_bytes args) Hlm)) in "Ht".
      iApply (wp_kgrep_main_usage h9 m3 na ltac:(lia) with "Ht Hcode Hro Hrun"). }
    (* A PATTERN: s4 := argv[1] ---- *)
    assert (Hnt : false
                  = uv_btaken BGE (m3 !!! Regidx a5_idx)
                      (m3 !!! Regidx a0_idx)).
    { rewrite Hge. symmetry. apply not_true_is_false. intro HH.
      apply Z.geb_le in HH. lia. }
    iApply (wp_uk_btype N h8 m3 (mword_of_int 0x1e2)
              (mword_of_int 76 : mword 13) a0_idx a5_idx BGE false
              (add_vec (mword_of_int 0x1e2 : mword 64)
                 (sign_extend' 64 (mword_of_int 76 : mword 13)))
              na Hnt eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_grep_1e2 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1e2 : mword 64) 4
                 = mword_of_int 0x1e6);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h9) "Hrun".
    (* the argv vector's extent, off the heap *)
    destruct (lookup_lt_is_Some_2 args 0%nat ltac:(lia)) as [g0 Hg0].
    destruct (lookup_lt_is_Some_2 args 1%nat ltac:(lia)) as [g1 Hg1].
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
    iDestruct (uargv_acc γd av args 1%nat g1 Hg1 with "Hargv")
      as "[[#Hw1a #Hpat] _]".
    (* ---- 0x1e6  ld s4,8(a1) ---- *)
    assert (Haddr : (av + 8 * Z.of_nat 1)%Z
                    = uint (m3 !!! Regidx a1_idx)
                      + uoff_i12 (mword_of_int 8 : mword 12)).
    { rewrite Ha1_3 (uint_moi av ltac:(unfold Z64; lia)).
      replace (uoff_i12 (mword_of_int 8 : mword 12)) with 8
        by (vm_compute; reflexivity).
      lia. }
    assert (Hal1 : (av + 8 * Z.of_nat 1) mod 8 = 0).
    { rewrite Z.add_mod; [ | lia ]. rewrite Hal Z.mul_comm Z_mod_mult.
      reflexivity. }
    iApply (wp_uk_ld N h9 m3 (mword_of_int 0x1e6)
              (mword_of_int 8 : mword 12) a1_idx s4_idx DfracDiscarded
              (av + 8 * Z.of_nat 1) (mword_of_int (ua_ptr g1)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hal1 ltac:(vm_compute; discriminate)
              with "[] Hw1a Hrun").
    { iApply (uis_grep_1e6 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1e6 : mword 64) 4
                 = mword_of_int 0x1ea);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros "_" (h10) "Hrun".
    set (m4 := <[Regidx s4_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr g1) : mword 64)]> m3).
    assert (Hs4_4 : m4 !!! Regidx s4_idx = mword_of_int (ua_ptr g1))
      by exact (upd_eq m3 (Regidx s4_idx) (regval_into_reg _)).
    assert (Ha0_4 : m4 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat (length args))).
    { rewrite <- Ha0_3.
      exact (upd_ne m3 (Regidx s4_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1_4 : m4 !!! Regidx a1_idx = mword_of_int av).
    { rewrite <- Ha1_3.
      exact (upd_ne m3 (Regidx s4_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hsp4 : m4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite <- Hsp3.
      exact (upd_ne m3 (Regidx s4_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1ea  c.li a5,2 ---- *)
    iApply (wp_uk_cli N h10 m4 (mword_of_int 0x1ea)
              (mword_of_int 2 : mword 6) a5_idx na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_grep_1ea with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1ea : mword 64) 2
                 = mword_of_int 0x1ec);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h11) "Hrun".
    set (m5 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 2 : mword 6)
                       : mword 64)]> m4).
    assert (Ha5_5 : m5 !!! Regidx a5_idx = mword_of_int 2).
    { rewrite (upd_eq m4 (Regidx a5_idx) (regval_into_reg _)).
      apply bv_eq. vm_compute. reflexivity. }
    assert (Ha0_5 : m5 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat (length args))).
    { rewrite <- Ha0_4.
      exact (upd_ne m4 (Regidx a5_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1_5 : m5 !!! Regidx a1_idx = mword_of_int av).
    { rewrite <- Ha1_4.
      exact (upd_ne m4 (Regidx a5_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hs4_5 : m5 !!! Regidx s4_idx = mword_of_int (ua_ptr g1)).
    { rewrite <- Hs4_4.
      exact (upd_ne m4 (Regidx a5_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hsp5 : m5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite <- Hsp4.
      exact (upd_ne m4 (Regidx a5_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1ec  bge a5,a0,0x242 -- any file named? ---- *)
    assert (Hge2 : uv_btaken BGE (m5 !!! Regidx a5_idx) (m5 !!! Regidx a0_idx)
                   = Z.geb 2 (Z.of_nat (length args))).
    { rewrite Ha5_5 Ha0_5. cbn [uv_btaken].
      apply (moi_ge_s 2 (Z.of_nat (length args)));
        unfold Z63; lia. }
    destruct (Nat.le_gt_cases (length args) 2) as [Hle2 | Hgt2].
    { (* THE PATTERN ALONE: grep the standard input ---- *)
      assert (Hl2 : length args = 2%nat) by lia.
      assert (Ht : true
                   = uv_btaken BGE (m5 !!! Regidx a5_idx)
                       (m5 !!! Regidx a0_idx))
        by (rewrite Hge2; symmetry; apply Z.geb_le; lia).
      assert (Etgt : add_vec (mword_of_int 0x1ec : mword 64)
                       (sign_extend' 64 (mword_of_int 86 : mword 13))
                     = mword_of_int 0x242)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype N h11 m5 (mword_of_int 0x1ec)
                (mword_of_int 86 : mword 13) a0_idx a5_idx BGE true
                (mword_of_int 0x242) na Ht
                (eq_sym Etgt) ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_1ec with "Hcode"). }
      iIntros (h12) "Hrun".
      rewrite (grep_main_words_stdin args g1 Hl2 Hg1) in Hneed.
      iEval (rewrite (grep_tree_stdin args g1 Hl2 Hg1)) in "Ht".
      iApply (wp_kgrep_main_stdin h12 m5 g1 f na ltac:(lia) Hs4_5
                with "Ht Hcode Hpat Hbuf Hrun"). }
    (* FILES: set up the walk over argv[2..argc) ---- *)
    assert (Hl3 : (3 <= length args)%nat) by lia.
    rewrite (grep_main_words_files args g1 Hl3 Hg1) in Hneed.
    assert (Hmx : (grep_words (uarg_bytes g1) <= na /\ 28 <= na)%nat)
      by (apply Nat.max_lub_iff; lia).
    destruct Hmx as [Hwn H28].
    iEval (rewrite (grep_tree_files args g1 Hl3 Hg1)) in "Ht".
    assert (Hnt2 : false
                   = uv_btaken BGE (m5 !!! Regidx a5_idx)
                       (m5 !!! Regidx a0_idx)).
    { rewrite Hge2. symmetry. apply not_true_is_false. intro HH.
      apply Z.geb_le in HH. lia. }
    iApply (wp_uk_btype N h11 m5 (mword_of_int 0x1ec)
              (mword_of_int 86 : mword 13) a0_idx a5_idx BGE false
              (add_vec (mword_of_int 0x1ec : mword 64)
                 (sign_extend' 64 (mword_of_int 86 : mword 13)))
              na Hnt2 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_grep_1ec with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1ec : mword 64) 4
                 = mword_of_int 0x1f0);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h12) "Hrun".
    (* ---- 0x1f0  addi s2,a1,16 -- &argv[2] ---- *)
    assert (E16 : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                  = mword_of_int 16)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi N h12 m5 (mword_of_int 0x1f0)
              (mword_of_int 16 : mword 12) a1_idx s2_idx
              (mword_of_int (av + 8 * Z.of_nat 2)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_5 E16 moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_grep_1f0 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1f0 : mword 64) 4
                 = mword_of_int 0x1f4);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h13) "Hrun".
    set (m6 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (av + 8 * Z.of_nat 2) : mword 64)]> m5).
    assert (Ha0_6 : m6 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat (length args))).
    { rewrite <- Ha0_5.
      exact (upd_ne m5 (Regidx s2_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1f4  addiw s3,a0,-3 ---- *)
    assert (Em3 : (sign_extend' 64 (mword_of_int 4093 : mword 12)
                   : mword 64)
                  = mword_of_int (-3))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addiw N h13 m6 (mword_of_int 0x1f4)
              (mword_of_int 4093 : mword 12) a0_idx s3_idx
              (mword_of_int (Z.of_nat (length args) - 3)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6 Em3
                      (moi_addw (Z.of_nat (length args)) (-3)
                         ltac:(unfold Z31; lia));
                    f_equal; lia)
              with "[] Hrun").
    { iApply (uis_grep_1f4 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1f4 : mword 64) 4
                 = mword_of_int 0x1f8);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h14) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (length args) - 3)
                       : mword 64)]> m6).
    assert (Hs3_7 : m7 !!! Regidx s3_idx
                    = mword_of_int (Z.of_nat (length args) - 3))
      by exact (upd_eq m6 (Regidx s3_idx) (regval_into_reg _)).
    (* ---- 0x1f8  slli a5,s3,32 ---- *)
    iApply (wp_uk_slli N h14 m7 (mword_of_int 0x1f8)
              (mword_of_int 32 : mword 6) s3_idx a5_idx
              (shift_bits_left
                 (mword_of_int (Z.of_nat (length args) - 3) : mword 64)
                 (subrange_vec_dec (mword_of_int 32 : mword 6)
                    (Z.sub log2_xlen 1) 0))
              na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_7; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_1f8 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1f8 : mword 64) 4
                 = mword_of_int 0x1fc);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h15) "Hrun".
    set (m8 := <[Regidx a5_idx
                 := regval_into_reg
                      (shift_bits_left
                         (mword_of_int (Z.of_nat (length args) - 3)
                          : mword 64)
                         (subrange_vec_dec (mword_of_int 32 : mword 6)
                            (Z.sub log2_xlen 1) 0))]> m7).
    assert (Ha5_8 : m8 !!! Regidx a5_idx
                    = shift_bits_left
                        (mword_of_int (Z.of_nat (length args) - 3)
                         : mword 64)
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0))
      by exact (upd_eq m7 (Regidx a5_idx) (regval_into_reg _)).
    (* ---- 0x1fc  srli s3,a5,29 : s3 := 8 * (argc - 3) ---- *)
    iApply (wp_uk_srli N h15 m8 (mword_of_int 0x1fc)
              (mword_of_int 29 : mword 6) a5_idx s3_idx
              (mword_of_int ((Z.of_nat (length args) - 3) * 8)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_8; symmetry;
                    exact (moi_shl32_shr29 (Z.of_nat (length args) - 3)
                             ltac:(unfold Z32; lia)))
              with "[] Hrun").
    { iApply (uis_grep_1fc with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1fc : mword 64) 4
                 = mword_of_int 0x200);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h16) "Hrun".
    set (m9 := <[Regidx s3_idx
                 := regval_into_reg
                      (mword_of_int ((Z.of_nat (length args) - 3) * 8)
                       : mword 64)]> m8).
    assert (Ha1_9 : m9 !!! Regidx a1_idx = mword_of_int av).
    { rewrite <- Ha1_5.
      rewrite /m9 (upd_ne m8 (Regidx s3_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m8 (upd_ne m7 (Regidx a5_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m7 (upd_ne m6 (Regidx s3_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m6. exact (upd_ne m5 (Regidx s2_idx) (Regidx a1_idx) _
                            ltac:(vm_compute; discriminate)). }
    (* ---- 0x200  c.addi a1,a1,24 ---- *)
    assert (E24 : (sign_extend' 64 (mword_of_int 24 : mword 6) : mword 64)
                  = mword_of_int 24)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h16 m9 (mword_of_int 0x200)
              (mword_of_int 24 : mword 6) a1_idx (mword_of_int (av + 24)) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_9 E24 moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_200 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x200 : mword 64) 2
                 = mword_of_int 0x202);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h17) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int (av + 24) : mword 64)]> m9).
    assert (Hs3_10 : m10 !!! Regidx s3_idx
                     = mword_of_int ((Z.of_nat (length args) - 3) * 8)).
    { rewrite /m10 (upd_ne m9 (Regidx a1_idx) (Regidx s3_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /m9. exact (upd_eq m8 (Regidx s3_idx) (regval_into_reg _)). }
    assert (Ha1_10 : m10 !!! Regidx a1_idx = mword_of_int (av + 24))
      by exact (upd_eq m9 (Regidx a1_idx) (regval_into_reg _)).
    (* ---- 0x202  c.add s3,s3,a1 : s3 := &argv[argc] ---- *)
    iApply (wp_uk_cadd N h17 m10 (mword_of_int 0x202) s3_idx a1_idx
              (mword_of_int (av + 8 * Z.of_nat (length args))) na
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_10 Ha1_10 moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_grep_202 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x202 : mword 64) 2
                 = mword_of_int 0x204);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h18) "Hrun".
    set (m11 := <[Regidx s3_idx
                  := regval_into_reg
                       (mword_of_int (av + 8 * Z.of_nat (length args))
                        : mword 64)]> m10).
    assert (Hinv : gm_inv sp0 av (length args) 2 (ua_ptr g1) m11).
    { unfold gm_inv. split_and!.
      - rewrite /m11 (upd_ne m10 (Regidx s3_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        rewrite /m10 (upd_ne m9 (Regidx a1_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        rewrite /m9 (upd_ne m8 (Regidx s3_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m8 (upd_ne m7 (Regidx a5_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_ne m6 (Regidx s3_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6 (upd_ne m5 (Regidx s2_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        exact Hsp5.
      - rewrite /m11 (upd_ne m10 (Regidx s3_idx) (Regidx s2_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /m10 (upd_ne m9 (Regidx a1_idx) (Regidx s2_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /m9 (upd_ne m8 (Regidx s3_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m8 (upd_ne m7 (Regidx a5_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_ne m6 (Regidx s3_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6. exact (upd_eq m5 (Regidx s2_idx) (regval_into_reg _)).
      - exact (upd_eq m10 (Regidx s3_idx) (regval_into_reg _)).
      - rewrite /m11 (upd_ne m10 (Regidx s3_idx) (Regidx s4_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /m10 (upd_ne m9 (Regidx a1_idx) (Regidx s4_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /m9 (upd_ne m8 (Regidx s3_idx) (Regidx s4_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m8 (upd_ne m7 (Regidx a5_idx) (Regidx s4_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m7 (upd_ne m6 (Regidx s3_idx) (Regidx s4_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m6 (upd_ne m5 (Regidx s2_idx) (Regidx s4_idx) _
                       ltac:(vm_compute; discriminate)).
        exact Hs4_5. }
    iApply (wp_kgrep_main_loop sp0 av args g1 (length args - 3)%nat
              Hav0' Havhi' Hptr Hg1 2%nat h18 m11 f na ltac:(lia)
              Hwn H28 Hinv
              with "Ht Hcode Hro Hargv Hbuf Hrun").
  Qed.

End UkGrepMain.
