(* ===================================================================== *)
(* UkShFork.v -- sh's FORK ARM: the four instructions of main's body that  *)
(* start a command, and the payload that crosses the fork with it.        *)
(*                                                                        *)
(*   0x92c  jal  ra,fork1                                                 *)
(*   0x930  c.beqz a0,0x9c0        the CHILD -- parse and exec            *)
(*   0x932  c.li a0,0                                                     *)
(*   0x934  jal  ra,wait           the PARENT -- reap, and round again    *)
(*          ...falls into 0x938, the loop head                            *)
(*                                                                        *)
(* FOUR INSTRUCTIONS AND TWO PROCESSES.  [UkShDiag.wp_kshr_fork1_final]    *)
(* already carries fork1's own [-1 -> panic -> exit] arm, so what is left  *)
(* is a pair of continuations: the parent's, which reaps and goes back to  *)
(* the command loop, and the child's, which is                            *)
(* [UkShMain.wp_kshm_child_alloc] -- the parse, the runner, and [exec].    *)
(*                                                                        *)
(* WHAT CROSSES, AND WHY IT IS SHAPED THIS WAY.  [Forkable P] hands the    *)
(* PARENT [P] back and mints the CHILD's copy at FRESH ghost names, which  *)
(* is exactly the address-space copy fork performs.  So the payload is     *)
(* everything the child's walk reads out of memory:                        *)
(*                                                                        *)
(*   the text and its jump table  (persistent, and the same proposition    *)
(*                                 as the parser's [shp_code]/[shp_rodata])*)
(*   the two static lexer tables at 0x2000 / 0x2008                        *)
(*   the allocator's untouched first-call state ([freep] = 0, [base])      *)
(*   the whole line buffer                                                 *)
(*                                                                        *)
(* THE BREAK IS NOT IN IT.  [usz] is a ghost var, not bytes, so it cannot  *)
(* be [Forkable]; [wp_kshr_fork1_final] hands [usz gs szv] to the child     *)
(* itself.  The child assembles [UkShMalloc.ushm_fresh] out of that and    *)
(* the payload's two data cells.                                           *)
(*                                                                        *)
(* AND FIRST-CALL-ONLY MALLOC IS ENOUGH FOREVER, which is worth saying     *)
(* out loud because it looks like a gap and is not: the PARENT never calls *)
(* [malloc].  Only the forked child does, exactly once, in a fresh copy of *)
(* the address space.  So the parent carrying an untouched [ushf_dat]      *)
(* round the loop is the actual control flow and not a weakening.          *)
(*                                                                        *)
(* WHAT THIS IS NOT YET.  [UkSh.ush_rest] hands its walk [16 + n] and      *)
(* carries neither the tables, nor the allocator state, nor [usz]; this    *)
(* arm needs all three and a budget of [16 + (80 + n)] (fork1's 2, the     *)
(* diagnostic subtree's 28, the parser's 60 and the runner's 8).  So the   *)
(* loop head is stated HERE, as [ushf_head], at the interface the re-cut   *)
(* will have to meet.  The other reason [ush_rest] is not dischargeable is *)
(* not about fork at all: the child's walk needs the line to be one the    *)
(* LEXER ACCEPTS ([ushp_no_symbols], fewer than MAXARGS tokens), and the   *)
(* command loop cannot promise that about a line the user typed.  That is  *)
(* stage 5's [ush_simple] scope -- the REDIRECT and PIPE arms -- and it is *)
(* a premise here for the same reason [UkShCd] takes "this line begins     *)
(* cd " as one.                                                            *)
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
Require Import UserBits.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk.
Require Import UkStep.
From Stdlib Require Import FunctionalExtensionality.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import UkFork.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShCd.
Require Import UkShMain.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UkShFork.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

  Local Notation ush_std := (UkSh.ush_std γfd).
  Local Notation ushl_dat := (UkShLoop.ushl_dat γd).
  Local Notation ushl_head := (UkShLoop.ushl_head γt γd γs γfd).

  (* ===================================================================== *)
  (* §1 THE TWO CATALOG BRIDGES THE CHILD NEEDS.                            *)
  (*                                                                        *)
  (* The payload carries the KERNEL-lane catalog's names because that is    *)
  (* what fork1 hands over; the child's walk asks for the PARSER lane's.    *)
  (* They are the same propositions -- [shp_code] and [shk_code] are both   *)
  (* [utext_img g ShInstrs.sh_bytes], and [shp_ro] and [shk_ro] are the     *)
  (* same filter of [ShData.sh_data] -- so each bridge is one line.         *)
  (* ===================================================================== *)
  Lemma ushf_code_shp (g : gname) : shk_code g -∗ shp_code g.
  Proof. rewrite /shk_code /shp_code. iIntros "#H". iExact "H". Qed.

  Lemma ushf_rodata_shp (g : gname) : shk_rodata g -∗ shp_rodata g.
  Proof.
    rewrite /shk_rodata /shp_rodata /shk_ro /shp_ro.
    iIntros "#H". iExact "H".
  Qed.

  (* ===================================================================== *)
  (* §2 THE PAYLOAD.                                                        *)
  (*                                                                        *)
  (* Everything the child's walk reads out of memory: the text and its jump *)
  (* table, and the DATA half a turn of the loop carries                    *)
  (* ([UkShLoop.ushl_dat] -- the two lexer tables and the allocator's       *)
  (* first-call state) plus the line buffer itself.                        *)
  (* ===================================================================== *)
  Definition ushf_pay (f : nat -> bv 8)
      : gname -> gname -> gname -> iProp Σ :=
    fun gt gd _ =>
      (shk_code gt ∗ shk_rodata gt ∗ ush_jtab gt ∗
       UkShLoop.ushl_dat gd ∗ ubytes gd sh_buf sh_nbuf f)%I.

  Global Instance forkable_ushf_pay (f : nat -> bv 8) :
    Forkable (ushf_pay f).
  Proof.
    rewrite /ushf_pay /UkShLoop.ushl_dat.
    apply forkable_sep; [ apply forkable_shk_code | ].
    apply forkable_sep; [ apply forkable_shk_rodata | ].
    apply forkable_sep; [ apply forkable_ush_jtab | ].
    apply forkable_sep; [ | apply forkable_ubytes ].
    apply forkable_sep; [ apply forkable_ustr_disc | ].
    apply forkable_sep; [ apply forkable_ustr_disc | ].
    apply forkable_sep; [ apply forkable_uword | ].
    apply forkable_exist. intros fb. apply forkable_ubytes.
  Qed.

  (* what a nonzero pid does to the [c.beqz] at 0x930 *)
  Lemma ushf_eqv_false (x : mword 64) :
    x <> (mword_of_int 0 : mword 64) -> eq_vec x zero_reg = false.
  Proof.
    intros H. apply (proj2 (eq_vec_false_iff x zero_reg)).
    rewrite zero_reg_moi. exact H.
  Qed.

  (* ===================================================================== *)
  (* §3 THE ARM.                                                            *)
  (* ===================================================================== *)
  Lemma wp_kshf_fork
      (Hsbrk : forall (gd gs : gname) (sz n : Z) (r : mword 64),
         UkShMalloc.ushm_sbrk_ans gd gs sz n r -∗
         ⌜ r = (mword_of_int sz : mword 64) ⌝ ∗
         UkShMalloc.ushm_sbrk_ans gd gs sz n r)
      (Hclw : UkShDiag.ushd_clw_text_ty)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (toks : list (nat * nat)) (sz : Z) (l : list fdstate) (n : nat) :
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    (* the line at [k] is one the LEXER accepts -- see the header *)
    ushp_no_symbols len (fun j : nat => f (k + j)%nat) ->
    ushp_tokens len (fun j : nat => f (k + j)%nat) 0 toks ->
    (length toks < 10)%nat ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    ushl_head l sz -∗
    shk_code γt -∗ shk_rodata γt -∗ ush_jtab γt -∗
    ush_std l -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h m (mword_of_int 0x92c) (16 + (80 + n)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hregs Hs1 Hns Htoks Htlen Hnn Hnul Hkl Hszlo Hszal Hszok.
    iIntros "Hhead #Hcode #Hro #Hjt Hstd Hdat Hsz Hbuf Hrun".
    destruct Hregs as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    iDestruct "Hstd" as "[Hustd %Hlow]".
    assert (Hlen31 : Z.of_nat len < 2 ^ 31)
      by (unfold sh_nbuf in Hkl; lia).
    (* ---- 0x92c  jal ra,fork1 ---- *)
    iApply (wp_uk_jal γt γd γs γfd h m (mword_of_int 0x92c)
              (mword_of_int 2094908 : mword 21) ra_idx
              (mword_of_int ShSyms.fork1) (mword_of_int 0x930)
              (16 + (80 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_92c with "Hcode"). }
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x930 : mword 64)]> m).
    assert (Hra_1 : m1 !!! Regidx ra_idx = (mword_of_int 0x930 : mword 64))
      by exact (upd_eq m (Regidx ra_idx) _).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx ra_idx) (Regidx q) _ Hq)).
    (* ---- fork1() ---- *)
    replace (16 + (80 + n))%nat with (2 + (UkShDiag.ush_Dg + (66 + n)))%nat
      by (unfold UkShDiag.ush_Dg; lia).
    iApply (UkShDiag.wp_kshr_fork1_final γt γd γs γfd (ushf_pay f)
              sz l ∅ h1 m1 (66 + n)
              with "Hcode Hro [Hdat Hbuf] Hsz Hustd [] Hrun").
    { rewrite /ushf_pay.
      iSplitR; [ iExact "Hcode" | ].
      iSplitR; [ iExact "Hro" | ].
      iSplitR; [ iExact "Hjt" | ].
      iFrame "Hdat Hbuf". }
    { rewrite big_sepM_empty. done. }
    rewrite Hra_1.
    assert (Eret : ret_pc (mword_of_int 0x930 : mword 64)
                   = mword_of_int 0x930)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    iSplitL "Hhead".
    - (* ================= THE PARENT: reap, and round again ============= *)
      iIntros (hA mA rA) "%HrA %HcsA %Ha0A Hpay Hsz Hustd _ Hrun".
      iDestruct "Hpay" as "(_ & _ & _ & Hdat & Hbuf)".
      (* ---- 0x930  c.beqz a0,0x9c0 -- NOT taken: this is the parent ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd hA mA (mword_of_int 0x930)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x9c0)
                (2 + (UkShDiag.ush_Dg + (66 + n)))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0A; symmetry; exact (ushf_eqv_false rA HrA))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_930 with "Hcode"). }
      assert (E930 : add_vec_int (mword_of_int 0x930 : mword 64) 2
                     = mword_of_int 0x932)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E930. iIntros (hB) "Hrun".
      (* ---- 0x932  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs γfd hB mA (mword_of_int 0x932)
                (mword_of_int 0 : mword 6) a0_idx
                (2 + (UkShDiag.ush_Dg + (66 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_shk_932 with "Hcode"). }
      assert (Em0 : <[Regidx a0_idx
                      := regval_into_reg (sign_extend' 64
                           (mword_of_int 0 : mword 6) : mword 64)]> mA
                    = <[Regidx a0_idx
                        := regval_into_reg (mword_of_int 0 : mword 64)]> mA)
        by (f_equal; apply bv_eq; vm_compute; reflexivity).
      assert (E932 : add_vec_int (mword_of_int 0x932 : mword 64) 2
                     = mword_of_int 0x934)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E932 Em0. iIntros (hC) "Hrun".
      set (mB := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> mA).
      (* ---- 0x934  jal ra,wait ---- *)
      iApply (wp_uk_jal γt γd γs γfd hC mB (mword_of_int 0x934)
                (mword_of_int 858 : mword 21) ra_idx
                (mword_of_int ShSyms.wait) (mword_of_int 0x938)
                (2 + (UkShDiag.ush_Dg + (66 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_934 with "Hcode"). }
      iIntros (hD) "Hrun".
      set (mC := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x938 : mword 64)]> mB).
      assert (Ha0_C : uint (mC !!! Regidx a0_idx) = 0).
      { rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mB (upd_eq mA (Regidx a0_idx) _).
        exact (uint_moi 0 ltac:(unfold Z64; lia)). }
      assert (Hra_C : mC !!! Regidx ra_idx = (mword_of_int 0x938 : mword 64))
        by exact (upd_eq mB (Regidx ra_idx) _).
      (* ---- wait((int * )0) ---- *)
      iApply (UkShRun.wp_kshr_wait γt γd γs γfd hD mC
                (2 + (UkShDiag.ush_Dg + (66 + n))) Ha0_C
                with "Hcode Hrun").
      iIntros (hE ret) "Hrun".
      rewrite Hra_C.
      assert (Eret2 : ret_pc (mword_of_int 0x938 : mword 64)
                      = mword_of_int 0x938)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eret2.
      set (mD := <[Regidx a0_idx := ret]>
                   (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> mC)).
      (* the five constants are still where main put them *)
      assert (HkeepD : forall q : mword 5,
                ucallee_saved_idx q = true ->
                mD !!! Regidx q = m !!! Regidx q).
      { intros q Hq.
        assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                        Regidx q <> Regidx rq).
        { intros rq Hr He. injection He as He. subst q.
          rewrite Hr in Hq. discriminate Hq. }
        assert (Fra : ucallee_saved_idx ra_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa0 : ucallee_saved_idx a0_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa7 : ucallee_saved_idx a7_idx = false)
          by (vm_compute; reflexivity).
        rewrite /mD (upd_ne _ (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
        rewrite (upd_ne mC (Regidx a7_idx) (Regidx q) _ (Hne a7_idx Fa7)).
        rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx q) _ (Hne ra_idx Fra)).
        rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
        rewrite (HcsA q Hq).
        exact (Hm1 q (Hne ra_idx Fra)). }
      assert (HregsD : UkSh.ush_regs mD).
      { rewrite /UkSh.ush_regs. split_and!.
        - rewrite (HkeepD s2_idx ltac:(vm_compute; reflexivity)). exact Hs2.
        - rewrite (HkeepD s3_idx ltac:(vm_compute; reflexivity)). exact Hs3.
        - rewrite (HkeepD s4_idx ltac:(vm_compute; reflexivity)). exact Hs4.
        - rewrite (HkeepD s5_idx ltac:(vm_compute; reflexivity)). exact Hs5.
        - rewrite (HkeepD s6_idx ltac:(vm_compute; reflexivity)). exact Hs6. }
      replace (2 + (UkShDiag.ush_Dg + (66 + n)))%nat
        with (16 + (80 + n))%nat by (unfold UkShDiag.ush_Dg; lia).
      iApply ("Hhead" $! hE mD f n with "[%] [Hustd] Hdat Hsz Hbuf Hrun").
      + exact HregsD.
      + rewrite /UkSh.ush_std. iFrame "Hustd". iPureIntro. exact Hlow.
    - (* ================= THE CHILD: parse, run, exec =================== *)
      iIntros (gt gd gs gfd hA mA) "%HcsA %Ha0A #Hcode' Hpay Hsz Hustd _ Hrun".
      iDestruct "Hpay" as "(_ & #Hro' & #Hjt' & Hdat & Hbuf)".
      (* ---- 0x930  c.beqz a0,0x9c0 -- TAKEN: this is the child ---- *)
      iApply (wp_uk_cbeqz gt gd gs gfd hA mA (mword_of_int 0x930)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x9c0)
                (2 + (UkShDiag.ush_Dg + (66 + n)))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0A; symmetry;
                      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia));
                      reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_930 with "Hcode'"). }
      iIntros (hB) "Hrun".
      (* the line, cut out of the child's own copy of the buffer *)
      iDestruct (UkShCd.ushc_bytes_sub gd sh_buf sh_nbuf f k (S len)
                   ltac:(lia) with "Hbuf") as "[Hsub _]".
      iDestruct (UkShCd.ushc_ustr_of_bytes gd (sh_buf + Z.of_nat k) len
                   (fun j : nat => f (k + j)%nat) Hnn Hlen31 Hnul
                   with "Hsub") as "Hline".
      iDestruct (UkShLoop.ushl_fresh_of_dat gd gs sz with "Hdat Hsz")
        as "(Hfresh & Hws & Hsy)".
      assert (Hs1_A : mA !!! Regidx s1_idx
                      = (mword_of_int (sh_buf + Z.of_nat k) : mword 64)).
      { rewrite (HcsA s1_idx ltac:(vm_compute; reflexivity)).
        rewrite (Hm1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1. }
      replace (2 + (UkShDiag.ush_Dg + (66 + n)))%nat
        with (60 + (8 + (UkShDiag.ush_Dg + n)))%nat
        by (unfold UkShDiag.ush_Dg; lia).
      iApply (UkShMain.wp_kshm_child_alloc gt gd gs gfd (Hsbrk gd gs) Hclw
                hB mA DfracDiscarded DfracDiscarded
                (sh_buf + Z.of_nat k) len (fun j : nat => f (k + j)%nat)
                toks sz l n
                Hs1_A Hns Htoks Htlen
                ltac:(unfold sh_buf; lia)
                ltac:(unfold sh_buf, sh_nbuf, Z64 in *; lia)
                ltac:(unfold sh_buf, sh_nbuf in *; lia)
                Hszlo Hszal Hszok
                with "Hcode' [] [] Hjt' Hline Hws Hsy Hustd Hfresh Hrun").
      + iApply (ushf_code_shp with "Hcode'").
      + iApply (ushf_rodata_shp with "Hro'").
  Qed.

  (* ===================================================================== *)
  (* §4 MAIN'S BODY, WHOLE -- 0x97a..0x9be and 0x92c..0x938.                *)
  (*                                                                        *)
  (* The three byte tests are the dispatch: all three fall through and the  *)
  (* line is a [cd] command; any one of them is taken and control goes to   *)
  (* the fork.  Which one decides nothing about the walk -- every taken arm *)
  (* lands on 0x92c -- so the case split is on the three bytes and the two  *)
  (* arms are the two lemmas above.                                         *)
  (*                                                                        *)
  (* THE LOADS ARE IN BOUNDS BECAUSE OF THE STRING, not because of a        *)
  (* separate premise: [lbu a5,1(s1)] is only reached when buf[k] is 'c',   *)
  (* which is not NUL, so the line is at least one byte long and k+1 is     *)
  (* inside it; and [lbu a5,2(s1)] only when buf[k+1] is 'd' as well.       *)
  (*                                                                        *)
  (* THIS IS [UkSh.ush_rest]'S SHAPE, modulo two things and nothing else:   *)
  (* the loop head's budget and carried resources ([UkShLoop.ushl_head]     *)
  (* instead of [UkSh.ush_loop_head]), and the LEXABILITY premise, which    *)
  (* the command loop cannot supply about a line the user typed.  The       *)
  (* second is stage 5's [ush_simple] scope and not this file's.            *)
  (* ===================================================================== *)
  Lemma wp_kshm_body
      (Hsbrk : forall (gd gs : gname) (sz n : Z) (r : mword 64),
         UkShMalloc.ushm_sbrk_ans gd gs sz n r -∗
         ⌜ r = (mword_of_int sz : mword 64) ⌝ ∗
         UkShMalloc.ushm_sbrk_ans gd gs sz n r)
      (Hclw : UkShDiag.ushd_clw_text_ty)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (toks : list (nat * nat)) (sz : Z) (l : list fdstate) (n : nat) :
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (* the line at [k] *)
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* ...and it is one the LEXER accepts, which is the scope stage 5 left *)
    ushp_no_symbols len (fun j : nat => f (k + j)%nat) ->
    ushp_tokens len (fun j : nat => f (k + j)%nat) 0 toks ->
    (length toks < 10)%nat ->
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    ushl_head l sz -∗
    shk_code γt -∗ shk_rodata γt -∗ shp_code γt -∗ ush_jtab γt -∗
    ush_std l -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h m (mword_of_int 0x97a) (16 + (80 + n)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hregs Hs1 Ha5 Hnn Hnul Hkl Hns Htoks Htlen Hszlo Hszal Hszok.
    iIntros "Hhead #Hcode #Hro #Hpcode #Hjt Hstd Hdat Hsz Hbuf Hrun".
    assert (Hz0 : bv_unsigned ubyte0 = 0) by (vm_compute; reflexivity).
    assert (Hbr : forall j : nat, 0 <= bv_unsigned (f j) < Z64).
    { intros j. pose proof (bv_unsigned_in_range 8 (f j)) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. unfold Z64. lia. }
    (* THE DISPATCH IS DECIDED BEFORE ANYTHING IS WALKED, because the [cd]
       arm's own walk begins at 0x97a: the three tests belong to it, and
       this lemma may only walk them on the way OUT. *)
    destruct (decide (bv_unsigned (f k) = 99 /\
                      bv_unsigned (f (S k)) = 100 /\
                      bv_unsigned (f (S (S k))) = 32))
      as [(Hck & Hck1 & Hck2) | Hne].
    - (* ================= the line is a [cd] command =================== *)
      iApply (UkShCd.wp_kshc_cd γt γd γs γfd h m f k (k + len)%nat l sz n
                Hregs Hs1 Ha5 ltac:(lia) Hnul Hck Hck1 Hck2
                with "Hhead Hcode Hro Hpcode Hstd Hdat Hsz Hbuf Hrun").
    - (* ================= it is not: fall through to the fork ========== *)
      pose proof Hregs as Hregs'.
      destruct Hregs' as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
      destruct (decide (bv_unsigned (f k) = 99)) as [Hck | Hnck].
      + (* buf[k] is 'c', so the line is at least one byte long and the
           load at k+1 is inside it *)
        assert (HL1 : (1 <= len)%nat).
        { destruct len as [| len' ]; [ exfalso | lia ].
          rewrite Nat.add_0_r in Hnul. rewrite Hnul Hz0 in Hck. lia. }
        (* ---- 0x97a  bne a5,s5 -- NOT taken ---- *)
        assert (Htk7a : false = uv_btaken BNE (m !!! Regidx a5_idx)
                                  (m !!! Regidx s5_idx)).
        { cbn [uv_btaken]. rewrite Ha5 Hs5 Hck.
          rewrite (moi_neq_vec 99 99 ltac:(unfold Z64; lia)
                     ltac:(unfold Z64; lia)).
          symmetry. apply negb_false_iff. apply Z.eqb_eq. reflexivity. }
        iApply (wp_uk_btype γt γd γs γfd h m (mword_of_int 0x97a)
                  (mword_of_int 8114 : mword 13) s5_idx a5_idx BNE false
                  (mword_of_int 0x92c) (16 + (80 + n))
                  Htk7a
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_shk_97a with "Hcode"). }
        assert (E97a : add_vec_int (mword_of_int 0x97a : mword 64) 4
                       = mword_of_int 0x97e)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E97a. iIntros (h1) "Hrun".
        (* ---- 0x97e  lbu a5,1(s1) ---- *)
        assert (Ead1 : sh_buf + Z.of_nat (S k) = sh_buf + Z.of_nat k + 1)
          by lia.
        iDestruct (UkShCd.ushc_bytes_one γd sh_buf sh_nbuf f (S k)
                     ltac:(lia) with "Hbuf") as "[Hb1 Hcl1]".
        iEval (rewrite Ead1) in "Hb1".
        iApply (wp_uk_lbu γt γd γs γfd h1 m (mword_of_int 0x97e)
                  (mword_of_int 1 : mword 12) s1_idx a5_idx (DfracOwn 1)
                  (sh_buf + Z.of_nat k + 1) (f (S k)) (16 + (80 + n))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(rewrite Hs1
                          (uint_moi (sh_buf + Z.of_nat k)
                             ltac:(unfold sh_buf, sh_nbuf, Z64 in *; lia));
                        vm_compute uoff_i12; lia)
                  ltac:(vm_compute; discriminate)
                  with "[] Hb1 Hrun").
        { iApply (uis_shk_97e with "Hcode"). }
        iIntros "Hb1". iIntros (h2) "Hrun".
        iEval (rewrite <- Ead1) in "Hb1".
        iDestruct ("Hcl1" $! (f (S k)) with "Hb1") as "Hbuf".
        assert (Eset1 : UkSh.ush_set f (S k) (f (S k)) = f).
        { apply functional_extensionality. intros q. rewrite /UkSh.ush_set.
          destruct (Nat.eqb_spec q (S k)) as [-> | _]; reflexivity. }
        rewrite Eset1.
        assert (E97e : add_vec_int (mword_of_int 0x97e : mword 64) 4
                       = mword_of_int 0x982)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E97e.
        set (m1 := <[Regidx a5_idx
                     := regval_into_reg
                          (zero_extend' 64 (f (S k) : mword 8)
                           : mword 64)]> m).
        assert (Ha5_1 : m1 !!! Regidx a5_idx
                        = mword_of_int (bv_unsigned (f (S k))))
          by (rewrite /m1 (upd_eq m (Regidx a5_idx) _) zext8_moi; reflexivity).
        assert (Hm1 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                        m1 !!! Regidx q = m !!! Regidx q)
          by (intros q Hq; exact (upd_ne m (Regidx a5_idx) (Regidx q) _ Hq)).
        assert (Hregs1 : UkSh.ush_regs m1).
        { rewrite /UkSh.ush_regs. split_and!;
            [ rewrite (Hm1 s2_idx ltac:(vm_compute; discriminate))
            | rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate))
            | rewrite (Hm1 s4_idx ltac:(vm_compute; discriminate))
            | rewrite (Hm1 s5_idx ltac:(vm_compute; discriminate))
            | rewrite (Hm1 s6_idx ltac:(vm_compute; discriminate)) ];
            assumption. }
        assert (Hs1_1 : m1 !!! Regidx s1_idx
                        = mword_of_int (sh_buf + Z.of_nat k))
          by (rewrite (Hm1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
        assert (Hs3_1 : m1 !!! Regidx s3_idx = mword_of_int 100)
          by (rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)); exact Hs3).
        assert (Hs6_1 : m1 !!! Regidx s6_idx = mword_of_int 32)
          by (rewrite (Hm1 s6_idx ltac:(vm_compute; discriminate)); exact Hs6).
        destruct (decide (bv_unsigned (f (S k)) = 100)) as [Hck1 | Hnck1].
        * (* buf[k+1] is 'd' too, so the load at k+2 is inside the line *)
          assert (HL2 : (2 <= len)%nat).
          { destruct (Nat.lt_ge_cases len 2) as [Hlt | Hge]; [ exfalso | lia ].
            assert (E : len = 1%nat) by lia. rewrite E in Hnul.
            replace (k + 1)%nat with (S k) in Hnul by lia.
            rewrite Hnul Hz0 in Hck1. lia. }
          (* ---- 0x982  bne a5,s3 -- NOT taken ---- *)
          assert (Htk82 : false = uv_btaken BNE (m1 !!! Regidx a5_idx)
                                    (m1 !!! Regidx s3_idx)).
          { cbn [uv_btaken]. rewrite Ha5_1 Hs3_1 Hck1.
            rewrite (moi_neq_vec 100 100 ltac:(unfold Z64; lia)
                       ltac:(unfold Z64; lia)).
            symmetry. apply negb_false_iff. apply Z.eqb_eq. reflexivity. }
          iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0x982)
                    (mword_of_int 8106 : mword 13) s3_idx a5_idx BNE false
                    (mword_of_int 0x92c) (16 + (80 + n))
                    Htk82
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(discriminate)
                    with "[] Hrun").
          { iApply (uis_shk_982 with "Hcode"). }
          assert (E982 : add_vec_int (mword_of_int 0x982 : mword 64) 4
                         = mword_of_int 0x986)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E982. iIntros (h3) "Hrun".
          (* ---- 0x986  lbu a5,2(s1) ---- *)
          assert (Ead2 : sh_buf + Z.of_nat (S (S k))
                         = sh_buf + Z.of_nat k + 2) by lia.
          iDestruct (UkShCd.ushc_bytes_one γd sh_buf sh_nbuf f (S (S k))
                       ltac:(lia) with "Hbuf") as "[Hb2 Hcl2]".
          iEval (rewrite Ead2) in "Hb2".
          iApply (wp_uk_lbu γt γd γs γfd h3 m1 (mword_of_int 0x986)
                    (mword_of_int 2 : mword 12) s1_idx a5_idx (DfracOwn 1)
                    (sh_buf + Z.of_nat k + 2) (f (S (S k))) (16 + (80 + n))
                    ltac:(unfold unot_sp; vm_compute; discriminate)
                    ltac:(rewrite Hs1_1
                            (uint_moi (sh_buf + Z.of_nat k)
                               ltac:(unfold sh_buf, sh_nbuf, Z64 in *; lia));
                          vm_compute uoff_i12; lia)
                    ltac:(vm_compute; discriminate)
                    with "[] Hb2 Hrun").
          { iApply (uis_shk_986 with "Hcode"). }
          iIntros "Hb2". iIntros (h4) "Hrun".
          iEval (rewrite <- Ead2) in "Hb2".
          iDestruct ("Hcl2" $! (f (S (S k))) with "Hb2") as "Hbuf".
          assert (Eset2 : UkSh.ush_set f (S (S k)) (f (S (S k))) = f).
          { apply functional_extensionality. intros q. rewrite /UkSh.ush_set.
            destruct (Nat.eqb_spec q (S (S k))) as [-> | _]; reflexivity. }
          rewrite Eset2.
          assert (E986 : add_vec_int (mword_of_int 0x986 : mword 64) 4
                         = mword_of_int 0x98a)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E986.
          set (m2 := <[Regidx a5_idx
                       := regval_into_reg
                            (zero_extend' 64 (f (S (S k)) : mword 8)
                             : mword 64)]> m1).
          assert (Ha5_2 : m2 !!! Regidx a5_idx
                          = mword_of_int (bv_unsigned (f (S (S k)))))
            by (rewrite /m2 (upd_eq m1 (Regidx a5_idx) _) zext8_moi;
                reflexivity).
          assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                          m2 !!! Regidx q = m1 !!! Regidx q)
            by (intros q Hq;
                exact (upd_ne m1 (Regidx a5_idx) (Regidx q) _ Hq)).
          destruct Hregs1 as (K2 & K3 & K4 & K5 & K6).
          assert (Hregs2 : UkSh.ush_regs m2).
          { rewrite /UkSh.ush_regs. split_and!;
              [ rewrite (Hm2 s2_idx ltac:(vm_compute; discriminate))
              | rewrite (Hm2 s3_idx ltac:(vm_compute; discriminate))
              | rewrite (Hm2 s4_idx ltac:(vm_compute; discriminate))
              | rewrite (Hm2 s5_idx ltac:(vm_compute; discriminate))
              | rewrite (Hm2 s6_idx ltac:(vm_compute; discriminate)) ];
              assumption. }
          assert (Hs1_2 : m2 !!! Regidx s1_idx
                          = mword_of_int (sh_buf + Z.of_nat k))
            by (rewrite (Hm2 s1_idx ltac:(vm_compute; discriminate));
                exact Hs1_1).
          assert (Hs6_2 : m2 !!! Regidx s6_idx = mword_of_int 32)
            by (rewrite (Hm2 s6_idx ltac:(vm_compute; discriminate));
                exact Hs6_1).
          (* the third byte is the one that differs -- the other two just
             matched, and the line is not a [cd] command *)
          assert (Hnck2 : bv_unsigned (f (S (S k))) <> 32)
            by (intro Hc2; apply Hne; split_and!; assumption).
          (* ---- 0x98a  bne a5,s6 -- TAKEN ---- *)
          assert (Htk8a : true = uv_btaken BNE (m2 !!! Regidx a5_idx)
                                   (m2 !!! Regidx s6_idx)).
          { cbn [uv_btaken]. rewrite Ha5_2 Hs6_2.
            rewrite (moi_neq_vec (bv_unsigned (f (S (S k)))) 32
                       (Hbr (S (S k))) ltac:(unfold Z64; lia)).
            symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnck2. }
          iApply (wp_uk_btype γt γd γs γfd h4 m2 (mword_of_int 0x98a)
                    (mword_of_int 8098 : mword 13) s6_idx a5_idx BNE true
                    (mword_of_int 0x92c) (16 + (80 + n))
                    Htk8a
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(intros _; vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_shk_98a with "Hcode"). }
          iIntros (h5) "Hrun".
          iApply (wp_kshf_fork Hsbrk Hclw h5 m2 f k len toks sz l n
                    Hregs2 Hs1_2 Hns Htoks Htlen Hnn Hnul Hkl
                    Hszlo Hszal Hszok
                    with "Hhead Hcode Hro Hjt Hstd Hdat Hsz Hbuf Hrun").
        * (* ---- 0x982  bne a5,s3 -- TAKEN ---- *)
          assert (Htk82 : true = uv_btaken BNE (m1 !!! Regidx a5_idx)
                                   (m1 !!! Regidx s3_idx)).
          { cbn [uv_btaken]. rewrite Ha5_1 Hs3_1.
            rewrite (moi_neq_vec (bv_unsigned (f (S k))) 100
                       (Hbr (S k)) ltac:(unfold Z64; lia)).
            symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnck1. }
          iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0x982)
                    (mword_of_int 8106 : mword 13) s3_idx a5_idx BNE true
                    (mword_of_int 0x92c) (16 + (80 + n))
                    Htk82
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(intros _; vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_shk_982 with "Hcode"). }
          iIntros (h3) "Hrun".
          iApply (wp_kshf_fork Hsbrk Hclw h3 m1 f k len toks sz l n
                    Hregs1 Hs1_1 Hns Htoks Htlen Hnn Hnul Hkl
                    Hszlo Hszal Hszok
                    with "Hhead Hcode Hro Hjt Hstd Hdat Hsz Hbuf Hrun").
      + (* ---- 0x97a  bne a5,s5 -- TAKEN ---- *)
        assert (Htk7a : true = uv_btaken BNE (m !!! Regidx a5_idx)
                                 (m !!! Regidx s5_idx)).
        { cbn [uv_btaken]. rewrite Ha5 Hs5.
          rewrite (moi_neq_vec (bv_unsigned (f k)) 99 (Hbr k)
                     ltac:(unfold Z64; lia)).
          symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnck. }
        iApply (wp_uk_btype γt γd γs γfd h m (mword_of_int 0x97a)
                  (mword_of_int 8114 : mword 13) s5_idx a5_idx BNE true
                  (mword_of_int 0x92c) (16 + (80 + n))
                  Htk7a
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_97a with "Hcode"). }
        iIntros (h1) "Hrun".
        iApply (wp_kshf_fork Hsbrk Hclw h1 m f k len toks sz l n
                  Hregs Hs1 Hns Htoks Htlen Hnn Hnul Hkl
                  Hszlo Hszal Hszok
                  with "Hhead Hcode Hro Hjt Hstd Hdat Hsz Hbuf Hrun").
  Qed.

End UkShFork.
