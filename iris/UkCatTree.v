(* ===================================================================== *)
(* UkCatTree.v -- cat's landed obligations are INSTANCES of the tree      *)
(* payment: [UkCatMain.kcat_pay_all] at the tree [ProgTree.cat_tree] of   *)
(* its arguments' bytes, and the walk's entry at that tree.               *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.2, cut 3 (cat half).   *)
(* [UkTree] states the hole one event costs at a program instance; this   *)
(* file names cat's instance ([cat_prog]: its code and its five stubs)    *)
(* and shows that a payer of [tree_pay (cat_tree bs)] has paid every      *)
(* obligation cat's walk spends:                                          *)
(*                                                                        *)
(*   - the exit hole IS [UkCat.kcat_exit] ([kcat_exit_ex_obl]);           *)
(*   - a run of one-byte writes to fd 2 is the tree's [write_bytes]       *)
(*     ([kcat_pay_seq_tree]), and the three diagnostics are the tree's    *)
(*     three literals ([kcat_dg_cr_tree], [kcat_dg_cw_tree],             *)
(*     [kcat_dg_open_tree]);                                              *)
(*   - one turn of the loop is one unfolding of [cat_loop]                *)
(*     ([kcat_round_tree]): the read hole takes the buffer, the write hole *)
(*     the prefix the read filled, and the write's own return picks the   *)
(*     arm of [UkCatCat.kcat_wpost];                                      *)
(*   - one file is one node of [cat_files] ([kcat_file_tree]), and the    *)
(*     whole argv is [cat_tree] ([kcat_pay_all_tree]);                    *)
(*   - the entry ([wp_kcat_start_tree]) is [UkCatMain.wp_kcat_start_at]   *)
(*     at those, with the normal exit spent through the hole at 0.        *)
(*                                                                        *)
(* The direction is generic to specific, as in [UkEchoTree]: the holes     *)
(* demand the weakest argument readings, and cat's obligations ask for    *)
(* the registers cat's code actually has.                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import UmodeArith.
Require Import UserHeap UkRun.
Require Import UCodeCat.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSG.
Require User.CatSyms.
Require Import UserFd.
Require Import ProcGeom.     (* [NOFILE] *)
Require Import VcGen.        (* [trunc32_mword_of_int], [trunc32_subrange] *)
Require Import LineWords.
Require Import ProgTree UkTree.
Require Import UkCat UkCatLit UkCatCat UkCatMain.
Require Import UkHandler.       (* [ep_iface] / [env_res] / [tree_pay_of_conforms] *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  PURE FACTS about the trees                                        *)
(* ===================================================================== *)

Lemma write_bytes_app (fd : Z) (a b : bytes) (rest : proc) :
  write_bytes fd (a ++ b) rest = write_bytes fd a (write_bytes fd b rest).
Proof. induction a as [| x a IH]; simpl; [ reflexivity | by rewrite IH ]. Qed.

(* the three diagnostics, as cat's .rodata spells them *)
Lemma cat_dg_read_lit :
  @map nat (bv 8) (cat_lit 0x9c8) (seq 0 16) = cat_dg_read.
Proof. vm_compute. reflexivity. Qed.
Lemma cat_dg_write_lit :
  @map nat (bv 8) (cat_lit 0x9b0) (seq 0 17) = cat_dg_write.
Proof. vm_compute. reflexivity. Qed.
Lemma cat_dg_open_pre_lit :
  @map nat (bv 8) cm_lit (seq 0 cm_msg_q) = sb "cat: cannot open ".
Proof. vm_compute. reflexivity. Qed.
Lemma cat_dg_open_nl_lit :
  @map nat (bv 8) cm_lit (seq (S (S cm_msg_q)) (cm_msg_len - S (S cm_msg_q)))
  = [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* one turn of [cat_loop], named so a payer can rewrite at its branches *)
Definition cat_step (fd : Z) (rest : proc) : rd_ans -> proc :=
  fun a =>
    match a with
    | RdErr => write_bytes 2 cat_dg_read (exit_ 1)
    | RdBytes [] => rest
    | RdBytes bs =>
        Vis (EWrite 1 bs) (fun r =>
          if decide (r = Z.of_nat (length bs)) then Tau (cat_loop fd rest)
          else write_bytes 2 cat_dg_write (exit_ 1))
    end.

Lemma cat_loop_step (fd : Z) (rest : proc) :
  cat_loop fd rest = Vis (ERead fd cat_bufsz) (cat_step fd rest).
Proof. rewrite cat_loop_unfold. reflexivity. Qed.

Lemma cat_step_err (fd : Z) (rest : proc) :
  cat_step fd rest RdErr = write_bytes 2 cat_dg_read (exit_ 1).
Proof. reflexivity. Qed.
Lemma cat_step_nil (fd : Z) (rest : proc) :
  cat_step fd rest (RdBytes []) = rest.
Proof. reflexivity. Qed.
Lemma cat_step_cons (fd : Z) (rest : proc) (bs : bytes) :
  bs <> [] ->
  cat_step fd rest (RdBytes bs)
  = Vis (EWrite 1 bs) (fun r =>
      if decide (r = Z.of_nat (length bs)) then Tau (cat_loop fd rest)
      else write_bytes 2 cat_dg_write (exit_ 1)).
Proof. destruct bs; [ done | reflexivity ]. Qed.

Lemma cat_tree_stdin (argv : list bytes) :
  (length argv <= 1)%nat -> cat_tree argv = cat_loop 0 (exit_ 0).
Proof. intros H. unfold cat_tree. rewrite drop_ge; [ reflexivity | lia ]. Qed.
Lemma cat_tree_files (argv : list bytes) :
  (2 <= length argv)%nat -> cat_tree argv = cat_files (drop 1 argv) (exit_ 0).
Proof.
  intros H. unfold cat_tree.
  destruct (drop 1 argv) eqn:E; [| reflexivity ].
  exfalso. apply (f_equal (@length _)) in E. rewrite length_drop in E.
  simpl in E. lia.
Qed.

Lemma bvs_moi_small (z : Z) :
  0 <= z < 2 ^ 63 -> bv_signed (mword_of_int z : mword 64) = z.
Proof.
  intros H. apply (sint_moi z). unfold Z63.
  assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

(* a small descriptor read back as the C [int] the kernel reads *)
Lemma cint_moi_small (z : Z) :
  0 <= z < 2 ^ 31 -> bv_signed (trunc32 (mword_of_int z : mword 64)) = z.
Proof.
  intros Hz. rewrite trunc32_mword_of_int.
  assert (Hbw : bv_wrap 32 z = z) by (apply bvw32_small; lia).
  unfold bv_signed. rewrite moi32_unsigned Hbw.
  apply bv_swrap_small.
  assert (Hh32 : bv_half_modulus 32 = 2147483648%Z) by (vm_compute; reflexivity).
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite Hh32. lia.
Qed.

Lemma uarg_bytes_of (g : uarg) : bytes_of (uarg_bytes g) (ua_bytes g).
Proof.
  intros j Hj. rewrite uarg_bytes_length in Hj. by apply map_seq_lookup.
Qed.

Lemma bytes_of_one (b : bv 8) : bytes_of [b] (fun _ => b).
Proof. intros j Hj. simpl in Hj. by destruct j; [| lia]. Qed.

Lemma bytes_of_prefix (g : nat -> bv 8) (nb : nat) :
  bytes_of (map g (seq 0 nb)) g.
Proof.
  intros j Hj. rewrite length_map length_seq in Hj. by apply map_seq_lookup.
Qed.

Section UkCatTree.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).

  (* cat's instance: its code and its five stubs *)
  Definition cat_prog : uprog Σ :=
    MkUprog Σ (cat_code γt) CatSyms.write CatSyms.read CatSyms.open
      CatSyms.close CatSyms.exit.

  Local Notation tp := (tree_pay N cat_prog).

  (* ------------------------------------------------------------------- *)
  (*  1.  the exit hole IS cat's                                          *)
  (* ------------------------------------------------------------------- *)

  Lemma kcat_exit_ex_obl (s : Z) : kcat_exit N s ⊣⊢ ex_obl N cat_prog s.
  Proof using . reflexivity. Qed.

  Lemma tree_pay_exit (s : Z) : tp (exit_ s) ⊣⊢ kcat_exit N s.
  Proof using . rewrite /exit_ tree_pay_vis. reflexivity. Qed.

  Lemma usrc_at_data (dq : dfrac) (a : Z) (n : nat) (f : nat -> bv 8) :
    usrc_at N false dq a n f = ubytesq γd dq a n f.
  Proof using . reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (*  2.  the byte-literal chains                                         *)
  (* ------------------------------------------------------------------- *)

  (* one putc byte is one node [EWrite 2 [b]] *)
  Lemma kcat_wb_tree (b : bv 8) (T : proc) :
    ⊢ kcat_wb N (mword_of_int 2) b (tp (Vis (EWrite 2 [b]) (fun _ => T))) (tp T).
  Proof using .
    iIntros (ua h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Ht Hb] Hrun Hcont".
    iEval (rewrite tree_pay_vis; cbn [ev_obl]) in "Ht".
    iApply ("Ht" $! h m avail (uint ua) false (DfracOwn 1) (fun _ => b)
              with "[%] [%] [%] [%] Hcode [Hb] Hrun [Hcont]").
    { exact (bytes_of_one b). }
    { rewrite Ha0. vm_compute. reflexivity. }
    { rewrite Ha1. symmetry. apply mword_of_int_uint. }
    { exact Ha2. }
    { rewrite usrc_at_data /ubytesq /=. rewrite Z.add_0_r. by iFrame "Hb". }
    iIntros (h' ret) "HK Hs Hrun".
    iApply ("Hcont" $! h' ret with "[HK Hs] Hrun").
    rewrite usrc_at_data /ubytesq /=. rewrite Z.add_0_r.
    iDestruct "Hs" as "[Hb _]". iFrame "HK Hb".
  Qed.

  Lemma kcat_pay_seq_tree (fb : nat -> bv 8) (k : nat) :
    forall (i : nat) (rest : proc),
      ⊢ kcat_pay_seq N (mword_of_int 2) fb i k
          (tp (write_bytes 2 (map fb (seq i k)) rest)) (tp rest).
  Proof using .
    induction k as [| k IH]; intros i rest.
    - cbn [kcat_pay_seq seq map write_bytes]. by iIntros "H".
    - cbn [kcat_pay_seq seq map write_bytes].
      iExists (tp (write_bytes 2 (map fb (seq (S i) k)) rest)).
      iSplitR.
      + iApply kcat_wb_tree.
      + iApply IH.
  Qed.

  (* a chain started at [emp], with the tree's payment handed in once *)
  Lemma kcat_pay_seq_tree_emp (fb : nat -> bv 8) (i k : nat) (bs : bytes)
      (rest : proc) (Cend : iProp Σ) :
    map fb (seq i k) = bs ->
    (tp rest -∗ Cend) -∗
    tp (write_bytes 2 bs rest) -∗
    kcat_pay_seq N (mword_of_int 2) fb i k emp%I Cend.
  Proof using .
    intros Hbs. iIntros "HC Ht".
    iApply (kcat_pay_seq_frame N _ _ _ i emp%I _ (tp (write_bytes 2 bs rest))
              with "Ht").
    iApply (kcat_pay_seq_in N _ _ _ i (tp (write_bytes 2 bs rest)) with "[]").
    { by iIntros "[_ $]". }
    iApply (kcat_pay_seq_mono N _ _ _ i _ (tp rest) with "HC").
    rewrite -Hbs. iApply kcat_pay_seq_tree.
  Qed.

  Lemma kcat_dg_cr_tree :
    tp (write_bytes 2 cat_dg_read (exit_ 1)) -∗ kcat_dg_cr N.
  Proof using .
    iIntros "Ht". rewrite /kcat_dg_cr.
    iApply (kcat_pay_seq_tree_emp _ 0 16 cat_dg_read (exit_ 1) _
              cat_dg_read_lit with "[] Ht").
    iIntros "H". by iApply tree_pay_exit.
  Qed.

  Lemma kcat_dg_cw_tree :
    tp (write_bytes 2 cat_dg_write (exit_ 1)) -∗ kcat_dg_cw N.
  Proof using .
    iIntros "Ht". rewrite /kcat_dg_cw.
    iApply (kcat_pay_seq_tree_emp _ 0 17 cat_dg_write (exit_ 1) _
              cat_dg_write_lit with "[] Ht").
    iIntros "H". by iApply tree_pay_exit.
  Qed.

  Lemma kcat_dg_open_tree (g : uarg) :
    tp (write_bytes 2 (cat_dg_open (uarg_bytes g)) (exit_ 1)) -∗
    kcat_dg_open N g.
  Proof using .
    iIntros "Ht". rewrite /kcat_dg_open /cat_dg_open.
    rewrite !write_bytes_app.
    iExists (tp (write_bytes 2 (uarg_bytes g) (write_bytes 2 [wl_nl] (exit_ 1)))),
            (tp (write_bytes 2 [wl_nl] (exit_ 1))).
    iSplitL "Ht"; [| iSplitR ].
    - iApply (kcat_pay_seq_tree_emp _ 0 cm_msg_q (sb "cat: cannot open ") _ _
                cat_dg_open_pre_lit with "[] Ht").
      by iIntros "H".
    - iApply (kcat_pay_seq_tree (ua_bytes g) (ua_len g) 0).
    - iApply (kcat_pay_seq_mono N _ _ _ _ _ (tp (exit_ 1)) with "[]").
      { iIntros "H". by iApply tree_pay_exit. }
      rewrite -cat_dg_open_nl_lit. iApply kcat_pay_seq_tree.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  the round: one unfolding of [cat_loop]                          *)
  (* ------------------------------------------------------------------- *)

  Lemma ubytes_split512 (a : Z) (nb : nat) (g : nat -> bv 8) :
    (nb <= 512)%nat ->
    ubytes γd a 512 g ⊣⊢
    ubytes γd a nb g ∗ ubytes γd (a + Z.of_nat nb) (512 - nb) (fun j => g (nb + j)%nat).
  Proof using .
    intros H. rewrite -ubytes_app.
    by replace (nb + (512 - nb))%nat with 512%nat by lia.
  Qed.

  Lemma kcat_round_tree (fdv : mword 64) (fd : Z) (rest : proc) :
    bv_signed (trunc32 fdv) = fd ->
    ⊢ kcat_round N fdv (tp (cat_loop fd rest)) (tp rest).
  Proof using .
    intros Hfd. rewrite /kcat_round. iModIntro.
    iIntros (h m avail f) "%Ha0 %Ha1 %Ha2 #Hcode HI Hbuf Hrun Hcont".
    iEval (rewrite cat_loop_step tree_pay_vis; cbn [ev_obl]) in "HI".
    iApply ("HI" $! h m avail CatSyms.buf f with "[%] [%] [%] Hcode Hbuf Hrun").
    { rewrite Ha0. exact Hfd. }
    { exact Ha1. }
    { rewrite trunc32_subrange. exact Ha2. }
    iIntros (h' ret g) "%Hok HK Hbuf Hrun".
    iApply ("Hcont" $! h' ret g with "[HK] Hbuf Hrun").
    iEval (cbv beta) in "HK". cbv beta.
    iSplit; [| iSplit ].
    - (* the read failed: the read-error tail *)
      iIntros "%Hneg".
      assert (Hr : rd_ans_of ret g = RdErr).
      { unfold rd_ans_of. destruct (decide (bv_signed ret < 0)); [ done | lia ]. }
      iEval (rewrite Hr cat_step_err) in "HK".
      iApply (kcat_dg_cr_tree with "HK").
    - (* end of file: the rest *)
      iIntros "%Hz".
      assert (Hr : rd_ans_of ret g = RdBytes []).
      { unfold rd_ans_of. destruct (decide (bv_signed ret < 0)); [ lia | ].
        rewrite Hz. reflexivity. }
      iEval (rewrite Hr cat_step_nil) in "HK". iExact "HK".
    - (* [nb] bytes: the write of the prefix the read filled *)
      iIntros (nb) "%Hnb %Hpos".
      assert (Hle : (nb <= 512)%nat).
      { unfold read_ans_ok in Hok.
        try change (Z.of_nat cat_bufsz) with 512 in Hok.
        try change (Z.of_nat 512) with 512 in Hok.
        lia. }
      assert (Hr : rd_ans_of ret g = RdBytes (map g (seq 0 nb))).
      { unfold rd_ans_of. destruct (decide (bv_signed ret < 0)); [ lia | ].
        rewrite Hnb Nat2Z.id. reflexivity. }
      assert (Hne : map g (seq 0 nb) <> []).
      { destruct nb as [| nb']; [ lia | ]. simpl. discriminate. }
      iEval (rewrite Hr (cat_step_cons _ _ _ Hne) tree_pay_vis; cbn [ev_obl]) in "HK".
      iEval (rewrite length_map length_seq) in "HK".
      iIntros (h2 m2 av2) "%Ha0' %Ha1' %Ha2' #Hc Hbuf Hrun Hcont".
      iDestruct (ubytes_split512 _ nb g Hle with "Hbuf") as "[Hb1 Hb2]".
      iApply ("HK" $! h2 m2 av2 CatSyms.buf false (DfracOwn 1) g
                with "[%] [%] [%] [%] Hc [Hb1] Hrun [Hcont Hb2]").
      { apply bytes_of_prefix. }
      { rewrite Ha0'. vm_compute. reflexivity. }
      { exact Ha1'. }
      { rewrite length_map length_seq. exact Ha2'. }
      { rewrite usrc_at_data length_map length_seq. iExact "Hb1". }
      iIntros (h3 wret) "HK Hs Hrun".
      iApply ("Hcont" $! h3 wret with "[HK Hs Hb2] Hrun").
      iEval (rewrite usrc_at_data length_map length_seq) in "Hs".
      iSplitL "HK"; last first.
      { iApply (ubytes_split512 _ nb g Hle). iFrame "Hs Hb2". }
      iEval (cbv beta) in "HK".
      rewrite /kcat_wpost.
      destruct (decide (bv_signed wret = Z.of_nat nb)) as [Hw | Hw].
      + iSplit.
        * iIntros "_". iEval (rewrite (decide_True _ _ Hw) tree_pay_tau) in "HK". iExact "HK".
        * iIntros "%Hne'". iExFalso. iPureIntro. apply Hne'.
          rewrite -Hw. symmetry. apply UkCat.moi_of_sint.
      + iSplit.
        * iIntros "%Hw'". iExFalso. iPureIntro. apply Hw.
          rewrite Hw'. apply bvs_moi_small.
          assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
          lia.
        * iIntros "_". iEval (rewrite (decide_False _ _ Hw)) in "HK".
          iApply (kcat_dg_cw_tree with "HK").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  4.  the file chain                                                  *)
  (* ------------------------------------------------------------------- *)

  Lemma kcat_o_mono_in (pv : mword 64) (Oi Oi' : iProp Σ)
      (Oo : mword 64 -> iProp Σ) :
    (Oi' -∗ Oi) -∗ kcat_o N pv Oi Oo -∗ kcat_o N pv Oi' Oo.
  Proof using .
    iIntros "Hm Ho" (h m avail) "%Ha0 %Ha1 #Hcode HOi Hrun Hcont".
    iApply ("Ho" $! h m avail with "[%] [%] Hcode [Hm HOi] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | ].
    iApply ("Hm" with "HOi").
  Qed.

  Lemma kcat_pay_in (args : list uarg) (k : nat) :
    forall (i : nat) (Ci Ci' Cend : iProp Σ),
      (Ci' -∗ Ci) -∗ kcat_pay N args i k Ci Cend -∗ kcat_pay N args i k Ci' Cend.
  Proof using .
    destruct k as [| k]; intros i Ci Ci' Cend; iIntros "Hm Hp".
    - cbn [kcat_pay]. iIntros "H". iApply "Hp". iApply ("Hm" with "H").
    - cbn [kcat_pay]. iDestruct "Hp" as (g Cm) "(%Hg & Hf & Hp)".
      iExists g, Cm. iFrame "Hp". iSplitR; [ done | ].
      rewrite /kcat_file. iApply (kcat_o_mono_in with "Hm Hf").
  Qed.

  Lemma kcat_file_tree (av : Z) (args : list uarg) (i : nat) (g : uarg)
      (ps : list bytes) (rest : proc) :
    args !! i = Some g ->
    uargv γd av args -∗
    kcat_file N g (tp (cat_files (uarg_bytes g :: ps) rest)) (tp (cat_files ps rest)).
  Proof using .
    intros Hg. iIntros "#Hargv".
    iAssert (ustr γd DfracDiscarded (ua_ptr g) (ua_len g) (ua_bytes g))%I
      as "#Hstr".
    { iDestruct "Hargv" as "(_ & _ & Hl)".
      iDestruct (big_sepL_lookup _ _ i g Hg with "Hl") as "[_ $]". }
    rewrite /kcat_file.
    iIntros (h m avail) "%Ha0 %Ha1 #Hcode Ht Hrun Hcont".
    iEval (cbn [cat_files]; rewrite tree_pay_vis; cbn [ev_obl]) in "Ht".
    iApply ("Ht" $! h m avail (ua_ptr g) false (ua_bytes g)
              with "[%] [%] [%] Hcode [] Hrun").
    { apply uarg_bytes_of. }
    { exact Ha0. }
    { exact Ha1. }
    { rewrite uarg_bytes_length. iExact "Hstr". }
    iIntros (h' ret) "%Hok HK _ Hrun".
    iApply ("Hcont" $! h' ret with "[HK] Hrun").
    iEval (cbv beta) in "HK". cbv beta.
    destruct (decide (bv_signed ret < 0)) as [Hneg | Hnn].
    - iSplit.
      + iIntros "_". iApply (kcat_dg_open_tree with "HK").
      + iIntros "%Hnn". lia.
    - iSplit.
      + iIntros "%Hneg". lia.
      + iIntros "_".
        destruct Hok as [Hm1 | [Hrng Hret]]; [ lia | ].
        set (s := bv_signed ret) in *.
        assert (Hlt : (Z.to_nat s < NOFILE)%nat).
        { assert (E : Z.of_nat NOFILE = 16) by reflexivity.
          rewrite E in Hrng. unfold NOFILE. lia. }
        assert (Hfdz : Z.of_nat (Z.to_nat s) = s) by lia.
        iExists (Z.to_nat s), (tp (Vis (EClose s) (fun _ => cat_files ps rest))).
        iSplitR; [ iPureIntro; by rewrite Hfdz | ].
        iSplitR; [ by iPureIntro | ].
        iSplitL "HK".
        * rewrite /kcat_run0.
          iExists (tp (cat_loop s (Vis (EClose s) (fun _ => cat_files ps rest)))),
                  (tp (Vis (EClose s) (fun _ => cat_files ps rest))).
          iSplitR.
          { rewrite Hfdz. iApply kcat_round_tree.
            apply cint_moi_small. unfold NOFILE in Hlt.
            assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
            lia. }
          iFrame "HK". by iIntros "H".
        * iIntros (h2 m2 av2) "%Ha0' #Hc HCm Hrun Hcont".
          iEval (rewrite tree_pay_vis; cbn [ev_obl]) in "HCm".
          iApply ("HCm" $! h2 m2 av2 with "[%] Hc Hrun").
          { rewrite Ha0'. exact Hfdz. }
          iIntros (h3 r) "HK Hrun".
          iApply ("Hcont" $! h3 r with "HK Hrun").
  Qed.

  Lemma kcat_pay_tree (av : Z) (args : list uarg) (k : nat) :
    forall (i : nat) (rest : proc) (Cend : iProp Σ),
      (i + k)%nat = length args ->
      uargv γd av args -∗
      (tp rest -∗ Cend) -∗
      kcat_pay N args i k (tp (cat_files (map uarg_bytes (drop i args)) rest)) Cend.
  Proof using .
    induction k as [| k IH]; intros i rest Cend Hlen; iIntros "#Hargv HC".
    - cbn [kcat_pay]. rewrite drop_ge; [| lia ]. cbn [map cat_files].
      iIntros "Ht". iApply ("HC" with "Ht").
    - cbn [kcat_pay].
      destruct (lookup_lt_is_Some_2 args i ltac:(lia)) as [g Hg].
      rewrite (drop_S args g i Hg). cbn [List.map cat_files].
      iExists g, (tp (cat_files (map uarg_bytes (drop (S i) args)) rest)).
      iSplitR; [ done | ]. iSplitR.
      + iApply (kcat_file_tree av args i g with "Hargv"). exact Hg.
      + iApply (IH (S i) rest Cend ltac:(lia) with "Hargv HC").
  Qed.

  Lemma kcat_pay_all_tree (av : Z) (args : list uarg) :
    uargv γd av args -∗
    tp (cat_tree (map uarg_bytes args)) -∗
    kcat_pay_all N args emp%I (ex_obl N cat_prog 0).
  Proof using .
    iIntros "#Hargv Ht". rewrite /kcat_pay_all. iSplit.
    - iIntros "%Hle".
      iEval (rewrite cat_tree_stdin; [| rewrite length_map; lia ]) in "Ht".
      iExists (tp (exit_ 0)). iSplitL "Ht".
      + rewrite /kcat_run0. iExists (tp (cat_loop 0 (exit_ 0))), (tp (exit_ 0)).
        iSplitR.
        { iApply kcat_round_tree. vm_compute. reflexivity. }
        iFrame "Ht". by iIntros "H".
      + iIntros "[_ H]". rewrite -kcat_exit_ex_obl. by iApply tree_pay_exit.
    - iIntros "%Hge".
      iEval (rewrite cat_tree_files; [| rewrite length_map; lia ]) in "Ht".
      iEval (rewrite -map_drop) in "Ht".
      iApply (kcat_pay_in args (length args - 1)%nat 1%nat
                (tp (cat_files (map uarg_bytes (drop 1 args)) (exit_ 0)))
              with "[Ht]").
      { by iIntros "_". }
      iApply (kcat_pay_tree av args (length args - 1)%nat 1%nat (exit_ 0)
                (ex_obl N cat_prog 0) ltac:(lia) with "Hargv").
      iIntros "H". rewrite -kcat_exit_ex_obl. by iApply tree_pay_exit.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  5.  the entry at the tree                                           *)
  (* ------------------------------------------------------------------- *)

  Lemma wp_kcat_start_tree (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) :
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx (mword_of_int 10 : mword 5)
      = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int av ->
    tp (cat_tree (map uarg_bytes args)) -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int CatSyms.start)
      (2 + (6 + (8 + (10 + (12 + (4 + n)))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hptr Ha0 Ha1. iIntros "Ht #Hcode #Hro #Hargv Hbuf Hrun".
    iApply (wp_kcat_start_at N h m av args f n emp%I (ex_obl N cat_prog 0)
              Hptr Ha0 Ha1 with "[Ht] [] Hcode Hro Hargv [] Hbuf Hrun").
    - iApply (kcat_pay_all_tree with "Hargv Ht").
    - iIntros "H". by rewrite kcat_exit_ex_obl.
    - done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  6.  the entry at a handler (program-specs cut 5, lane C)            *)
  (* ------------------------------------------------------------------- *)

  (* [wp_kcat_start_tree] with the tree paid by an ENVIRONMENT
     ([UkHandler.tree_pay_of_conforms]); [UkEchoTree.wp_kecho_start_env]'s
     twin. *)
  Lemma wp_kcat_start_env {Dp : list nat} (I : ep_ifaceP (Dp := Dp) N cat_prog)
      (E : penv) (ds : gset nat)
      (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) :
    conforms E (cat_tree (map uarg_bytes args)) ->
    safe_fds (dom (pe_fd E)) (cat_tree (map uarg_bytes args)) ->
    dp_in Dp ds ->
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx (mword_of_int 10 : mword 5)
      = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int av ->
    env_res N cat_prog I E ds -∗
    cat_code γt -∗
    cat_rodata γt -∗
    uargv γd av args -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int CatSyms.start)
      (2 + (6 + (8 + (10 + (12 + (4 + n)))))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hc Hs Hdp Hptr Ha0 Ha1. iIntros "Henv #Hcode #Hro #Hargv Hbuf Hrun".
    iApply (wp_kcat_start_tree h m av args f n Hptr Ha0 Ha1
              with "[Henv] Hcode Hro Hargv Hbuf Hrun").
    iApply (tree_pay_of_conforms_p N cat_prog I E ds _ Hc Hs Hdp with "Henv").
  Qed.

End UkCatTree.
