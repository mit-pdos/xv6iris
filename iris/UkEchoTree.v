(* ===================================================================== *)
(* UkEchoTree.v -- echo's landed obligations are INSTANCES of the tree     *)
(* payment: [UkEcho.kecho_pay_all] at the tree [ProgTree.echo_tree] of     *)
(* its arguments' bytes.                                                  *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.2, cut 2.  [UkTree]    *)
(* states the hole one event costs at a program instance; this file       *)
(* names echo's instance ([echo_prog]: its code and its five stubs, of    *)
(* which it calls write and exit) and shows that a payer of [tree_pay     *)
(* (echo_tree bs)] has paid                                                *)
(* the whole chain echo's walk spends -- so a walk stated at the chain     *)
(* is a walk stated at the tree, and every landed destination that builds *)
(* the chain is a HANDLER of the tree.                                     *)
(*                                                                        *)
(* The direction is generic to specific: the tree's write hole demands    *)
(* the weakest argument readings and hands the source run back, and       *)
(* [kecho_w] asks for exactly the console-shaped run echo has (a0 = 1,    *)
(* a1 the address, a2 the count) with its sources held PERSISTENTLY       *)
(* outside the obligation (argv's strings and the two .rodata literals),  *)
(* which is why the bridge takes the sources boxed and never returns      *)
(* them.                                                                  *)
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
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeEcho.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require User.EchoSyms.
Require Import FdSlots UserFd.
Require Import LineWords.
Require Import ProgTree UkTree UkEcho.
Require Import UkHandler.       (* [ep_iface] / [env_res] / [tree_pay_of_conforms] *)
Local Open Scope Z_scope.
Import Defs.

(* the two literal bytes, where echo's .rodata has them *)
Lemma echo_sep_ro : echo_ro !! UkEcho.echo_sep_ptr = Some wl_sp.
Proof. vm_compute. reflexivity. Qed.
Lemma echo_nl_ro : echo_ro !! UkEcho.echo_nl_ptr = Some wl_nl.
Proof. vm_compute. reflexivity. Qed.

Section UkEchoTree.
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

  (* echo's instance: its code and its five stubs.  echo calls only write
     and exit; read, open and close are named at echo's own addresses
     ([UkStub.echo_stub_read] and its two siblings) so that a handler
     record stated at any program with the five stubs -- [UkHandler.
     ep_iface] asks for every law whatever tree it pays -- has an instance
     at echo's. *)
  Definition echo_prog : uprog Σ :=
    MkUprog Σ (echo_code γt) EchoSyms.write EchoSyms.read EchoSyms.open EchoSyms.close
      EchoSyms.exit.

  Global Instance echo_prog_code_persistent : Persistent (up_code echo_prog).
  Proof using . simpl. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (*  1.  echo's sources, as the hole wants them                          *)
  (* ------------------------------------------------------------------- *)

  Lemma uarg_bytes_of (g : uarg) : bytes_of (uarg_bytes g) (ua_bytes g).
  Proof using .
    intros j Hj. rewrite uarg_bytes_length in Hj. by apply map_seq_lookup.
  Qed.

  Lemma usrc_arg (av : Z) (args : list uarg) (i : nat) (g : uarg) :
    args !! i = Some g ->
    uargv γd av args -∗
    □ usrc_at N false DfracDiscarded (ua_ptr g) (ua_len g) (ua_bytes g).
  Proof using .
    intros Hg. iIntros "#(_ & _ & Hl)".
    iDestruct (big_sepL_lookup _ _ i g Hg with "Hl") as "#[_ (_ & _ & Hb & _)]".
    iModIntro. iExact "Hb".
  Qed.

  Lemma bytes_of_one (b : bv 8) : bytes_of [b] (fun _ => b).
  Proof using . intros j Hj. simpl in Hj. by destruct j; [| lia]. Qed.

  Lemma usrc_lit (a : Z) (b : bv 8) :
    echo_ro !! a = Some b ->
    echo_rodata γt -∗
    □ usrc_at N true DfracDiscarded a 1 (fun _ => b).
  Proof using .
    intros Ha. rewrite /echo_rodata /utext_img. iIntros "#H".
    iDestruct (big_sepM_lookup _ _ a b Ha with "H") as "#Hb".
    iModIntro. rewrite /usrc_at. simpl. rewrite Z.add_0_r. by iFrame "Hb".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2.  the hole IS echo's obligation                                   *)
  (* ------------------------------------------------------------------- *)

  (* [kecho_w] is monotone on its INPUT side too *)
  Lemma kecho_w_mono_in (ua : mword 64) (nb : nat) (Ci Ci' Co : iProp Σ) :
    (Ci' -∗ Ci) -∗ kecho_w N ua nb Ci Co -∗ kecho_w N ua nb Ci' Co.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode [Hm HCi] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iApply ("Hm" with "HCi").
  Qed.

  Lemma kecho_w_of_wr_obl (ua : Z) (bs : list (bv 8)) (K : Z -> iProp Σ)
      (Co : iProp Σ) (tx : bool) (dq : dfrac) (f : nat -> bv 8) :
    bytes_of bs f ->
    □ usrc_at N tx dq ua (length bs) f -∗
    (∀ r : Z, K r -∗ Co) -∗
    kecho_w N (mword_of_int ua) (length bs) (wr_obl N echo_prog 1 bs K) Co.
  Proof using .
    intros Hf. iIntros "#Hs HK" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode Ho Hrun Hcont".
    iApply ("Ho" $! h m avail ua tx dq f with "[%] [%] [%] [%] Hcode Hs Hrun").
    { exact Hf. }
    { rewrite Ha0. vm_compute. reflexivity. }
    { exact Ha1. }
    { exact Ha2. }
    iIntros (h' ret) "HKr _ Hrun".
    iApply ("Hcont" $! h' ret with "[HK HKr] Hrun").
    iApply ("HK" with "HKr").
  Qed.

  (* ...at a tree node: the payment of [Vis (EWrite 1 bs) k] is the
     obligation whose output is the payment of [k]'s (constant) subtree *)
  Lemma kecho_w_of_tree (ua : Z) (bs : list (bv 8)) (rest : proc)
      (tx : bool) (dq : dfrac) (f : nat -> bv 8) :
    bytes_of bs f ->
    □ usrc_at N tx dq ua (length bs) f -∗
    kecho_w N (mword_of_int ua) (length bs)
      (tree_pay N echo_prog (Vis (EWrite 1 bs) (fun _ => rest)))
      (tree_pay N echo_prog rest).
  Proof using .
    intros Hf. iIntros "#Hs".
    iApply (kecho_w_mono_in with "[]").
    { iIntros "Ht". rewrite tree_pay_vis. iExact "Ht". }
    iApply (kecho_w_of_wr_obl _ _ _ _ tx dq f Hf with "Hs").
    iIntros (r) "Ht". iExact "Ht".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  the whole chain                                                 *)
  (* ------------------------------------------------------------------- *)

  Lemma kecho_pay_tree (av : Z) (args : list uarg) (k i : nat) (rest : proc)
      (Cend : iProp Σ) :
    length args = (i + k + 1)%nat ->
    uargv γd av args -∗
    echo_rodata γt -∗
    (tree_pay N echo_prog rest -∗ Cend) -∗
    kecho_pay N args k i
      (tree_pay N echo_prog (echo_words (map uarg_bytes (drop i args)) rest))
      Cend.
  Proof using .
    revert i. induction k as [| k IH]; intros i Hlen; iIntros "#Hargv #Hro HC".
    - iIntros (g) "%Hg".
      assert (Hd : drop i args = [g]).
      { rewrite (drop_S args g i Hg).
        assert (length (drop (S i) args) = 0%nat) by (rewrite length_drop; lia).
        by destruct (drop (S i) args). }
      rewrite Hd. simpl.
      iExists (tree_pay N echo_prog (Vis (EWrite 1 [wl_nl]) (fun _ => rest))).
      iDestruct (usrc_arg av args i g Hg with "Hargv") as "#Hsg".
      iDestruct (usrc_lit UkEcho.echo_nl_ptr wl_nl echo_nl_ro with "Hro") as "#Hsn".
      iSplitR.
      + rewrite -(uarg_bytes_length g).
        iApply (kecho_w_of_tree _ _ _ false DfracDiscarded (ua_bytes g)
                  (uarg_bytes_of g)).
        rewrite uarg_bytes_length. iExact "Hsg".
      + iApply (kecho_w_mono with "HC").
        iApply (kecho_w_of_tree UkEcho.echo_nl_ptr [wl_nl] _ true DfracDiscarded
                  (fun _ => wl_nl) (bytes_of_one wl_nl) with "Hsn").
    - iIntros (g) "%Hg".
      rewrite (drop_S args g i Hg).
      assert (Hne : exists g' r', drop (S i) args = g' :: r').
      { assert (length (drop (S i) args) = S k) by (rewrite length_drop; lia).
        destruct (drop (S i) args) as [| g' r']; [ done | by eexists _, _ ]. }
      destruct Hne as (g' & r' & Hr'). rewrite Hr'. simpl.
      iExists (tree_pay N echo_prog
                 (Vis (EWrite 1 [wl_sp])
                    (fun _ => echo_words (uarg_bytes g' :: map uarg_bytes r') rest))),
              (tree_pay N echo_prog (echo_words (uarg_bytes g' :: map uarg_bytes r') rest)).
      iDestruct (usrc_arg av args i g Hg with "Hargv") as "#Hsg".
      iDestruct (usrc_lit UkEcho.echo_sep_ptr wl_sp echo_sep_ro with "Hro") as "#Hss".
      iSplitR; [| iSplitR ].
      + rewrite -(uarg_bytes_length g).
        iApply (kecho_w_of_tree _ _ _ false DfracDiscarded (ua_bytes g)
                  (uarg_bytes_of g)).
        rewrite uarg_bytes_length. iExact "Hsg".
      + iApply (kecho_w_of_tree UkEcho.echo_sep_ptr [wl_sp] _ true DfracDiscarded
                  (fun _ => wl_sp) (bytes_of_one wl_sp) with "Hss").
      + iPoseProof (IH (S i) ltac:(lia) with "Hargv Hro HC") as "IH'".
        iEval (rewrite Hr' /=) in "IH'". iExact "IH'".
  Qed.

  Lemma kecho_pay_all_tree (av : Z) (args : list uarg) :
    uargv γd av args -∗
    echo_rodata γt -∗
    kecho_pay_all N args
      (tree_pay N echo_prog (echo_tree (map uarg_bytes args)))
      (ex_obl N echo_prog 0).
  Proof using .
    iIntros "#Hargv #Hro". rewrite /kecho_pay_all /echo_tree. iSplit.
    - iIntros "%Hle Ht".
      rewrite drop_ge; [| rewrite length_map; lia ]. simpl.
      rewrite tree_pay_vis. iExact "Ht".
    - iIntros "%Hge". rewrite -map_drop.
      iApply (kecho_pay_tree av args (length args - 2) 1 (exit_ 0) _
                ltac:(lia) with "Hargv Hro").
      iIntros "Ht". rewrite tree_pay_vis. iExact "Ht".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  4.  the entry at the tree (program-specs cut 3)                     *)
  (* ------------------------------------------------------------------- *)

  (* A payer of echo's tree runs echo from its ELF entry: the walk's chain
     is the tree's ([kecho_pay_all_tree]), and the chain's end is the
     tree's exit hole, which IS the walk's exit hole [UkEcho.kecho_exit] at
     echo's instance.  No payload record is named: the exit is paid by
     whoever pays the tree. *)
  Lemma wp_kecho_start_tree (h : CpuId) (m : regfile) (av : Z)
      (args : list uarg) (n : nat) :
    m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int av ->
    tree_pay N echo_prog (echo_tree (map uarg_bytes args)) -∗
    echo_code γt -∗
    echo_rodata γt -∗
    uargv γd av args -∗
    urun N h m (mword_of_int EchoSyms.start) (2 + (8 + (2 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1. iIntros "Ht #Hcode #Hro #Hargv Hrun".
    iApply (wp_kecho_start_at N h m av args n
              (tree_pay N echo_prog (echo_tree (map uarg_bytes args)))
              (ex_obl N echo_prog 0) Ha0 Ha1
              with "[] [] Hcode Hargv Ht Hrun").
    - iApply (kecho_pay_all_tree av args with "Hargv Hro").
    - iIntros "H". iExact "H".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  5.  the entry at a handler (program-specs cut 5, lane C)            *)
  (* ------------------------------------------------------------------- *)

  (* [wp_kecho_start_tree] with the tree paid by an ENVIRONMENT: an
     interface [I] at echo's instance, its resources at [E] over the
     devices [ds], and the pure half -- the tree conforms to [E] and keeps
     the descriptor discipline ([UkHandler.tree_pay_of_conforms]). *)
  Lemma wp_kecho_start_env {Dp : list nat} (I : ep_ifaceP (Dp := Dp) N echo_prog)
      (E : penv) (ds : gset nat)
      (h : CpuId) (m : regfile) (av : Z) (args : list uarg) (n : nat) :
    conforms E (echo_tree (map uarg_bytes args)) ->
    safe_fds (dom (pe_fd E)) (echo_tree (map uarg_bytes args)) ->
    dp_in Dp ds ->
    m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int av ->
    env_res N echo_prog I E ds -∗
    echo_code γt -∗
    echo_rodata γt -∗
    uargv γd av args -∗
    urun N h m (mword_of_int EchoSyms.start) (2 + (8 + (2 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hc Hs Hdp Ha0 Ha1. iIntros "Henv #Hcode #Hro #Hargv Hrun".
    iApply (wp_kecho_start_tree h m av args n Ha0 Ha1
              with "[Henv] Hcode Hro Hargv Hrun").
    iApply (tree_pay_of_conforms_p N echo_prog I E ds _ Hc Hs Hdp with "Henv").
  Qed.

End UkEchoTree.
