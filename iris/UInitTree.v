(* ===================================================================== *)
(* UInitTree.v -- /INIT'S CONSOLE CREDENTIALS AT THE TREE CLAIM, AND THE  *)
(* MINT AT THE BANNER (lane TL-6; design/user-tree.md section 9.4).       *)
(*                                                                       *)
(* WHAT THIS FILE IS FOR.  [UTreeAdequacy.tree_Hinit_boot] spends the     *)
(* era's licence AT BOOT: the taint is minted before /init has executed   *)
(* one instruction, [AppInv.app_sup] follows, and the whole of the era    *)
(* runs on the generic bundle.  That is honest but says nothing about     *)
(* /init.  The target section 9.3(6) named is TAINT AT THE BANNER: xv6's  *)
(* /init does its whole console SETUP -- mknod("/console"), the two       *)
(* opens, the two dups -- BEFORE it prints anything, so the tree claim's  *)
(* live arm can cover the setup and everything from the first console     *)
(* byte on runs under the taint.                                          *)
(*                                                                       *)
(* THE CREDENTIAL FAMILY IS WHERE THE MINT LIVES.  /init's walk is        *)
(* claim-generic ([UInitKernel.init_boot_con] names no application): what *)
(* it takes is a [UserConsole.cons_cred] record and the laws over it.     *)
(* Echo's is [UInitBoot.echo_cc], six families off its console ledger.    *)
(* THE TREE CLAIM SAYS NOTHING ABOUT THE CONSOLE, so its record is the    *)
(* era's own licence and the taint, and nothing else:                     *)
(*                                                                       *)
(*   [cc_wb] (the BANNER-OWED credential) = the era's licence, or the     *)
(*      taint if it has already been spent;                              *)
(*   [cc_wp] (the ROUND-OPEN credential, what the banner LEAVES) = the    *)
(*      taint;                                                           *)
(*   the other three ([cc_rd] and [cc_mid], the lease's per-position and  *)
(*      mid-line pieces, and [cc_wc], the shell's command loop's) =       *)
(*      [True]: /init reads no byte and a tree application claims neither *)
(*      what the console delivers nor what a shell puts on it.            *)
(*                                                                       *)
(* SO THE BANNER IS THE MINT ([tree_kinit_ban_law]): the first byte of    *)
(* "init: starting sh" spends the licence, and what the last byte leaves  *)
(* is the taint.  Before it, the licence is unspent and the claim's live  *)
(* arm holds; after it, [AppInv.app_sup] is reachable and the rest of the *)
(* walk is the supply's -- which is exactly what [UkInit.init_deps] and   *)
(* the two diagnostics are paid from here ([tree_init_deps],              *)
(* [tree_kinit_diag_law]).                                               *)
(*                                                                       *)
(* AND IT IS WHAT MAKES RULING (b) PAYABLE.  [UkInit.init_kill_law] --    *)
(* lane TL-6's restatement of [init_boot_con]'s P2 -- asks for the kill   *)
(* row off the credential the round is already carrying.  At this record  *)
(* that is [tree_init_kill_law], and its content is the ruling's: a kill  *)
(* /init cannot account for costs the tree application the era's licence, *)
(* not "nothing" (which is false, [AppTree.tree_bump_free_is_vacuous])    *)
(* and not "always the taint" (which is the design decision section 3     *)
(* argues against).                                                      *)
(*                                                                       *)
(* WHAT IS NOT HERE, and section 9.3(6) is the worklist: the SETUP's own  *)
(* rows -- the console dance's two leaves ([UkInit.init_cons_leaves] /    *)
(* [init_cons_hit]) at the tree claim, which want a tree-side reading of  *)
(* [UInitCons.init_cons_laws_at]'s nine laws, and the exec supply         *)
(* ([UkInit.init_cons_sup], ten more).  Those are stated over ECHO's      *)
(* names ([UInitCons.v] is [echo_names]-indexed throughout), so they need *)
(* that file generalised first; the lane note records the cost.  Until    *)
(* then [UTreeAdequacy.tree_Hinit_boot] stands as it is and this file's   *)
(* laws are the half of /init's premise list the tree claim can already   *)
(* pay.                                                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.            (* [cons_licence_triv]: free at a trivial claim *)
Require Import Xv6G.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import AppCfg.
Require Import AppInv.
Require Import UexecExecInst.     (* [uprogSG_free] -- /init's instance *)
Require Import UexecExecMint.     (* [udepw_law_of_sup] / [_of_sup_write] *)
Require Import UserFd.
Require Import UInitFd.           (* [ufd_l3] / [ufd_l0] *)
Require Import UserConsole.       (* [cons_cred] / [cc_wbn] *)
Require Import UkRun.             (* [udepw_law] *)
Require Import UkInit.            (* [init_kill_law] / [kinit_w1] / the deposits *)
Require Import UkInitMain.        (* [kinit_ban_law] / [kinit_diag_law] *)
Require Import UkWriteClosed.     (* [kinit_w1_of_closed_l0] *)
Require Import AppTree.           (* the licence, the taint and the claim *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE RECORD, AND THE RULED PREMISE AT IT                          *)
(*                                                                       *)
(*  A LIGHT SECTION: everything here is the registry's own vocabulary     *)
(*  plus [RiscvPtsto.app_taint], and [UkInit.init_kill_law] needs   *)
(*  no more than that (it is stated over [UkInit.init_lend_cred], which   *)
(*  names two fixed descriptor lists and nothing else).                   *)
(* ===================================================================== *)
Section TreeConsCred.
  Context {Σ : gFunctors}.
  Context `{!riscvGS Σ}.
  Context `{!treeG Σ}.

  (* the lease's two READ-side families and the shell loop's write one:
     /init reads no console byte and the tree application claims none, so
     all three are [True].
     They are not dead -- the lease's payload is stated at them
     ([UserConsole.ucons_pay]) and /init hands them to the shell it forks
     -- they simply carry no information at this claim. *)
  Lemma tree_cc_rd_timeless : forall i : nat, Timeless (True%I : iProp Σ).
  Proof using . intros _. apply _. Qed.

  (* THE BANNER-OWED CREDENTIAL IS THE ERA'S LICENCE, or the taint where
     the licence has already been spent.  BOTH ARMS ARE NEEDED and the
     second is not slack: the round-open credential the banner leaves is
     the taint, the two diagnostics are paid from it and the first of
     them LEAVES a banner-owed credential again
     ([UkInitMain.kinit_diag_law]) -- and a licence cannot be re-minted
     out of the taint (it is the registry authority's to file, and
     [AppTree.tree_bump_free_is_vacuous] is why).  So the family that
     closes under /init's own restart loop is "the licence, or the taint". *)
  Definition tree_wb (c : tree_fixed) (_ : list (bv 8)) : iProp Σ :=
    (tree_turn c ∨ tree_taint c)%I.

  Lemma tree_cc_wb_timeless (c : tree_fixed) :
    forall I : list (bv 8), Timeless (tree_wb c I).
  Proof using . intros I. rewrite /tree_wb. apply _. Qed.

  Definition tree_cc (c : tree_fixed) : cons_cred Σ :=
    MkConsCred
      (fun _ : nat => True%I) tree_cc_rd_timeless
      (fun (_ : gname) (_ : list (bv 8)) => True%I)
      (fun (_ : list (bv 8)) (_ : nat) => True%I)
      (tree_wb c) (tree_cc_wb_timeless c)
      (fun _ : nat => tree_taint c).

  (* the two projections this file and its consumers actually read *)
  Lemma tree_cc_wp (c : tree_fixed) (n : nat) :
    cc_wp (tree_cc c) n = tree_taint c.
  Proof using . reflexivity. Qed.

  Lemma tree_cc_wb_eq (c : tree_fixed) (I : list (bv 8)) :
    cc_wb (tree_cc c) I = (tree_turn c ∨ tree_taint c)%I.
  Proof using . reflexivity. Qed.

  (* THE LICENCE IS A BANNER-OWED CREDENTIAL AT EVERY COUNT.  /init's own
     families are position-indexed and the input itself is existential
     ([UserConsole.cc_wbn]), so the era's one licence answers the count
     the boot hands it and every count a later round asks for. *)
  Lemma tree_cc_wbn_of_turn (c : tree_fixed) (n : nat) :
    tree_turn c -∗ cc_wbn (tree_cc c) n.
  Proof using .
    iIntros "Ht". rewrite /cc_wbn. iExists (replicate n (bv_0 8)).
    iSplitR; [ iPureIntro; apply length_replicate | ].
    rewrite tree_cc_wb_eq. by iLeft.
  Qed.

  Lemma tree_cc_wbn_of_taint (c : tree_fixed) (n : nat) :
    tree_taint c -∗ cc_wbn (tree_cc c) n.
  Proof using .
    iIntros "#Ht". rewrite /cc_wbn. iExists (replicate n (bv_0 8)).
    iSplitR; [ iPureIntro; apply length_replicate | ].
    rewrite tree_cc_wb_eq. by iRight.
  Qed.

  (* ...AND WHAT IT BUYS: THE MINT.  This is the whole of the move section
     9.4 asked for -- the taint comes out of the banner-owed credential,
     so it is minted where that credential is SPENT (the banner) and
     nowhere earlier. *)
  Lemma tree_cc_wbn_mint (c : tree_fixed) (n : nat) :
    cc_wbn (tree_cc c) n ==∗ tree_taint c.
  Proof using .
    iIntros "Hb". rewrite /cc_wbn. iDestruct "Hb" as (I _) "Hb".
    rewrite tree_cc_wb_eq. iDestruct "Hb" as "[Ht | #Ht]".
    - iApply (tree_taint_mint c with "Ht").
    - iModIntro. iExact "Ht".
  Qed.

  (* =================================================================== *)
  (*  RULING (b), DISCHARGED AT THE TREE CLAIM                            *)
  (*                                                                     *)
  (*  [UkInit.init_kill_law] is what [UInitKernel.init_boot_con]'s P2 was *)
  (*  re-cut to (lane TL-6): give the lend, get it back and the child's   *)
  (*  kill row.  At echo it is the identity                              *)
  (*  ([UkInit.init_kill_law_of_taint]).  HERE IT HAS CONTENT, and the    *)
  (*  content is the ruling's: a kill /init cannot account for -- the     *)
  (*  shell it forked dies holding the console lease -- costs the tree    *)
  (*  application the era's LICENCE.  Each arm:                           *)
  (*                                                                     *)
  (*    the round-open arm: the banner has already run, the taint is in   *)
  (*      hand and persistent, and the lend goes back untouched;         *)
  (*    the banner-owed arm: the licence has not been spent, so it is     *)
  (*      spent HERE and the lend comes back on its TAINT arm -- the      *)
  (*      price, paid at the moment the kill is accounted for;           *)
  (*    the taint arm: nothing to pay.                                   *)
  (*                                                                     *)
  (*  WHAT IT DOES NOT DO is mint anything for free: no arm of the lend   *)
  (*  is derivable from the claim, and a spent licence is exactly the     *)
  (*  fact "some move of the file system was paid by nobody".            *)
  (* =================================================================== *)
  (* THE ROUND'S CREDENTIAL BUYS THE TAINT, AT EVERY ARM OF THE LEND.
     This is the whole of what the tree claim can read off
     [UkInit.init_lend_cred], and it is an UPDATE because one of the three
     arms is the era's LICENCE and minting the taint out of it SPENDS it
     ([tree_cc_wbn_mint] is one [ghost_map_elem_persist]).  The lend comes
     back at the arm it can: the round-open arm gives the taint by reading
     ([tree_cc_wp]), the banner-owed arm by minting -- and then the lend
     goes back on its own THIRD arm, which is the taint -- and the taint
     arm costs nothing.

     TWO CONSUMERS, which is why it is named here rather than written
     inline: the kill row just below (lane TL-6) and /init's EXEC SUPPLY
     at the tree claim ([UInitTreeExec.tree_init_exec_sup_lend_of_lend],
     lane TL-9), which is what the exec node's update door
     ([UkInit.init_exec_sup_pos]) was cut for. *)
  Lemma tree_lend_taint (c : tree_fixed) (st : fdstate)
      (l : list fdstate) (n : nat) :
    UkInit.init_lend_cred (tree_taint c) st
      (cc_wp (tree_cc c)) (cc_wbn (tree_cc c)) l n ==∗
    UkInit.init_lend_cred (tree_taint c) st
      (cc_wp (tree_cc c)) (cc_wbn (tree_cc c)) l n ∗ tree_taint c.
  Proof using .
    iIntros "Hl". rewrite /UkInit.init_lend_cred.
    iDestruct "Hl" as "[[%Hl Hw] | [[%Hl Hw] | #Ht]]".
    - (* the round-open arm: the taint IS the credential here, so the
         lend goes back on the arm it came in on *)
      rewrite tree_cc_wp. iDestruct "Hw" as "#Ht". iModIntro. iSplit.
      + iLeft. iSplitR; [ done | ]. iExact "Ht".
      + iExact "Ht".
    - (* the banner-owed arm: the licence is SPENT, and the lend comes
         back on the taint arm -- that is the price *)
      iMod (tree_cc_wbn_mint c n with "Hw") as "#Ht". iModIntro. iSplit.
      + iRight. iRight. iExact "Ht".
      + iExact "Ht".
    - iModIntro. iSplit.
      + iRight. iRight. iExact "Ht".
      + iExact "Ht".
  Qed.

  Lemma tree_init_kill_law (c : tree_fixed) (st : fdstate) :
    ⊢ UkInit.init_kill_law (tree_taint c) st
        (cc_wp (tree_cc c)) (cc_wbn (tree_cc c)).
  Proof using .
    rewrite /UkInit.init_kill_law. iIntros "!>" (l n) "Hl".
    iMod (tree_lend_taint c st l n with "Hl") as "[Hl #Ht]".
    iModIntro. iFrame "Hl". iIntros "!> _". iExact "Ht".
  Qed.

End TreeConsCred.

(* ===================================================================== *)
(*  2.  THE WRITE SIDE: THE DEPOSITS, THE BANNER AND THE DIAGNOSTICS      *)
(*                                                                       *)
(*  THE HEAVY SECTION, and its binder list is what [UkInit.kinit_w1]      *)
(*  needs and no more.  NO [Context] for [uexecSG]/[uprogSG]              *)
(*  ([UInitBoot.v]'s rule, learned the expensive way there): the          *)
(*  instances are [UexecExecInst]'s globals, and /init's own is the FREE  *)
(*  one, named explicitly at every statement below.                       *)
(* ===================================================================== *)
Section TreeInitWrite.
  Context {Σ : gFunctors}.
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!treeG Σ}.

  (* ------------------------------------------------------------------- *)
  (*  THE ONE STUB LEMMA: a byte of putc whose deposit is paid BY AN       *)
  (*  UPDATE the byte itself runs.                                        *)
  (*                                                                     *)
  (*  [UkInit.kinit_w1_of_law] pays the write off the flagged deposit and *)
  (*  carries nothing across; [UkInit.kinit_w1_frame] carries a resource  *)
  (*  across untouched.  Neither lets the byte MOVE ghost state, and the  *)
  (*  banner's first byte must: the licence it is handed is not a deposit *)
  (*  and has to become one.  The conclusion of [kinit_w1] is a [WP], so  *)
  (*  a basic update runs inside it -- that is the whole of this lemma,   *)
  (*  and it is where the tree application's taint is minted.             *)
  (* ------------------------------------------------------------------- *)
  Lemma kinit_w1_of_upd (N : uk_names Σ) (fdv : mword 64) (b : bv 8)
      (Ci Co : iProp Σ) :
    □ (Ci ==∗ UkRun.udepw_law (PS := uprogSG_free) 16 ∗ Co) -∗
    UkInit.kinit_w1 (PS := uprogSG_free) N fdv b Ci Co.
  Proof using .
    iIntros "#Hm" (h m avail) "%Ha0 %Ha2 #Hcode Hbuf HCi Hrun Hcont".
    iMod ("Hm" with "HCi") as "[Hwr HCo]".
    iDestruct (UkInit.kinit_w1_of_law (PS := uprogSG_free) N fdv b
                 with "Hwr") as "Hw1".
    iApply ("Hw1" $! h m avail with "[%] [%] Hcode Hbuf [] Hrun [HCo Hcont]");
      [ exact Ha0 | exact Ha2 | done | ].
    iIntros (h' ret) "Hbuf _ Hrun".
    iApply ("Hcont" $! h' ret with "Hbuf HCo Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  /INIT'S THREE DEPOSITS AT THE TREE CLAIM.                            *)
  (*                                                                     *)
  (*  [UInitBoot]'s assembly for echo, one application over, and every    *)
  (*  reading it does of the era's interface is TRIVIAL here: the output  *)
  (*  licence is free at a claim that claims no console                   *)
  (*  ([WpUart.cons_licence_triv]) and the kill credential is free at the *)
  (*  generic interface ([App.kill_cred_triv]) -- so all three deposits   *)
  (*  come off the supply alone, and the supply comes off the taint       *)
  (*  ([AppTree.tree_sup_of_taint]).  WHICH IS THE POINT: before the      *)
  (*  banner there is no taint and /init cannot write; after it there is, *)
  (*  and the rest of the walk is the supply's.                           *)
  (* ------------------------------------------------------------------- *)
  Lemma tree_init_deps (c : tree_fixed) (r : tree_names) :
    @file_app Σ _ = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    app_taint = kill_cred_triv ->
    ⊢ □ UkInit.init_deps (PS := uprogSG_free) (tree_taint c).
  Proof using .
    intros Heq Hcons Hkill.
    (* the supply, off the taint and at the era's record equation *)
    iAssert (□ (tree_taint c -∗ AppInv.app_sup))%I as "#Hsup".
    { iIntros "!> #Ht". rewrite /AppInv.app_sup Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (tree_sup_of_taint c r with "Ht"). }
    rewrite /UkInit.init_deps /UkInit.kinit_wlaw.
    iModIntro. iSplit; [ iSplit | iSplit ].
    - (* 16, the write: the supply and the kill credential, the latter
         free at this interface.  NO OUTPUT LICENCE (lane SUP-ONE): the
         taint buys it ([WpUart.cons_licence_of_taint]). *)
      iIntros "!> #Ht".
      iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
      + iApply ("Hsup" with "Ht").
      + rewrite Hkill /kill_cred_triv. done.
    - (* ...and the closed-fd leaf, which needs no claim at all *)
      rewrite /UkInit.kinit_wcl. iIntros "!>" (N0 b vw).
      iApply (UkWriteClosed.kinit_w1_of_closed_l0 (PS := uprogSG_free) N0 b vw).
    - iIntros "!> #Ht".
      iApply (udepw_law_of_sup (PSx := uprogSG_free) 15 (or_introl eq_refl)).
      iApply ("Hsup" with "Ht").
    - iIntros "!> #Ht".
      iApply (udepw_law_of_sup (PSx := uprogSG_free) 17 (or_intror eq_refl)).
      iApply ("Hsup" with "Ht").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE BANNER, AND THE MINT (the lane's deliverable).                   *)
  (*                                                                     *)
  (*  "init: starting sh" is eighteen bytes on fd 1 at the ledger /init's *)
  (*  prologue leaves on the console arm ([UInitFd.ufd_l3]).  The chain   *)
  (*  carries the table and one credential: the banner-owed one at the    *)
  (*  first byte, the taint at every byte after it.  THE FIRST BYTE IS    *)
  (*  THE MINT -- the licence becomes the taint, the taint becomes the    *)
  (*  write deposit, and the seventeen bytes that follow are paid from    *)
  (*  the same persistent fact.  What the last byte leaves is [cc_wp],    *)
  (*  the taint, which is what /init lends the shell it forks and what    *)
  (*  the two diagnostics below are paid from.                            *)
  (*                                                                     *)
  (*  SO THE CLAIM'S LIVE ARM COVERS EVERYTHING BEFORE THIS POINT -- the  *)
  (*  mknod, the two opens, the two dups -- and nothing after it.  That   *)
  (*  is section 9.4's "taint at the banner", in one lemma.               *)
  (* ------------------------------------------------------------------- *)
  Lemma tree_kinit_ban_law (c : tree_fixed) (stc : fdstate) (N : uk_names Σ) :
    □ UkInit.init_deps (PS := uprogSG_free) (tree_taint c) -∗
    UkInitMain.kinit_ban_law (PS := uprogSG_free) N stc
      (cc_wp (tree_cc c)) (cc_wbn (tree_cc c)).
  Proof using .
    iIntros "#Hdp".
    iAssert (□ (tree_taint c -∗ UkRun.udepw_law (PS := uprogSG_free) 16))%I
      as "#Hwr".
    { rewrite /UkInit.init_deps /UkInit.kinit_wlaw.
      iDestruct "Hdp" as "[[#Hwr _] _]". iExact "Hwr". }
    rewrite /UkInitMain.kinit_ban_law. iIntros "!>" (n) "Hwb".
    rewrite /UkInitMain.kinit_banner0 /UkInit.kinit_banner_pay.
    iIntros "Hstd".
    iExists (fun j : nat =>
               (UserFd.ustd (ukn_fd N) (ufd_l3 stc)
                ∗ match j with
                  | O => cc_wbn (tree_cc c) n
                  | S _ => tree_taint c
                  end)%I).
    iSplitR.
    - iIntros "!>" (j _). destruct j as [| j ].
      + (* THE FIRST BYTE: the licence is spent here *)
        iApply (kinit_w1_of_upd N _ _
                  (UserFd.ustd (ukn_fd N) (ufd_l3 stc) ∗ cc_wbn (tree_cc c) n)
                  (UserFd.ustd (ukn_fd N) (ufd_l3 stc) ∗ tree_taint c)).
        iIntros "!> [Hstd Hwb]".
        iMod (tree_cc_wbn_mint c n with "Hwb") as "#Ht". iModIntro.
        iFrame "Hstd Ht". iApply ("Hwr" with "Ht").
      + (* ...and every byte after it, off the same persistent fact *)
        iApply (kinit_w1_of_upd N _ _
                  (UserFd.ustd (ukn_fd N) (ufd_l3 stc) ∗ tree_taint c)
                  (UserFd.ustd (ukn_fd N) (ufd_l3 stc) ∗ tree_taint c)).
        iIntros "!> [Hstd #Ht]". iModIntro. iFrame "Hstd Ht".
        iApply ("Hwr" with "Ht").
    - iSplitL "Hstd Hwb"; [ iFrame "Hstd Hwb" | ].
      iIntros "[Hstd #Ht]". iFrame "Hstd". rewrite tree_cc_wp. iExact "Ht".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE TWO DIAGNOSTICS, off the round-open credential the banner left. *)
  (*  "init: exec sh failed" leaves a banner-owed credential for the next *)
  (*  sub-round (the taint answers it -- the licence is gone and cannot   *)
  (*  come back) and "init: fork failed" leaves nothing.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma tree_kinit_diag_law (c : tree_fixed) (stc : fdstate) :
    □ UkInit.init_deps (PS := uprogSG_free) (tree_taint c) -∗
    UkInitMain.kinit_diag_law (PS := uprogSG_free) stc
      (cc_wp (tree_cc c)) (cc_wbn (tree_cc c)).
  Proof using .
    iIntros "#Hdp".
    iAssert (□ (tree_taint c -∗ UkRun.udepw_law (PS := uprogSG_free) 16))%I
      as "#Hwr".
    { rewrite /UkInit.init_deps /UkInit.kinit_wlaw.
      iDestruct "Hdp" as "[[#Hwr _] _]". iExact "Hwr". }
    (* one chain, both literals: the table rides and the taint pays *)
    iAssert (□ (∀ (N' : uk_names Σ) (len : nat) (f : nat -> bv 8)
                  (Rt : iProp Σ),
                  □ (tree_taint c -∗ Rt) -∗
                  tree_taint c -∗
                  UkInit.kinit_banner_pay (PS := uprogSG_free) N' stc len f Rt))%I
      as "#Hchain".
    { iIntros "!>" (N' len f Rt) "#Hrt #Ht".
      rewrite /UkInit.kinit_banner_pay. iIntros "Hstd".
      iExists (fun _ : nat => UserFd.ustd (ukn_fd N') (ufd_l3 stc)).
      iSplitR.
      - iIntros "!>" (j _).
        iApply (kinit_w1_of_upd N' _ _
                  (UserFd.ustd (ukn_fd N') (ufd_l3 stc))
                  (UserFd.ustd (ukn_fd N') (ufd_l3 stc))).
        iIntros "!> Hstd". iModIntro. iFrame "Hstd".
        iApply ("Hwr" with "Ht").
      - iSplitL "Hstd"; [ iExact "Hstd" | ].
        iIntros "Hstd". iFrame "Hstd". iApply ("Hrt" with "Ht"). }
    rewrite /UkInitMain.kinit_diag_law. iSplit.
    - iIntros "!>" (n N') "Ht". rewrite tree_cc_wp.
      iApply ("Hchain" $! N' 21%nat _ (cc_wbn (tree_cc c) n) with "[] Ht").
      iIntros "!> #Ht'". iApply (tree_cc_wbn_of_taint c n with "Ht'").
    - iIntros "!>" (n N') "Ht". rewrite tree_cc_wp.
      iApply ("Hchain" $! N' 18%nat _ emp%I with "[] Ht").
      by iIntros "!> _".
  Qed.

End TreeInitWrite.
