(* ===================================================================== *)
(*  UInitDiag.v -- WHAT PAYS FOR /init's TWO DIAGNOSTICS                  *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane INIT-DIAG, the      *)
(*   preparation for IO-LEAF M6b.  [UInitBanner] is the mould.)           *)
(*                                                                       *)
(*  <init> prints "init: exec sh failed\n" in the child whose exec of the *)
(*  shell failed (user/init.c:35) and "init: fork failed\n" when it       *)
(*  cannot fork (user/init.c:30), both with [printf] to fd 1 -- the       *)
(*  console, on the ledger the head's console arm is at                   *)
(*  ([UInitFd.ufd_l3], [ufd_l3_row1]).  Both are PROLOGUE ALTERNATIVES of *)
(*  the transcript ([EchoDisc.pro_alts !!! 1] and [!!! 2]) and both start *)
(*  from the credential the banner leaves behind: the round's prologue   *)
(*  open with the next byte its choice byte ([LinkRec.lk_pban]).          *)
(*                                                                       *)
(*  WHAT THIS FILE IS: the two per-byte obligations                       *)
(*  ([UkInit.kinit_w1] at fd 1, one byte of the alternative, on           *)
(*  [UInitBanner.kinit_w1_of_link_at]'s exact mould) and the two PAYMENTS *)
(*  in the shape /init's printf tower consumes                            *)
(*  ([UkInit.kinit_banner_pay] is generic in the literal: “give me the    *)
(*  descriptor table and I give you a per-byte family for the [len] bytes *)
(*  [f]”, which is what [UkInitPrintf.wp_kinit_printf_chain] takes), as   *)
(*  PERSISTENT conversions of the credential on                           *)
(*  [kinit_banner_law_holds_at]'s mould.                                  *)
(*  The exec diagnostic's payment ENDS at the next sub-round's banner     *)
(*  credential at the same count ([UInitBanner.kinit_ban_at n]), so the   *)
(*  restart head pays its banner from it with the law it already has;     *)
(*  the fork diagnostic's ends nowhere (the round is terminal).           *)
(*                                                                       *)
(*  WHAT IT IS NOT: nothing here is wired into /init's walk.  The two die *)
(*  arms ([UkInitMain.wp_kinit_main_die_de] / [_die_df]) print through    *)
(*  [UkInitPrintf.wp_kinit_printf], the free-law form at                  *)
(*  [Ch := fun _ => emp]; threading a credential to them is M6b proper.   *)
(*                                                                       *)
(*  ...AND THE CREDENTIAL THE BANNER LEAVES, EXACTLY ([kinit_pro_at]):    *)
(*  [UInitBanner.kinit_own_at] is stated at the record's [lk_owed], the   *)
(*  disjunction the SHELL is lent, and the other arm is not refutable     *)
(*  from anything /init holds ([EchoLinksPro.wr_owed_ambiguous]).  What   *)
(*  the fork's refund (FORK-REFUND's [Rc]) must hand back for the fork    *)
(*  diagnostic to be payable is therefore [kinit_pro_at], and the         *)
(*  banner's law is restated to leave it                                  *)
(*  ([kinit_banner_law_pro_holds_at]); [kinit_own_of_pro_at] is the lend. *)
(*                                                                       *)
(*  GENERIC OVER THE LINK RECORD (lane LINK-GEN / INIT-FILE), exactly as  *)
(*  [UInitBanner] is: everything below is proved once at an arbitrary     *)
(*  [L : LinkRec Σ] and the landed echo names are the generic ones at     *)
(*  [LinkRec.echo_link_inst], with no proof text.  NOTE the family's BASE *)
(*  is [lk_pban] and NOT [lk_pro]: echo's base carries the prologue's     *)
(*  failure index, which is what [lk_pdiag_done_1] needs, while the FILE  *)
(*  era loses it at its banner's end -- see [LinkRec]'s own note on the   *)
(*  prologue-diagnostic field set.  [lk_pro_of_pban] is the sound         *)
(*  projection out to the weaker round-open shape.                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
(* the ghost binder list, each module IMPORTED and not merely required --
   see [UkWriteLeaf.v]'s header *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UexecSlot UexecSG.
Require Import UkRun UkRunSys.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import UInitFd.            (* [ufd_l3] / [ufd_l3_row1] *)
Require Import UkInit UkInitLit UkInitMain.
Require Import EchoDisc.
Require Import EchoOut.
Require Import EchoLinks.
Require Import LinkRec.            (* lane LINK-GEN: the record this file
                                      is generic over *)
Require Import UInitBanner.        (* the mould: the halves, [kbn_fam_at],
                                      [kinit_ban_at] / [kinit_own_at] *)
Require Import CtxIdDefs.
Require User.InitSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  S1  THE PURE HALF: init's two rodata diagnostics ARE the era's        *)
(*      alternatives 1 and 2.  Era-free -- no link record, no [Σ] --      *)
(*      so it sits above the generic section and is not repeated in it.   *)
(* ===================================================================== *)
Section UInitDiagPure.
  (* init's literals, by base ([UkInitMain]'s table) *)
  Local Notation LIT_FORK  := 0x9a0.   (* "init: fork failed\n"     *)
  Local Notation LIT_EXEC  := 0x9c0.   (* "init: exec sh failed\n"  *)

  Lemma init_execfail_bytes_bool :
    forallb (fun j : nat =>
               match pro_alts !!! 1%nat !! j with
               | Some x => Z.eqb (bv_unsigned x)
                                 (bv_unsigned (init_lit LIT_EXEC j))
               | None => false
               end) (seq 0 21) = true.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma init_execfail_bytes (j : nat) :
    (j < 21)%nat -> pro_alts !!! 1%nat !! j = Some (init_lit LIT_EXEC j).
  Proof using .
    intros Hj. pose proof init_execfail_bytes_bool as H.
    rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    destruct (pro_alts !!! 1%nat !! j) as [x |] eqn:Hx; [| discriminate ].
    apply Z.eqb_eq in H. f_equal. by apply bv_eq.
  Qed.

  Lemma init_forkfail_bytes_bool :
    forallb (fun j : nat =>
               match pro_alts !!! 2%nat !! j with
               | Some x => Z.eqb (bv_unsigned x)
                                 (bv_unsigned (init_lit LIT_FORK j))
               | None => false
               end) (seq 0 18) = true.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma init_forkfail_bytes (j : nat) :
    (j < 18)%nat -> pro_alts !!! 2%nat !! j = Some (init_lit LIT_FORK j).
  Proof using .
    intros Hj. pose proof init_forkfail_bytes_bool as H.
    rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    destruct (pro_alts !!! 2%nat !! j) as [x |] eqn:Hx; [| discriminate ].
    apply Z.eqb_eq in H. f_equal. by apply bv_eq.
  Qed.

End UInitDiagPure.

Section UInitDiagGen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  (* THE LINK RECORD (lane LINK-GEN): /init's two prologue diagnostics are
     the same bytes at either application, and what changes -- the taint,
     the era's pin, the era's extra state under the credential -- is the
     record's. *)
  Context (L : LinkRec Σ).
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  (* init's literals, by base ([UkInitMain]'s table) *)
  Local Notation LIT_START := 0x988.   (* "init: starting sh\n"     *)
  Local Notation LIT_FORK  := 0x9a0.   (* "init: fork failed\n"     *)
  Local Notation LIT_EXEC  := 0x9c0.   (* "init: exec sh failed\n"  *)

  (* =================================================================== *)
  (*  S2  ONE BYTE OF A DIAGNOSTIC, THROUGH THE ERA'S LINKS               *)
  (* =================================================================== *)
  (* WHAT THE WALK WOULD CARRY: the round's choice [a] filed with [i] of
     its bytes out, or the taint -- the record's prologue-diagnostic
     family, as [UInitBanner.bnr_at] is its banner one. *)
  Definition pdg_at (v : era_pins) (I : list (bv 8)) (a i : nat) : iProp Σ :=
    lk_pdiag L (S gen_id) v I a i.

  (* [UInitBanner.kinit_w1_of_link_at]'s exact mould, with the diagnostic's
     step in the banner's place. *)
  Lemma kinit_w1_of_link_pdiag_at (N : uk_names Σ) (v : era_pins)
      (I : list (bv 8))
      (l vw : list fdstate) (rb : bool) (a i : nat) (b : bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    pro_alts !!! a !! i = Some b ->
    lk_pin L (S gen_id) v -∗
    lk_links L -∗
    UkInit.kinit_w1 N (mword_of_int 1 : mword 64) b
      (UserFd.ustd_at (ukn_fd N) l vw ∗ pdg_at v I a i)
      (UserFd.ustd_at (ukn_fd N) l vw ∗ pdg_at v I a (S i)).
  Proof using .
    intros Hli Hb. iIntros "#Hpin #Hlk".
    iApply (UInitBanner.kinit_w1_of_step N _ _ l vw rb b Hli).
    iIntros "!>" (Φ) "Hbnd HΦ". rewrite /pdg_at.
    iApply (lk_pdiag_step L (S gen_id) v I a i b Φ Hb with "Hpin Hlk Hbnd HΦ").
  Qed.

  (* =================================================================== *)
  (*  S3  THE CREDENTIAL THE BANNER LEAVES, EXACTLY                       *)
  (* =================================================================== *)
  Local Notation stc_cons := (FdOpen true true (FdDevice CONSOLE)).

  (* the round's prologue open, the choice byte next, with the era's pin
     beside it: [UInitBanner.kinit_own_at] at the record's [lk_pban], which
     is the base of the diagnostic family and is STRICTLY MORE than the
     round-open shape [lk_pro] (see the file header). *)
  Definition kinit_pro_at (n : nat) : iProp Σ :=
    (∃ (v : era_pins) (I : list (bv 8)),
       ⌜length I = n⌝ ∗ lk_pin L (S gen_id) v
       ∗ lk_pban L (S gen_id) v I)%I.

  (* A bare [apply _] here cost 7.4 s of this file's 11 s: the search is on
     the (exists, sep) STRUCTURE, not on the leaves.  Naming the two
     structural instances first leaves the leaf search cheap (0.6 s). *)
  Global Instance kinit_pro_timeless_at n : Timeless (kinit_pro_at n).
  Proof using .
    rewrite /kinit_pro_at.
    apply bi.exist_timeless => v.
    apply bi.exist_timeless => I.
    apply bi.sep_timeless; [ apply _ | ].
    apply bi.sep_timeless; apply _.
  Qed.

  (* ...is what /init lends the shell ([kinit_own_at] is the shape the
     shell's prompt law takes), through the record's projection out of the
     prologue base and then the loose reading ... *)
  Lemma kinit_own_of_pro_at (n : nat) :
    kinit_pro_at n -∗ UInitBanner.kinit_own_at L n.
  Proof using .
    rewrite /kinit_pro_at /UInitBanner.kinit_own_at.
    iIntros "H". iDestruct "H" as (v I) "(%Hl & #Hpin & Hc)".
    iExists v, I. iSplitR; [ by iPureIntro | ]. iFrame "Hpin".
    iDestruct (lk_pro_of_pban L (S gen_id) v I with "Hc") as "Hc".
    iApply (lk_pro_owed L (S gen_id) v I with "Hc").
  Qed.

  (* ...and is what the banner's eighteenth byte leaves: the banner law
     restated to keep it ([UInitBanner.kinit_banner_law_holds_at] with the
     end shape not weakened).  Same proof, one lemma different. *)
  Lemma kinit_banner_law_pro_holds_at :
    lk_links L -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         UInitBanner.kinit_ban_at L n -∗
         UkInitMain.kinit_banner0 N stc_cons (kinit_pro_at n)).
  Proof using .
    iIntros "#Hlk !>" (n N) "Hban".
    rewrite /UkInitMain.kinit_banner0 /UkInit.kinit_banner_pay.
    iIntros (vw) "Hl".
    rewrite /UInitBanner.kinit_ban_at.
    iDestruct "Hban" as (v I) "(%Hlen & #Hpin & Hbnr)".
    iExists (fun i => UserFd.ustd_at (ukn_fd N) (ufd_l3 stc_cons) vw
                      ∗ UInitBanner.bnr_at L v I i)%I.
    iSplitR "Hbnr Hl".
    { iIntros "!>" (j) "%Hj".
      iApply (UInitBanner.kinit_w1_of_link_at L N v I (ufd_l3 stc_cons) vw true j
                (init_lit LIT_START j)
                (ufd_l3_row1 stc_cons) (UInitBanner.init_banner_bytes j Hj)
                with "Hpin Hlk"). }
    iSplitL; [ rewrite /UInitBanner.bnr_at; iFrame "Hl Hbnr" | ].
    iIntros "[$ Hbnd]". rewrite /kinit_pro_at. iExists v, I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpin".
    iApply (lk_pban_of_ban_done L (S gen_id) v I with "[Hbnd]").
    rewrite /UInitBanner.bnr_at.
    by replace (length u_banner) with 18%nat by (vm_compute; reflexivity).
  Qed.

  (* =================================================================== *)
  (*  S4  THE TWO PAYMENTS, AS PERSISTENT CONVERSIONS OF THE CREDENTIAL   *)
  (*                                                                     *)
  (*  [UkInit.kinit_banner_pay N stc len f Rt] is what the printf tower   *)
  (*  spends for ANY literal ([UkInitPrintf.wp_kinit_printf_chain] takes  *)
  (*  its [∃ Ch] apart), and [UkInitMain.kinit_banner0] is it at the      *)
  (*  banner.  These are it at the two diagnostics, paid from             *)
  (*  [kinit_pro_at n] on the console ledger, closed under the era's links *)
  (*  and so [□]: whatever /init's walk will carry the credential as, the *)
  (*  conversion travels beside it the way [UkInitMain.kinit_ban_law]     *)
  (*  does for the banner.                                               *)
  (* =================================================================== *)

  (* "init: exec sh failed\n": 21 bytes at fd 1, alternative 1, and what
     is left is the NEXT sub-round's banner credential at the same count
     -- /init reaps this child and its restart head spends it on the
     banner law it already holds. *)
  Lemma kinit_execfail_law_holds_at :
    lk_links L -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         kinit_pro_at n -∗
         UkInit.kinit_banner_pay N stc_cons 21%nat (init_lit LIT_EXEC)
           (UInitBanner.kinit_ban_at L n)).
  Proof using .
    iIntros "#Hlk !>" (n N) "Hpro".
    rewrite /UkInit.kinit_banner_pay. iIntros (vw) "Hl".
    rewrite /kinit_pro_at. iDestruct "Hpro" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists (fun i => UserFd.ustd_at (ukn_fd N) (ufd_l3 stc_cons) vw
                      ∗ pdg_at v I 1%nat i)%I.
    iSplitR "Hc Hl".
    { iIntros "!>" (j) "%Hj".
      iApply (kinit_w1_of_link_pdiag_at N v I (ufd_l3 stc_cons) vw true 1%nat j
                (init_lit LIT_EXEC j)
                (ufd_l3_row1 stc_cons) (init_execfail_bytes j Hj)
                with "Hpin Hlk"). }
    iSplitL.
    { iFrame "Hl". rewrite /pdg_at.
      iApply (lk_pdiag_0 L (S gen_id) v I 1%nat with "Hc"). }
    iIntros "[$ Hc]". rewrite /UInitBanner.kinit_ban_at. iExists v, I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpin".
    iApply (lk_pdiag_done_1 L (S gen_id) v I 21%nat
              ltac:(vm_compute; reflexivity) with "[Hc]").
    rewrite /pdg_at. iExact "Hc".
  Qed.

  (* "init: fork failed\n": 18 bytes at fd 1, alternative 2, the round
     terminal -- nothing follows on this wire, so nothing is left: the
     credential the last byte hands back is dropped (affine). *)
  Lemma kinit_forkfail_law_holds_at :
    lk_links L -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         kinit_pro_at n -∗
         UkInit.kinit_banner_pay N stc_cons 18%nat (init_lit LIT_FORK) emp).
  Proof using .
    iIntros "#Hlk !>" (n N) "Hpro".
    rewrite /UkInit.kinit_banner_pay. iIntros (vw) "Hl".
    rewrite /kinit_pro_at. iDestruct "Hpro" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists (fun i => UserFd.ustd_at (ukn_fd N) (ufd_l3 stc_cons) vw
                      ∗ pdg_at v I 2%nat i)%I.
    iSplitR "Hc Hl".
    { iIntros "!>" (j) "%Hj".
      iApply (kinit_w1_of_link_pdiag_at N v I (ufd_l3 stc_cons) vw true 2%nat j
                (init_lit LIT_FORK j)
                (ufd_l3_row1 stc_cons) (init_forkfail_bytes j Hj)
                with "Hpin Hlk"). }
    iSplitL.
    { iFrame "Hl". rewrite /pdg_at.
      iApply (lk_pdiag_0 L (S gen_id) v I 2%nat with "Hc"). }
    by iIntros "[$ _]".
  Qed.

End UInitDiagGen.

(* ===================================================================== *)
(*  THE ECHO INSTANCE (lane LINK-GEN): the names this file exports are    *)
(*  the generic ones at [echo_link_inst], with no proof text.             *)
(* ===================================================================== *)
Section UInitDiagEcho.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{PS : uprogSG Σ}.

  Local Notation stc_cons := (FdOpen true true (FdDevice CONSOLE)).
  Local Notation LIT_FORK  := 0x9a0.
  Local Notation LIT_EXEC  := 0x9c0.
  Local Notation EI := (echo_link_inst T γ).

  Definition pdg (v : era_pins) (I : list (bv 8)) (a i : nat) : iProp Σ :=
    pdg_at EI v I a i.

  Definition kinit_w1_of_link_pdiag (N : uk_names Σ) (v : era_pins)
      (I : list (bv 8))
      (l vw : list fdstate) (rb : bool) (a i : nat) (b : bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    pro_alts !!! a !! i = Some b ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    UkInit.kinit_w1 N (mword_of_int 1 : mword 64) b
      (UserFd.ustd_at (ukn_fd N) l vw ∗ pdg v I a i)
      (UserFd.ustd_at (ukn_fd N) l vw ∗ pdg v I a (S i))
    := kinit_w1_of_link_pdiag_at EI N v I l vw rb a i b.

  Definition kinit_pro (n : nat) : iProp Σ := kinit_pro_at EI n.

  Global Instance kinit_pro_timeless n : Timeless (kinit_pro n).
  Proof using . rewrite /kinit_pro. apply _. Qed.

  Definition kinit_own_of_pro (n : nat) :
    kinit_pro n -∗ UInitBanner.kinit_own T γ n
    := kinit_own_of_pro_at EI n.

  Definition kinit_banner_law_pro_holds :
    echo_links T γ -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         UInitBanner.kinit_ban T γ n -∗
         UkInitMain.kinit_banner0 N stc_cons (kinit_pro n))
    := kinit_banner_law_pro_holds_at EI.

  Definition kinit_execfail_law_holds :
    echo_links T γ -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         kinit_pro n -∗
         UkInit.kinit_banner_pay N stc_cons 21%nat (init_lit LIT_EXEC)
           (UInitBanner.kinit_ban T γ n))
    := kinit_execfail_law_holds_at EI.

  Definition kinit_forkfail_law_holds :
    echo_links T γ -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         kinit_pro n -∗
         UkInit.kinit_banner_pay N stc_cons 18%nat (init_lit LIT_FORK) emp)
    := kinit_forkfail_law_holds_at EI.

End UInitDiagEcho.
