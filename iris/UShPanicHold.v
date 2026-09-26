(* ===================================================================== *)
(*  UShPanicHold.v -- THE PROMPT LAW WITH A LINEAR FRAME                  *)
(*  (lane INIT-FILE, round 6 item A).                                     *)
(*                                                                       *)
(*  MEASURED, AND IT IS A FRAME.  [UShKernel.sh_prompt_law Wc] is two     *)
(*  arms: the open-fd one, [ksh_w ... (ustd * Wc I 0) (ustd * Wc I 2)],   *)
(*  and the closed one, which does not mention [Wc] at all.  The input    *)
(*  [I] IS THE SAME ON BOTH SIDES of the open arm -- the prompt resolves  *)
(*  a round, it does not read a line -- so a conjunct indexed by [I] and  *)
(*  not looked at rides through untouched.  And the step itself never     *)
(*  reaches the deed: [UShPanic.sh_prompt_law_holds_line_at] goes through *)
(*  [prompt_step_lpr_at], i.e. through the RECORD's own [lk_lpr_step].    *)
(*                                                                       *)
(*  WHAT [UShRound.sh_prompt_alt_of_deed] IS ABOUT IS A DIFFERENT BYTE.   *)
(*  That one is the round's BLOCK-FIRST byte, whose alternative the deed  *)
(*  decides; it lives in the round's own S3 and is not what this law      *)
(*  pays for.  So the [Hold] twin is three lines of plumbing and the      *)
(*  round keeps its deed-decided alternative to itself.                   *)
(*                                                                       *)
(*  A LEAF FILE: [UShPanic.v] does not move.                              *)
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
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
(* the ghost binder list, each module IMPORTED and not merely required --
   see [UkWriteLeaf.v]'s header *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UexecSG.
Require Import UkRun.
Require Import WpUart.
Require Import UkSh.               (* [ksh_w] / [wp_ksh_write_chain_txt] *)
Require Import UShKernel.          (* [sh_prompt_law] *)
Require Import UShOut.             (* the prompt's pure half and its call *)
Require Import EchoDisc.
Require Import EchoOut.
Require Import CtxIdDefs.
Require User.ShSyms.
(* as in EchoDisc / UEchoOut / UShOut: the Sail imports leave string_scope
   on top and [++] would elaborate as String.append *)
Local Open Scope list_scope.

Local Lemma shp_write : ShSyms.write = 0xca6%Z.
Proof. reflexivity. Qed.

(* THE TWO CONSTANT ALTERNATIVES' LENGTHS (lane LINK-GEN).  [FileDisc.cont]
   returns [EchoDisc.alt_panic] at [RFFork] / [RCFork] and [alt_execfail] at
   [RFExec] verbatim, so the shell's own two diagnostics are the SAME bytes
   at either application and their lengths are read once, here, instead of
   off [EchoDisc.line_alts_len3] / [line_alts_len1]. *)
Lemma alt_panic_len : length alt_panic = 5%nat.
Proof using .
  rewrite <- (line_alts_of_3 []). exact (EchoDisc.line_alts_len3 []).
Qed.

Lemma alt_execfail_len : length alt_execfail = 19%nat.
Proof using .
  rewrite <- (line_alts_of_1 []). exact (EchoDisc.line_alts_len1 []).
Qed.


Section UShPanicHold.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context `{PS : uprogSG Σ}.

  (* ---- the write tower's two structural moves ---- *)
  Lemma ksh_w_mono (N : uk_names Σ) (fdw ua : mword 64) (nb : nat)
      (Ci Ci' Co Co' : iProp Σ) :
    (Ci' -∗ Ci) -∗ (Co -∗ Co') -∗
    UkSh.ksh_w N fdw ua nb Ci Co -∗ UkSh.ksh_w N fdw ua nb Ci' Co'.
  Proof using .
    iIntros "Hin Hout H" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iDestruct ("Hin" with "HCi") as "HCi".
    iApply ("H" $! h m avail with "[%] [%] [%] Hcode HCi Hrun [Hout Hcont]");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "HCo Hrun".
    iApply ("Hcont" $! h' ret with "[Hout HCo] Hrun").
    iApply ("Hout" with "HCo").
  Qed.

  Lemma ksh_w_hold (N : uk_names Σ) (fdw ua : mword 64) (nb : nat)
      (Ci Co R : iProp Σ) :
    UkSh.ksh_w N fdw ua nb Ci Co -∗
    UkSh.ksh_w N fdw ua nb (Ci ∗ R) (Co ∗ R).
  Proof using .
    iIntros "H" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [HCi HR] Hrun Hcont".
    iApply ("H" $! h m avail with "[%] [%] [%] Hcode HCi Hrun [HR Hcont]");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "HCo Hrun".
    iApply ("Hcont" $! h' ret with "[$HCo $HR] Hrun").
  Qed.

  (* ...and at an EXISTENTIAL frame, which is the shape ruling H' puts the
     round's families in: the era's boot state is a shared index, so the
     credential and the hold are under ONE existential. *)
  Lemma ksh_w_ex {A : Type} (N : uk_names Σ) (fdw ua : mword 64) (nb : nat)
      (Ci Co : A -> iProp Σ) :
    (∀ x : A, UkSh.ksh_w N fdw ua nb (Ci x) (Co x)) -∗
    UkSh.ksh_w N fdw ua nb (∃ x : A, Ci x) (∃ x : A, Co x).
  Proof using .
    iIntros "H" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iDestruct "HCi" as (x) "HCi".
    iApply ("H" $! x h m avail with "[%] [%] [%] Hcode HCi Hrun [Hcont]");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "HCo Hrun".
    iApply ("Hcont" $! h' ret with "[HCo] Hrun"). by iExists x.
  Qed.

  (* ---- THE PROMPT LAW, WITH THE FRAME ---- *)
  Lemma sh_prompt_law_hold (Wc : list (bv 8) -> nat -> iProp Σ)
      (Hold : list (bv 8) -> iProp Σ) :
    UShKernel.sh_prompt_law (PS := PS) Wc -∗
    UShKernel.sh_prompt_law (PS := PS)
      (fun (I : list (bv 8)) (p : nat) => Wc I p ∗ Hold I)%I.
  Proof using .
    iIntros "#H !>" (N) "#Hro".
    iDestruct ("H" $! N with "Hro") as "#Hp".
    rewrite /UkSh.ush_prompt_law.
    iDestruct "Hp" as "#[Hopen Hclosed]". iModIntro. iSplitR.
    - iIntros (I l vw) "%Hfd".
      iApply (ksh_w_mono N _ _ _
                ((UserFd.ustd_at (ukn_fd N) l vw ∗ Wc I 0%nat) ∗ Hold I)%I
                _ ((UserFd.ustd_at (ukn_fd N) l vw ∗ Wc I 2%nat) ∗ Hold I)%I
                with "[] []").
      { iIntros "[Hs [Hc Hh]]". iFrame "Hs Hc Hh". }
      { iIntros "[[Hs Hc] Hh]". iFrame "Hs Hc Hh". }
      iApply ksh_w_hold. iApply ("Hopen" $! I l vw). by iPureIntro.
    - iIntros (l vw) "%Hcl". iApply ("Hclosed" $! l vw). by iPureIntro.
  Qed.

  (* ...and at the existential shape, where the RECORD itself is indexed
     by the era's boot state.  [lk_links] does not depend on that index at
     the file instance, so the one resource serves every [x]. *)
  Lemma sh_prompt_law_ex {A : Type} (x0 : A)
      (Wc : A -> list (bv 8) -> nat -> iProp Σ)
      (Hold : A -> list (bv 8) -> iProp Σ) :
    (∀ x : A, UShKernel.sh_prompt_law (PS := PS) (Wc x)) -∗
    UShKernel.sh_prompt_law (PS := PS)
      (fun (I : list (bv 8)) (p : nat) =>
         ∃ x : A, Wc x I p ∗ Hold x I)%I.
  Proof using .
    iIntros "#H !>" (N) "#Hro". iModIntro. iSplitR.
    - iIntros (I l vw) "%Hfd".
      iApply (ksh_w_mono N _ _ _
                (∃ x : A, (UserFd.ustd_at (ukn_fd N) l vw ∗ Wc x I 0%nat)
                          ∗ Hold x I)%I
                _ (∃ x : A, (UserFd.ustd_at (ukn_fd N) l vw ∗ Wc x I 2%nat)
                            ∗ Hold x I)%I
                with "[] []").
      { iIntros "[Hs Hc]". iDestruct "Hc" as (x) "[Hc Hh]".
        iExists x. iFrame "Hs Hc Hh". }
      { iIntros "Hq". iDestruct "Hq" as (x) "[[Hs Hc] Hh]".
        iFrame "Hs". iExists x. iFrame "Hc Hh". }
      iApply (ksh_w_ex N _ _ _
                (fun x : A => (UserFd.ustd_at (ukn_fd N) l vw ∗ Wc x I 0%nat)
                              ∗ Hold x I)%I
                (fun x : A => (UserFd.ustd_at (ukn_fd N) l vw ∗ Wc x I 2%nat)
                              ∗ Hold x I)%I).
      iIntros (x). iApply ksh_w_hold.
      iDestruct ("H" $! x N with "Hro") as "#Hpx".
      rewrite /UkSh.ush_prompt_law. iDestruct "Hpx" as "#[Hopen _]".
      iApply ("Hopen" $! I l vw). by iPureIntro.
    - iIntros (l vw) "%Hcl".
      iDestruct ("H" $! x0 N with "Hro") as "#Hp0".
      rewrite /UkSh.ush_prompt_law. iDestruct "Hp0" as "#[_ Hclosed]".
      iApply ("Hclosed" $! l vw). by iPureIntro.
  Qed.

End UShPanicHold.
