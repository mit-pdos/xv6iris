(* ===================================================================== *)
(*  UShPipeChild.v -- THE PIPELINE LINE'S CHILD, PAID (lane              *)
(*  SH-PIPE-ROUND-3, item 1; design claude-notes/design/app-pipe.md      *)
(*  SS4.3c).                                                             *)
(*                                                                       *)
(*  [UkShPipeRound.wp_kshm_child_pipe] is sh's runcmd child at the pipe  *)
(*  line -- 0x9c0, [parsecmd], the seam, and [runcmd]'s PIPE arm -- and  *)
(*  it inherits two things from the FREE arm it ends on                   *)
(*  ([UkShPipe.wp_kshr_pipe_arm]): the free write law [UkSh.sh_deps],     *)
(*  which a verified shell holds only under the taint, and the free exit  *)
(*  payload [(|- ukn_pay N (-1))].  A ROUND whose console block the wire  *)
(*  accounts for holds neither (SH-PIPE-ROUND-2, refutation 2).           *)
(*                                                                       *)
(*  This file is the PAID twin, and it costs NO new walk: lane            *)
(*  PIPE-ARM-PAID left [UkShPipePaid.wp_kshr_pipe_arm_paid] -- the same   *)
(*  arm with its three [panic] tails paid at the era's credential -- so   *)
(*  what is here is [wp_kshm_child_pipe]'s walk ending on THAT.  It is    *)
(*  [UkShRedirChild.wp_kshm_child_file_redir] one line shape over: no     *)
(*  [UkSh.sh_deps] anywhere, every exit paid by a law into the payload,   *)
(*  and the lend [Cr] carried whole across the parse.                     *)
(*                                                                       *)
(*  WHAT IS NOT HERE, and why (see the lane report, STOP 1).  The brief's *)
(*  item 2 -- [UShPipeRound.sh_pipe_child_law] proved -- is NOT in this   *)
(*  file: the round's EXIT cannot be built out of the landed pieces.      *)
(*  [PipeBoth.pblk2_exit] files the round's code at the PROMPT's first    *)
(*  byte and leaves [PipeLinksLine.pwc_sp_t], i.e. [Wcf I 1]; sh's        *)
(*  runcmd child hands back [UkShFork.ushf_wq I = Wcf I 3 \/ Wcf I 0]     *)
(*  and the prompt is written by the MAIN loop, one process later.  The   *)
(*  mismatch is mechanised in [iris/UShPipeExit.v]                        *)
(*  ([pipe_open_not_line], [pipe_blk2_not_line]).                         *)
(*                                                                       *)
(*  TWO NOTES ON THE STATEMENT BELOW.                                     *)
(*                                                                       *)
(*   - THE ALLOCATOR'S LEFTOVER [UM3] IS DROPPED.  The free walk's split  *)
(*     took it ([forall gp, UM3 -* Cr -* R gp -* ...]) so a caller could  *)
(*     route it; the paid arm's split is fixed at [forall gp, Cr -* R gp  *)
(*     -* RcL gp * (RcR gp * (Rk gp * Cx gp))] -- the arm chooses whether *)
(*     [Cr] pays the [pipe(2)] tail or is split at the forks, so no       *)
(*     caller may split it up front -- and there is no slot for [UM3].    *)
(*     The child exits at the end of the round and the round wants        *)
(*     nothing of the heap, so the walk simply drops it.                  *)
(*   - [shk_rodata] is not a new premise: it is [UkSh.ush_jtab_ro] of the *)
(*     jump table the walk already holds.                                 *)
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
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import PipeNames.
Require Import UserCwd.
Require Import UserChildren.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShLoop.
Require Import UkShMain.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShRedirSeam.
Require Import UkShPipe.
Require Import UkShPipePaid.    (* the PAID arm *)
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import UkShPipeLex.
Require Import UkShPipeSeam.
Require Import RefParse.
Require Import RefParseBridge.  (* [ref_parsecmd_pipe]: the pipe line at the reference *)
Require Import UkShRedirs.      (* [ushp_malloc_chain] *)
Require Import UkShParser.      (* [ushp_room], [ushp_zero_at]: the reference's room and cut *)
Require Import UkShSeam.        (* [wp_ref_child]: THE CHILD, once *)
Require Import UkShPipeRound.   (* the free walk, the cut and the line shape *)
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UexecSG.
Require Import UexecRet.
Local Open Scope Z_scope.
Import Defs.

Section UShPipeChild.
  (* [UkShPipeRound.v]'s binder list verbatim. *)
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).

  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

  Context (UM0 UM1 UM2 UM3 : iProp Σ).
  Hypothesis ushq_malloc_ok12 : ushp_malloc_ty UM1 UM2.

  (* A FANCY UPDATE IN FRONT OF THE TRIVIAL-POST WP ([UConsOpen.fupd_wp_triv]
     restated -- that file is not in this one's cone).  [RiscvPtsto.wp_triv]
     is a DEFINITION, so the proofmode's [ElimModal] instance for [wp] does
     not see through it and [iMod] fails against a bare [mWP e] goal. *)
  Local Lemma fupd_mwp_pipe (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* =================================================================== *)
  (*  S0  THE PAID CHILD AT *TWO* PAYERS (lane SH-PIPE-ROUND-8; design    *)
  (*      SS4.3q, whose one-token repair this REPLACES -- see the lane's   *)
  (*      Findings block).                                                *)
  (*                                                                     *)
  (*  SS4.3q rules that [box (Cr -* ukn_pay N (-1))] below must become a   *)
  (*  FANCY UPDATE, because the round's [Cr] is the two-writer family and  *)
  (*  the family is born by one ([UShPipeRound2.pipe_round_entry]).  That  *)
  (*  token change is NOT MAKEABLE HERE and is NOT NEEDED, and both are    *)
  (*  measured:                                                           *)
  (*                                                                     *)
  (*   - NOT MAKEABLE: the premise is not spent in this file.  It is       *)
  (*     forwarded, as the lend's law, to [UkShSeam.wp_ref_child], which   *)
  (*     forwards it again into the whole general parse cone               *)
  (*     ([UkShParser], [UkShArgs], [UkShRedirs], [UkShGettoken],           *)
  (*     [UkShParse*]) -- none of which is this lane's, and every one of    *)
  (*     which states it as a PURE wand.  [UkShPipePaid.                    *)
  (*     wp_kshr_pipe_arm_paid], the other callee, does not take it at all. *)
  (*   - NOT NEEDED: the family has to exist before [pipe(2)], not before   *)
  (*     the PARSE, and the parse's payer and the arm's lend need not be    *)
  (*     the same resource.  [Pex] comes BACK out of the parse, and the     *)
  (*     parse's return is a WP point -- so the walk carries the round's    *)
  (*     LEND [Cp] (for which the pure wand is [UkShPipeFork.pterm_wc_of],  *)
  (*     i.e. [Wcf I 3 -* ushf_wq Wct I]) across the parse and turns it     *)
  (*     into the family with ONE [iMod] at 0x9c6, before [runcmd].        *)
  (*                                                                     *)
  (*  So this is the landed walk with the lend and the arm's [Cr] split     *)
  (*  into two premises and one [iMod] between them; [wp_kshm_child_pipe_  *)
  (*  paid] below is this at [Cp := Cr] and its statement does not move.   *)
  (* =================================================================== *)
  (* ...AND THE BREAK IS READ OFF THE PARSE'S LEFTOVER (lane
     SH-PIPE-ROUND-12; SS4.3u's standing grant).  The landed statement
     asked for [usz γs szv] BESIDE [UM0], and that premise list is
     UNSATISFIABLE at any real allocator state: [UkShMalloc.ushm_fresh]
     and [ushm_one] both carry [usz γs _], [UserHeap.uheap] -- inside
     [urun] -- carries the other half of the same [ghost_var], and three
     halves is [False] ([UShPipeLaw.pipe_paid_entry_absurd] mechanises
     it).  The child law hands its prover exactly ONE program-side half,
     so the break has to come OUT of what the parse leaves: [UM3] at the
     round's own instantiation is [ushm_one_ge N (sz + 65536) _], whose
     [usz γs (sz + 65536)] IS the [szv] the arm wants.

     SO THE RESOURCE IS A PARAMETER [Usz] and the reading is a premise.
     At [Usz := usz γs szv] and the trivial reading this is the landed
     statement, BYTE-IDENTICAL -- [wp_kshm_child_pipe_paid_at] below --
     and at [Usz := emp] the round reads the break off [UM3]. *)
  (* =================================================================== *)
  (*  THE PAID CHILD AT THE REFERENCE PARSER, ONCE (user-once A3b).       *)
  (*                                                                     *)
  (*  [UkShSeam.wp_ref_child_pipe]'s paid twin: the same [UkShSeam.        *)
  (*  wp_ref_child] from 0x9c0 through [parsecmd] and the seam to          *)
  (*  [runcmd]'s entry, ending on the PAID arm [UkShPipePaid.               *)
  (*  wp_kshr_pipe_arm_paid] instead of the free one.  The parse is paid   *)
  (*  by the lend [Cp] whole; the family is born out of it at the parse's  *)
  (*  return (the fancy update at [runcmd]'s entry, a WP point); the       *)
  (*  break is read off the allocator's leftover [UM'] as the note above   *)
  (*  says.  The landed statement below is this at the pipe line's shape. *)
  (* =================================================================== *)
  Lemma wp_ref_child_pipe_paid (UM UM' : iProp Σ)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (toksl toksr : list (nat * nat)) (g : nat -> bv 8)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cp Cr Bp Usz Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ref_sym_scope len f ->
    ref_parsecmd len f = Some (UshpPipe (UshpExec toksl) (UshpExec toksr)) ->
    g = UkShParser.ushp_zero_at
          (ref_nulcut (UshpPipe (UshpExec toksl) (UshpExec toksr))) (ushp_ext len f) ->
    UkShRedirs.ushp_malloc_chain N 3 UM UM' ->
    (⊢ UM' -∗ Usz -∗ usz γs szv) ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    Usz -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM -∗
    Cp -∗
    □ (app_taint -∗ Qc (-1)) -∗
    □ (Cp -∗ ukn_pay N (-1)) -∗
    (Cp ={⊤}=∗ Cr) -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    Wr -∗
    UkShPipe.ush_wait0_law N Wr Pw -∗
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q (UExec (ush_args s0 g toksl)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q (UExec (ush_args s0 g toksr)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       Cx γp -∗
       Wr -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hscope Href Hg Hchain Hszof Hs0 Hs64 Hs38
           HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2.
    subst g.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Husz Hstd Hcwd Hch
             HM Hcr #Hkw #Hpxw Halloc Hsplit Hpipe HWr #Hwl
             #Hlawp #Hbp #Hlawf #Hbx Hrun HcL HcR Hpar".
    iDestruct (UkSh.ush_jtab_ro γt with "Hjt") as "#Hro".
    (* ---- 0x9c0 .. parsecmd .. the seam .. runcmd's entry: THE CHILD ---- *)
    replace (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (UkShParser.ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr))
            + (8 + (UkShDiag.ush_Dg + (2 + n))))%nat
      by (change (UkShParser.ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr)))
            with 66%nat; lia).
    iApply (UkShSeam.wp_ref_child N UM UM' h m dw dv s0 len f
              (UshpPipe (UshpExec toksl) (UshpExec toksr)) (2 + n) Cp
              Hs1 Hscope Href (conj I I) Hchain Hs0 Hs64 Hs38
              with "Hcode Hpcode Hpro Hline Hws Hsy HM Hpxw Hcr Hrun").
    iIntros (h' m' p) "%Ha0 %Hcs #Htree #Hlineq Hws Hsy HM' Hcr Hrun".
    (* ---- THE BREAK, off what the parse left ---- *)
    iPoseProof (Hszof with "HM' Husz") as "Hsz".
    (* ---- THE FAMILY IS BORN HERE: runcmd's entry is a WP point ---- *)
    iApply fupd_mwp_pipe.
    iMod ("Halloc" with "Hcr") as "Hcr". iModIntro.
    (* ---- runcmd's PIPE arm, PAID ---- *)
    replace (UkShParser.ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr))
             + (8 + (UkShDiag.ush_Dg + (2 + n))))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (68 + n))))%nat
      by (change (UkShParser.ushp_room (UshpPipe (UshpExec toksl) (UshpExec toksr)))
            with 66%nat; lia).
    iApply (UkShPipePaid.wp_kshr_pipe_arm_paid Hpsok_free N
              (UExec (ush_args s0 _ toksl)) (UExec (ush_args s0 _ toksr))
              h' m' p szv cwdv ld st0 st1 Sc (68 + n)%nat
              R RcL RcR Rk Cx Bx Qc Cr Bp Wr Pw
              HQc Ha0 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2
              with "Hcode Hro Hjt Htree Hsz Hstd Hcwd Hch Hkw Hcr Hsplit
                    Hpipe HWr Hwl Hlawp Hbp Hlawf Hbx Hrun HcL HcR Hpar").
  Qed.

  Lemma wp_kshm_child_pipe_paid_at_sz
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp ge : nat)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cp Cr Bp : iProp Σ)
      (* WHERE THE BREAK COMES FROM *)
      (Usz : iProp Σ)
      (* the two [wait(0)]s' law, relayed (design app-pipe SS4.3w,
         purchase 3) -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
      (Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    (⊢ UM3 -∗ Usz -∗ usz γs szv) ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    Usz -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    (* THE PARSE'S PAYER: the round's lend, whole, across [parsecmd] *)
    Cp -∗
    □ (app_taint -∗ Qc (-1)) -∗
    □ (Cp -∗ ukn_pay N (-1)) -∗
    (* ...AND THE ARM'S LEND, born out of it at the parse's return *)
    (Cp ={⊤}=∗ Cr) -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    (* the wait credential and the law that spends it, twice *)
    Wr -∗
    UkShPipe.ush_wait0_law N Wr Pw -∗
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    (* SS4.3u (lane SH-PIPE-ROUND-9): the fork tails' credential is
       [RcR γp ∗ Cx γp] and not [Cx γp] -- the family's RIGHT chain is
       ONE resource, shared by design between cat's output (mode 1) and
       a [panic("fork")] (mode 3), and the arm's single up-front split
       cannot give it to both.  It does not have to: the right child's
       lend is in sh's hand at BOTH tails and was being dropped.  This
       file only forwards the law. *)
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) args)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) [(S (S gp), ge)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       (* the two forks returned a pid (purchase 3): a -1 panics and never
          reaches 0xea -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       Cx γp -∗
       (* ...and the wait credential, unspent *)
       Wr -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hszof Hs1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hs38
           HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Husz Hstd Hcwd Hch
             HM Hcr #Hkw #Hpxw Halloc Hsplit Hpipe HWr #Hwl
             #Hlawp #Hbp #Hlawf #Hbx Hrun HcL HcR Hpar".
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    (* THE GENERAL PAID CHILD at the pipe line's tree: the line parses to
       ONE PIPE of two EXECs (RefParseBridge.ref_parsecmd_pipe), its symbol
       bytes are in the catalogued scope, its cut is the reference's, and
       the three allocations chain *)
    iApply (wp_ref_child_pipe_paid UM0 UM3 h m dw dv s0 szv cwdv len f
              args [(S (S gp), ge)] (ushq_cut args len f ge) ld st0 st1 Sc n
              R RcL RcR Rk Cx Bx Qc Cp Cr Bp Usz Wr Pw
              Hs1
              (UkShPipeLex.ushq_sym_ok_scope len f (UkShPipeLex.ushq_sym_ok_pipe len f gp ge Hpq))
              (ref_parsecmd_pipe len f gp ge args Hnn0 Hpq Htoks Htlen)
              ltac:(cbn [ref_nulcut]; rewrite UkShParser.ushp_zero_at_app;
                    rewrite <- (UkShParser.ushp_nulfold_zero_at args);
                    rewrite <- (UkShParser.ushp_nulfold_zero_at [(S (S gp), ge)]);
                    reflexivity)
              ltac:(cbn [UkShRedirs.ushp_malloc_chain];
                    exists UM1; split; [ exact Hm01 | ];
                    exists UM2; split; [ exact ushq_malloc_ok12 | ];
                    exists UM3; split; [ exact Hm23 | reflexivity ])
              Hszof Hs0 Hs64 Hs38 HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2
              with "Hcode Hjt Hpcode Hpro Hline Hws Hsy Husz Hstd Hcwd Hch
                    HM Hcr Hkw Hpxw Halloc Hsplit Hpipe HWr Hwl Hlawp Hbp Hlawf
                    Hbx Hrun HcL HcR Hpar").
  Qed.

  (* ...AND THE LANDED STATEMENT, BYTE-IDENTICAL: the general one at
     [Usz := usz γs szv], whose reading of [UM3] is the projection that
     throws the leftover away. *)
  Lemma wp_kshm_child_pipe_paid_at
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp ge : nat)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cp Cr Bp : iProp Σ)
      (* the two [wait(0)]s' law, relayed (design app-pipe SS4.3w,
         purchase 3) -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
      (Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    (* THE PARSE'S PAYER: the round's lend, whole, across [parsecmd] *)
    Cp -∗
    □ (app_taint -∗ Qc (-1)) -∗
    □ (Cp -∗ ukn_pay N (-1)) -∗
    (* ...AND THE ARM'S LEND, born out of it at the parse's return *)
    (Cp ={⊤}=∗ Cr) -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    (* the wait credential and the law that spends it, twice *)
    Wr -∗
    UkShPipe.ush_wait0_law N Wr Pw -∗
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    (* SS4.3u (lane SH-PIPE-ROUND-9): the fork tails' credential is
       [RcR γp ∗ Cx γp] and not [Cx γp] -- the family's RIGHT chain is
       ONE resource, shared by design between cat's output (mode 1) and
       a [panic("fork")] (mode 3), and the arm's single up-front split
       cannot give it to both.  It does not have to: the right child's
       lend is in sh's hand at BOTH tails and was being dropped.  This
       file only forwards the law. *)
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) args)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) [(S (S gp), ge)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       (* the two forks returned a pid (purchase 3): a -1 panics and never
          reaches 0xea -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       Cx γp -∗
       (* ...and the wait credential, unspent *)
       Wr -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hs38
           HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2.
    exact (wp_kshm_child_pipe_paid_at_sz h m dw dv s0 szv cwdv len f args
             gp ge ld st0 st1 Sc n R RcL RcR Rk Cx Bx Qc Cp Cr Bp
             (usz γs szv) Wr Pw
             Hm01 Hm23 ltac:(iIntros "_ $") Hs1 Hpq Htoks Hpos Htlen
             Hs0 Hs64 Hs38 HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2).
  Qed.

  (* =================================================================== *)
  (*  S1  THE PAID CHILD, at the pipe shape                               *)
  (* =================================================================== *)
  Lemma wp_kshm_child_pipe_paid
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp ge : nat)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr Bp : iProp Σ)
      (* the two [wait(0)]s' law, relayed (design app-pipe SS4.3w,
         purchase 3) -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
      (Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (* fd 2 IS THE CONSOLE: a PAID write names the row it goes out on *)
    UkSh.ush_fd2p ld ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    Cr -∗
    □ (app_taint -∗ Qc (-1)) -∗
    (* the lend pays the parse's own exits, whole (no [ukn_pay] for free) *)
    □ (Cr -∗ ukn_pay N (-1)) -∗
    (* the arm's own split -- the arm chooses between the [pipe(2)] tail
       and the forks, so nothing is split before it *)
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    (* the wait credential and the law that spends it, twice *)
    Wr -∗
    UkShPipe.ush_wait0_law N Wr Pw -∗
    (* ---- THE THREE DIAGNOSTICS, PAID ---- *)
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    (* SS4.3u (lane SH-PIPE-ROUND-9): the fork tails' credential is
       [RcR γp ∗ Cx γp] and not [Cx γp] -- the family's RIGHT chain is
       ONE resource, shared by design between cat's output (mode 1) and
       a [panic("fork")] (mode 3), and the arm's single up-front split
       cannot give it to both.  It does not have to: the right child's
       lend is in sh's hand at BOTH tails and was being dropped.  This
       file only forwards the law. *)
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (* ---- THE LEFT CHILD: fd 1 is the pipe's WRITE end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) args)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE RIGHT CHILD: fd 0 is the pipe's READ end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) [(S (S gp), ge)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* ---- THE PARENT, at 0xea, with the forks' borrowed credential ---- *)
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       (* the two forks returned a pid (purchase 3): a -1 panics and never
          reaches 0xea -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       Cx γp -∗
       (* ...and the wait credential, unspent *)
       Wr -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hs38
           HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hsz Hstd Hcwd Hch
             HM Hcr #Hkw #Hpxw Hsplit Hpipe HWr #Hwl #Hlawp #Hbp #Hlawf #Hbx
             Hrun HcL HcR Hpar".
    iApply (wp_kshm_child_pipe_paid_at h m dw dv s0 szv cwdv len f args gp ge
              ld st0 st1 Sc n R RcL RcR Rk Cx Bx Qc Cr Cr Bp Wr Pw
              Hm01 Hm23 Hs1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hs38
              HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2
              with "Hcode Hjt Hpcode Hpro Hline Hws Hsy Hsz Hstd Hcwd Hch
                    HM Hcr Hkw Hpxw [] Hsplit Hpipe HWr Hwl Hlawp Hbp Hlawf
                    Hbx Hrun HcL HcR Hpar").
    iIntros "H". by iModIntro.
  Qed.

  (* =================================================================== *)
  (*  S2  ...AND AT THE LINE                                              *)
  (*                                                                     *)
  (*  [UkShPipeRound.wp_kshm_child_pipe_line]'s twin: the buffer at [s0]  *)
  (*  holds `echo w1 ... wn | cat\n' and the two children come out at     *)
  (*  [runcmd]'s entry with the pipe's two ends at fd 1 and fd 0.         *)
  (* =================================================================== *)
  Corollary wp_kshm_child_pipe_paid_line
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (ws : list (list (bv 8)))
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr Bp : iProp Σ)
      (* the two [wait(0)]s' law, relayed (design app-pipe SS4.3w,
         purchase 3) -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
      (Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    UkShPipeRound.ushq_line_at ws f 0%nat len ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    Cr -∗
    □ (app_taint -∗ Qc (-1)) -∗
    □ (Cr -∗ ukn_pay N (-1)) -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    (* the wait credential and the law that spends it, twice *)
    Wr -∗
    UkShPipe.ush_wait0_law N Wr Pw -∗
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    (* SS4.3u (lane SH-PIPE-ROUND-9): the fork tails' credential is
       [RcR γp ∗ Cx γp] and not [Cx γp] -- the family's RIGHT chain is
       ONE resource, shared by design between cat's output (mode 1) and
       a [panic("fork")] (mode 3), and the arm's single up-front split
       cannot give it to both.  It does not have to: the right child's
       lend is in sh's hand at BOTH tails and was being dropped.  This
       file only forwards the law. *)
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat) (wl_toks ws))) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat)
                   [((length (wl_body ws) + 3)%nat,
                     (length (wl_body ws) + 3 + 3)%nat)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       (* the two forks returned a pid (purchase 3): a -1 panics and never
          reaches 0xea -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       Cx γp -∗
       (* ...and the wait credential, unspent *)
       Wr -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hline Hs0 Hs64 Hs38 HQc Hl0 Hl1 Hne0 Hne1
           Hnp0 Hnp1 Hfd2.
    pose proof (UkShPipeRound.ushq_line_is_of_at ws f 0%nat len Hline) as Hli.
    destruct (UkShPipeLex.ush_line_toks_holds_pipe ws UkShPipeLex.ushq_cat f
                0%nat len Hli) as (Hq & Ht & Hpos & Htlen & _).
    assert (Ef : (fun j : nat => f (0 + j)%nat) = f) by reflexivity.
    rewrite Ef in Hq, Ht.
    rewrite UkShPipeLex.ushq_cat_len in Hq.
    assert (Ege : (length (wl_body ws) + 3)%nat
                  = S (S (length (wl_body ws) + 1))) by lia.
    rewrite Ege in Hq |- *.
    exact (wp_kshm_child_pipe_paid h m dw dv s0 szv cwdv len f (wl_toks ws)
             (length (wl_body ws) + 1)%nat
             (S (S (length (wl_body ws) + 1)) + 3)%nat
             ld st0 st1 Sc n R RcL RcR Rk Cx Bx Qc Cr Bp Wr Pw
             Hm01 Hm23 Hs1 Hq Ht Hpos Htlen Hs0 Hs64 Hs38
             HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2).
  Qed.

  (* =================================================================== *)
  (*  S3  ...AND THE TWO-PAYER LINE COROLLARY (lane SH-PIPE-ROUND-8): the  *)
  (*      round's own entry point.  [Cp] is what sh's fork lent ([Wcf I    *)
  (*      3]), which pays the parse's exits PURELY; [Cr] is the two-writer *)
  (*      family it becomes at the parse's return.                         *)
  (* =================================================================== *)
  Corollary wp_kshm_child_pipe_paid_line_at
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (ws : list (list (bv 8)))
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cp Cr Bp : iProp Σ)
      (* the two [wait(0)]s' law, relayed (design app-pipe SS4.3w,
         purchase 3) -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
      (Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    UkShPipeRound.ushq_line_at ws f 0%nat len ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    Cp -∗
    □ (app_taint -∗ Qc (-1)) -∗
    □ (Cp -∗ ukn_pay N (-1)) -∗
    (Cp ={⊤}=∗ Cr) -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    (* the wait credential and the law that spends it, twice *)
    Wr -∗
    UkShPipe.ush_wait0_law N Wr Pw -∗
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    (* SS4.3u (lane SH-PIPE-ROUND-9): the fork tails' credential is
       [RcR γp ∗ Cx γp] and not [Cx γp] -- the family's RIGHT chain is
       ONE resource, shared by design between cat's output (mode 1) and
       a [panic("fork")] (mode 3), and the arm's single up-front split
       cannot give it to both.  It does not have to: the right child's
       lend is in sh's hand at BOTH tails and was being dropped.  This
       file only forwards the law. *)
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat) (wl_toks ws))) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat)
                   [((length (wl_body ws) + 3)%nat,
                     (length (wl_body ws) + 3 + 3)%nat)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       (* the two forks returned a pid (purchase 3): a -1 panics and never
          reaches 0xea -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       Cx γp -∗
       (* ...and the wait credential, unspent *)
       Wr -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hline Hs0 Hs64 Hs38 HQc Hl0 Hl1 Hne0 Hne1
           Hnp0 Hnp1 Hfd2.
    pose proof (UkShPipeRound.ushq_line_is_of_at ws f 0%nat len Hline) as Hli.
    destruct (UkShPipeLex.ush_line_toks_holds_pipe ws UkShPipeLex.ushq_cat f
                0%nat len Hli) as (Hq & Ht & Hpos & Htlen & _).
    assert (Ef : (fun j : nat => f (0 + j)%nat) = f) by reflexivity.
    rewrite Ef in Hq, Ht.
    rewrite UkShPipeLex.ushq_cat_len in Hq.
    assert (Ege : (length (wl_body ws) + 3)%nat
                  = S (S (length (wl_body ws) + 1))) by lia.
    rewrite Ege in Hq |- *.
    exact (wp_kshm_child_pipe_paid_at h m dw dv s0 szv cwdv len f (wl_toks ws)
             (length (wl_body ws) + 1)%nat
             (S (S (length (wl_body ws) + 1)) + 3)%nat
             ld st0 st1 Sc n R RcL RcR Rk Cx Bx Qc Cp Cr Bp Wr Pw
             Hm01 Hm23 Hs1 Hq Ht Hpos Htlen Hs0 Hs64 Hs38
             HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2).
  Qed.


  (* =================================================================== *)
  (*  S4  ...AND THE ROUND'S OWN ENTRY POINT (lane SH-PIPE-ROUND-12): S3  *)
  (*      with the break read off the parse's leftover.  See              *)
  (*      [wp_kshm_child_pipe_paid_at_sz] for why the landed shape        *)
  (*      cannot be met at any real allocator state.                      *)
  (* =================================================================== *)
  Corollary wp_kshm_child_pipe_paid_line_at_sz
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (ws : list (list (bv 8)))
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cp Cr Bp : iProp Σ)
      (* WHERE THE BREAK COMES FROM (see [wp_kshm_child_pipe_paid_at_sz]) *)
      (Usz : iProp Σ)
      (* the two [wait(0)]s' law, relayed (design app-pipe SS4.3w,
         purchase 3) -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
      (Wr : iProp Σ)
      (Pw : mword 64 -> gset gname -> gset gname -> iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    (⊢ UM3 -∗ Usz -∗ usz γs szv) ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    UkShPipeRound.ushq_line_at ws f 0%nat len ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    Usz -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    Cp -∗
    □ (app_taint -∗ Qc (-1)) -∗
    □ (Cp -∗ ukn_pay N (-1)) -∗
    (Cp ={⊤}=∗ Cr) -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    (* the wait credential and the law that spends it, twice *)
    Wr -∗
    UkShPipe.ush_wait0_law N Wr Pw -∗
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    (* SS4.3u (lane SH-PIPE-ROUND-9): the fork tails' credential is
       [RcR γp ∗ Cx γp] and not [Cx γp] -- the family's RIGHT chain is
       ONE resource, shared by design between cat's output (mode 1) and
       a [panic("fork")] (mode 3), and the arm's single up-front split
       cannot give it to both.  It does not have to: the right child's
       lend is in sh's hand at BOTH tails and was being dropped.  This
       file only forwards the law. *)
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (RcR γp ∗ Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat) (wl_toks ws))) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat)
                   [((length (wl_body ws) + 3)%nat,
                     (length (wl_body ws) + 3 + 3)%nat)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       (* the two forks returned a pid (purchase 3): a -1 panics and never
          reaches 0xea -- see [UkShPipe.wp_kshr_pipe_arm_g] *)
       ⌜ r1 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       ⌜ r2 <> (mword_of_int (-1) : mword 64) ⌝ -∗
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       Pw rw1 S2 S3 -∗
       Pw rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       Cx γp -∗
       (* ...and the wait credential, unspent *)
       Wr -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hszof Hs1 Hline Hs0 Hs64 Hs38 HQc Hl0 Hl1 Hne0 Hne1
           Hnp0 Hnp1 Hfd2.
    pose proof (UkShPipeRound.ushq_line_is_of_at ws f 0%nat len Hline) as Hli.
    destruct (UkShPipeLex.ush_line_toks_holds_pipe ws UkShPipeLex.ushq_cat f
                0%nat len Hli) as (Hq & Ht & Hpos & Htlen & _).
    assert (Ef : (fun j : nat => f (0 + j)%nat) = f) by reflexivity.
    rewrite Ef in Hq, Ht.
    rewrite UkShPipeLex.ushq_cat_len in Hq.
    assert (Ege : (length (wl_body ws) + 3)%nat
                  = S (S (length (wl_body ws) + 1))) by lia.
    rewrite Ege in Hq |- *.
    exact (wp_kshm_child_pipe_paid_at_sz h m dw dv s0 szv cwdv len f
             (wl_toks ws)
             (length (wl_body ws) + 1)%nat
             (S (S (length (wl_body ws) + 1)) + 3)%nat
             ld st0 st1 Sc n R RcL RcR Rk Cx Bx Qc Cp Cr Bp Usz Wr Pw
             Hm01 Hm23 Hszof Hs1 Hq Ht Hpos Htlen Hs0 Hs64 Hs38
             HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2).
  Qed.


End UShPipeChild.
