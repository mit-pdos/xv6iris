(* ===================================================================== *)
(* UkShMain.v -- sh's MAIN BODY, SH LANE STAGE 6: the walk from the       *)
(* blank-line test to the fork, and the two lanes it joins.               *)
(*                                                                        *)
(* [UkSh.v] walks main down to 0x956 and hands the rest over as an        *)
(* abstract continuation, [UkSh.ush_rest]; [UkShParse.v] proves the       *)
(* parser and [UkShRun.v]/[UkShDiag.v] the command-tree runner.  Nothing   *)
(* joined them, and joining them is what this file is: the twenty-odd     *)
(* instructions between the blank-line test and the loop head, plus the   *)
(* SEAM between what the parser BUILDS and what the runner CONSUMES.      *)
(*                                                                        *)
(* WHAT MAIN'S BODY IS, at the pcs the catalog names:                     *)
(*                                                                        *)
(*   0x956  bne s5,a5   -> 0x908      buf[k] != 'c'                        *)
(*   0x95a  lbu a5,1(s1)                                                   *)
(*   0x95e  bne s3,a5   -> 0x908      buf[k+1] != 'd'                      *)
(*   0x962  lbu a5,2(s1)                                                   *)
(*   0x966  bne s6,a5   -> 0x908      buf[k+2] != ' '                      *)
(*   0x96a..0x99a                     the cd builtin                       *)
(*   0x908  jal fork1                                                      *)
(*   0x90c  c.beqz a0   -> 0x99c      the CHILD                            *)
(*   0x90e  c.li a0,0 ; 0x910 jal wait  ; falls into 0x914, the loop head  *)
(*   0x99c  c.mv a0,s1 ; 0x99e jal parsecmd ; 0x9a2 jal runcmd             *)
(*                                                                        *)
(* THE SEAM.  [UkShParse.ushp_tree] owns its node at [DfracOwn 1] and     *)
(* names the argument vector as INDEX PAIRS into the line;                *)
(* [UkShRun.ush_cmd] reads it at [DfracDiscarded] and names it as         *)
(* [UserHeap.uarg]s -- pointer, length, bytes.  The NUL-CUT the parser    *)
(* publishes is exactly what turns one into the other: a token (i,j)      *)
(* becomes the string at [s0+i] of length [j-i], whose terminator is the  *)
(* zero [nulterminate] wrote at [j].  The conversion DISCARDS, which is   *)
(* what makes the tree persistent and so what lets it cross the fork as a *)
(* [UkFork.Forkable] payload.                                             *)
(*                                                                        *)
(* THE SCOPE, and both halves of it are premises of the theorem rather    *)
(* than assumptions about the kernel:                                     *)
(*                                                                        *)
(*   the line is one the LEXER ACCEPTS -- no symbol byte, fewer than      *)
(*     MAXARGS tokens -- which is stage 4's own scope, and                *)
(*   the line is not a [cd] COMMAND.  sh's cd arm prints its failure with *)
(*     [fprintf] and RETURNS to the loop, so its '%s' argument is the     *)
(*     line buffer, which the loop rewrites; [UkShDiag.shd_str] is        *)
(*     persistent-only, so printing a mutable buffer needs that predicate *)
(*     re-cut at a dfrac.  Until then the arm is REFUTED from the premise *)
(*     at its three byte tests rather than walked.                        *)
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
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import RefParse.
Require Import RefParseBridge.  (* [ref_parsecmd_nosym]: the symbol-free line at the reference *)
Require Import UkShRedirs.      (* [ushp_malloc_chain] *)
Require Import UkShSeam.        (* THE SEAM AND THE CHILD, once *)
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require UkShCmdalloc.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShMain.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.

  (* the four ghost names a program proof runs at, as every file in the
     lane binds them *)
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_triv]). *)
  Context `{Hpay : !ukn_const N}.
  (* THE CHILD'S PAYLOAD IS NOT TRIVIAL ANY MORE (lane IO-LEAF, M3b).
     There used to be a second class here, [UkRun.ukn_triv N], because the
     generic exec supply [UkRun.uxsup] is the exec bundle at the trivial
     payload and this file walks the process sh FORKED.  A child that has
     to ECHO A LINE cannot be at the trivial payload: what it owes its
     parent is the era's credential at the alternative it took.  So the
     two things the class was used for -- the free exit row and the exec
     supply -- are PREMISES of the two lemmas below, at whatever payload
     sh chose for its child. *)
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
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

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

(*ALIASES-BEGIN*)
  (* ---- the parser's files, at this file's own ghost names ---- *)
(*ALIASES-END*)


  (* ===================================================================== *)
  (* §1-§3 MOVED DOWN (lane user-once A3a).  Persisting a run, the           *)
  (* separation fact, [ush_args] and the EXEC conversion                     *)
  (* [ush_cmd_of_ushp_gen] live in [UkShSeam.v] now, where they are the      *)
  (* EXEC case of the seam stated over the WHOLE tree                        *)
  (* ([UkShSeam.ush_cmd_of_ushp_tree]); every name is re-exported below the  *)
  (* section under its landed spelling, so [UkShMain.ush_args] and its       *)
  (* siblings resolve unchanged.                                             *)
  (* ===================================================================== *)

  (* ---- the landed statement, which is that conversion at STAGE 4's cut -- *)
  Lemma ush_cmd_of_ushp (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat)
      (s0 p : Z) (len : nat) (f : nat -> bv 8)
      (toks : list (nat * nat)) :
    ushp_tokens len f 0 toks ->
    ushp_no_symbols len f ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    urun N h m pc avail -∗
    ushp_tree N s0 p (UshpExec toks) -∗
    ubytes γd s0 (S len) (ushp_nulfold toks (ushp_ext len f)) ==∗
    urun N h m pc avail ∗
    ush_cmd γd p (UExec (ush_args s0 (ushp_nulfold toks (ushp_ext len f)) toks)).
  Proof using .
    intros Htoks Hns Hnn Hlen31 Hs0 Hs0hi.
    iIntros "Hrun Hnode Hline".
    iMod (UkShSeam.ubytes_persist γd s0 (S len) _ with "Hline") as "#Hline".
    iApply (UkShSeam.ush_cmd_of_ushp_gen N h m pc avail s0 p len
              (ushp_nulfold toks (ushp_ext len f)) toks
              ltac:(intros i tk Hi;
                    destruct (ushp_tokens_in len f 0%nat toks Htoks
                                ltac:(lia) i tk Hi) as [Hlo Hhi];
                    split; lia)
              ltac:(intros i tk Hi;
                    exact (UkShParseCmd.ushp_nulfold_hit toks
                             (ushp_ext len f) i tk Hi))
              ltac:(intros i tk Hi j Hj;
                    destruct (ushp_tokens_in len f 0%nat toks Htoks
                                ltac:(lia) i tk Hi) as [Hlo Hhi];
                    rewrite (UkShSeam.ushp_nulfold_miss toks (ushp_ext len f)
                               (fst tk + j)%nat
                               ltac:(intros q t Hq;
                                     exact (UkShSeam.ushp_tokens_gap len f 0%nat toks
                                              Hns Htoks ltac:(lia)
                                              i tk Hi q t Hq
                                              (fst tk + j)%nat ltac:(lia))));
                    rewrite /ushp_ext
                      (bool_decide_eq_true_2 ((fst tk + j) < len)%nat
                         ltac:(lia));
                    apply Hnn; lia)
              Hlen31 Hs0 Hs0hi
              with "Hrun Hnode Hline").
  Qed.



  (* ===================================================================== *)
  (* §4 THE CHILD: parse the line, then run the tree.                       *)
  (*                                                                       *)
  (*   0x99c  c.mv a0,s1        the line                                    *)
  (*   0x99e  jal  ra,parsecmd  -> the node                                 *)
  (*   0x9a2  jal  ra,runcmd    -> exec, and never back                     *)
  (*                                                                       *)
  (* This is where the theorem's content is: the tree [runcmd] walks is the *)
  (* one [parsecmd] just built out of THIS line, so the [exec] at the       *)
  (* bottom of [runcmd]'s EXEC arm names the line's own words.              *)
  (* ===================================================================== *)
  Lemma wp_kshm_child (UMalloc : iProp Σ) (szv : Z)
      (Hmalloc : forall (h : CpuId) (m : regfile) (nbytes : Z) (avail : nat),
         m !!! Regidx (mword_of_int 10) = mword_of_int nbytes ->
         0 < nbytes -> nbytes <= 65504 ->
         shp_code γt -∗
         UMalloc -∗
         urun N h m (mword_of_int ShSyms.malloc) (10 + avail) -∗
         (∀ (h' : CpuId) (m' : regfile),
            ⌜ ucallee_saved m m' ⌝ -∗
            (⌜ m' !!! Regidx (mword_of_int 10) = (mword_of_int 0 : mword 64) ⌝
             ∨ (∃ (p : Z) (g : nat -> bv 8),
                  ⌜ m' !!! Regidx (mword_of_int 10) = mword_of_int p ⌝ ∗
                  ⌜ 0 < p /\ p mod 16 = 0 /\ p + nbytes < 2 ^ 38 ⌝ ∗
                  ubytes γd p (Z.to_nat nbytes) g ∗ usz γs szv)) -∗
            urun N h' m' (ret_pc (m !!! Regidx (mword_of_int 1)))
              (10 + avail) -∗
            mWP (Loop : expr riscv_lang)) -∗
         mWP (Loop : expr riscv_lang))
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (ld : list fdstate) (n : nat) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0 toks ->
    (length toks < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (* THE PAYLOAD IS FREE AT THIS RECORD (lane IO-LEAF, M3b): a premise
       now, where it used to be [UkRun.ukn_pay_free_of_triv] off the
       file's own class. *)
    (⊢ ukn_pay N (-1)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    (* the exec deposit's supplier -- [UkRun.uxsup_at] at THIS record's
       own payload, see [UkShRun.wp_kshr_runcmd]: this walk reaches
       runcmd's EXEC arm, and its forks run at the same payload. *)
    uxsup_at (ukn_pay N) -∗
    (* ...and how a killer pays for a forked child (lane IO-LEAF, M3b) *)
    □ (app_taint -∗ ukn_pay N (-1)) -∗
    shp_code γt -∗ shp_rodata γt -∗ ush_jtab γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd_any γcwd -∗
    (* ...and its children set, index-free: runcmd's LIST and BACK arms
       fork, and the set moves at each ([UkShRun.wp_kshr_fork1]) *)
    UserChildren.uch_any γch -∗ UMalloc -∗
    (* the out-of-memory law at this record's own payload: the parser's
       [cmdalloc] panics ([UkShCmdalloc.ushp_oom]; upstream d66e41c) *)
    UkShCmdalloc.ushp_oom N (ukn_pay N (-1)) (8 + (UkShDiag.ush_Dg + n) - 2) -∗
    urun N h m (mword_of_int 0x99c)
      (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hns Htoks Htlen Hs0 Hs64 Hs38 Hpx.
    iIntros "#Hdp #Hcode #Hxs #Hkw #Hpcode #Hpro #Hjt Hline Hws Hsy Hstd Hcwd
             Hch HM #Hpxw Hrun".
    (* the line's own bytes are non-NUL, which is what makes the line the
       reference parses: [ref_parsecmd] at the symbol-free line is ONE EXEC
       node over exactly these tokens (RefParseBridge.ref_parsecmd_nosym) *)
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    (* THE CAPABILITY IS WEAKENED HERE, AND NOWHERE ELSE (lane SH-MALLOC-3).
       This lemma's [Hmalloc] is the UNBOUNDED contract, unchanged -- it is
       what [UkShMalloc]'s adapter proves and what every caller supplies --
       while the parser asks for [UkShParse.ushp_malloc_ty_le N 168], ONE
       link of the chain [UkShRedirs.ushp_malloc_chain]. *)
    iApply (UkShSeam.wp_ref_child_exec N Hpsok_free UMalloc (usz γs szv)
              h m dw dv s0 len f toks szv ld n
              Hs1 (RefParse.ref_sym_scope_nosym len f Hns)
              (RefParseBridge.ref_parsecmd_nosym len f toks Hnn0 Hns Htoks Htlen)
              (UkShRedirs.ushp_malloc_chain_1 N UMalloc (usz γs szv)
                 (UkShParse.ushp_malloc_ty_le_mono N 65504 168 UMalloc
                    (usz γs szv) ltac:(lia)
                    (UkShParse.ushp_malloc_ty_le_top N UMalloc (usz γs szv)
                       Hmalloc)))
              Hs0 Hs64 Hs38 Hpx
              with "Hdp Hcode Hxs Hkw Hpcode Hpro Hjt Hline Hws Hsy Hstd Hcwd
                    Hch HM [] Hpxw Hrun").
    iIntros "$".
  Qed.

  (* ===================================================================== *)
  (* §5 THE CHILD, WITH THE ALLOCATOR DISCHARGED.                           *)
  (*                                                                        *)
  (* [wp_kshm_child] is stated over an ABSTRACT allocator, because that is  *)
  (* what stage 4's contract is cut at; this is it at the CONCRETE one --   *)
  (* [UkShMalloc.ushm_fresh], the [freep] cell holding zero, the sixteen    *)
  (* bytes of [base] and the break -- so the only thing left on the far     *)
  (* side of the seam is the one place stage 3 had to name an assumption    *)
  (* -- and since lane SELF-KILL's step 5 there is NOTHING there: the        *)
  (* allocator's failure arm is carried all the way up and ends in the       *)
  (* child's own death at [memset]'s first store, so the assumption          *)
  (* [ushm_sbrk_never_fails] is gone.                                        *)
  (*                                                                        *)
  (* THE BREAK MOVES ACROSS THE PARSE, and the statement says where to:     *)
  (* the run [runcmd] and [exec] see is at [sz + 65536], because the        *)
  (* allocator asked the kernel for sixteen pages on the way through.       *)
  (* ===================================================================== *)
  Lemma wp_kshm_child_alloc
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (sz : Z) (ld : list fdstate) (n : nat) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0 toks ->
    (length toks < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (* the break is above [base] (0x2088, the last sixteen bytes of the
       image) and page-aligned, which [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (* THE PAYLOAD IS FREE AT THIS RECORD (lane IO-LEAF, M3b): a premise
       now, where it used to be [UkRun.ukn_pay_free_of_triv] off the
       file's own class. *)
    (⊢ ukn_pay N (-1)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    (* the exec deposit's supplier -- [UkRun.uxsup_at] at THIS record's
       own payload, see [UkShRun.wp_kshr_runcmd]: this walk reaches
       runcmd's EXEC arm, and its forks run at the same payload. *)
    uxsup_at (ukn_pay N) -∗
    (* ...and how a killer pays for a forked child (lane IO-LEAF, M3b) *)
    □ (app_taint -∗ ukn_pay N (-1)) -∗
    shp_code γt -∗ shp_rodata γt -∗ ush_jtab γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd_any γcwd -∗
    UserChildren.uch_any γch -∗
    UkShMalloc.ushm_fresh N sz -∗
    (* the out-of-memory law at this record's own payload: the parser's
       [cmdalloc] panics ([UkShCmdalloc.ushp_oom]; upstream d66e41c) *)
    UkShCmdalloc.ushp_oom N (ukn_pay N (-1)) (8 + (UkShDiag.ush_Dg + n) - 2) -∗
    urun N h m (mword_of_int 0x99c)
      (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free.
    intros Hs1 Hns Htoks Htlen Hs0 Hs64 Hs38 Hszlo Hszal Hszok Hpx.
    iIntros "#Hdp #Hcode #Hxs #Hkw #Hpcode #Hpro #Hjt Hline Hws Hsy Hstd Hcwd
             Hch HM #Hpxw Hrun".
    iApply (wp_kshm_child (UkShMalloc.ushm_fresh N sz) (sz + 65536)
              (UkShMalloc.ushm_malloc_ok_holds N Hpsok_free sz
                 Hszlo Hszal Hszok)
              h m dw dv s0 len f toks ld n
              Hs1 Hns Htoks Htlen Hs0 Hs64 Hs38 Hpx
              with "Hdp Hcode Hxs Hkw Hpcode Hpro Hjt Hline Hws Hsy Hstd Hcwd
                    Hch HM Hpxw Hrun").
  Qed.

End UkShMain.

(* ===================================================================== *)
(* THE MOVED VOCABULARY, RE-EXPORTED (lane user-once A3a).  These lived    *)
(* in SS1-SS3 of this file and are [UkShSeam.v]'s now; every consumer      *)
(* names them [UkShMain.X], so each keeps that name as an abbreviation of  *)
(* the one constant -- the same device [UkShPipeNode.ushp_pipe_node] uses. *)
(* ===================================================================== *)
Notation ubytes_persist := UkShSeam.ubytes_persist.
Notation uword_persist := UkShSeam.uword_persist.
Notation ustr_persist := UkShSeam.ustr_persist.
Notation ushp_toklen_end := UkShSeam.ushp_toklen_end.
Notation ushp_nulfold_miss := UkShSeam.ushp_nulfold_miss.
Notation ushp_tokens_gap := UkShSeam.ushp_tokens_gap.
Notation ubytesq_sub := UkShSeam.ubytesq_sub.
Notation ubytesq_at := UkShSeam.ubytesq_at.
Notation ush_args := UkShSeam.ush_args.
Notation ush_args_length := UkShSeam.ush_args_length.
Notation ush_args_lookup := UkShSeam.ush_args_lookup.
Notation urun_ubytes_bnd := UkShSeam.urun_ubytes_bnd.
Notation ush_cmd_of_ushp_gen := UkShSeam.ush_cmd_of_ushp_gen.
