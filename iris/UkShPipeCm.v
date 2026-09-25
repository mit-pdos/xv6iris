(* ===================================================================== *)
(* UkShPipeCm.v -- parsepipe's TURN, lane SH-PARSE-PIPE part 2            *)
(* (design/app-pipe.md SS5.1: parsepipe is walked at the '>' shape         *)
(* ([UkShRedirCm.wp_kshp_parsepipe_gt]) and must turn ONCE for the pipe.)  *)
(*                                                                        *)
(* The landed walk is this one with the guard REFUTED: on a symbol-free or *)
(* a redirect line the peek for '|' answers 0 and [parsepipe] returns its  *)
(* sub-command unchanged.  The pipe line is the first line that makes it   *)
(* TURN, and the turn is THIRTEEN instructions -- 0x6c2..0x6e0 -- which    *)
(* rejoin the landed walk's own tail at 0x6b0, so the prologue, the guard, *)
(* the tail and the epilogue are all the landed text.                     *)
(*                                                                        *)
(* WHAT IS DISCHARGED HERE, of the turn's three calls:                     *)
(*                                                                        *)
(*   0x6ca [gettoken] -- [UkShPipeTok.wp_kshp_gettoken_syms] at the '|':   *)
(*     it answers 124 and leaves the cursor at [S (S gp)], the right       *)
(*     command's first byte, with BOTH out-parameters NULL (which is       *)
(*     [UkShParseTok.ushp_cell]'s left disjunct, free).                    *)
(*   0x6d2 [parsepipe] -- THE RECURSION, and it is the LANDED symbol-free  *)
(*     walk on the line's own suffix ([UkShPipeRight.                       *)
(*     wp_kshp_parsepipe_right]).  Nothing about the right-hand side of a  *)
(*     pipe needed a new walk.                                            *)
(*                                                                        *)
(* WHAT IS A CALL PREMISE (SH-REDIR's [ush_open_call] shape, §1):          *)
(*                                                                        *)
(*   0x698 [parseexec] -- the LEFT command's parse.  It is a RE-STATEMENT  *)
(*     of the landed walks at [UkShParseSym.ushs_toks] (the loop's exit is *)
(*     [UkShPipeEx.wp_kshp_pex_bar] and its last [parseredirs] is          *)
(*     [UkShPipePr.wp_kshp_parseredirs_miss], both landed by this lane);   *)
(*     this lane did not finish the ~2,400 lines of re-statement itself.   *)
(*   0x6da [pipecmd] -- its 48 instructions are in NO catalog              *)
(*     (`skipfunc pipecmd` in tools/ucode_shp.txt) and cannot be put in    *)
(*     one from this worktree: [make gen-ucode] shells out to [coqc] and   *)
(*     needs a BUILT iris/, which the lane's local tree has not got.  See  *)
(*     the lane's findings for exactly what it needs.                      *)
(*                                                                        *)
(* So the arm compiles TODAY, before either of those exists, and the lane  *)
(* that lands them instantiates two premises and nothing else.             *)
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
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShRedirCmd.
Require Import UkShRedirPr.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Require Import UkShPipeLex.
Require Import UkShPipeTok.
Require Import UkShPipeParse.
Require Import UkShPipeEx.
Require Import UkShPipeCmd.
Require Import UkShParseCmd.
Require Import UkShPipePex.
Require Import UkShPipeRight.
Require Import UkShPipesLex.  (* [ushq_barw]: a bar read locally (lane PIPES-C3) *)

Section UkShPipeCm.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
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

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).


(*ALIASES-BEGIN*)
  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_exec_pre := (UkShParse.ushp_exec_pre N).
  Local Notation ushp_exec_pre_at := (UkShParse.ushp_exec_pre_at N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_slots_cap := (UkShParse.ushp_slots_cap N).
  Local Notation ushp_slots_upd := (UkShParse.ushp_slots_upd N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_pipe_node := (UkShPipeParse.ushp_pipe_node N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_ustr_bytes := (UkShParseCmd.ushp_ustr_bytes N).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  (* THREE allocator capabilities, chained: a pipe line makes THREE
     constructor calls (an [execcmd] per side of the '|' and one
     [pipecmd]), and the chain is funded -- UkShPipeSeam's
     [ushq_malloc_le_third] is the third link and no chain had to be
     extended.  UM0 -> UM1 is the LEFT [execcmd] (inside premise (i)),
     UM1 -> UM2 the RIGHT one (inside the recursion, so it is a real
     Hypothesis here), UM2 -> UM3 [pipecmd] (inside premise (ii)). *)
  Context (UM0 UM1 UM2 UM3 : iProp Σ).
  Hypothesis ushp_malloc_ok12 : ushp_malloc_ty UM1 UM2.
  (* ===================================================================== *)
  (* §1 THE TWO CALL PREMISES                                               *)
  (*                                                                        *)
  (* SH-REDIR's [ush_open_call] shape: the call stated as the CONCLUSION a   *)
  (* walk of it would have, so the arm compiles before the walk exists and   *)
  (* the lane that lands the walk instantiates the premise and nothing else. *)
  (* ===================================================================== *)

  (* (i) the LEFT command's [parseexec].  Its answer is the exec node for
     the line's OWN token list [args], and it leaves the cursor AT the '|'
     -- which is exactly what the guard's peek then reads. *)
  Definition ushq_pex_left (dq dw dv : dfrac) (ps s0 : Z) (len gp : nat)
      (f : nat -> bv 8) (args : list (nat * nat)) (Pex : iProp Σ)
      (av : nat) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (rpc : mword 64),
       ⌜ m !!! Regidx a0_idx = mword_of_int ps ⌝ -∗
       ⌜ m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
       (* the RETURN PC as a parameter, so the caller hands the equation in
          and the answer arrives at the pc it wants *)
       ⌜ ret_pc (m !!! Regidx ra_idx) = rpc ⌝ -∗
       shp_code γt -∗
       shp_rodata γt -∗
       uword γd ps (mword_of_int s0) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UM0 -∗
       □ (Pex -∗ ukn_pay N (-1)) -∗
       Pex -∗
       urun N h m (mword_of_int ShSyms.parseexec) av -∗
       (∀ pl : Z,
          ⌜ pl + 168 < Z64 ⌝ -∗
          ushp_exec_at s0 pl args -∗
          uword γd ps (mword_of_int (s0 + Z.of_nat gp)) -∗
          ustr γd dq s0 len f -∗
          ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
          ustr γd dv ushp_symbols 7 ushp_sym_f -∗
            ∀ (h' : CpuId) (m' : regfile),
              ⌜ ucallee_saved m m' ⌝ -∗
              ⌜ m' !!! Regidx a0_idx = mword_of_int pl ⌝ -∗
              UM1 -∗
              Pex -∗
              urun N h' m' rpc av -∗
              mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...AT ANY CURSOR (lane PIPES-C3).  The same call with the cursor word
     [w0] a parameter: a pipeline's stages after the first are parsed from
     the cursor the previous bar's gettoken left.  [ushq_pex_left] is this
     at the line's first byte ([ushq_pex_left_to_at]). *)
  Definition ushq_pex_left_at (dq dw dv : dfrac) (ps s0 : Z) (w0 : mword 64)
      (len gp : nat) (f : nat -> bv 8) (args : list (nat * nat))
      (Pex : iProp Σ) (av : nat) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (rpc : mword 64),
       ⌜ m !!! Regidx a0_idx = mword_of_int ps ⌝ -∗
       ⌜ m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
       ⌜ ret_pc (m !!! Regidx ra_idx) = rpc ⌝ -∗
       shp_code γt -∗
       shp_rodata γt -∗
       uword γd ps w0 -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UM0 -∗
       □ (Pex -∗ ukn_pay N (-1)) -∗
       Pex -∗
       urun N h m (mword_of_int ShSyms.parseexec) av -∗
       (∀ pl : Z,
          ⌜ pl + 168 < Z64 ⌝ -∗
          ushp_exec_at s0 pl args -∗
          uword γd ps (mword_of_int (s0 + Z.of_nat gp)) -∗
          ustr γd dq s0 len f -∗
          ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
          ustr γd dv ushp_symbols 7 ushp_sym_f -∗
            ∀ (h' : CpuId) (m' : regfile),
              ⌜ ucallee_saved m m' ⌝ -∗
              ⌜ m' !!! Regidx a0_idx = mword_of_int pl ⌝ -∗
              UM1 -∗
              Pex -∗
              urun N h' m' rpc av -∗
              mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Lemma ushq_pex_left_to_at {Pex : iProp Σ} (dq dw dv : dfrac) (ps s0 : Z)
      (len gp : nat) (f : nat -> bv 8) (args : list (nat * nat)) (av : nat) :
    ushq_pex_left dq dw dv ps s0 len gp f args Pex av -∗
    ushq_pex_left_at dq dw dv ps s0 (mword_of_int s0) len gp f args Pex av.
  Proof using . rewrite /ushq_pex_left /ushq_pex_left_at. iIntros "H". iExact "H". Qed.

  (* (iii) THE RECURSION (lane PIPES-C3): [parsepipe] on the rest of the
     line, from the cursor gettoken leaves after the bar, answering an
     ABSTRACT tree [Tr] at the node it returns.  The landed turn discharges
     it with the symbol-free walk (one word after the bar); a pipeline of
     more stages discharges it with the turn itself, one bar shorter
     ([UkShPipesParse.wp_kshp_parsepipe_bars]). *)
  Definition ushq_rec_call (dq dw dv : dfrac) (ps s0 : Z) (len c : nat)
      (f : nat -> bv 8) (Tr : Z -> iProp Σ) (Pex : iProp Σ) (av : nat)
      : iProp Σ :=
    (∀ (h : CpuId) (m : regfile),
       ⌜ m !!! Regidx a0_idx = mword_of_int ps ⌝ -∗
       ⌜ m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
       shp_code γt -∗
       shp_rodata γt -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat c)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UM1 -∗
       □ (Pex -∗ ukn_pay N (-1)) -∗
       Pex -∗
       urun N h m (mword_of_int ShSyms.parsepipe) av -∗
       (∀ q : Z,
          Tr q -∗
          uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
          ustr γd dq s0 len f -∗
          ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
          ustr γd dv ushp_symbols 7 ushp_sym_f -∗
            ∀ (h' : CpuId) (m' : regfile),
              ⌜ ucallee_saved m m' ⌝ -∗
              ⌜ m' !!! Regidx a0_idx = mword_of_int q ⌝ -∗
              UM2 -∗
              Pex -∗
              urun N h' m' (ret_pc (m !!! Regidx ra_idx)) av -∗
              mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* (ii) [pipecmd] (0x260).  Stated as [UkShRedirCmd.wp_kshp_redircmd_n] is:
     the two subtrees ride through in an ABSTRACT [Sub], because the node
     and its children are relayed SEPARATELY all the way up to the parser
     theorem (SH-PARSE-2's shape fact), and what comes back is the node with
     both child pointers NAMED. *)
  Definition ushq_pipecmd_call (Pex : iProp Σ) (av : nat) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (pl pr : Z) (rpc : mword 64)
       (Sub : iProp Σ),
       ⌜ m !!! Regidx a0_idx = mword_of_int pl ⌝ -∗
       ⌜ m !!! Regidx a1_idx = mword_of_int pr ⌝ -∗
       ⌜ ret_pc (m !!! Regidx ra_idx) = rpc ⌝ -∗
       shp_code γt -∗
       UM2 -∗
       □ (Pex -∗ ukn_pay N (-1)) -∗
       Pex -∗
       Sub -∗
       urun N h m (mword_of_int 0x260) av -∗
       (∀ (h' : CpuId) (m' : regfile) (t : Z),
          ⌜ ucallee_saved m m' ⌝ -∗
          ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
          ushp_pipe_node t pl pr -∗
          Sub -∗
          UM3 -∗
          Pex -∗
          urun N h' m' rpc av -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* NON-VACUITY, for premise (i).  A premise nobody can satisfy is worse
     than no premise (durable-notes, Vacuity), so here is [ushq_pex_left]'s
     SHAPE inhabited: at [gp := len] -- a line whose parse runs to the end
     -- it is exactly the LANDED [UkShParseExec.wp_kshp_parseexec]'s
     conclusion, so the pipe line's instance differs from a proved one only
     in WHERE the cursor stops.  (Premise (ii) cannot be witnessed this way:
     nothing in the tree fetches an instruction of [pipecmd] -- see the
     lane's findings.) *)
  Lemma ushq_pex_left_nosym {Pex : iProp Σ} (dq dw dv : dfrac)
      (ps s0 : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0%nat args ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    ⊢ ushq_pex_left dq dw dv ps s0 len len f args Pex (16 + (24 + nn)).
  Proof using .
    intros Hmal01 Hns Htoks Hlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros (h m rpc) "%Ha0 %Ha1 %Erpc #Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hrun Hcont".
    iApply (UkShParseExec.wp_kshp_parseexec N UM0 UM1 Hmal01 h m dq dw dv
              ps s0 len 0%nat f (mword_of_int s0) args nn
              Ha0 Ha1 ltac:(lia)
              ltac:(rewrite Z.add_0_r; reflexivity)
              Hns Htoks Hlen Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay Hrun").
    iIntros (q) "%Hqsz Hnode Hcur Hstr Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM1 Hpay Hrun".
    rewrite Erpc.
    iApply ("Hcont" $! q with "[] Hnode Hcur Hstr Hws Hsy [] [] HM1 Hpay Hrun").
    - iPureIntro. exact Hqsz.
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  (* PREMISE (ii) IS DISCHARGED: [pipecmd]'s twenty-seven instructions are
     walked ([UkShPipeCmd.wp_kshp_pipecmd]) now that its catalog row exists,
     so the turn below needs only premise (i).  The budget arithmetic is the
     only thing to say: the walk asks for [6 + (10 + nn')] and the turn's
     call site has [16 + (24 + (8 + nn))], so [nn' := 32 + nn] and the two
     are the same [48 + nn]. *)
  Lemma ushq_pipecmd_call_holds {Pex : iProp Σ} (nn : nat) :
    ushp_malloc_ty UM2 UM3 ->
    ⊢ ushq_pipecmd_call Pex (16 + (24 + (8 + nn))).
  Proof using .
    intro Hmal23.
    iIntros (h m pl pr rpc Sub) "%Ha0 %Ha1 %Erpc #Hcode HM #Hpx Hpay Hsub Hrun Hcont".
    rewrite <- Erpc.
    iApply (UkShPipeCmd.wp_kshp_pipecmd N UM2 UM3 Hmal23 h m pl pr Sub
              (32 + nn) Ha0 Ha1
              with "Hcode HM Hpx Hpay Hsub Hrun").
    iIntros (h' m' t) "%Hcs %Ha0' %Htb Hnode Hsub HM' Hpay Hrun".
    iApply ("Hcont" $! h' m' t with "[] [] Hnode Hsub HM' Hpay Hrun").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  (* ===================================================================== *)
  (* §2 THE TURN                                                            *)
  (*                                                                        *)
  (* [UkShRedirCm.wp_kshp_parsepipe_gt] is this walk with the guard REFUTED. *)
  (* The pipe line is the first line that makes it TURN, and the turn is     *)
  (* THIRTEEN instructions, 0x6c2..0x6e0, rejoining the landed walk's own    *)
  (* tail at 0x6b0:                                                         *)
  (*                                                                        *)
  (*   0x6c2 c.li a3,0 ; 0x6c4 c.li a2,0 ; 0x6c6 c.mv a1,s1                 *)
  (*   0x6c8 c.mv a0,s4 ; 0x6ca jal gettoken   -- consumes the '|'          *)
  (*   0x6ce c.mv a1,s1 ; 0x6d0 c.mv a0,s4                                  *)
  (*   0x6d2 jal parsepipe                     -- THE RECURSION             *)
  (*   0x6d6 c.mv a1,a0 ; 0x6d8 c.mv a0,s3                                  *)
  (*   0x6da jal pipecmd                        -- the PIPE node            *)
  (*   0x6de c.mv s3,a0 ; 0x6e0 c.j 6b0                                     *)
  (*                                                                        *)
  (* Two of its three calls are DISCHARGED here: [gettoken] by              *)
  (* [UkShPipeTok.wp_kshp_gettoken_syms] (it answers 124 and advances the    *)
  (* cursor to [S (S gp)]) and the RECURSION by                              *)
  (* [UkShPipeRight.wp_kshp_parsepipe_right] (the landed symbol-free walk    *)
  (* on the line's own suffix).  The other two are CALL PREMISES in          *)
  (* SH-REDIR's [ush_open_call] style: the LEFT [parseexec], whose walk is   *)
  (* a re-statement this lane did not finish, and [pipecmd], whose 48        *)
  (* instructions are in NO catalog (`skipfunc pipecmd`) and cannot be put   *)
  (* in one from this worktree -- see the lane's findings.                   *)
  (* ===================================================================== *)

  (* THE TURN AT A BAR READ LOCALLY, THE RECURSION A PREMISE (lane
     PIPES-C3).  The walk below at [UkShPipesLex.ushq_barw], from ANY
     cursor [w0], with the recursive [parsepipe] as premise (iii) answering
     an abstract [Tr]: the step of [UkShPipesParse.wp_kshp_parsepipe_bars],
     whose induction hypothesis discharges (iii).  The landed
     [wp_kshp_parsepipe_bar] after it is the one-bar line's instance, (iii)
     discharged by the symbol-free walk. *)
  Lemma wp_kshp_parsepipe_bar_g {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (w0 : mword 64) (len gp : nat)
      (f : nat -> bv 8) (args : list (nat * nat)) (Tr : Z -> iProp Σ)
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_barw len f gp ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    (* (i) the LEFT command's parse, as a CALL PREMISE *)
    ushq_pex_left_at dq dw dv ps s0 w0 len gp f args Pex
      (16 + (24 + (8 + nn))) -∗
    (* (iii) the RECURSION, as a CALL PREMISE *)
    ushq_rec_call dq dw dv ps s0 len (S (S gp)) f Tr Pex
      (16 + (24 + (8 + nn))) -∗
    (* (ii) [pipecmd], as a CALL PREMISE *)
    ushq_pipecmd_call Pex (16 + (24 + (8 + nn))) -∗
    urun N h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + (8 + nn)))) -∗
    (∀ t pl pr : Z,
       ⌜ pl + 168 < Z64 ⌝ -∗
       ushp_pipe_node t pl pr -∗
       ushp_exec_at s0 pl args -∗
       Tr pr -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + (8 + nn)))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hpq Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hleft Hrec Hpipec Hrun
             Hcont".
    rewrite shpp_parsepipe.
    (* the cursor the LEFT parse leaves is AT the '|', so the guard's own
       blank scan does not move and the peek answers at [gp] itself *)
    assert (Egp0 : (gp + ushp_skipws (len - gp) gp f)%nat = gp)
      by (rewrite (ushq_skipws_at_barw len f gp (len - gp)%nat Hpq); lia).
    assert (Hgplt : (gp < len)%nat) by exact (ushq_barw_lt len f gp Hpq).
    assert (Hgple : (gp <= len)%nat) by lia.
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x682..0x690  the prologue ---- *)
    iApply (wp_kshp_frame_pro 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] 0x682
              (fun i : nat => match i with
                              | 0%nat => 0x684 | 1%nat => 0x686
                              | 2%nat => 0x688 | 3%nat => 0x68a
                              | 4%nat => 0x68c | 5%nat => 0x68e
                              | _ => 0x690 end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (16 + (24 + (8 + nn))) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_682 with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_684 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_686 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_688 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68e with "Hcode") | done ]. }
    { iApply (uis_shp_690 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (mA := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (HmA : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    mA !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (HspA : mA !!! Regidx csp_rs1 = spn).
    { rewrite (HmA csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x692  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv N h1 mA (mword_of_int 0x692) s2_idx a0_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_692 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> mA).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m2 !!! Regidx q = mA !!! Regidx q)
      by (intros q Hq; exact (upd_ne mA (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x694  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0x694) s4_idx a0_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_694 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x696  c.mv s1,a1 ---- *)
    iApply (wp_uk_cmv N h3 m3 (mword_of_int 0x696) s1_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (HmA a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_696 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x698  jal 590 <parseexec> ---- *)
    iApply (wp_uk_jal N h4 m4 (mword_of_int 0x698)
              (mword_of_int 2096888 : mword 21) ra_idx
              (mword_of_int 0x590) (mword_of_int 0x69c) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_698 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x69c : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret5 : ret_pc (m5 !!! Regidx ra_idx) = mword_of_int 0x69c).
    { rewrite (upd_eq m4 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x69c : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (HmA a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_5 : m5 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate))
              (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (HmA a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    rewrite <- shpp_parseexec.
    (* ---- 0x698  jal 590 <parseexec> -- THE LEFT COMMAND, premise (i) -- *)
    iApply ("Hleft" $! h5 m5 (mword_of_int 0x69c)
              with "[] [] [] Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay Hrun").
    { iPureIntro. exact Ha0_5. }
    { iPureIntro. exact Ha1_5. }
    { iPureIntro. exact Eret5. }
    iIntros (pl) "%Hplsz Hnodel Hcur Hstr Hws Hsy".
    iIntros (h6 m6) "%Hcs56 %Ha0_6 HM1 Hpay Hrun".
    (* ---- 0x69c  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv N h6 m6 (mword_of_int 0x69c) s3_idx a0_idx
              (mword_of_int pl) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6; symmetry; exact (ushp_mv_val pl))
              with "[] Hrun").
    { iApply (uis_shp_69c with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int pl : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x69e/0x6a2  the pipe table ---- *)
    iApply (wp_uk_auipc N h7 m7 (mword_of_int 0x69e)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x169e) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_69e with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0x169e : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_8 : m8 !!! Regidx a2_idx = mword_of_int 0x169e)
      by exact (upd_eq m7 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x169e : mword 64))).
    iApply (wp_uk_addi N h8 m8 (mword_of_int 0x6a2)
              (mword_of_int 3218 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_pipe) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_8; unfold ushp_T_pipe;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6a2 with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_pipe : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x6a6/0x6a8  peek's two other arguments ---- *)
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate))
              (Hm8 s1_idx ltac:(vm_compute; discriminate))
              (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hcs56 s1_idx ltac:(vm_compute; reflexivity))
              (Hm5 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hcs56 s2_idx ltac:(vm_compute; reflexivity))
              (Hm5 s2_idx ltac:(vm_compute; discriminate))
              (Hm4 s2_idx ltac:(vm_compute; discriminate))
              (Hm3 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s2_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    iApply (wp_uk_cmv N h9 m9 (mword_of_int 0x6a6) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6a6 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h10 m10 (mword_of_int 0x6a8) a0_idx
              s2_idx (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6a8 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x6aa  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h11 m11 (mword_of_int 0x6aa)
              (mword_of_int 2096542 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x6ae) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6aa with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x6ae : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x6ae).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x6ae : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_12 : m12 !!! Regidx a2_idx = mword_of_int ushp_T_pipe).
    { rewrite (Hm12 a2_idx ltac:(vm_compute; discriminate))
              (Hm11 a2_idx ltac:(vm_compute; discriminate))
              (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_pipe : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h12 m12 dq dw true DfracDiscarded ps s0
              ushp_T_pipe len gp 1 f (ushp_lit ushp_T_pipe)
              (mword_of_int (s0 + Z.of_nat gp)) (30 + (8 + nn))
              Ha0_12 Ha1_12 Ha2_12 Hgple eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_pipe; lia)
              ltac:(unfold ushp_T_pipe, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_pipe 1 DfracDiscarded
                ushp_T_pipe_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h13 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12 Egp0.
    rewrite Egp0 in Ha0_13.
    (* THE GUARD TURNS.  peek's table at 0x1330 is the one byte '|', and the
       byte at the cursor IS it -- the one fact no landed walk could produce
       ([UkShPipeEx.ushq_peek_pipe_hit_pipe]). *)
    rewrite (ushp_peek_pipe_hit len f gp (ushq_barw_lt len f gp Hpq)
               (ushq_barw_bar len f gp Hpq)) in Ha0_13.
    (* ---- the register file the turn starts from ---- *)
    assert (Hs1_13 : m13 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_9. }
    assert (Hs4_13 : m13 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hcs1213 s4_idx ltac:(vm_compute; reflexivity))
              (Hm12 s4_idx ltac:(vm_compute; discriminate))
              (Hm11 s4_idx ltac:(vm_compute; discriminate))
              (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hcs56 s4_idx ltac:(vm_compute; reflexivity))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int pl).
    { rewrite (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m6 (Regidx s3_idx)
               (regval_into_reg (mword_of_int pl : mword 64))). }
    (* ---- 0x6ae  c.bnez a0 -- TAKEN: there IS a pipe ---- *)
    iApply (wp_uk_cbnez N h13 m13 (mword_of_int 0x6ae)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx true (mword_of_int 0x6c2) (16 + (24 + (8 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6ae with "Hcode"). }
    iIntros (h14) "Hrun".
    (* ---- 0x6c2  c.li a3,0 ---- *)
    iApply (wp_uk_cli N h14 m13 (mword_of_int 0x6c2)
              (mword_of_int 0 : mword 6) a3_idx (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_6c2 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c2 2). iIntros (h15) "Hrun".
    set (q1 := <[Regidx a3_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m13).
    assert (Hq1 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                    q1 !!! Regidx r = m13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m13 (Regidx a3_idx) (Regidx r) _ Hr)).
    assert (Ha3_q1 : q1 !!! Regidx a3_idx = mword_of_int 0).
    { rewrite (upd_eq m13 (Regidx a3_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x6c4  c.li a2,0 ---- *)
    iApply (wp_uk_cli N h15 q1 (mword_of_int 0x6c4)
              (mword_of_int 0 : mword 6) a2_idx (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_6c4 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c4 2). iIntros (h16) "Hrun".
    set (q2 := <[Regidx a2_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> q1).
    assert (Hq2 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    q2 !!! Regidx r = q1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q1 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_q2 : q2 !!! Regidx a2_idx = mword_of_int 0).
    { rewrite (upd_eq q1 (Regidx a2_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x6c6  c.mv a1,s1  --  es ---- *)
    iApply (wp_uk_cmv N h16 q2 (mword_of_int 0x6c6) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hq2 s1_idx ltac:(vm_compute; discriminate))
                      (Hq1 s1_idx ltac:(vm_compute; discriminate)) Hs1_13;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6c6 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c6 2). iIntros (h17) "Hrun".
    set (q3 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> q2).
    assert (Hq3 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    q3 !!! Regidx r = q2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q2 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x6c8  c.mv a0,s4  --  &s ---- *)
    iApply (wp_uk_cmv N h17 q3 (mword_of_int 0x6c8) a0_idx s4_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hq3 s4_idx ltac:(vm_compute; discriminate))
                      (Hq2 s4_idx ltac:(vm_compute; discriminate))
                      (Hq1 s4_idx ltac:(vm_compute; discriminate)) Hs4_13;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6c8 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c8 2). iIntros (h18) "Hrun".
    set (q4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> q3).
    assert (Hq4 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    q4 !!! Regidx r = q3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q3 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x6ca  jal 310 <gettoken> -- consumes the '|' ---- *)
    iApply (wp_uk_jal N h18 q4 (mword_of_int 0x6ca)
              (mword_of_int 2096198 : mword 21) ra_idx
              (mword_of_int 0x310) (mword_of_int 0x6ce) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6ca with "Hcode"). }
    iIntros (h19) "Hrun".
    set (q5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6ce : mword 64)]> q4).
    assert (Hq5 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    q5 !!! Regidx r = q4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q4 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Eret_g : ret_pc (q5 !!! Regidx ra_idx) = mword_of_int 0x6ce);
      [ rewrite (upd_eq q4 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x6ce : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_q5 : q5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hq5 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq q3 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_q5 : q5 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hq5 a1_idx ltac:(vm_compute; discriminate))
              (Hq4 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq q2 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_q5 : q5 !!! Regidx a2_idx = mword_of_int 0).
    { rewrite (Hq5 a2_idx ltac:(vm_compute; discriminate))
              (Hq4 a2_idx ltac:(vm_compute; discriminate))
              (Hq3 a2_idx ltac:(vm_compute; discriminate)). exact Ha2_q2. }
    assert (Ha3_q5 : q5 !!! Regidx a3_idx = mword_of_int 0).
    { rewrite (Hq5 a3_idx ltac:(vm_compute; discriminate))
              (Hq4 a3_idx ltac:(vm_compute; discriminate))
              (Hq3 a3_idx ltac:(vm_compute; discriminate))
              (Hq2 a3_idx ltac:(vm_compute; discriminate)). exact Ha3_q1. }
    rewrite <- shpp_gettoken.
    (* gettoken at EITHER symbol byte: here it is the '|', it answers 124,
       and it leaves the cursor at [S (S gp)] -- the right command's first
       byte ([UkShPipeLex.ushq_gettok_fin_bar]).  Both out-parameters are
       NULL, which is [UkShParseTok.ushp_cell]'s left disjunct. *)
    iApply (UkShPipeTok.wp_kshp_gettoken_syms N h19 q5 dq dw dv ps 0 0 s0
              len gp f (mword_of_int (s0 + Z.of_nat gp))
              (mword_of_int 0) (mword_of_int 0) (38 + nn)
              Ha0_q5 Ha1_q5 Ha2_q5 Ha3_q5 Hgple eq_refl
              (ushq_barw_sym_ok len f gp Hpq) Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hcur [] [] Hstr Hws Hsy Hrun").
    { iLeft. iPureIntro. reflexivity. }
    { iLeft. iPureIntro. reflexivity. }
    iIntros "Hcur _ _ Hstr Hws Hsy" (h20 g1) "%Hcsg %Ha0_g Hrun".
    rewrite Eret_g.
    (* the cursor gettoken leaves: [S (S gp)], the right command's first
       byte ([UkShPipeLex.ushq_gettok_fin_bar]) *)
    rewrite Egp0.
    rewrite (ushq_gettok_fin_barw len f gp Hpq).
    (* ---- 0x6ce  c.mv a1,s1 ---- *)
    assert (Hs1_g1 : g1 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hcsg s1_idx ltac:(vm_compute; reflexivity))
              (Hq5 s1_idx ltac:(vm_compute; discriminate))
              (Hq4 s1_idx ltac:(vm_compute; discriminate))
              (Hq3 s1_idx ltac:(vm_compute; discriminate))
              (Hq2 s1_idx ltac:(vm_compute; discriminate))
              (Hq1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_13. }
    assert (Hs4_g1 : g1 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hcsg s4_idx ltac:(vm_compute; reflexivity))
              (Hq5 s4_idx ltac:(vm_compute; discriminate))
              (Hq4 s4_idx ltac:(vm_compute; discriminate))
              (Hq3 s4_idx ltac:(vm_compute; discriminate))
              (Hq2 s4_idx ltac:(vm_compute; discriminate))
              (Hq1 s4_idx ltac:(vm_compute; discriminate)). exact Hs4_13. }
    iApply (wp_uk_cmv N h20 g1 (mword_of_int 0x6ce) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_g1; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6ce with "Hcode"). }
    rewrite (ushp_pc_step 0x6ce 2). iIntros (h21) "Hrun".
    set (g2 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> g1).
    assert (Hg2 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    g2 !!! Regidx r = g1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g1 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x6d0  c.mv a0,s4 ---- *)
    iApply (wp_uk_cmv N h21 g2 (mword_of_int 0x6d0) a0_idx s4_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hg2 s4_idx ltac:(vm_compute; discriminate))
                      Hs4_g1; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6d0 with "Hcode"). }
    rewrite (ushp_pc_step 0x6d0 2). iIntros (h22) "Hrun".
    set (g3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> g2).
    assert (Hg3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    g3 !!! Regidx r = g2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g2 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x6d2  jal 682 <parsepipe> -- THE RECURSION ---- *)
    iApply (wp_uk_jal N h22 g3 (mword_of_int 0x6d2)
              (mword_of_int 2097072 : mword 21) ra_idx
              (mword_of_int 0x682) (mword_of_int 0x6d6) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6d2 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (g4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6d6 : mword 64)]> g3).
    assert (Hg4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    g4 !!! Regidx r = g3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g3 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Eret_r : ret_pc (g4 !!! Regidx ra_idx) = mword_of_int 0x6d6);
      [ rewrite (upd_eq g3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x6d6 : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_g4 : g4 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hg4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq g2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_g4 : g4 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hg4 a1_idx ltac:(vm_compute; discriminate))
              (Hg3 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq g1 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    rewrite <- shpp_parsepipe.
    (* the recursive call is premise (iii) *)
    iApply ("Hrec" $! h23 g4 with "[] [] Hcode Hro Hcur Hstr Hws Hsy HM1 Hpx
                                    Hpay Hrun").
    { iPureIntro. exact Ha0_g4. }
    { iPureIntro. exact Ha1_g4. }
    iIntros (pr) "Hnoder Hcur Hstr Hws Hsy".
    iIntros (h24 r1) "%Hcsr %Ha0_r HM2 Hpay Hrun".
    rewrite Eret_r.
    (* ---- 0x6d6  c.mv a1,a0  --  the RIGHT node ---- *)
    iApply (wp_uk_cmv N h24 r1 (mword_of_int 0x6d6) a1_idx a0_idx
              (mword_of_int pr) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_r; symmetry; exact (ushp_mv_val pr))
              with "[] Hrun").
    { iApply (uis_shp_6d6 with "Hcode"). }
    rewrite (ushp_pc_step 0x6d6 2). iIntros (h25) "Hrun".
    set (r2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int pr : mword 64)]> r1).
    assert (Hr2 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    r2 !!! Regidx r = r1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r1 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x6d8  c.mv a0,s3  --  the LEFT node ---- *)
    assert (Hs3_r1 : r1 !!! Regidx s3_idx = mword_of_int pl).
    { rewrite (Hcsr s3_idx ltac:(vm_compute; reflexivity))
              (Hg4 s3_idx ltac:(vm_compute; discriminate))
              (Hg3 s3_idx ltac:(vm_compute; discriminate))
              (Hg2 s3_idx ltac:(vm_compute; discriminate))
              (Hcsg s3_idx ltac:(vm_compute; reflexivity))
              (Hq5 s3_idx ltac:(vm_compute; discriminate))
              (Hq4 s3_idx ltac:(vm_compute; discriminate))
              (Hq3 s3_idx ltac:(vm_compute; discriminate))
              (Hq2 s3_idx ltac:(vm_compute; discriminate))
              (Hq1 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_13. }
    iApply (wp_uk_cmv N h25 r2 (mword_of_int 0x6d8) a0_idx s3_idx
              (mword_of_int pl) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr2 s3_idx ltac:(vm_compute; discriminate))
                      Hs3_r1; symmetry; exact (ushp_mv_val pl))
              with "[] Hrun").
    { iApply (uis_shp_6d8 with "Hcode"). }
    rewrite (ushp_pc_step 0x6d8 2). iIntros (h26) "Hrun".
    set (r3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int pl : mword 64)]> r2).
    assert (Hr3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    r3 !!! Regidx r = r2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r2 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x6da  jal 260 <pipecmd> -- premise (ii) ---- *)
    iApply (wp_uk_jal N h26 r3 (mword_of_int 0x6da)
              (mword_of_int 2096006 : mword 21) ra_idx
              (mword_of_int 0x260) (mword_of_int 0x6de) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6da with "Hcode"). }
    iIntros (h27) "Hrun".
    set (r4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6de : mword 64)]> r3).
    assert (Hr4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    r4 !!! Regidx r = r3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r3 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Eret_c : ret_pc (r4 !!! Regidx ra_idx) = mword_of_int 0x6de);
      [ rewrite (upd_eq r3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x6de : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_r4 : r4 !!! Regidx a0_idx = mword_of_int pl).
    { rewrite (Hr4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int pl : mword 64))). }
    assert (Ha1_r4 : r4 !!! Regidx a1_idx = mword_of_int pr).
    { rewrite (Hr4 a1_idx ltac:(vm_compute; discriminate))
              (Hr3 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r1 (Regidx a1_idx)
               (regval_into_reg (mword_of_int pr : mword 64))). }
    iApply ("Hpipec" $! h27 r4 pl pr (mword_of_int 0x6de)
              (ushp_exec_at s0 pl args ∗ Tr pr)%I
              with "[] [] [] Hcode HM2 Hpx Hpay [Hnodel Hnoder] Hrun").
    { iPureIntro. exact Ha0_r4. }
    { iPureIntro. exact Ha1_r4. }
    { iPureIntro. exact Eret_c. }
    { iSplitL "Hnodel"; [ iExact "Hnodel" | iExact "Hnoder" ]. }
    iIntros (h28 q11 t) "%Hcsc %Ha0_c Hpnode [Hnodel Hnoder] HM3 Hpay Hrun".
    (* ---- 0x6de  c.mv s3,a0  --  the PIPE node becomes the answer ---- *)
    iApply (wp_uk_cmv N h28 q11 (mword_of_int 0x6de) s3_idx a0_idx
              (mword_of_int t) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_c; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_6de with "Hcode"). }
    rewrite (ushp_pc_step 0x6de 2). iIntros (h29) "Hrun".
    set (q12 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int t : mword 64)]> q11).
    assert (Hq12 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
                     q12 !!! Regidx r = q11 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q11 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hs3_q12 : q12 !!! Regidx s3_idx = mword_of_int t)
      by exact (upd_eq q11 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int t : mword 64))).
    (* ---- 0x6e0  c.j 6b0 -- into the landed walk's own tail ---- *)
    iApply (wp_uk_cj N h29 q12 (mword_of_int 0x6e0)
              (mword_of_int 2024 : mword 11) (mword_of_int 0x6b0)
              (16 + (24 + (8 + nn)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6e0 with "Hcode"). }
    iIntros (h30) "Hrun".
    (* ---- 0x6b0  c.mv a0,s3 -- the landed walk's own tail, unchanged ---- *)
    iApply (wp_uk_cmv N h30 q12 (mword_of_int 0x6b0) a0_idx
              s3_idx (mword_of_int t) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_q12; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_6b0 with "Hcode"). }
    iIntros (h31) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> q12).
    assert (Hme : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    me !!! Regidx r = q12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q12 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* the whole body, as one preservation fact.  Every one of the three
       calls preserves the callee-saved set, so the chain is the a-register
       writes plus s3 (which the turn overwrites with the PIPE node). *)
    assert (Hkeep : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              me !!! Regidx r = m !!! Regidx r).
    { intros r Hr Hsp Hx0 Hx1 Hx2 Hx3 Hx4.
      rewrite (Hme r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq12 r Hx3)
              (Hcsc r Hr)
              (Hr4 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr3 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr2 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hcsr r Hr)
              (Hg4 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hg3 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hg2 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hcsg r Hr)
              (Hq5 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq4 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq3 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq2 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq1 r (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)))
              (Hcs1213 r Hr)
              (Hm12 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm11 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm10 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm9 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm8 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm7 r Hx3) (Hcs56 r Hr)
              (Hm5 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm4 r Hx1) (Hm3 r Hx4) (Hm2 r Hx2) (HmA r Hx0) (Hm1 r Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hq12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcsc csp_rs1 ltac:(vm_compute; reflexivity))
              (Hr4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hr3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hr2 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcsr csp_rs1 ltac:(vm_compute; reflexivity))
              (Hg4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hg3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hg2 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcsg csp_rs1 ltac:(vm_compute; reflexivity))
              (Hq5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq2 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq1 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs56 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact HspA. }
    (* ---- 0x6b2..0x6c0  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x6b2 | 1%nat => 0x6b4
                              | 2%nat => 0x6b6 | 3%nat => 0x6b8
                              | 4%nat => 0x6ba | 5%nat => 0x6bc
                              | _ => 0x6be end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 6)) vals
              (16 + (24 + (8 + nn))) h31 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_6b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6bc with "Hcode") | done ]. }
    { iApply (uis_shp_6be with "Hcode"). }
    { iApply (uis_shp_6c0 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! t pl pr
              with "[] Hpnode Hnodel Hnoder Hcur Hstr Hws Hsy [] [] HM3 Hpay Hrun").
    - iPureIntro. exact Hplsz.
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6) eq_refl)
                 (Hmiss 5%nat s4_idx (mword_of_int 0 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq q12 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int t : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  Lemma wp_kshp_parsepipe_bar {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len gp ge : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_pipe len f gp ge ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int s0) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    (* (i) the LEFT command's parse, as a CALL PREMISE *)
    ushq_pex_left dq dw dv ps s0 len gp f args Pex (16 + (24 + (8 + nn))) -∗
    (* (ii) [pipecmd], as a CALL PREMISE *)
    ushq_pipecmd_call Pex (16 + (24 + (8 + nn))) -∗
    urun N h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + (8 + nn)))) -∗
    (∀ t pl pr : Z,
       ⌜ pl + 168 < Z64 ⌝ -∗
       ⌜ pr + 168 < Z64 ⌝ -∗
       ushp_pipe_node t pl pr -∗
       ushp_exec_at s0 pl args -∗
       ushp_exec_at s0 pr [(S (S gp), ge)] -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + (8 + nn)))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok12.
    intros Ha0 Ha1 Hpq Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "Hcode Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hleft Hpipec Hrun Hcont".
    iApply (wp_kshp_parsepipe_bar_g h m dq dw dv ps s0 (mword_of_int s0)
              len gp f args
              (fun pr : Z => ⌜ pr + 168 < Z64 ⌝ ∗ ushp_exec_at s0 pr [(S (S gp), ge)])%I
              nn Ha0 Ha1 (ushq_barw_of_pipe len f gp ge Hpq)
              Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay [Hleft] [] Hpipec Hrun
                    [Hcont]").
    - iApply (ushq_pex_left_to_at with "Hleft").
    - (* (iii): the landed symbol-free walk on the line's suffix *)
      iIntros (h1 m1) "%Ha0' %Ha1' Hcode' Hro' Hcur Hstr Hws Hsy HM1 _ Hpay
                       Hrun Hk".
      iApply (UkShPipeRight.wp_kshp_parsepipe_right N UM1 UM2 ushp_malloc_ok12
                h1 m1 dq dw dv ps s0 len gp ge f (2 + nn)
                Ha0' Ha1' Hpq Hs0 Hs64 Hps0 Hps8 Hpssz
                with "Hcode' Hro' Hcur Hstr Hws Hsy HM1 Hpx Hpay Hrun").
      iIntros (pr) "%Hprsz Hnoder".
      iApply ("Hk" $! pr with "[Hnoder]").
      iSplitR; [ iPureIntro; exact Hprsz | iExact "Hnoder" ].
    - iIntros (t pl pr) "%Hplsz Hpnode Hnodel [%Hprsz Hnoder]".
      iApply ("Hcont" $! t pl pr with "[] [] Hpnode Hnodel Hnoder").
      + iPureIntro. exact Hplsz.
      + iPureIntro. exact Hprsz.
  Qed.

  (* ===================================================================== *)
  (* §3 BOTH PREMISES DISCHARGED: THE TURN, CLOSED                          *)
  (*                                                                        *)
  (* Premise (i) is [UkShPipePex.wp_kshp_parseexec_bar] (the LEFT command's  *)
  (* parse, the re-statement this lane finished) and premise (ii) is         *)
  (* [UkShPipeCmd.wp_kshp_pipecmd] (the constructor, walkable now that its   *)
  (* catalog row exists).  So [parsepipe] at the pipe shape is a closed      *)
  (* walk: the only things it still takes are the LINE, the two allocator    *)
  (* links, and the exit payload every parser walk takes.                    *)
  (* ===================================================================== *)

  Lemma ushq_pex_left_holds {Pex : iProp Σ} (dq dw dv : dfrac)
      (ps s0 : Z) (len gp ge : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    ⊢ ushq_pex_left dq dw dv ps s0 len gp f args Pex
        (16 + (24 + (8 + nn))).
  Proof using .
    intros Hmal01 Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros (h m rpc)
      "%Ha0 %Ha1 %Erpc #Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hrun Hcont".
    rewrite <- Erpc.
    iApply (UkShPipePex.wp_kshp_parseexec_bar N UM0 UM1 Hmal01 h m dq dw dv
              ps s0 len 0%nat f (mword_of_int s0) args gp ge nn
              Ha0 Ha1 ltac:(lia) ltac:(f_equal; lia)
              Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay Hrun").
    iIntros (pl) "%Hplsz Hnodel Hcur Hstr Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM1 Hpay Hrun".
    iApply ("Hcont" $! pl with "[] Hnodel Hcur Hstr Hws Hsy [] [] HM1 Hpay Hrun").
    - iPureIntro. exact Hplsz.
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  (* THE TURN, with nothing left to instantiate. *)
  Corollary wp_kshp_parsepipe_bar_closed {Pex : iProp Σ} (h : CpuId)
      (m : regfile) (dq dw dv : dfrac) (ps s0 : Z) (len gp ge : nat)
      (f : nat -> bv 8) (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int s0) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + (8 + nn)))) -∗
    (∀ t pl pr : Z,
       ⌜ pl + 168 < Z64 ⌝ -∗
       ⌜ pr + 168 < Z64 ⌝ -∗
       ushp_pipe_node t pl pr -∗
       ushp_exec_at s0 pl args -∗
       ushp_exec_at s0 pr [(S (S gp), ge)] -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + (8 + nn)))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok12.
    intros Hmal01 Hmal23 Ha0 Ha1 Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hrun Hcont".
    iApply (wp_kshp_parsepipe_bar h m dq dw dv ps s0 len gp ge f args nn
              Ha0 Ha1 Hpq Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay [] [] Hrun Hcont").
    - iApply (ushq_pex_left_holds dq dw dv ps s0 len gp ge f args nn
                Hmal01 Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz).
    - iApply (ushq_pipecmd_call_holds nn Hmal23).
  Qed.


  (* ===================================================================== *)
  (* parseline ON THE PIPE LINE                                             *)
  (*                                                                        *)
  (* One-line body: call [parsepipe], then peek for '&' and for ';' and     *)
  (* find neither.  [UkShRedirCm.wp_kshp_parseline_gt] is this walk on the  *)
  (* redirect line and the two peeks are refuted there for the same reason   *)
  (* as here -- the CURSOR has run out, [parsepipe] having consumed the      *)
  (* whole line -- so those two lines of proof text are untouched.  What     *)
  (* changes is the call ([wp_kshp_parsepipe_bar_closed], premise-free) and  *)
  (* the answer: THREE nodes relayed separately (the PIPE node and one EXEC  *)
  (* node per side) where the redirect line relays two.                     *)
  (* ===================================================================== *)

  (* THE WALK WITH ITS [parsepipe] CALL A PREMISE (lane PIPES-C3b): the
     call's answer is an abstract resource [PT t] at the returned tree
     pointer, and its allocator links [UA]/[UB] are the caller's.  The
     landed [wp_kshp_parseline_bar] below is this at the one-bar turn;
     [UkShPipesCmd] instantiates it at [UkShPipesParse.
     wp_kshp_parsepipe_bars], any number of bars. *)
  Lemma wp_kshp_parseline_bar_g {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len : nat) (f : nat -> bv 8)
      (UA UB : iProp Σ) (PT : Z -> iProp Σ) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int s0) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UA -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parseline)
      (6 + (6 + (16 + (24 + (8 + nn))))) -∗
    (* the [parsepipe] call *)
    (∀ (h1 : CpuId) (m1 : regfile),
       ⌜ m1 !!! Regidx a0_idx = mword_of_int ps ⌝ -∗
       ⌜ m1 !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
       uword γd ps (mword_of_int s0) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UA -∗
       Pex -∗
       urun N h1 m1 (mword_of_int ShSyms.parsepipe)
         (6 + (16 + (24 + (8 + nn)))) -∗
       (∀ t : Z,
          PT t -∗
          uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
          ustr γd dq s0 len f -∗
          ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
          ustr γd dv ushp_symbols 7 ushp_sym_f -∗
            ∀ (h2 : CpuId) (m2 : regfile),
              ⌜ ucallee_saved m1 m2 ⌝ -∗
              ⌜ m2 !!! Regidx a0_idx = mword_of_int t ⌝ -∗
              UB -∗
              Pex -∗
              urun N h2 m2 (ret_pc (m1 !!! Regidx ra_idx))
                (6 + (16 + (24 + (8 + nn)))) -∗
              mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ t : Z,
       PT t -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UB -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (6 + (16 + (24 + (8 + nn))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hs0 Hs64 Hps0 Hps8 Hpssz.
    assert (Hnend : (len < len)%nat -> ushp_is_sym (f len) = false)
      by (intro Hlt; exfalso; lia).
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM Hpay Hrun Hpp Hcont".
    rewrite shpp_parseline.
    assert (Elen0 : (len + ushp_skipws (len - len) len f)%nat = len)
      by (rewrite Nat.sub_diag; cbn [ushp_skipws]; lia).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x6e2..0x6f0  the prologue ---- *)
    iApply (wp_kshp_frame_pro 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] 0x6e2
              (fun i : nat => match i with
                              | 0%nat => 0x6e4 | 1%nat => 0x6e6
                              | 2%nat => 0x6e8 | 3%nat => 0x6ea
                              | 4%nat => 0x6ec | 5%nat => 0x6ee
                              | _ => 0x6f0 end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (6 + (16 + (24 + (8 + nn)))) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_6e2 with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_6e4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6e6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6e8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ea with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ec with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ee with "Hcode") | done ]. }
    { iApply (uis_shp_6f0 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (mA := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (HmA : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    mA !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (HspA : mA !!! Regidx csp_rs1 = spn).
    { rewrite (HmA csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x6f2  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv N h1 mA (mword_of_int 0x6f2) s2_idx a0_idx
              (mword_of_int ps) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6f2 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> mA).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m2 !!! Regidx q = mA !!! Regidx q)
      by (intros q Hq; exact (upd_ne mA (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x6f4  c.mv s3,a1 ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0x6f4) s3_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (HmA a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6f4 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx s3_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x6f6  jal 682 <parsepipe> ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x6f6)
              (mword_of_int 2097036 : mword 21) ra_idx
              (mword_of_int 0x682) (mword_of_int 0x6fa)
              (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6f6 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6fa : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret4 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x6fa).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x6fa : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (HmA a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_4 : m4 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (HmA a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    rewrite <- shpp_parsepipe.
    iApply ("Hpp" $! h4 m4 with "[] [] Hcur Hstr Hws Hsy HM Hpay Hrun").
    { iPureIntro. exact Ha0_4. }
    { iPureIntro. exact Ha1_4. }
    iIntros (t) "HPT Hcur Hstr Hws Hsy".
    iIntros (h5 m5) "%Hcs45 %Ha0_5 HM' Hpay Hrun".
    rewrite Eret4.
    (* ---- 0x6fa  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h5 m5 (mword_of_int 0x6fa) s1_idx a0_idx
              (mword_of_int t) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_6fa with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x6fc/0x700  the ampersand table ---- *)
    iApply (wp_uk_auipc N h6 m6 (mword_of_int 0x6fc)
              (mword_of_int 1 : mword 20) s4_idx
              (mword_of_int 0x16fc) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6fc with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 0x16fc : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s4_idx) (Regidx q) _ Hq)).
    assert (Hs4_7 : m7 !!! Regidx s4_idx = mword_of_int 0x16fc)
      by exact (upd_eq m6 (Regidx s4_idx)
                  (regval_into_reg (mword_of_int 0x16fc : mword 64))).
    iApply (wp_uk_addi N h7 m7 (mword_of_int 0x700)
              (mword_of_int 3132 : mword 12) s4_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_7; unfold ushp_T_back;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_700 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx s4_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_back : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s4_idx) (Regidx q) _ Hq)).
    assert (Hs4_8 : m8 !!! Regidx s4_idx = mword_of_int ushp_T_back)
      by exact (upd_eq m7 (Regidx s4_idx)
                  (regval_into_reg (mword_of_int ushp_T_back : mword 64))).
    (* the two values the guards read, once *)
    assert (Hs2_8 : m8 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate))
              (Hcs45 s2_idx ltac:(vm_compute; reflexivity))
              (Hm4 s2_idx ltac:(vm_compute; discriminate))
              (Hm3 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s2_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs3_8 : m8 !!! Regidx s3_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hcs45 s3_idx ltac:(vm_compute; reflexivity))
              (Hm4 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s3_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    (* ---- 0x704  c.j 0x71a -- into the backgrounding loop's GUARD ---- *)
    iApply (wp_uk_cj N h8 m8 (mword_of_int 0x704)
              (mword_of_int 11 : mword 11) (mword_of_int 0x71a)
              (6 + (16 + (24 + (8 + nn))))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_704 with "Hcode"). }
    iIntros (h9) "Hrun".
    (* ---- 0x71a..0x71e  peek's three arguments ---- *)
    iApply (wp_uk_cmv N h9 m8 (mword_of_int 0x71a) a2_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_8; symmetry;
                    exact (ushp_mv_val ushp_T_back))
              with "[] Hrun").
    { iApply (uis_shp_71a with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_back : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a2_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h10 m9 (mword_of_int 0x71c) a1_idx s3_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm9 s3_idx ltac:(vm_compute; discriminate))
                      Hs3_8; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_71c with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h11 m10 (mword_of_int 0x71e) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      (Hm9 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_8; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_71e with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x720  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h12 m11 (mword_of_int 0x720)
              (mword_of_int 2096424 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x724)
              (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_720 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x724 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x724).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x724 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_12 : m12 !!! Regidx a2_idx = mword_of_int ushp_T_back).
    { rewrite (Hm12 a2_idx ltac:(vm_compute; discriminate))
              (Hm11 a2_idx ltac:(vm_compute; discriminate))
              (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_back : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h13 m12 dq dw true DfracDiscarded ps s0
              ushp_T_back len len 1 f (ushp_lit ushp_T_back)
              (mword_of_int (s0 + Z.of_nat len)) (36 + (8 + nn))
              Ha0_12 Ha1_12 Ha2_12 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_back; lia)
              ltac:(unfold ushp_T_back, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_back 1 DfracDiscarded
                ushp_T_back_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h14 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12 Elen0.
    rewrite (ushs_peek_res_nsym len f
               (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_back ltac:(rewrite Elen0; exact Hnend) ushp_T_back_sym) in Ha0_13.
    (* ---- 0x724  c.bnez a0 -- NOT taken: nothing is backgrounded ---- *)
    iApply (wp_uk_cbnez N h14 m13 (mword_of_int 0x724)
              (mword_of_int 241 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x706) (6 + (16 + (24 + (8 + nn))))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_724 with "Hcode"). }
    iIntros (h15) "Hrun".
    (* ---- 0x726/0x72a  the semicolon table ---- *)
    iApply (wp_uk_auipc N h15 m13 (mword_of_int 0x726)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x1726) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_726 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m14 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 0x1726 : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_14 : m14 !!! Regidx a2_idx = mword_of_int 0x1726)
      by exact (upd_eq m13 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x1726 : mword 64))).
    iApply (wp_uk_addi N h16 m14 (mword_of_int 0x72a)
              (mword_of_int 3098 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_list) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_14; unfold ushp_T_list;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_72a with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m15 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_list : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x72e/0x730  the other two arguments again ---- *)
    assert (Hs3_15 : m15 !!! Regidx s3_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm15 s3_idx ltac:(vm_compute; discriminate))
              (Hm14 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_8. }
    assert (Hs2_15 : m15 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm15 s2_idx ltac:(vm_compute; discriminate))
              (Hm14 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s2_idx ltac:(vm_compute; reflexivity))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_8. }
    iApply (wp_uk_cmv N h17 m15 (mword_of_int 0x72e) a1_idx
              s3_idx (mword_of_int (s0 + Z.of_nat len))
              (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_15; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_72e with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m16 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h18 m16 (mword_of_int 0x730) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm16 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_15; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_730 with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m17 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m16).
    assert (Hm17 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m17 !!! Regidx q = m16 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m16 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x732  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h19 m17 (mword_of_int 0x732)
              (mword_of_int 2096406 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x736)
              (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_732 with "Hcode"). }
    iIntros (h20) "Hrun".
    set (m18 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x736 : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret18 : ret_pc (m18 !!! Regidx ra_idx) = mword_of_int 0x736).
    { rewrite (upd_eq m17 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x736 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_18 : m18 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm18 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m16 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_18 : m18 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm18 a1_idx ltac:(vm_compute; discriminate))
              (Hm17 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m15 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_18 : m18 !!! Regidx a2_idx = mword_of_int ushp_T_list).
    { rewrite (Hm18 a2_idx ltac:(vm_compute; discriminate))
              (Hm17 a2_idx ltac:(vm_compute; discriminate))
              (Hm16 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m14 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_list : mword 64))). }
    iApply (wp_kshp_peek h20 m18 dq dw true DfracDiscarded ps s0
              ushp_T_list len len 1 f (ushp_lit ushp_T_list)
              (mword_of_int (s0 + Z.of_nat len)) (36 + (8 + nn))
              Ha0_18 Ha1_18 Ha2_18 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_list; lia)
              ltac:(unfold ushp_T_list, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_list 1 DfracDiscarded
                ushp_T_list_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h21 m19) "%Hcs1819 %Ha0_19 Hrun".
    rewrite Eret18 Elen0.
    rewrite (ushs_peek_res_nsym len f
               (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_list ltac:(rewrite Elen0; exact Hnend) ushp_T_list_sym) in Ha0_19.
    (* ---- 0x736  c.bnez a0 -- NOT taken: there is no list ---- *)
    iApply (wp_uk_cbnez N h21 m19 (mword_of_int 0x736)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x74a) (6 + (16 + (24 + (8 + nn))))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_19; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_736 with "Hcode"). }
    iIntros (h22) "Hrun".
    (* ---- 0x738  c.mv a0,s1 ---- *)
    assert (Hs1_19 : m19 !!! Regidx s1_idx = mword_of_int t).
    { rewrite (Hcs1819 s1_idx ltac:(vm_compute; reflexivity))
              (Hm18 s1_idx ltac:(vm_compute; discriminate))
              (Hm17 s1_idx ltac:(vm_compute; discriminate))
              (Hm16 s1_idx ltac:(vm_compute; discriminate))
              (Hm15 s1_idx ltac:(vm_compute; discriminate))
              (Hm14 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate))
              (Hm9 s1_idx ltac:(vm_compute; discriminate))
              (Hm8 s1_idx ltac:(vm_compute; discriminate))
              (Hm7 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s1_idx)
               (regval_into_reg (mword_of_int t : mword 64))). }
    iApply (wp_uk_cmv N h22 m19 (mword_of_int 0x738) a0_idx
              s1_idx (mword_of_int t) (6 + (16 + (24 + (8 + nn))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_19; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_738 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> m19).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m19 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m19 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3 Hq4.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1819 q Hq)
              (Hm18 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm17 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm16 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q Hq4) (Hm7 q Hq4) (Hm6 q Hq1) (Hcs45 q Hq)
              (Hm4 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm3 q Hq3) (Hm2 q Hq2) (HmA q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1819 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm18 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm17 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm16 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact HspA. }
    (* ---- 0x73a..0x748  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x73a | 1%nat => 0x73c
                              | 2%nat => 0x73e | 3%nat => 0x740
                              | 4%nat => 0x742 | 5%nat => 0x744
                              | _ => 0x746 end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 6)) vals
              (6 + (16 + (24 + (8 + nn)))) h23 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_73a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_73c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_73e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_740 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_742 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_744 with "Hcode") | done ]. }
    { iApply (uis_shp_746 with "Hcode"). }
    { iApply (uis_shp_748 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! t
              with "HPT Hcur Hstr Hws Hsy [] [] HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6) eq_refl)
                 (Hmiss 5%nat s4_idx (mword_of_int 0 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m19 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int t : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ...AND THE LANDED WALK, BYTE-IDENTICAL: the call is the one-bar turn,
     its answer the PIPE node and the two EXEC nodes relayed separately. *)
  Lemma wp_kshp_parseline_bar {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len gp ge : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int s0) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parseline)
      (6 + (6 + (16 + (24 + (8 + nn))))) -∗
    (∀ t pl pr : Z,
       ⌜ pl + 168 < Z64 ⌝ -∗
       ⌜ pr + 168 < Z64 ⌝ -∗
       ushp_pipe_node t pl pr -∗
       ushp_exec_at s0 pl args -∗
       ushp_exec_at s0 pr [(S (S gp), ge)] -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (6 + (16 + (24 + (8 + nn))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok12.
    intros Hmal01 Hmal23 Ha0 Ha1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iApply (wp_kshp_parseline_bar_g h m dq dw dv ps s0 len f UM0 UM3
              (fun t : Z => ∃ pl pr : Z,
                 ⌜ pl + 168 < Z64 ⌝ ∗ ⌜ pr + 168 < Z64 ⌝ ∗
                 ushp_pipe_node t pl pr ∗
                 ushp_exec_at s0 pl args ∗
                 ushp_exec_at s0 pr [(S (S gp), ge)])%I nn
              Ha0 Ha1 Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpay Hrun [] [Hcont]").
    - iIntros (h1 m1) "%Ha0' %Ha1' Hcur Hstr Hws Hsy HM Hpay Hrun Hk".
      iApply (wp_kshp_parsepipe_bar_closed h1 m1 dq dw dv ps s0 len gp ge f
                args nn Hmal01 Hmal23
                Ha0' Ha1' Hpq Htoks Hpos Htlen Hs0 Hs64
                Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
      iIntros (t pl pr) "%Hplsz %Hprsz Hpnode Hnodel Hnoder Hcur Hstr Hws Hsy".
      iIntros (h2 m2) "%Hcs %Ha0'' HUB Hpay Hrun".
      iSpecialize ("Hk" $! t with "[Hpnode Hnodel Hnoder] Hcur Hstr Hws Hsy").
      { iExists pl, pr.
        iSplitR; [ iPureIntro; exact Hplsz | ].
        iSplitR; [ iPureIntro; exact Hprsz | ].
        iFrame "Hpnode Hnodel Hnoder". }
      iApply ("Hk" $! h2 m2 with "[] [] HUB Hpay Hrun").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0''.
    - iIntros (t) "HPT Hcur Hstr Hws Hsy".
      iDestruct "HPT" as (pl pr) "(%Hplsz & %Hprsz & Hpnode & Hnodel & Hnoder)".
      iIntros (h2 m2) "%Hcs %Ha0'' HUB Hpay Hrun".
      iApply ("Hcont" $! t pl pr
                with "[] [] Hpnode Hnodel Hnoder Hcur Hstr Hws Hsy [] [] HUB
                      Hpay Hrun").
      + iPureIntro. exact Hplsz.
      + iPureIntro. exact Hprsz.
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0''.
  Qed.

  (* ===================================================================== *)
  (* parsecmd ON THE PIPE LINE                                              *)
  (*                                                                        *)
  (* [strlen], [parseline], the leftovers [peek] and [nulterminate] -- and   *)
  (* on this line the last of those is part 1's                              *)
  (* [UkShPipeParse.wp_kshp_nulterminate_pipe], whose answer is the argv     *)
  (* cut of BOTH sides: [ushp_nulfold] of the right command's token over     *)
  (* [ushp_nulfold] of the left command's, on one buffer.                    *)
  (* ===================================================================== *)

  (* THE WALK WITH ITS TWO CALLS PREMISES (lane PIPES-C3b): [parseline]
     answers an abstract tree resource [PT t] and [nulterminate] cuts the
     line to the abstract [gN] under it.  The landed [wp_kshp_parsecmd_bar]
     below is this at the one-bar calls; [UkShPipesCmd] instantiates it at
     any number of bars. *)
  Lemma wp_kshp_parsecmd_bar_g {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dw dv : dfrac) (s0 : Z) (len : nat) (f : nat -> bv 8)
      (UA UB : iProp Σ) (PT : Z -> iProp Σ) (gN : nat -> bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UA -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd)
      (8 + (6 + (6 + (16 + (24 + (8 + nn)))))) -∗
    (* the [parseline] call, at a cursor slot [ps] of the caller's frame *)
    (∀ (h1 : CpuId) (m1 : regfile) (ps : Z),
       ⌜ m1 !!! Regidx a0_idx = mword_of_int ps ⌝ -∗
       ⌜ m1 !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
       ⌜ 0 < ps ⌝ -∗ ⌜ ps mod 8 = 0 ⌝ -∗ ⌜ ps + 8 < Z64 ⌝ -∗
       uword γd ps (mword_of_int s0) -∗
       ustr γd (DfracOwn 1) s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UA -∗
       Pex -∗
       urun N h1 m1 (mword_of_int ShSyms.parseline)
         (6 + (6 + (16 + (24 + (8 + nn))))) -∗
       (∀ t : Z,
          PT t -∗
          uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
          ustr γd (DfracOwn 1) s0 len f -∗
          ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
          ustr γd dv ushp_symbols 7 ushp_sym_f -∗
            ∀ (h2 : CpuId) (m2 : regfile),
              ⌜ ucallee_saved m1 m2 ⌝ -∗
              ⌜ m2 !!! Regidx a0_idx = mword_of_int t ⌝ -∗
              UB -∗
              Pex -∗
              urun N h2 m2 (ret_pc (m1 !!! Regidx ra_idx))
                (6 + (6 + (16 + (24 + (8 + nn))))) -∗
              mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* the [nulterminate] call, at the tree [parseline] answered *)
    (∀ (h1 : CpuId) (m1 : regfile) (t : Z),
       ⌜ m1 !!! Regidx a0_idx = mword_of_int t ⌝ -∗
       PT t -∗
       ubytes γd s0 (S len) (UkShParseCmd.ushp_ext len f) -∗
       urun N h1 m1 (mword_of_int ShSyms.nulterminate) (60 + nn) -∗
       (PT t -∗
        ubytes γd s0 (S len) gN -∗
          ∀ (h2 : CpuId) (m2 : regfile),
            ⌜ ucallee_saved m1 m2 ⌝ -∗
            ⌜ m2 !!! Regidx a0_idx = mword_of_int t ⌝ -∗
            urun N h2 m2 (ret_pc (m1 !!! Regidx ra_idx)) (60 + nn) -∗
            mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (∀ t : Z,
       PT t -∗
       ubytes γd s0 (S len) gN -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UB -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (8 + (6 + (6 + (16 + (24 + (8 + nn)))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM Hpay Hrun Hplc Hnc Hcont".
    rewrite shpp_parsecmd.
    iDestruct (ustr_len with "Hstr") as %Hlen31.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    assert (Elen0 : (len + ushp_skipws (len - len) len f)%nat = len)
      by (rewrite Nat.sub_diag; cbn [ushp_skipws]; lia).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | _ => m !!! Regidx s3_idx end).
    (* ---- 0x86e  c.addi16sp sp,sp,-64 ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x86e)
              (mword_of_int 60 : mword 6) 8 (60 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_86e with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 40) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 40)
      by (unfold spl; apply uint_moi; lia).
    set (sp3 := (mword_of_int (uint sp0 - 64) : mword 64)).
    assert (Hsp3u : uint sp3 = uint sp0 - 64)
      by (unfold sp3; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 3 [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    iDestruct (ushp_frame_split spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hloc") as "[Hlc Hbot]".
    rewrite !big_sepL_cons big_sepL_nil.
    iDestruct "Hlc" as "([%wl0 L0] & [%wcur Lcur] & [%wl2 L2] & _)".
    assert (E0 : uint sp0 - 40 - 8 * (Z.of_nat 0 + 1) = uint sp0 - 48)
      by lia.
    assert (E1 : uint sp0 - 40 - 8 * (Z.of_nat 1 + 1) = uint sp0 - 56)
      by lia.
    assert (E2 : uint sp0 - 40 - 8 * (Z.of_nat 2 + 1) = uint sp0 - 64)
      by lia.
    rewrite Hsplu E0 E1 E2.
    (* ---- 0x870..0x878  the five spills ---- *)
    iApply (wp_kshp_spill spn (60 + nn) [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x870 | 1%nat => 0x872
                              | 2%nat => 0x874 | 3%nat => 0x876
                              | 4%nat => 0x878 | _ => 0x87a end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_870 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_872 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_874 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_876 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_878 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x87a  c.addi4spn s0,sp,64 -- and its VALUE matters here ---- *)
    assert (Hup : add_vec_int spn (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 8) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    assert (Efp : add_vec spn
                    (sign_extend' 64
                       (caddi4spn_imm (mword_of_int 16 : mword 8))) = sp0).
    { assert (Ei : (sign_extend' 64
                      (caddi4spn_imm (mword_of_int 16 : mword 8)) : mword 64)
                   = mword_of_int (8 * Z.of_nat 8))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ei. exact Hup. }
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x87a)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              sp0 (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1; symmetry; exact Efp)
              with "[] Hrun").
    { iApply (uis_shp_87a with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hs0_2 : m2 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
      symmetry. exact (moi_of_uint sp0). }
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int s0).
    { rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x87c  sd a0,-56(s0) -- the cursor cell is initialised ---- *)
    assert (Hcur0 : 0 < uint sp0 - 56) by lia.
    assert (Hcur8 : (uint sp0 - 56) mod 8 = 0).
    { rewrite Zminus_mod Hal8. reflexivity. }
    assert (Hcurz : uint sp0 - 56 + 8 < Z64) by lia.
    iApply (wp_uk_sd N h3 m2 (mword_of_int 0x87c)
              (mword_of_int 4040 : mword 12) s0_idx a0_idx
              (uint sp0 - 56) wcur (60 + nn)
              ltac:(rewrite Hs0_2 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              with "[] Lcur Hrun").
    { iApply (uis_shp_87c with "Hcode"). }
    iIntros "Lcur" (h4) "Hrun".
    rewrite Ha0_2.
    (* ---- 0x880  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h4 m2 (mword_of_int 0x880) s1_idx a0_idx
              (mword_of_int s0) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2; symmetry; exact (ushp_mv_val s0))
              with "[] Hrun").
    { iApply (uis_shp_880 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int s0 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x882  jal a30 <strlen> ---- *)
    iApply (wp_uk_jal N h5 m3 (mword_of_int 0x882)
              (mword_of_int 430 : mword 21) ra_idx
              (mword_of_int 0xa30) (mword_of_int 0x886) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_882 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x886 : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret4 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x886).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x886 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int s0).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_2. }
    rewrite <- shpp_strlen.
    iApply (wp_kshp_strlen h6 m4 (DfracOwn 1) s0 len f (58 + nn)
              Ha0_4 ltac:(lia) ltac:(lia) with "Hcode Hstr Hrun").
    iIntros "Hstr" (h7 m5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    (* ---- 0x886/0x888  the 32-bit zero extension ---- *)
    assert (E32 : (2:Z) ^ 32 = 4294967296) by (vm_compute; reflexivity).
    iApply (wp_uk_cslli N h7 m5 (mword_of_int 0x886)
              (mword_of_int 32 : mword 6) a0_idx
              (mword_of_int (Z.of_nat len * 2 ^ 32)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry;
                    exact (moi_shl (Z.of_nat len) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_886 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m6 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat len * 2 ^ 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat len * 2 ^ 32))
      by exact (upd_eq m5 (Regidx a0_idx)
                  (regval_into_reg
                     (mword_of_int (Z.of_nat len * 2 ^ 32) : mword 64))).
    iApply (wp_uk_csrli N h8 m6 (mword_of_int 0x888)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 3) a0_idx
              (mword_of_int (Z.of_nat len)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6
                      (moi_shr (Z.of_nat len * 2 ^ 32) 32 ltac:(lia)
                         ltac:(rewrite E32; unfold Z64; lia));
                    f_equal; symmetry; apply Z.div_mul; lia)
              with "[] Hrun").
    { iApply (uis_shp_888 with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m7 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat len) : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha0_7 : m7 !!! Regidx a0_idx = mword_of_int (Z.of_nat len))
      by exact (upd_eq m6 (Regidx a0_idx)
                  (regval_into_reg
                     (mword_of_int (Z.of_nat len) : mword 64))).
    (* ---- 0x88a  c.add s1,s1,a0 -- es = s + len ---- *)
    assert (Hs1_7 : m7 !!! Regidx s1_idx = mword_of_int s0).
    { rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hm6 s1_idx ltac:(vm_compute; discriminate))
              (Hcs45 s1_idx ltac:(vm_compute; reflexivity))
              (Hm4 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s1_idx)
               (regval_into_reg (mword_of_int s0 : mword 64))). }
    iApply (wp_uk_cadd N h9 m7 (mword_of_int 0x88a) s1_idx
              a0_idx (mword_of_int (s0 + Z.of_nat len)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_7 Ha0_7; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_88a with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m8 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_8 : m8 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len))
      by exact (upd_eq m7 (Regidx s1_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat len) : mword 64))).
    (* ---- 0x88c  addi s2,s0,-56 -- &s ---- *)
    assert (Hs0_8 : m8 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm8 s0_idx ltac:(vm_compute; discriminate))
              (Hm7 s0_idx ltac:(vm_compute; discriminate))
              (Hm6 s0_idx ltac:(vm_compute; discriminate))
              (Hcs45 s0_idx ltac:(vm_compute; reflexivity))
              (Hm4 s0_idx ltac:(vm_compute; discriminate))
              (Hm3 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_2. }
    iApply (wp_uk_addi N h10 m8 (mword_of_int 0x88c)
              (mword_of_int 4040 : mword 12) s0_idx s2_idx
              (mword_of_int (uint sp0 - 56)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_8;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 4040 : mword 12)
                                  : mword 64) = mword_of_int (-56))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_88c with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m9 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (uint sp0 - 56) : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s2_idx) (Regidx q) _ Hq)).
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int (uint sp0 - 56))
      by exact (upd_eq m8 (Regidx s2_idx)
                  (regval_into_reg
                     (mword_of_int (uint sp0 - 56) : mword 64))).
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_8. }
    (* ---- 0x890/0x892  parseline(&s, es) ---- *)
    iApply (wp_uk_cmv N h11 m9 (mword_of_int 0x890) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_890 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h12 m10 (mword_of_int 0x892) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_892 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x894  jal 6e2 <parseline> ---- *)
    iApply (wp_uk_jal N h13 m11 (mword_of_int 0x894)
              (mword_of_int 2096718 : mword 21) ra_idx
              (mword_of_int 0x6e2) (mword_of_int 0x898) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_894 with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x898 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x898).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x898 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 56) : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    rewrite <- shpp_parseline.
    iApply ("Hplc" $! h14 m12 (uint sp0 - 56)
              with "[] [] [] [] [] Lcur Hstr Hws Hsy HM Hpay Hrun").
    { iPureIntro. exact Ha0_12. }
    { iPureIntro. exact Ha1_12. }
    { iPureIntro. exact Hcur0. }
    { iPureIntro. exact Hcur8. }
    { iPureIntro. exact Hcurz. }
    iIntros (p) "HPT Lcur Hstr Hws Hsy".
    iIntros (h15 m13) "%Hcs1213 %Ha0_13 HM' Hpay Hrun".
    rewrite Eret12.
    (* ---- 0x898  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv N h15 m13 (mword_of_int 0x898) s3_idx
              a0_idx (mword_of_int p) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_13; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_898 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m14 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx s3_idx) (Regidx q) _ Hq)).
    assert (Hs3_14 : m14 !!! Regidx s3_idx = mword_of_int p)
      by exact (upd_eq m13 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hs1_14 : m14 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm14 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_9. }
    assert (Hs2_14 : m14 !!! Regidx s2_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm14 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s2_idx ltac:(vm_compute; reflexivity))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_9. }
    assert (Hs0_14 : m14 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm14 s0_idx ltac:(vm_compute; discriminate))
              (Hcs1213 s0_idx ltac:(vm_compute; reflexivity))
              (Hm12 s0_idx ltac:(vm_compute; discriminate))
              (Hm11 s0_idx ltac:(vm_compute; discriminate))
              (Hm10 s0_idx ltac:(vm_compute; discriminate))
              (Hm9 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_8. }
    (* ---- 0x89a/0x89e  the EMPTY token table ---- *)
    iApply (wp_uk_auipc N h16 m14 (mword_of_int 0x89a)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x189a) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_89a with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m15 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 0x189a : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_15 : m15 !!! Regidx a2_idx = mword_of_int 0x189a)
      by exact (upd_eq m14 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x189a : mword 64))).
    iApply (wp_uk_addi N h17 m15 (mword_of_int 0x89e)
              (mword_of_int 2558 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_none) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_15; unfold ushp_T_none;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_89e with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m16 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_none : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x8a2/0x8a4  peek(&s, es, "") ---- *)
    iApply (wp_uk_cmv N h18 m16 (mword_of_int 0x8a2) a1_idx
              s1_idx (mword_of_int (s0 + Z.of_nat len)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm16 s1_idx ltac:(vm_compute; discriminate))
                      (Hm15 s1_idx ltac:(vm_compute; discriminate))
                      Hs1_14; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_8a2 with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m17 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m16).
    assert (Hm17 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m17 !!! Regidx q = m16 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m16 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h19 m17 (mword_of_int 0x8a4) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm17 s2_idx ltac:(vm_compute; discriminate))
                      (Hm16 s2_idx ltac:(vm_compute; discriminate))
                      (Hm15 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_14; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_8a4 with "Hcode"). }
    iIntros (h20) "Hrun".
    set (m18 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x8a6  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h20 m18 (mword_of_int 0x8a6)
              (mword_of_int 2096034 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x8aa) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_8a6 with "Hcode"). }
    iIntros (h21) "Hrun".
    set (m19 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8aa : mword 64)]> m18).
    assert (Hm19 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m19 !!! Regidx q = m18 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m18 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret19 : ret_pc (m19 !!! Regidx ra_idx) = mword_of_int 0x8aa).
    { rewrite (upd_eq m18 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x8aa : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_19 : m19 !!! Regidx a0_idx
                     = mword_of_int (uint sp0 - 56)).
    { rewrite (Hm19 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m17 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 56) : mword 64))). }
    assert (Ha1_19 : m19 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm19 a1_idx ltac:(vm_compute; discriminate))
              (Hm18 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m16 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_19 : m19 !!! Regidx a2_idx = mword_of_int ushp_T_none).
    { rewrite (Hm19 a2_idx ltac:(vm_compute; discriminate))
              (Hm18 a2_idx ltac:(vm_compute; discriminate))
              (Hm17 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m15 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_none : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h21 m19 (DfracOwn 1) dw true DfracDiscarded
              (uint sp0 - 56) s0 ushp_T_none len len 0 f
              (ushp_lit ushp_T_none)
              (mword_of_int (s0 + Z.of_nat len)) (50 + nn)
              Ha0_19 Ha1_19 Ha2_19 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)
              ltac:(unfold ushp_T_none; lia)
              ltac:(unfold ushp_T_none, Z64; lia) Hcur0 Hcur8 Hcurz
              with "Hcode Lcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_none 0 DfracDiscarded
                ushp_T_none_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Lcur Hstr Hws _" (h22 m20) "%Hcs1920 %Ha0_20 Hrun".
    rewrite Eret19 Elen0.
    (* ---- 0x8aa  ld a2,-56(s0) -- the cursor, read back ---- *)
    assert (Hs0_19 : m19 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm19 s0_idx ltac:(vm_compute; discriminate))
              (Hm18 s0_idx ltac:(vm_compute; discriminate))
              (Hm17 s0_idx ltac:(vm_compute; discriminate))
              (Hm16 s0_idx ltac:(vm_compute; discriminate))
              (Hm15 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_14. }
    assert (Hs0_20 : m20 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hcs1920 s0_idx ltac:(vm_compute; reflexivity)).
      exact Hs0_19. }
    iApply (wp_uk_ld N h22 m20 (mword_of_int 0x8aa)
              (mword_of_int 4040 : mword 12) s0_idx a2_idx (DfracOwn 1)
              (uint sp0 - 56) (mword_of_int (s0 + Z.of_nat len)) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_20 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              ltac:(vm_compute; discriminate)
              with "[] Lcur Hrun").
    { iApply (uis_shp_8aa with "Hcode"). }
    iIntros "Lcur" (h23) "Hrun".
    set (m21 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m20).
    assert (Hm21 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m21 !!! Regidx q = m20 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m20 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_21 : m21 !!! Regidx a2_idx
                     = mword_of_int (s0 + Z.of_nat len))
      by exact (upd_eq m20 (Regidx a2_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat len) : mword 64))).
    assert (Hs1_21 : m21 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm21 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1920 s1_idx ltac:(vm_compute; reflexivity))
              (Hm19 s1_idx ltac:(vm_compute; discriminate))
              (Hm18 s1_idx ltac:(vm_compute; discriminate))
              (Hm17 s1_idx ltac:(vm_compute; discriminate))
              (Hm16 s1_idx ltac:(vm_compute; discriminate))
              (Hm15 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_14. }
    (* ---- 0x8ae  bne a2,s1 -- NOT taken: there are no leftovers ---- *)
    iApply (wp_uk_btype N h23 m21 (mword_of_int 0x8ae)
              (mword_of_int 26 : mword 13) s1_idx a2_idx BNE false
              (mword_of_int 0x8c8) (60 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha2_21 Hs1_21;
                    rewrite (moi_neq_vec (s0 + Z.of_nat len)
                               (s0 + Z.of_nat len)
                               ltac:(unfold Z64 in *; lia)
                               ltac:(unfold Z64 in *; lia));
                    rewrite Z.eqb_refl; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_8ae with "Hcode"). }
    iIntros (h24) "Hrun".
    (* ---- 0x8b2  c.mv a0,s3 ---- *)
    assert (Hs3_21 : m21 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hm21 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1920 s3_idx ltac:(vm_compute; reflexivity))
              (Hm19 s3_idx ltac:(vm_compute; discriminate))
              (Hm18 s3_idx ltac:(vm_compute; discriminate))
              (Hm17 s3_idx ltac:(vm_compute; discriminate))
              (Hm16 s3_idx ltac:(vm_compute; discriminate))
              (Hm15 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_14. }
    iApply (wp_uk_cmv N h24 m21 (mword_of_int 0x8b2) a0_idx
              s3_idx (mword_of_int p) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_21; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_8b2 with "Hcode"). }
    iIntros (h25) "Hrun".
    set (m22 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m21).
    assert (Hm22 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m22 !!! Regidx q = m21 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m21 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x8b4  jal 7ee <nulterminate> ---- *)
    iApply (wp_uk_jal N h25 m22 (mword_of_int 0x8b4)
              (mword_of_int 2096954 : mword 21) ra_idx
              (mword_of_int 0x7ee) (mword_of_int 0x8b8) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_8b4 with "Hcode"). }
    iIntros (h26) "Hrun".
    set (m23 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8b8 : mword 64)]> m22).
    assert (Hm23 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m23 !!! Regidx q = m22 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m22 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret23 : ret_pc (m23 !!! Regidx ra_idx) = mword_of_int 0x8b8).
    { rewrite (upd_eq m22 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x8b8 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_23 : m23 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm23 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m21 (Regidx a0_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iDestruct (ushp_ustr_bytes s0 len f with "Hstr") as "Hline".
    rewrite <- shpp_nulterminate.
    iApply ("Hnc" $! h26 m23 p with "[] HPT Hline Hrun").
    { iPureIntro. exact Ha0_23. }
    iIntros "HPT Hline" (h27 m24) "%Hcs2324 %Ha0_24 Hrun".
    rewrite Eret23.
    (* ---- 0x8b8  c.mv a0,s3 ---- *)
    assert (Hs3_24 : m24 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs2324 s3_idx ltac:(vm_compute; reflexivity))
              (Hm23 s3_idx ltac:(vm_compute; discriminate))
              (Hm22 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_21. }
    iApply (wp_uk_cmv N h27 m24 (mword_of_int 0x8b8) a0_idx
              s3_idx (mword_of_int p) (60 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_24; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_8b8 with "Hcode"). }
    iIntros (h28) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m24).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m24 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m24 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* the whole body, as one preservation fact *)
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs2324 q Hq)
              (Hm23 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm22 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm21 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1920 q Hq)
              (Hm19 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm18 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm17 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm16 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q Hq3) (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q Hq2) (Hm8 q Hq1)
              (Hm7 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs45 q Hq)
              (Hm4 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm3 q Hq1) (Hm2 q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs2324 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm23 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm22 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm21 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1920 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm19 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm18 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm17 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm16 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x8ba..0x8c6  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 8 3 [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)] (mword_of_int 7 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x8ba | 1%nat => 0x8bc
                              | 2%nat => 0x8be | 3%nat => 0x8c0
                              | 4%nat => 0x8c2 | _ => 0x8c4 end)
              (mword_of_int 4 : mword 6) sp0 spl vals (60 + nn) h28 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) ltac:(lia)
              ltac:(cbn [length]; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl [L0 Lcur L2 Hbot] Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_8ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_8c2 with "Hcode") | done ]. }
    { iApply (uis_shp_8c4 with "Hcode"). }
    { iApply (uis_shp_8c6 with "Hcode"). }
    { iApply (ushp_frame_join spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                (fun i : nat => match i with
                                | 0%nat => wl0
                                | 1%nat => mword_of_int (s0 + Z.of_nat len)
                                | _ => wl2 end)
                ltac:(cbn [length]; lia) with "[L0 Lcur L2] Hbot").
      rewrite !big_sepL_cons big_sepL_nil Hsplu E0 E1 E2.
      iSplitL "L0"; [ iExact "L0" | ].
      iSplitL "Lcur"; [ iExact "Lcur" | ].
      iSplitL "L2"; [ iExact "L2" | done ]. }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! p
              with "HPT Hline Hws Hsy [] [] HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 6 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 5 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 3 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m24 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  (* ...AND THE LANDED WALK, BYTE-IDENTICAL: the two calls at the one-bar
     line -- [wp_kshp_parseline_bar] and part 1's
     [UkShPipeParse.wp_kshp_nulterminate_pipe]. *)
  Lemma wp_kshp_parsecmd_bar {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (args : list (nat * nat))
      (gp ge : nat) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd)
      (8 + (6 + (6 + (16 + (24 + (8 + nn)))))) -∗
    (∀ t pl pr : Z,
       UkShPipeParse.ushp_pipe_node N t pl pr -∗
       ushp_exec_at s0 pl args -∗
       ushp_exec_at s0 pr [(S (S gp), ge)] -∗
       ubytes γd s0 (S len)
         (UkShParseCmd.ushp_nulfold [(S (S gp), ge)]
            (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f))) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (8 + (6 + (6 + (16 + (24 + (8 + nn)))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok12.
    intros Hmal01 Hmal23 Ha0 Hpq Htoks Hpos Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iApply (wp_kshp_parsecmd_bar_g h m dw dv s0 len f UM0 UM3
              (fun t : Z => ∃ pl pr : Z,
                 ⌜ pl + 168 < Z64 ⌝ ∗ ⌜ pr + 168 < Z64 ⌝ ∗
                 ushp_pipe_node t pl pr ∗
                 ushp_exec_at s0 pl args ∗
                 ushp_exec_at s0 pr [(S (S gp), ge)])%I
              (UkShParseCmd.ushp_nulfold [(S (S gp), ge)]
                 (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f)))
              nn Ha0 Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy HM Hpay Hrun [] [] [Hcont]").
    - (* parseline, at the one-bar line *)
      iIntros (h1 m1 ps) "%Ha0' %Ha1' %Hps0 %Hps8 %Hpsz Hcur Hstr Hws Hsy HM
                          Hpay Hrun Hk".
      iApply (wp_kshp_parseline_bar h1 m1 (DfracOwn 1) dw dv ps s0 len gp ge f
                args nn Hmal01 Hmal23 Ha0' Ha1'
                Hpq Htoks Hpos Htlen ltac:(lia) ltac:(lia) Hps0 Hps8 Hpsz
                with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
      iIntros (t pl pr) "%Hplsz %Hprsz Hpnode Hnodel Hnoder Hcur Hstr Hws Hsy".
      iIntros (h2 m2) "%Hcs %Ha0'' HUB Hpay Hrun".
      iSpecialize ("Hk" $! t with "[Hpnode Hnodel Hnoder] Hcur Hstr Hws Hsy").
      { iExists pl, pr.
        iSplitR; [ iPureIntro; exact Hplsz | ].
        iSplitR; [ iPureIntro; exact Hprsz | ].
        iFrame "Hpnode Hnodel Hnoder". }
      iApply ("Hk" $! h2 m2 with "[] [] HUB Hpay Hrun").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0''.
    - (* nulterminate, at the PIPE node over two EXEC nodes *)
      iIntros (h1 m1 t) "%Ha0' HPT Hline Hrun Hk".
      iDestruct "HPT" as (pl pr) "(%Hplsz & %Hprsz & Hpnode & Hnodel & Hnoder)".
      iDestruct (UkShPipeParse.ushp_pipe_node_addr N with "Hpnode")
        as "[%Hraddr Hpnode]".
      destruct Hraddr as (Hp0 & Hp8 & Hpz40).
      iDestruct (UkShPipeParse.ushp_exec_at_facts N with "Hnodel")
        as "[%Hfl Hnodel]".
      destruct Hfl as (_ & Hpe0 & Hpe8).
      iDestruct (UkShPipeParse.ushp_exec_at_facts N with "Hnoder")
        as "[%Hfr Hnoder]".
      destruct Hfr as (_ & Hpr0 & Hpr8).
      iApply (UkShPipeParse.wp_kshp_nulterminate_pipe N h1 m1 s0 t pl pr
                len (UkShParseCmd.ushp_ext len f) args [(S (S gp), ge)] (52 + nn)
                Ha0' ltac:(lia) ltac:(lia) Hp0 Hp8 Hpz40
                Hpe0 Hpe8 Hplsz Hpr0 Hpr8 Hprsz
                Htlen ltac:(cbn [length]; lia)
                ltac:(intros i tk Hi;
                      destruct (ushs_toks_in len f gp 0%nat args Htoks
                                  i tk Hi) as [ Hlo0 Hhi0 ];
                      split; lia)
                ltac:(intros i tk Hi;
                      destruct i as [| i ]; cbn in Hi;
                      [ injection Hi as <-; cbn [fst snd];
                        destruct Hpq as (_ & _ & _ & _ & Hlo1 & Hhi1 & _);
                        split; lia
                      | rewrite lookup_nil in Hi; discriminate ])
                with "Hcode Hro Hpnode Hnodel Hnoder Hline Hrun").
      iIntros "Hpnode Hnodel Hnoder Hline" (h2 m2) "%Hcs %Ha0'' Hrun".
      iSpecialize ("Hk" with "[Hpnode Hnodel Hnoder] Hline").
      { iExists pl, pr.
        iSplitR; [ iPureIntro; exact Hplsz | ].
        iSplitR; [ iPureIntro; exact Hprsz | ].
        iFrame "Hpnode Hnodel Hnoder". }
      iApply ("Hk" $! h2 m2 with "[] [] Hrun").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0''.
    - iIntros (t) "HPT Hline Hws Hsy".
      iDestruct "HPT" as (pl pr) "(_ & _ & Hpnode & Hnodel & Hnoder)".
      iIntros (h2 m2) "%Hcs %Ha0'' HUB Hpay Hrun".
      iApply ("Hcont" $! t pl pr
                with "Hpnode Hnodel Hnoder Hline Hws Hsy [] [] HUB Hpay Hrun").
      + iPureIntro. exact Hcs.
      + iPureIntro. exact Ha0''.
  Qed.

  (* ===================================================================== *)
  (* THE PARSER THEOREM AT THE PIPE SHAPE                                   *)
  (*                                                                        *)
  (* [UkShRedirPc.wp_kshp_parser_redir]'s twin: the walk above with the      *)
  (* three nodes CLOSED into one [ushp_tree] by part 1's                     *)
  (* [UkShPipeParse.ushp_pipe_close].  Everything below the theorem relays   *)
  (* the nodes separately -- SH-PARSE-2's shape fact, at three nodes now --  *)
  (* and this is the one place that closes them.                             *)
  (* ===================================================================== *)

  Theorem wp_kshp_parser_pipe {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dw dv : dfrac) (s0 : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp ge : nat) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd)
      (8 + (6 + (6 + (16 + (24 + (8 + nn)))))) -∗
    (∀ t : Z,
       ushp_tree s0 t
         (UshpPipe (UshpExec args) (UshpExec [(S (S gp), ge)])) -∗
       ubytes γd s0 (S len)
         (UkShParseCmd.ushp_nulfold [(S (S gp), ge)]
            (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f))) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (8 + (6 + (6 + (16 + (24 + (8 + nn)))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok12.
    intros Hmal01 Hmal23 Ha0 Hpq Htoks Hpos Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iApply (wp_kshp_parsecmd_bar h m dw dv s0 len f args gp ge nn
              Hmal01 Hmal23 Ha0 Hpq Htoks Hpos Htlen Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (t pl pr) "Hpnode Hnodel Hnoder Hline Hws Hsy".
    iApply ("Hcont" $! t with "[Hpnode Hnodel Hnoder] Hline Hws Hsy").
    iApply (UkShPipeParse.ushp_pipe_close N s0 t pl pr
              (UshpExec args) (UshpExec [(S (S gp), ge)])
              with "Hpnode Hnodel Hnoder").
  Qed.

End UkShPipeCm.
