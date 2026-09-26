(* ===================================================================== *)
(* UkShArgs.v -- parseexec AT THE REFERENCE PARSER, ONCE                   *)
(* (design/user-once.md SS2, worklist A2c).                                *)
(*                                                                        *)
(*   struct cmd *parseexec(char **ps, char *es) {                          *)
(*     if(peek(ps, es, LPAREN)) return parseblock(ps, es);                 *)
(*     ret = execcmd();  cmd = (struct execcmd * )ret;  argc = 0;          *)
(*     ret = parseredirs(ret, ps, es);                                     *)
(*     while(!peek(ps, es, STOPS)) {                                       *)
(*       if((tok = gettoken(ps, es, &q, &eq)) == 0) break;                 *)
(*       if(tok != 'a') panic(syntax);                                     *)
(*       cmd->argv[argc] = q;  cmd->eargv[argc] = eq;  argc++;             *)
(*       if(argc >= MAXARGS) panic(too many args);                         *)
(*       ret = parseredirs(ret, ps, es);  }                                *)
(*     cmd->argv[argc] = 0;  cmd->eargv[argc] = 0;  return ret;  }         *)
(*                                                                        *)
(* sh's parseexec used to be walked THREE times -- the argument loop at    *)
(* [ushp_tokens] under [ushp_no_symbols] (UkShParseExec.wp_kshp_pex_loop), *)
(* at [ushs_toks] ending in the '>' with the REDIR node re-rooting [ret]   *)
(* (UkShRedirEx.wp_kshp_pex_loop_gt) and at [ushs_toks] ending AT the '|'  *)
(* (UkShPipeEx2.wp_kshp_pex_loop_bar); two exit rounds (UkShRedirEx.       *)
(* wp_kshp_pex_end at the end of the line, UkShPipeEx.wp_kshp_pex_bar at   *)
(* the '|'); and the whole function three times (UkShParseExec.            *)
(* wp_kshp_parseexec, UkShRedirPex.wp_kshp_parseexec_gt, UkShPipePex.      *)
(* wp_kshp_parseexec_bar).  This file is that walk once, stated at the     *)
(* reference parser [RefParse.ref_args] / [RefParse.ref_parseexec], and    *)
(* the landed statements above this file are corollaries in place; the    *)
(* base tier (UkShParseExec) sits below it and keeps its proof.            *)
(*                                                                        *)
(* (0) [ushp_pex_res rs Pex]: what a loop whose turns consumed the         *)
(*     redirects [rs] spends and hands back -- nothing at zero redirects,  *)
(*     redircmd's exit payment with its door otherwise -- so the loops     *)
(*     that allocate nothing come back exact.  [ushp_pex_gtk_in] /        *)
(*     [_out]: the exit round's gettoken resources, empty when the round   *)
(*     stops on the table and never reaches gettoken.                     *)
(* (1) [wp_ref_pex_exit]: the round that leaves the loop, at              *)
(*     [ref_peek]'s answer -- a hit on the stop table (0x608 taken), or a  *)
(*     miss followed by gettoken's NUL (0x616 taken).  _end and _bar are   *)
(*     its two instances.                                                 *)
(* (2) [wp_ref_pex_loop]: the loop at [ref_args len f n cur done rs0 =     *)
(*     Some (toks, rs0 ++ rs', fin)], by induction on the fuel driven by   *)
(*     RefParseSym.ref_args_inv: the two exits are (1), the turn is peek's *)
(*     miss, gettoken's word (UkShGettoken.wp_ref_gettoken), the two       *)
(*     stores, argc++ (MAXARGS refuted from the equation), parseredirs at   *)
(*     the redirects it consumes (UkShRedirs.wp_ref_parseredirs, which     *)
(*     re-roots s1), then the induction hypothesis.  The invariant is the  *)
(*     node so far [ushp_exec_pre s0 p done] and the REDIR chain so far    *)
(*     [ushp_redirs_at s0 t0 p rs0] with [s1 = t0]; the answer is the      *)
(*     node at [toks] and the chain at [rs0 ++ rs'] with [s1 = t].         *)
(* (3) [wp_ref_parseexec]: the whole function at [ref_parseexec len f n   *)
(*     off = Some (t, fin)]: the '(' peek misses (a hit is [None]),        *)
(*     execcmd, the leading parseredirs, the loop, the two terminator      *)
(*     stores, the epilogue.  The answer is OPEN -- the EXEC node at its   *)
(*     address with its 168-byte bound, the REDIR chain around it, and     *)
(*     [t = ref_wrap (UshpExec toks) rs] -- because the landed redirect    *)
(*     corollary hands its caller the two nodes separately (the child      *)
(*     pointer named, the bounds kept), which [ushp_tree] does not carry;  *)
(*     [wp_ref_parseexec_tree] closes it to [ushp_tree s0 root t] by       *)
(*     UkShRedirs.ushp_redirs_close for a caller that wants the published  *)
(*     form.  Allocations: [ushp_malloc_chain (ushp_nodes t)].             *)
(*     [ushp_cat t] is NOT a premise: under [ref_sym_scope] every redirect *)
(*     the reference consumes is the '>' one, so it is implied.           *)
(* (4) THE BUDGET IS GUARDED as UkShRedirs guards parseredirs' turn: the   *)
(*     loop runs at [24 + nn] with [rs' <> [] -> 12 <= nn], the function at *)
(*     [16 + (24 + nn)] with [ref_has_redir t = true -> 12 <= nn] -- the    *)
(*     redirect turn's eight words are owed exactly when a redirect was    *)
(*     consumed, so the symbol-free and the pipe shapes are exact          *)
(*     instances at [nn] and the redirect shape at [12 + nn] (A2e).         *)
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
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require UkShCmdalloc.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShParseTok.
Require Import RefParse.
Require Import RefParseSym.
Require Import UkShGettoken.
Require Import UkShRedirCmd.
Require Import UkShRedirs.

Require Import UexecSG.

Section UkShArgs.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).
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
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).

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
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).
  Local Notation ushp_cell := (UkShParseTok.ushp_cell N).
  Local Notation wp_ref_gettoken := (UkShGettoken.wp_ref_gettoken N).
  Local Notation wp_ref_peek := (UkShGettoken.wp_ref_peek N).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_malloc_chain := (UkShRedirs.ushp_malloc_chain N).
  Local Notation ushp_malloc_chain_1 := (UkShRedirs.ushp_malloc_chain_1 N).
  Local Notation ushp_malloc_chain_split := (UkShRedirs.ushp_malloc_chain_split N).
  Local Notation ushp_redirs_at := (UkShRedirs.ushp_redirs_at N).
  Local Notation ushp_redirs_res := (UkShRedirs.ushp_redirs_res N).
  Local Notation ushp_redirs_res_of := (UkShRedirs.ushp_redirs_res_of N).
  Local Notation ushp_redirs_close := (UkShRedirs.ushp_redirs_close N).
  Local Notation wp_ref_parseredirs := (UkShRedirs.wp_ref_parseredirs N).
(*ALIASES-END*)

  (* ===================================================================== *)
  (* (0) WHAT THE TURNS SPEND, AND THE EXIT ROUND'S GETTOKEN RESOURCES      *)
  (* ===================================================================== *)

  (* a loop whose turns consumed no redirect allocates nothing and needs no
     exit payment; otherwise redircmd's malloc may fail and the payment with
     its door is what the turn spends and hands back *)
  Definition ushp_pex_res (rs : list rredir) (Pex : iProp Σ) (K : nat)
      : iProp Σ :=
    match rs with
    | [] => emp%I
    | _ :: _ => (Pex ∗ ushp_oom Pex K)%I
    end.

  Lemma ushp_pex_res_of (rs : list rredir) (Pex : iProp Σ) {K : nat} :
    ushp_oom Pex K -∗ Pex -∗
    ushp_pex_res rs Pex K ∗ (ushp_pex_res rs Pex K -∗ Pex).
  Proof using .
    iIntros "#Hpx Hpay". destruct rs as [| r rs ]; cbn [ushp_pex_res].
    - iSplitR; [ done | ]. iIntros "_". iExact "Hpay".
    - iSplitL "Hpay"; [ iFrame "Hpay Hpx" | ]. iIntros "(Hpay & _)". iExact "Hpay".
  Qed.

  (* a turn that consumed a redirect lends parseredirs the table and the
     payment [UkShRedirs.ushp_redirs_res] asks for; one that consumed none
     lends nothing *)
  Lemma ushp_pex_res_lend (rs : list rredir) (dv : dfrac) (Pex : iProp Σ)
      {K : nat} :
    ushp_pex_res rs Pex K -∗ ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    ushp_redirs_res rs dv Pex K
    ∗ (ushp_redirs_res rs dv Pex K -∗
       ushp_pex_res rs Pex K ∗ ustr γd dv ushp_symbols 7 ushp_sym_f).
  Proof using .
    iIntros "Hres Hsy". destruct rs as [| r rs ]; cbn [ushp_pex_res UkShRedirs.ushp_redirs_res].
    - iSplitR; [ done | ]. iIntros "_". iFrame "Hsy".
    - iDestruct "Hres" as "(Hpay & #Hpx)".
      iSplitL "Hsy Hpay"; [ iFrame "Hsy Hpay Hpx" | ].
      iIntros "(Hsy & Hpay & _)". iFrame "Hsy Hpay Hpx".
  Qed.

  (* the payment at the redirects of one turn and of the rest of the loop,
     out of the payment at all of them: nothing to split at zero, and the
     ONE payment serves both when there is something, because each hands
     it back *)
  Lemma ushp_pex_res_app (rs1 rs2 : list rredir) (Pex : iProp Σ) {K : nat} :
    ushp_pex_res (rs1 ++ rs2) Pex K -∗
    ushp_pex_res rs1 Pex K
    ∗ (ushp_pex_res rs1 Pex K -∗
       ushp_pex_res rs2 Pex K ∗ (ushp_pex_res rs2 Pex K -∗ ushp_pex_res (rs1 ++ rs2) Pex K)).
  Proof using .
    iIntros "Hres". destruct rs1 as [| r1 rs1 ]; cbn [app].
    - iSplitR; [ done | ]. iIntros "_". iFrame "Hres". iIntros "$".
    - cbn [ushp_pex_res]. iDestruct "Hres" as "(Hpay & #Hpx)".
      iSplitL "Hpay"; [ iFrame "Hpay Hpx" | ].
      iIntros "(Hpay & _)".
      iDestruct (ushp_pex_res_of rs2 Pex with "Hpx Hpay") as "[Hres2 Hback]".
      iFrame "Hres2". iIntros "Hres2". iDestruct ("Hback" with "Hres2") as "Hpay".
      iFrame "Hpay Hpx".
  Qed.

  (* the exit round's gettoken resources: the two out-cells and the symbol
     table, which the round touches only when the stop table MISSED *)
  Definition ushp_pex_gtk_in (stop : bool) (dv : dfrac) (fp : Z)
      (wq weq : mword 64) : iProp Σ :=
    if stop then emp%I
    else (uword γd (fp - 120) wq ∗ uword γd (fp - 128) weq
          ∗ ustr γd dv ushp_symbols 7 ushp_sym_f)%I.

  Definition ushp_pex_gtk_out (stop : bool) (dv : dfrac) (fp : Z) : iProp Σ :=
    if stop then emp%I
    else ((∃ w : mword 64, uword γd (fp - 120) w)
          ∗ (∃ w : mword 64, uword γd (fp - 128) w)
          ∗ ustr γd dv ushp_symbols 7 ushp_sym_f)%I.

  (* peek's two tables here, as the reference's lists *)
  Lemma ushp_T_arg_tl :
    [rb_bar; rb_rpar; rb_amp; rb_semi] = ushp_lit ushp_T_arg <$> seq 0%nat 4.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma ushp_T_block_tl : [rb_lpar] = ushp_lit ushp_T_block <$> seq 0%nat 1.
  Proof using . vm_compute. reflexivity. Qed.


  (* ===================================================================== *)
  (* (1) THE ROUND THAT LEAVES THE LOOP                                     *)
  (*                                                                        *)
  (*   0x5fe  c.mv a2,s6        the stop table                              *)
  (*   0x600  c.mv a1,s5        es                                          *)
  (*   0x602  c.mv a0,s4        &s                                          *)
  (*   0x604  jal  424 <peek>   answers [stop]                              *)
  (*   0x608  c.bnez a0,0x63e   TAKEN on a hit -- the loop is done;         *)
  (*   0x60a..0x612  else gettoken(ps, es, &q, &eq), which answers 0, and   *)
  (*   0x616  c.beqz a0,0x63e   TAKEN.                                      *)
  (*                                                                        *)
  (* The round touches neither the node nor s1/s2/s3, so it is stated over  *)
  (* none of them.  The gettoken leg's premises and resources are guarded   *)
  (* by [stop = false] so the round that stops on the table comes back      *)
  (* without them (UkShPipeEx.wp_kshp_pex_bar).                             *)
  (* ===================================================================== *)

  Lemma wp_ref_pex_exit (dq dw dv : dfrac) (s0 ps fp : Z)
      (len : nat) (f : nat -> bv 8) (nn cur : nat) (h : CpuId)
      (mc : regfile) (wq weq : mword 64) (stop : bool) (s q e fin : nat) :
    (cur <= len)%nat ->
    ref_peek len f cur [rb_bar; rb_rpar; rb_amp; rb_semi] = (stop, s) ->
    (stop = false -> ref_sym_scope len f) ->
    (stop = false -> ref_gettoken len f s = (0%Z, q, e, fin)) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    (stop = false ->
     0 < fp - 128 /\ (fp - 128) mod 8 = 0 /\ 0 <= fp /\ fp < Z64) ->
    mc !!! Regidx s4_idx = mword_of_int ps ->
    mc !!! Regidx s5_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int ushp_T_arg ->
    (stop = false -> mc !!! Regidx s7_idx = mword_of_int (fp - 120)) ->
    (stop = false -> mc !!! Regidx s8_idx = mword_of_int (fp - 128)) ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    ushp_pex_gtk_in stop dv fp wq weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun N h mc (mword_of_int 0x5fe) (24 + nn) -∗
    (uword γd ps (mword_of_int (s0 + Z.of_nat (if stop then s else fin))) -∗
     ushp_pex_gtk_out stop dv fp -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun N h' mc' (mword_of_int 0x63e) (24 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hcur Hpk Hscope Hgtk Hs0 Hs64 Hps0 Hps8 Hpssz Hfp Hs4v Hs5v Hs6v Hs7v Hs8v.
    iIntros "#Hcode #Hro Hcur Hin Hstr Hws Hrun Hcont".
    (* ---- 0x5fe  c.mv a2,s6 ---- *)
    iApply (wp_uk_cmv N h mc (mword_of_int 0x5fe) a2_idx
              s6_idx (mword_of_int ushp_T_arg) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6v; symmetry;
                    exact (ushp_mv_val ushp_T_arg))
              with "[] Hrun").
    { iApply (uis_shp_5fe with "Hcode"). }
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_arg : mword 64)]> mc).
    assert (Hk1 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n1 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          exact (upd_ne mc (Regidx a2_idx) (Regidx r) _
                   (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))).
    (* ---- 0x600  c.mv a1,s5 ---- *)
    iApply (wp_uk_cmv N h1 n1 (mword_of_int 0x600) a1_idx
              s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hk1 s5_idx ltac:(vm_compute; reflexivity))
                      Hs5v; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_600 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (n2 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> n1).
    assert (Hk2 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n2 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n1 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk1 r Hr)).
    (* ---- 0x602  c.mv a0,s4 ---- *)
    iApply (wp_uk_cmv N h2 n2 (mword_of_int 0x602) a0_idx
              s4_idx (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hk2 s4_idx ltac:(vm_compute; reflexivity))
                      Hs4v; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_602 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (n3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> n2).
    assert (Hk3 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n3 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n2 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk2 r Hr)).
    (* ---- 0x604  jal 424 <peek> ---- *)
    iApply (wp_uk_jal N h3 n3 (mword_of_int 0x604)
              (mword_of_int 2096672 : mword 21) ra_idx
              (mword_of_int 0x424) (mword_of_int 0x608) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_604 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (n4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x608 : mword 64)]> n3).
    assert (Hk4 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n4 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n3 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk3 r Hr)).
    assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x608);
      [ rewrite (upd_eq n3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x608 : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_4 : n4 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    assert (Ha1_4 : n4 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n1 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    assert (Ha2_4 : n4 !!! Regidx a2_idx = mword_of_int ushp_T_arg);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n1 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq mc (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int ushp_T_arg : mword 64))) | ].
    rewrite <- shpp_peek.
    iApply (wp_ref_peek h4 n4 dq dw true DfracDiscarded ps s0
              ushp_T_arg len cur 4 f (ushp_lit ushp_T_arg)
              (mword_of_int (s0 + Z.of_nat cur)) (14 + nn)
              [rb_bar; rb_rpar; rb_amp; rb_semi] stop s
              Ha0_4 Ha1_4 Ha2_4 Hcur eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_arg; lia)
              ltac:(unfold ushp_T_arg, Z64; lia) Hps0 Hps8 Hpssz
              ushp_T_arg_tl Hpk
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_arg 4 DfracDiscarded
                ushp_T_arg_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h5 n5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    assert (Hk5 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n5 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs45 r Hr); exact (Hk4 r Hr)).
    destruct stop.
    - (* =========== THE STOP TABLE WAS HIT: 0x608 c.bnez TAKEN ============ *)
      iApply (wp_uk_cbnez N h5 n5 (mword_of_int 0x608)
                (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x63e) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_5; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_608 with "Hcode"). }
      iIntros (h6) "Hrun".
      iApply ("Hcont" with "Hcur Hin Hstr Hws [] Hrun").
      iPureIntro. exact Hk5.
    - (* =========== A MISS, THEN gettoken ANSWERS NUL ===================== *)
      specialize (Hscope eq_refl). specialize (Hgtk eq_refl).
      destruct (Hfp eq_refl) as (Hfp0 & Hfp8 & Hfpl & Hfph).
      specialize (Hs7v eq_refl). specialize (Hs8v eq_refl).
      rewrite /ushp_pex_gtk_in. iDestruct "Hin" as "(Hq & Heq & Hsy)".
      assert (Hq0 : 0 < fp - 120) by lia.
      assert (Hq8 : (fp - 120) mod 8 = 0);
        [ replace (fp - 120) with (fp - 128 + 8) by lia;
          rewrite Zplus_mod Hfp8; reflexivity | ].
      assert (Hqz : fp - 120 + 8 < Z64) by lia.
      assert (Hez : fp - 128 + 8 < Z64) by lia.
      assert (Hsle : (s <= len)%nat)
        by (rewrite (ref_peek_miss_inv _ _ _ _ _ Hpk); exact (ref_skip_le len f cur Hcur)).
      (* ---- 0x608  c.bnez a0 -- NOT taken ---- *)
      iApply (wp_uk_cbnez N h5 n5 (mword_of_int 0x608)
                (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx false (mword_of_int 0x63e) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_5; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_608 with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0x60a..0x610  the four argument moves ---- *)
      iApply (wp_uk_cmv N h6 n5 (mword_of_int 0x60a) a3_idx
                s8_idx (mword_of_int (fp - 128)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk5 s8_idx ltac:(vm_compute; reflexivity))
                        Hs8v; symmetry; exact (ushp_mv_val (fp - 128)))
                with "[] Hrun").
      { iApply (uis_shp_60a with "Hcode"). }
      iIntros (h7) "Hrun".
      set (n6 := <[Regidx a3_idx
                   := regval_into_reg
                        (mword_of_int (fp - 128) : mword 64)]> n5).
      assert (Hk6 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n6 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n5 (Regidx a3_idx) (Regidx r) _
                       (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk5 r Hr)).
      iApply (wp_uk_cmv N h7 n6 (mword_of_int 0x60c) a2_idx
                s7_idx (mword_of_int (fp - 120)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk6 s7_idx ltac:(vm_compute; reflexivity))
                        Hs7v; symmetry; exact (ushp_mv_val (fp - 120)))
                with "[] Hrun").
      { iApply (uis_shp_60c with "Hcode"). }
      iIntros (h8) "Hrun".
      set (n7 := <[Regidx a2_idx
                   := regval_into_reg
                        (mword_of_int (fp - 120) : mword 64)]> n6).
      assert (Hk7 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n7 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n6 (Regidx a2_idx) (Regidx r) _
                       (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk6 r Hr)).
      iApply (wp_uk_cmv N h8 n7 (mword_of_int 0x60e) a1_idx
                s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk7 s5_idx ltac:(vm_compute; reflexivity))
                        Hs5v; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_60e with "Hcode"). }
      iIntros (h9) "Hrun".
      set (n8 := <[Regidx a1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat len) : mword 64)]> n7).
      assert (Hk8 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n8 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n7 (Regidx a1_idx) (Regidx r) _
                       (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk7 r Hr)).
      iApply (wp_uk_cmv N h9 n8 (mword_of_int 0x610) a0_idx
                s4_idx (mword_of_int ps) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk8 s4_idx ltac:(vm_compute; reflexivity))
                        Hs4v; symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_610 with "Hcode"). }
      iIntros (h10) "Hrun".
      set (n9 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int ps : mword 64)]> n8).
      assert (Hk9 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n9 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n8 (Regidx a0_idx) (Regidx r) _
                       (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk8 r Hr)).
      (* ---- 0x612  jal 2ec <gettoken> ---- *)
      iApply (wp_uk_jal N h10 n9 (mword_of_int 0x612)
                (mword_of_int 2096346 : mword 21) ra_idx
                (mword_of_int 0x2ec) (mword_of_int 0x616) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_612 with "Hcode"). }
      iIntros (h11) "Hrun".
      set (n10 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x616 : mword 64)]> n9).
      assert (Hk10 : forall r : mword 5, ucallee_saved_idx r = true ->
                       n10 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n9 (Regidx ra_idx) (Regidx r) _
                       (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk9 r Hr)).
      assert (Eret10 : ret_pc (n10 !!! Regidx ra_idx) = mword_of_int 0x616);
        [ rewrite (upd_eq n9 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x616 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_10 : n10 !!! Regidx a0_idx = mword_of_int ps);
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n8 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int ps : mword 64))) | ].
      assert (Ha1_10 : n10 !!! Regidx a1_idx
                       = mword_of_int (s0 + Z.of_nat len));
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n7 (Regidx a1_idx)
                   (regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
      assert (Ha2_10 : n10 !!! Regidx a2_idx = mword_of_int (fp - 120));
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n6 (Regidx a2_idx)
                   (regval_into_reg
                      (mword_of_int (fp - 120) : mword 64))) | ].
      assert (Ha3_10 : n10 !!! Regidx a3_idx = mword_of_int (fp - 128));
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n6 (Regidx a2_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n5 (Regidx a3_idx)
                   (regval_into_reg
                      (mword_of_int (fp - 128) : mword 64))) | ].
      rewrite <- shpp_gettoken.
      iApply (wp_ref_gettoken h11 n10 dq dw dv ps (fp - 120) (fp - 128)
                s0 len s f (mword_of_int (s0 + Z.of_nat s)) wq weq (14 + nn)
                0%Z q e fin
                Ha0_10 Ha1_10 Ha2_10 Ha3_10 Hsle eq_refl Hscope Hs0 Hs64
                Hps0 Hps8 Hpssz Hgtk
                with "Hcode Hcur [Hq] [Heq] Hstr Hws Hsy Hrun").
      { iRight. iSplitR;
          [ iPureIntro; exact (conj Hq0 (conj Hq8 Hqz)) | iExact "Hq" ]. }
      { iRight. iSplitR;
          [ iPureIntro; exact (conj Hfp0 (conj Hfp8 Hez)) | iExact "Heq" ]. }
      iIntros "Hcur Hq Heq Hstr Hws Hsy" (h12 n11) "%Hcs1011 %Ha0_11 Hrun".
      rewrite Eret10.
      iDestruct "Hq" as "[%Hbadq | [_ Hq]]"; [ exfalso; lia | ].
      iDestruct "Heq" as "[%Hbade | [_ Heq]]"; [ exfalso; lia | ].
      assert (Hk11 : forall r : mword 5, ucallee_saved_idx r = true ->
                       n11 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr; rewrite (Hcs1011 r Hr); exact (Hk10 r Hr)).
      (* ---- 0x616  c.beqz a0 -- TAKEN: the line is exhausted ---- *)
      iApply (wp_uk_cbeqz N h12 n11 (mword_of_int 0x616)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x63e) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_11; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_616 with "Hcode"). }
      iIntros (h13) "Hrun".
      iApply ("Hcont" with "Hcur [Hq Heq Hsy] Hstr Hws [] Hrun").
      + rewrite /ushp_pex_gtk_out.
        iSplitL "Hq"; [ iExists _; iExact "Hq" | ].
        iSplitL "Heq"; [ iExists _; iExact "Heq" | ].
        iExact "Hsy".
      + iPureIntro. exact Hk11.
  Qed.

  (* the chain built so far, extended by the chain one turn's parseredirs
     built around its root *)
  Lemma ushp_redirs_at_app (s0 t0 t1 p : Z) (rs0 rs1 : list rredir) :
    ushp_redirs_at s0 t0 p rs0 -∗ ushp_redirs_at s0 t1 t0 rs1 -∗
    ushp_redirs_at s0 t1 p (rs0 ++ rs1).
  Proof using .
    revert p. induction rs0 as [| r rs0 IH ]; intro p;
      cbn [app UkShRedirs.ushp_redirs_at].
    - iIntros "%E H". subst t0. iExact "H".
    - iIntros "(%p1 & Hn & Hrest) H". iExists p1. iFrame "Hn".
      iApply (IH with "Hrest H").
  Qed.


  (* ===================================================================== *)
  (* (2) THE ARGUMENT LOOP, at the reference                                *)
  (*                                                                        *)
  (* THE INVARIANT IS TWO PREDICATES AND ONE EQUATION: the node holds the    *)
  (* tokens consumed so far ([ushp_exec_pre s0 p done]), the REDIR chain    *)
  (* the turns' parseredirs built so far wraps it up to [ret] ([ushp_redirs *)
  (* _at s0 t0 p rs0], s1 = t0), and the reference at the cursor answers    *)
  (* what the loop will have consumed when it leaves.  [s2] is [argc] and   *)
  (* [s3] is [&argv[argc]], both DERIVED from [length done].                *)
  (*                                                                        *)
  (* THE INDUCTION IS ON THE REFERENCE'S FUEL, and RefParseSym.ref_args_inv *)
  (* is the case split: the stop table was hit or gettoken answered NUL     *)
  (* (the two exits, (1)); or a word was consumed and the loop went round.  *)
  (* The two panics are refuted by the equation alone -- a non-word token   *)
  (* and a tenth argument both make the reference answer [None].            *)
  (* ===================================================================== *)

  Lemma wp_ref_pex_loop {Pex : iProp Σ} (dq dw dv : dfrac) (s0 ps p fp : Z)
      (len : nat) (f : nat -> bv 8) (nn : nat) :
    forall (n : nat) (done toks : list (nat * nat)) (rs0 rs' : list rredir)
           (t0 : Z) (cur fin : nat) (UM UM' : iProp Σ) (h : CpuId)
           (mc : regfile) (wq weq : mword 64),
    ref_sym_scope len f ->
    ref_args len f n cur done rs0 = Some (toks, rs0 ++ rs', fin) ->
    ushp_malloc_chain (length rs') UM UM' ->
    (rs' <> [] -> (12 <= nn)%nat) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    0 < fp - 128 -> (fp - 128) mod 8 = 0 -> 0 <= fp -> fp < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (cur <= len)%nat ->
    mc !!! Regidx s0_idx = mword_of_int fp ->
    mc !!! Regidx s1_idx = mword_of_int t0 ->
    mc !!! Regidx s2_idx = mword_of_int (Z.of_nat (length done)) ->
    mc !!! Regidx s3_idx
      = mword_of_int (p + 8 + 8 * Z.of_nat (length done)) ->
    mc !!! Regidx s4_idx = mword_of_int ps ->
    mc !!! Regidx s5_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int ushp_T_arg ->
    mc !!! Regidx s7_idx = mword_of_int (fp - 120) ->
    mc !!! Regidx s8_idx = mword_of_int (fp - 128) ->
    mc !!! Regidx s9_idx = mword_of_int 10 ->
    mc !!! Regidx s10_idx = mword_of_int 97 ->
    mc !!! Regidx s11_idx = mword_of_int p ->
    shp_code γt -∗
    shp_rodata γt -∗
    UM -∗
    ushp_pex_res rs' Pex (nn - 2) -∗
    ushp_exec_pre s0 p done -∗
    ushp_redirs_at s0 t0 p rs0 -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    uword γd (fp - 120) wq -∗
    uword γd (fp - 128) weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h mc (mword_of_int 0x5fe) (24 + nn) -∗
    (∀ t : Z,
     ushp_exec_pre s0 p toks -∗
     ushp_redirs_at s0 t p (rs0 ++ rs') -∗
     uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
     (∃ w : mword 64, uword γd (fp - 120) w) -∗
     (∃ w : mword 64, uword γd (fp - 128) w) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
     UM' -∗
     ushp_pex_res rs' Pex (nn - 2) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
             Regidx r <> Regidx s3_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         ⌜ mc' !!! Regidx s2_idx = mword_of_int (Z.of_nat (length toks)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int t ⌝ -∗
         urun N h' mc' (mword_of_int 0x63e) (24 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intro n.
    induction n as [| n IH ];
      intros done toks rs0 rs' t0 cur fin UM UM' h mc wq weq
        Hscope Href Hchain Hnn Hs0 Hs64 Hps0 Hps8 Hpssz
        Hfp0 Hfp8 Hfpl Hfph Hp0 Hp8 Hpsz Hcur
        Hs0v Hs1v Hs2v Hs3v Hs4v Hs5v Hs6v Hs7v Hs8v Hs9v Hs10v Hs11v;
      [ discriminate Href | ].
    iIntros "#Hcode #Hro HM Hres Hnode Hrat Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    destruct (ref_args_inv len f n cur done toks rs0 (rs0 ++ rs') fin Hcur Href)
      as [ (Hpk & -> & Hrs)
         | [ (s & q & e & Hpk & Hsle & Hgtk & -> & Hrs)
           | (s & q & e & s1 & s2 & rs1 & Hpk & Hsle & Hgtk & Hs1 & Hlen9
              & Hrd & Hs2 & Hrest) ] ].
    - (* =========== THE STOP TABLE WAS HIT: the loop is done ============ *)
      assert (Hrs' : rs' = [])
        by (apply (app_inv_head rs0); rewrite app_nil_r; exact Hrs).
      subst rs'. cbn [length UkShRedirs.ushp_malloc_chain] in Hchain. subst UM'.
      iApply (wp_ref_pex_exit dq dw dv s0 ps fp len f nn cur h mc wq weq
                true fin 0%nat 0%nat 0%nat Hcur Hpk
                ltac:(intro E; discriminate E) ltac:(intro E; discriminate E)
                Hs0 Hs64 Hps0 Hps8 Hpssz
                ltac:(intro E; discriminate E) Hs4v Hs5v Hs6v
                ltac:(intro E; discriminate E) ltac:(intro E; discriminate E)
                with "Hcode Hro Hcur [] Hstr Hws Hrun").
      { done. }
      iIntros "Hcur _ Hstr Hws" (h' mc') "%Hpres Hrun".
      rewrite app_nil_r.
      iApply ("Hcont" $! t0
                with "Hnode Hrat Hcur [Hq] [Heq] Hstr Hws Hsy HM Hres [] [] [] Hrun").
      + iExists wq. iExact "Hq".
      + iExists weq. iExact "Heq".
      + iPureIntro. intros r Hr _ _ _. exact (Hpres r Hr).
      + iPureIntro. rewrite (Hpres s2_idx ltac:(vm_compute; reflexivity)). exact Hs2v.
      + iPureIntro. rewrite (Hpres s1_idx ltac:(vm_compute; reflexivity)). exact Hs1v.
    - (* =========== gettoken ANSWERED NUL: the loop is done ============== *)
      assert (Hrs' : rs' = [])
        by (apply (app_inv_head rs0); rewrite app_nil_r; exact Hrs).
      subst rs'. cbn [length UkShRedirs.ushp_malloc_chain] in Hchain. subst UM'.
      iApply (wp_ref_pex_exit dq dw dv s0 ps fp len f nn cur h mc wq weq
                false s q e fin Hcur Hpk (fun _ => Hscope) (fun _ => Hgtk)
                Hs0 Hs64 Hps0 Hps8 Hpssz
                (fun _ => conj Hfp0 (conj Hfp8 (conj Hfpl Hfph))) Hs4v Hs5v Hs6v
                (fun _ => Hs7v) (fun _ => Hs8v)
                with "Hcode Hro Hcur [Hq Heq Hsy] Hstr Hws Hrun").
      { rewrite /ushp_pex_gtk_in. iFrame "Hq Heq Hsy". }
      iIntros "Hcur Hout Hstr Hws" (h' mc') "%Hpres Hrun".
      rewrite /ushp_pex_gtk_out. iDestruct "Hout" as "(Hq & Heq & Hsy)".
      rewrite app_nil_r.
      iApply ("Hcont" $! t0
                with "Hnode Hrat Hcur Hq Heq Hstr Hws Hsy HM Hres [] [] [] Hrun").
      + iPureIntro. intros r Hr _ _ _. exact (Hpres r Hr).
      + iPureIntro. rewrite (Hpres s2_idx ltac:(vm_compute; reflexivity)). exact Hs2v.
      + iPureIntro. rewrite (Hpres s1_idx ltac:(vm_compute; reflexivity)). exact Hs1v.
    - (* =========== A WORD: store it, run parseredirs, go round ========== *)
      (* the redirects still to come split into this turn's and the rest's *)
      destruct (ref_args_prefix len f n s2 _ _ _ _ _ Hrest) as [ rs'' Hrs'' ].
      assert (Hrs' : rs' = rs1 ++ rs'')
        by (apply (app_inv_head rs0); rewrite app_assoc; exact Hrs'').
      subst rs'. clear Hrs''.
      rewrite length_app in Hchain.
      destruct (ushp_malloc_chain_split (length rs1) (length rs'') UM UM' Hchain)
        as (UM1 & Hchain1 & Hchain2).
      rewrite app_assoc in Hrest.
      iDestruct (ushp_pex_res_app rs1 rs'' Pex with "Hres") as "[Hres1 Hback1]".
      assert (Hnodelen : (length done < 10)%nat) by lia.
      (* ---- the frame's two out-cells are hygienic wherever the frame is -- *)
      assert (Hq0 : 0 < fp - 120) by lia.
      assert (Hq8 : (fp - 120) mod 8 = 0);
        [ replace (fp - 120) with (fp - 128 + 8) by lia;
          rewrite Zplus_mod Hfp8; reflexivity | ].
      assert (Hqz : fp - 120 + 8 < Z64) by lia.
      assert (Hez : fp - 128 + 8 < Z64) by lia.
      assert (Hfp64 : 0 <= fp < Z64) by lia.
      (* ---- 0x5fe  c.mv a2,s6 ---- *)
      iApply (wp_uk_cmv N h mc (mword_of_int 0x5fe) a2_idx
                s6_idx (mword_of_int ushp_T_arg) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs6v; symmetry;
                      exact (ushp_mv_val ushp_T_arg))
                with "[] Hrun").
      { iApply (uis_shp_5fe with "Hcode"). }
      iIntros (h1) "Hrun".
      set (n1 := <[Regidx a2_idx
                   := regval_into_reg
                        (mword_of_int ushp_T_arg : mword 64)]> mc).
      assert (Hk1 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n1 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            exact (upd_ne mc (Regidx a2_idx) (Regidx r) _
                     (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))).
      (* ---- 0x600  c.mv a1,s5 ---- *)
      iApply (wp_uk_cmv N h1 n1 (mword_of_int 0x600) a1_idx
                s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk1 s5_idx ltac:(vm_compute; reflexivity))
                        Hs5v; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_600 with "Hcode"). }
      iIntros (h2) "Hrun".
      set (n2 := <[Regidx a1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat len) : mword 64)]> n1).
      assert (Hk2 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n2 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n1 (Regidx a1_idx) (Regidx r) _
                       (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk1 r Hr)).
      (* ---- 0x602  c.mv a0,s4 ---- *)
      iApply (wp_uk_cmv N h2 n2 (mword_of_int 0x602) a0_idx
                s4_idx (mword_of_int ps) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk2 s4_idx ltac:(vm_compute; reflexivity))
                        Hs4v; symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_602 with "Hcode"). }
      iIntros (h3) "Hrun".
      set (n3 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int ps : mword 64)]> n2).
      assert (Hk3 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n3 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n2 (Regidx a0_idx) (Regidx r) _
                       (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk2 r Hr)).
      (* ---- 0x604  jal 424 <peek> ---- *)
      iApply (wp_uk_jal N h3 n3 (mword_of_int 0x604)
                (mword_of_int 2096672 : mword 21) ra_idx
                (mword_of_int 0x424) (mword_of_int 0x608) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_604 with "Hcode"). }
      iIntros (h4) "Hrun".
      set (n4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x608 : mword 64)]> n3).
      assert (Hk4 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n4 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n3 (Regidx ra_idx) (Regidx r) _
                       (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk3 r Hr)).
      assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x608);
        [ rewrite (upd_eq n3 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x608 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_4 : n4 !!! Regidx a0_idx = mword_of_int ps);
        [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n2 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int ps : mword 64))) | ].
      assert (Ha1_4 : n4 !!! Regidx a1_idx
                      = mword_of_int (s0 + Z.of_nat len));
        [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n1 (Regidx a1_idx)
                   (regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
      assert (Ha2_4 : n4 !!! Regidx a2_idx = mword_of_int ushp_T_arg);
        [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n1 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq mc (Regidx a2_idx)
                   (regval_into_reg
                      (mword_of_int ushp_T_arg : mword 64))) | ].
      rewrite <- shpp_peek.
      iApply (wp_ref_peek h4 n4 dq dw true DfracDiscarded ps s0
                ushp_T_arg len cur 4 f (ushp_lit ushp_T_arg)
                (mword_of_int (s0 + Z.of_nat cur)) (14 + nn)
                [rb_bar; rb_rpar; rb_amp; rb_semi] false s
                Ha0_4 Ha1_4 Ha2_4 Hcur eq_refl Hs0 Hs64
                ltac:(unfold ushp_T_arg; lia)
                ltac:(unfold ushp_T_arg, Z64; lia) Hps0 Hps8 Hpssz
                ushp_T_arg_tl Hpk
                with "Hcode Hcur Hstr Hws [] Hrun").
      { iApply (ushp_lit_str ushp_T_arg 4 DfracDiscarded
                  ushp_T_arg_ok ltac:(cbn; lia) with "Hro"). }
      iIntros "Hcur Hstr Hws _" (h5 n5) "%Hcs45 %Ha0_5 Hrun".
      rewrite Eret4.
      assert (Hk5 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n5 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr; rewrite (Hcs45 r Hr); exact (Hk4 r Hr)).
      (* ---- 0x608  c.bnez a0 -- NOT taken: the guard missed ---- *)
      iApply (wp_uk_cbnez N h5 n5 (mword_of_int 0x608)
                (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx false (mword_of_int 0x63e) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_5; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_608 with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0x60a..0x610  the four argument moves ---- *)
      iApply (wp_uk_cmv N h6 n5 (mword_of_int 0x60a) a3_idx
                s8_idx (mword_of_int (fp - 128)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk5 s8_idx ltac:(vm_compute; reflexivity))
                        Hs8v; symmetry; exact (ushp_mv_val (fp - 128)))
                with "[] Hrun").
      { iApply (uis_shp_60a with "Hcode"). }
      iIntros (h7) "Hrun".
      set (n6 := <[Regidx a3_idx
                   := regval_into_reg
                        (mword_of_int (fp - 128) : mword 64)]> n5).
      assert (Hk6 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n6 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n5 (Regidx a3_idx) (Regidx r) _
                       (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk5 r Hr)).
      iApply (wp_uk_cmv N h7 n6 (mword_of_int 0x60c) a2_idx
                s7_idx (mword_of_int (fp - 120)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk6 s7_idx ltac:(vm_compute; reflexivity))
                        Hs7v; symmetry; exact (ushp_mv_val (fp - 120)))
                with "[] Hrun").
      { iApply (uis_shp_60c with "Hcode"). }
      iIntros (h8) "Hrun".
      set (n7 := <[Regidx a2_idx
                   := regval_into_reg
                        (mword_of_int (fp - 120) : mword 64)]> n6).
      assert (Hk7 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n7 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n6 (Regidx a2_idx) (Regidx r) _
                       (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk6 r Hr)).
      iApply (wp_uk_cmv N h8 n7 (mword_of_int 0x60e) a1_idx
                s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk7 s5_idx ltac:(vm_compute; reflexivity))
                        Hs5v; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_60e with "Hcode"). }
      iIntros (h9) "Hrun".
      set (n8 := <[Regidx a1_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat len) : mword 64)]> n7).
      assert (Hk8 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n8 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n7 (Regidx a1_idx) (Regidx r) _
                       (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk7 r Hr)).
      iApply (wp_uk_cmv N h9 n8 (mword_of_int 0x610) a0_idx
                s4_idx (mword_of_int ps) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk8 s4_idx ltac:(vm_compute; reflexivity))
                        Hs4v; symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_610 with "Hcode"). }
      iIntros (h10) "Hrun".
      set (n9 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int ps : mword 64)]> n8).
      assert (Hk9 : forall r : mword 5, ucallee_saved_idx r = true ->
                      n9 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n8 (Regidx a0_idx) (Regidx r) _
                       (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk8 r Hr)).
      (* ---- 0x612  jal 2ec <gettoken> ---- *)
      iApply (wp_uk_jal N h10 n9 (mword_of_int 0x612)
                (mword_of_int 2096346 : mword 21) ra_idx
                (mword_of_int 0x2ec) (mword_of_int 0x616) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_612 with "Hcode"). }
      iIntros (h11) "Hrun".
      set (n10 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x616 : mword 64)]> n9).
      assert (Hk10 : forall r : mword 5, ucallee_saved_idx r = true ->
                       n10 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n9 (Regidx ra_idx) (Regidx r) _
                       (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
            exact (Hk9 r Hr)).
      assert (Eret10 : ret_pc (n10 !!! Regidx ra_idx) = mword_of_int 0x616);
        [ rewrite (upd_eq n9 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x616 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_10 : n10 !!! Regidx a0_idx = mword_of_int ps);
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n8 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int ps : mword 64))) | ].
      assert (Ha1_10 : n10 !!! Regidx a1_idx
                       = mword_of_int (s0 + Z.of_nat len));
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n7 (Regidx a1_idx)
                   (regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
      assert (Ha2_10 : n10 !!! Regidx a2_idx = mword_of_int (fp - 120));
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n6 (Regidx a2_idx)
                   (regval_into_reg
                      (mword_of_int (fp - 120) : mword 64))) | ].
      assert (Ha3_10 : n10 !!! Regidx a3_idx = mword_of_int (fp - 128));
        [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n6 (Regidx a2_idx) (Regidx a3_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n5 (Regidx a3_idx)
                   (regval_into_reg
                      (mword_of_int (fp - 128) : mword 64))) | ].
      rewrite <- shpp_gettoken.
      iApply (wp_ref_gettoken h11 n10 dq dw dv ps (fp - 120) (fp - 128)
                s0 len s f (mword_of_int (s0 + Z.of_nat s)) wq weq (14 + nn)
                rt_word q e s1
                Ha0_10 Ha1_10 Ha2_10 Ha3_10 Hsle eq_refl Hscope Hs0 Hs64
                Hps0 Hps8 Hpssz Hgtk
                with "Hcode Hcur [Hq] [Heq] Hstr Hws Hsy Hrun").
      { iRight. iSplitR;
          [ iPureIntro; exact (conj Hq0 (conj Hq8 Hqz)) | iExact "Hq" ]. }
      { iRight. iSplitR;
          [ iPureIntro; exact (conj Hfp0 (conj Hfp8 Hez)) | iExact "Heq" ]. }
      iIntros "Hcur Hq Heq Hstr Hws Hsy" (h12 n11) "%Hcs1011 %Ha0_11 Hrun".
      rewrite Eret10.
      iDestruct "Hq" as "[%Hbadq | [_ Hq]]"; [ exfalso; lia | ].
      iDestruct "Heq" as "[%Hbade | [_ Heq]]"; [ exfalso; lia | ].
      assert (Hk11 : forall r : mword 5, ucallee_saved_idx r = true ->
                       n11 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr; rewrite (Hcs1011 r Hr); exact (Hk10 r Hr)).
      (* ---- 0x616  c.beqz a0 -- NOT taken: a token came back ---- *)
      iApply (wp_uk_cbeqz N h12 n11 (mword_of_int 0x616)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx false (mword_of_int 0x63e) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_11; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_616 with "Hcode"). }
      iIntros (h13) "Hrun".
      (* ---- 0x618  bne a0,s10 -- NOT taken: the token IS a word ---- *)
      iApply (wp_uk_btype N h13 n11 (mword_of_int 0x618)
                (mword_of_int 8140 : mword 13) s10_idx a0_idx BNE false
                (mword_of_int 0x5e4) (24 + nn)
                ltac:(cbn [uv_btaken]; rewrite Ha0_11
                        (Hk11 s10_idx ltac:(vm_compute; reflexivity)) Hs10v;
                      vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_618 with "Hcode"). }
      iIntros (h14) "Hrun".
      (* ---- 0x61c  ld a5,-120(s0) -- q ---- *)
      assert (Hs0_11 : n11 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk11 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld N h14 n11 (mword_of_int 0x61c)
                (mword_of_int 3976 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 120) (mword_of_int (s0 + Z.of_nat q)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_11 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hq8
                ltac:(vm_compute; discriminate)
                with "[] Hq Hrun").
      { iApply (uis_shp_61c with "Hcode"). }
      iIntros "Hq" (h15) "Hrun".
      set (n12 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat q) : mword 64)]> n11).
      assert (Hk12 : forall r : mword 5, ucallee_saved_idx r = true ->
                 n12 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n11 (Regidx a5_idx) (Regidx r) _
                       (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk11 r Hr)).
      assert (Ha5_12 : n12 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat q))
        by exact (upd_eq n11 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat q) : mword 64))).
      assert (Hs3_12 : n12 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk12 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3v).
      (* ---- 0x620  sd a5,0(s3) -- argv[argc] = q ---- *)
      iDestruct "Hnode" as "(%Hdl & _ & _ & Hty & Hav & Hev)".
      iDestruct (ushp_slots_upd s0 (p + 8) done (q, e) fst Hnodelen with "Hav")
        as "[Hav0 Havc]".
      iApply (wp_uk_sd N h15 n12 (mword_of_int 0x620)
                (mword_of_int 0 : mword 12) s3_idx a5_idx
                (p + 8 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + nn)
                ltac:(rewrite Hs3_12
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (length done) Hp8))
                with "[] [Hav0] Hrun").
      { iApply (uis_shp_620 with "Hcode"). }
      { iExact "Hav0". }
      iIntros "Hav0" (h16) "Hrun".
      rewrite Ha5_12.
      iDestruct ("Havc" with "[Hav0]") as "Hav"; [ cbn [fst]; iExact "Hav0" | ].
      (* ---- 0x624  ld a5,-128(s0) -- eq ---- *)
      assert (Hs0_12 : n12 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk12 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld N h16 n12 (mword_of_int 0x624)
                (mword_of_int 3968 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 128) (mword_of_int (s0 + Z.of_nat e)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_12 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hfp8
                ltac:(vm_compute; discriminate)
                with "[] Heq Hrun").
      { iApply (uis_shp_624 with "Hcode"). }
      iIntros "Heq" (h17) "Hrun".
      set (n13 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat e) : mword 64)]> n12).
      assert (Hk13 : forall r : mword 5, ucallee_saved_idx r = true ->
                 n13 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n12 (Regidx a5_idx) (Regidx r) _
                       (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk12 r Hr)).
      assert (Ha5_13 : n13 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat e))
        by exact (upd_eq n12 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat e) : mword 64))).
      assert (Hs3_13 : n13 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk13 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3v).
      (* ---- 0x628  sd a5,80(s3) -- eargv[argc] = eq ---- *)
      iDestruct (ushp_slots_upd s0 (p + 88) done (q, e) snd Hnodelen with "Hev")
        as "[Hev0 Hevc]".
      iApply (wp_uk_sd N h17 n13 (mword_of_int 0x628)
                (mword_of_int 80 : mword 12) s3_idx a5_idx
                (p + 88 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + nn)
                ltac:(rewrite Hs3_13
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 11 (length done) Hp8))
                with "[] [Hev0] Hrun").
      { iApply (uis_shp_628 with "Hcode"). }
      { iExact "Hev0". }
      iIntros "Hev0" (h18) "Hrun".
      rewrite Ha5_13.
      iDestruct ("Hevc" with "[Hev0]") as "Hev"; [ cbn [snd]; iExact "Hev0" | ].
      (* ---- 0x62c  c.addiw s2,s2,1 -- argc++ ---- *)
      assert (Hs2_13 : n13 !!! Regidx s2_idx
                       = mword_of_int (Z.of_nat (length done)))
        by (rewrite (Hk13 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2v).
      assert (Esx : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                    = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddiw N h18 n13 (mword_of_int 0x62c)
                (mword_of_int 1 : mword 6) s2_idx
                (mword_of_int (Z.of_nat (length done) + 1)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_13 Esx; symmetry;
                      exact (moi_addw (Z.of_nat (length done)) 1
                               ltac:(unfold Z31; lia)))
                with "[] Hrun").
      { iApply (uis_shp_62c with "Hcode"). }
      iIntros (h19) "Hrun".
      set (n14 := <[Regidx s2_idx
                    := regval_into_reg
                         (mword_of_int (Z.of_nat (length done) + 1)
                          : mword 64)]> n13).
      assert (Hk14 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx ->
                 n14 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2;
            rewrite (upd_ne n13 (Regidx s2_idx) (Regidx r) _ Hr2);
            exact (Hk13 r Hr)).
      assert (Hs2_14 : n14 !!! Regidx s2_idx
                       = mword_of_int (Z.of_nat (length done) + 1))
        by exact (upd_eq n13 (Regidx s2_idx)
                    (regval_into_reg
                       (mword_of_int (Z.of_nat (length done) + 1)
                        : mword 64))).
      (* ---- 0x62e  bne s2,s9 -- TAKEN: MAXARGS is not reached ---- *)
      iApply (wp_uk_btype N h19 n14 (mword_of_int 0x62e)
                (mword_of_int 8130 : mword 13) s9_idx s2_idx BNE true
                (mword_of_int 0x5f0) (24 + nn)
                ltac:(cbn [uv_btaken]; rewrite Hs2_14
                        (Hk14 s9_idx ltac:(vm_compute; reflexivity)
                           ltac:(vm_compute; discriminate)) Hs9v;
                      rewrite (moi_neq_vec (Z.of_nat (length done) + 1) 10
                                 ltac:(unfold Z64; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hne : (Z.of_nat (length done) + 1 =? 10)
                                    = false)
                        by (apply Z.eqb_neq; lia);
                      rewrite Hne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_62e with "Hcode"). }
      iIntros (h20) "Hrun".
      (* ---- 0x5f0  c.addi s3,s3,8 ---- *)
      assert (Hs3_14 : n14 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk14 s3_idx ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; discriminate)); exact Hs3v).
      assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                     = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi N h20 n14 (mword_of_int 0x5f0)
                (mword_of_int 8 : mword 6) s3_idx
                (mword_of_int (p + 8 + 8 * Z.of_nat (length done) + 8))
                (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_14 Esx8; symmetry; apply moi_add)
                with "[] Hrun").
      { iApply (uis_shp_5f0 with "Hcode"). }
      iIntros (h21) "Hrun".
      set (n15 := <[Regidx s3_idx
                    := regval_into_reg
                         (mword_of_int
                            (p + 8 + 8 * Z.of_nat (length done) + 8)
                          : mword 64)]> n14).
      assert (Hk15 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n15 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n14 (Regidx s3_idx) (Regidx r) _ Hr3);
            exact (Hk14 r Hr Hr2)).
      (* ---- 0x5f2..0x5f6  parseredirs(ret, ps, es) ---- *)
      iApply (wp_uk_cmv N h21 n15 (mword_of_int 0x5f2) a2_idx
                s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk15 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs5v;
                      symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_5f2 with "Hcode"). }
      iIntros (h22) "Hrun".
      set (n16 := <[Regidx a2_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat len)
                          : mword 64)]> n15).
      assert (Hk16 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n16 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n15 (Regidx a2_idx) (Regidx r) _
                       (ushp_cs_ne r a2_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk15 r Hr Hr2 Hr3)).
      iApply (wp_uk_cmv N h22 n16 (mword_of_int 0x5f4) a1_idx
                s4_idx (mword_of_int ps) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk16 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs4v;
                      symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_5f4 with "Hcode"). }
      iIntros (h23) "Hrun".
      set (n17 := <[Regidx a1_idx
                    := regval_into_reg (mword_of_int ps : mword 64)]> n16).
      assert (Hk17 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n17 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n16 (Regidx a1_idx) (Regidx r) _
                       (ushp_cs_ne r a1_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk16 r Hr Hr2 Hr3)).
      iApply (wp_uk_cmv N h23 n17 (mword_of_int 0x5f6) a0_idx
                s1_idx (mword_of_int t0) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk17 s1_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs1v;
                      symmetry; exact (ushp_mv_val t0))
                with "[] Hrun").
      { iApply (uis_shp_5f6 with "Hcode"). }
      iIntros (h24) "Hrun".
      set (n18 := <[Regidx a0_idx
                    := regval_into_reg (mword_of_int t0 : mword 64)]> n17).
      assert (Hk18 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n18 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n17 (Regidx a0_idx) (Regidx r) _
                       (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk17 r Hr Hr2 Hr3)).
      (* ---- 0x5f8  jal 488 <parseredirs> ---- *)
      iApply (wp_uk_jal N h24 n18 (mword_of_int 0x5f8)
                (mword_of_int 2096784 : mword 21) ra_idx
                (mword_of_int 0x488) (mword_of_int 0x5fc) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_5f8 with "Hcode"). }
      iIntros (h25) "Hrun".
      set (n19 := <[Regidx ra_idx
                    := regval_into_reg
                         (mword_of_int 0x5fc : mword 64)]> n18).
      assert (Hk19 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n19 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n18 (Regidx ra_idx) (Regidx r) _
                       (ushp_cs_ne r ra_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk18 r Hr Hr2 Hr3)).
      assert (Eret19 : ret_pc (n19 !!! Regidx ra_idx)
                       = mword_of_int 0x5fc);
        [ rewrite (upd_eq n18 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x5fc : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_19 : n19 !!! Regidx a0_idx = mword_of_int t0);
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n17 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int t0 : mword 64))) | ].
      assert (Ha1_19 : n19 !!! Regidx a1_idx = mword_of_int ps);
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n17 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n16 (Regidx a1_idx)
                   (regval_into_reg (mword_of_int ps : mword 64))) | ].
      assert (Ha2_19 : n19 !!! Regidx a2_idx
                       = mword_of_int (s0 + Z.of_nat len));
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n17 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n16 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n15 (Regidx a2_idx)
                   (regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
      rewrite <- shpp_parseredirs.
      (* the turn lends parseredirs the table and the payment it asks for
         at the redirects it consumes, and nothing at none *)
      iDestruct (ushp_pex_res_lend rs1 dv Pex with "Hres1 Hsy") as "[Hrres Hback2]".
      iApply (wp_ref_parseredirs h25 n19 dq dw dv t0 ps s0 len s1 n s2 f rs1
                UM UM1 (mword_of_int (s0 + Z.of_nat s1)) nn
                Ha0_19 Ha1_19 Ha2_19 Hs1 eq_refl Hrd Hchain1
                (fun _ => Hscope)
                (fun Hne => Hnn (app_ne_l rs1 rs'' Hne))
                Hs0 Hs64
                Hps0 Hps8 Hpssz
                with "Hcode Hro HM Hrres Hcur Hstr Hws Hrun").
      iIntros (t1) "Hcur Hstr Hws Hat HM1 Hrres".
      iIntros (h26 n20) "%Hcs1920 %Ha0_20 Hrun".
      rewrite Eret19.
      iDestruct ("Hback2" with "Hrres") as "[Hres1 Hsy]".
      iDestruct ("Hback1" with "Hres1") as "[Hres2 Hback3]".
      iDestruct (ushp_redirs_at_app s0 t0 t1 p rs0 rs1 with "Hrat Hat") as "Hrat".
      assert (Hk20 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n20 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3; rewrite (Hcs1920 r Hr);
            exact (Hk19 r Hr Hr2 Hr3)).
      (* ---- 0x5fc  c.mv s1,a0 -- ret = what parseredirs returned ---- *)
      iApply (wp_uk_cmv N h26 n20 (mword_of_int 0x5fc) s1_idx
                a0_idx (mword_of_int t1) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_20; symmetry; exact (ushp_mv_val t1))
                with "[] Hrun").
      { iApply (uis_shp_5fc with "Hcode"). }
      iIntros (h27) "Hrun".
      set (n21 := <[Regidx s1_idx
                    := regval_into_reg (mword_of_int t1 : mword 64)]> n20).
      assert (Hk21 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
                 Regidx r <> Regidx s3_idx ->
                 n21 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr1 Hr2 Hr3;
            rewrite (upd_ne n20 (Regidx s1_idx) (Regidx r) _ Hr1);
            exact (Hk20 r Hr Hr2 Hr3)).
      assert (Hs3_15 : n15 !!! Regidx s3_idx
                       = mword_of_int
                           (p + 8 + 8 * Z.of_nat (length done) + 8))
        by exact (upd_eq n14 (Regidx s3_idx)
                    (regval_into_reg
                       (mword_of_int
                          (p + 8 + 8 * Z.of_nat (length done) + 8)
                        : mword 64))).
      assert (HIs3 : n21 !!! Regidx s3_idx
                     = mword_of_int
                         (p + 8 + 8 * Z.of_nat (length (done ++ [(q, e)])))).
      { rewrite ushp_len_app1.
        rewrite (upd_ne n20 (Regidx s1_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (Hcs1920 s3_idx ltac:(vm_compute; reflexivity)).
        rewrite (upd_ne n18 (Regidx ra_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n17 (Regidx a0_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n16 (Regidx a1_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n15 (Regidx a2_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Hs3_15. f_equal. rewrite Nat2Z.inj_succ. lia. }
      (* ---- and round again, with the token banked ---- *)
      iApply (IH (done ++ [(q, e)]) toks (rs0 ++ rs1) rs'' t1 s2 fin UM1 UM'
                h27 n21
                (mword_of_int (s0 + Z.of_nat q))
                (mword_of_int (s0 + Z.of_nat e))
                Hscope Hrest Hchain2
                (fun Hne => Hnn (app_ne_r rs1 rs'' Hne))
                Hs0 Hs64 Hps0 Hps8 Hpssz Hfp0 Hfp8 Hfpl Hfph
                Hp0 Hp8 Hpsz Hs2
                ltac:(rewrite (Hk21 s0_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs0v)
                ltac:(exact (upd_eq n20 (Regidx s1_idx)
                               (regval_into_reg (mword_of_int t1 : mword 64))))
                ltac:(rewrite ushp_len_app1;
                      rewrite (upd_ne n20 (Regidx s1_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hcs1920 s2_idx ltac:(vm_compute; reflexivity));
                      rewrite (upd_ne n18 (Regidx ra_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n17 (Regidx a0_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n16 (Regidx a1_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n15 (Regidx a2_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n14 (Regidx s3_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite Hs2_14; f_equal; lia)
                HIs3
                ltac:(rewrite (Hk21 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4v)
                ltac:(rewrite (Hk21 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5v)
                ltac:(rewrite (Hk21 s6_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs6v)
                ltac:(rewrite (Hk21 s7_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs7v)
                ltac:(rewrite (Hk21 s8_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs8v)
                ltac:(rewrite (Hk21 s9_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs9v)
                ltac:(rewrite (Hk21 s10_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs10v)
                ltac:(rewrite (Hk21 s11_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs11v)
                with "Hcode Hro HM1 Hres2 [Hty Hav Hev] Hrat Hcur Hq Heq Hstr Hws Hsy Hrun").
      { rewrite /ushp_exec_pre.
        iSplitR; [ iPureIntro; rewrite ushp_len_app1; lia | ].
        iSplitR; [ iPureIntro; exact Hp0 | ].
        iSplitR; [ iPureIntro; exact Hp8 | ].
        iFrame "Hav Hev". rewrite /ushp_type_at. iExact "Hty". }
      iIntros (t) "Hnode Hrat Hcur Hq Heq Hstr Hws Hsy HM' Hres2".
      iIntros (hf mf) "%Hpres %Hs2f %Hs1f Hrun".
      iDestruct ("Hback3" with "Hres2") as "Hres".
      rewrite <- app_assoc.
      iApply ("Hcont" $! t
                with "Hnode Hrat Hcur Hq Heq Hstr Hws Hsy HM' Hres [] [] [] Hrun").
      + iPureIntro. intros r Hr Hr1 Hr2 Hr3.
        rewrite (Hpres r Hr Hr1 Hr2 Hr3). exact (Hk21 r Hr Hr1 Hr2 Hr3).
      + iPureIntro. exact Hs2f.
      + iPureIntro. exact Hs1f.
  Qed.



  (* ===================================================================== *)
  (* (3) parseexec @0x56c, THE WHOLE FUNCTION, at the reference             *)
  (*                                                                        *)
  (* THE FRAME IS SPLIT IN TWO, BOTH WAYS.  gcc spills ra/s0/s1/s4/s5        *)
  (* before the [peek(ps,es,LPAREN)] that decides whether this is a block,   *)
  (* and the other eight only on the fall-through -- so the [parseblock]    *)
  (* arm pays for five saves instead of thirteen.  The restores mirror it:  *)
  (* the eight come back at 0x64c and the five at 0x5d6, and the [c.j 0x5d4] *)
  (* between them is the join.  So the frame is four separate runs over    *)
  (* UkShParse's two, at the SLOT ADDRESSES rather than at consecutive      *)
  (* indexes.                                                               *)
  (*                                                                        *)
  (* WHAT IT RETURNS is [ret], re-rooted by every parseredirs that turned:  *)
  (* a0 holds the outermost node of the chain [rs] around the EXEC node,   *)
  (* while [cmd] (s11) still names the EXEC node, which is what the two     *)
  (* terminator stores go through after the loop.  The answer keeps the    *)
  (* two apart -- [ushp_exec_at] at the named EXEC address with its bound, *)
  (* [ushp_redirs_at] around it -- because the landed redirect tier hands   *)
  (* its caller exactly that and [ushp_tree] does not carry the bounds     *)
  (* back out; [wp_ref_parseexec_tree] below is the closed form.           *)
  (*                                                                        *)
  (* THE ALLOCATIONS are one per node of the answer: execcmd's, then one    *)
  (* per redirect the two parseredirs consumed, chained.                    *)
  (* ===================================================================== *)
  Lemma wp_ref_parseexec {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len off n fin : nat) (f : nat -> bv 8)
      (w0 : mword 64) (t : ushp_cmd) (UM UM' : iProp Σ) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope len f ->
    ref_parseexec len f n off = Some (t, fin) ->
    ushp_malloc_chain (ushp_nodes t) UM UM' ->
    (ref_has_redir t = true -> (12 <= nn)%nat) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    ushp_oom Pex (nn - 2) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parseexec) (16 + (24 + nn)) -∗
    (∀ (root p : Z) (toks : list (nat * nat)) (rs : list rredir),
       ⌜ t = ref_wrap (UshpExec toks) rs ⌝ -∗
       ⌜ p + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 p toks -∗
       ushp_redirs_at s0 root p rs -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int root ⌝ -∗
           UM' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (16 + (24 + nn)) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hoffle Hw0 Hscope Href Hchain Hnn Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    (* ---- the reference's answer, taken apart: the '(' peek MISSED (a hit
       is [None]), parseredirs ran at the skipped cursor, then the loop ---- *)
    unfold ref_parseexec in Href.
    destruct (ref_peek len f off [rb_lpar]) as [ blk s ] eqn:Epk.
    destruct blk; [ discriminate Href | ].
    destruct (ref_redirs len f n s []) as [[ rs_l s1 ] | ] eqn:Erd;
      [ | discriminate Href ].
    destruct (ref_args len f n s1 [] rs_l) as [[[ toks rs_tot ] s2 ] | ] eqn:Eargs;
      [ | discriminate Href ].
    injection Href as Ht Hfin. subst t fin.
    destruct (ref_args_prefix len f n s1 [] toks rs_l rs_tot s2 Eargs) as [ rs' Hrs' ].
    subst rs_tot.
    assert (Hs : (s <= len)%nat)
      by (rewrite (ref_peek_miss_inv _ _ _ _ _ Epk); exact (ref_skip_le len f off Hoffle)).
    assert (Hs1 : (s1 <= len)%nat) by exact (ref_redirs_fin_le len f n s [] rs_l s1 Hs Erd).
    (* ---- the allocations: execcmd's, then one per redirect ---- *)
    rewrite ushp_nodes_wrap in Hchain. cbn [ushp_nodes] in Hchain.
    rewrite length_app in Hchain.
    destruct (ushp_malloc_chain_split 1 (length rs_l + length rs') UM UM' Hchain)
      as (UM1 & Hch0 & Hch12).
    destruct (ushp_malloc_chain_split (length rs_l) (length rs') UM1 UM' Hch12)
      as (UM2 & Hch1 & Hch2).
    destruct Hch0 as (UM1' & Hok0 & E1). cbn [UkShRedirs.ushp_malloc_chain] in E1.
    subst UM1'.
    rewrite shpp_parseexec.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 128 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    (* ---- 0x56c  c.addi16sp sp,sp,-128 ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x56c)
              (mword_of_int 56 : mword 6) 16 (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_56c with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 16))).
    assert (Hspu : uint spn = uint sp0 - 128).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 16)) with (-128) by lia.
      exact (uv_avi_neg sp0 128 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 104) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 104)
      by (unfold spl; apply uint_moi; lia).
    set (sp3 := (mword_of_int (uint sp0 - 128) : mword 64)).
    assert (Hsp3u : uint sp3 = uint sp0 - 128)
      by (unfold sp3; apply uint_moi; lia).
    (* ---- the frame, cut into thirteen spill slots and three locals ---- *)
    iDestruct (ushp_frame_split sp0 spl 3 [(ra_idx, mword_of_int 15 : mword 6);
                 (s0_idx, mword_of_int 14 : mword 6);
                 (s1_idx, mword_of_int 13 : mword 6);
                 (s2_idx, mword_of_int 12 : mword 6);
                 (s3_idx, mword_of_int 11 : mword 6);
                 (s4_idx, mword_of_int 10 : mword 6);
                 (s5_idx, mword_of_int 9 : mword 6);
                 (s6_idx, mword_of_int 8 : mword 6);
                 (s7_idx, mword_of_int 7 : mword 6);
                 (s8_idx, mword_of_int 6 : mword 6);
                 (s9_idx, mword_of_int 5 : mword 6);
                 (s10_idx, mword_of_int 4 : mword 6);
                 (s11_idx, mword_of_int 3 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    iDestruct (ushp_frame_split spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hloc") as "[Hlc Hbot]".
    (* [iEval ... in "H"] and NOT a bare [rewrite]: ssr's [!] repeats over
       the WHOLE [envs_entails], so one such rewrite re-walks every OTHER
       [big_sepL] in the context as well.  Per hypothesis it is the same
       law at a fraction of the cost (7.6 s -> 1.7 s at the pair below). *)
    iEval (rewrite !big_sepL_cons big_sepL_nil) in "Hsl".
    iEval (rewrite !big_sepL_cons big_sepL_nil) in "Hlc".
    iDestruct "Hsl" as "(C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 &
                         C10 & C11 & C12 & _)".
    iDestruct "Hlc" as "([%wl0 L0] & [%wq Lq] & [%weq Leq] & _)".
    assert (E0 : uint sp0 - 104 - 8 * (Z.of_nat 0 + 1) = uint sp0 - 112)
      by lia.
    assert (E1 : uint sp0 - 104 - 8 * (Z.of_nat 1 + 1) = uint sp0 - 120)
      by lia.
    assert (E2 : uint sp0 - 104 - 8 * (Z.of_nat 2 + 1) = uint sp0 - 128)
      by lia.
    rewrite Hsplu E0 E1 E2.
    set (valsA := fun i : nat =>
                    match i with
                    | 0%nat => m !!! Regidx ra_idx
                    | 1%nat => m !!! Regidx s0_idx
                    | 2%nat => m !!! Regidx s1_idx
                    | 3%nat => m !!! Regidx s4_idx
                    | _ => m !!! Regidx s5_idx end).
    set (valsB := fun i : nat =>
                    match i with
                    | 0%nat => m !!! Regidx s2_idx
                    | 1%nat => m !!! Regidx s3_idx
                    | 2%nat => m !!! Regidx s6_idx
                    | 3%nat => m !!! Regidx s7_idx
                    | 4%nat => m !!! Regidx s8_idx
                    | 5%nat => m !!! Regidx s9_idx
                    | 6%nat => m !!! Regidx s10_idx
                    | _ => m !!! Regidx s11_idx end).
    set (adA := fun i : nat =>
                  uint sp0 - 8 * (Z.of_nat (match i with
                                            | 0%nat => 0 | 1%nat => 1
                                            | 2%nat => 2 | 3%nat => 5
                                            | _ => 6 end) + 1)).
    set (adB := fun i : nat =>
                  uint sp0 - 8 * (Z.of_nat (match i with
                                            | 0%nat => 3 | 1%nat => 4
                                            | 2%nat => 7 | 3%nat => 8
                                            | 4%nat => 9 | 5%nat => 10
                                            | 6%nat => 11
                                            | _ => 12 end) + 1)).
    (* ---- 0x56e..0x576  the FIRST five spills ---- *)
    iApply (wp_kshp_spill spn (24 + nn) [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x56e | 1%nat => 0x570
                              | 2%nat => 0x572 | 3%nat => 0x574
                              | 4%nat => 0x576 | _ => 0x578 end)
              adA valsA h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adA; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adA; apply ushp_slot_al; exact Hal8
                       | unfold valsA;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] [C0 C1 C2 C5 C6] Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_56e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_570 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_572 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_574 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_576 with "Hcode") | done ]. }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplitL "C0"; [ iExact "C0" | ].
      iSplitL "C1"; [ iExact "C1" | ].
      iSplitL "C2"; [ iExact "C2" | ].
      iSplitL "C5"; [ iExact "C5" | ].
      iSplitL "C6"; [ iExact "C6" | done ]. }
    iIntros "HslA" (h2) "Hrun". cbn [length].
    (* ---- 0x578  c.addi4spn s0,sp,128 ---- *)
    assert (Hup : add_vec_int spn (8 * Z.of_nat 16) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 16) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    assert (Efp : add_vec spn
                    (sign_extend' 64
                       (caddi4spn_imm (mword_of_int 32 : mword 8))) = sp0).
    { assert (Ei : (sign_extend' 64
                      (caddi4spn_imm (mword_of_int 32 : mword 8)) : mword 64)
                   = mword_of_int (8 * Z.of_nat 16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ei. exact Hup. }
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x578)
              (mword_of_int 0 : mword 3) (mword_of_int 32 : mword 8) s0_idx
              sp0 (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1; symmetry; exact Efp)
              with "[] Hrun").
    { iApply (uis_shp_578 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hs0_2 : m2 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
      symmetry. exact (moi_of_uint sp0). }
    (* ---- 0x57a  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x57a) s4_idx a0_idx
              (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_57a with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x57c  c.mv s5,a1 ---- *)
    iApply (wp_uk_cmv N h4 m3 (mword_of_int 0x57c) s5_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_57c with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m4 := <[Regidx s5_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x57e  auipc a2,0x1 ---- *)
    iApply (wp_uk_auipc N h5 m4 (mword_of_int 0x57e)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x157e) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_57e with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0x157e : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int 0x157e)
      by exact (upd_eq m4 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x157e : mword 64))).
    (* ---- 0x582  addi a2,a2,-682 -- the open-paren table ---- *)
    iApply (wp_uk_addi N h6 m5 (mword_of_int 0x582)
              (mword_of_int 3450 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_block) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_5; unfold ushp_T_block;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_582 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m6 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_block : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x586  jal 424 <peek> ---- *)
    iApply (wp_uk_jal N h7 m6 (mword_of_int 0x586)
              (mword_of_int 2096798 : mword 21) ra_idx
              (mword_of_int 0x424) (mword_of_int 0x58a) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_586 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x58a : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret7 : ret_pc (m7 !!! Regidx ra_idx) = mword_of_int 0x58a).
    { rewrite (upd_eq m6 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x58a : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_7 : m7 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm7 a0_idx ltac:(vm_compute; discriminate))
              (Hm6 a0_idx ltac:(vm_compute; discriminate))
              (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_7 : m7 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm7 a1_idx ltac:(vm_compute; discriminate))
              (Hm6 a1_idx ltac:(vm_compute; discriminate))
              (Hm5 a1_idx ltac:(vm_compute; discriminate))
              (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Ha2_7 : m7 !!! Regidx a2_idx = mword_of_int ushp_T_block).
    { rewrite (Hm7 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_block : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_ref_peek h8 m7 dq dw true DfracDiscarded ps s0
              ushp_T_block len off 1 f (ushp_lit ushp_T_block)
              w0 (14 + nn) [rb_lpar] false s
              Ha0_7 Ha1_7 Ha2_7 Hoffle Hw0 Hs0 Hs64
              ltac:(unfold ushp_T_block; lia)
              ltac:(unfold ushp_T_block, Z64; lia) Hps0 Hps8 Hpssz
              ushp_T_block_tl Epk
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_block 1 DfracDiscarded
                ushp_T_block_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h9 m8) "%Hcs78 %Ha0_8' Hrun".
    rewrite Eret7.
    assert (Ha0_8 : m8 !!! Regidx a0_idx = mword_of_int 0) by exact Ha0_8'.
    clear Ha0_8'.
    (* ---- 0x58a  c.bnez a0 -- NOT taken: this is not a block ---- *)
    iApply (wp_uk_cbnez N h9 m8 (mword_of_int 0x58a)
              (mword_of_int 32 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x5ca) (24 + nn)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_8; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_58a with "Hcode"). }
    iIntros (h10) "Hrun".
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = spn).
    { rewrite (Hcs78 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* THE REGISTERS THE SECOND SPILL RUN SAVES, read back once.  s0, s4
       and s5 are excluded because the prologue has already written them;
       every register the run actually saves is outside that set, so the
       [vm_compute] at each concrete index closes it.  It is hoisted rather
       than inlined because an [ltac:] under a [_] the goal mentions is
       THE divergence of this lane (see the file header). *)
    assert (Hk8 : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s4_idx -> Regidx q <> Regidx s5_idx ->
              m8 !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hqs0 Hqs4 Hqs5.
      rewrite (Hcs78 q Hq)
              (Hm7 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm5 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q Hqs5) (Hm3 q Hqs4) (Hm2 q Hqs0) (Hm1 q Hsp).
      reflexivity. }
    (* ---- 0x58c..0x59a  the OTHER eight spills ---- *)
    iApply (wp_kshp_spill spn (24 + nn) [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x58c | 1%nat => 0x58e
                              | 2%nat => 0x590 | 3%nat => 0x592
                              | 4%nat => 0x594 | 5%nat => 0x596
                              | 6%nat => 0x598 | 7%nat => 0x59a
                              | _ => 0x59c end)
              adB valsB h10 m8 Hsp8
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adB; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adB; apply ushp_slot_al; exact Hal8
                       | unfold valsB; cbn;
                         refine (eq_sym (Hk8 _ _ _ _ _ _));
                         vm_compute; first [ reflexivity | discriminate ] ] ]))
              with "[] [C3 C4 C7 C8 C9 C10 C11 C12] Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_58c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_58e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_590 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_592 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_594 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_596 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_598 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_59a with "Hcode") | done ]. }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplitL "C3"; [ iExact "C3" | ].
      iSplitL "C4"; [ iExact "C4" | ].
      iSplitL "C7"; [ iExact "C7" | ].
      iSplitL "C8"; [ iExact "C8" | ].
      iSplitL "C9"; [ iExact "C9" | ].
      iSplitL "C10"; [ iExact "C10" | ].
      iSplitL "C11"; [ iExact "C11" | ].
      iSplitL "C12"; [ iExact "C12" | done ]. }
    iIntros "HslB" (h11) "Hrun". cbn [length].
    (* ---- 0x59c  c.mv s2,a0 -- argc = 0, and a0 IS 0 ---- *)
    iApply (wp_uk_cmv N h11 m8 (mword_of_int 0x59c) s2_idx a0_idx
              (mword_of_int 0) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_8; symmetry; exact (ushp_mv_val 0))
              with "[] Hrun").
    { iApply (uis_shp_59c with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x59e  jal 20a <execcmd> ---- *)
    iApply (wp_uk_jal N h12 m9 (mword_of_int 0x59e)
              (mword_of_int 2096236 : mword 21) ra_idx
              (mword_of_int 0x20a) (mword_of_int 0x5a2) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_59e with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x5a2 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret10 : ret_pc (m10 !!! Regidx ra_idx) = mword_of_int 0x5a2).
    { rewrite (upd_eq m9 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5a2 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_execcmd.
    (* the out-of-memory law, at execcmd's (deeper) budget *)
    iDestruct (UkShCmdalloc.ushp_oom_mono N Pex (nn - 2) (10 + (8 + nn))
                 ltac:(lia) with "Hpx") as "#Hpx8".
    iApply (UkShParseLex.wp_kshp_execcmd N UM UM1 Hok0 h13 m10 s0 (8 + nn)
              with "Hcode HM Hpx8 Hpay Hrun").
    iIntros (h14 m11 p) "%Hcs1011 %Ha0_11 %Hpb Hnode HM' Hpay Hrun".
    rewrite Eret10.
    destruct Hpb as [ Hp0 [ Hp16 Hpsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Hp64 : 0 <= p /\ p + 168 < Z64)
      by (rewrite H38 in Hpsz; unfold Z64; lia).
    assert (Hp8 : p mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp16 ]. }
    (* ---- 0x5a2  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv N h14 m11 (mword_of_int 0x5a2) s3_idx a0_idx
              (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5a2 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x5a4  c.mv s11,a0 ---- *)
    iApply (wp_uk_cmv N h15 m12 (mword_of_int 0x5a4) s11_idx
              a0_idx (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate))
                      Ha0_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5a4 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (m13 := <[Regidx s11_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m12).
    assert (Hm13 : forall q : mword 5, Regidx q <> Regidx s11_idx ->
                     m13 !!! Regidx q = m12 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m12 (Regidx s11_idx) (Regidx q) _ Hq)).
    (* ---- the register values the calls below read, once ---- *)
    assert (Hk13 : forall q : mword 5, ucallee_saved_idx q = true ->
                     Regidx q <> Regidx s2_idx -> Regidx q <> Regidx s3_idx ->
                     Regidx q <> Regidx s11_idx ->
                     m13 !!! Regidx q = m7 !!! Regidx q).
    { intros q Hq H2 H3 H11.
      rewrite (Hm13 q H11) (Hm12 q H3)
              (Hcs1011 q Hq)
              (Hm10 q (ushp_cs_ne q ra_idx Hq
                         ltac:(vm_compute; reflexivity)))
              (Hm9 q H2) (Hcs78 q Hq). reflexivity. }
    assert (Hs4_13 : m13 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hk13 s4_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hm6 s4_idx ltac:(vm_compute; discriminate))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs5_13 : m13 !!! Regidx s5_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hk13 s5_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm7 s5_idx ltac:(vm_compute; discriminate))
              (Hm6 s5_idx ltac:(vm_compute; discriminate))
              (Hm5 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s5_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Hs0_13 : m13 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hk13 s0_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm7 s0_idx ltac:(vm_compute; discriminate))
              (Hm6 s0_idx ltac:(vm_compute; discriminate))
              (Hm5 s0_idx ltac:(vm_compute; discriminate))
              (Hm4 s0_idx ltac:(vm_compute; discriminate))
              (Hm3 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_2. }
    (* ---- 0x5a6  c.mv a2,s5 ---- *)
    iApply (wp_uk_cmv N h16 m13 (mword_of_int 0x5a6) a2_idx
              s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_13; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_5a6 with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m14 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len)
                        : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x5a8  c.mv a1,s4 ---- *)
    iApply (wp_uk_cmv N h17 m14 (mword_of_int 0x5a8) a1_idx
              s4_idx (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm14 s4_idx ltac:(vm_compute; discriminate))
                      Hs4_13; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_5a8 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m15 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x5aa  jal 488 <parseredirs> ---- *)
    iApply (wp_uk_jal N h18 m15 (mword_of_int 0x5aa)
              (mword_of_int 2096862 : mword 21) ra_idx
              (mword_of_int 0x488) (mword_of_int 0x5ae) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5aa with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m16 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x5ae : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret16 : ret_pc (m16 !!! Regidx ra_idx) = mword_of_int 0x5ae).
    { rewrite (upd_eq m15 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5ae : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_16 : m16 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm16 a0_idx ltac:(vm_compute; discriminate))
              (Hm15 a0_idx ltac:(vm_compute; discriminate))
              (Hm14 a0_idx ltac:(vm_compute; discriminate))
              (Hm13 a0_idx ltac:(vm_compute; discriminate))
              (Hm12 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_11. }
    assert (Ha1_16 : m16 !!! Regidx a1_idx = mword_of_int ps).
    { rewrite (Hm16 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m14 (Regidx a1_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha2_16 : m16 !!! Regidx a2_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm16 a2_idx ltac:(vm_compute; discriminate))
              (Hm15 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m13 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    (* the cursor has already been moved once, by the block peek: it sits
       at [s], where the reference ran parseredirs *)
    rewrite <- shpp_parseredirs.
    iDestruct (ushp_redirs_res_of rs_l dv Pex with "Hpx Hsy Hpay") as "[Hrres Hback]".
    iApply (wp_ref_parseredirs h19 m16 dq dw dv p ps s0 len s n s1 f rs_l
              UM1 UM2 (mword_of_int (s0 + Z.of_nat s)) nn
              Ha0_16 Ha1_16 Ha2_16 Hs eq_refl Erd Hch1
              (fun _ => Hscope)
              (fun Hne => Hnn (ref_has_redir_wrap _ _ (app_ne_l rs_l rs' Hne)))
              Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hro HM' Hrres Hcur Hstr Hws Hrun").
    iIntros (t0) "Hcur Hstr Hws Hrat HM2 Hrres".
    iIntros (h20 m17) "%Hcs1617 %Ha0_17 Hrun".
    rewrite Eret16.
    iDestruct ("Hback" with "Hrres") as "[Hsy Hpay]".
    (* ---- 0x5ae  c.mv s1,a0 -- ret = what parseredirs returned ---- *)
    iApply (wp_uk_cmv N h20 m17 (mword_of_int 0x5ae) s1_idx
              a0_idx (mword_of_int t0) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_17; symmetry; exact (ushp_mv_val t0))
              with "[] Hrun").
    { iApply (uis_shp_5ae with "Hcode"). }
    iIntros (h21) "Hrun".
    set (m18 := <[Regidx s1_idx
                  := regval_into_reg (mword_of_int t0 : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs3_18 : m18 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hm18 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1617 s3_idx ltac:(vm_compute; reflexivity))
              (Hm16 s3_idx ltac:(vm_compute; discriminate))
              (Hm15 s3_idx ltac:(vm_compute; discriminate))
              (Hm14 s3_idx ltac:(vm_compute; discriminate))
              (Hm13 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx s3_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    (* ---- 0x5b0  c.addi s3,s3,8 -- s3 = &argv[0] ---- *)
    assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                   = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h21 m18 (mword_of_int 0x5b0)
              (mword_of_int 8 : mword 6) s3_idx (mword_of_int (p + 8))
              (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_18 Esx8; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_5b0 with "Hcode"). }
    iIntros (h22) "Hrun".
    set (m19 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int (p + 8) : mword 64)]> m18).
    assert (Hm19 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m19 !!! Regidx q = m18 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m18 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x5b2/0x5b6  the argument-loop table ---- *)
    iApply (wp_uk_auipc N h22 m19 (mword_of_int 0x5b2)
              (mword_of_int 1 : mword 20) s6_idx
              (mword_of_int 0x15b2) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5b2 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (m20 := <[Regidx s6_idx
                  := regval_into_reg (mword_of_int 0x15b2 : mword 64)]> m19).
    assert (Hm20 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                     m20 !!! Regidx q = m19 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m19 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_20 : m20 !!! Regidx s6_idx = mword_of_int 0x15b2)
      by exact (upd_eq m19 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int 0x15b2 : mword 64))).
    iApply (wp_uk_addi N h23 m20 (mword_of_int 0x5b6)
              (mword_of_int 3430 : mword 12) s6_idx s6_idx
              (mword_of_int ushp_T_arg) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_20; unfold ushp_T_arg;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5b6 with "Hcode"). }
    iIntros (h24) "Hrun".
    set (m21 := <[Regidx s6_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_arg : mword 64)]> m20).
    assert (Hm21 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                     m21 !!! Regidx q = m20 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m20 (Regidx s6_idx) (Regidx q) _ Hq)).
    (* ---- 0x5ba/0x5be  &eq and &q, the two locals ---- *)
    assert (Hs0_21 : m21 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm21 s0_idx ltac:(vm_compute; discriminate))
              (Hm20 s0_idx ltac:(vm_compute; discriminate))
              (Hm19 s0_idx ltac:(vm_compute; discriminate))
              (Hm18 s0_idx ltac:(vm_compute; discriminate))
              (Hcs1617 s0_idx ltac:(vm_compute; reflexivity))
              (Hm16 s0_idx ltac:(vm_compute; discriminate))
              (Hm15 s0_idx ltac:(vm_compute; discriminate))
              (Hm14 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_13. }
    iApply (wp_uk_addi N h24 m21 (mword_of_int 0x5ba)
              (mword_of_int 3968 : mword 12) s0_idx s8_idx
              (mword_of_int (uint sp0 - 128)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_21;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 3968 : mword 12)
                                  : mword 64) = mword_of_int (-128))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_5ba with "Hcode"). }
    iIntros (h25) "Hrun".
    set (m22 := <[Regidx s8_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 128) : mword 64)]> m21).
    assert (Hm22 : forall q : mword 5, Regidx q <> Regidx s8_idx ->
                     m22 !!! Regidx q = m21 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m21 (Regidx s8_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_addi N h25 m22 (mword_of_int 0x5be)
              (mword_of_int 3976 : mword 12) s0_idx s7_idx
              (mword_of_int (uint sp0 - 120)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm22 s0_idx ltac:(vm_compute; discriminate))
                      Hs0_21;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 3976 : mword 12)
                                  : mword 64) = mword_of_int (-120))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_5be with "Hcode"). }
    iIntros (h26) "Hrun".
    set (m23 := <[Regidx s7_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 120) : mword 64)]> m22).
    assert (Hm23 : forall q : mword 5, Regidx q <> Regidx s7_idx ->
                     m23 !!! Regidx q = m22 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m22 (Regidx s7_idx) (Regidx q) _ Hq)).
    (* ---- 0x5c2/0x5c6  the two constants ---- *)
    iApply (wp_uk_li N h26 m23 (mword_of_int 0x5c2)
              (mword_of_int 97 : mword 12) s10_idx (mword_of_int 97)
              (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 97))
              with "[] Hrun").
    { iApply (uis_shp_5c2 with "Hcode"). }
    iIntros (h27) "Hrun".
    set (m24 := <[Regidx s10_idx
                  := regval_into_reg (mword_of_int 97 : mword 64)]> m23).
    assert (Hm24 : forall q : mword 5, Regidx q <> Regidx s10_idx ->
                     m24 !!! Regidx q = m23 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m23 (Regidx s10_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cli N h27 m24 (mword_of_int 0x5c6)
              (mword_of_int 10 : mword 6) s9_idx (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_5c6 with "Hcode"). }
    iIntros (h28) "Hrun".
    set (m25 := <[Regidx s9_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 10 : mword 6)
                        : mword 64)]> m24).
    assert (Hm25 : forall q : mword 5, Regidx q <> Regidx s9_idx ->
                     m25 !!! Regidx q = m24 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m24 (Regidx s9_idx) (Regidx q) _ Hq)).
    (* ---- 0x5c8  c.j 0x5fe -- into the loop ---- *)
    iApply (wp_uk_cj N h28 m25 (mword_of_int 0x5c8)
              (mword_of_int 27 : mword 11) (mword_of_int 0x5fe) (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5c8 with "Hcode"). }
    iIntros (h29) "Hrun".
    (* ---- the register file the loop is entered in ---- *)
    assert (Hk25 : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s3_idx ->
              Regidx q <> Regidx s6_idx -> Regidx q <> Regidx s7_idx ->
              Regidx q <> Regidx s8_idx -> Regidx q <> Regidx s9_idx ->
              Regidx q <> Regidx s10_idx ->
              m25 !!! Regidx q = m13 !!! Regidx q).
    { intros q Hq H1 H3 H6 H7 H8 H9 H10.
      rewrite (Hm25 q H9) (Hm24 q H10) (Hm23 q H7) (Hm22 q H8)
              (Hm21 q H6) (Hm20 q H6) (Hm19 q H3) (Hm18 q H1)
              (Hcs1617 q Hq)
              (Hm16 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm15 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm14 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity))).
      reflexivity. }
    assert (Hs2_13 : m13 !!! Regidx s2_idx = mword_of_int 0).
    { rewrite (Hm13 s2_idx ltac:(vm_compute; discriminate))
              (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hcs1011 s2_idx ltac:(vm_compute; reflexivity))
              (Hm10 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx s2_idx)
               (regval_into_reg (mword_of_int 0 : mword 64))). }
    assert (Hs11_13 : m13 !!! Regidx s11_idx = mword_of_int p)
      by exact (upd_eq m12 (Regidx s11_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hkm : forall q : mword 5, Regidx q <> Regidx s1_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s6_idx ->
              Regidx q <> Regidx s7_idx -> Regidx q <> Regidx s8_idx ->
              Regidx q <> Regidx s9_idx -> Regidx q <> Regidx s10_idx ->
              m25 !!! Regidx q = m18 !!! Regidx q).
    { intros q H1 H3 H6 H7 H8 H9 H10.
      rewrite (Hm25 q H9) (Hm24 q H10) (Hm23 q H7) (Hm22 q H8)
              (Hm21 q H6) (Hm20 q H6) (Hm19 q H3). reflexivity. }
    assert (Hs1_25 : m25 !!! Regidx s1_idx = mword_of_int t0).
    { rewrite (Hm25 s1_idx ltac:(vm_compute; discriminate))
              (Hm24 s1_idx ltac:(vm_compute; discriminate))
              (Hm23 s1_idx ltac:(vm_compute; discriminate))
              (Hm22 s1_idx ltac:(vm_compute; discriminate))
              (Hm21 s1_idx ltac:(vm_compute; discriminate))
              (Hm20 s1_idx ltac:(vm_compute; discriminate))
              (Hm19 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m17 (Regidx s1_idx)
               (regval_into_reg (mword_of_int t0 : mword 64))). }
    assert (Hs3_25 : m25 !!! Regidx s3_idx = mword_of_int (p + 8)).
    { rewrite (Hm25 s3_idx ltac:(vm_compute; discriminate))
              (Hm24 s3_idx ltac:(vm_compute; discriminate))
              (Hm23 s3_idx ltac:(vm_compute; discriminate))
              (Hm22 s3_idx ltac:(vm_compute; discriminate))
              (Hm21 s3_idx ltac:(vm_compute; discriminate))
              (Hm20 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m18 (Regidx s3_idx)
               (regval_into_reg (mword_of_int (p + 8) : mword 64))). }
    assert (Hs6_25 : m25 !!! Regidx s6_idx = mword_of_int ushp_T_arg).
    { rewrite (Hm25 s6_idx ltac:(vm_compute; discriminate))
              (Hm24 s6_idx ltac:(vm_compute; discriminate))
              (Hm23 s6_idx ltac:(vm_compute; discriminate))
              (Hm22 s6_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m20 (Regidx s6_idx)
               (regval_into_reg (mword_of_int ushp_T_arg : mword 64))). }
    assert (Hs7_25 : m25 !!! Regidx s7_idx
                     = mword_of_int (uint sp0 - 120)).
    { rewrite (Hm25 s7_idx ltac:(vm_compute; discriminate))
              (Hm24 s7_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m22 (Regidx s7_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 120) : mword 64))). }
    assert (Hs8_25 : m25 !!! Regidx s8_idx
                     = mword_of_int (uint sp0 - 128)).
    { rewrite (Hm25 s8_idx ltac:(vm_compute; discriminate))
              (Hm24 s8_idx ltac:(vm_compute; discriminate))
              (Hm23 s8_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m21 (Regidx s8_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 128) : mword 64))). }
    assert (Hs9_25 : m25 !!! Regidx s9_idx = mword_of_int 10).
    { rewrite (upd_eq m24 (Regidx s9_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 10 : mword 6)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs10_25 : m25 !!! Regidx s10_idx = mword_of_int 97).
    { rewrite (Hm25 s10_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m23 (Regidx s10_idx)
               (regval_into_reg (mword_of_int 97 : mword 64))). }
    assert (Hsp8al : (uint sp0 - 128) mod 8 = 0).
    { rewrite Zminus_mod Hal8. reflexivity. }
    (* ---- 0x5fe..0x63e  THE ARGUMENT LOOP ---- *)
    iDestruct (ushp_pex_res_of rs' Pex with "Hpx Hpay") as "[Hres Hback']".
    iApply (wp_ref_pex_loop dq dw dv s0 ps p (uint sp0) len f nn
              n (@nil (nat * nat)) toks rs_l rs' t0 s1 s2 UM2 UM' h29 m25 wq weq
              Hscope Eargs Hch2
              (fun Hne => Hnn (ref_has_redir_wrap _ _ (app_ne_r rs_l rs' Hne)))
              Hs0 Hs64 Hps0 Hps8 Hpssz
              ltac:(lia) Hsp8al ltac:(lia) ltac:(lia)
              Hp0 Hp8 ltac:(lia) Hs1
              ltac:(rewrite (Hk25 s0_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs0_13)
              Hs1_25
              ltac:(rewrite (Hk25 s2_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    rewrite Hs2_13; f_equal; cbn [length]; lia)
              ltac:(rewrite Hs3_25; f_equal; cbn [length]; lia)
              ltac:(rewrite (Hk25 s4_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs4_13)
              ltac:(rewrite (Hk25 s5_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs5_13)
              Hs6_25 Hs7_25 Hs8_25 Hs9_25 Hs10_25
              ltac:(rewrite (Hk25 s11_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs11_13)
              with "Hcode Hro HM2 Hres Hnode Hrat Hcur Lq Leq Hstr Hws Hsy Hrun").
    iIntros (root) "Hnode Hrat Hcur [%vq Lq] [%veq Leq] Hstr Hws Hsy HM' Hres".
    iIntros (h30 mf) "%Hpresf %Hs2f %Hs1f Hrun".
    iDestruct ("Hback'" with "Hres") as "Hpay".
    assert (Hs2f' : mf !!! Regidx s2_idx
                    = mword_of_int (Z.of_nat (length toks))) by exact Hs2f.
    assert (Hsp_f : mf !!! Regidx csp_rs1 = spn).
    { rewrite (Hpresf csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hk25 csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1011 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp8. }
    assert (Hs11_f : mf !!! Regidx s11_idx = mword_of_int p).
    { rewrite (Hpresf s11_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate))
              (Hk25 s11_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hs11_13. }
    (* ---- 0x63e  c.slli s2,s2,0x3 ---- *)
    iApply (wp_uk_cslli N h30 mf (mword_of_int 0x63e)
              (mword_of_int 3 : mword 6) s2_idx
              (mword_of_int (8 * Z.of_nat (length toks))) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2f'
                      (moi_shl (Z.of_nat (length toks)) 3 ltac:(lia));
                    f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_63e with "Hcode"). }
    iIntros (h31) "Hrun".
    set (mg := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (8 * Z.of_nat (length toks))
                       : mword 64)]> mf).
    assert (Hmg : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    mg !!! Regidx q = mf !!! Regidx q)
      by (intros q Hq; exact (upd_ne mf (Regidx s2_idx) (Regidx q) _ Hq)).
    assert (Hs2_g : mg !!! Regidx s2_idx
                    = mword_of_int (8 * Z.of_nat (length toks)))
      by exact (upd_eq mf (Regidx s2_idx)
                  (regval_into_reg
                     (mword_of_int (8 * Z.of_nat (length toks))
                      : mword 64))).
    (* ---- 0x640  add a5,s11,s2 ---- *)
    iApply (wp_uk_add N h31 mg (mword_of_int 0x640)
              s11_idx s2_idx a5_idx
              (mword_of_int (p + 8 * Z.of_nat (length toks))) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_g (Hmg s11_idx ltac:(vm_compute; discriminate))
                      Hs11_f; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_640 with "Hcode"). }
    iIntros (h32) "Hrun".
    set (mh := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (p + 8 * Z.of_nat (length toks))
                       : mword 64)]> mg).
    assert (Hmh : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    mh !!! Regidx q = mg !!! Regidx q)
      by (intros q Hq; exact (upd_ne mg (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_h : mh !!! Regidx a5_idx
                    = mword_of_int (p + 8 * Z.of_nat (length toks)))
      by exact (upd_eq mg (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int (p + 8 * Z.of_nat (length toks))
                      : mword 64))).
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Ez : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    iDestruct "Hnode" as "(%Hdl & _ & _ & Hty & Hav & Hev)".
    (* ---- 0x644  sd zero,8(a5) -- argv[argc] = 0, which it already is ---- *)
    iDestruct (ushp_slots_cap s0 (p + 8) toks fst Hdl with "Hav")
      as "[Hav0 Havc]".
    iApply (wp_uk_sd N h32 mh (mword_of_int 0x644)
              (mword_of_int 8 : mword 12) a5_idx x0_idx
              (p + 8 + 8 * Z.of_nat (length toks)) (mword_of_int 0)
              (24 + nn)
              ltac:(rewrite Ha5_h
                      (uint_moi (p + 8 * Z.of_nat (length toks))
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(exact (ushp_slot_al8 p 1 (length toks) Hp8))
              with "[] [Hav0] Hrun").
    { iApply (uis_shp_644 with "Hcode"). }
    { iExact "Hav0". }
    iIntros "Hav0" (h33) "Hrun".
    rewrite Hx0 Ez.
    iDestruct ("Havc" with "Hav0") as "Hav".
    (* ---- 0x648  sd zero,88(a5) -- eargv[argc] = 0 ---- *)
    iDestruct (ushp_slots_cap s0 (p + 88) toks snd Hdl with "Hev")
      as "[Hev0 Hevc]".
    iApply (wp_uk_sd N h33 mh (mword_of_int 0x648)
              (mword_of_int 88 : mword 12) a5_idx x0_idx
              (p + 88 + 8 * Z.of_nat (length toks)) (mword_of_int 0)
              (24 + nn)
              ltac:(rewrite Ha5_h
                      (uint_moi (p + 8 * Z.of_nat (length toks))
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(exact (ushp_slot_al8 p 11 (length toks) Hp8))
              with "[] [Hev0] Hrun").
    { iApply (uis_shp_648 with "Hcode"). }
    { iExact "Hev0". }
    iIntros "Hev0" (h34) "Hrun".
    rewrite Hx0 Ez.
    iDestruct ("Hevc" with "Hev0") as "Hev".
    (* ---- 0x64c..0x65a  the EIGHT restores ---- *)
    assert (Hsp_h : mh !!! Regidx csp_rs1 = spn).
    { rewrite (Hmh csp_rs1 ltac:(vm_compute; discriminate))
              (Hmg csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_f. }
    iApply (wp_kshp_restore spn (24 + nn) [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x64c | 1%nat => 0x64e
                              | 2%nat => 0x650 | 3%nat => 0x652
                              | 4%nat => 0x654 | 5%nat => 0x656
                              | 6%nat => 0x658 | 7%nat => 0x65a
                              | _ => 0x65c end)
              adB valsB h34 mh Hsp_h
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adB; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adB; apply ushp_slot_al; exact Hal8
                       | split; [ unfold unot_sp; vm_compute; discriminate
                                | vm_compute; discriminate ] ] ]))
              with "[] HslB Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_64c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_64e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_650 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_652 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_654 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_656 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_658 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_65a with "Hcode") | done ]. }
    iIntros "HslB" (h35) "Hrun". cbn [length].
    set (mi := ushp_spillback [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] valsB mh).
    assert (Hmi : forall q : mword 5,
              (forall (i : nat) (r : mword 5) (u : mword 6),
                 [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] !! i = Some (r, u) -> Regidx q <> Regidx r) ->
              mi !!! Regidx q = mh !!! Regidx q)
      by (intros q Hq; exact (ushp_spillback_ne [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] valsB mh q Hq)).
    assert (Hs1_i : mi !!! Regidx s1_idx = mword_of_int root).
    { rewrite (Hmi s1_idx
                 ltac:(ushp_ne_vm))
              (Hmh s1_idx ltac:(vm_compute; discriminate))
              (Hmg s1_idx ltac:(vm_compute; discriminate)). exact Hs1f. }
    assert (Hsp_i : mi !!! Regidx csp_rs1 = spn).
    { rewrite (Hmi csp_rs1
                 ltac:(ushp_ne_vm)). exact Hsp_h. }
    (* ---- 0x65c  c.j 0x5d4 -- into the common tail ---- *)
    iApply (wp_uk_cj N h35 mi (mword_of_int 0x65c)
              (mword_of_int 1980 : mword 11) (mword_of_int 0x5d4) (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_65c with "Hcode"). }
    iIntros (h36) "Hrun".
    (* ---- 0x5d4  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv N h36 mi (mword_of_int 0x5d4) a0_idx
              s1_idx (mword_of_int root) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_i; symmetry; exact (ushp_mv_val root))
              with "[] Hrun").
    { iApply (uis_shp_5d4 with "Hcode"). }
    iIntros (h37) "Hrun".
    set (mj := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int root : mword 64)]> mi).
    assert (Hmj : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    mj !!! Regidx q = mi !!! Regidx q)
      by (intros q Hq; exact (upd_ne mi (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hsp_j : mj !!! Regidx csp_rs1 = spn).
    { rewrite (Hmj csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_i. }
    (* ---- 0x5d6..0x5de  the FIVE restores ---- *)
    iApply (wp_kshp_restore spn (24 + nn) [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x5d6 | 1%nat => 0x5d8
                              | 2%nat => 0x5da | 3%nat => 0x5dc
                              | 4%nat => 0x5de | _ => 0x5e0 end)
              adA valsA h37 mj Hsp_j
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adA; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adA; apply ushp_slot_al; exact Hal8
                       | split; [ unfold unot_sp; vm_compute; discriminate
                                | vm_compute; discriminate ] ] ]))
              with "[] HslA Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_5d6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5d8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5da with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5dc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5de with "Hcode") | done ]. }
    iIntros "HslA" (h38) "Hrun". cbn [length].
    set (mk := ushp_spillback [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] valsA mj).
    assert (Hspk : mk !!! Regidx csp_rs1 = spn).
    { rewrite (ushp_spillback_ne [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] valsA mj csp_rs1
                 ltac:(ushp_ne_vm)). exact Hsp_j. }
    assert (Hrak : mk !!! Regidx ra_idx = valsA 0%nat)
      by exact (ushp_spillback_ra [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] (mword_of_int 15 : mword 6) valsA mj
                  eq_refl
                  ltac:(ushp_ne_vm)).
    (* ---- the frame, put back together ---- *)
    set (valsAll := fun i : nat =>
                      match i with
                      | 0%nat => m !!! Regidx ra_idx
                      | 1%nat => m !!! Regidx s0_idx
                      | 2%nat => m !!! Regidx s1_idx
                      | 3%nat => m !!! Regidx s2_idx
                      | 4%nat => m !!! Regidx s3_idx
                      | 5%nat => m !!! Regidx s4_idx
                      | 6%nat => m !!! Regidx s5_idx
                      | 7%nat => m !!! Regidx s6_idx
                      | 8%nat => m !!! Regidx s7_idx
                      | 9%nat => m !!! Regidx s8_idx
                      | 10%nat => m !!! Regidx s9_idx
                      | 11%nat => m !!! Regidx s10_idx
                      | _ => m !!! Regidx s11_idx end).
    iEval (rewrite !big_sepL_cons big_sepL_nil) in "HslA".
    iEval (rewrite !big_sepL_cons big_sepL_nil) in "HslB".
    iDestruct "HslA" as "(A0 & A1 & A2 & A3 & A4 & _)".
    iDestruct "HslB" as "(B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & _)".
    (* ---- 0x5e0  c.addi16sp sp,sp,128 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up N h38 mk (mword_of_int 0x5e0)
              (mword_of_int 8 : mword 6) 16 (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 B5 B6 B7 L0 Lq Leq Hbot]
                   Hrun").
    { iApply (uis_shp_5e0 with "Hcode"). }
    { rewrite Hspk Hup.
      iDestruct (ushp_frame_join spl sp3 0 [(x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6);
                 (x0_idx, mword_of_int 0 : mword 6)]
                   (fun i : nat => match i with
                                   | 0%nat => wl0 | 1%nat => vq
                                   | _ => veq end)
                   ltac:(cbn [length]; lia)
                   with "[L0 Lq Leq] Hbot") as "Hloc".
      { rewrite !big_sepL_cons big_sepL_nil Hsplu E0 E1 E2.
        iSplitL "L0"; [ iExact "L0" | ].
        iSplitL "Lq"; [ iExact "Lq" | ].
        iSplitL "Leq"; [ iExact "Leq" | done ]. }
      iDestruct (ushp_frame_join sp0 spl 3 [(ra_idx, mword_of_int 15 : mword 6);
                 (s0_idx, mword_of_int 14 : mword 6);
                 (s1_idx, mword_of_int 13 : mword 6);
                 (s2_idx, mword_of_int 12 : mword 6);
                 (s3_idx, mword_of_int 11 : mword 6);
                 (s4_idx, mword_of_int 10 : mword 6);
                 (s5_idx, mword_of_int 9 : mword 6);
                 (s6_idx, mword_of_int 8 : mword 6);
                 (s7_idx, mword_of_int 7 : mword 6);
                 (s8_idx, mword_of_int 6 : mword 6);
                 (s9_idx, mword_of_int 5 : mword 6);
                 (s10_idx, mword_of_int 4 : mword 6);
                 (s11_idx, mword_of_int 3 : mword 6)] valsAll
                   ltac:(cbn [length]; lia)
                   with "[A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 B5 B6 B7] Hloc")
        as "Hstk".
      { rewrite !big_sepL_cons big_sepL_nil.
        iSplitL "A0"; [ iExact "A0" | ].
        iSplitL "A1"; [ iExact "A1" | ].
        iSplitL "A2"; [ iExact "A2" | ].
        iSplitL "B0"; [ iExact "B0" | ].
        iSplitL "B1"; [ iExact "B1" | ].
        iSplitL "A3"; [ iExact "A3" | ].
        iSplitL "A4"; [ iExact "A4" | ].
        iSplitL "B2"; [ iExact "B2" | ].
        iSplitL "B3"; [ iExact "B3" | ].
        iSplitL "B4"; [ iExact "B4" | ].
        iSplitL "B5"; [ iExact "B5" | ].
        iSplitL "B6"; [ iExact "B6" | ].
        iSplitL "B7"; [ iExact "B7" | done ]. }
      iExact "Hstk". }
    rewrite Hspk Hup. iIntros (h39) "Hrun".
    (* ---- 0x5e2  c.jr ra ---- *)
    iApply (wp_uk_cjr N h39
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mk)
              (mword_of_int 0x5e2) ra_idx (ret_pc (m !!! Regidx ra_idx))
              (16 + (24 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mk (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrak; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5e2 with "Hcode"). }
    iIntros (h40) "Hrun".
    iApply ("Hcont" $! root p toks (rs_l ++ rs')
              with "[] [] [Hty Hav Hev] Hrat Hcur Hstr Hws Hsy [] [] HM' Hpay Hrun").
    - iPureIntro. reflexivity.
    - iPureIntro. lia.
    - iApply ushp_exec_pre_at. rewrite /ushp_exec_pre.
      iSplitR; [ iPureIntro; exact Hdl | ].
      iSplitR; [ iPureIntro; exact Hp0 | ].
      iSplitR; [ iPureIntro; exact Hp8 | ].
      iSplitL "Hty"; [ iExact "Hty" | ].
      iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] valsA m mj sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        rewrite (Hmj q (ushp_cs_ne q a0_idx Hq
                          ltac:(vm_compute; reflexivity))).
        apply ushp_spillback_eq.
        * intros Hmiss2.
          assert (HmB : forall (i : nat) (r' : mword 5) (u : mword 6),
                    [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)] !! i = Some (r', u) -> Regidx q <> Regidx r')
            by (intros i r' u Hi He; exact (Hmiss2 i r' u Hi (eq_sym He))).
          rewrite (Hmh q (ushp_cs_ne q a5_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hmg q (HmB 0%nat s2_idx (mword_of_int 12 : mword 6)
                            eq_refl))
                  (Hpresf q Hq
                     (Hmiss 2%nat s1_idx (mword_of_int 13 : mword 6) eq_refl)
                     (HmB 0%nat s2_idx (mword_of_int 12 : mword 6) eq_refl)
                     (HmB 1%nat s3_idx (mword_of_int 11 : mword 6) eq_refl))
                  (Hk25 q Hq
                     (Hmiss 2%nat s1_idx (mword_of_int 13 : mword 6) eq_refl)
                     (HmB 1%nat s3_idx (mword_of_int 11 : mword 6) eq_refl)
                     (HmB 2%nat s6_idx (mword_of_int 8 : mword 6) eq_refl)
                     (HmB 3%nat s7_idx (mword_of_int 7 : mword 6) eq_refl)
                     (HmB 4%nat s8_idx (mword_of_int 6 : mword 6) eq_refl)
                     (HmB 5%nat s9_idx (mword_of_int 5 : mword 6) eq_refl)
                     (HmB 6%nat s10_idx (mword_of_int 4 : mword 6) eq_refl))
                  (Hm13 q (HmB 7%nat s11_idx (mword_of_int 3 : mword 6)
                             eq_refl))
                  (Hm12 q (HmB 1%nat s3_idx (mword_of_int 11 : mword 6)
                             eq_refl))
                  (Hcs1011 q Hq)
                  (Hm10 q (ushp_cs_ne q ra_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hm9 q (HmB 0%nat s2_idx (mword_of_int 12 : mword 6)
                            eq_refl))
                  (Hcs78 q Hq)
                  (Hm7 q (ushp_cs_ne q ra_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hm6 q (ushp_cs_ne q a2_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hm5 q (ushp_cs_ne q a2_idx Hq
                            ltac:(vm_compute; reflexivity)))
                  (Hm4 q (Hmiss 4%nat s5_idx (mword_of_int 9 : mword 6)
                            eq_refl))
                  (Hm3 q (Hmiss 3%nat s4_idx (mword_of_int 10 : mword 6)
                            eq_refl))
                  (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 14 : mword 6)
                            eq_refl))
                  (Hm1 q Hqsp).
          reflexivity.
        * intros i r u Hi He.
          destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; unfold valsB;
            rewrite <- He; reflexivity.
    - iPureIntro.
      rewrite (upd_ne mk (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq mi (Regidx a0_idx)
                 (regval_into_reg (mword_of_int root : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  (* ---- the closed form: the answer as the published tree at its root ---- *)
  (* For a caller that wants [ushp_tree] rather than the two halves: the
     EXEC node closes into the chain by UkShRedirs.ushp_redirs_close along
     [ref_wrap], which is what the reference's answer IS. *)
  Lemma wp_ref_parseexec_tree {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len off n fin : nat) (f : nat -> bv 8)
      (w0 : mword 64) (t : ushp_cmd) (UM UM' : iProp Σ) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope len f ->
    ref_parseexec len f n off = Some (t, fin) ->
    ushp_malloc_chain (ushp_nodes t) UM UM' ->
    (ref_has_redir t = true -> (12 <= nn)%nat) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM -∗
    ushp_oom Pex (nn - 2) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parseexec) (16 + (24 + nn)) -∗
    (∀ root : Z,
       ushp_tree s0 root t -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int root ⌝ -∗
           UM' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (16 + (24 + nn)) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hoffle Hw0 Hscope Href Hchain Hnn Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iApply (wp_ref_parseexec h m dq dw dv ps s0 len off n fin f w0 t UM UM' nn
              Ha0 Ha1 Hoffle Hw0 Hscope Href Hchain Hnn Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (root p toks rs) "%Ht %Hp Hexec Hrat Hcur Hstr Hws Hsy". subst t.
    iIntros (h' m') "%Hcs %Ha0' HM' Hpay Hrun".
    iApply ("Hcont" $! root
              with "[Hexec Hrat] Hcur Hstr Hws Hsy [%//] [%//] HM' Hpay Hrun").
    iApply (ushp_redirs_close s0 root p rs (UshpExec toks) with "Hrat [Hexec]").
    cbn [UkShParse.ushp_tree]. iExact "Hexec".
  Qed.


End UkShArgs.
