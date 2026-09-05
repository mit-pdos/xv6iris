(* ===================================================================== *)
(* UkShParseCmd.v -- SH LANE STAGE 4, part 6: the two one-line bodies, the *)
(* NUL cut, the front door, and THE PARSER THEOREM.                        *)
(*                                                                        *)
(*   parsepipe    @0x682  one [parseexec] and a [peek] for '|'             *)
(*   parseline    @0x6e2  one [parsepipe] and a [peek] for '&' / ';'       *)
(*   nulterminate @0x7ee  the jump table -- the one COMPUTED control       *)
(*                        transfer in the parser -- walking the tree and   *)
(*                        writing a NUL at every recorded token END.  That *)
(*                        cut is what turns token BOUNDARIES into the argv *)
(*                        vector [exec] observes, and it is the fact       *)
(*                        stage 6's seam is built on.                      *)
(*   parsecmd     @0x86e  the front door: [strlen] the line, run the       *)
(*                        descent, [nulterminate], return the node.        *)
(*   wp_kshp_parser       THE THEOREM, and the two Hypotheses that reach   *)
(*                        it -- [ushp_malloc_ok] (through execcmd, now     *)
(*                        discharged by iris/UkShMalloc.v) and            *)
(*                        [ushp_clw_text_ok] (the engine's width-4 text    *)
(*                        load, declared here because nulterminate's jump  *)
(*                        table is the only thing that needs it).          *)
(*                                                                        *)
(* See iris/UkShParse.v's header for why stage 4 is six files.            *)
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
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShK UCodeShP.
Require Import UkSh.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseLex.
Require Import UkShParseTok.
Require Import UkShParseExec.

Section UkShParseCmd.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

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

(*ALIASES-BEGIN*)
  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 γt γd γs γfd).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at γd).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join γd).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split γd).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str γt γd).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty γt γd γs γfd).
  Local Notation ushp_slot := (UkShParse.ushp_slot γd).
  Local Notation ushp_tree := (UkShParse.ushp_tree γd).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at γd).
  Local Notation ushp_ubytes_ext := (UkShParse.ushp_ubytes_ext γd).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp γt γd γs γfd).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi γt γd γs γfd).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro γt γd γs γfd).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek γt γd γs γfd).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill γt γd γs γfd).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen γt γd γs γfd).

  (* stage 4's one Hypothesis, at the type the base file names *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  Local Notation wp_kshp_parseexec := (UkShParseExec.wp_kshp_parseexec γt γd γs γfd UMalloc UMalloc' ushp_malloc_ok).
(*ALIASES-END*)

  (* ===================================================================== *)
  (* §12 parsepipe @0x682 and parseline @0x6e2 -- the two one-line bodies.  *)
  (*                                                                       *)
  (*   parsepipe: cmd = parseexec(ps,es);                                   *)
  (*              if(peek(ps,es,"|")) { ... }  return cmd;                  *)
  (*   parseline: cmd = parsepipe(ps,es);                                   *)
  (*              while(peek(ps,es,"&")) { ... }                            *)
  (*              if(peek(ps,es,";")) { ... }  return cmd;                  *)
  (*                                                                       *)
  (* All three guards are peeks for a symbol byte, so all three are 0 by    *)
  (* ushp_peek_res_sym and neither [pipecmd], [backcmd] nor [listcmd] is    *)
  (* ever fetched -- which is exactly what the catalog's [skipfunc] lines   *)
  (* claimed and this is where the claim becomes a theorem.  Both frames    *)
  (* are k = 6, j = 6, no locals, and both are CONTIGUOUS, so §4c's two     *)
  (* lemmas take the whole prologue and the whole epilogue.                 *)
  (* ===================================================================== *)

  Lemma wp_kshp_parsepipe (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps s0 : Z) (len off : nat) (f : nat -> bv 8) (w0 : mword 64)
      (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    ushp_tokens len f off toks ->
    (length toks < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UMalloc -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + nn))) -∗
    (∀ p : Z,
       ⌜ p + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 p toks -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UMalloc' -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + nn))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM Hrun Hcont".
    rewrite shpp_parsepipe.
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
              vals (16 + (24 + nn)) h m
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
    iApply (wp_uk_cmv γt γd γs γfd h1 mA (mword_of_int 0x692) s2_idx a0_idx
              (mword_of_int ps) (16 + (24 + nn))
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
    iApply (wp_uk_cmv γt γd γs γfd h2 m2 (mword_of_int 0x694) s4_idx a0_idx
              (mword_of_int ps) (16 + (24 + nn))
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
    iApply (wp_uk_cmv γt γd γs γfd h3 m3 (mword_of_int 0x696) s1_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn))
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
    iApply (wp_uk_jal γt γd γs γfd h4 m4 (mword_of_int 0x698)
              (mword_of_int 2096888 : mword 21) ra_idx
              (mword_of_int 0x590) (mword_of_int 0x69c) (16 + (24 + nn))
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
    iApply (wp_kshp_parseexec h5 m5 dq dw dv ps s0 len off f w0 toks nn
              Ha0_5 Ha1_5 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hrun").
    iIntros (p) "%Hpsz Hnode Hcur Hstr Hws Hsy".
    iIntros (h6 m6) "%Hcs56 %Ha0_6 HM' Hrun".
    rewrite Eret5.
    (* ---- 0x69c  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 m6 (mword_of_int 0x69c) s3_idx a0_idx
              (mword_of_int p) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_69c with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x69e/0x6a2  the pipe table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h7 m7 (mword_of_int 0x69e)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x169e) (16 + (24 + nn))
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
    iApply (wp_uk_addi γt γd γs γfd h8 m8 (mword_of_int 0x6a2)
              (mword_of_int 3202 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_pipe) (16 + (24 + nn))
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
    iApply (wp_uk_cmv γt γd γs γfd h9 m9 (mword_of_int 0x6a6) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + nn))
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
    iApply (wp_uk_cmv γt γd γs γfd h10 m10 (mword_of_int 0x6a8) a0_idx
              s2_idx (mword_of_int ps) (16 + (24 + nn))
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
    iApply (wp_uk_jal γt γd γs γfd h11 m11 (mword_of_int 0x6aa)
              (mword_of_int 2096542 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x6ae) (16 + (24 + nn))
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
              ushp_T_pipe len len 1 f (ushp_lit ushp_T_pipe)
              (mword_of_int (s0 + Z.of_nat len)) (30 + nn)
              Ha0_12 Ha1_12 Ha2_12 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_pipe; lia)
              ltac:(unfold ushp_T_pipe, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_pipe 1 DfracDiscarded
                ushp_T_pipe_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h13 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12 Elen0.
    rewrite (ushp_peek_res_sym len f (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_pipe Hnosym ushp_T_pipe_sym) in Ha0_13.
    (* ---- 0x6ae  c.bnez a0 -- NOT taken: there is no pipe ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h13 m13 (mword_of_int 0x6ae)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x6c2) (16 + (24 + nn))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_6ae with "Hcode"). }
    iIntros (h14) "Hrun".
    (* ---- 0x6b0  c.mv a0,s3 ---- *)
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m6 (Regidx s3_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h14 m13 (mword_of_int 0x6b0) a0_idx
              s3_idx (mword_of_int p) (16 + (24 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_13; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_6b0 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m13).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* the whole body, as one preservation fact *)
    assert (Hkeep : forall q : mword 5, ucallee_saved_idx q = true ->
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              me !!! Regidx q = m !!! Regidx q).
    { intros q Hq Hsp Hq0 Hq1 Hq2 Hq3 Hq4.
      rewrite (Hme q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hcs1213 q Hq)
              (Hm12 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm7 q Hq3) (Hcs56 q Hq)
              (Hm5 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q Hq1) (Hm3 q Hq4) (Hm2 q Hq2) (HmA q Hq0) (Hm1 q Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
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
              (16 + (24 + nn)) h15 me
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
    iApply ("Hcont" $! p with "[] Hnode Hcur Hstr Hws Hsy [] [] HM' Hrun").
    - iPureIntro. exact Hpsz.
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
        exact (upd_eq m13 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ---- parseline, the same shape with TWO refuted guards -------------- *)
  Lemma wp_kshp_parseline (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps s0 : Z) (len off : nat) (f : nat -> bv 8) (w0 : mword 64)
      (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    ushp_tokens len f off toks ->
    (length toks < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UMalloc -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parseline)
      (6 + (6 + (16 + (24 + nn)))) -∗
    (∀ p : Z,
       ⌜ p + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 p toks -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UMalloc' -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (6 + (16 + (24 + nn)))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM Hrun Hcont".
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
              vals (6 + (16 + (24 + nn))) h m
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
    iApply (wp_uk_cmv γt γd γs γfd h1 mA (mword_of_int 0x6f2) s2_idx a0_idx
              (mword_of_int ps) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_cmv γt γd γs γfd h2 m2 (mword_of_int 0x6f4) s3_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_jal γt γd γs γfd h3 m3 (mword_of_int 0x6f6)
              (mword_of_int 2097036 : mword 21) ra_idx
              (mword_of_int 0x682) (mword_of_int 0x6fa)
              (6 + (16 + (24 + nn)))
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
    iApply (wp_kshp_parsepipe h4 m4 dq dw dv ps s0 len off f w0 toks nn
              Ha0_4 Ha1_4 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hrun").
    iIntros (p) "%Hpsz Hnode Hcur Hstr Hws Hsy".
    iIntros (h5 m5) "%Hcs45 %Ha0_5 HM' Hrun".
    rewrite Eret4.
    (* ---- 0x6fa  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h5 m5 (mword_of_int 0x6fa) s1_idx a0_idx
              (mword_of_int p) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_6fa with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x6fc/0x700  the ampersand table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h6 m6 (mword_of_int 0x6fc)
              (mword_of_int 1 : mword 20) s4_idx
              (mword_of_int 0x16fc) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_addi γt γd γs γfd h7 m7 (mword_of_int 0x700)
              (mword_of_int 3116 : mword 12) s4_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_cj γt γd γs γfd h8 m8 (mword_of_int 0x704)
              (mword_of_int 11 : mword 11) (mword_of_int 0x71a)
              (6 + (16 + (24 + nn)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_704 with "Hcode"). }
    iIntros (h9) "Hrun".
    (* ---- 0x71a..0x71e  peek's three arguments ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h9 m8 (mword_of_int 0x71a) a2_idx s4_idx
              (mword_of_int ushp_T_back) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_cmv γt γd γs γfd h10 m9 (mword_of_int 0x71c) a1_idx s3_idx
              (mword_of_int (s0 + Z.of_nat len)) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_cmv γt γd γs γfd h11 m10 (mword_of_int 0x71e) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_jal γt γd γs γfd h12 m11 (mword_of_int 0x720)
              (mword_of_int 2096424 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x724)
              (6 + (16 + (24 + nn)))
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
              (mword_of_int (s0 + Z.of_nat len)) (36 + nn)
              Ha0_12 Ha1_12 Ha2_12 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_back; lia)
              ltac:(unfold ushp_T_back, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_back 1 DfracDiscarded
                ushp_T_back_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h14 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12 Elen0.
    rewrite (ushp_peek_res_sym len f (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_back Hnosym ushp_T_back_sym) in Ha0_13.
    (* ---- 0x724  c.bnez a0 -- NOT taken: nothing is backgrounded ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h14 m13 (mword_of_int 0x724)
              (mword_of_int 241 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x706) (6 + (16 + (24 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_724 with "Hcode"). }
    iIntros (h15) "Hrun".
    (* ---- 0x726/0x72a  the semicolon table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h15 m13 (mword_of_int 0x726)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x1726) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_addi γt γd γs γfd h16 m14 (mword_of_int 0x72a)
              (mword_of_int 3082 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_list) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_cmv γt γd γs γfd h17 m15 (mword_of_int 0x72e) a1_idx
              s3_idx (mword_of_int (s0 + Z.of_nat len))
              (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_cmv γt γd γs γfd h18 m16 (mword_of_int 0x730) a0_idx
              s2_idx (mword_of_int ps) (6 + (16 + (24 + nn)))
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
    iApply (wp_uk_jal γt γd γs γfd h19 m17 (mword_of_int 0x732)
              (mword_of_int 2096406 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x736)
              (6 + (16 + (24 + nn)))
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
              (mword_of_int (s0 + Z.of_nat len)) (36 + nn)
              Ha0_18 Ha1_18 Ha2_18 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_list; lia)
              ltac:(unfold ushp_T_list, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_list 1 DfracDiscarded
                ushp_T_list_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h21 m19) "%Hcs1819 %Ha0_19 Hrun".
    rewrite Eret18 Elen0.
    rewrite (ushp_peek_res_sym len f (len + ushp_skipws (len - len) len f)%nat
               1 ushp_T_list Hnosym ushp_T_list_sym) in Ha0_19.
    (* ---- 0x736  c.bnez a0 -- NOT taken: there is no list ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h21 m19 (mword_of_int 0x736)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x74a) (6 + (16 + (24 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_19; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_736 with "Hcode"). }
    iIntros (h22) "Hrun".
    (* ---- 0x738  c.mv a0,s1 ---- *)
    assert (Hs1_19 : m19 !!! Regidx s1_idx = mword_of_int p).
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
               (regval_into_reg (mword_of_int p : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h22 m19 (mword_of_int 0x738) a0_idx
              s1_idx (mword_of_int p) (6 + (16 + (24 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_19; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_738 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m19).
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
              (6 + (16 + (24 + nn))) h23 me
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
    iApply ("Hcont" $! p with "[] Hnode Hcur Hstr Hws Hsy [] [] HM' Hrun").
    - iPureIntro. exact Hpsz.
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
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* §13 nulterminate @0x7ee -- the jump table, and the ONE leaf this file  *)
  (*     could not build.                                                   *)
  (*                                                                       *)
  (*   struct cmd *nulterminate(struct cmd *cmd) {                          *)
  (*     if(cmd == 0) return 0;                                             *)
  (*     switch(cmd->type) {                                                *)
  (*     case EXEC: for(i = 0; ecmd->argv[i]; i++) *ecmd->eargv[i] = 0;      *)
  (*     ... }                                                              *)
  (*     return cmd; }                                                      *)
  (*                                                                       *)
  (* THIS IS WHERE THE TOKEN BOUNDARIES BECOME C STRINGS.  parseexec left   *)
  (* argv[i] and eargv[i] as two pointers INTO THE LINE; nulterminate       *)
  (* writes a NUL at every eargv[i], and after it the bytes from argv[i]    *)
  (* are the NUL-terminated argument [exec] observes.  The walk says        *)
  (* exactly that and no more: the node is unchanged and the line comes     *)
  (* back as [ushp_nulfold toks], the original bytes with a zero at each    *)
  (* token's END INDEX.                                                     *)
  (*                                                                       *)
  (* THE ONE HYPOTHESIS THIS FUNCTION FORCES.  The switch is a genuine      *)
  (* computed transfer through a table in .rodata, and .rodata is the TEXT  *)
  (* half, so the [c.lw a5,0(a5)] at 0x814 is a FOUR-BYTE LOAD OUT OF THE   *)
  (* TEXT HALF.  [UkRunMem.wp_uk_lbu_text] is one byte and                  *)
  (* [UkRunMem.wp_uk_clw] takes [ubytes γd].  The leaf EXISTS -- it is      *)
  (* [UkShRun.wp_uk_clw_text], built for runcmd's own jump table -- but it  *)
  (* is [Local] to that file, so this walk cannot name it.                  *)
  (* [ushp_clw_text_ok] below is its statement, VERBATIM, and the discharge *)
  (* is one [exact] the moment relocation ask 3 lands it in [UkRunMem.v].   *)
  (* Round 3 recorded this leaf as a BASE-encoding [lw]; the catalog says   *)
  (* [c.lw], so the ask is the compressed one and it is already written.    *)
  (* ===================================================================== *)

  Hypothesis ushp_clw_text_ok :
    forall (h : CpuId) (m : regfile) (pc : mword 64)
           (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (a : Z)
           (wv : mword 32) (avail : nat),
      unot_sp rd ->
      creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
      creg2reg_idx (Cregidx crd) = Regidx rd ->
      a = uint (m !!! Regidx rs1) + uoff_c4 uimm ->
      a mod 4 = 0 ->
      uint rd <> 0 ->
      uinstr_is γt pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) -∗
      ([∗ list] j ∈ seq 0 4, utext γt (a + Z.of_nat j) (nth_byte wv j)) -∗
      urun γt γd γs γfd h m pc avail -∗
      (∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx rd := regval_into_reg (sign_extend' 64 wv)]> m)
           (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).

  (* ---- the line, and what the loop does to it ------------------------- *)
  Definition ushp_setb (g : nat -> bv 8) (j : nat) (b : bv 8) : nat -> bv 8 :=
    fun i => if Nat.eqb i j then b else g i.

  Fixpoint ushp_nulfold (toks : list (nat * nat)) (g : nat -> bv 8)
    : nat -> bv 8 :=
    match toks with
    | [] => g
    | tk :: r => ushp_nulfold r (ushp_setb g (snd tk) ubyte0)
    end.

  Lemma ushp_bytes_upd (a : Z) (n : nat) (g : nat -> bv 8) (j : nat)
      (b : bv 8) :
    (j < n)%nat ->
    ubytes γd a n g -∗
    ubyte γd (a + Z.of_nat j) (g j) ∗
    (ubyte γd (a + Z.of_nat j) b -∗ ubytes γd a n (ushp_setb g j b)).
  Proof.
    intro Hj. iIntros "H".
    assert (Hjs : seq 0 n !! j = Some j) by (apply lookup_seq; lia).
    rewrite /ubytes /ubytesq.
    rewrite (big_sepL_delete
               (fun _ i : nat => ubyteq γd (DfracOwn 1) (a + Z.of_nat i) (g i))
               (seq 0 n) j j Hjs).
    iDestruct "H" as "[Hj Hrest]". iFrame "Hj". iIntros "Hj".
    rewrite (big_sepL_delete
               (fun _ i : nat =>
                  ubyteq γd (DfracOwn 1) (a + Z.of_nat i)
                    (ushp_setb g j b i))
               (seq 0 n) j j Hjs).
    iSplitL "Hj".
    { assert (Ehit : ushp_setb g j b j = b)
        by (rewrite /ushp_setb Nat.eqb_refl; reflexivity).
      rewrite Ehit. iExact "Hj". }
    iApply (big_sepL_mono with "Hrest").
    intros k y Hy. apply lookup_seq in Hy as [ -> Hlt ].
    rewrite Nat.add_0_l.
    destruct (decide (k = j)) as [ Ek | Ek ]; [ done | ].
    assert (Ese : ushp_setb g j b k = g k)
      by (rewrite /ushp_setb (proj2 (Nat.eqb_neq k j) Ek); reflexivity).
    rewrite Ese. done.
  Qed.

  (* ---- reading one slot of a FINISHED node ---------------------------- *)
  Lemma ushp_slot_read (t0 base : Z) (toks : list (nat * nat))
      (sel : nat * nat -> nat) (i : nat) :
    (i < 10)%nat ->
    ([∗ list] j ∈ seq 0 10, ushp_slot t0 base toks sel j) -∗
    ushp_slot t0 base toks sel i ∗
    (ushp_slot t0 base toks sel i -∗
     [∗ list] j ∈ seq 0 10, ushp_slot t0 base toks sel j).
  Proof.
    intro Hi. iIntros "H".
    iApply (big_sepL_lookup_acc _ (seq 0 10) i i
              ltac:(apply lookup_seq; lia) with "H").
  Qed.

  (* ---- one byte of the read-only image, by its address ---------------- *)
  Lemma ushp_ro_byte (a : Z) (b : bv 8) :
    shp_ro !! a = Some b -> shp_rodata γt -∗ utext γt a b.
  Proof.
    intro Ha. iIntros "#H". rewrite /shp_rodata /utext_img.
    iApply (big_sepM_lookup _ _ a b with "H"). exact Ha.
  Qed.

  (* ...and the FOUR that make the EXEC arm's jump-table entry.  The entry
     is a signed displacement from the table's own base, so 0x13b0 plus it
     is 0x81a -- which is checked by [vm_compute] below, not asserted. *)
  Lemma ushp_jrow_exec :
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4,
      utext γt (0x13b4 + Z.of_nat j)
        (nth_byte (mword_of_int 4294964330 : mword 32) j).
  Proof.
    iIntros "#H". rewrite !big_sepL_cons big_sepL_nil.
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 0%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 0%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 1%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 1%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 2%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 2%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 3%nat)
                        (nth_byte (mword_of_int 4294964330 : mword 32) 3%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | done ].
  Qed.

  (* ---- the EXEC arm's loop, 0x822..0x82e ------------------------------ *)
  Lemma wp_kshp_nul_loop (s0 p : Z) (len : nat) (nn : nat) :
    forall (rest : list (nat * nat)) (done : list (nat * nat))
           (tk : nat * nat) (toks : list (nat * nat)) (g : nat -> bv 8)
           (h : CpuId) (mc : regfile),
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    toks = done ++ tk :: rest ->
    (length toks < 10)%nat ->
    (forall (i : nat) (t : nat * nat), toks !! i = Some t ->
       (fst t <= len)%nat /\ (snd t <= len)%nat) ->
    mc !!! Regidx a5_idx
      = mword_of_int (p + 16 + 8 * Z.of_nat (length done)) ->
    shp_code γt -∗
    ushp_exec_at s0 p toks -∗
    ubytes γd s0 (S len) g -∗
    urun γt γd γs γfd h mc (mword_of_int 0x822) nn -∗
    (ushp_exec_at s0 p toks -∗
     ubytes γd s0 (S len) (ushp_nulfold (tk :: rest) g) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x83e) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro rest.
    induction rest as [| tk' rest IH ];
      intros done tk toks g h mc Hs0 Hs64 Hp0 Hp8 Hpsz Htoksd Htlen Hsnd Ha5;
      iIntros "#Hcode Hnode Hline Hrun Hcont".
    all: assert (Hlk : toks !! (length done) = Some tk)
      by (rewrite Htoksd; exact (ushp_lookup_app_mid' done tk _)).
    all: assert (Ht2 : (S (length done) <= length toks)%nat);
      [ rewrite Htoksd ushp_len_app_cons; lia | ].
    all: assert (Hdlen : (S (length done) < 10)%nat) by lia.
    all: assert (Hsndtk : (snd tk <= len)%nat)
      by exact (proj2 (Hsnd _ _ Hlk)).
    all: iDestruct "Hnode" as "(%Hnl & %Hnp & %Hna & Hty & Hav & Hev)".
    (* ---- 0x822  c.ld a4,72(a5) -- eargv[i] ---- *)
    all: iDestruct (ushp_slot_read s0 (p + 88) toks snd (length done)
                      ltac:(lia) with "Hev") as "[Hslot Hevc]".
    all: assert (Eslot : ushp_slot s0 (p + 88) toks snd (length done)
                         = uword γd (p + 88 + 8 * Z.of_nat (length done))
                             (mword_of_int (s0 + Z.of_nat (snd tk))))
      by (rewrite /ushp_slot Hlk; reflexivity).
    all: rewrite Eslot.
    all: iApply (wp_uk_cld γt γd γs γfd h mc (mword_of_int 0x822)
                   (mword_of_int 9 : mword 5) (mword_of_int 7 : mword 3)
                   (mword_of_int 6 : mword 3) a5_idx a4_idx
                   (p + 88 + 8 * Z.of_nat (length done))
                   (mword_of_int (s0 + Z.of_nat (snd tk))) nn
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   ltac:(rewrite Ha5
                           (uint_moi (p + 16 + 8 * Z.of_nat (length done))
                              ltac:(unfold Z64 in *; lia));
                         vm_compute uoff_c8; lia)
                   ltac:(exact (ushp_slot_al8 p 11 (length done) Hp8))
                   ltac:(vm_compute; discriminate)
                   with "[] Hslot Hrun");
      [ iApply (uis_shp_822 with "Hcode") | ].
    all: iIntros "Hslot" (h1) "Hrun".
    all: iDestruct ("Hevc" with "Hslot") as "Hev".
    all: set (n1 := <[Regidx a4_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat (snd tk))
                            : mword 64)]> mc).
    all: assert (Hn1 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                   n1 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc (Regidx a4_idx) (Regidx q) _ Hq)).
    all: assert (Ha4_1 : n1 !!! Regidx a4_idx
                         = mword_of_int (s0 + Z.of_nat (snd tk)))
      by exact (upd_eq mc (Regidx a4_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat (snd tk)) : mword 64))).
    (* ---- 0x824  sb zero,0(a4) -- THE NUL ---- *)
    all: iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    all: iDestruct (ushp_bytes_upd s0 (S len) g (snd tk) ubyte0
                      ltac:(lia) with "Hline") as "[Hb Hbc]".
    all: iApply (wp_uk_sb γt γd γs γfd h1 n1 (mword_of_int 0x824)
                   (mword_of_int 0 : mword 12) a4_idx x0_idx
                   (s0 + Z.of_nat (snd tk)) (g (snd tk)) nn
                   ltac:(rewrite Ha4_1
                           (uint_moi (s0 + Z.of_nat (snd tk))
                              ltac:(unfold Z64 in *; lia));
                         vm_compute uoff_i12; lia)
                   with "[] Hb Hrun");
      [ iApply (uis_shp_824 with "Hcode") | ].
    all: iIntros "Hb" (h2) "Hrun".
    all: rewrite Hx0.
    all: assert (Enb : nth_byte (zero_reg : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    all: rewrite Enb.
    all: iDestruct ("Hbc" with "Hb") as "Hline".
    (* ---- 0x828  c.addi a5,a5,8 ---- *)
    all: assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6)
                         : mword 64) = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    all: iApply (wp_uk_caddi γt γd γs γfd h2 n1 (mword_of_int 0x828)
                   (mword_of_int 8 : mword 6) a5_idx
                   (mword_of_int (p + 16 + 8 * Z.of_nat (length done) + 8)) nn
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hn1 a5_idx ltac:(vm_compute; discriminate))
                           Ha5 Esx8; symmetry; apply moi_add)
                   with "[] Hrun");
      [ iApply (uis_shp_828 with "Hcode") | ].
    all: iIntros (h3) "Hrun".
    all: set (n2 := <[Regidx a5_idx
                      := regval_into_reg
                           (mword_of_int
                              (p + 16 + 8 * Z.of_nat (length done) + 8)
                            : mword 64)]> n1).
    all: assert (Hn2 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                   n2 !!! Regidx q = n1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n1 (Regidx a5_idx) (Regidx q) _ Hq)).
    all: assert (Ha5_2 : n2 !!! Regidx a5_idx
                         = mword_of_int
                             (p + 16 + 8 * Z.of_nat (length done) + 8))
      by exact (upd_eq n1 (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int (p + 16 + 8 * Z.of_nat (length done) + 8)
                      : mword 64))).
    all: iDestruct (ushp_slot_read s0 (p + 8) toks fst
                      (S (length done)) ltac:(lia) with "Hav")
           as "[Hnx Havc]".
    - (* ======= the LAST token: argv[i+1] is the NULL cap ============== *)
      assert (Ecap : toks !! S (length done) = None)
        by (rewrite Htoksd ushp_lookup_app_past; reflexivity).
      assert (Ecl : (S (length done) = length toks)%nat).
      { rewrite Htoksd ushp_len_app_cons. cbn [length]. lia. }
      assert (Eslotn : ushp_slot s0 (p + 8) toks fst (S (length done))
                       = uword γd (p + 8 + 8 * Z.of_nat (S (length done)))
                           (mword_of_int 0)).
      { rewrite /ushp_slot Ecap (bool_decide_eq_true_2 _ Ecl). reflexivity. }
      rewrite Eslotn.
      (* ---- 0x82a  ld a4,-8(a5) ---- *)
      iApply (wp_uk_ld γt γd γs γfd h3 n2 (mword_of_int 0x82a)
                (mword_of_int 4088 : mword 12) a5_idx a4_idx (DfracOwn 1)
                (p + 8 + 8 * Z.of_nat (S (length done)))
                (mword_of_int 0) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha5_2
                        (uint_moi (p + 16 + 8 * Z.of_nat (length done) + 8)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (S (length done)) Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_82a with "Hcode"). }
      iIntros "Hnx" (h4) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (n3 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> n2).
      assert (Hn3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                 n3 !!! Regidx q = n2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n2 (Regidx a4_idx) (Regidx q) _ Hq)).
      assert (Ha4_3 : n3 !!! Regidx a4_idx = (mword_of_int 0 : mword 64))
        by exact (upd_eq n2 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 0 : mword 64))).
      (* ---- 0x82e  c.bnez a4 -- NOT taken: the vector is capped ---- *)
      iApply (wp_uk_cbnez γt γd γs γfd h4 n3 (mword_of_int 0x82e)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3)
                a4_idx false (mword_of_int 0x822) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha4_3; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_82e with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x830  c.j 0x83e ---- *)
      iApply (wp_uk_cj γt γd γs γfd h5 n3 (mword_of_int 0x830)
                (mword_of_int 7 : mword 11) (mword_of_int 0x83e) nn
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_830 with "Hcode"). }
      iIntros (h6) "Hrun".
      iApply ("Hcont" with "[Hty Hav Hev] Hline [] Hrun").
      + rewrite /ushp_exec_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty"; [ iExact "Hty" | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
      + iPureIntro. intros r Hr.
        rewrite (Hn3 r (ushp_cs_ne r a4_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hn2 r (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hn1 r (ushp_cs_ne r a4_idx Hr
                          ltac:(vm_compute; reflexivity))).
        reflexivity.
    - (* ======= ANOTHER token: argv[i+1] points into the line ========== *)
      assert (Enx : toks !! S (length done) = Some tk')
        by (rewrite Htoksd; exact (ushp_lookup_app_next done tk tk' rest)).
      assert (Eslotn : ushp_slot s0 (p + 8) toks fst (S (length done))
                       = uword γd (p + 8 + 8 * Z.of_nat (S (length done)))
                           (mword_of_int (s0 + Z.of_nat (fst tk'))))
        by (rewrite /ushp_slot Enx; reflexivity).
      rewrite Eslotn.
      assert (Hfst' : (fst tk' <= len)%nat)
        by exact (proj1 (Hsnd _ _ Enx)).
      (* ---- 0x82a  ld a4,-8(a5) ---- *)
      iApply (wp_uk_ld γt γd γs γfd h3 n2 (mword_of_int 0x82a)
                (mword_of_int 4088 : mword 12) a5_idx a4_idx (DfracOwn 1)
                (p + 8 + 8 * Z.of_nat (S (length done)))
                (mword_of_int (s0 + Z.of_nat (fst tk'))) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha5_2
                        (uint_moi (p + 16 + 8 * Z.of_nat (length done) + 8)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (S (length done)) Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_82a with "Hcode"). }
      iIntros "Hnx" (h4) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (n3 := <[Regidx a4_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat (fst tk'))
                         : mword 64)]> n2).
      assert (Hn3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                 n3 !!! Regidx q = n2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n2 (Regidx a4_idx) (Regidx q) _ Hq)).
      assert (Ha4_3 : n3 !!! Regidx a4_idx
                      = mword_of_int (s0 + Z.of_nat (fst tk')))
        by exact (upd_eq n2 (Regidx a4_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat (fst tk'))
                        : mword 64))).
      (* ---- 0x82e  c.bnez a4 -- TAKEN: the line's address is not 0 ---- *)
      iApply (wp_uk_cbnez γt γd γs γfd h4 n3 (mword_of_int 0x82e)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3)
                a4_idx true (mword_of_int 0x822) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha4_3;
                      assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Ezr;
                      rewrite (moi_neq_vec (s0 + Z.of_nat (fst tk')) 0
                                 ltac:(unfold Z64 in *; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hnz : (s0 + Z.of_nat (fst tk') =? 0) = false)
                        by (apply Z.eqb_neq; lia);
                      rewrite Hnz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_82e with "Hcode"). }
      iIntros (h5) "Hrun".
      iApply (IH (done ++ [tk]) tk' toks (ushp_setb g (snd tk) ubyte0) h5 n3
                Hs0 Hs64 Hp0 Hp8 Hpsz
                ltac:(rewrite Htoksd; symmetry; apply ushp_app_cons)
                Htlen Hsnd
                ltac:(rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate))
                        Ha5_2 ushp_len_app1; f_equal;
                      rewrite Nat2Z.inj_succ; lia)
                with "Hcode [Hty Hav Hev] Hline Hrun").
      { rewrite /ushp_exec_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty"; [ iExact "Hty" | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
      iIntros "Hnode Hline" (hf mf) "%Hpres Hrun".
      iApply ("Hcont" with "Hnode Hline [] Hrun").
      iPureIntro. intros r Hr.
      rewrite (Hpres r Hr)
              (Hn3 r (ushp_cs_ne r a4_idx Hr ltac:(vm_compute; reflexivity)))
              (Hn2 r (ushp_cs_ne r a5_idx Hr ltac:(vm_compute; reflexivity)))
              (Hn1 r (ushp_cs_ne r a4_idx Hr ltac:(vm_compute; reflexivity))).
      reflexivity.
  Qed.


  (* ---- the common landing, 0x83e..0x848 -------------------------------- *)
  (* Both ways out of the switch -- the empty argument vector and the loop's
     exit -- arrive here, so the [c.mv a0,s1] and the epilogue are one
     lemma rather than two copies. *)
  Lemma wp_kshp_nul_fin (sp0 spl : mword 64) (vals : nat -> mword 64)
      (p : Z) (nn : nat) (h : CpuId) (me : regfile) :
    uint sp0 mod 8 = 0 -> 32 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 24 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)) ->
    me !!! Regidx s1_idx = mword_of_int p ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 1 -∗
    urun γt γd γs γfd h me (mword_of_int 0x83e) nn -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals
               (<[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> me)))
         (ret_pc (vals 0%nat)) (4 + nn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hal8 Hlo Hhi Hsplu Hsp Hs1.
    iIntros "#Hcode Hsl Hloc Hrun Hcont".
    iApply (wp_uk_cmv γt γd γs γfd h me (mword_of_int 0x83e) a0_idx s1_idx
              (mword_of_int p) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_83e with "Hcode"). }
    iIntros (h1) "Hrun".
    set (mz := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> me).
    assert (Hspz : mz !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne me (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp. }
    iApply (wp_kshp_frame_epi 4 1 [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] (mword_of_int 3 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x840 | 1%nat => 0x842
                              | 2%nat => 0x844 | _ => 0x846 end)
              (mword_of_int 2 : mword 6) sp0 spl vals nn h1 mz
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(cbn [length]; lia)
              Hspz
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| i ]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| i ]]];
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
      iSplit; [ iApply (uis_shp_840 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_842 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_844 with "Hcode") | done ]. }
    { iApply (uis_shp_846 with "Hcode"). }
    { iApply (uis_shp_848 with "Hcode"). }
    iIntros (hf) "Hrun". iApply ("Hcont" $! hf with "Hrun").
  Qed.

  (* ---- nulterminate, the whole function -------------------------------- *)
  (* TAINT: [ushp_clw_text_ok], and nothing else -- it allocates nothing. *)
  Lemma wp_kshp_nulterminate (h : CpuId) (m : regfile) (s0 p : Z) (len : nat)
      (g : nat -> bv 8) (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int p ->
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (length toks < 10)%nat ->
    (forall (i : nat) (t : nat * nat), toks !! i = Some t ->
       (fst t <= len)%nat /\ (snd t <= len)%nat) ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_exec_at s0 p toks -∗
    ubytes γd s0 (S len) g -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.nulterminate) (4 + nn) -∗
    (ushp_exec_at s0 p toks -∗
     ubytes γd s0 (S len) (ushp_nulfold toks g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hs0 Hs64 Hp0 Hp8 Hpsz Htlen Hsnd.
    iIntros "#Hcode #Hro Hnode Hline Hrun Hcont".
    rewrite shpp_nulterminate.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | _ => m !!! Regidx s1_idx end).
    (* ---- 0x7ee  c.addi sp,sp,-32 ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x7ee)
              (mword_of_int 32 : mword 6) 4 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7ee with "Hcode"). }
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 4))).
    assert (Hspu : uint spn = uint sp0 - 32).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 24)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 1 [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    (* ---- 0x7f0..0x7f4  the three spills ---- *)
    iApply (wp_kshp_spill spn nn [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x7f0 | 1%nat => 0x7f2
                              | 2%nat => 0x7f4 | _ => 0x7f6 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| [| i ]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| i ]]];
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
      iSplit; [ iApply (uis_shp_7f0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7f2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7f4 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x7f6  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_kshp_fp h2 m1 0x7f6 (mword_of_int 8 : mword 8) nn
              with "[] Hrun").
    { iApply (uis_shp_7f6 with "Hcode"). }
    iIntros (h3 v) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x7f8  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x7f8) s1_idx a0_idx
              (mword_of_int p) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_7f8 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Hs1_3 : m3 !!! Regidx s1_idx = mword_of_int p)
      by exact (upd_eq m2 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    assert (Hsp3 : m3 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x7fa  c.beqz a0 -- NOT taken: the node is not null ---- *)
    iApply (wp_uk_cbeqz γt γd γs γfd h4 m3 (mword_of_int 0x7fa)
              (mword_of_int 34 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x83e) nn
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3;
                    assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ezr;
                    rewrite (moi_eq_vec p 0 ltac:(unfold Z64 in *; lia)
                               ltac:(unfold Z64; lia));
                    assert (Hnz : (p =? 0) = false)
                      by (apply Z.eqb_neq; lia);
                    rewrite Hnz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7fa with "Hcode"). }
    iIntros (h5) "Hrun".
    (* ---- the node's type word, read twice ---- *)
    iDestruct "Hnode" as "(%Hnl & %Hnp & %Hna & Hty & Hav & Hev)".
    iDestruct "Hty" as "[Hty4 Hpad]".
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    (* ---- 0x7fc  c.lw a4,0(a0) ---- *)
    iApply (wp_uk_clw γt γd γs γfd h5 m3 (mword_of_int 0x7fc)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx p
              (mword_of_int 1 : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c4; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_7fc with "Hcode"). }
    iIntros "Hty4" (h6) "Hrun".
    set (m4 := <[Regidx a4_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 32)
                       : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_4 : m4 !!! Regidx a4_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_eq m3 (Regidx a4_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x7fe  c.li a5,5 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h6 m4 (mword_of_int 0x7fe)
              (mword_of_int 5 : mword 6) a5_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7fe with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m5 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 5 : mword 6)
                       : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_5 : m5 !!! Regidx a5_idx = (mword_of_int 5 : mword 64)).
    { rewrite (upd_eq m4 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 5 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int 1 : mword 64)).
    { rewrite (Hm5 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_4. }
    (* ---- 0x800  bltu a5,a4 -- NOT taken: EXEC is in range ---- *)
    iApply (wp_uk_btype γt γd γs γfd h7 m5 (mword_of_int 0x800)
              (mword_of_int 62 : mword 13) a4_idx a5_idx BLTU false
              (mword_of_int 0x83e) nn
              ltac:(cbn [uv_btaken]; rewrite Ha5_5 Ha4_5;
                    rewrite (moi_lt_u 5 1 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia)); reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_800 with "Hcode"). }
    iIntros (h8) "Hrun".
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_3. }
    (* ---- 0x804  lwu a5,0(a0) ---- *)
    iApply (wp_uk_lwu γt γd γs γfd h8 m5 (mword_of_int 0x804)
              (mword_of_int 0 : mword 12) a0_idx a5_idx p
              (mword_of_int 1 : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_5 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_804 with "Hcode"). }
    iIntros "Hty4" (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (zero_extend' 64 (mword_of_int 1 : mword 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_eq m5 (Regidx a5_idx)
                 (regval_into_reg
                    (zero_extend' 64 (mword_of_int 1 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x808  c.slli a5,a5,0x2 ---- *)
    iApply (wp_uk_cslli γt γd γs γfd h9 m6 (mword_of_int 0x808)
              (mword_of_int 2 : mword 6) a5_idx (mword_of_int 4) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_6 (moi_shl 1 2 ltac:(lia)); f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_808 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 4 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_7 : m7 !!! Regidx a5_idx = (mword_of_int 4 : mword 64))
      by exact (upd_eq m6 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 4 : mword 64))).
    (* ---- 0x80a/0x80e  the jump table's base ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h10 m7 (mword_of_int 0x80a)
              (mword_of_int 1 : mword 20) a4_idx
              (mword_of_int 0x180a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_80a with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x180a : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int 0x180a)
      by exact (upd_eq m7 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x180a : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h11 m8 (mword_of_int 0x80e)
              (mword_of_int 2982 : mword 12) a4_idx a4_idx
              (mword_of_int 0x13b0) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_8; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_80e with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x13b0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = mword_of_int 0x13b0)
      by exact (upd_eq m8 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x13b0 : mword 64))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = (mword_of_int 4 : mword 64)).
    { rewrite (Hm9 a5_idx ltac:(vm_compute; discriminate))
              (Hm8 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0x812  c.add a5,a5,a4 -- the row's address ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h12 m9 (mword_of_int 0x812) a5_idx
              a4_idx (mword_of_int 0x13b4) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_9 Ha4_9; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_812 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x13b4 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_10 : m10 !!! Regidx a5_idx = mword_of_int 0x13b4)
      by exact (upd_eq m9 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 0x13b4 : mword 64))).
    (* ---- 0x814  c.lw a5,0(a5) -- THE TEXT-HALF LOAD (the Hypothesis) ---- *)
    iApply (ushp_clw_text_ok h13 m10 (mword_of_int 0x814)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx 0x13b4
              (mword_of_int 4294964330 : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_10;
                    rewrite (uint_moi 0x13b4 ltac:(unfold Z64; lia));
                    vm_compute uoff_c4; lia)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] [] Hrun").
    { iApply (uis_shp_814 with "Hcode"). }
    { iApply (ushp_jrow_exec with "Hro"). }
    iIntros (h14) "Hrun".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64
                          (mword_of_int 4294964330 : mword 32)
                        : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha4_11 : m11 !!! Regidx a4_idx = mword_of_int 0x13b0).
    { rewrite (Hm11 a4_idx ltac:(vm_compute; discriminate))
              (Hm10 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_9. }
    (* ---- 0x816  c.add a5,a5,a4 -- the arm's pc ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h14 m11 (mword_of_int 0x816) a5_idx
              a4_idx (mword_of_int 0x81a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_11
                      (upd_eq m10 (Regidx a5_idx)
                         (regval_into_reg
                            (sign_extend' 64
                               (mword_of_int 4294964330 : mword 32)
                             : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_816 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x81a : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a5_idx) (Regidx q) _ Hq)).
    (* ---- 0x818  c.jr a5 -- the switch ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h15 m12 (mword_of_int 0x818) a5_idx
              (mword_of_int 0x81a) nn
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m11 (Regidx a5_idx)
                               (regval_into_reg
                                  (mword_of_int 0x81a : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_818 with "Hcode"). }
    iIntros (h16) "Hrun".
    (* ---- 0x81a  c.ld a5,8(a0) -- argv[0] ---- *)
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate))
              (Hm11 a0_idx ltac:(vm_compute; discriminate))
              (Hm10 a0_idx ltac:(vm_compute; discriminate))
              (Hm9 a0_idx ltac:(vm_compute; discriminate))
              (Hm8 a0_idx ltac:(vm_compute; discriminate))
              (Hm7 a0_idx ltac:(vm_compute; discriminate))
              (Hm6 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_5. }
    assert (Hkeep12 : forall q : mword 5, ucallee_saved_idx q = true ->
              m12 !!! Regidx q = m3 !!! Regidx q).
    { intros q Hq.
      rewrite (Hm12 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm11 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm10 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm9 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm8 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm7 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm6 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm5 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity)))
              (Hm4 q (ushp_cs_ne q a4_idx Hq ltac:(vm_compute; reflexivity))).
      reflexivity. }
    iDestruct (ushp_slot_read s0 (p + 8) toks fst 0%nat ltac:(lia)
                 with "Hav") as "[Hnx Havc]".
    destruct toks as [| tk rest ].
    - (* ======= NO ARGUMENTS: argv[0] is the cap ======================= *)
      assert (Eslot0 : ushp_slot s0 (p + 8) [] fst 0%nat
                       = uword γd (p + 8 + 8 * Z.of_nat 0)
                           (mword_of_int 0))
        by reflexivity.
      rewrite Eslot0.
      iApply (wp_uk_cld γt γd γs γfd h16 m12 (mword_of_int 0x81a)
                (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 7 : mword 3) a0_idx a5_idx
                (p + 8 + 8 * Z.of_nat 0) (mword_of_int 0) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_12
                        (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(exact (ushp_slot_al8 p 1 0%nat Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_81a with "Hcode"). }
      iIntros "Hnx" (h17) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (m13 := <[Regidx a5_idx
                    := regval_into_reg (mword_of_int 0 : mword 64)]> m12).
      assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                       m13 !!! Regidx q = m12 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m12 (Regidx a5_idx) (Regidx q) _ Hq)).
      assert (Ha5_13 : m13 !!! Regidx a5_idx = (mword_of_int 0 : mword 64))
        by exact (upd_eq m12 (Regidx a5_idx)
                    (regval_into_reg (mword_of_int 0 : mword 64))).
      (* ---- 0x81c  c.beqz a5 -- TAKEN: nothing to nul-terminate ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h17 m13 (mword_of_int 0x81c)
                (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0x83e) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha5_13; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_81c with "Hcode"). }
      iIntros (h18) "Hrun".
      iApply (wp_kshp_nul_fin sp0 spl vals p nn h18 m13
                Hal8 Hlo ltac:(lia) Hsplu
                ltac:(rewrite (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hkeep12 csp_rs1 ltac:(vm_compute; reflexivity));
                      exact Hsp3)
                ltac:(rewrite (Hm13 s1_idx ltac:(vm_compute; discriminate))
                        (Hkeep12 s1_idx ltac:(vm_compute; reflexivity));
                      exact Hs1_3)
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with "[Hty4 Hpad Hav Hev] Hline [] [] Hrun").
      + rewrite /ushp_exec_at /ushp_type_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                 iExact "Hpad" ] | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
      + iPureIntro.
        apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals m
                 (<[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> m13)
                 sp0 eq_refl).
        * intros i r u Hi.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; reflexivity.
        * intros q Hq Hqsp Hmiss.
          rewrite (upd_ne m13 (Regidx a0_idx) (Regidx q) _
                     (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
                  (Hm13 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hkeep12 q Hq)
                  (Hm3 q (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6)
                            eq_refl))
                  (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6)
                            eq_refl))
                  (Hm1 q Hqsp).
          reflexivity.
      + iPureIntro.
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        apply ushp_spillback_eq.
        * intros _.
          exact (upd_eq m13 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))).
        * intros i r u Hi He.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
    - (* ======= AT LEAST ONE ARGUMENT: into the loop =================== *)
      assert (Eslot0 : ushp_slot s0 (p + 8) (tk :: rest) fst 0%nat
                       = uword γd (p + 8 + 8 * Z.of_nat 0)
                           (mword_of_int (s0 + Z.of_nat (fst tk))))
        by reflexivity.
      rewrite Eslot0.
      assert (Hfst0 : (fst tk <= len)%nat)
        by exact (proj1 (Hsnd 0%nat tk eq_refl)).
      iApply (wp_uk_cld γt γd γs γfd h16 m12 (mword_of_int 0x81a)
                (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 7 : mword 3) a0_idx a5_idx
                (p + 8 + 8 * Z.of_nat 0)
                (mword_of_int (s0 + Z.of_nat (fst tk))) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_12
                        (uint_moi p ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_c8; lia)
                ltac:(exact (ushp_slot_al8 p 1 0%nat Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_81a with "Hcode"). }
      iIntros "Hnx" (h17) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (m13 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat (fst tk))
                          : mword 64)]> m12).
      assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                       m13 !!! Regidx q = m12 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m12 (Regidx a5_idx) (Regidx q) _ Hq)).
      assert (Ha5_13 : m13 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat (fst tk)))
        by exact (upd_eq m12 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat (fst tk)) : mword 64))).
      (* ---- 0x81c  c.beqz a5 -- NOT taken ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h17 m13 (mword_of_int 0x81c)
                (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx false (mword_of_int 0x83e) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha5_13;
                      assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Ezr;
                      rewrite (moi_eq_vec (s0 + Z.of_nat (fst tk)) 0
                                 ltac:(unfold Z64 in *; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hnz : (s0 + Z.of_nat (fst tk) =? 0) = false)
                        by (apply Z.eqb_neq; lia);
                      rewrite Hnz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_81c with "Hcode"). }
      iIntros (h18) "Hrun".
      (* ---- 0x81e  addi a5,a0,16 ---- *)
      assert (Ha0_13 : m13 !!! Regidx a0_idx = mword_of_int p).
      { rewrite (Hm13 a0_idx ltac:(vm_compute; discriminate)).
        exact Ha0_12. }
      iApply (wp_uk_addi γt γd γs γfd h18 m13 (mword_of_int 0x81e)
                (mword_of_int 16 : mword 12) a0_idx a5_idx
                (mword_of_int (p + 16)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_13;
                      assert (Ei : (sign_extend' 64
                                      (mword_of_int 16 : mword 12)
                                    : mword 64) = mword_of_int 16)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Ei; symmetry; apply moi_add)
                with "[] Hrun").
      { iApply (uis_shp_81e with "Hcode"). }
      iIntros (h19) "Hrun".
      set (m14 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (p + 16) : mword 64)]> m13).
      assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                       m14 !!! Regidx q = m13 !!! Regidx q)
        by (intros q Hq; exact (upd_ne m13 (Regidx a5_idx) (Regidx q) _ Hq)).
      iApply (wp_kshp_nul_loop s0 p len nn rest (@nil (nat * nat)) tk
                (tk :: rest) g h19 m14
                Hs0 Hs64 Hp0 Hp8 Hpsz eq_refl Htlen Hsnd
                ltac:(assert (Ep16 : p + 16
                                     + 8 * Z.of_nat
                                             (length (@nil (nat * nat)))
                                     = p + 16)
                        by (cbn [length]; lia);
                      rewrite Ep16;
                      exact (upd_eq m13 (Regidx a5_idx)
                               (regval_into_reg
                                  (mword_of_int (p + 16) : mword 64))))
                with "Hcode [Hty4 Hpad Hav Hev] Hline Hrun").
      { rewrite /ushp_exec_at /ushp_type_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                                 iExact "Hpad" ] | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
      iIntros "Hnode Hline" (h20 mf) "%Hpresf Hrun".
      iApply (wp_kshp_nul_fin sp0 spl vals p nn h20 mf
                Hal8 Hlo ltac:(lia) Hsplu
                ltac:(rewrite (Hpresf csp_rs1
                                 ltac:(vm_compute; reflexivity))
                        (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
                        (Hkeep12 csp_rs1 ltac:(vm_compute; reflexivity));
                      exact Hsp3)
                ltac:(rewrite (Hpresf s1_idx
                                 ltac:(vm_compute; reflexivity))
                        (Hm14 s1_idx ltac:(vm_compute; discriminate))
                        (Hm13 s1_idx ltac:(vm_compute; discriminate))
                        (Hkeep12 s1_idx ltac:(vm_compute; reflexivity));
                      exact Hs1_3)
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with "Hnode Hline [] [] Hrun").
      + iPureIntro.
        apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals m
                 (<[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> mf)
                 sp0 eq_refl).
        * intros i r u Hi.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; reflexivity.
        * intros q Hq Hqsp Hmiss.
          rewrite (upd_ne mf (Regidx a0_idx) (Regidx q) _
                     (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity)))
                  (Hpresf q Hq)
                  (Hm14 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hm13 q (ushp_cs_ne q a5_idx Hq
                             ltac:(vm_compute; reflexivity)))
                  (Hkeep12 q Hq)
                  (Hm3 q (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6)
                            eq_refl))
                  (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6)
                            eq_refl))
                  (Hm1 q Hqsp).
          reflexivity.
      + iPureIntro.
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        apply ushp_spillback_eq.
        * intros _.
          exact (upd_eq mf (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))).
        * intros i r u Hi He.
          destruct i as [| [| [| i ]]];
            cbn in Hi; try discriminate Hi;
            injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ===================================================================== *)
  (* §14 parsecmd @0x86e -- the parser's front door, and the THEOREM.       *)
  (*                                                                       *)
  (*   struct cmd *parsecmd(char *s) {                                      *)
  (*     es = s + strlen(s);                                                *)
  (*     cmd = parseline(&s, es);                                           *)
  (*     peek(&s, es, "");                                                  *)
  (*     if(s != es) { fprintf(2, "leftovers: %s\n", s); panic("syntax"); }  *)
  (*     nulterminate(cmd);                                                 *)
  (*     return cmd; }                                                      *)
  (*                                                                       *)
  (* THE LEFTOVERS ARM IS REFUTED, which is the last of the five.  parseexec *)
  (* leaves the cursor at the end of the line -- its loop exits exactly when *)
  (* gettoken runs out -- and neither parsepipe nor parseline moves it       *)
  (* further, so [s == es] and the [fprintf]/[panic] pair is never fetched.  *)
  (* That is why the diagnostic subtree does not appear in this file at all. *)
  (*                                                                       *)
  (* THE CURSOR IS parsecmd's OWN LOCAL.  [&s] is a stack slot of this       *)
  (* frame, so the [uword] every function below has been threading is a      *)
  (* word of the frame the prologue just cut -- which is why the walk needs  *)
  (* the frame pointer's VALUE (it is [sp0]) and not the [∀ v] that          *)
  (* [wp_kshp_fp] hands out.                                                *)
  (* ===================================================================== *)

  (* the line as a byte run: [len] body bytes and the terminator *)
  Definition ushp_ext (len : nat) (f : nat -> bv 8) : nat -> bv 8 :=
    fun j => if bool_decide (j < len)%nat then f j else ubyte0.

  Lemma ushp_ustr_bytes (a : Z) (len : nat) (f : nat -> bv 8) :
    ustr γd (DfracOwn 1) a len f -∗ ubytes γd a (S len) (ushp_ext len f).
  Proof.
    iIntros "(_ & _ & Hbs & Hnul)".
    assert (ES : S len = (len + 1)%nat) by lia.
    rewrite ES (ubytes_app γd a len 1 (ushp_ext len f)).
    iSplitL "Hbs".
    - iApply (ushp_ubytes_ext a len f (ushp_ext len f) with "Hbs").
      intros j Hj. rewrite /ushp_ext (bool_decide_eq_true_2 _ Hj).
      reflexivity.
    - rewrite /ubytes /ubytesq. cbn [seq].
      rewrite big_sepL_cons big_sepL_nil.
      iSplitL; [ | done ].
      assert (Ez : a + Z.of_nat len + Z.of_nat 0 = a + Z.of_nat len) by lia.
      rewrite Ez.
      assert (Eh : ushp_ext len f (len + 0)%nat = ubyte0).
      { rewrite /ushp_ext
          (bool_decide_eq_false_2 (len + 0 < len)%nat ltac:(lia)).
        reflexivity. }
      rewrite Eh. iExact "Hnul".
  Qed.

  (* ---- parsecmd, the whole function ------------------------------------ *)
  (* TAINT: [ushp_malloc_ok] (through execcmd) and [ushp_clw_text_ok]
     (through nulterminate).  Nothing else. *)
  Lemma wp_kshp_parsecmd (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0%nat toks ->
    (length toks < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UMalloc -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parsecmd)
      (8 + (6 + (6 + (16 + (24 + nn))))) -∗
    (∀ p : Z,
       ushp_exec_at s0 p toks -∗
       ubytes γd s0 (S len) (ushp_nulfold toks (ushp_ext len f)) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UMalloc' -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (8 + (6 + (6 + (16 + (24 + nn))))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hnosym Htoks Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM Hrun Hcont".
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
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x86e)
              (mword_of_int 60 : mword 6) 8 (52 + nn)
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
    iApply (wp_kshp_spill spn (52 + nn) [(ra_idx, mword_of_int 7 : mword 6);
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
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 m1 (mword_of_int 0x87a)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              sp0 (52 + nn)
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
    iApply (wp_uk_sd γt γd γs γfd h3 m2 (mword_of_int 0x87c)
              (mword_of_int 4040 : mword 12) s0_idx a0_idx
              (uint sp0 - 56) wcur (52 + nn)
              ltac:(rewrite Hs0_2 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              with "[] Lcur Hrun").
    { iApply (uis_shp_87c with "Hcode"). }
    iIntros "Lcur" (h4) "Hrun".
    rewrite Ha0_2.
    (* ---- 0x880  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m2 (mword_of_int 0x880) s1_idx a0_idx
              (mword_of_int s0) (52 + nn)
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
    iApply (wp_uk_jal γt γd γs γfd h5 m3 (mword_of_int 0x882)
              (mword_of_int 430 : mword 21) ra_idx
              (mword_of_int 0xa30) (mword_of_int 0x886) (52 + nn)
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
    iApply (wp_kshp_strlen h6 m4 (DfracOwn 1) s0 len f (50 + nn)
              Ha0_4 ltac:(lia) ltac:(lia) with "Hcode Hstr Hrun").
    iIntros "Hstr" (h7 m5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    (* ---- 0x886/0x888  the 32-bit zero extension ---- *)
    assert (E32 : (2:Z) ^ 32 = 4294967296) by (vm_compute; reflexivity).
    iApply (wp_uk_cslli γt γd γs γfd h7 m5 (mword_of_int 0x886)
              (mword_of_int 32 : mword 6) a0_idx
              (mword_of_int (Z.of_nat len * 2 ^ 32)) (52 + nn)
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
    iApply (wp_uk_csrli γt γd γs γfd h8 m6 (mword_of_int 0x888)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 3) a0_idx
              (mword_of_int (Z.of_nat len)) (52 + nn)
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
    iApply (wp_uk_cadd γt γd γs γfd h9 m7 (mword_of_int 0x88a) s1_idx
              a0_idx (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
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
    iApply (wp_uk_addi γt γd γs γfd h10 m8 (mword_of_int 0x88c)
              (mword_of_int 4040 : mword 12) s0_idx s2_idx
              (mword_of_int (uint sp0 - 56)) (52 + nn)
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
    iApply (wp_uk_cmv γt γd γs γfd h11 m9 (mword_of_int 0x890) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
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
    iApply (wp_uk_cmv γt γd γs γfd h12 m10 (mword_of_int 0x892) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (52 + nn)
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
    iApply (wp_uk_jal γt γd γs γfd h13 m11 (mword_of_int 0x894)
              (mword_of_int 2096718 : mword 21) ra_idx
              (mword_of_int 0x6e2) (mword_of_int 0x898) (52 + nn)
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
    iApply (wp_kshp_parseline h14 m12 (DfracOwn 1) dw dv
              (uint sp0 - 56) s0 len 0%nat f (mword_of_int s0) toks nn
              Ha0_12 Ha1_12 ltac:(lia)
              ltac:(f_equal; lia)
              Hnosym Htoks Htlen ltac:(lia) ltac:(lia)
              Hcur0 Hcur8 Hcurz
              with "Hcode Hro Lcur Hstr Hws Hsy HM Hrun").
    iIntros (p) "%Hpsz Hnode Lcur Hstr Hws Hsy".
    iIntros (h15 m13) "%Hcs1213 %Ha0_13 HM' Hrun".
    rewrite Eret12.
    iDestruct "Hnode" as "(%Hnl & %Hp0 & %Hp8 & Hty & Hav & Hev)".
    iAssert (ushp_exec_at s0 p toks) with "[Hty Hav Hev]" as "Hnode".
    { rewrite /ushp_exec_at.
      iSplitR; [ iPureIntro; exact Hnl | ].
      iSplitR; [ iPureIntro; exact Hp0 | ].
      iSplitR; [ iPureIntro; exact Hp8 | ].
      iSplitL "Hty"; [ iExact "Hty" | ].
      iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
    (* ---- 0x898  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h15 m13 (mword_of_int 0x898) s3_idx
              a0_idx (mword_of_int p) (52 + nn)
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
    iApply (wp_uk_auipc γt γd γs γfd h16 m14 (mword_of_int 0x89a)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x189a) (52 + nn)
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
    iApply (wp_uk_addi γt γd γs γfd h17 m15 (mword_of_int 0x89e)
              (mword_of_int 2542 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_none) (52 + nn)
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
    iApply (wp_uk_cmv γt γd γs γfd h18 m16 (mword_of_int 0x8a2) a1_idx
              s1_idx (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
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
    iApply (wp_uk_cmv γt γd γs γfd h19 m17 (mword_of_int 0x8a4) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (52 + nn)
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
    iApply (wp_uk_jal γt γd γs γfd h20 m18 (mword_of_int 0x8a6)
              (mword_of_int 2096034 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x8aa) (52 + nn)
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
              (mword_of_int (s0 + Z.of_nat len)) (42 + nn)
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
    iApply (wp_uk_ld γt γd γs γfd h22 m20 (mword_of_int 0x8aa)
              (mword_of_int 4040 : mword 12) s0_idx a2_idx (DfracOwn 1)
              (uint sp0 - 56) (mword_of_int (s0 + Z.of_nat len)) (52 + nn)
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
    iApply (wp_uk_btype γt γd γs γfd h23 m21 (mword_of_int 0x8ae)
              (mword_of_int 26 : mword 13) s1_idx a2_idx BNE false
              (mword_of_int 0x8c8) (52 + nn)
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
    iApply (wp_uk_cmv γt γd γs γfd h24 m21 (mword_of_int 0x8b2) a0_idx
              s3_idx (mword_of_int p) (52 + nn)
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
    iApply (wp_uk_jal γt γd γs γfd h25 m22 (mword_of_int 0x8b4)
              (mword_of_int 2096954 : mword 21) ra_idx
              (mword_of_int 0x7ee) (mword_of_int 0x8b8) (52 + nn)
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
    iApply (wp_kshp_nulterminate h26 m23 s0 p len (ushp_ext len f) toks
              (48 + nn) Ha0_23 ltac:(lia) ltac:(lia) Hp0 Hp8
              Hpsz Htlen
              ltac:(intros i t Hi;
                    destruct (ushp_tokens_in len f 0%nat toks Htoks
                                ltac:(lia) i t Hi) as [ Hlo0 Hhi0 ];
                    split; lia)
              with "Hcode Hro Hnode Hline Hrun").
    iIntros "Hnode Hline" (h27 m24) "%Hcs2324 %Ha0_24 Hrun".
    rewrite Eret23.
    (* ---- 0x8b8  c.mv a0,s3 ---- *)
    assert (Hs3_24 : m24 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs2324 s3_idx ltac:(vm_compute; reflexivity))
              (Hm23 s3_idx ltac:(vm_compute; discriminate))
              (Hm22 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_21. }
    iApply (wp_uk_cmv γt γd γs γfd h27 m24 (mword_of_int 0x8b8) a0_idx
              s3_idx (mword_of_int p) (52 + nn)
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
              (mword_of_int 4 : mword 6) sp0 spl vals (52 + nn) h28 me
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
    iApply ("Hcont" $! p with "Hnode Hline Hws Hsy [] [] HM' Hrun").
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


  (* ===================================================================== *)
  (* §15 THE PARSER THEOREM.                                                *)
  (*                                                                       *)
  (* Everything above is a walk of one function; this is the statement the  *)
  (* lane owed, and it is a two-line corollary of [wp_kshp_parsecmd]        *)
  (* because the walks were stated in the vocabulary stages 5-6 read:       *)
  (*                                                                       *)
  (*   GIVEN a NUL-terminated command line at [s0] with no symbol byte in   *)
  (*   it, whose tokens (in the ported [ushp_tokens] sense) are [toks] and  *)
  (*   number fewer than MAXARGS, and sh's two static tables,               *)
  (*                                                                       *)
  (*   sh's [parsecmd] RETURNS a node [p] with [ushp_tree s0 p              *)
  (*   (UshpExec toks)] -- the deliverable interface of §5 -- with the line *)
  (*   NUL-CUT at every token's end index, with the callee-saved file       *)
  (*   intact, and at the return address.                                   *)
  (*                                                                       *)
  (* WHAT IT IS NOT.  It is not parametric in the SHAPE of the command: a   *)
  (* line with a symbol byte in it reaches parseblock, redircmd, pipecmd,   *)
  (* listcmd or backcmd, none of which is catalogued, and the [panic] arms  *)
  (* are refuted only under [ushp_no_symbols].  That premise is the scope   *)
  (* stage 4 was given and it is the scope this theorem keeps.              *)
  (*                                                                       *)
  (* AUDIT.  Two Hypotheses reach it and no others: [ushp_malloc_ok]        *)
  (* (stage 3's allocator, through execcmd) and [ushp_clw_text_ok]          *)
  (* (the four-byte TEXT-half load, through nulterminate's jump table --    *)
  (* which is [UkShRun.wp_uk_clw_text] and needs only to be un-Local'd).    *)
  (* Everything else is the standing three.                                 *)
  (* ===================================================================== *)

  (* the NUL-cut, as a fact about the bytes: every write the loop makes is a
     zero, so a byte it has zeroed stays zero *)
  Lemma ushp_nulfold_keep (toks : list (nat * nat)) (g : nat -> bv 8)
      (j : nat) :
    g j = ubyte0 -> ushp_nulfold toks g j = ubyte0.
  Proof.
    revert g. induction toks as [| tk r IH ]; intros g Hg;
      cbn [ushp_nulfold]; [ exact Hg | ].
    apply IH. rewrite /ushp_setb.
    destruct (Nat.eqb j (snd tk)); [ reflexivity | exact Hg ].
  Qed.

  Lemma ushp_nulfold_hit (toks : list (nat * nat)) (g : nat -> bv 8)
      (i : nat) (tk : nat * nat) :
    toks !! i = Some tk -> ushp_nulfold toks g (snd tk) = ubyte0.
  Proof.
    revert g i. induction toks as [| t r IH ]; intros g i Hi;
      [ rewrite lookup_nil in Hi; discriminate | ].
    destruct i as [| i ]; cbn in Hi.
    - injection Hi as <-. cbn [ushp_nulfold]. apply ushp_nulfold_keep.
      rewrite /ushp_setb Nat.eqb_refl. reflexivity.
    - cbn [ushp_nulfold]. exact (IH _ i Hi).
  Qed.

  Theorem wp_kshp_parser (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0%nat toks ->
    (length toks < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UMalloc -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parsecmd) (60 + nn) -∗
    (∀ p : Z,
       ⌜ ushp_parses s0 len f p (UshpExec toks) ⌝ -∗
       ushp_tree s0 p (UshpExec toks) -∗
       ubytes γd s0 (S len) (ushp_nulfold toks (ushp_ext len f)) -∗
       ⌜ forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
           ushp_nulfold toks (ushp_ext len f) (snd tk) = ubyte0 ⌝ -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UMalloc' -∗
           urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
             (60 + nn) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hnosym Htoks Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM Hrun Hcont".
    iApply (wp_kshp_parsecmd h m dw dv s0 len f toks nn
              Ha0 Hnosym Htoks Htlen Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy HM Hrun").
    iIntros (p) "Hnode Hline Hws Hsy".
    iApply ("Hcont" $! p with "[] Hnode Hline [] Hws Hsy").
    - iPureIntro. exists toks. split; [ exact Htoks | ].
      split; [ exact Htlen | reflexivity ].
    - iPureIntro. intros i tk Hi.
      exact (ushp_nulfold_hit toks (ushp_ext len f) i tk Hi).
  Qed.

End UkShParseCmd.
