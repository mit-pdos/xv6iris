(* ===================================================================== *)
(* UkShParseExec.v -- SH LANE STAGE 4, part 5: parseexec, THE ARGUMENT     *)
(* LOOP.                                                                   *)
(*                                                                        *)
(*   parseexec @0x590 -- the loop that calls [gettoken] once per token and *)
(*   records the token's two boundaries in the execcmd node.               *)
(*                                                                        *)
(* THE INDUCTION IS [ushp_tokens], and it was defined in the base file in  *)
(* exactly the shape this loop runs: one constructor per turn, so the loop *)
(* invariant is one constructor and not a re-derivation.  This is the      *)
(* file's whole content and it is the most expensive of the six to         *)
(* compile -- the frame is eight words with a spill list, so every step    *)
(* moves a [big_sepL] over the slots.                                      *)
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
Require Import UkShParseRedir.

Section UkShParseExec.
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
  Local Notation ushp_exec_pre := (UkShParse.ushp_exec_pre γd).
  Local Notation ushp_exec_pre_at := (UkShParse.ushp_exec_pre_at γd).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join γd).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split γd).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str γt γd).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty γt γd γs γfd).
  Local Notation ushp_slots_cap := (UkShParse.ushp_slots_cap γd).
  Local Notation ushp_slots_upd := (UkShParse.ushp_slots_upd γd).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at γd).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi γt γd γs γfd).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro γt γd γs γfd).
  Local Notation wp_kshp_gettoken := (UkShParseTok.wp_kshp_gettoken γt γd γs γfd).
  Local Notation wp_kshp_parseredirs := (UkShParseRedir.wp_kshp_parseredirs γt γd γs γfd).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek γt γd γs γfd).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore γt γd γs γfd).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill γt γd γs γfd).

  (* stage 4's one Hypothesis, at the type the base file names *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  Local Notation wp_kshp_execcmd := (UkShParseLex.wp_kshp_execcmd γt γd γs γfd UMalloc UMalloc' ushp_malloc_ok).
(*ALIASES-END*)
  (* ===================================================================== *)
  (* §11 parseexec @0x590 -- the ARGUMENT LOOP.                             *)
  (*                                                                       *)
  (*   struct cmd *parseexec(char **ps, char *es) {                         *)
  (*     if(peek(ps, es, "(")) return parseblock(ps, es);                   *)
  (*     ret = execcmd();  cmd = (struct execcmd * )ret;  argc = 0;         *)
  (*     ret = parseredirs(ret, ps, es);                                    *)
  (*     while(!peek(ps, es, "|)&;")) {                                     *)
  (*       if((tok = gettoken(ps, es, &q, &eq)) == 0) break;                *)
  (*       if(tok != 'a') panic("syntax");                                  *)
  (*       cmd->argv[argc] = q;  cmd->eargv[argc] = eq;  argc++;            *)
  (*       if(argc >= MAXARGS) panic("too many args");                      *)
  (*       ret = parseredirs(ret, ps, es);  }                               *)
  (*     cmd->argv[argc] = 0;  cmd->eargv[argc] = 0;  return ret;  }        *)
  (*                                                                       *)
  (* THE INVARIANT IS ONE PREDICATE AND ONE EQUATION: the node holds the    *)
  (* tokens consumed so far ([ushp_exec_pre s0 p done]) and the cursor is   *)
  (* where the tokens still to come start ([ushp_tokens len f cur rest]).   *)
  (* [s2] is [argc] and [s3] is [&argv[argc]], and both are DERIVED from    *)
  (* [length done] rather than tracked, which is why the step does no index *)
  (* arithmetic beyond one [c.addiw] and one [c.addi].                      *)
  (*                                                                       *)
  (* THREE ARMS ARE REFUTED, NOT WEAKENED.  [peek(ps,es,"|)&;")] is 0 by    *)
  (* [ushp_peek_res_sym]; [tok != 'a'] cannot happen because gettoken's     *)
  (* answer on a symbol-free line is 'a' or 0 and the 0 arm is the loop's   *)
  (* exit; and [argc >= MAXARGS] cannot happen because the caller's         *)
  (* [length toks < 10] bounds it.  So neither [panic] is fetched and       *)
  (* [parseblock] is not either.                                            *)
  (* ===================================================================== *)

  Lemma wp_kshp_pex_loop (dq dw dv : dfrac) (s0 ps p fp : Z)
      (len : nat) (f : nat -> bv 8) (nn : nat) :
    forall (rest done : list (nat * nat)) (cur : nat) (h : CpuId)
           (mc : regfile) (wq weq : mword 64),
    ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    0 < fp - 128 -> (fp - 128) mod 8 = 0 -> 0 <= fp -> fp < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (cur <= len)%nat ->
    (length done + length rest < 10)%nat ->
    ushp_tokens len f cur rest ->
    mc !!! Regidx s0_idx = mword_of_int fp ->
    mc !!! Regidx s1_idx = mword_of_int p ->
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
    ushp_exec_pre s0 p done -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    uword γd (fp - 120) wq -∗
    uword γd (fp - 128) weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x622) (24 + nn) -∗
    (ushp_exec_pre s0 p (done ++ rest) -∗
     uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
     (∃ w : mword 64, uword γd (fp - 120) w) -∗
     (∃ w : mword 64, uword γd (fp - 128) w) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
             Regidx r <> Regidx s3_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         ⌜ mc' !!! Regidx s2_idx
             = mword_of_int (Z.of_nat (length done + length rest)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int p ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x662) (24 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro rest.
    induction rest as [| tk rest IH ];
      intros done cur h mc wq weq Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz
        Hfp0 Hfp8 Hfpl Hfph Hp0 Hp8 Hpsz Hcur Hcnt Htoks
        Hs0v Hs1v Hs2v Hs3v Hs4v Hs5v Hs6v Hs7v Hs8v Hs9v Hs10v Hs11v;
      iIntros "#Hcode #Hro Hnode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    (* ---- the frame's two out-cells are hygienic wherever the frame is -- *)
    all: assert (Hq0 : 0 < fp - 120) by lia.
    all: assert (Hq8 : (fp - 120) mod 8 = 0);
      [ replace (fp - 120) with (fp - 128 + 8) by lia;
        rewrite Zplus_mod Hfp8; reflexivity | ].
    all: assert (Hqz : fp - 120 + 8 < Z64) by lia.
    all: assert (Hez : fp - 128 + 8 < Z64) by lia.
    all: assert (Hfp64 : 0 <= fp < Z64) by lia.
    all: assert (Hnodelen : (length done < 10)%nat)
      by (cbn [length] in Hcnt; lia).
    (* ---- and the position peek is about to leave the cursor at -------- *)
    all: pose (cur' := (cur + ushp_skipws (len - cur) cur f)%nat).
    all: assert (Hcure : cur' = (cur + ushp_skipws (len - cur) cur f)%nat)
      by reflexivity.
    all: assert (Hcur' : (cur' <= len)%nat);
      [ rewrite Hcure; pose proof (ushp_skipws_le (len - cur) cur f); lia | ].
    all: assert (Hz' : ushp_skipws (len - cur') cur' f = 0%nat)
      by exact (ushp_skipws_idem len cur f Hcur).
    all: assert (Ekk : (cur' + ushp_skipws (len - cur') cur' f)%nat = cur')
      by (rewrite Hz'; lia).
    (* ---- 0x622  c.mv a2,s6 ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h mc (mword_of_int 0x622) a2_idx
                   s6_idx (mword_of_int ushp_T_arg) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite Hs6v; symmetry;
                         exact (ushp_mv_val ushp_T_arg))
                   with "[] Hrun");
      [ iApply (uis_shp_622 with "Hcode") | ].
    all: iIntros (h1) "Hrun".
    all: set (n1 := <[Regidx a2_idx
                      := regval_into_reg
                           (mword_of_int ushp_T_arg : mword 64)]> mc).
    all: assert (Hk1 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n1 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          exact (upd_ne mc (Regidx a2_idx) (Regidx r) _
                   (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))).
    (* ---- 0x624  c.mv a1,s5 ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h1 n1 (mword_of_int 0x624) a1_idx
                   s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk1 s5_idx ltac:(vm_compute; reflexivity))
                           Hs5v; symmetry;
                         exact (ushp_mv_val (s0 + Z.of_nat len)))
                   with "[] Hrun");
      [ iApply (uis_shp_624 with "Hcode") | ].
    all: iIntros (h2) "Hrun".
    all: set (n2 := <[Regidx a1_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat len)
                            : mword 64)]> n1).
    all: assert (Hk2 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n2 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n1 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk1 r Hr)).
    (* ---- 0x626  c.mv a0,s4 ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h2 n2 (mword_of_int 0x626) a0_idx
                   s4_idx (mword_of_int ps) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk2 s4_idx ltac:(vm_compute; reflexivity))
                           Hs4v; symmetry; exact (ushp_mv_val ps))
                   with "[] Hrun");
      [ iApply (uis_shp_626 with "Hcode") | ].
    all: iIntros (h3) "Hrun".
    all: set (n3 := <[Regidx a0_idx
                      := regval_into_reg (mword_of_int ps : mword 64)]> n2).
    all: assert (Hk3 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n3 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n2 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk2 r Hr)).
    (* ---- 0x628  jal 448 <peek> ---- *)
    all: iApply (wp_uk_jal γt γd γs γfd h3 n3 (mword_of_int 0x628)
                   (mword_of_int 2096672 : mword 21) ra_idx
                   (mword_of_int 0x448) (mword_of_int 0x62c) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   with "[] Hrun");
      [ iApply (uis_shp_628 with "Hcode") | ].
    all: iIntros (h4) "Hrun".
    all: set (n4 := <[Regidx ra_idx
                      := regval_into_reg
                           (mword_of_int 0x62c : mword 64)]> n3).
    all: assert (Hk4 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n4 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n3 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk3 r Hr)).
    all: assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x62c);
      [ rewrite (upd_eq n3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x62c : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    all: assert (Ha0_4 : n4 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    all: assert (Ha1_4 : n4 !!! Regidx a1_idx
                         = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n1 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    all: assert (Ha2_4 : n4 !!! Regidx a2_idx = mword_of_int ushp_T_arg);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n1 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq mc (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int ushp_T_arg : mword 64))) | ].
    all: rewrite <- shpp_peek.
    all: iApply (wp_kshp_peek h4 n4 dq dw true DfracDiscarded ps s0
                   ushp_T_arg len cur 4 f (ushp_lit ushp_T_arg)
                   (mword_of_int (s0 + Z.of_nat cur)) (14 + nn)
                   Ha0_4 Ha1_4 Ha2_4 Hcur eq_refl Hs0 Hs64
                   ltac:(unfold ushp_T_arg; lia)
                   ltac:(unfold ushp_T_arg, Z64; lia) Hps0 Hps8 Hpssz
                   with "Hcode Hcur Hstr Hws [] Hrun");
      [ iApply (ushp_lit_str ushp_T_arg 4 DfracDiscarded
                  ushp_T_arg_ok ltac:(cbn; lia) with "Hro") | ].
    all: iIntros "Hcur Hstr Hws _" (h5 n5) "%Hcs45 %Ha0_5 Hrun".
    all: rewrite Eret4.
    all: rewrite (ushp_peek_res_sym len f
                    (cur + ushp_skipws (len - cur) cur f)%nat 4 ushp_T_arg
                    Hnosym ushp_T_arg_sym) in Ha0_5.
    all: assert (Hk5 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n5 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs45 r Hr); exact (Hk4 r Hr)).
    (* ---- 0x62c  c.bnez a0 -- NOT taken: the guard is refuted ---- *)
    all: iApply (wp_uk_cbnez γt γd γs γfd h5 n5 (mword_of_int 0x62c)
                   (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3)
                   a0_idx false (mword_of_int 0x662) (24 + nn)
                   ltac:(vm_compute; reflexivity)
                   ltac:(rewrite Ha0_5; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(discriminate)
                   with "[] Hrun");
      [ iApply (uis_shp_62c with "Hcode") | ].
    all: iIntros (h6) "Hrun".
    (* ---- 0x62e..0x634  the four argument moves ---- *)
    all: iApply (wp_uk_cmv γt γd γs γfd h6 n5 (mword_of_int 0x62e) a3_idx
                   s8_idx (mword_of_int (fp - 128)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk5 s8_idx ltac:(vm_compute; reflexivity))
                           Hs8v; symmetry; exact (ushp_mv_val (fp - 128)))
                   with "[] Hrun");
      [ iApply (uis_shp_62e with "Hcode") | ].
    all: iIntros (h7) "Hrun".
    all: set (n6 := <[Regidx a3_idx
                      := regval_into_reg
                           (mword_of_int (fp - 128) : mword 64)]> n5).
    all: assert (Hk6 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n6 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n5 (Regidx a3_idx) (Regidx r) _
                     (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk5 r Hr)).
    all: iApply (wp_uk_cmv γt γd γs γfd h7 n6 (mword_of_int 0x630) a2_idx
                   s7_idx (mword_of_int (fp - 120)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk6 s7_idx ltac:(vm_compute; reflexivity))
                           Hs7v; symmetry; exact (ushp_mv_val (fp - 120)))
                   with "[] Hrun");
      [ iApply (uis_shp_630 with "Hcode") | ].
    all: iIntros (h8) "Hrun".
    all: set (n7 := <[Regidx a2_idx
                      := regval_into_reg
                           (mword_of_int (fp - 120) : mword 64)]> n6).
    all: assert (Hk7 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n7 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n6 (Regidx a2_idx) (Regidx r) _
                     (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk6 r Hr)).
    all: iApply (wp_uk_cmv γt γd γs γfd h8 n7 (mword_of_int 0x632) a1_idx
                   s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk7 s5_idx ltac:(vm_compute; reflexivity))
                           Hs5v; symmetry;
                         exact (ushp_mv_val (s0 + Z.of_nat len)))
                   with "[] Hrun");
      [ iApply (uis_shp_632 with "Hcode") | ].
    all: iIntros (h9) "Hrun".
    all: set (n8 := <[Regidx a1_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat len)
                            : mword 64)]> n7).
    all: assert (Hk8 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n8 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n7 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk7 r Hr)).
    all: iApply (wp_uk_cmv γt γd γs γfd h9 n8 (mword_of_int 0x634) a0_idx
                   s4_idx (mword_of_int ps) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk8 s4_idx ltac:(vm_compute; reflexivity))
                           Hs4v; symmetry; exact (ushp_mv_val ps))
                   with "[] Hrun");
      [ iApply (uis_shp_634 with "Hcode") | ].
    all: iIntros (h10) "Hrun".
    all: set (n9 := <[Regidx a0_idx
                      := regval_into_reg (mword_of_int ps : mword 64)]> n8).
    all: assert (Hk9 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n9 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk8 r Hr)).
    (* ---- 0x636  jal 310 <gettoken> ---- *)
    all: iApply (wp_uk_jal γt γd γs γfd h10 n9 (mword_of_int 0x636)
                   (mword_of_int 2096346 : mword 21) ra_idx
                   (mword_of_int 0x310) (mword_of_int 0x63a) (24 + nn)
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   with "[] Hrun");
      [ iApply (uis_shp_636 with "Hcode") | ].
    all: iIntros (h11) "Hrun".
    all: set (n10 := <[Regidx ra_idx
                       := regval_into_reg
                            (mword_of_int 0x63a : mword 64)]> n9).
    all: assert (Hk10 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n10 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n9 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk9 r Hr)).
    all: assert (Eret10 : ret_pc (n10 !!! Regidx ra_idx)
                          = mword_of_int 0x63a);
      [ rewrite (upd_eq n9 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x63a : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    all: assert (Ha0_10 : n10 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n8 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    all: assert (Ha1_10 : n10 !!! Regidx a1_idx
                          = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n7 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    all: assert (Ha2_10 : n10 !!! Regidx a2_idx = mword_of_int (fp - 120));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n6 (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int (fp - 120) : mword 64))) | ].
    all: assert (Ha3_10 : n10 !!! Regidx a3_idx = mword_of_int (fp - 128));
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
    all: rewrite <- shpp_gettoken.
    all: iApply (wp_kshp_gettoken h11 n10 dq dw dv ps (fp - 120) (fp - 128)
                   s0 len cur' f (mword_of_int (s0 + Z.of_nat cur'))
                   wq weq (14 + nn)
                   Ha0_10 Ha1_10 Ha2_10 Ha3_10 Hcur' eq_refl Hnosym Hs0 Hs64
                   Hps0 Hps8 Hpssz
                   with "Hcode Hcur [Hq] [Heq] Hstr Hws Hsy Hrun");
      [ iRight; iSplitR;
        [ iPureIntro; exact (conj Hq0 (conj Hq8 Hqz)) | iExact "Hq" ]
      | iRight; iSplitR;
        [ iPureIntro; exact (conj Hfp0 (conj Hfp8 Hez)) | iExact "Heq" ]
      | ].
    all: iIntros "Hcur Hq Heq Hstr Hws Hsy" (h12 n11) "%Hcs1011 %Ha0_11 Hrun".
    all: rewrite Eret10.
    all: rewrite Ekk.
    all: rewrite Ekk in Ha0_11.
    all: iDestruct "Hq" as "[%Hbadq | [_ Hq]]"; [ exfalso; lia | ].
    all: iDestruct "Heq" as "[%Hbade | [_ Heq]]"; [ exfalso; lia | ].
    all: assert (Hk11 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n11 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs1011 r Hr); exact (Hk10 r Hr)).
    - (* =========== THE LOOP EXITS: no token is left =================== *)
      assert (Hend : cur' = len)
        by exact (ushp_tokens_nil_inv len cur f Htoks).
      assert (Hres0 : ushp_gettok_res len f cur' = 0);
        [ rewrite /ushp_gettok_res
            (bool_decide_eq_false_2 (cur' < len)%nat ltac:(lia));
          reflexivity | ].
      rewrite Hres0 in Ha0_11.
      assert (Heend : ushp_gettok_end len f cur' = len);
        [ rewrite /ushp_gettok_end Hend Nat.sub_diag;
          cbn [ushp_toklen]; lia | ].
      assert (Hfin : ushp_gettok_fin len f cur' = len);
        [ rewrite /ushp_gettok_fin; cbv zeta;
          rewrite Heend Nat.sub_diag; cbn [ushp_skipws]; lia | ].
      rewrite Hfin.
      (* ---- 0x63a  c.beqz a0 -- TAKEN: the line is exhausted ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h12 n11 (mword_of_int 0x63a)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x662) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_11; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_63a with "Hcode"). }
      iIntros (h13) "Hrun".
      cbn [length]. rewrite app_nil_r Nat.add_0_r.
      iApply ("Hcont" with "Hnode Hcur [Hq] [Heq] Hstr Hws Hsy [] [] [] Hrun").
      + iExists (mword_of_int (s0 + Z.of_nat cur')). iExact "Hq".
      + iExists (mword_of_int (s0 + Z.of_nat len)). rewrite Heend. iExact "Heq".
      + iPureIntro. intros r Hr _ _ _. exact (Hk11 r Hr).
      + iPureIntro.
        rewrite (Hk11 s2_idx ltac:(vm_compute; reflexivity)). exact Hs2v.
      + iPureIntro.
        rewrite (Hk11 s1_idx ltac:(vm_compute; reflexivity)). exact Hs1v.
    - (* =========== A TOKEN: store it and go round ===================== *)
      pose (q := ushp_toklen (len - cur') cur' f).
      assert (Hqe : q = ushp_toklen (len - cur') cur' f) by reflexivity.
      destruct (ushp_tokens_cons_inv' len cur cur' q f tk rest
                  Hcure Hqe Htoks) as (Hn & Htkeq & Hrest).
      pose (e := (cur' + q)%nat).
      assert (Hee : e = (cur' + q)%nat) by reflexivity.
      assert (Hele : (e <= len)%nat);
        [ rewrite Hee Hqe;
          pose proof (ushp_toklen_le (len - cur') cur' f); lia | ].
      pose (nxt := (e + ushp_skipws (len - e) e f)%nat).
      assert (Hnxte : nxt = (e + ushp_skipws (len - e) e f)%nat)
        by reflexivity.
      assert (Hnxt : (nxt <= len)%nat);
        [ rewrite Hnxte; pose proof (ushp_skipws_le (len - e) e f); lia | ].
      assert (Hres97 : ushp_gettok_res len f cur' = 97);
        [ rewrite /ushp_gettok_res
            (bool_decide_eq_true_2 (cur' < len)%nat
               ltac:(rewrite Hqe in Hn; lia));
          reflexivity | ].
      rewrite Hres97 in Ha0_11.
      assert (Hendv : ushp_gettok_end len f cur' = e) by reflexivity.
      assert (Hfin : ushp_gettok_fin len f cur' = nxt) by reflexivity.
      rewrite Hendv Hfin.
      (* ---- 0x63a  c.beqz a0 -- NOT taken ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h12 n11 (mword_of_int 0x63a)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx false (mword_of_int 0x662) (24 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_11; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_63a with "Hcode"). }
      iIntros (h13) "Hrun".
      (* ---- 0x63c  bne a0,s10 -- NOT taken: the token IS a word ---- *)
      iApply (wp_uk_btype γt γd γs γfd h13 n11 (mword_of_int 0x63c)
                (mword_of_int 8140 : mword 13) s10_idx a0_idx BNE false
                (mword_of_int 0x608) (24 + nn)
                ltac:(cbn [uv_btaken]; rewrite Ha0_11
                        (Hk11 s10_idx ltac:(vm_compute; reflexivity)) Hs10v;
                      vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_63c with "Hcode"). }
      iIntros (h14) "Hrun".
      (* ---- 0x640  ld a5,-120(s0) -- q ---- *)
      assert (Hs0_11 : n11 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk11 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld γt γd γs γfd h14 n11 (mword_of_int 0x640)
                (mword_of_int 3976 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 120) (mword_of_int (s0 + Z.of_nat cur')) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_11 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hq8
                ltac:(vm_compute; discriminate)
                with "[] Hq Hrun").
      { iApply (uis_shp_640 with "Hcode"). }
      iIntros "Hq" (h15) "Hrun".
      set (n12 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat cur')
                          : mword 64)]> n11).
      assert (Hk12 : forall r : mword 5, ucallee_saved_idx r = true ->
                 n12 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n11 (Regidx a5_idx) (Regidx r) _
                       (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk11 r Hr)).
      assert (Ha5_12 : n12 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat cur'))
        by exact (upd_eq n11 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat cur') : mword 64))).
      assert (Hs3_12 : n12 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk12 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3v).
      (* ---- 0x644  sd a5,0(s3) -- argv[argc] = q ---- *)
      iDestruct "Hnode" as "(%Hdl & _ & _ & Hty & Hav & Hev)".
      iDestruct (ushp_slots_upd s0 (p + 8) done tk fst Hnodelen with "Hav")
        as "[Hav0 Havc]".
      iApply (wp_uk_sd γt γd γs γfd h15 n12 (mword_of_int 0x644)
                (mword_of_int 0 : mword 12) s3_idx a5_idx
                (p + 8 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + nn)
                ltac:(rewrite Hs3_12
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (length done) Hp8))
                with "[] [Hav0] Hrun").
      { iApply (uis_shp_644 with "Hcode"). }
      { iExact "Hav0". }
      iIntros "Hav0" (h16) "Hrun".
      rewrite Ha5_12.
      iDestruct ("Havc" with "[Hav0]") as "Hav";
        [ rewrite Htkeq; iExact "Hav0" | ].
      (* ---- 0x648  ld a5,-128(s0) -- eq ---- *)
      assert (Hs0_12 : n12 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk12 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld γt γd γs γfd h16 n12 (mword_of_int 0x648)
                (mword_of_int 3968 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 128) (mword_of_int (s0 + Z.of_nat e)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_12 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hfp8
                ltac:(vm_compute; discriminate)
                with "[] Heq Hrun").
      { iApply (uis_shp_648 with "Hcode"). }
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
      (* ---- 0x64c  sd a5,80(s3) -- eargv[argc] = eq ---- *)
      iDestruct (ushp_slots_upd s0 (p + 88) done tk snd Hnodelen with "Hev")
        as "[Hev0 Hevc]".
      iApply (wp_uk_sd γt γd γs γfd h17 n13 (mword_of_int 0x64c)
                (mword_of_int 80 : mword 12) s3_idx a5_idx
                (p + 88 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + nn)
                ltac:(rewrite Hs3_13
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 11 (length done) Hp8))
                with "[] [Hev0] Hrun").
      { iApply (uis_shp_64c with "Hcode"). }
      { iExact "Hev0". }
      iIntros "Hev0" (h18) "Hrun".
      rewrite Ha5_13.
      iDestruct ("Hevc" with "[Hev0]") as "Hev";
        [ rewrite Htkeq; iExact "Hev0" | ].
      (* ---- 0x650  c.addiw s2,s2,1 -- argc++ ---- *)
      assert (Hs2_13 : n13 !!! Regidx s2_idx
                       = mword_of_int (Z.of_nat (length done)))
        by (rewrite (Hk13 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2v).
      assert (Esx : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                    = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddiw γt γd γs γfd h18 n13 (mword_of_int 0x650)
                (mword_of_int 1 : mword 6) s2_idx
                (mword_of_int (Z.of_nat (length done) + 1)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_13 Esx; symmetry;
                      exact (moi_addw (Z.of_nat (length done)) 1
                               ltac:(unfold Z31; lia)))
                with "[] Hrun").
      { iApply (uis_shp_650 with "Hcode"). }
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
      (* ---- 0x652  bne s2,s9 -- TAKEN: MAXARGS is not reached ---- *)
      iApply (wp_uk_btype γt γd γs γfd h19 n14 (mword_of_int 0x652)
                (mword_of_int 8130 : mword 13) s9_idx s2_idx BNE true
                (mword_of_int 0x614) (24 + nn)
                ltac:(cbn [uv_btaken]; rewrite Hs2_14
                        (Hk14 s9_idx ltac:(vm_compute; reflexivity)
                           ltac:(vm_compute; discriminate)) Hs9v;
                      rewrite (moi_neq_vec (Z.of_nat (length done) + 1) 10
                                 ltac:(unfold Z64; cbn [length] in Hcnt; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hne : (Z.of_nat (length done) + 1 =? 10)
                                    = false)
                        by (apply Z.eqb_neq; cbn [length] in Hcnt; lia);
                      rewrite Hne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_652 with "Hcode"). }
      iIntros (h20) "Hrun".
      (* ---- 0x614  c.addi s3,s3,8 ---- *)
      assert (Hs3_14 : n14 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk14 s3_idx ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; discriminate)); exact Hs3v).
      assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                     = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi γt γd γs γfd h20 n14 (mword_of_int 0x614)
                (mword_of_int 8 : mword 6) s3_idx
                (mword_of_int (p + 8 + 8 * Z.of_nat (length done) + 8))
                (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_14 Esx8; symmetry; apply moi_add)
                with "[] Hrun").
      { iApply (uis_shp_614 with "Hcode"). }
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
      (* ---- 0x616..0x61a  parseredirs(ret, ps, es) ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h21 n15 (mword_of_int 0x616) a2_idx
                s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk15 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs5v;
                      symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_616 with "Hcode"). }
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
      iApply (wp_uk_cmv γt γd γs γfd h22 n16 (mword_of_int 0x618) a1_idx
                s4_idx (mword_of_int ps) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk16 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs4v;
                      symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_618 with "Hcode"). }
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
      iApply (wp_uk_cmv γt γd γs γfd h23 n17 (mword_of_int 0x61a) a0_idx
                s1_idx (mword_of_int p) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk17 s1_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs1v;
                      symmetry; exact (ushp_mv_val p))
                with "[] Hrun").
      { iApply (uis_shp_61a with "Hcode"). }
      iIntros (h24) "Hrun".
      set (n18 := <[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> n17).
      assert (Hk18 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n18 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n17 (Regidx a0_idx) (Regidx r) _
                       (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk17 r Hr Hr2 Hr3)).
      (* ---- 0x61c  jal 4ac <parseredirs> ---- *)
      iApply (wp_uk_jal γt γd γs γfd h24 n18 (mword_of_int 0x61c)
                (mword_of_int 2096784 : mword 21) ra_idx
                (mword_of_int 0x4ac) (mword_of_int 0x620) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_61c with "Hcode"). }
      iIntros (h25) "Hrun".
      set (n19 := <[Regidx ra_idx
                    := regval_into_reg
                         (mword_of_int 0x620 : mword 64)]> n18).
      assert (Hk19 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n19 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n18 (Regidx ra_idx) (Regidx r) _
                       (ushp_cs_ne r ra_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk18 r Hr Hr2 Hr3)).
      assert (Eret19 : ret_pc (n19 !!! Regidx ra_idx)
                       = mword_of_int 0x620);
        [ rewrite (upd_eq n18 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x620 : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_19 : n19 !!! Regidx a0_idx = mword_of_int p);
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n17 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))) | ].
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
      iApply (wp_kshp_parseredirs h25 n19 dq dw p ps s0 len nxt f
                (mword_of_int (s0 + Z.of_nat nxt)) nn
                Ha0_19 Ha1_19 Ha2_19 Hnxt eq_refl Hnosym Hs0 Hs64
                Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hrun").
      iIntros "Hcur Hstr Hws" (h26 n20) "%Hcs1920 %Ha0_20 Hrun".
      rewrite Eret19.
      assert (Hnz : ushp_skipws (len - nxt) nxt f = 0%nat)
        by exact (ushp_skipws_idem len e f Hele).
      assert (Enx : (nxt + ushp_skipws (len - nxt) nxt f)%nat = nxt)
        by (rewrite Hnz; lia).
      rewrite Enx.
      assert (Hk20 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n20 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3; rewrite (Hcs1920 r Hr);
            exact (Hk19 r Hr Hr2 Hr3)).
      (* ---- 0x620  c.mv s1,a0 ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h26 n20 (mword_of_int 0x620) s1_idx
                a0_idx (mword_of_int p) (24 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_20; symmetry; exact (ushp_mv_val p))
                with "[] Hrun").
      { iApply (uis_shp_620 with "Hcode"). }
      iIntros (h27) "Hrun".
      set (n21 := <[Regidx s1_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> n20).
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
                         (p + 8 + 8 * Z.of_nat (length (done ++ [tk])))).
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
      iApply (IH (done ++ [tk]) nxt h27 n21
                (mword_of_int (s0 + Z.of_nat cur'))
                (mword_of_int (s0 + Z.of_nat e))
                Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz Hfp0 Hfp8 Hfpl Hfph
                Hp0 Hp8 Hpsz Hnxt
                ltac:(rewrite ushp_len_app1; cbn [length] in Hcnt; lia)
                ltac:(exact (ushp_tokens_skip len f e rest Hele Hrest))
                ltac:(rewrite (Hk21 s0_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs0v)
                ltac:(exact (upd_eq n20 (Regidx s1_idx)
                               (regval_into_reg (mword_of_int p : mword 64))))
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
                with "Hcode Hro [Hty Hav Hev] Hcur Hq Heq Hstr Hws Hsy Hrun").
      { rewrite /ushp_exec_pre.
        iSplitR; [ iPureIntro; rewrite ushp_len_app1;
                   cbn [length] in Hcnt; lia | ].
        iSplitR; [ iPureIntro; exact Hp0 | ].
        iSplitR; [ iPureIntro; exact Hp8 | ].
        iFrame "Hav Hev". rewrite /ushp_type_at. iExact "Hty". }
      iIntros "Hnode Hcur Hq Heq Hstr Hws Hsy" (hf mf) "%Hpres %Hs2f %Hs1f Hrun".
      rewrite ushp_app_cons.
      iApply ("Hcont" with "Hnode Hcur Hq Heq Hstr Hws Hsy [] [] [] Hrun").
      + iPureIntro. intros r Hr Hr1 Hr2 Hr3.
        rewrite (Hpres r Hr Hr1 Hr2 Hr3). exact (Hk21 r Hr Hr1 Hr2 Hr3).
      + iPureIntro. rewrite Hs2f ushp_len_app1.
        assert (El : (S (length done) + length rest)%nat
                     = (length done + length (tk :: rest))%nat)
          by (cbn [length]; lia).
        rewrite El. reflexivity.
      + iPureIntro. exact Hs1f.
  Qed.


  (* ---- parseexec, the whole function ---------------------------------- *)
  (* THE FRAME IS SPLIT IN TWO, BOTH WAYS.  gcc spills ra/s0/s1/s4/s5 before
     the [peek(ps,es,"(")] that decides whether this is a block, and the
     other eight only on the fall-through -- so the [parseblock] arm pays
     for five saves instead of thirteen.  The restores mirror it: the eight
     come back at 0x670 and the five at 0x5fa, and the [c.j 0x5f8] between
     them is the join.  Neither §4c lemma fits that shape, so the frame is
     four separate runs over §4b's two, at the SLOT ADDRESSES rather than at
     consecutive indexes.
     TAINT: [ushp_malloc_ok], through [execcmd]. *)
  Lemma wp_kshp_parseexec (h : CpuId) (m : regfile) (dq dw dv : dfrac)
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
    urun γt γd γs γfd h m (mword_of_int ShSyms.parseexec) (16 + (24 + nn)) -∗
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
             (16 + (24 + nn)) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Hoffle Hw0 Hnosym Htoks Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM Hrun Hcont".
    rewrite shpp_parseexec.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 128 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    (* ---- 0x590  c.addi16sp sp,sp,-128 ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x590)
              (mword_of_int 56 : mword 6) 16 (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_590 with "Hcode"). }
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
    rewrite !big_sepL_cons big_sepL_nil.
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
    (* ---- 0x592..0x59a  the FIRST five spills ---- *)
    iApply (wp_kshp_spill spn (24 + nn) [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x592 | 1%nat => 0x594
                              | 2%nat => 0x596 | 3%nat => 0x598
                              | 4%nat => 0x59a | _ => 0x59c end)
              adA valsA h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
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
      iSplit; [ iApply (uis_shp_592 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_594 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_596 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_598 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_59a with "Hcode") | done ]. }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplitL "C0"; [ iExact "C0" | ].
      iSplitL "C1"; [ iExact "C1" | ].
      iSplitL "C2"; [ iExact "C2" | ].
      iSplitL "C5"; [ iExact "C5" | ].
      iSplitL "C6"; [ iExact "C6" | done ]. }
    iIntros "HslA" (h2) "Hrun". cbn [length].
    (* ---- 0x59c  c.addi4spn s0,sp,128 ---- *)
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
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 m1 (mword_of_int 0x59c)
              (mword_of_int 0 : mword 3) (mword_of_int 32 : mword 8) s0_idx
              sp0 (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1; symmetry; exact Efp)
              with "[] Hrun").
    { iApply (uis_shp_59c with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hs0_2 : m2 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
      symmetry. exact (moi_of_uint sp0). }
    (* ---- 0x59e  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x59e) s4_idx a0_idx
              (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_59e with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x5a0  c.mv s5,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m3 (mword_of_int 0x5a0) s5_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_5a0 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m4 := <[Regidx s5_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x5a2  auipc a2,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h5 m4 (mword_of_int 0x5a2)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x15a2) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5a2 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0x15a2 : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int 0x15a2)
      by exact (upd_eq m4 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x15a2 : mword 64))).
    (* ---- 0x5a6  addi a2,a2,-682 -- the open-paren table ---- *)
    iApply (wp_uk_addi γt γd γs γfd h6 m5 (mword_of_int 0x5a6)
              (mword_of_int 3414 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_block) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_5; unfold ushp_T_block;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5a6 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m6 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_block : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x5aa  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h7 m6 (mword_of_int 0x5aa)
              (mword_of_int 2096798 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x5ae) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5aa with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x5ae : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret7 : ret_pc (m7 !!! Regidx ra_idx) = mword_of_int 0x5ae).
    { rewrite (upd_eq m6 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5ae : mword 64))).
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
    iApply (wp_kshp_peek h8 m7 dq dw true DfracDiscarded ps s0
              ushp_T_block len off 1 f (ushp_lit ushp_T_block)
              w0 (14 + nn)
              Ha0_7 Ha1_7 Ha2_7 Hoffle Hw0 Hs0 Hs64
              ltac:(unfold ushp_T_block; lia)
              ltac:(unfold ushp_T_block, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_block 1 DfracDiscarded
                ushp_T_block_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h9 m8) "%Hcs78 %Ha0_8 Hrun".
    rewrite Eret7.
    rewrite (ushp_peek_res_sym len f
               (off + ushp_skipws (len - off) off f)%nat 1 ushp_T_block
               Hnosym ushp_T_block_sym) in Ha0_8.
    (* ---- 0x5ae  c.bnez a0 -- NOT taken: this is not a block ---- *)
    iApply (wp_uk_cbnez γt γd γs γfd h9 m8 (mword_of_int 0x5ae)
              (mword_of_int 32 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x5ee) (24 + nn)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_8; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_5ae with "Hcode"). }
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
    (* ---- 0x5b0..0x5be  the OTHER eight spills ---- *)
    iApply (wp_kshp_spill spn (24 + nn) [(s2_idx, mword_of_int 12 : mword 6);
               (s3_idx, mword_of_int 11 : mword 6);
               (s6_idx, mword_of_int 8 : mword 6);
               (s7_idx, mword_of_int 7 : mword 6);
               (s8_idx, mword_of_int 6 : mword 6);
               (s9_idx, mword_of_int 5 : mword 6);
               (s10_idx, mword_of_int 4 : mword 6);
               (s11_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x5b0 | 1%nat => 0x5b2
                              | 2%nat => 0x5b4 | 3%nat => 0x5b6
                              | 4%nat => 0x5b8 | 5%nat => 0x5ba
                              | 6%nat => 0x5bc | 7%nat => 0x5be
                              | _ => 0x5c0 end)
              adB valsB h10 m8 Hsp8
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate;
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
      iSplit; [ iApply (uis_shp_5b0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5be with "Hcode") | done ]. }
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
    (* ---- 0x5c0  c.mv s2,a0 -- argc = 0, and a0 IS 0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h11 m8 (mword_of_int 0x5c0) s2_idx a0_idx
              (mword_of_int 0) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_8; symmetry; exact (ushp_mv_val 0))
              with "[] Hrun").
    { iApply (uis_shp_5c0 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x5c2  jal 1d2 <execcmd> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h12 m9 (mword_of_int 0x5c2)
              (mword_of_int 2096144 : mword 21) ra_idx
              (mword_of_int 0x1d2) (mword_of_int 0x5c6) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5c2 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x5c6 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret10 : ret_pc (m10 !!! Regidx ra_idx) = mword_of_int 0x5c6).
    { rewrite (upd_eq m9 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5c6 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_execcmd.
    iApply (wp_kshp_execcmd h13 m10 s0 (10 + nn) with "Hcode HM Hrun").
    iIntros (h14 m11 p) "%Hcs1011 %Ha0_11 %Hpb Hnode HM' Hrun".
    rewrite Eret10.
    destruct Hpb as [ Hp0 [ Hp16 Hpsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Hp64 : 0 <= p /\ p + 168 < Z64)
      by (rewrite H38 in Hpsz; unfold Z64; lia).
    assert (Hp8 : p mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp16 ]. }
    (* ---- 0x5c6  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h14 m11 (mword_of_int 0x5c6) s3_idx a0_idx
              (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5c6 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x5c8  c.mv s11,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h15 m12 (mword_of_int 0x5c8) s11_idx
              a0_idx (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate))
                      Ha0_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5c8 with "Hcode"). }
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
    (* ---- 0x5ca  c.mv a2,s5 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h16 m13 (mword_of_int 0x5ca) a2_idx
              s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_13; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_5ca with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m14 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len)
                        : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x5cc  c.mv a1,s4 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h17 m14 (mword_of_int 0x5cc) a1_idx
              s4_idx (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm14 s4_idx ltac:(vm_compute; discriminate))
                      Hs4_13; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_5cc with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m15 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x5ce  jal 4ac <parseredirs> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h18 m15 (mword_of_int 0x5ce)
              (mword_of_int 2096862 : mword 21) ra_idx
              (mword_of_int 0x4ac) (mword_of_int 0x5d2) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5ce with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m16 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x5d2 : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret16 : ret_pc (m16 !!! Regidx ra_idx) = mword_of_int 0x5d2).
    { rewrite (upd_eq m15 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x5d2 : mword 64))).
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
    (* the cursor has already been moved once, by the block peek *)
    pose (off1 := (off + ushp_skipws (len - off) off f)%nat).
    assert (Hoff1e : off1 = (off + ushp_skipws (len - off) off f)%nat)
      by reflexivity.
    assert (Hoff1 : (off1 <= len)%nat);
      [ rewrite Hoff1e; pose proof (ushp_skipws_le (len - off) off f); lia | ].
    assert (Hz1 : ushp_skipws (len - off1) off1 f = 0%nat)
      by exact (ushp_skipws_idem len off f Hoffle).
    assert (Ez1 : (off1 + ushp_skipws (len - off1) off1 f)%nat = off1)
      by (rewrite Hz1; lia).
    rewrite <- shpp_parseredirs.
    iApply (wp_kshp_parseredirs h19 m16 dq dw p ps s0 len off1 f
              (mword_of_int (s0 + Z.of_nat off1)) nn
              Ha0_16 Ha1_16 Ha2_16 Hoff1 eq_refl Hnosym Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hrun").
    iIntros "Hcur Hstr Hws" (h20 m17) "%Hcs1617 %Ha0_17 Hrun".
    rewrite Eret16 Ez1.
    (* ---- 0x5d2  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h20 m17 (mword_of_int 0x5d2) s1_idx
              a0_idx (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_17; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5d2 with "Hcode"). }
    iIntros (h21) "Hrun".
    set (m18 := <[Regidx s1_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m17).
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
    (* ---- 0x5d4  c.addi s3,s3,8 -- s3 = &argv[0] ---- *)
    assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                   = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h21 m18 (mword_of_int 0x5d4)
              (mword_of_int 8 : mword 6) s3_idx (mword_of_int (p + 8))
              (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_18 Esx8; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_5d4 with "Hcode"). }
    iIntros (h22) "Hrun".
    set (m19 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int (p + 8) : mword 64)]> m18).
    assert (Hm19 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                     m19 !!! Regidx q = m18 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m18 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x5d6/0x5da  the argument-loop table ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h22 m19 (mword_of_int 0x5d6)
              (mword_of_int 1 : mword 20) s6_idx
              (mword_of_int 0x15d6) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5d6 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (m20 := <[Regidx s6_idx
                  := regval_into_reg (mword_of_int 0x15d6 : mword 64)]> m19).
    assert (Hm20 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                     m20 !!! Regidx q = m19 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m19 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_20 : m20 !!! Regidx s6_idx = mword_of_int 0x15d6)
      by exact (upd_eq m19 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int 0x15d6 : mword 64))).
    iApply (wp_uk_addi γt γd γs γfd h23 m20 (mword_of_int 0x5da)
              (mword_of_int 3394 : mword 12) s6_idx s6_idx
              (mword_of_int ushp_T_arg) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_20; unfold ushp_T_arg;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5da with "Hcode"). }
    iIntros (h24) "Hrun".
    set (m21 := <[Regidx s6_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_arg : mword 64)]> m20).
    assert (Hm21 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                     m21 !!! Regidx q = m20 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m20 (Regidx s6_idx) (Regidx q) _ Hq)).
    (* ---- 0x5de/0x5e2  &eq and &q, the two locals ---- *)
    assert (Hs0_21 : m21 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm21 s0_idx ltac:(vm_compute; discriminate))
              (Hm20 s0_idx ltac:(vm_compute; discriminate))
              (Hm19 s0_idx ltac:(vm_compute; discriminate))
              (Hm18 s0_idx ltac:(vm_compute; discriminate))
              (Hcs1617 s0_idx ltac:(vm_compute; reflexivity))
              (Hm16 s0_idx ltac:(vm_compute; discriminate))
              (Hm15 s0_idx ltac:(vm_compute; discriminate))
              (Hm14 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_13. }
    iApply (wp_uk_addi γt γd γs γfd h24 m21 (mword_of_int 0x5de)
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
    { iApply (uis_shp_5de with "Hcode"). }
    iIntros (h25) "Hrun".
    set (m22 := <[Regidx s8_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 128) : mword 64)]> m21).
    assert (Hm22 : forall q : mword 5, Regidx q <> Regidx s8_idx ->
                     m22 !!! Regidx q = m21 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m21 (Regidx s8_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_addi γt γd γs γfd h25 m22 (mword_of_int 0x5e2)
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
    { iApply (uis_shp_5e2 with "Hcode"). }
    iIntros (h26) "Hrun".
    set (m23 := <[Regidx s7_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 120) : mword 64)]> m22).
    assert (Hm23 : forall q : mword 5, Regidx q <> Regidx s7_idx ->
                     m23 !!! Regidx q = m22 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m22 (Regidx s7_idx) (Regidx q) _ Hq)).
    (* ---- 0x5e6/0x5ea  the two constants ---- *)
    iApply (wp_uk_li γt γd γs γfd h26 m23 (mword_of_int 0x5e6)
              (mword_of_int 97 : mword 12) s10_idx (mword_of_int 97)
              (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 97))
              with "[] Hrun").
    { iApply (uis_shp_5e6 with "Hcode"). }
    iIntros (h27) "Hrun".
    set (m24 := <[Regidx s10_idx
                  := regval_into_reg (mword_of_int 97 : mword 64)]> m23).
    assert (Hm24 : forall q : mword 5, Regidx q <> Regidx s10_idx ->
                     m24 !!! Regidx q = m23 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m23 (Regidx s10_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cli γt γd γs γfd h27 m24 (mword_of_int 0x5ea)
              (mword_of_int 10 : mword 6) s9_idx (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_5ea with "Hcode"). }
    iIntros (h28) "Hrun".
    set (m25 := <[Regidx s9_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 10 : mword 6)
                        : mword 64)]> m24).
    assert (Hm25 : forall q : mword 5, Regidx q <> Regidx s9_idx ->
                     m25 !!! Regidx q = m24 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m24 (Regidx s9_idx) (Regidx q) _ Hq)).
    (* ---- 0x5ec  c.j 0x622 -- into the loop ---- *)
    iApply (wp_uk_cj γt γd γs γfd h28 m25 (mword_of_int 0x5ec)
              (mword_of_int 27 : mword 11) (mword_of_int 0x622) (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_5ec with "Hcode"). }
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
    assert (Hs1_25 : m25 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hm25 s1_idx ltac:(vm_compute; discriminate))
              (Hm24 s1_idx ltac:(vm_compute; discriminate))
              (Hm23 s1_idx ltac:(vm_compute; discriminate))
              (Hm22 s1_idx ltac:(vm_compute; discriminate))
              (Hm21 s1_idx ltac:(vm_compute; discriminate))
              (Hm20 s1_idx ltac:(vm_compute; discriminate))
              (Hm19 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m17 (Regidx s1_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
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
    (* ---- 0x622..0x662  THE ARGUMENT LOOP ---- *)
    iApply (wp_kshp_pex_loop dq dw dv s0 ps p (uint sp0) len f nn
              toks (@nil (nat * nat)) off1 h29 m25 wq weq
              Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz
              ltac:(lia) Hsp8al ltac:(lia) ltac:(lia)
              Hp0 Hp8 ltac:(lia) Hoff1 ltac:(cbn [length]; lia)
              ltac:(exact (ushp_tokens_skip len f off toks Hoffle Htoks))
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
              with "Hcode Hro Hnode Hcur Lq Leq Hstr Hws Hsy Hrun").
    iIntros "Hnode Hcur [%vq Lq] [%veq Leq] Hstr Hws Hsy"
      (h30 mf) "%Hpresf %Hs2f %Hs1f Hrun".
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
    (* ---- 0x662  c.slli s2,s2,0x3 ---- *)
    iApply (wp_uk_cslli γt γd γs γfd h30 mf (mword_of_int 0x662)
              (mword_of_int 3 : mword 6) s2_idx
              (mword_of_int (8 * Z.of_nat (length toks))) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2f'
                      (moi_shl (Z.of_nat (length toks)) 3 ltac:(lia));
                    f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_662 with "Hcode"). }
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
    (* ---- 0x664  add a5,s11,s2 ---- *)
    iApply (wp_uk_add γt γd γs γfd h31 mg (mword_of_int 0x664)
              s11_idx s2_idx a5_idx
              (mword_of_int (p + 8 * Z.of_nat (length toks))) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_g (Hmg s11_idx ltac:(vm_compute; discriminate))
                      Hs11_f; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_664 with "Hcode"). }
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
    (* ---- 0x668  sd zero,8(a5) -- argv[argc] = 0, which it already is ---- *)
    iDestruct (ushp_slots_cap s0 (p + 8) toks fst Htlen with "Hav")
      as "[Hav0 Havc]".
    iApply (wp_uk_sd γt γd γs γfd h32 mh (mword_of_int 0x668)
              (mword_of_int 8 : mword 12) a5_idx x0_idx
              (p + 8 + 8 * Z.of_nat (length toks)) (mword_of_int 0)
              (24 + nn)
              ltac:(rewrite Ha5_h
                      (uint_moi (p + 8 * Z.of_nat (length toks))
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(exact (ushp_slot_al8 p 1 (length toks) Hp8))
              with "[] [Hav0] Hrun").
    { iApply (uis_shp_668 with "Hcode"). }
    { iExact "Hav0". }
    iIntros "Hav0" (h33) "Hrun".
    rewrite Hx0 Ez.
    iDestruct ("Havc" with "Hav0") as "Hav".
    (* ---- 0x66c  sd zero,88(a5) -- eargv[argc] = 0 ---- *)
    iDestruct (ushp_slots_cap s0 (p + 88) toks snd Htlen with "Hev")
      as "[Hev0 Hevc]".
    iApply (wp_uk_sd γt γd γs γfd h33 mh (mword_of_int 0x66c)
              (mword_of_int 88 : mword 12) a5_idx x0_idx
              (p + 88 + 8 * Z.of_nat (length toks)) (mword_of_int 0)
              (24 + nn)
              ltac:(rewrite Ha5_h
                      (uint_moi (p + 8 * Z.of_nat (length toks))
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(exact (ushp_slot_al8 p 11 (length toks) Hp8))
              with "[] [Hev0] Hrun").
    { iApply (uis_shp_66c with "Hcode"). }
    { iExact "Hev0". }
    iIntros "Hev0" (h34) "Hrun".
    rewrite Hx0 Ez.
    iDestruct ("Hevc" with "Hev0") as "Hev".
    (* ---- 0x670..0x67e  the EIGHT restores ---- *)
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
                              | 0%nat => 0x670 | 1%nat => 0x672
                              | 2%nat => 0x674 | 3%nat => 0x676
                              | 4%nat => 0x678 | 5%nat => 0x67a
                              | 6%nat => 0x67c | 7%nat => 0x67e
                              | _ => 0x680 end)
              adB valsB h34 mh Hsp_h
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adB; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adB; apply ushp_slot_al; exact Hal8
                       | split; [ unfold unot_sp; vm_compute; discriminate
                                | vm_compute; discriminate ] ] ]))
              with "[] HslB Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_670 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_672 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_674 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_676 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_678 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_67a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_67c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_67e with "Hcode") | done ]. }
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
    assert (Hs1_i : mi !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hmi s1_idx
                 ltac:(intros i r u Hi;
                       destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                       cbn in Hi; try discriminate;
                       injection Hi as Hr Hu0; subst;
                       vm_compute; discriminate))
              (Hmh s1_idx ltac:(vm_compute; discriminate))
              (Hmg s1_idx ltac:(vm_compute; discriminate)). exact Hs1f. }
    assert (Hsp_i : mi !!! Regidx csp_rs1 = spn).
    { rewrite (Hmi csp_rs1
                 ltac:(intros i r u Hi;
                       destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                       cbn in Hi; try discriminate;
                       injection Hi as Hr Hu0; subst;
                       vm_compute; discriminate)). exact Hsp_h. }
    (* ---- 0x680  c.j 0x5f8 -- into the common tail ---- *)
    iApply (wp_uk_cj γt γd γs γfd h35 mi (mword_of_int 0x680)
              (mword_of_int 1980 : mword 11) (mword_of_int 0x5f8) (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_680 with "Hcode"). }
    iIntros (h36) "Hrun".
    (* ---- 0x5f8  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h36 mi (mword_of_int 0x5f8) a0_idx
              s1_idx (mword_of_int p) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_i; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_5f8 with "Hcode"). }
    iIntros (h37) "Hrun".
    set (mj := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> mi).
    assert (Hmj : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    mj !!! Regidx q = mi !!! Regidx q)
      by (intros q Hq; exact (upd_ne mi (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hsp_j : mj !!! Regidx csp_rs1 = spn).
    { rewrite (Hmj csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_i. }
    (* ---- 0x5fa..0x602  the FIVE restores ---- *)
    iApply (wp_kshp_restore spn (24 + nn) [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x5fa | 1%nat => 0x5fc
                              | 2%nat => 0x5fe | 3%nat => 0x600
                              | 4%nat => 0x602 | _ => 0x604 end)
              adA valsA h37 mj Hsp_j
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ unfold adA; rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ unfold adA; apply ushp_slot_al; exact Hal8
                       | split; [ unfold unot_sp; vm_compute; discriminate
                                | vm_compute; discriminate ] ] ]))
              with "[] HslA Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_5fa with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5fc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_5fe with "Hcode") | ].
      iSplit; [ iApply (uis_shp_600 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_602 with "Hcode") | done ]. }
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
                 ltac:(intros i r u Hi;
                       destruct i as [| [| [| [| [| i ]]]]];
                       cbn in Hi; try discriminate;
                       injection Hi as Hr Hu0; subst;
                       vm_compute; discriminate)). exact Hsp_j. }
    assert (Hrak : mk !!! Regidx ra_idx = valsA 0%nat)
      by exact (ushp_spillback_ra [(ra_idx, mword_of_int 15 : mword 6);
               (s0_idx, mword_of_int 14 : mword 6);
               (s1_idx, mword_of_int 13 : mword 6);
               (s4_idx, mword_of_int 10 : mword 6);
               (s5_idx, mword_of_int 9 : mword 6)] (mword_of_int 15 : mword 6) valsA mj
                  eq_refl
                  ltac:(intros i r u Hi;
                        destruct i as [| [| [| [| i ]]]];
                        cbn in Hi; try discriminate;
                        injection Hi as Hr Hu0; subst;
                        vm_compute; discriminate)).
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
    rewrite !big_sepL_cons big_sepL_nil.
    iDestruct "HslA" as "(A0 & A1 & A2 & A3 & A4 & _)".
    iDestruct "HslB" as "(B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & _)".
    (* ---- 0x604  c.addi16sp sp,sp,128 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h38 mk (mword_of_int 0x604)
              (mword_of_int 8 : mword 6) 16 (24 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 B5 B6 B7 L0 Lq Leq Hbot]
                   Hrun").
    { iApply (uis_shp_604 with "Hcode"). }
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
    (* ---- 0x606  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h39
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mk)
              (mword_of_int 0x606) ra_idx (ret_pc (m !!! Regidx ra_idx))
              (16 + (24 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mk (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrak; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_606 with "Hcode"). }
    iIntros (h40) "Hrun".
    iApply ("Hcont" $! p with "[] [Hty Hav Hev] Hcur Hstr Hws Hsy [] [] HM' Hrun").
    - iPureIntro. lia.
    - iApply ushp_exec_pre_at. rewrite /ushp_exec_pre.
      iSplitR; [ iPureIntro; exact Htlen | ].
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
          cbn in Hi; try discriminate;
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
            cbn in Hi; try discriminate;
            injection Hi as Hr Hu0; subst; unfold valsB;
            rewrite <- He; reflexivity.
    - iPureIntro.
      rewrite (upd_ne mk (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq mi (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

End UkShParseExec.
