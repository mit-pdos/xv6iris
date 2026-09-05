(* ===================================================================== *)
(* UkShParseRedir.v -- SH LANE STAGE 4, part 4: parseredirs.               *)
(*                                                                        *)
(*   parseredirs @0x4ac -- 85 instructions, 40 of them REACHED.            *)
(*                                                                        *)
(* THE OTHER 45 ARE REFUTED, NOT WALKED.  parseredirs loops while the next *)
(* non-blank byte is '<' or '>', and [ushp_no_symbols] says the line has   *)
(* neither -- so the loop runs ZERO times and its body (the redircmd       *)
(* constructor, the second [gettoken], the two panics) is dead for every   *)
(* line this stage is scoped to.  The walk is the entry, the [peek], and   *)
(* the exit.                                                               *)
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

Section UkShParseRedir.
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
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek γt γd γs γfd).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore γt γd γs γfd).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill γt γd γs γfd).

  (* stage 4's one Hypothesis, at the type the base file names *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  Local Notation wp_kshp_execcmd := (UkShParseLex.wp_kshp_execcmd γt γd γs γfd UMalloc UMalloc' ushp_malloc_ok).
(*ALIASES-END*)


  (* ===================================================================== *)
  (* §10 parseredirs @0x4ac -- 85 instructions, 40 of them REACHED.         *)
  (*                                                                       *)
  (*   struct cmd *parseredirs(struct cmd *cmd, char **ps, char *es) {      *)
  (*     while(peek(ps, es, "<>")) { ... }                                  *)
  (*     return cmd;  }                                                     *)
  (*                                                                       *)
  (* THE LOOP NEVER TURNS.  Its guard is a peek for the two redirection     *)
  (* bytes, both of them in sh's symbol table, so [ushp_no_symbols] refutes *)
  (* it at the [c.beqz] -- [ushp_peek_res_sym] is that refutation and it is *)
  (* the same one line at all five sites.  What is left is a fourteen-word  *)
  (* frame, eleven spills, eight register moves, ONE call and the return:   *)
  (* 40 instructions of the 85 catalogued, and the other 45 -- the two      *)
  (* [redircmd] arms, the [panic], the switch on the redirection byte --    *)
  (* are never fetched.                                                     *)
  (*                                                                       *)
  (* IT IS ALSO THE FIRST WALK THAT CONSUMES [wp_kshp_peek], and the        *)
  (* postcondition is exactly what it wanted: the cursor cell has moved to  *)
  (* the first non-blank byte and the answer is a [Z] this lemma computes   *)
  (* rather than a case it has to split on.                                 *)
  (* ===================================================================== *)

  Lemma wp_kshp_parseredirs (h : CpuId) (m : regfile) (dq dw : dfrac)
      (cmd ps s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.parseredirs)
      (14 + (8 + (2 + nn))) -∗
    (uword γd ps
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int cmd ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
           (14 + (8 + (2 + nn))) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hrun Hcont".
    rewrite shpp_parseredirs.
    set (vals := fun i : nat =>
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
                   | _ => m !!! Regidx s9_idx end).
    (* ---- 0x4ac..0x4c4  the prologue: k = 14, eleven spills ---- *)
    iApply (wp_kshp_frame_pro 14 3 [(ra_idx, mword_of_int 13 : mword 6);
               (s0_idx, mword_of_int 12 : mword 6);
               (s1_idx, mword_of_int 11 : mword 6);
               (s2_idx, mword_of_int 10 : mword 6);
               (s3_idx, mword_of_int 9 : mword 6);
               (s4_idx, mword_of_int 8 : mword 6);
               (s5_idx, mword_of_int 7 : mword 6);
               (s6_idx, mword_of_int 6 : mword 6);
               (s7_idx, mword_of_int 5 : mword 6);
               (s8_idx, mword_of_int 4 : mword 6);
               (s9_idx, mword_of_int 3 : mword 6)] 0x4ac
              (fun i : nat => match i with
                              | 0%nat => 0x4ae | 1%nat => 0x4b0
                              | 2%nat => 0x4b2 | 3%nat => 0x4b4
                              | 4%nat => 0x4b6 | 5%nat => 0x4b8
                              | 6%nat => 0x4ba | 7%nat => 0x4bc
                              | 8%nat => 0x4be | 9%nat => 0x4c0
                              | 10%nat => 0x4c2 | 11%nat => 0x4c4
                              | _ => 0x4c6 end)
              (mword_of_int 57 : mword 6) (mword_of_int 28 : mword 8)
              vals (8 + (2 + nn)) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_4ac with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_4ae with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4c2 with "Hcode") | done ]. }
    { iApply (uis_shp_4c4 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 14))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x4c6  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m2 (mword_of_int 0x4c6) s4_idx a0_idx
              (mword_of_int cmd) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val cmd))
              with "[] Hrun").
    { iApply (uis_shp_4c6 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x4c8  c.mv s3,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h2 m3 (mword_of_int 0x4c8) s3_idx a1_idx
              (mword_of_int ps) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_4c8 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m4 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x4ca  c.mv s2,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m4 (mword_of_int 0x4ca) s2_idx a2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_4ca with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m5 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x4cc  auipc s6,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h4 m5 (mword_of_int 0x4cc)
              (mword_of_int 1 : mword 20) s6_idx
              (mword_of_int 0x14cc) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4cc with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 0x14cc : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_6 : m6 !!! Regidx s6_idx = mword_of_int 0x14cc)
      by exact (upd_eq m5 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int 0x14cc : mword 64))).
    (* ---- 0x4d0  addi s6,s6,-476 -- the table base 0x12f0 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h5 m6 (mword_of_int 0x4d0)
              (mword_of_int 3620 : mword 12) s6_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_6; unfold ushp_T_redir;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4d0 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m7 := <[Regidx s6_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_redir : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_7 : m7 !!! Regidx s6_idx = mword_of_int ushp_T_redir)
      by exact (upd_eq m6 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int ushp_T_redir : mword 64))).
    (* ---- 0x4d4  addi s9,s0,-112 -- &q, dead on this path ---- *)
    iApply (wp_uk_addi γt γd γs γfd h6 m7 (mword_of_int 0x4d4)
              (mword_of_int 3984 : mword 12) s0_idx s9_idx
              (add_vec (m7 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 3984 : mword 12)))
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shp_4d4 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m8 := <[Regidx s9_idx
                 := regval_into_reg
                      (add_vec (m7 !!! Regidx s0_idx)
                         (sign_extend' 64
                            (mword_of_int 3984 : mword 12)))]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s9_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s9_idx) (Regidx q) _ Hq)).
    (* ---- 0x4d8  addi s8,s0,-104 -- &eq, dead ---- *)
    iApply (wp_uk_addi γt γd γs γfd h7 m8 (mword_of_int 0x4d8)
              (mword_of_int 3992 : mword 12) s0_idx s8_idx
              (add_vec (m8 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 3992 : mword 12)))
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shp_4d8 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m9 := <[Regidx s8_idx
                 := regval_into_reg
                      (add_vec (m8 !!! Regidx s0_idx)
                         (sign_extend' 64
                            (mword_of_int 3992 : mword 12)))]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s8_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s8_idx) (Regidx q) _ Hq)).
    (* ---- 0x4dc  li s7,97 -- the 'a' the dead arm compares against ---- *)
    iApply (wp_uk_li γt γd γs γfd h8 m9 (mword_of_int 0x4dc)
              (mword_of_int 97 : mword 12) s7_idx (mword_of_int 97)
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 97))
              with "[] Hrun").
    { iApply (uis_shp_4dc with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m10 := <[Regidx s7_idx
                  := regval_into_reg (mword_of_int 97 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx s7_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx s7_idx) (Regidx q) _ Hq)).
    (* ---- 0x4e0  c.j 0x502 -- into the loop's GUARD ---- *)
    iApply (wp_uk_cj γt γd γs γfd h9 m10 (mword_of_int 0x4e0)
              (mword_of_int 17 : mword 11) (mword_of_int 0x502)
              (8 + (2 + nn))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4e0 with "Hcode"). }
    iIntros (h10) "Hrun".
    (* ---- 0x502  li s5,60 -- the '<' the dead switch compares against ---- *)
    iApply (wp_uk_li γt γd γs γfd h10 m10 (mword_of_int 0x502)
              (mword_of_int 60 : mword 12) s5_idx (mword_of_int 60)
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 60))
              with "[] Hrun").
    { iApply (uis_shp_502 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 60 : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x506  c.mv a2,s6 ---- *)
    assert (Hs6_11 : m11 !!! Regidx s6_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm11 s6_idx ltac:(vm_compute; discriminate))
              (Hm10 s6_idx ltac:(vm_compute; discriminate))
              (Hm9 s6_idx ltac:(vm_compute; discriminate))
              (Hm8 s6_idx ltac:(vm_compute; discriminate)). exact Hs6_7. }
    iApply (wp_uk_cmv γt γd γs γfd h11 m11 (mword_of_int 0x506) a2_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_11; symmetry;
                    exact (ushp_mv_val ushp_T_redir))
              with "[] Hrun").
    { iApply (uis_shp_506 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m12 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_redir : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x508  c.mv a1,s2 ---- *)
    assert (Hs2_12 : m12 !!! Regidx s2_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h12 m12 (mword_of_int 0x508) a1_idx s2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_12; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_508 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m13 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m12).
    assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m13 !!! Regidx q = m12 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m12 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x50a  c.mv a0,s3 ---- *)
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int ps).
    { rewrite (Hm13 s3_idx ltac:(vm_compute; discriminate))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hm5 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s3_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h13 m13 (mword_of_int 0x50a) a0_idx s3_idx
              (mword_of_int ps) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_13; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_50a with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m14 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x50c  jal 448 <peek> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h14 m14 (mword_of_int 0x50c)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x510) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_50c with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m15 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x510 : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret : ret_pc (m15 !!! Regidx ra_idx) = mword_of_int 0x510).
    { rewrite (upd_eq m14 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x510 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_15 : m15 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm15 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m13 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_15 : m15 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm15 a1_idx ltac:(vm_compute; discriminate))
              (Hm14 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m12 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_15 : m15 !!! Regidx a2_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm15 a2_idx ltac:(vm_compute; discriminate))
              (Hm14 a2_idx ltac:(vm_compute; discriminate))
              (Hm13 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int ushp_T_redir : mword 64))). }
    rewrite <- shpp_peek.
    (* ---- peek(ps, es, the two redirection bytes) ---- *)
    iApply (wp_kshp_peek h15 m15 dq dw true DfracDiscarded ps s0
              ushp_T_redir len off 2 f (ushp_lit ushp_T_redir)
              (mword_of_int (s0 + Z.of_nat off)) nn
              Ha0_15 Ha1_15 Ha2_15 Hoffle eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_redir; lia)
              ltac:(unfold ushp_T_redir, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode [Hcur] Hstr Hws [] Hrun").
    { rewrite <- Hw0. iExact "Hcur". }
    { iApply (ushp_lit_str ushp_T_redir 2 DfracDiscarded
                ushp_T_redir_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h16 n0) "%Hcs %Ha0n0 Hrun".
    rewrite Eret.
    rewrite (ushp_peek_res_sym len f
               (off + ushp_skipws (len - off) off f) 2 ushp_T_redir
               Hnosym ushp_T_redir_sym) in Ha0n0.
    (* ---- 0x510  c.beqz a0 -- TAKEN: the loop never turns ---- *)
    iApply (wp_uk_cbeqz γt γd γs γfd h16 n0 (mword_of_int 0x510)
              (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x574) (8 + (2 + nn))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0n0; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_510 with "Hcode"). }
    iIntros (h17) "Hrun".
    (* ---- 0x574  c.mv a0,s4 -- the answer is the cmd we were handed ---- *)
    assert (Hs4_n0 : n0 !!! Regidx s4_idx = mword_of_int cmd).
    { rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity))
              (Hm15 s4_idx ltac:(vm_compute; discriminate))
              (Hm14 s4_idx ltac:(vm_compute; discriminate))
              (Hm13 s4_idx ltac:(vm_compute; discriminate))
              (Hm12 s4_idx ltac:(vm_compute; discriminate))
              (Hm11 s4_idx ltac:(vm_compute; discriminate))
              (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hm6 s4_idx ltac:(vm_compute; discriminate))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int cmd : mword 64))). }
    iApply (wp_uk_cmv γt γd γs γfd h17 n0 (mword_of_int 0x574) a0_idx s4_idx
              (mword_of_int cmd) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_n0; symmetry; exact (ushp_mv_val cmd))
              with "[] Hrun").
    { iApply (uis_shp_574 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> n0).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = n0 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n0 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 14))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    (* ---- 0x576..0x58e  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 14 3 [(ra_idx, mword_of_int 13 : mword 6);
               (s0_idx, mword_of_int 12 : mword 6);
               (s1_idx, mword_of_int 11 : mword 6);
               (s2_idx, mword_of_int 10 : mword 6);
               (s3_idx, mword_of_int 9 : mword 6);
               (s4_idx, mword_of_int 8 : mword 6);
               (s5_idx, mword_of_int 7 : mword 6);
               (s6_idx, mword_of_int 6 : mword 6);
               (s7_idx, mword_of_int 5 : mword 6);
               (s8_idx, mword_of_int 4 : mword 6);
               (s9_idx, mword_of_int 3 : mword 6)] (mword_of_int 13 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x576 | 1%nat => 0x578
                              | 2%nat => 0x57a | 3%nat => 0x57c
                              | 4%nat => 0x57e | 5%nat => 0x580
                              | 6%nat => 0x582 | 7%nat => 0x584
                              | 8%nat => 0x586 | 9%nat => 0x588
                              | 10%nat => 0x58a | 11%nat => 0x58c
                              | _ => 0x58e end)
              (mword_of_int 7 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 11)) vals
              (8 + (2 + nn)) h18 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]];
                    cbn in Hi; try discriminate;
                    injection Hi as Hr Hu0; subst;
                    vm_compute; discriminate)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_576 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_578 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_580 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_582 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_584 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_586 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_588 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_58a with "Hcode") | done ]. }
    { iApply (uis_shp_58c with "Hcode"). }
    { iApply (uis_shp_58e with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" with "Hcur Hstr Hws [] [] Hrun").
    - iPureIntro.
      apply (ushp_frame_cs _ vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        rewrite (Hme q (ushp_cs_ne q a0_idx Hq
                          ltac:(vm_compute; reflexivity)))
                (Hcs q Hq)
                (Hm15 q (Hmiss 0%nat ra_idx (mword_of_int 13 : mword 6)
                           eq_refl))
                (Hm14 q (ushp_cs_ne q a0_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm13 q (ushp_cs_ne q a1_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm12 q (ushp_cs_ne q a2_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm11 q (Hmiss 6%nat s5_idx (mword_of_int 7 : mword 6)
                           eq_refl))
                (Hm10 q (Hmiss 8%nat s7_idx (mword_of_int 5 : mword 6)
                           eq_refl))
                (Hm9 q (Hmiss 9%nat s8_idx (mword_of_int 4 : mword 6)
                          eq_refl))
                (Hm8 q (Hmiss 10%nat s9_idx (mword_of_int 3 : mword 6)
                          eq_refl))
                (Hm7 q (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm6 q (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm5 q (Hmiss 3%nat s2_idx (mword_of_int 10 : mword 6)
                          eq_refl))
                (Hm4 q (Hmiss 4%nat s3_idx (mword_of_int 9 : mword 6)
                          eq_refl))
                (Hm3 q (Hmiss 5%nat s4_idx (mword_of_int 8 : mword 6)
                          eq_refl))
                (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 12 : mword 6)
                          eq_refl))
                (Hm1 q Hqsp).
        reflexivity.
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq n0 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int cmd : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

End UkShParseRedir.
