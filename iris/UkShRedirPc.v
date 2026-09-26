(* ===================================================================== *)
(* UkShRedirPc.v -- parsecmd and THE PARSER THEOREM on the redirect line,  *)
(* lane SH-PARSE-2.                                                        *)
(*                                                                        *)
(* [UkShParseCmd.wp_kshp_parsecmd] with [parseline] and [nulterminate]     *)
(* swapped for their redirect forms, and then the theorem the lane owed:   *)
(*                                                                        *)
(*   GIVEN a NUL-terminated command line at [s0] of design SS5.1's          *)
(*   canonical redirect shape -- one '>' at [gp], one blank each side, the *)
(*   file name the run [[gp+2, fe)] -- whose ARGUMENT tokens are [args]    *)
(*   and number fewer than MAXARGS and at least one,                       *)
(*                                                                        *)
(*   sh's [parsecmd] RETURNS a node [p] with                               *)
(*   [ushp_tree s0 p (UshpRedir (UshpExec args) (S (S gp)) fe 1537 1)] --  *)
(*   the REDIR node over the exec node, at sh's own mode 0x601 and fd 1 -- *)
(*   with the line NUL-CUT at every argument's end index AND at the file   *)
(*   name's, with the callee-saved file intact, and at the return address. *)
(*                                                                        *)
(* AUDIT.  TWO Hypotheses reach it where the symbol-free theorem has one:  *)
(* the allocator's first call (execcmd's node) and its SECOND (redircmd's).*)
(* [UkShMalloc] proves only the first, so the second is an abstract        *)
(* premise here and stays one until a second-call theorem exists.          *)
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
Require UkShCmdalloc.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShRedirCmd.
Require Import UkShParseCmd.
Require Import UkShRedirNul.
Require Import UkShRedirCm.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShRedirPc.
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
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).


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
  Local Notation ushp_redir_close := (UkShRedirCmd.ushp_redir_close N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_ustr_bytes := (UkShParseCmd.ushp_ustr_bytes N).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen N).
  Local Notation wp_kshp_nulterminate_redir :=
    (UkShRedirNul.wp_kshp_nulterminate_redir N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  (* TWO allocator capabilities, chained -- see [UkShRedirPex]'s header. *)
  Context (UM0 UM1 UM2 : iProp Σ).
  Hypothesis ushp_malloc_ok0 : ushp_malloc_ty UM0 UM1.
  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).
  Hypothesis ushp_malloc_ok1 : ushp_malloc_ty UM1 UM2.

  Local Notation wp_kshp_execcmd :=
    (UkShParseLex.wp_kshp_execcmd N UM0 UM1 ushp_malloc_ok0).
  Local Notation wp_kshp_parseline_gt :=
    (UkShRedirCm.wp_kshp_parseline_gt N UM0 UM1 UM2
       ushp_malloc_ok0 ushp_malloc_ok1).

  (* the node's own extent, which the [nulterminate] descent needs before
     it may address the node at all *)
  Lemma ushp_redir_node_addr (s0 t pc : Z) (q eq : nat) (mode fd : Z) :
    ushp_redir_node s0 t pc q eq mode fd -∗
    ⌜ 0 < t /\ t mod 8 = 0 /\ t + 40 < Z64 ⌝ ∗
    ushp_redir_node s0 t pc q eq mode fd.
  Proof using .
    iIntros "Hn". rewrite {1}/ushp_redir_node.
    iDestruct "Hn" as "(%H1 & %H2 & %H3 & Hr)".
    iSplitR; [ iPureIntro; exact (conj H1 (conj H2 H3)) | ].
    rewrite /ushp_redir_node.
    iSplitR; [ iPureIntro; exact H1 | ].
    iSplitR; [ iPureIntro; exact H2 | ].
    iSplitR; [ iPureIntro; exact H3 | ]. iExact "Hr".
  Qed.

  (* the line after the parse: every argument's end byte cut to NUL by
     [nulterminate]'s EXEC arm, and the file name's by its REDIR arm *)
  Definition ushs_nulcut (args : list (nat * nat)) (len : nat)
      (f : nat -> bv 8) (fe : nat) : nat -> bv 8 :=
    ushp_setb (ushp_nulfold args (ushp_ext len f)) fe ubyte0.

  Lemma wp_kshp_parsecmd_gt {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dw dv : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (toks : list (nat * nat))
      (gp fe : nat) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat toks ->
    (0 < length toks)%nat ->
    (length toks < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    (* the exit resource the walk was LENT, and the out-of-memory law
       ([UkShCmdalloc.ushp_oom]; upstream d66e41c) that [cmdalloc]'s NULL
       arm hands it to, with the run at [panic]'s entry *)
    ushp_oom Pex (10 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd)
      (8 + (6 + (6 + (16 + (24 + (12 + nn)))))) -∗
    (∀ p pe : Z,
       ushp_redir_node s0 p pe (S (S gp)) fe 1537 1 -∗
       ushp_exec_at s0 pe toks -∗
       ubytes γd s0 (S len)
         (ushp_setb (ushp_nulfold toks (ushp_ext len f)) fe ubyte0) -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UM2 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (8 + (6 + (6 + (16 + (24 + (12 + nn)))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok0 ushp_malloc_ok1.
    intros Ha0 Hred Htoks Hpos Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
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
    (* ---- 0x84a  c.addi16sp sp,sp,-64 ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x84a)
              (mword_of_int 60 : mword 6) 8 (64 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_84a with "Hcode"). }
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
    (* ---- 0x84c..0x854  the five spills ---- *)
    iApply (wp_kshp_spill spn (64 + nn) [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x84c | 1%nat => 0x84e
                              | 2%nat => 0x850 | 3%nat => 0x852
                              | 4%nat => 0x854 | _ => 0x856 end)
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
      iSplit; [ iApply (uis_shp_84c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_84e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_850 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_852 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_854 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x856  c.addi4spn s0,sp,64 -- and its VALUE matters here ---- *)
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
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x856)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              sp0 (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1; symmetry; exact Efp)
              with "[] Hrun").
    { iApply (uis_shp_856 with "Hcode"). }
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
    (* ---- 0x858  sd a0,-56(s0) -- the cursor cell is initialised ---- *)
    assert (Hcur0 : 0 < uint sp0 - 56) by lia.
    assert (Hcur8 : (uint sp0 - 56) mod 8 = 0).
    { rewrite Zminus_mod Hal8. reflexivity. }
    assert (Hcurz : uint sp0 - 56 + 8 < Z64) by lia.
    iApply (wp_uk_sd N h3 m2 (mword_of_int 0x858)
              (mword_of_int 4040 : mword 12) s0_idx a0_idx
              (uint sp0 - 56) wcur (64 + nn)
              ltac:(rewrite Hs0_2 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              with "[] Lcur Hrun").
    { iApply (uis_shp_858 with "Hcode"). }
    iIntros "Lcur" (h4) "Hrun".
    rewrite Ha0_2.
    (* ---- 0x85c  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h4 m2 (mword_of_int 0x85c) s1_idx a0_idx
              (mword_of_int s0) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2; symmetry; exact (ushp_mv_val s0))
              with "[] Hrun").
    { iApply (uis_shp_85c with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int s0 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x85e  jal a0c <strlen> ---- *)
    iApply (wp_uk_jal N h5 m3 (mword_of_int 0x85e)
              (mword_of_int 430 : mword 21) ra_idx
              (mword_of_int 0xa0c) (mword_of_int 0x862) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_85e with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x862 : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret4 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x862).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x862 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int s0).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_2. }
    rewrite <- shpp_strlen.
    iApply (wp_kshp_strlen h6 m4 (DfracOwn 1) s0 len f (62 + nn)
              Ha0_4 ltac:(lia) ltac:(lia) with "Hcode Hstr Hrun").
    iIntros "Hstr" (h7 m5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    (* ---- 0x862/0x864  the 32-bit zero extension ---- *)
    assert (E32 : (2:Z) ^ 32 = 4294967296) by (vm_compute; reflexivity).
    iApply (wp_uk_cslli N h7 m5 (mword_of_int 0x862)
              (mword_of_int 32 : mword 6) a0_idx
              (mword_of_int (Z.of_nat len * 2 ^ 32)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry;
                    exact (moi_shl (Z.of_nat len) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_862 with "Hcode"). }
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
    iApply (wp_uk_csrli N h8 m6 (mword_of_int 0x864)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 3) a0_idx
              (mword_of_int (Z.of_nat len)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6
                      (moi_shr (Z.of_nat len * 2 ^ 32) 32 ltac:(lia)
                         ltac:(rewrite E32; unfold Z64; lia));
                    f_equal; symmetry; apply Z.div_mul; lia)
              with "[] Hrun").
    { iApply (uis_shp_864 with "Hcode"). }
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
    (* ---- 0x866  c.add s1,s1,a0 -- es = s + len ---- *)
    assert (Hs1_7 : m7 !!! Regidx s1_idx = mword_of_int s0).
    { rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hm6 s1_idx ltac:(vm_compute; discriminate))
              (Hcs45 s1_idx ltac:(vm_compute; reflexivity))
              (Hm4 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s1_idx)
               (regval_into_reg (mword_of_int s0 : mword 64))). }
    iApply (wp_uk_cadd N h9 m7 (mword_of_int 0x866) s1_idx
              a0_idx (mword_of_int (s0 + Z.of_nat len)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_7 Ha0_7; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_866 with "Hcode"). }
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
    (* ---- 0x868  addi s2,s0,-56 -- &s ---- *)
    assert (Hs0_8 : m8 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm8 s0_idx ltac:(vm_compute; discriminate))
              (Hm7 s0_idx ltac:(vm_compute; discriminate))
              (Hm6 s0_idx ltac:(vm_compute; discriminate))
              (Hcs45 s0_idx ltac:(vm_compute; reflexivity))
              (Hm4 s0_idx ltac:(vm_compute; discriminate))
              (Hm3 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_2. }
    iApply (wp_uk_addi N h10 m8 (mword_of_int 0x868)
              (mword_of_int 4040 : mword 12) s0_idx s2_idx
              (mword_of_int (uint sp0 - 56)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_8;
                    assert (Ei : (sign_extend' 64
                                    (mword_of_int 4040 : mword 12)
                                  : mword 64) = mword_of_int (-56))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_868 with "Hcode"). }
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
    (* ---- 0x86c/0x86e  parseline(&s, es) ---- *)
    iApply (wp_uk_cmv N h11 m9 (mword_of_int 0x86c) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_86c with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h12 m10 (mword_of_int 0x86e) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_86e with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x870  jal 6be <parseline> ---- *)
    iApply (wp_uk_jal N h13 m11 (mword_of_int 0x870)
              (mword_of_int 2096718 : mword 21) ra_idx
              (mword_of_int 0x6be) (mword_of_int 0x874) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_870 with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x874 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x874).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x874 : mword 64))).
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
    iApply (wp_kshp_parseline_gt h14 m12 (DfracOwn 1) dw dv
              (uint sp0 - 56) s0 len 0%nat f (mword_of_int s0) toks
              gp fe nn
              Ha0_12 Ha1_12 ltac:(lia)
              ltac:(f_equal; lia)
              Hred Htoks Hpos Htlen ltac:(lia) ltac:(lia)
              Hcur0 Hcur8 Hcurz
              with "Hcode Hro Lcur Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (p pe) "%Hpsz Hrnode Hnode Lcur Hstr Hws Hsy".
    iIntros (h15 m13) "%Hcs1213 %Ha0_13 HM' Hpay Hrun".
    rewrite Eret12.
    iDestruct (ushp_redir_node_addr with "Hrnode") as "[%Hraddr Hrnode]".
    destruct Hraddr as (Hp0 & Hp8 & Hpz40).
    iDestruct "Hnode" as "(%Hnl & %Hpe0 & %Hpe8 & Hty & Hav & Hev)".
    iAssert (ushp_exec_at s0 pe toks) with "[Hty Hav Hev]" as "Hnode".
    { rewrite /ushp_exec_at.
      iSplitR; [ iPureIntro; exact Hnl | ].
      iSplitR; [ iPureIntro; exact Hpe0 | ].
      iSplitR; [ iPureIntro; exact Hpe8 | ].
      iSplitL "Hty"; [ iExact "Hty" | ].
      iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
    (* ---- 0x874  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv N h15 m13 (mword_of_int 0x874) s3_idx
              a0_idx (mword_of_int p) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_13; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_874 with "Hcode"). }
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
    (* ---- 0x876/0x87a  the EMPTY token table ---- *)
    iApply (wp_uk_auipc N h16 m14 (mword_of_int 0x876)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x1876) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_876 with "Hcode"). }
    iIntros (h17) "Hrun".
    set (m15 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 0x1876 : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_15 : m15 !!! Regidx a2_idx = mword_of_int 0x1876)
      by exact (upd_eq m14 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x1876 : mword 64))).
    iApply (wp_uk_addi N h17 m15 (mword_of_int 0x87a)
              (mword_of_int 2562 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_none) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_15; unfold ushp_T_none;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_87a with "Hcode"). }
    iIntros (h18) "Hrun".
    set (m16 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_none : mword 64)]> m15).
    assert (Hm16 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m16 !!! Regidx q = m15 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m15 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x87e/0x880  peek(&s, es, "") ---- *)
    iApply (wp_uk_cmv N h18 m16 (mword_of_int 0x87e) a1_idx
              s1_idx (mword_of_int (s0 + Z.of_nat len)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm16 s1_idx ltac:(vm_compute; discriminate))
                      (Hm15 s1_idx ltac:(vm_compute; discriminate))
                      Hs1_14; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_87e with "Hcode"). }
    iIntros (h19) "Hrun".
    set (m17 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m16).
    assert (Hm17 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m17 !!! Regidx q = m16 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m16 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h19 m17 (mword_of_int 0x880) a0_idx
              s2_idx (mword_of_int (uint sp0 - 56)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm17 s2_idx ltac:(vm_compute; discriminate))
                      (Hm16 s2_idx ltac:(vm_compute; discriminate))
                      (Hm15 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_14; symmetry;
                    exact (ushp_mv_val (uint sp0 - 56)))
              with "[] Hrun").
    { iApply (uis_shp_880 with "Hcode"). }
    iIntros (h20) "Hrun".
    set (m18 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (uint sp0 - 56) : mword 64)]> m17).
    assert (Hm18 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m18 !!! Regidx q = m17 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m17 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x882  jal 424 <peek> ---- *)
    iApply (wp_uk_jal N h20 m18 (mword_of_int 0x882)
              (mword_of_int 2096034 : mword 21) ra_idx
              (mword_of_int 0x424) (mword_of_int 0x886) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_882 with "Hcode"). }
    iIntros (h21) "Hrun".
    set (m19 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x886 : mword 64)]> m18).
    assert (Hm19 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m19 !!! Regidx q = m18 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m18 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret19 : ret_pc (m19 !!! Regidx ra_idx) = mword_of_int 0x886).
    { rewrite (upd_eq m18 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x886 : mword 64))).
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
              (mword_of_int (s0 + Z.of_nat len)) (54 + nn)
              Ha0_19 Ha1_19 Ha2_19 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)
              ltac:(unfold ushp_T_none; lia)
              ltac:(unfold ushp_T_none, Z64; lia) Hcur0 Hcur8 Hcurz
              with "Hcode Lcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_none 0 DfracDiscarded
                ushp_T_none_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Lcur Hstr Hws _" (h22 m20) "%Hcs1920 %Ha0_20 Hrun".
    rewrite Eret19 Elen0.
    (* ---- 0x886  ld a2,-56(s0) -- the cursor, read back ---- *)
    assert (Hs0_19 : m19 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hm19 s0_idx ltac:(vm_compute; discriminate))
              (Hm18 s0_idx ltac:(vm_compute; discriminate))
              (Hm17 s0_idx ltac:(vm_compute; discriminate))
              (Hm16 s0_idx ltac:(vm_compute; discriminate))
              (Hm15 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_14. }
    assert (Hs0_20 : m20 !!! Regidx s0_idx = mword_of_int (uint sp0)).
    { rewrite (Hcs1920 s0_idx ltac:(vm_compute; reflexivity)).
      exact Hs0_19. }
    iApply (wp_uk_ld N h22 m20 (mword_of_int 0x886)
              (mword_of_int 4040 : mword 12) s0_idx a2_idx (DfracOwn 1)
              (uint sp0 - 56) (mword_of_int (s0 + Z.of_nat len)) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_20 (uint_moi (uint sp0) ltac:(lia));
                    vm_compute uoff_i12; lia)
              Hcur8
              ltac:(vm_compute; discriminate)
              with "[] Lcur Hrun").
    { iApply (uis_shp_886 with "Hcode"). }
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
    (* ---- 0x88a  bne a2,s1 -- NOT taken: there are no leftovers ---- *)
    iApply (wp_uk_btype N h23 m21 (mword_of_int 0x88a)
              (mword_of_int 26 : mword 13) s1_idx a2_idx BNE false
              (mword_of_int 0x8a4) (64 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha2_21 Hs1_21;
                    rewrite (moi_neq_vec (s0 + Z.of_nat len)
                               (s0 + Z.of_nat len)
                               ltac:(unfold Z64 in *; lia)
                               ltac:(unfold Z64 in *; lia));
                    rewrite Z.eqb_refl; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_88a with "Hcode"). }
    iIntros (h24) "Hrun".
    (* ---- 0x88e  c.mv a0,s3 ---- *)
    assert (Hs3_21 : m21 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hm21 s3_idx ltac:(vm_compute; discriminate))
              (Hcs1920 s3_idx ltac:(vm_compute; reflexivity))
              (Hm19 s3_idx ltac:(vm_compute; discriminate))
              (Hm18 s3_idx ltac:(vm_compute; discriminate))
              (Hm17 s3_idx ltac:(vm_compute; discriminate))
              (Hm16 s3_idx ltac:(vm_compute; discriminate))
              (Hm15 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_14. }
    iApply (wp_uk_cmv N h24 m21 (mword_of_int 0x88e) a0_idx
              s3_idx (mword_of_int p) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_21; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_88e with "Hcode"). }
    iIntros (h25) "Hrun".
    set (m22 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m21).
    assert (Hm22 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m22 !!! Regidx q = m21 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m21 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x890  jal 7ca <nulterminate> ---- *)
    iApply (wp_uk_jal N h25 m22 (mword_of_int 0x890)
              (mword_of_int 2096954 : mword 21) ra_idx
              (mword_of_int 0x7ca) (mword_of_int 0x894) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_890 with "Hcode"). }
    iIntros (h26) "Hrun".
    set (m23 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x894 : mword 64)]> m22).
    assert (Hm23 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m23 !!! Regidx q = m22 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m22 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret23 : ret_pc (m23 !!! Regidx ra_idx) = mword_of_int 0x894).
    { rewrite (upd_eq m22 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x894 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_23 : m23 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm23 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m21 (Regidx a0_idx)
               (regval_into_reg (mword_of_int p : mword 64))). }
    iDestruct (ushp_ustr_bytes s0 len f with "Hstr") as "Hline".
    rewrite <- shpp_nulterminate.
    iApply (wp_kshp_nulterminate_redir h26 m23 s0 p pe len (ushp_ext len f)
              toks (S (S gp)) fe 1537 1 (56 + nn)
              Ha0_23 ltac:(lia) ltac:(lia) Hp0 Hp8 Hpz40
              Hpe0 Hpe8 Hpsz
              ltac:(destruct Hred as (_ & _ & _ & _ & _ & Hlt & _ & _); lia)
              Htlen
              ltac:(intros i t Hi;
                    destruct (ushs_toks_in len f gp 0%nat toks Htoks
                                i t Hi) as [ Hlo0 Hhi0 ];
                    split; lia)
              with "Hcode Hro Hrnode Hnode Hline Hrun").
    iIntros "Hrnode Hnode Hline" (h27 m24) "%Hcs2324 %Ha0_24 Hrun".
    rewrite Eret23.
    (* ---- 0x894  c.mv a0,s3 ---- *)
    assert (Hs3_24 : m24 !!! Regidx s3_idx = mword_of_int p).
    { rewrite (Hcs2324 s3_idx ltac:(vm_compute; reflexivity))
              (Hm23 s3_idx ltac:(vm_compute; discriminate))
              (Hm22 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_21. }
    iApply (wp_uk_cmv N h27 m24 (mword_of_int 0x894) a0_idx
              s3_idx (mword_of_int p) (64 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_24; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_894 with "Hcode"). }
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
    (* ---- 0x896..0x8a2  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 8 3 [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6)] (mword_of_int 7 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x896 | 1%nat => 0x898
                              | 2%nat => 0x89a | 3%nat => 0x89c
                              | 4%nat => 0x89e | _ => 0x8a0 end)
              (mword_of_int 4 : mword 6) sp0 spl vals (64 + nn) h28 me
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
      iSplit; [ iApply (uis_shp_896 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_898 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_89a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_89c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_89e with "Hcode") | done ]. }
    { iApply (uis_shp_8a0 with "Hcode"). }
    { iApply (uis_shp_8a2 with "Hcode"). }
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
    iApply ("Hcont" $! p pe
              with "Hrnode Hnode Hline Hws Hsy [] [] HM' Hpay Hrun").
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
  (* THE PARSER THEOREM, at the redirect shape.                             *)
  (* ===================================================================== *)

  Lemma ushs_nulcut_arg (args : list (nat * nat)) (len : nat)
      (f : nat -> bv 8) (fe : nat) (i : nat) (tk : nat * nat) :
    args !! i = Some tk -> ushs_nulcut args len f fe (snd tk) = ubyte0.
  Proof using .
    intro Hi. rewrite /ushs_nulcut /ushp_setb.
    destruct (Nat.eqb (snd tk) fe); [ reflexivity | ].
    exact (ushp_nulfold_hit args (ushp_ext len f) i tk Hi).
  Qed.

  Lemma ushs_nulcut_file (args : list (nat * nat)) (len : nat)
      (f : nat -> bv 8) (fe : nat) :
    ushs_nulcut args len f fe fe = ubyte0.
  Proof using .
    rewrite /ushs_nulcut /ushp_setb Nat.eqb_refl. reflexivity.
  Qed.

  Theorem wp_kshp_parser_redir {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dw dv : dfrac) (s0 : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int s0 ->
    ushs_redir len f gp fe ->
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
    ushp_oom Pex (10 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsecmd) (72 + nn) -∗
    (∀ p : Z,
       ushp_tree s0 p (UshpRedir (UshpExec args) (S (S gp)) fe 1537 1) -∗
       ubytes γd s0 (S len) (ushs_nulcut args len f fe) -∗
       ⌜ forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
           ushs_nulcut args len f fe (snd tk) = ubyte0 ⌝ -∗
       ⌜ ushs_nulcut args len f fe fe = ubyte0 ⌝ -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
           UM2 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (72 + nn) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok0 ushp_malloc_ok1.
    intros Ha0 Hred Htoks Hpos Htlen Hs0 Hs64.
    iIntros "#Hcode #Hro Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iApply (wp_kshp_parsecmd_gt h m dw dv s0 len f args gp fe nn
              Ha0 Hred Htoks Hpos Htlen Hs0 Hs64
              with "Hcode Hro Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (p pe) "Hrnode Hnode Hline Hws Hsy".
    iApply ("Hcont" $! p with "[Hrnode Hnode] Hline [] [] Hws Hsy").
    - iApply (ushp_redir_close s0 p pe (S (S gp)) fe 1537 1 (UshpExec args)
                with "Hrnode Hnode").
    - iPureIntro. intros i tk Hi. exact (ushs_nulcut_arg args len f fe i tk Hi).
    - iPureIntro. exact (ushs_nulcut_file args len f fe).
  Qed.

End UkShRedirPc.
