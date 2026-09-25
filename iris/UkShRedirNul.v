(* ===================================================================== *)
(* UkShRedirNul.v -- nulterminate's REDIR ROW, lane SH-PARSE-2.           *)
(*                                                                        *)
(*   case REDIR: nulterminate(rcmd->cmd); *rcmd->efile = 0; break;        *)
(*                                                                        *)
(* FOUR INSTRUCTIONS -- 0x832 c.ld a0,8(a0); 0x834 jal nulterminate;      *)
(* 0x838 c.ld a5,24(s1); 0x83a sb zero,0(a5) -- and then the same 0x83e   *)
(* tail the EXEC arm falls into, so [UkShParseCmd.wp_kshp_nul_fin] closes *)
(* both.  Everything ABOVE the switch is the SAME walk at a different     *)
(* type word: 2 instead of 1, so the jump table is indexed at 0x13c8      *)
(* instead of 0x13c4 and the row there sends control to 0x832 instead of  *)
(* 0x81a.  [ushp_jrow_redir] is those four .rodata bytes, read off the    *)
(* image rather than written down.                                        *)
(*                                                                        *)
(* THE RECURSION IS ONE LEVEL, NOT AN INDUCTION.  The redirect line`s     *)
(* tree is a REDIR over an EXEC, so what the arm calls is the LANDED      *)
(* [UkShParseCmd.wp_kshp_nulterminate] and the answer is that lemma`s     *)
(* [ushp_nulfold] with ONE more byte cut, at the file name`s end.  A      *)
(* general nulterminate is an induction on [ushp_cmd] whose PIPE, LIST    *)
(* and BACK arms are three more walks over code no lane fetches; it is    *)
(* not free, so it is not stated.                                         *)
(*                                                                        *)
(* TAINT: none -- it allocates nothing.                                    *)
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
Require Import UkShParseLex.
Require Import UkShRedirCmd.
Require Import UkShParseCmd.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShRedirNul.
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
  Local Notation ushp_bytes_upd := (UkShParseCmd.ushp_bytes_upd N).
  Local Notation ushp_ro_byte := (UkShParseCmd.ushp_ro_byte N).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp N).
  Local Notation wp_kshp_nul_fin := (UkShParseCmd.wp_kshp_nul_fin N).
  Local Notation wp_kshp_nulterminate := (UkShParseCmd.wp_kshp_nulterminate N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  (* ---- the REDIR row of the jump table at 0x13c0 ---------------------- *)
  (* The row is a signed displacement from the table's own base, so 0x13c0 *)
  (* plus it is 0x832 -- which [vm_compute] checks below rather than this  *)
  (* comment asserting it. *)
  Lemma ushp_jrow_redir :
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4,
      utext γt (0x13c8 + Z.of_nat j)
        (nth_byte (mword_of_int 4294964338 : mword 32) j).
  Proof using .
    iIntros "#H". rewrite !big_sepL_cons big_sepL_nil.
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 0%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 0%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 1%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 1%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 2%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 2%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13c8 + Z.of_nat 3%nat)
                        (nth_byte (mword_of_int 4294964338 : mword 32) 3%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | done ].
  Qed.


  (* ---- nulterminate at a REDIR node over an EXEC node ------------------ *)
  Lemma wp_kshp_nulterminate_redir (h : CpuId) (m : regfile) (s0 p pc : Z)
      (len : nat) (g : nat -> bv 8) (toks : list (nat * nat))
      (qf e : nat) (mode fd : Z) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int p ->
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 40 < Z64 ->
    0 < pc -> pc mod 8 = 0 -> pc + 168 < Z64 ->
    (e <= len)%nat ->
    (length toks < 10)%nat ->
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       (fst tk <= len)%nat /\ (snd tk <= len)%nat) ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_redir_node s0 p pc qf e mode fd -∗
    ushp_exec_at s0 pc toks -∗
    ubytes γd s0 (S len) g -∗
    urun N h m (mword_of_int ShSyms.nulterminate) (4 + (4 + nn)) -∗
    (ushp_redir_node s0 p pc qf e mode fd -∗
     ushp_exec_at s0 pc toks -∗
     ubytes γd s0 (S len) (ushp_setb (ushp_nulfold toks g) e ubyte0) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (4 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Hs0 Hs64 Hp0 Hp8 Hpsz Hpc0 Hpc8 Hpcsz Hele Htlen Hsnd.
    iIntros "#Hcode #Hro Hn Hsub Hline Hrun Hcont".
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
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x7ee)
              (mword_of_int 32 : mword 6) 4 (4 + nn)
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
    iApply (wp_kshp_spill spn (4 + nn) [(ra_idx, mword_of_int 3 : mword 6);
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
    iApply (wp_kshp_fp h2 m1 0x7f6 (mword_of_int 8 : mword 8) (4 + nn)
              with "[] Hrun").
    { iApply (uis_shp_7f6 with "Hcode"). }
    iIntros (h3 v) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x7f8  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x7f8) s1_idx a0_idx
              (mword_of_int p) (4 + nn)
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
    iApply (wp_uk_cbeqz N h4 m3 (mword_of_int 0x7fa)
              (mword_of_int 34 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x83e) (4 + nn)
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
    rewrite /ushp_redir_node.
    iDestruct "Hn" as "(%Hnp & %Hna & %Hnz & [Hty4 Hpad] & Hcmd & Hfile
                        & Hefile & Hmode & Hfd)".
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    (* ---- 0x7fc  c.lw a4,0(a0) ---- *)
    iApply (wp_uk_clw N h5 m3 (mword_of_int 0x7fc)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx p
              (mword_of_int 2 : mword 32) (4 + nn)
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
                      (sign_extend' 64 (mword_of_int 2 : mword 32)
                       : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_4 : m4 !!! Regidx a4_idx = (mword_of_int 2 : mword 64)).
    { rewrite (upd_eq m3 (Regidx a4_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 2 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x7fe  c.li a5,5 ---- *)
    iApply (wp_uk_cli N h6 m4 (mword_of_int 0x7fe)
              (mword_of_int 5 : mword 6) a5_idx (4 + nn)
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
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int 2 : mword 64)).
    { rewrite (Hm5 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_4. }
    (* ---- 0x800  bltu a5,a4 -- NOT taken: EXEC is in range ---- *)
    iApply (wp_uk_btype N h7 m5 (mword_of_int 0x800)
              (mword_of_int 62 : mword 13) a4_idx a5_idx BLTU false
              (mword_of_int 0x83e) (4 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha5_5 Ha4_5;
                    rewrite (moi_lt_u 5 2 ltac:(unfold Z64; lia)
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
    iApply (wp_uk_lwu N h8 m5 (mword_of_int 0x804)
              (mword_of_int 0 : mword 12) a0_idx a5_idx p
              (mword_of_int 2 : mword 32) (4 + nn)
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
                      (zero_extend' 64 (mword_of_int 2 : mword 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int 2 : mword 64)).
    { rewrite (upd_eq m5 (Regidx a5_idx)
                 (regval_into_reg
                    (zero_extend' 64 (mword_of_int 2 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x808  c.slli a5,a5,0x2 ---- *)
    iApply (wp_uk_cslli N h9 m6 (mword_of_int 0x808)
              (mword_of_int 2 : mword 6) a5_idx (mword_of_int 8) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_6 (moi_shl 2 2 ltac:(lia)); f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_808 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 8 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_7 : m7 !!! Regidx a5_idx = (mword_of_int 8 : mword 64))
      by exact (upd_eq m6 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 8 : mword 64))).
    (* ---- 0x80a/0x80e  the jump table's base ---- *)
    iApply (wp_uk_auipc N h10 m7 (mword_of_int 0x80a)
              (mword_of_int 1 : mword 20) a4_idx
              (mword_of_int 0x180a) (4 + nn)
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
    iApply (wp_uk_addi N h11 m8 (mword_of_int 0x80e)
              (mword_of_int 2998 : mword 12) a4_idx a4_idx
              (mword_of_int 0x13c0) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_8; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_80e with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x13c0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = mword_of_int 0x13c0)
      by exact (upd_eq m8 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x13c0 : mword 64))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = (mword_of_int 8 : mword 64)).
    { rewrite (Hm9 a5_idx ltac:(vm_compute; discriminate))
              (Hm8 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0x812  c.add a5,a5,a4 -- the row's address ---- *)
    iApply (wp_uk_cadd N h12 m9 (mword_of_int 0x812) a5_idx
              a4_idx (mword_of_int 0x13c8) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_9 Ha4_9; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_812 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x13c8 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_10 : m10 !!! Regidx a5_idx = mword_of_int 0x13c8)
      by exact (upd_eq m9 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 0x13c8 : mword 64))).
    (* ---- 0x814  c.lw a5,0(a5) -- THE TEXT-HALF LOAD ---- *)
    iApply (wp_uk_clw_text N h13 m10 (mword_of_int 0x814)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx 0x13c8
              (mword_of_int 4294964338 : mword 32) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_10;
                    rewrite (uint_moi 0x13c8 ltac:(unfold Z64; lia));
                    vm_compute uoff_c4; lia)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] [] Hrun").
    { iApply (uis_shp_814 with "Hcode"). }
    { iApply (ushp_jrow_redir with "Hro"). }
    iIntros (h14) "Hrun".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64
                          (mword_of_int 4294964338 : mword 32)
                        : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha4_11 : m11 !!! Regidx a4_idx = mword_of_int 0x13c0).
    { rewrite (Hm11 a4_idx ltac:(vm_compute; discriminate))
              (Hm10 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_9. }
    (* ---- 0x816  c.add a5,a5,a4 -- the arm's pc ---- *)
    iApply (wp_uk_cadd N h14 m11 (mword_of_int 0x816) a5_idx
              a4_idx (mword_of_int 0x832) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_11
                      (upd_eq m10 (Regidx a5_idx)
                         (regval_into_reg
                            (sign_extend' 64
                               (mword_of_int 4294964338 : mword 32)
                             : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_816 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x832 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a5_idx) (Regidx q) _ Hq)).
    (* ---- 0x818  c.jr a5 -- the switch ---- *)
    iApply (wp_uk_cjr N h15 m12 (mword_of_int 0x818) a5_idx
              (mword_of_int 0x832) (4 + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m11 (Regidx a5_idx)
                               (regval_into_reg
                                  (mword_of_int 0x832 : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_818 with "Hcode"). }
    iIntros (h16) "Hrun".
    (* ---- 0x832  c.ld a5,8(a0) -- argv[0] ---- *)
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
    (* ---- 0x832  c.ld a0,8(a0) -- rcmd->cmd ---- *)
    iApply (wp_uk_cld N h16 m12 (mword_of_int 0x832)
              (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 2 : mword 3) a0_idx a0_idx
              (p + 8) (mword_of_int pc) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_12 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              ltac:(rewrite Zplus_mod Hp8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hcmd Hrun").
    { iApply (uis_shp_832 with "Hcode"). }
    iIntros "Hcmd" (h17) "Hrun".
    set (n1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int pc : mword 64)]> m12).
    assert (Hn1 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    n1 !!! Regidx r = m12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m12 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Ha0_n1 : n1 !!! Regidx a0_idx = mword_of_int pc)
      by exact (upd_eq m12 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int pc : mword 64))).
    (* ---- 0x834  jal ra,7ee <nulterminate> -- THE RECURSION ---- *)
    iApply (wp_uk_jal N h17 n1 (mword_of_int 0x834)
              (mword_of_int 2097082 : mword 21) ra_idx
              (mword_of_int 0x7ee) (mword_of_int 0x838) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_834 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (n2 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x838 : mword 64)]> n1).
    assert (Hn2 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    n2 !!! Regidx r = n1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n1 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_n2 : n2 !!! Regidx a0_idx = mword_of_int pc)
      by (rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_n1).
    assert (Eret2 : ret_pc (n2 !!! Regidx ra_idx) = mword_of_int 0x838);
      [ rewrite (upd_eq n1 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x838 : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    rewrite <- shpp_nulterminate.
    iApply (wp_kshp_nulterminate h18 n2 s0 pc len g toks nn
              Ha0_n2 Hs0 Hs64 Hpc0 Hpc8 Hpcsz Htlen Hsnd
              with "Hcode Hro Hsub Hline Hrun").
    iIntros "Hsub Hline" (h19 mr) "%Hcsr %Ha0_r Hrun".
    rewrite Eret2.
    (* ---- 0x838  c.ld a5,24(s1) -- rcmd->efile ---- *)
    assert (Hs1_r : mr !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcsr s1_idx ltac:(vm_compute; reflexivity))
              (Hn2 s1_idx ltac:(vm_compute; discriminate))
              (Hn1 s1_idx ltac:(vm_compute; discriminate))
              (Hkeep12 s1_idx ltac:(vm_compute; reflexivity)). exact Hs1_3. }
    iApply (wp_uk_cld N h19 mr (mword_of_int 0x838)
              (mword_of_int 3 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 7 : mword 3) s1_idx a5_idx
              (p + 24) (mword_of_int (s0 + Z.of_nat e)) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_r (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              ltac:(rewrite Zplus_mod Hp8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hefile Hrun").
    { iApply (uis_shp_838 with "Hcode"). }
    iIntros "Hefile" (h20) "Hrun".
    set (n3 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat e) : mword 64)]> mr).
    assert (Hn3 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                    n3 !!! Regidx r = mr !!! Regidx r)
      by (intros r Hr; exact (upd_ne mr (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha5_n3 : n3 !!! Regidx a5_idx
                     = mword_of_int (s0 + Z.of_nat e))
      by exact (upd_eq mr (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat e) : mword 64))).
    (* ---- 0x83a  sb zero,0(a5) -- *rcmd->efile = 0 ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    iDestruct (ushp_bytes_upd s0 (S len) (ushp_nulfold toks g) e ubyte0
                 ltac:(lia) with "Hline") as "[Hb Hbc]".
    iApply (wp_uk_sb N h20 n3 (mword_of_int 0x83a)
              (mword_of_int 0 : mword 12) a5_idx x0_idx
              (s0 + Z.of_nat e) (ushp_nulfold toks g e) (4 + nn)
              ltac:(rewrite Ha5_n3
                      (uint_moi (s0 + Z.of_nat e)
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              with "[] Hb Hrun").
    { iApply (uis_shp_83a with "Hcode"). }
    iIntros "Hb" (h21) "Hrun".
    rewrite Hx0.
    assert (Enb : nth_byte (zero_reg : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    rewrite Enb.
    iDestruct ("Hbc" with "Hb") as "Hline".
    (* ---- 0x83e..0x848  the common tail ---- *)
    iApply (wp_kshp_nul_fin sp0 spl vals p (4 + nn) h21 n3
              Hal8 Hlo ltac:(lia) Hsplu
              ltac:(rewrite (Hn3 csp_rs1 ltac:(vm_compute; discriminate))
                      (Hcsr csp_rs1 ltac:(vm_compute; reflexivity))
                      (Hn2 csp_rs1 ltac:(vm_compute; discriminate))
                      (Hn1 csp_rs1 ltac:(vm_compute; discriminate))
                      (Hkeep12 csp_rs1 ltac:(vm_compute; reflexivity));
                    exact Hsp3)
              ltac:(rewrite (Hn3 s1_idx ltac:(vm_compute; discriminate));
                    exact Hs1_r)
              with "Hcode Hsl Hloc Hrun").
    iIntros (hf) "Hrun".
    iApply ("Hcont" with
             "[Hty4 Hpad Hcmd Hfile Hefile Hmode Hfd] Hsub Hline [] [] Hrun").
    - rewrite /ushp_redir_node.
      iSplitR; [ iPureIntro; exact Hnp | ].
      iSplitR; [ iPureIntro; exact Hna | ].
      iSplitR; [ iPureIntro; exact Hnz | ].
      iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                               iExact "Hpad" ] | ].
      iFrame "Hcmd Hfile Hefile Hmode Hfd".
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals m
               (<[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> n3)
               sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| i ]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (upd_ne n3 (Regidx a0_idx) (Regidx r) _
                   (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
                (Hn3 r (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hcsr r Hr)
                (Hn2 r (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                          eq_refl))
                (Hn1 r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hkeep12 r Hr)
                (Hm3 r (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6)
                          eq_refl))
                (Hm2 r (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6)
                          eq_refl))
                (Hm1 r Hrsp).
        reflexivity.
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq n3 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| i ]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

End UkShRedirNul.
