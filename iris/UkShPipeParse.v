(* ===================================================================== *)
(* UkShPipeParse.v -- THE PIPE NODE AND nulterminate's PIPE ROW,          *)
(* lane SH-PARSE-PIPE (design/app-pipe.md SS5.1, the parser paragraph).     *)
(*                                                                        *)
(*   case PIPE: nulterminate(pcmd->left); nulterminate(pcmd->right);      *)
(*              break;                        (user/sh.c:481)             *)
(*                                                                        *)
(* FIVE INSTRUCTIONS -- 0x826 c.ld a0,8(a0); 0x828 jal nulterminate;      *)
(* 0x82c c.ld a0,16(s1); 0x82e jal nulterminate; 0x832 c.j 83e -- and     *)
(* then the same 0x81a tail the EXEC and REDIR arms fall into, so          *)
(* [UkShParseCmd.wp_kshp_nul_fin] closes this one too.  Everything ABOVE   *)
(* the switch is the SAME walk at a different type word: 3 instead of 2,   *)
(* so the row is indexed at 0x13bc instead of 0x13b8 and the table sends   *)
(* control to 0x826 instead of 0x80e.  [ushp_jrow_pipe] is those four      *)
(* .rodata bytes (0xFFFFF49A, and 0x13b0 + it IS 0x826), read off the      *)
(* image rather than written down.                                        *)
(*                                                                        *)
(* THE RECURSION IS ONE LEVEL EACH SIDE, NOT AN INDUCTION.  The pipe       *)
(* line's tree is a PIPE over two EXEC nodes, so what the arm calls twice  *)
(* is the LANDED [UkShParseCmd.wp_kshp_nulterminate] and the answer is     *)
(* that lemma's [ushp_nulfold] COMPOSED -- the right command's argv cut    *)
(* over the left command's, both in the one line buffer.  The two calls    *)
(* run at the same stack depth, so the arm's budget is the REDIR arm's     *)
(* unchanged: [4 + (4 + nn)].                                             *)
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

Section UkShPipeParse.
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
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
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

  (* ===================================================================== *)
  (* §1 THE PIPE NODE, WITH BOTH CHILD POINTERS NAMED                       *)
  (*                                                                        *)
  (* SH-PARSE-2's shape fact, at two pointers instead of one:               *)
  (* [UkShParse.ushp_tree]'s PIPE row hides the children under existentials, *)
  (* which is the right reading of a FINISHED tree and the wrong            *)
  (* postcondition for a CONSTRUCTOR, because [nulterminate] has to ADDRESS  *)
  (* each child.  So this is the node's own three fields with both pointers  *)
  (* named and nothing said about what lives there, and [ushp_pipe_close]    *)
  (* is the one-way door to the published form.                              *)
  (* ===================================================================== *)

  Definition ushp_pipe_node (t pl pr : Z) : iProp Σ :=
    (⌜ 0 < t ⌝ ∗ ⌜ t mod 8 = 0 ⌝ ∗ ⌜ t + 40 < Z64 ⌝ ∗
     (ubytes γd t 4 (nth_byte (mword_of_int 3 : mword 32)) ∗
      (∃ g : nat -> bv 8, ubytes γd (t + 4) 4 g)) ∗
     uword γd (t + 8) (mword_of_int pl) ∗
     uword γd (t + 16) (mword_of_int pr))%I.

  (* the node's own address facts, handed back with the node -- the twin of
     [UkShRedirPc.ushp_redir_node_addr], and what [nulterminate]'s walk
     needs before it may address the children *)
  Lemma ushp_pipe_node_addr (t pl pr : Z) :
    ushp_pipe_node t pl pr -∗
    ⌜ 0 < t /\ t mod 8 = 0 /\ t + 40 < Z64 ⌝ ∗ ushp_pipe_node t pl pr.
  Proof using .
    iIntros "Hn". rewrite {1}/ushp_pipe_node.
    iDestruct "Hn" as "(%H1 & %H2 & %H3 & Hr)".
    iSplitR; [ iPureIntro; exact (conj H1 (conj H2 H3)) | ].
    rewrite /ushp_pipe_node.
    iSplitR; [ iPureIntro; exact H1 | ].
    iSplitR; [ iPureIntro; exact H2 | ].
    iSplitR; [ iPureIntro; exact H3 | ]. iExact "Hr".
  Qed.

  (* ...and an EXEC node's own three pure facts, handed back with it
     (lane PIPES-C3b: what a caller of the arm's EXEC call reads) *)
  Lemma ushp_exec_at_facts (s0 p : Z) (toks : list (nat * nat)) :
    ushp_exec_at s0 p toks -∗
    ⌜ (length toks < 10)%nat /\ 0 < p /\ p mod 8 = 0 ⌝ ∗ ushp_exec_at s0 p toks.
  Proof using .
    iIntros "Hn". rewrite {1}/UkShParse.ushp_exec_at.
    iDestruct "Hn" as "(%H1 & %H2 & %H3 & Hr)".
    iSplitR; [ iPureIntro; exact (conj H1 (conj H2 H3)) | ].
    rewrite /UkShParse.ushp_exec_at.
    iSplitR; [ iPureIntro; exact H1 | ].
    iSplitR; [ iPureIntro; exact H2 | ].
    iSplitR; [ iPureIntro; exact H3 | ]. iExact "Hr".
  Qed.

  Lemma ushp_pipe_close (s0 t pl pr : Z) (l r : ushp_cmd) :
    ushp_pipe_node t pl pr -∗
    ushp_tree s0 pl l -∗ ushp_tree s0 pr r -∗
    ushp_tree s0 t (UshpPipe l r).
  Proof using .
    iIntros "Hn Hl Hr". rewrite /ushp_pipe_node.
    iDestruct "Hn" as "(%Ht0 & %Ht8 & %Htz & Hty & Hleft & Hright)".
    cbn [ushp_tree ushp_ty]. rewrite /ushp_type_at.
    iSplitR; [ iPureIntro; exact Ht0 | ].
    iSplitR; [ iPureIntro; exact Ht8 | ].
    iSplitL "Hty"; [ iExact "Hty" | ].
    iSplitL "Hleft Hl"; [ iExists pl; iFrame "Hleft Hl" | ].
    iExists pr. iFrame "Hright Hr".
  Qed.

  (* ---- the PIPE row of the jump table at 0x13b0 ---------------------- *)
  (* The row is a signed displacement from the table's own base, so 0x13b0 *)
  (* plus it is 0x826 -- which [vm_compute] checks below rather than this  *)
  (* comment asserting it. *)
  Lemma ushp_jrow_pipe :
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4,
      utext γt (0x13bc + Z.of_nat j)
        (nth_byte (mword_of_int 4294964342 : mword 32) j).
  Proof using .
    iIntros "#H". rewrite !big_sepL_cons big_sepL_nil.
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 0%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 0%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 1%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 1%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 2%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 2%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 3%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 3%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | done ].
  Qed.


  (* ===================================================================== *)
  (* §2 nulterminate AT A PIPE NODE OVER TWO EXEC NODES                     *)
  (* ===================================================================== *)

  (* THE ARM WITH ITS RIGHT RECURSION A PREMISE (lane PIPES-C3b).  The
     left child of a pipe node is always an EXEC node (sh's parse is
     right-recursive), so the left call stays the landed EXEC walk; the
     right child is whatever the rest of the spine is, so its call is a
     premise at the child's own resource [RR] and cut [gR] -- which at
     the one-bar line is the landed EXEC walk again
     ([wp_kshp_nulterminate_pipe] below) and at a longer line is the
     induction hypothesis ([UkShPipesCmd.wp_kshp_nulterminate_pipes]).
     Both calls run at the same stack depth, [4 + nn]. *)
  Lemma wp_kshp_nulterminate_pipe_g (h : CpuId) (m : regfile) (s0 p pl pr : Z)
      (len : nat) (g : nat -> bv 8) (toksl : list (nat * nat))
      (RR : iProp Σ) (gR : (nat -> bv 8) -> nat -> bv 8)
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int p ->
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 40 < Z64 ->
    0 < pl -> pl mod 8 = 0 -> pl + 168 < Z64 ->
    (length toksl < 10)%nat ->
    (forall (i : nat) (tk : nat * nat), toksl !! i = Some tk ->
       (fst tk <= len)%nat /\ (snd tk <= len)%nat) ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_pipe_node p pl pr -∗
    ushp_exec_at s0 pl toksl -∗
    RR -∗
    ubytes γd s0 (S len) g -∗
    urun N h m (mword_of_int ShSyms.nulterminate) (4 + (4 + nn)) -∗
    (* the RIGHT child's call *)
    (∀ (h1 : CpuId) (m1 : regfile) (g1 : nat -> bv 8),
       ⌜ m1 !!! Regidx a0_idx = mword_of_int pr ⌝ -∗
       RR -∗
       ubytes γd s0 (S len) g1 -∗
       urun N h1 m1 (mword_of_int ShSyms.nulterminate) (4 + nn) -∗
       (RR -∗
        ubytes γd s0 (S len) (gR g1) -∗
          ∀ (h2 : CpuId) (m2 : regfile),
            ⌜ ucallee_saved m1 m2 ⌝ -∗
            ⌜ m2 !!! Regidx a0_idx = mword_of_int pr ⌝ -∗
            urun N h2 m2 (ret_pc (m1 !!! Regidx ra_idx)) (4 + nn) -∗
            mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (ushp_pipe_node p pl pr -∗
     ushp_exec_at s0 pl toksl -∗
     RR -∗
     ubytes γd s0 (S len) (gR (ushp_nulfold toksl g)) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (4 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Hs0 Hs64 Hp0 Hp8 Hpsz Hpl0 Hpl8 Hplsz Htlenl Hsndl.
    iIntros "#Hcode #Hro Hn Hsubl Hsubr Hline Hrun Hrcall Hcont".
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
    (* ---- 0x7ca  c.addi sp,sp,-32 ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x7ca)
              (mword_of_int 32 : mword 6) 4 (4 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7ca with "Hcode"). }
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
    (* ---- 0x7cc..0x7d0  the three spills ---- *)
    iApply (wp_kshp_spill spn (4 + nn) [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x7cc | 1%nat => 0x7ce
                              | 2%nat => 0x7d0 | _ => 0x7d2 end)
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
      iSplit; [ iApply (uis_shp_7cc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7ce with "Hcode") | ].
      iSplit; [ iApply (uis_shp_7d0 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x7d2  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_kshp_fp h2 m1 0x7d2 (mword_of_int 8 : mword 8) (4 + nn)
              with "[] Hrun").
    { iApply (uis_shp_7d2 with "Hcode"). }
    iIntros (h3 v) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x7d4  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x7d4) s1_idx a0_idx
              (mword_of_int p) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_7d4 with "Hcode"). }
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
    (* ---- 0x7d6  c.beqz a0 -- NOT taken: the node is not null ---- *)
    iApply (wp_uk_cbeqz N h4 m3 (mword_of_int 0x7d6)
              (mword_of_int 34 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x81a) (4 + nn)
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
    { iApply (uis_shp_7d6 with "Hcode"). }
    iIntros (h5) "Hrun".
    (* ---- the node's type word, read twice ---- *)
    rewrite /ushp_pipe_node.
    iDestruct "Hn" as "(%Hnp & %Hna & %Hnz & [Hty4 Hpad] & Hleft & Hright)".
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    (* ---- 0x7d8  c.lw a4,0(a0) ---- *)
    iApply (wp_uk_clw N h5 m3 (mword_of_int 0x7d8)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx p
              (mword_of_int 3 : mword 32) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c4; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_7d8 with "Hcode"). }
    iIntros "Hty4" (h6) "Hrun".
    set (m4 := <[Regidx a4_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 3 : mword 32)
                       : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_4 : m4 !!! Regidx a4_idx = (mword_of_int 3 : mword 64)).
    { rewrite (upd_eq m3 (Regidx a4_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 3 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x7da  c.li a5,5 ---- *)
    iApply (wp_uk_cli N h6 m4 (mword_of_int 0x7da)
              (mword_of_int 5 : mword 6) a5_idx (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7da with "Hcode"). }
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
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int 3 : mword 64)).
    { rewrite (Hm5 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_4. }
    (* ---- 0x7dc  bltu a5,a4 -- NOT taken: PIPE is in range ---- *)
    iApply (wp_uk_btype N h7 m5 (mword_of_int 0x7dc)
              (mword_of_int 62 : mword 13) a4_idx a5_idx BLTU false
              (mword_of_int 0x81a) (4 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha5_5 Ha4_5;
                    rewrite (moi_lt_u 5 3 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia)); reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_7dc with "Hcode"). }
    iIntros (h8) "Hrun".
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_3. }
    (* ---- 0x7e0  lwu a5,0(a0) ---- *)
    iApply (wp_uk_lwu N h8 m5 (mword_of_int 0x7e0)
              (mword_of_int 0 : mword 12) a0_idx a5_idx p
              (mword_of_int 3 : mword 32) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_5 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hp4
              ltac:(vm_compute; discriminate)
              with "[] Hty4 Hrun").
    { iApply (uis_shp_7e0 with "Hcode"). }
    iIntros "Hty4" (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (zero_extend' 64 (mword_of_int 3 : mword 32)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int 3 : mword 64)).
    { rewrite (upd_eq m5 (Regidx a5_idx)
                 (regval_into_reg
                    (zero_extend' 64 (mword_of_int 3 : mword 32)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x7e4  c.slli a5,a5,0x2 ---- *)
    iApply (wp_uk_cslli N h9 m6 (mword_of_int 0x7e4)
              (mword_of_int 2 : mword 6) a5_idx (mword_of_int 12) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_6 (moi_shl 3 2 ltac:(lia)); f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shp_7e4 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 12 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_7 : m7 !!! Regidx a5_idx = (mword_of_int 12 : mword 64))
      by exact (upd_eq m6 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 12 : mword 64))).
    (* ---- 0x7e6/0x7ea  the jump table's base ---- *)
    iApply (wp_uk_auipc N h10 m7 (mword_of_int 0x7e6)
              (mword_of_int 1 : mword 20) a4_idx
              (mword_of_int 0x17e6) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7e6 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x17e6 : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int 0x17e6)
      by exact (upd_eq m7 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x17e6 : mword 64))).
    iApply (wp_uk_addi N h11 m8 (mword_of_int 0x7ea)
              (mword_of_int 3018 : mword 12) a4_idx a4_idx
              (mword_of_int 0x13b0) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_8; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7ea with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x13b0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = mword_of_int 0x13b0)
      by exact (upd_eq m8 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x13b0 : mword 64))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = (mword_of_int 12 : mword 64)).
    { rewrite (Hm9 a5_idx ltac:(vm_compute; discriminate))
              (Hm8 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0x7ee  c.add a5,a5,a4 -- the row's address ---- *)
    iApply (wp_uk_cadd N h12 m9 (mword_of_int 0x7ee) a5_idx
              a4_idx (mword_of_int 0x13bc) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_9 Ha4_9; symmetry; apply moi_add)
              with "[] Hrun").
    { iApply (uis_shp_7ee with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x13bc : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_10 : m10 !!! Regidx a5_idx = mword_of_int 0x13bc)
      by exact (upd_eq m9 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 0x13bc : mword 64))).
    (* ---- 0x7f0  c.lw a5,0(a5) -- THE TEXT-HALF LOAD ---- *)
    iApply (wp_uk_clw_text N h13 m10 (mword_of_int 0x7f0)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx 0x13bc
              (mword_of_int 4294964342 : mword 32) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_10;
                    rewrite (uint_moi 0x13bc ltac:(unfold Z64; lia));
                    vm_compute uoff_c4; lia)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] [] Hrun").
    { iApply (uis_shp_7f0 with "Hcode"). }
    { iApply (ushp_jrow_pipe with "Hro"). }
    iIntros (h14) "Hrun".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64
                          (mword_of_int 4294964342 : mword 32)
                        : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha4_11 : m11 !!! Regidx a4_idx = mword_of_int 0x13b0).
    { rewrite (Hm11 a4_idx ltac:(vm_compute; discriminate))
              (Hm10 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_9. }
    (* ---- 0x7f2  c.add a5,a5,a4 -- the arm's pc ---- *)
    iApply (wp_uk_cadd N h14 m11 (mword_of_int 0x7f2) a5_idx
              a4_idx (mword_of_int 0x826) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_11
                      (upd_eq m10 (Regidx a5_idx)
                         (regval_into_reg
                            (sign_extend' 64
                               (mword_of_int 4294964342 : mword 32)
                             : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7f2 with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x826 : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a5_idx) (Regidx q) _ Hq)).
    (* ---- 0x7f4  c.jr a5 -- the switch ---- *)
    iApply (wp_uk_cjr N h15 m12 (mword_of_int 0x7f4) a5_idx
              (mword_of_int 0x826) (4 + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m11 (Regidx a5_idx)
                               (regval_into_reg
                                  (mword_of_int 0x826 : mword 64)));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_7f4 with "Hcode"). }
    iIntros (h16) "Hrun".
    (* ---- the two child pointers the arm is about to read ---- *)
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
    (* ---- 0x826  c.ld a0,8(a0) -- pcmd->left ---- *)
    iApply (wp_uk_cld N h16 m12 (mword_of_int 0x826)
              (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 2 : mword 3) a0_idx a0_idx
              (p + 8) (mword_of_int pl) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_12 (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              ltac:(rewrite Zplus_mod Hp8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hleft Hrun").
    { iApply (uis_shp_826 with "Hcode"). }
    iIntros "Hleft" (h17) "Hrun".
    set (n1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int pl : mword 64)]> m12).
    assert (Hn1 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    n1 !!! Regidx r = m12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m12 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Ha0_n1 : n1 !!! Regidx a0_idx = mword_of_int pl)
      by exact (upd_eq m12 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int pl : mword 64))).
    (* ---- 0x828  jal ra,7ca <nulterminate> -- THE LEFT RECURSION ---- *)
    iApply (wp_uk_jal N h17 n1 (mword_of_int 0x828)
              (mword_of_int 2097058 : mword 21) ra_idx
              (mword_of_int 0x7ca) (mword_of_int 0x82c) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_828 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (n2 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x82c : mword 64)]> n1).
    assert (Hn2 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    n2 !!! Regidx r = n1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n1 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_n2 : n2 !!! Regidx a0_idx = mword_of_int pl)
      by (rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_n1).
    assert (Eret2 : ret_pc (n2 !!! Regidx ra_idx) = mword_of_int 0x82c);
      [ rewrite (upd_eq n1 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x82c : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    rewrite <- shpp_nulterminate.
    iApply (wp_kshp_nulterminate h18 n2 s0 pl len g toksl nn
              Ha0_n2 Hs0 Hs64 Hpl0 Hpl8 Hplsz Htlenl Hsndl
              with "Hcode Hro Hsubl Hline Hrun").
    iIntros "Hsubl Hline" (h19 mr) "%Hcsr %Ha0_r Hrun".
    rewrite Eret2.
    (* ---- 0x82c  c.ld a0,16(s1) -- pcmd->right ---- *)
    assert (Hs1_r : mr !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcsr s1_idx ltac:(vm_compute; reflexivity))
              (Hn2 s1_idx ltac:(vm_compute; discriminate))
              (Hn1 s1_idx ltac:(vm_compute; discriminate))
              (Hkeep12 s1_idx ltac:(vm_compute; reflexivity)). exact Hs1_3. }
    iApply (wp_uk_cld N h19 mr (mword_of_int 0x82c)
              (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 2 : mword 3) s1_idx a0_idx
              (p + 16) (mword_of_int pr) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_r (uint_moi p ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              ltac:(rewrite Zplus_mod Hp8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hright Hrun").
    { iApply (uis_shp_82c with "Hcode"). }
    iIntros "Hright" (h20) "Hrun".
    set (n3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int pr : mword 64)]> mr).
    assert (Hn3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    n3 !!! Regidx r = mr !!! Regidx r)
      by (intros r Hr; exact (upd_ne mr (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Ha0_n3 : n3 !!! Regidx a0_idx = mword_of_int pr)
      by exact (upd_eq mr (Regidx a0_idx)
                  (regval_into_reg (mword_of_int pr : mword 64))).
    (* ---- 0x82e  jal ra,7ca <nulterminate> -- THE RIGHT RECURSION ---- *)
    iApply (wp_uk_jal N h20 n3 (mword_of_int 0x82e)
              (mword_of_int 2097052 : mword 21) ra_idx
              (mword_of_int 0x7ca) (mword_of_int 0x832) (4 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_82e with "Hcode"). }
    iIntros (h21) "Hrun".
    set (n4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x832 : mword 64)]> n3).
    assert (Hn4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    n4 !!! Regidx r = n3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n3 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_n4 : n4 !!! Regidx a0_idx = mword_of_int pr)
      by (rewrite (Hn4 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_n3).
    assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x832);
      [ rewrite (upd_eq n3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x832 : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    rewrite <- shpp_nulterminate.
    iApply ("Hrcall" $! h21 n4 (ushp_nulfold toksl g)
              with "[] Hsubr Hline Hrun").
    { iPureIntro. exact Ha0_n4. }
    iIntros "Hsubr Hline" (h22 mr2) "%Hcsr2 %Ha0_r2 Hrun".
    rewrite Eret4.
    (* ---- 0x832  c.j 83e -- into the common tail ---- *)
    iApply (wp_uk_cj N h22 mr2 (mword_of_int 0x832)
              (mword_of_int 2036 : mword 11) (mword_of_int 0x81a) (4 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_832 with "Hcode"). }
    iIntros (h23) "Hrun".
    (* ---- 0x81a..0x824  the common tail, the EXEC arm's own ---- *)
    assert (Hs1_r2 : mr2 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcsr2 s1_idx ltac:(vm_compute; reflexivity))
              (Hn4 s1_idx ltac:(vm_compute; discriminate))
              (Hn3 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_r. }
    iApply (wp_kshp_nul_fin sp0 spl vals p (4 + nn) h23 mr2
              Hal8 Hlo ltac:(lia) Hsplu
              ltac:(rewrite (Hcsr2 csp_rs1 ltac:(vm_compute; reflexivity))
                      (Hn4 csp_rs1 ltac:(vm_compute; discriminate))
                      (Hn3 csp_rs1 ltac:(vm_compute; discriminate))
                      (Hcsr csp_rs1 ltac:(vm_compute; reflexivity))
                      (Hn2 csp_rs1 ltac:(vm_compute; discriminate))
                      (Hn1 csp_rs1 ltac:(vm_compute; discriminate))
                      (Hkeep12 csp_rs1 ltac:(vm_compute; reflexivity));
                    exact Hsp3)
              Hs1_r2
              with "Hcode Hsl Hloc Hrun").
    iIntros (hf) "Hrun".
    iApply ("Hcont" with
             "[Hty4 Hpad Hleft Hright] Hsubl Hsubr Hline [] [] Hrun").
    - rewrite /ushp_pipe_node.
      iSplitR; [ iPureIntro; exact Hnp | ].
      iSplitR; [ iPureIntro; exact Hna | ].
      iSplitR; [ iPureIntro; exact Hnz | ].
      iSplitL "Hty4 Hpad"; [ iSplitL "Hty4"; [ iExact "Hty4" |
                                               iExact "Hpad" ] | ].
      iFrame "Hleft Hright".
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals m
               (<[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> mr2)
               sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| i ]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (upd_ne mr2 (Regidx a0_idx) (Regidx r) _
                   (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
                (Hcsr2 r Hr)
                (Hn4 r (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                          eq_refl))
                (Hn3 r (ushp_cs_ne r a0_idx Hr
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
        exact (upd_eq mr2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| i ]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  (* ...AND THE LANDED ARM, BYTE-IDENTICAL: the right child an EXEC node,
     its call the landed EXEC walk. *)
  Lemma wp_kshp_nulterminate_pipe (h : CpuId) (m : regfile) (s0 p pl pr : Z)
      (len : nat) (g : nat -> bv 8) (toksl toksr : list (nat * nat))
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int p ->
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 40 < Z64 ->
    0 < pl -> pl mod 8 = 0 -> pl + 168 < Z64 ->
    0 < pr -> pr mod 8 = 0 -> pr + 168 < Z64 ->
    (length toksl < 10)%nat ->
    (length toksr < 10)%nat ->
    (forall (i : nat) (tk : nat * nat), toksl !! i = Some tk ->
       (fst tk <= len)%nat /\ (snd tk <= len)%nat) ->
    (forall (i : nat) (tk : nat * nat), toksr !! i = Some tk ->
       (fst tk <= len)%nat /\ (snd tk <= len)%nat) ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_pipe_node p pl pr -∗
    ushp_exec_at s0 pl toksl -∗
    ushp_exec_at s0 pr toksr -∗
    ubytes γd s0 (S len) g -∗
    urun N h m (mword_of_int ShSyms.nulterminate) (4 + (4 + nn)) -∗
    (ushp_pipe_node p pl pr -∗
     ushp_exec_at s0 pl toksl -∗
     ushp_exec_at s0 pr toksr -∗
     ubytes γd s0 (S len) (ushp_nulfold toksr (ushp_nulfold toksl g)) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (4 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Hs0 Hs64 Hp0 Hp8 Hpsz Hpl0 Hpl8 Hplsz Hpr0 Hpr8 Hprsz
      Htlenl Htlenr Hsndl Hsndr.
    iIntros "#Hcode #Hro Hn Hsubl Hsubr Hline Hrun Hcont".
    iApply (wp_kshp_nulterminate_pipe_g h m s0 p pl pr len g toksl
              (ushp_exec_at s0 pr toksr) (ushp_nulfold toksr) nn
              Ha0 Hs0 Hs64 Hp0 Hp8 Hpsz Hpl0 Hpl8 Hplsz Htlenl Hsndl
              with "Hcode Hro Hn Hsubl Hsubr Hline Hrun [] Hcont").
    iIntros (h1 m1 g1) "%Ha0' Hsubr Hline Hrun Hk".
    iApply (wp_kshp_nulterminate h1 m1 s0 pr len g1 toksr nn
              Ha0' Hs0 Hs64 Hpr0 Hpr8 Hprsz Htlenr Hsndr
              with "Hcode Hro Hsubr Hline Hrun Hk").
  Qed.

End UkShPipeParse.
