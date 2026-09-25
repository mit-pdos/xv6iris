(* ===================================================================== *)
(* UkShPipeCmd.v -- pipecmd, lane SH-PARSE-PIPE part 3.                   *)
(*                                                                        *)
(*   struct cmd * pipecmd(struct cmd *left, struct cmd *right) {          *)
(*     struct pipecmd *cmd = malloc(sizeof( *cmd ));                        *)
(*     memset(cmd, 0, sizeof( *cmd ));                                      *)
(*     cmd->type = PIPE; cmd->left = left; cmd->right = right;            *)
(*     return (struct cmd * )cmd; }                 (user/sh.c:228)       *)
(*                                                                        *)
(* TWENTY-SEVEN INSTRUCTIONS, 0x260..0x29c, and they are in the catalog    *)
(* only as of this lane: [tools/ucode_shp.txt] carried `skipfunc pipecmd`  *)
(* -- reached only from parsepipe's peek arm for the bar, which            *)
(* [ushp_no_symbols] refutes -- and now carries `func pipecmd`, as SH-PARSE *)
(* turned [redircmd] from one into the other.  A coverage change is an     *)
(* edit to the SPEC and never to the output, so the regenerated            *)
(* [iris/UCodeShP.v] (603 -> 630 instruction facts, 12 -> 13 functions) is *)
(* committed with it, and [shp_syms_pins] gains a thirteenth conjunct --   *)
(* which is why the eleven [destruct shp_syms_pins] patterns in            *)
(* [UkShParse.v] each gained one `_` and [UkShParse.shpp_pipecmd] is new.  *)
(*                                                                        *)
(* The walk is [UkShRedirCmd.wp_kshp_redircmd_n]'s, one size smaller: a    *)
(* SIX-word frame with five spills (redircmd's is eight with eight),       *)
(* [malloc(24)] rather than 40, and THREE field stores rather than seven   *)
(* -- the type word at 0, the left child at 8, the right child at 16.  The *)
(* NULL arm is redircmd's verbatim in shape: [pipecmd] does not test       *)
(* malloc's answer either, so [memset(0, 0, 24)] faults and the child dies *)
(* on its exit payload.                                                    *)
(*                                                                        *)
(* Its answer is [UkShPipeParse.ushp_pipe_node] -- the node with BOTH      *)
(* child pointers NAMED -- and the two subtrees ride through in an         *)
(* abstract [Sub], because everything from here to the parser theorem      *)
(* relays the node and its children SEPARATELY (SH-PARSE-2's shape fact).  *)
(* This is exactly [UkShPipeCm.ushq_pipecmd_call]'s shape, which is what   *)
(* the turn takes as its second premise.                                   *)
(* ===================================================================== *)
(* [malloc] through the one named Hypothesis [ushp_malloc_ok], [memset]    *)
(* across the [shp_code]/[shk_code] bridge -- and then SEVEN field stores  *)
(* instead of one.  The frame is eight words rather than four because five *)
(* arguments have to survive the two calls, and it is [gettoken]'s frame   *)
(* instruction for instruction, so [wp_kshp_frame_pro] / [_epi] drive both *)
(* ends and nothing here is hand-stepped but the body.                     *)
(*                                                                        *)
(* THE NULL ARM IS execcmd's TOO: [redircmd] does not test [malloc]'s      *)
(* answer either, so a failed allocation walks into [memset(0, 0, 40)],    *)
(* whose first store faults on sh's own read-only first text byte and      *)
(* kills the process.  That branch spends the exit payload and has no      *)
(* continuation.                                                           *)
(*                                                                        *)
(* TAINT: [ushp_malloc_ok], and nothing else.                              *)
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
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Require Import UserFd.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseLex.
Require Import UkShPipeParse.
Require Import UexecSG.
Import Defs.

Section UkShPipeCmd.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
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

  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_peel0 := (UkShParse.ushp_peel0 N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation ushp_ubytes_ext := (UkShParse.ushp_ubytes_ext N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).

  (* the capability is stated at [B = 168] like every other parser file's,
     even though the call below asks for 24 (lane SH-MALLOC-3: one bound,
     no weakening lemma anywhere). *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  Lemma wp_kshp_pipecmd {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (pl pr : Z) (Sub : iProp Σ) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int pl ->
    m !!! Regidx a1_idx = mword_of_int pr ->
    shp_code γt -∗
    UMalloc -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    Sub -∗
    urun N h m (mword_of_int ShSyms.pipecmd) (6 + (10 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile) (t : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
       ⌜ 0 < t /\ t mod 16 = 0 /\ t + 24 < 2 ^ 38 ⌝ -∗
       UkShPipeParse.ushp_pipe_node N t pl pr -∗
       Sub -∗
       UMalloc' -∗
       Pex -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (6 + (10 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1.
    iIntros "#Hcode HM #Hpx Hpay Hsub Hrun Hcont".
    iDestruct (ushp_code_shk γt with "Hcode") as "#Hkcode".
    rewrite UkShParse.shpp_pipecmd.
    set (rs := [(ra_idx, mword_of_int 5 : mword 6);
                (s0_idx, mword_of_int 4 : mword 6);
                (s1_idx, mword_of_int 3 : mword 6);
                (s2_idx, mword_of_int 2 : mword 6);
                (s3_idx, mword_of_int 1 : mword 6)]).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | _ => m !!! Regidx s3_idx end).
    (* ---- 0x260..0x26c  the prologue: k = 6, FIVE spills and one pad ---- *)
    iApply (wp_kshp_frame_pro 6 1 rs 0x260
              (fun i : nat => match i with
                              | 0%nat => 0x262 | 1%nat => 0x264
                              | 2%nat => 0x266 | 3%nat => 0x268
                              | 4%nat => 0x26a | _ => 0x26c end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (10 + nn) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_260 with "Hcode"). }
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_262 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_264 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_266 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_268 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_26a with "Hcode") | done ]. }
    { iApply (uis_shp_26c with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x26e  c.mv s2,a0  --  left ---- *)
    iApply (wp_uk_cmv N h1 m2 (mword_of_int 0x26e) s2_idx a0_idx
              (mword_of_int pl) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val pl))
              with "[] Hrun").
    { iApply (uis_shp_26e with "Hcode"). }
    rewrite (ushp_pc_step 0x26e 2). iIntros (h2) "Hrun".
    set (m3 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int pl : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
                    m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s2_idx) (Regidx r) _ Hr)).
    (* ---- 0x270  c.mv s3,a1  --  right ---- *)
    iApply (wp_uk_cmv N h2 m3 (mword_of_int 0x270) s3_idx a1_idx
              (mword_of_int pr) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val pr))
              with "[] Hrun").
    { iApply (uis_shp_270 with "Hcode"). }
    rewrite (ushp_pc_step 0x270 2). iIntros (h3) "Hrun".
    set (m4 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int pr : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx s3_idx) (Regidx r) _ Hr)).
    (* ---- 0x272  c.li a0,24 ---- *)
    assert (E24 : (sign_extend' 64 (mword_of_int 24 : mword 6) : mword 64)
                  = mword_of_int 24)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli N h3 m4 (mword_of_int 0x272)
              (mword_of_int 24 : mword 6) a0_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_272 with "Hcode"). }
    rewrite (ushp_pc_step 0x272 2). iIntros (h4) "Hrun".
    set (m5 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 24 : mword 6)
                       : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x274  jal 118c <malloc> ---- *)
    iApply (wp_uk_jal N h4 m5 (mword_of_int 0x274)
              (mword_of_int 3872 : mword 21) ra_idx
              (mword_of_int 0x1194) (mword_of_int 0x278) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_274 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x278 : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx = mword_of_int 24).
    { rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m4 (Regidx a0_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 24 : mword 6)
                     : mword 64))). exact E24. }
    assert (Eret1 : ret_pc (m6 !!! Regidx ra_idx) = mword_of_int 0x278).
    { rewrite (upd_eq m5 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x278 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- UkShParseLex.shpp_malloc.
    (* ---- malloc(24) -- THE HYPOTHESIS, and this lemma's only taint ---- *)
    iApply (ushp_malloc_ok h5 m6 24 nn Ha0_6 ltac:(lia) ltac:(lia)
              with "Hcode HM Hrun").
    iIntros (h6 m7) "%Hcs67 Hans Hrun".
    rewrite Eret1.
    iDestruct "Hans" as
      "[%Ha0_7 | (%t & %g & %Ha0_7 & %Htb & Hbs & HM')]".
    { (* ---- THE NULL ARM: memset(0, 0, 24) faults and the child dies -- *)
      iApply (wp_uk_cmv N h6 m7 (mword_of_int 0x278) s1_idx a0_idx
                (mword_of_int 0) (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_7; symmetry; exact (ushp_mv_val 0))
                with "[] Hrun").
      { iApply (uis_shp_278 with "Hcode"). }
      rewrite (ushp_pc_step 0x278 2). iIntros (h7) "Hrun".
      set (n1 := <[Regidx s1_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> m7).
      assert (Hn1 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                      n1 !!! Regidx r = m7 !!! Regidx r)
        by (intros r Hr; exact (upd_ne m7 (Regidx s1_idx) (Regidx r) _ Hr)).
      iApply (wp_uk_cli N h7 n1 (mword_of_int 0x27a)
                (mword_of_int 24 : mword 6) a2_idx (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_27a with "Hcode"). }
      rewrite (ushp_pc_step 0x27a 2). iIntros (h8) "Hrun".
      set (n2 := <[Regidx a2_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 24 : mword 6)
                         : mword 64)]> n1).
      assert (Hn2 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                      n2 !!! Regidx r = n1 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n1 (Regidx a2_idx) (Regidx r) _ Hr)).
      iApply (wp_uk_cli N h8 n2 (mword_of_int 0x27c)
                (mword_of_int 0 : mword 6) a1_idx (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_27c with "Hcode"). }
      rewrite (ushp_pc_step 0x27c 2). iIntros (h9) "Hrun".
      set (n3 := <[Regidx a1_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)]> n2).
      assert (Hn3 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                      n3 !!! Regidx r = n2 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n2 (Regidx a1_idx) (Regidx r) _ Hr)).
      iApply (wp_uk_jal N h9 n3 (mword_of_int 0x27e)
                (mword_of_int 2014 : mword 21) ra_idx
                (mword_of_int 0xa5c) (mword_of_int 0x282) (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_27e with "Hcode"). }
      iIntros (h10) "Hrun".
      set (n4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x282 : mword 64)]> n3).
      assert (Hn4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                      n4 !!! Regidx r = n3 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n3 (Regidx ra_idx) (Regidx r) _ Hr)).
      assert (Hna0 : n4 !!! Regidx a0_idx = mword_of_int 0).
      { rewrite (Hn4 a0_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn3 a0_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_7. }
      assert (Hna2 : n4 !!! Regidx a2_idx = mword_of_int (Z.of_nat 24)).
      { rewrite (Hn4 a2_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn3 a2_idx ltac:(vm_compute; discriminate)).
        rewrite (upd_eq n1 (Regidx a2_idx)
                   (regval_into_reg
                      (sign_extend' 64 (mword_of_int 24 : mword 6)
                       : mword 64))).
        rewrite E24. now f_equal. }
      rewrite <- UkShParseLex.shpp_memset.
      iDestruct (ush_text0 γt with "Hkcode") as (btx) "#Ht0".
      iApply (wp_ksh_memset_null N h10 n4 0 24%nat btx (8 + nn)
                ltac:(lia) ltac:(vm_compute; reflexivity)
                Hna0 Hna2 ltac:(lia) ltac:(unfold Z31; lia)
                with "Hkcode Ht0 [Hpay] Hrun").
      iApply ("Hpx" with "Hpay"). }
    destruct Htb as [ Ht0 [ Ht16 Htsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Ht64 : 0 <= t < Z64)
      by (rewrite H38 in Htsz; unfold Z64; lia).
    assert (Ht8 : t mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 t); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Ht16 ]. }
    assert (Ht4 : t mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 t); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Ht8 ]. }
    assert (E24n : Z.to_nat 24 = 24%nat) by (vm_compute; reflexivity).
    rewrite E24n.
    (* ---- 0x278  c.mv s1,a0  --  cmd ---- *)
    iApply (wp_uk_cmv N h6 m7 (mword_of_int 0x278) s1_idx a0_idx
              (mword_of_int t) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_7; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_278 with "Hcode"). }
    rewrite (ushp_pc_step 0x278 2). iIntros (h7) "Hrun".
    set (m8 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> m7).
    assert (Hm8 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                    m8 !!! Regidx r = m7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m7 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hs1_8 : m8 !!! Regidx s1_idx = mword_of_int t)
      by exact (upd_eq m7 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int t : mword 64))).
    (* ---- 0x27a  c.li a2,24 ---- *)
    iApply (wp_uk_cli N h7 m8 (mword_of_int 0x27a)
              (mword_of_int 24 : mword 6) a2_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_27a with "Hcode"). }
    rewrite (ushp_pc_step 0x27a 2). iIntros (h8) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 24 : mword 6)
                       : mword 64)]> m8).
    assert (Hm9 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m9 !!! Regidx r = m8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m8 (Regidx a2_idx) (Regidx r) _ Hr)).
    (* ---- 0x27c  c.li a1,0 ---- *)
    iApply (wp_uk_cli N h8 m9 (mword_of_int 0x27c)
              (mword_of_int 0 : mword 6) a1_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_27c with "Hcode"). }
    rewrite (ushp_pc_step 0x27c 2). iIntros (h9) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 0 : mword 6)
                        : mword 64)]> m9).
    assert (Hm10 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                     m10 !!! Regidx r = m9 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m9 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Ha1_10 : m10 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite (upd_eq m9 (Regidx a1_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6)
                     : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x27e  jal a5c <memset> ---- *)
    iApply (wp_uk_jal N h9 m10 (mword_of_int 0x27e)
              (mword_of_int 2014 : mword 21) ra_idx
              (mword_of_int 0xa5c) (mword_of_int 0x282) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_27e with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m11 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x282 : mword 64)]> m10).
    assert (Hm11 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                     m11 !!! Regidx r = m10 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m10 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_11 : m11 !!! Regidx a0_idx = mword_of_int t).
    { rewrite (Hm11 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm10 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm9 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_7. }
    assert (Ha2_11 : m11 !!! Regidx a2_idx = mword_of_int (Z.of_nat 24)).
    { rewrite (Hm11 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m8 (Regidx a2_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 24 : mword 6)
                     : mword 64))).
      rewrite E24. now f_equal. }
    assert (Ha1_11 : m11 !!! Regidx a1_idx = (mword_of_int 0 : mword 64))
      by (rewrite (Hm11 a1_idx ltac:(vm_compute; discriminate)); exact Ha1_10).
    assert (Eret2 : ret_pc (m11 !!! Regidx ra_idx) = mword_of_int 0x282).
    { rewrite (upd_eq m10 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x282 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- UkShParseLex.shpp_memset.
    (* ---- memset(cmd, 0, 24) -- UkSh.v's, across the code bridge ---- *)
    iApply (wp_ksh_memset N h10 m11 t 24%nat g (8 + nn)
              Ha0_11 Ha2_11 ltac:(lia) ltac:(unfold Z31; lia)
              with "Hkcode Hbs Hrun").
    iIntros "Hbs" (h11 m12) "%Hcs1112 Hrun".
    rewrite Eret2 Ha1_11.
    assert (Eb0 : nth_byte (mword_of_int 0 : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    rewrite Eb0.
    (* ---- the node's four slices ---- *)
    iDestruct (ushp_peel0 t (t + 4) 4 20 ltac:(lia) with "Hbs")
      as "[Hty Hbs]".
    iDestruct (ushp_peel0 (t + 4) (t + 8) 4 16 ltac:(lia) with "Hbs")
      as "[Hpad Hbs]".
    iDestruct (ushp_peel0 (t + 8) (t + 16) 8 8 ltac:(lia) with "Hbs")
      as "[Hleft Hright]".
    iAssert (uword γd (t + 8) (mword_of_int 0)) with "[Hleft]" as "Hleft".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (t + 8) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hleft").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iAssert (uword γd (t + 16) (mword_of_int 0)) with "[Hright]" as "Hright".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (t + 16) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hright").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    (* ---- 0x282  c.li a5,3 ---- *)
    iApply (wp_uk_cli N h11 m12 (mword_of_int 0x282)
              (mword_of_int 3 : mword 6) a5_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_282 with "Hcode"). }
    rewrite (ushp_pc_step 0x282 2). iIntros (h12) "Hrun".
    set (m13 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 3 : mword 6)
                        : mword 64)]> m12).
    assert (Hm13 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                     m13 !!! Regidx r = m12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m12 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha5_13 : m13 !!! Regidx a5_idx = (mword_of_int 3 : mword 64)).
    { rewrite (upd_eq m12 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 3 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* the three registers the stores read *)
    assert (Hs1_13 : m13 !!! Regidx s1_idx = mword_of_int t).
    { rewrite (Hm13 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1112 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm11 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm10 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_8. }
    assert (Hs2_13 : m13 !!! Regidx s2_idx = mword_of_int pl).
    { rewrite (Hm13 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1112 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm11 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs67 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s2_idx)
               (regval_into_reg (mword_of_int pl : mword 64))). }
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int pr).
    { rewrite (Hm13 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1112 s3_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm11 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm10 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm9 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs67 s3_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm6 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s3_idx)
               (regval_into_reg (mword_of_int pr : mword 64))). }
    (* ---- 0x284  c.sw a5,0(s1)  --  cmd->type = PIPE ---- *)
    iApply (wp_uk_csw N h12 m13 (mword_of_int 0x284)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 7 : mword 3) s1_idx a5_idx t
              (mword_of_int 0 : mword 64) (10 + nn)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_13 (uint_moi t Ht64);
                    vm_compute uoff_c4; lia)
              Ht4
              with "[] [Hty] Hrun").
    { iApply (uis_shp_284 with "Hcode"). }
    { iApply (ushp_ubytes_ext t 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hty").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hty". rewrite Ha5_13.
    rewrite (ushp_pc_step 0x284 2). iIntros (h13) "Hrun".
    (* ---- 0x286  sd s2,8(s1)  --  cmd->left = left ---- *)
    iApply (wp_uk_sd N h13 m13 (mword_of_int 0x286)
              (mword_of_int 8 : mword 12) s1_idx s2_idx (t + 8)
              (mword_of_int 0) (10 + nn)
              ltac:(rewrite Hs1_13 (uint_moi t Ht64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Ht8;
                    reflexivity)
              with "[] Hleft Hrun").
    { iApply (uis_shp_286 with "Hcode"). }
    iIntros "Hleft". rewrite Hs2_13.
    rewrite (ushp_pc_step 0x286 4). iIntros (h14) "Hrun".
    (* ---- 0x28a  sd s3,16(s1)  --  cmd->right = right ---- *)
    iApply (wp_uk_sd N h14 m13 (mword_of_int 0x28a)
              (mword_of_int 16 : mword 12) s1_idx s3_idx (t + 16)
              (mword_of_int 0) (10 + nn)
              ltac:(rewrite Hs1_13 (uint_moi t Ht64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Ht8;
                    reflexivity)
              with "[] Hright Hrun").
    { iApply (uis_shp_28a with "Hcode"). }
    iIntros "Hright". rewrite Hs3_13.
    rewrite (ushp_pc_step 0x28a 4). iIntros (h15) "Hrun".
    (* ---- 0x28e  c.mv a0,s1  --  return cmd ---- *)
    iApply (wp_uk_cmv N h15 m13 (mword_of_int 0x28e) a0_idx
              s1_idx (mword_of_int t) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_13; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_28e with "Hcode"). }
    rewrite (ushp_pc_step 0x28e 2). iIntros (h16) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> m13).
    assert (Hme : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    me !!! Regidx r = m13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m13 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm13 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs1112 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm11 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm10 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs67 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0x290..0x29c  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 1 rs (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x290 | 1%nat => 0x292
                              | 2%nat => 0x294 | 3%nat => 0x296
                              | 4%nat => 0x298 | _ => 0x29a end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 5)) vals
              (10 + nn) h16 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
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
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_290 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_292 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_294 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_296 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_298 with "Hcode") | done ]. }
    { iApply (uis_shp_29a with "Hcode"). }
    { iApply (uis_shp_29c with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! hf _ t with "[] [] [] [Hty Hpad Hleft Hright] Hsub HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs rs vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (Hme r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm13 r (ushp_cs_ne r a5_idx Hr
                           ltac:(vm_compute; reflexivity))).
        rewrite (Hcs1112 r Hr).
        rewrite (Hm11 r (Hmiss 0%nat ra_idx (mword_of_int 5 : mword 6)
                           eq_refl)).
        rewrite (Hm10 r (ushp_cs_ne r a1_idx Hr
                           ltac:(vm_compute; reflexivity))).
        rewrite (Hm9 r (ushp_cs_ne r a2_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm8 r (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6)
                          eq_refl)).
        rewrite (Hcs67 r Hr).
        rewrite (Hm6 r (Hmiss 0%nat ra_idx (mword_of_int 5 : mword 6)
                          eq_refl)).
        rewrite (Hm5 r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm4 r (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6)
                          eq_refl)).
        rewrite (Hm3 r (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6)
                          eq_refl)).
        rewrite (Hm2 r (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6)
                          eq_refl)).
        exact (Hm1 r Hrsp).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m13 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int t : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| i ]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
    - iPureIntro. exact (conj Ht0 (conj Ht16 Htsz)).
    - rewrite /UkShPipeParse.ushp_pipe_node.
      iSplitR; [ iPureIntro; exact Ht0 | ].
      iSplitR; [ iPureIntro; exact Ht8 | ].
      iSplitR; [ iPureIntro; rewrite H38 in Htsz; unfold Z64; lia | ].
      iSplitL "Hty Hpad".
      + iSplitL "Hty".
        * iApply (ushp_ubytes_ext t 4
                    (nth_byte (mword_of_int 3 : mword 64))
                    (nth_byte (mword_of_int 3 : mword 32)) with "Hty").
          intros j Hj. destruct j as [| [| [| [| j ]]]];
            [ vm_compute; reflexivity | vm_compute; reflexivity
            | vm_compute; reflexivity | vm_compute; reflexivity | lia ].
        * iExists (fun _ : nat => ubyte0). iExact "Hpad".
      + iFrame "Hleft Hright".
  Qed.

End UkShPipeCmd.
