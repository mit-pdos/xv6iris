(* ===================================================================== *)
(* UkShPipeCmd.v -- pipecmd, lane SH-PARSE-PIPE part 3.                   *)
(*                                                                        *)
(*   struct cmd * pipecmd(struct cmd *left, struct cmd *right) {          *)
(*     struct pipecmd *cmd = cmdalloc(sizeof( *cmd ));                      *)
(*     cmd->type = PIPE; cmd->left = left; cmd->right = right;            *)
(*     return (struct cmd * )cmd; }                 (user/sh.c)           *)
(*                                                                        *)
(* FIFTEEN INSTRUCTIONS, 0x272..0x29c.  It entered the catalog with lane   *)
(* SH-PARSE-PIPE: [tools/ucode_shp.txt] carried `skipfunc pipecmd` --      *)
(* reached only from parsepipe's peek arm for the bar, which               *)
(* [ushp_no_symbols] refutes -- and now carries `func pipecmd`.            *)
(*                                                                        *)
(* The walk is [UkShRedirCmd.wp_kshp_redircmd_n]'s, one size smaller: a    *)
(* FOUR-word frame with four spills, pushed with [c.addi sp,sp,-32]        *)
(* ([wp_kshp_frame_pro_ci]), [cmdalloc(24)] rather than 40, and THREE      *)
(* field stores -- the type word at 0, the left child at 8, the right      *)
(* child at 16.  The NULL arm is [cmdalloc]'s: [panic("out of memory")],   *)
(* handed to the caller's law [UkShCmdalloc.ushp_oom].                     *)
(*                                                                        *)
(* Its answer is [UkShPipeNode.ushp_pipe_node] -- the node with BOTH      *)
(* child pointers NAMED -- and the two subtrees ride through in an         *)
(* abstract [Sub], because everything from here to the parser theorem      *)
(* relays the node and its children SEPARATELY (SH-PARSE-2's shape fact).  *)
(* This is exactly [UkShPipeCm.ushq_pipecmd_call]'s shape, which is what   *)
(* the turn takes as its second premise.                                   *)
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
Require UkShCmdalloc.
Require Import UkShPipeNode.
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

  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).
  Local Notation wp_kshp_cmdalloc :=
    (UkShCmdalloc.wp_kshp_cmdalloc N UMalloc UMalloc' ushp_malloc_ok).
  Local Notation wp_kshp_frame_pro_ci := (UkShParse.wp_kshp_frame_pro_ci N).

  Lemma wp_kshp_pipecmd {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (pl pr : Z) (Sub : iProp Σ) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int pl ->
    m !!! Regidx a1_idx = mword_of_int pr ->
    shp_code γt -∗
    UMalloc -∗
    ushp_oom Pex (10 + nn) -∗
    Pex -∗
    Sub -∗
    urun N h m (mword_of_int ShSyms.pipecmd) (4 + (4 + (10 + nn))) -∗
    (∀ (h' : CpuId) (m' : regfile) (t : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
       ⌜ 0 < t /\ t mod 16 = 0 /\ t + 24 < 2 ^ 38 ⌝ -∗
       UkShPipeNode.ushp_pipe_node N t pl pr -∗
       Sub -∗
       UMalloc' -∗
       Pex -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (4 + (10 + nn))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1.
    iIntros "#Hcode HM #Hoom Hpay Hsub Hrun Hcont".
    rewrite UkShParse.shpp_pipecmd.
    set (rs := [(ra_idx, mword_of_int 3 : mword 6);
                (s0_idx, mword_of_int 2 : mword 6);
                (s1_idx, mword_of_int 1 : mword 6);
                (s2_idx, mword_of_int 0 : mword 6)]).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | _ => m !!! Regidx s2_idx end).
    (* ---- 0x272..0x27c  the prologue: k = 4, four spills, no pad ---- *)
    iApply (wp_kshp_frame_pro_ci 4 0 rs 0x272
              (fun i : nat => match i with
                              | 0%nat => 0x274 | 1%nat => 0x276
                              | 2%nat => 0x278 | 3%nat => 0x27a | _ => 0x27c end)
              (mword_of_int 32 : mword 6) (mword_of_int 8 : mword 8)
              vals (4 + (10 + nn)) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| i ]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_272 with "Hcode"). }
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_274 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_276 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_278 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_27a with "Hcode") | done ]. }
    { iApply (uis_shp_27c with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 4))).
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
    (* ---- 0x27e  c.mv s1,a0  --  left ---- *)
    iApply (wp_uk_cmv N h1 m2 (mword_of_int 0x27e) s1_idx a0_idx
              (mword_of_int pl) (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val pl))
              with "[] Hrun").
    { iApply (uis_shp_27e with "Hcode"). }
    rewrite (ushp_pc_step 0x27e 2). iIntros (h2) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int pl : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                    m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s1_idx) (Regidx r) _ Hr)).
    (* ---- 0x280  c.mv s2,a1  --  right ---- *)
    iApply (wp_uk_cmv N h2 m3 (mword_of_int 0x280) s2_idx a1_idx
              (mword_of_int pr) (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val pr))
              with "[] Hrun").
    { iApply (uis_shp_280 with "Hcode"). }
    rewrite (ushp_pc_step 0x280 2). iIntros (h3) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int pr : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx s2_idx) (Regidx r) _ Hr)).
    (* ---- 0x282  c.li a0,24 ---- *)
    assert (E24 : (sign_extend' 64 (mword_of_int 24 : mword 6) : mword 64)
                  = mword_of_int 24)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli N h3 m4 (mword_of_int 0x282)
              (mword_of_int 24 : mword 6) a0_idx (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_282 with "Hcode"). }
    rewrite (ushp_pc_step 0x282 2). iIntros (h4) "Hrun".
    set (m5 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 24 : mword 6)
                       : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x284  jal 1d2 <cmdalloc> ---- *)
    iApply (wp_uk_jal N h4 m5 (mword_of_int 0x284)
              (mword_of_int 2096974 : mword 21) ra_idx
              (mword_of_int 0x1d2) (mword_of_int 0x288) (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_284 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x288 : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx = mword_of_int 24).
    { rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m4 (Regidx a0_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 24 : mword 6)
                     : mword 64))). exact E24. }
    assert (Eret1 : ret_pc (m6 !!! Regidx ra_idx) = mword_of_int 0x288).
    { rewrite (upd_eq m5 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x288 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- UkShParse.shpp_cmdalloc.
    (* ---- cmdalloc(24) ---- *)
    iApply (wp_kshp_cmdalloc h5 m6 24 nn Ha0_6 ltac:(lia) ltac:(lia)
              with "Hcode HM Hoom Hpay Hrun").
    iIntros (h6 m7 t) "%Hcs67 %Ha0_7 %Htb Hbs HM' Hpay Hrun".
    rewrite Eret1.
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
    (* ---- 0x288  c.li a4,3 ---- *)
    iApply (wp_uk_cli N h6 m7 (mword_of_int 0x288)
              (mword_of_int 3 : mword 6) a4_idx (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_288 with "Hcode"). }
    rewrite (ushp_pc_step 0x288 2). iIntros (h7) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 3 : mword 6)
                       : mword 64)]> m7).
    assert (Hm8 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                    m8 !!! Regidx r = m7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m7 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (Ha4_8 : m8 !!! Regidx a4_idx = (mword_of_int 3 : mword 64)).
    { rewrite (upd_eq m7 (Regidx a4_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 3 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_8 : m8 !!! Regidx a0_idx = mword_of_int t)
      by (rewrite (Hm8 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_7).
    (* the two registers the stores read, across cmdalloc *)
    assert (Hs1_8 : m8 !!! Regidx s1_idx = mword_of_int pl).
    { rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs67 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm6 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s1_idx)
               (regval_into_reg (mword_of_int pl : mword 64))). }
    assert (Hs2_8 : m8 !!! Regidx s2_idx = mword_of_int pr).
    { rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs67 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s2_idx)
               (regval_into_reg (mword_of_int pr : mword 64))). }
    (* ---- 0x28a  c.sw a4,0(a0)  --  cmd->type = PIPE ---- *)
    iApply (wp_uk_csw N h7 m8 (mword_of_int 0x28a)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx t
              (mword_of_int 0 : mword 64) (4 + (10 + nn))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_8 (uint_moi t Ht64);
                    vm_compute uoff_c4; lia)
              Ht4
              with "[] [Hty] Hrun").
    { iApply (uis_shp_28a with "Hcode"). }
    { iApply (ushp_ubytes_ext t 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hty").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hty". rewrite Ha4_8.
    rewrite (ushp_pc_step 0x28a 2). iIntros (h8) "Hrun".
    (* ---- 0x28c  c.sd s1,8(a0)  --  cmd->left = left ---- *)
    iApply (wp_uk_csd N h8 m8 (mword_of_int 0x28c)
              (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx (t + 8)
              (mword_of_int 0) (4 + (10 + nn))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_8 (uint_moi t Ht64);
                    vm_compute uoff_c8; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Ht8;
                    reflexivity)
              with "[] Hleft Hrun").
    { iApply (uis_shp_28c with "Hcode"). }
    iIntros "Hleft". rewrite Hs1_8.
    rewrite (ushp_pc_step 0x28c 2). iIntros (h9) "Hrun".
    (* ---- 0x28e  sd s2,16(a0)  --  cmd->right = right ---- *)
    iApply (wp_uk_sd N h9 m8 (mword_of_int 0x28e)
              (mword_of_int 16 : mword 12) a0_idx s2_idx (t + 16)
              (mword_of_int 0) (4 + (10 + nn))
              ltac:(rewrite Ha0_8 (uint_moi t Ht64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Ht8;
                    reflexivity)
              with "[] Hright Hrun").
    { iApply (uis_shp_28e with "Hcode"). }
    iIntros "Hright". rewrite Hs2_8.
    rewrite (ushp_pc_step 0x28e 4). iIntros (h10) "Hrun".
    assert (Hspe : m8 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs67 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0x292..0x29c  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 4 0 rs (mword_of_int 3 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x292 | 1%nat => 0x294
                              | 2%nat => 0x296 | 3%nat => 0x298 | _ => 0x29a end)
              (mword_of_int 2 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 4)) vals
              (4 + (10 + nn)) h10 m8
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| i ]]]];
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
      iSplit; [ iApply (uis_shp_292 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_294 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_296 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_298 with "Hcode") | done ]. }
    { iApply (uis_shp_29a with "Hcode"). }
    { iApply (uis_shp_29c with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! hf _ t with "[] [] [] [Hty Hpad Hleft Hright] Hsub HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs rs vals m m8 sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| i ]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (Hm8 r (ushp_cs_ne r a4_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hcs67 r Hr).
        rewrite (Hm6 r (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                          eq_refl)).
        rewrite (Hm5 r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm4 r (Hmiss 3%nat s2_idx (mword_of_int 0 : mword 6)
                          eq_refl)).
        rewrite (Hm3 r (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6)
                          eq_refl)).
        rewrite (Hm2 r (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6)
                          eq_refl)).
        exact (Hm1 r Hrsp).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _. exact Ha0_8.
      + intros i r u Hi He.
        destruct i as [| [| [| [| i ]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
    - iPureIntro. exact (conj Ht0 (conj Ht16 Htsz)).
    - rewrite /UkShPipeNode.ushp_pipe_node.
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
