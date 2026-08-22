(* ProofMemcpy.v -- the whole-function WP for xv6's memcpy(), over the
   SIE-agnostic sconf world.

     void *memcpy(void *dst, const void *src, uint n)

   Contract: SpecMemcpy.v.  Nine instructions, a 2-slot ra/s0 frame, ONE callee.

   memcpy is a pure shim onto memmove -- the twenty bytes are

     +0x00  c.addi   sp,sp,-16      \
     +0x02  c.sdsp   ra,8(sp)        |  the standard 2-slot frame
     +0x04  c.sdsp   s0,0(sp)        |
     +0x06  c.addi4spn s0,sp,16     /
     +0x08  jal      ra,<memmove>      a0/a1/a2 are passed through UNTOUCHED
     +0x0c  c.ldsp   ra,8(sp)       \
     +0x0e  c.ldsp   s0,0(sp)        |  tear it down
     +0x10  c.addi   sp,sp,16        |
     +0x12  c.jr     ra             /

   -- note in particular that nothing writes a0 after the call, so memmove's
   return value (the destination pointer) IS memcpy's.  The proof therefore
   consumes the MEMMOVE module type and its contract is memmove's restated;
   the only arithmetic anywhere in the file is the frame's, and the only
   bookkeeping is threading [callee_saved] through the call.

   EXPLICIT-CPUID: the whole function threads a generic [b : bool].
   [mcp_tail] is a non-recursive fragment of the whole-function contract, so
   it takes its own leading (shadowing) hart [`{CID0 : CpuId}`] and its
   continuation is [wp_next]-wrapped; the caller peels a fresh [(CIDk, Hsk)]
   off its result exactly as for a leaf application. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import HartTp WpNext IntrDefs.
Require Import CodeMemcpy.
Require Import SpecMemmove.
Require Import SpecMemcpy.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module MemcpyProof (MM : MEMMOVE) : MEMCPY.

Section ProofMemcpy.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* the source's and the destination's own tiers -- see SpecMemmove.v's note *)
  Context {kts ktw : ktier}.
  Context `{!KtierLe kts kt} `{!KtierLe ktw kt}.
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Local Lemma cs_ne (k r : mword 5) :
    is_cs_idx k = false -> is_cs_idx r = true -> Regidx r <> Regidx k.
  Proof. intros Hk Hr He. symmetry in He. exact (is_cs_idx_true_neq k r Hk Hr He). Qed.

  Local Lemma mcp_push (X : mword 64) :
    add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk X 2.
  Proof. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

  (* ---- the epilogue, +0x0c .. +0x12 --------------------------------- *)
  Local Lemma mcp_tail `{CID0 : CpuId}
      (mm Mt : regfile) (K : nat) (rv sp0 ra0 s00 : mword 64) (b : bool) (p : mword 64) :
    (2 <= K)%nat ->
    mm !!! Regidx csp_rs1 = sp0 ->
    mm !!! Regidx Rra = ra0 ->
    mm !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        Mt !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr kt (CID := CID0) Mt (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.memcpy + 0x0c) : mword 64) -∗
    word_pointsto (KTR := kt) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := kt) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved mm mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr kt mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hcont".
    (* ---- +0x0c: c.ldsp ra,8(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memcpy + 0x0c))
              (mword_of_int 1 : mword 6) Rra Mt (K - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (mcpi_0c with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.memcpy + 0x0c) : mword 64) 2
                   = mword_of_int (KernelSyms.memcpy + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x0e: c.ldsp s0,0(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memcpy + 0x0e))
              (mword_of_int 0 : mword 6) Rs0 T1 (K - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (mcpi_0e with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.memcpy + 0x0e) : mword 64) 2
                   = mword_of_int (KernelSyms.memcpy + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x10: c.addi sp,16 ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_16).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv; exact HT2sp).
    iDestruct (stack_own_2_intro sp0 ra0 s00 with "Hb1 Hb2") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.memcpy + 0x10))
              (mword_of_int 16 : mword 6) T2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (mcpi_10 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T2 !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2) with T3.
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.memcpy + 0x10) : mword 64) 2
                   = mword_of_int (KernelSyms.memcpy + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* ---- +0x12: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    assert (HT3ra' : forall CID' : CpuId, rget (CID := CID') T3 Rra = ra0)
      by (intros CID'; rgne; exact HT3ra).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.memcpy + 0x12)) Rra T3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (mcpi_12 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rewrite HT3ra') in "Hpc".
    (* ---- postcondition ---- *)
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hgen : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                     T3 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /T3 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T1 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc").
    split; [| exact HT3a0].
    unfold callee_saved. split_and!.
    - rewrite /T3 upd_eq Hwv. symmetry. exact Hsp0.
    - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. symmetry. exact Hs00.
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                  *)
  (* =================================================================== *)
  Lemma wp_memcpy_sconf
      (m0 : regfile) (n : nat) (len : nat) (src_bytes dst_olds : nat -> bv 8) (b : bool) (p : mword 64)
    : wp_memcpy_sconf_body kt kts ktw m0 n len src_bytes dst_olds b p.
  Proof.
    cbv beta delta [wp_memcpy_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p_dst p_src ret_tgt Hn Hlen32 Ha2.
    pose (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    (* ---- +0x00: c.addi sp,-16 ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m0 n 2 b
              ltac:(lia) (mcp_push (m0 !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (mcpi_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m0 !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m0).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (m0 !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m0) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R1 upd_eq; apply mcp_push).
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.memcpy + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (u1 u2) "[Hb1 Hb2]".
    assert (Hpa1 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memcpy + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (n - 2)%nat u1 b
              with "Hcg Hpc [] [Hb1]").
    { iApply (mcpi_02 with "Htext"). }
    { iEval (rewrite Hpa1). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    assert (HR1ra : R1 !!! Regidx Rra = m0 !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1ra' : forall CID' : CpuId, rget (CID := CID') R1 Rra = m0 !!! Regidx Rra)
      by (intros CID'; rgne; exact HR1ra).
    iEval (rewrite HR1ra') in "Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.memcpy + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.memcpy + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (kt := kt) (ktd := kt) (mword_of_int (KernelSyms.memcpy + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (n - 2)%nat u2 b
              with "Hcg Hpc [] [Hb2]").
    { iApply (mcpi_04 with "Htext"). }
    { iEval (rewrite Hpa2). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = m0 !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0' : forall CID' : CpuId, rget (CID := CID') R1 Rs0 = m0 !!! Regidx Rs0)
      by (intros CID'; rgne; exact HR1s0).
    iEval (rewrite HR1s0') in "Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.memcpy + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.memcpy + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.memcpy + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0 R1 (n - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (mcpi_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
               (add_vec (R1 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1) with R2.
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.memcpy + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.memcpy + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* ---- +0x08: jal ra,<memmove> ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.memcpy + 0x08)) Rra
              (mword_of_int 2097048 : mword 21) R2 (n - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (mcpi_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.memcpy + 0x08) : mword 64) 4)]> R2).
    change (<[Regidx Rra := regval_into_reg
               (add_vec_int (mword_of_int (KernelSyms.memcpy + 0x08) : mword 64) 4)]> R2) with R3.
    assert (Htgt : add_vec (mword_of_int (KernelSyms.memcpy + 0x08) : mword 64)
                     (sign_extend' 64 (mword_of_int 2097048 : mword 21))
                   = mword_of_int KernelSyms.memmove)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    (* the entry map for the callee *)
    assert (HR3a0 : R3 !!! Regidx Ra0 = p_dst).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR3a1 : R3 !!! Regidx Ra1 = p_src).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR3a2 : R3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat len) : mword 64)).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [exact Ha2 | reg_neq]. }
    assert (HR3ra : R3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.memcpy + 0x08) : mword 64) 4)
      by (rewrite /R3; apply upd_eq).
    assert (HR3sp : R3 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq]. exact HR1sp. }
    assert (HR3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                       R3 !!! Regidx r = m0 !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /R3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
      rewrite /R2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /R1 upd_ne; [reflexivity | intro He; injection He as He'; congruence]. }
    assert (HKmm : (2 <= n - 2)%nat) by lia.
    iEval (rewrite -HR3a1) in "Hsrc".
    iEval (rewrite -HR3a0) in "Hdst".
    iApply (MM.wp_memmove_sconf kt kts ktw R3 (n - 2)%nat len src_bytes dst_olds (DfracOwn 1) b p
              HKmm Hlen32 HR3a2
              with "Hcg Htext Hpc Hsrc Hdst").
    iIntros (CID6 Hs6 mM) "Hcg Hpc Hsrc Hdst %HmMa0 %HcsM".
    (* memmove returns to memcpy+0x0c *)
    assert (Hpcret : ret_pc (R3 !!! Regidx Rra : mword 64)
                     = mword_of_int (KernelSyms.memcpy + 0x0c))
      by (rewrite HR3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcret) in "Hpc".
    iEval (rewrite HR3a1) in "Hsrc".
    iEval (rewrite HR3a0) in "Hdst".
    (* ---- +0x0c .. +0x12: the epilogue ---- *)
    assert (HmMa0' : mM !!! Regidx Ra0 = p_dst) by (rewrite HmMa0; exact HR3a0).
    assert (HmMsp : mM !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite (callee_saved_lookup HcsM csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR3sp. }
    assert (HmMthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                       mM !!! Regidx r = m0 !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite (callee_saved_lookup HcsM r Hr). exact (HR3thr r Hr Ncsp Ns0). }
    iApply (mcp_tail m0 mM n p_dst sp0 (m0 !!! Regidx Rra) (m0 !!! Regidx Rs0) b p
              ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
              HmMsp HmMa0' HmMthr
              with "Hcg Htext Hpc Hb1 Hb2").
    iIntros (CID7 Hs7 mf) "[%Hcs %Hfa0] Hcg Hpc".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "Hcg Hpc Hsrc Hdst [%] [%]").
    - exact Hfa0.
    - exact Hcs.
  Qed.

End ProofMemcpy.

End MemcpyProof.
