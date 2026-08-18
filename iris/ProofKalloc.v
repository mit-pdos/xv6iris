(* ProofKalloc.v -- kalloc over the SIE-agnostic sconf world (kalloc cone,
   stage 8).  The sconf mirror of [wp_kalloc] (WpKalloc.v): acquire -> load
   freelist head -> branch (empty: reclose+release+return null; nonempty:
   pop+release+memset(p,5,4096)+return p).  Both arms thread the counting
   token [intr_count] NET-ZERO (acquire n->S n, release S n->n).  sp moves
   only at prologue/epilogue (4-slot frame, 3 saves + padding), traded
   through sie_cap push/pop 4 (the avail param drops K -> K-4 across the
   body; the sub-calls carve their own frames from the threaded sie_cap
   avail); memset (nonempty arm, AFTER release, at the ambient level) runs
   SIE-blind via MemsetPage.wp_memset_page_sconf. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv CodeKalloc.
Require Import WpLock.
Require Import VcGen.
Require Import WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import SpecMemsetPage SpecAcquire SpecRelease.
Require Import SpecKalloc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.


Module KallocProof (Acquire : ACQUIRE) (MemsetPage : MEMSETPAGE) (Release : RELEASE) : KALLOC.

Section ProofKalloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Context {kt : ktier}.
  Lemma wp_kalloc_sconf
      (γl : gname) (γk : gname * gname) (fl : mword 64)
      (m : regfile)
      (on : option nat) (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool) (lks : gset string)
    : wp_kalloc_sconf_body kt γl γk fl m on n eb p K b lks.
  Proof.
    cbv beta delta [wp_kalloc_sconf_body].
    intros pcE ret_tgt HK Hfl Hnoffpos Hfresh.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hlock Havail Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbmatch. symmetry in Hbmatch.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (kai_00 with "Htext") as "Hi00".
    iPoseProof (kai_02 with "Htext") as "Hi02".
    iPoseProof (kai_04 with "Htext") as "Hi04".
    iPoseProof (kai_06 with "Htext") as "Hi06".
    iPoseProof (kai_08 with "Htext") as "Hi08".
    iPoseProof (kai_0a with "Htext") as "Hi0a".
    iPoseProof (kai_0e with "Htext") as "Hi0e".
    iPoseProof (kai_12 with "Htext") as "Hi12".
    (* ===== PROLOGUE: 4-slot frame trade + 3 saves (ra/s0/s1) + padding ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hsp1 : R1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite /R1 upd_eq. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* +0x00 c.addi sp,-32 -- the frame trade (push k := 4) *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 Hr24").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 Hr16").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 Hr8").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (Hra0v : m !!! Regidx (mword_of_int 1 : mword 5) = R1 !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kalloc + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kalloc + 0x0a)) (mword_of_int 10 : mword 5) (mword_of_int 0x12 : mword 20)
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kalloc + 0x0a) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> R2).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x0a) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e addi a0,a0,2046  (a0 := &kmem) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kalloc + 0x0e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x8be : mword 12)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2238 : mword 12)))]> R3).
    iEval (rgne) in "Hcg".
    assert (HR4a0 : R4 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /R4 upd_eq. rewrite /R3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== ACQUIRE call (intr_count n -> S n, deep-10 lent) ===== *)
    (* +0x12 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kalloc + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0xc8 : mword 21)
              R4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (mA := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kalloc + 0x12) : mword 64) 4)]> R4).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.kalloc + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0xc8 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /mA upd_ne; [| vm_compute; discriminate]. exact HR4a0. }
    assert (HmAra : mA !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.kalloc + 0x12) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    (* [Hcnt] was introduced at the function's ENTRY hart; the eight plain
       instructions above each moved to a FRESH hart (CID1..CID8), so
       acquire wants it at CID8. *)
    iDestruct (cpu_own_transport CID CID8 n eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf kt γl "kmem"%string (kmem_res γk fl) mA
              n eb p (K - 4)%nat b lks
              Hnoffpos
              ltac:(lia)
              Hfresh
              with "Hcg Hcnt Htext Hpc [Hlock]").
    all: try lkbelow.
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc16 : ret_pc (mA !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kalloc + 0x16)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc16) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    iPoseProof (kai_16 with "Htext") as "Hi16".
    iPoseProof (kai_1a with "Htext") as "Hi1a".
    iPoseProof (kai_1e with "Htext") as "Hi1e".
    (* ===== +0x16 auipc s1,0x12 ; +0x1a ld s1,head ; +0x1e beqz s1 ===== *)
    (* +0x16 auipc s1,0x12 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kalloc + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 0x12 : mword 20)
              macq (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (R6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kalloc + 0x16) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> macq).
    assert (Hs1R6 : R6 !!! Regidx (mword_of_int 9 : mword 5) = add_vec (mword_of_int (KernelSyms.kalloc + 0x16) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))
      by (rewrite /R6; apply upd_eq).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a ld s1,-2038(s1) : s1 := head *)
    iDestruct "HRres" as (head pages) "(Hflw & Hchain & Hauth)".
    assert (Hldaddr : add_vec (R6 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x8ca : mword 12)) = fl).
    { rewrite Hs1R6 Hfl. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.kalloc + 0x1a)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0x8ca : mword 12)
              R6 (trap_res b + (K - 4))%nat head false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [Hflw]").
    { iEval (rewrite -Hldaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hflw".
    iEval (rewrite Hldaddr) in "Hflw".
    set (R7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg head]> R6).
    assert (Hs1R7 : R7 !!! Regidx (mword_of_int 9 : mword 5) = head) by (rewrite /R7; apply upd_eq).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* map facts threaded to both release calls *)
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr) by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    (* +0x1e c.beqz s1,+0x4c : head=nullp -> empty ; else pop *)
    destruct pages as [|pg ps].
    - (* ===== EMPTY: head=nullp, taken to +0x4c ===== *)
      iDestruct "Hchain" as %Hhead.
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.kalloc + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 (trap_res b + (K - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hs1R7 Hhead; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1e").
      iApply wp_next_off_intro.
      iNext. iIntros "Hcg Hpc".
      assert (Htgtbeq : add_vec (mword_of_int (KernelSyms.kalloc + 0x1e) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.kalloc + 0x4c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtbeq) in "Hpc".
      (* the empty list pins the caller's count (if any) to 0 *)
      iDestruct (kalloc_avail_zero γk on with "Havail Hauth") as %Hzero.
      iAssert (kmem_res γk fl) with "[Hflw Hauth]" as "HRres".
      { iApply (kmem_res_close γk fl head []). rewrite /word_at.
        iFrame "Hflw Hauth". iPureIntro. exact Hhead. }
      iPoseProof (kai_4c with "Htext") as "Hi4c".
      iPoseProof (kai_50 with "Htext") as "Hi50".
      iPoseProof (kai_54 with "Htext") as "Hi54".
      (* +0x4c auipc a0,0x12 *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kalloc + 0x4c)) (mword_of_int 10 : mword 5) (mword_of_int 0x12 : mword 20)
                R7 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4c").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kalloc + 0x4c) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> R7).
      assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* +0x50 addi a0,a0,1980  (a0 := &kmem) *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kalloc + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x87c : mword 12)
                E1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi50").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (E1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2172 : mword 12)))]> E1).
      assert (Ha0kmem2 : E2 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /E2 upd_eq /E1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 jal ra,release *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kalloc + 0x54)) (mword_of_int 1 : mword 5) (mword_of_int 0x10e : mword 21)
                E2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi54").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kalloc + 0x54) : mword 64) 4)]> E2).
      assert (Htgtr2 : add_vec (mword_of_int (KernelSyms.kalloc + 0x54) : mword 64) (sign_extend' 64 (mword_of_int 0x10e : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtr2) in "Hpc".
      assert (HE3csp : E3 !!! Regidx csp_rs1 = spr).
      { rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1 upd_ne; [| vm_compute; discriminate].
        rewrite /R7 upd_ne; [| vm_compute; discriminate].
        rewrite /R6 upd_ne; [| vm_compute; discriminate].
        exact Hmsp. }
      assert (HE3a0 : E3 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /E3 upd_ne; [| vm_compute; discriminate]. exact Ha0kmem2. }
      assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.kalloc + 0x54) : mword 64) 4)
        by (rewrite /E3; apply upd_eq).
      (* the acquire handed the window index out as [trap_res b + N]; release
         wants it as [trap_res outb + N] with [outb = match n with O => eb
         | S _ => false end].  Those are the same bool -- [cpu_own] forces
         it -- so this is a pure re-spelling, and it is what makes the
         acquire/release pair compose back to [N]. *)
      iEval (rewrite Hbmatch) in "Hcg".
      iApply (Release.wp_release_sconf kt γl (mword_of_int KernelSyms.kmem) "kmem"%string (kmem_res γk fl) E3
                n eb p (K - 4)%nat ({["kmem"]} ∪ lks)
                ltac:(rewrite HE3a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
      { iExact "Hlock". }
      rewrite -Hbmatch.
      iIntros (CIDrel Hsrel mr0) "Hcg Hpc %Hrelpins Hcnt".
      rename mr0 into mr.
      pose proof (locks_below_not_elem _ _ Hfresh) as Hfresh_ne.
      iEval (rewrite (_ : ({["kmem"]} ∪ lks) ∖ {["kmem"]} = lks);
             [| apply locks_add_del_below; lkbelow]) in "Hcnt".
      assert (Hpc58 : ret_pc (E3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kalloc + 0x58)).
      { rewrite HE3ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc58) in "Hpc".
      pose proof Hrelpins as Hrelpins_cs.
      unfold callee_saved in Hrelpins.
      destruct Hrelpins as (Hmrcsp & Hmrs0 & Hmrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (HE3s1 : E3 !!! Regidx (mword_of_int 9 : mword 5) = nullp).
      { rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1 upd_ne; [| vm_compute; discriminate].
        rewrite Hs1R7. exact Hhead. }
      iPoseProof (kai_58 with "Htext") as "Hi58".
      iPoseProof (kai_40 with "Htext") as "Hi40".
      iPoseProof (kai_42 with "Htext") as "Hi42".
      iPoseProof (kai_44 with "Htext") as "Hi44".
      iPoseProof (kai_46 with "Htext") as "Hi46".
      iPoseProof (kai_48 with "Htext") as "Hi48".
      iPoseProof (kai_4a with "Htext") as "Hi4a".
      (* +0x58 c.j +0x40 *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.kalloc + 0x58))
                (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                mr (K - 4)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi58").
      iIntros (CIDe1 Hse1).
      iNext. iIntros "Hcg Hpc".
      assert (Htgtj : add_vec (mword_of_int (KernelSyms.kalloc + 0x58) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.kalloc + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtj) in "Hpc".
      (* +0x40 c.mv a0,s1  (a0 := s1 = nullp) *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kalloc + 0x40)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mr (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi40").
      iIntros (CIDe2 Hse2) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (P41 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mr !!! Regidx (mword_of_int 9 : mword 5)))]> mr).
      assert (HspP41 : P41 !!! Regidx csp_rs1 = spr).
      { rewrite /P41 upd_ne; [| vm_compute; discriminate].
        rewrite Hmrcsp HE3csp. reflexivity. }
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16". iEval (rewrite HspR1) in "Hr8". iEval (rewrite HspR1) in "Hg4".
      (* +0x42 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                P41 (K - 4)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42 [Hr24]").
      { iEval (rewrite HspP41). iExact "Hr24". }
      iIntros (CIDe3 Hse3) "Hcg Hpc Hr24".
      iEval (rewrite HspP41) in "Hr24".
      set (P42 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> P41).
      assert (HspP42 : P42 !!! Regidx csp_rs1 = spr) by (rewrite /P42 upd_ne; [ exact HspP41 | vm_compute; discriminate ]).
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x44)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                P42 (K - 4)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi44 [Hr16]").
      { iEval (rewrite HspP42). iExact "Hr16". }
      iIntros (CIDe4 Hse4) "Hcg Hpc Hr16".
      iEval (rewrite HspP42) in "Hr16".
      set (P43 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> P42).
      assert (HspP43 : P43 !!! Regidx csp_rs1 = spr) by (rewrite /P43 upd_ne; [ exact HspP42 | vm_compute; discriminate ]).
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                P43 (K - 4)%nat (R1 !!! Regidx (mword_of_int 9 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi46 [Hr8]").
      { iEval (rewrite HspP43). iExact "Hr8". }
      iIntros (CIDe5 Hse5) "Hcg Hpc Hr8".
      iEval (rewrite HspP43) in "Hr8".
      set (P44 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> P43).
      assert (HspP44 : P44 !!! Regidx csp_rs1 = spr) by (rewrite /P44 upd_ne; [ exact HspP43 | vm_compute; discriminate ]).
      assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* +0x48 c.addi16sp sp,32 -- the frame trade back (pop 4) *)
      set (P45 := <[Regidx csp_rs1 := regval_into_reg (add_vec (P44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P44).
      assert (HP45csp : P45 !!! Regidx csp_rs1 = sp0).
      { rewrite /P45 upd_eq. rewrite HspP44. unfold spr, sp0. apply frame_cancel_32. }
      assert (Hwv : add_vec (P44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HspP44. unfold spr, sp0. apply frame_cancel_32. }
      assert (Hpop : P44 !!! Regidx csp_rs1 = pa_stk (add_vec (P44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HspP44. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iAssert (stack_own (KTR := kt) sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
      { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
        iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
        iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
        iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
        iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.kalloc + 0x48)) (mword_of_int 2 : mword 6) P44 (K - 4)%nat 4 b Hpop
                with "Hcg Hpc Hi48 Hframe4").
      iIntros (CIDe6 Hse6) "Hcg Hpc".
      assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (P44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P44) with P45.
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a c.ret *)
      assert (HP45ra : P45 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /P45 upd_ne; [| vm_compute; discriminate].
        rewrite /P44 upd_ne; [| vm_compute; discriminate].
        rewrite /P43 upd_ne; [| vm_compute; discriminate].
        rewrite /P42 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HP45a0 : P45 !!! Regidx (mword_of_int 10 : mword 5) = nullp).
      { rewrite /P45 upd_ne; [| vm_compute; discriminate].
        rewrite /P44 upd_ne; [| vm_compute; discriminate].
        rewrite /P43 upd_ne; [| vm_compute; discriminate].
        rewrite /P42 upd_ne; [| vm_compute; discriminate].
        rewrite /P41 upd_eq.
        rewrite Hmrs1 HE3s1. apply add_vec_zero_l. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kalloc + 0x4a)) (mword_of_int 1 : mword 5) P45 K b
                ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi4a").
      iIntros (CIDe7 Hse7) "Hcg Hpc".
      assert (Hretf : ret_pc (P45 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
        by (rewrite HP45ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDrel CIDe7 n eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDe7 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! P45 with "Hcg Hcnt Hpc [%] [Havail]").
      { (* callee_saved m P45 *)
        assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                  c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                  c <> mword_of_int 9 -> c <> mword_of_int 10 ->
                  P45 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N1 N2 N8 N9 N10.
          let peel := (repeat (rewrite upd_ne; [ | congruence ])) in
          rewrite /P45 /P44 /P43 /P42 /P41; peel;
          rewrite (callee_saved_lookup Hrelpins_cs c Hcs);
          rewrite /E3 /E2 /E1 /R7 /R6; peel;
          rewrite (callee_saved_lookup Hacqpins_cs c Hcs);
          rewrite /mA /R4 /R3 /R2 /R1; peel;
          reflexivity. }
        unfold callee_saved.
        split.
        { rewrite /P45 upd_eq.
          assert (HP44csp : P44 !!! Regidx csp_rs1 = spr) by exact HspP44.
          rewrite HP44csp. unfold regval_into_reg, spr. apply frame_cancel_32. }
        split.
        { rewrite /P45 upd_ne; [| vm_compute; discriminate].
          rewrite /P44 upd_ne; [| vm_compute; discriminate].
          rewrite /P43 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        split.
        { rewrite /P45 upd_ne; [| vm_compute; discriminate].
          rewrite /P44 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      { rewrite /kalloc_post. iLeft. iFrame "Havail".
        iSplit; iPureIntro; [exact HP45a0 | exact Hzero]. }
    - (* ===== NONEMPTY: head=pg, pop + release + memset(p,5,4096) ===== *)
      iDestruct "Hchain" as "(-> & %Hpv & Hrun)".
      iDestruct "Hrun" as (nxt) "[Hrun Hchain]".
      (* the pop's ghost step: count S (length ps) -> length ps *)
      iEval (cbn [length]) in "Hauth".
      iMod (kmem_avail_dec γk on (length ps) with "Havail Hauth") as "[Havail Hauth]".
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.kalloc + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 (trap_res b + (K - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hs1R7; apply eq_vec_false_iff; intro Hpz;
                      apply (page_valid_ne_null pg Hpv); rewrite Hpz; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi1e").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rewrite /run_page) in "Hrun".
      iDestruct "Hrun" as "[Hpnext Hprest]".
      iPoseProof (kai_20 with "Htext") as "Hi20".
      iPoseProof (kai_22 with "Htext") as "Hi22".
      iPoseProof (kai_26 with "Htext") as "Hi26".
      (* +0x20 c.ld a5,0(s1) : a5 := nxt *)
      assert (Hpaddr : add_vec (R7 !!! Regidx (mword_of_int 9 : mword 5))
                 (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = pg).
      { replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hs1R7. apply kv_addv_zero. }
      iApply (wp_cld_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.kalloc + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
                R7 (trap_res b + (K - 4))%nat nxt false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi20 [Hpnext]").
      { iEval (rewrite Hpaddr). rewrite /word_at. iExact "Hpnext". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hpnext".
      iEval (rewrite Hpaddr) in "Hpnext".
      set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg nxt]> R7).
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 auipc a4,0x12 *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kalloc + 0x22)) (mword_of_int 14 : mword 5) (mword_of_int 0x12 : mword 20)
                R8 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (R9 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kalloc + 0x22) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> R8).
      assert (Ha4R9 : R9 !!! Regidx (mword_of_int 14 : mword 5) = add_vec (mword_of_int (KernelSyms.kalloc + 0x22) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))
        by (rewrite /R9; apply upd_eq).
      assert (Ha5R9 : R9 !!! Regidx (mword_of_int 15 : mword 5) = nxt).
      { rewrite /R9 upd_ne; [| vm_compute; discriminate]. rewrite /R8; apply upd_eq. }
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 sd a5,2046(a4) : kmem.freelist := nxt *)
      assert (Hstaddr : add_vec (R9 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 0x8be : mword 12)) = fl).
      { rewrite Ha4R9 Hfl. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_sd_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (KernelSyms.kalloc + 0x26)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0x8be : mword 12)
                R9 (trap_res b + (K - 4))%nat pg false with "Hcg Hpc Hi26 [Hflw]").
      { iEval (rewrite -Hstaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hflw".
      iEval (repeat rgne) in "Hflw".
      iEval (rewrite Ha5R9) in "Hflw". iEval (rewrite Hstaddr) in "Hflw".
      iAssert (kmem_res γk fl) with "[Hflw Hchain Hauth]" as "HRres".
      { iApply (kmem_res_close γk fl nxt ps). rewrite /word_at. iFrame "Hflw Hchain Hauth". }
      iAssert (page_own pg) with "[Hpnext Hprest]" as "Hpage".
      { iApply (run_page_page_own pg nxt). rewrite /run_page /word_at. iFrame "Hpnext Hprest". }
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iPoseProof (kai_2a with "Htext") as "Hi2a".
      iPoseProof (kai_2e with "Htext") as "Hi2e".
      (* +0x2a auipc a0,0x12 ; +0x2e addi a0,a0,2000 (a0 := &kmem) *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kalloc + 0x2a)) (mword_of_int 10 : mword 5) (mword_of_int 0x12 : mword 20)
                R9 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (R10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kalloc + 0x2a) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> R9).
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kalloc + 0x2e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x89e : mword 12)
                R10 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2e").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (R11 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R10 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2206 : mword 12)))]> R10).
      assert (Ha0kmem : R11 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R11 upd_eq /R10 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.kalloc + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      iPoseProof (kai_32 with "Htext") as "Hi32".
      (* +0x32 jal ra,release *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kalloc + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 0x130 : mword 21)
                R11 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi32").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (R12 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kalloc + 0x32) : mword 64) 4)]> R11).
      assert (Htgtr : add_vec (mword_of_int (KernelSyms.kalloc + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 0x130 : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtr) in "Hpc".
      assert (HR12csp : R12 !!! Regidx csp_rs1 = spr).
      { rewrite /R12 /R11 /R10 /R9 /R8 /R7 /R6;
        repeat (rewrite upd_ne; [| vm_compute; discriminate]); exact Hmsp. }
      assert (HR12a0 : R12 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R12 upd_ne; [| vm_compute; discriminate]. exact Ha0kmem. }
      assert (HR12ra : R12 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.kalloc + 0x32) : mword 64) 4)
        by (rewrite /R12; apply upd_eq).
      assert (HR12s1 : R12 !!! Regidx (mword_of_int 9 : mword 5) = pg).
      (* [repeat (rewrite upd_ne; …)] here costs ~6 s: R7 -- one layer below
         the five named above -- is itself an s1 (reg 9) write, so once the
         five real peels are done, [repeat]'s next iteration DOES unify
         [upd_ne] against R7 (its `set` body deltas open to `<[Regidx 9 :=
         head]> R6`), only to land the false side goal [Regidx 9 <> Regidx 9]
         that [vm_compute; discriminate] then fails to close.  Contrast
         [HR12csp] two asserts up: its peel also ends with a spurious
         [repeat] iteration, but at [macq], an opaque `iIntros`-bound
         variable with no `set` body to delta into, so the extra attempt
         fails to even unify and costs nothing.  [do 5] stops at exactly the
         five real peels [Hs1R7] is already stated over, so the goal never
         reaches R7 and [repeat]'s expensive misfire never fires. *)
      { rewrite /R12 /R11 /R10 /R9 /R8;
        do 5 (rewrite upd_ne; [| vm_compute; discriminate]); exact Hs1R7. }
      (* the acquire handed the window index out as [trap_res b + N]; release
         wants it as [trap_res outb + N] with [outb = match n with O => eb
         | S _ => false end].  Those are the same bool -- [cpu_own] forces
         it -- so this is a pure re-spelling, and it is what makes the
         acquire/release pair compose back to [N]. *)
      iEval (rewrite Hbmatch) in "Hcg".
      iApply (Release.wp_release_sconf kt γl (mword_of_int KernelSyms.kmem) "kmem"%string (kmem_res γk fl) R12
                n eb p (K - 4)%nat ({["kmem"]} ∪ lks)
                ltac:(rewrite HR12a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
      { iExact "Hlock". }
      rewrite -Hbmatch.
      iIntros (CIDrel Hsrel mr0) "Hcg Hpc %Hrelpins Hcnt".
      rename mr0 into mr.
      pose proof (locks_below_not_elem _ _ Hfresh) as Hfresh_ne.
      iEval (rewrite (_ : ({["kmem"]} ∪ lks) ∖ {["kmem"]} = lks);
             [| apply locks_add_del_below; lkbelow]) in "Hcnt".
      assert (Hpc36 : ret_pc (R12 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kalloc + 0x36)).
      { rewrite HR12ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc36) in "Hpc".
      pose proof Hrelpins as Hrelpins_cs.
      unfold callee_saved in Hrelpins.
      destruct Hrelpins as (Hmrcsp & Hmrs0 & Hmrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      iPoseProof (kai_36 with "Htext") as "Hi36".
      iPoseProof (kai_38 with "Htext") as "Hi38".
      iPoseProof (kai_3a with "Htext") as "Hi3a".
      (* +0x36 c.lui a2,0x1 (a2:=4096) *)
      iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.kalloc + 0x36)) (mword_of_int 12 : mword 5)
                (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
                mr (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(unfold luival; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi36").
      iIntros (CIDf1 Hsf1) "Hcg Hpc".
      set (Mlui := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> mr).
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.li a1,5 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kalloc + 0x38)) (mword_of_int 11 : mword 5)
                (mword_of_int 5 : mword 6) (mword_of_int 5 : mword 64)
                Mlui (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi38").
      iIntros (CIDf2 Hsf2) "Hcg Hpc".
      set (Mli := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 5 : mword 64)]> Mlui).
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.mv a0,s1 (a0 := p) *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kalloc + 0x3a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                Mli (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3a").
      iIntros (CIDf3 Hsf3) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (M3a := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Mli !!! Regidx (mword_of_int 9 : mword 5)))]> Mli).
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      iPoseProof (kai_3c with "Htext") as "Hi3c".
      (* +0x3c jal ra,memset *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kalloc + 0x3c)) (mword_of_int 1 : mword 5) (mword_of_int 0x15e : mword 21)
                M3a (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3c").
      iIntros (CIDf4 Hsf4) "Hcg Hpc".
      set (Mms := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kalloc + 0x3c) : mword 64) 4)]> M3a).
      assert (Htgtms : add_vec (mword_of_int (KernelSyms.kalloc + 0x3c) : mword 64) (sign_extend' 64 (mword_of_int 0x15e : mword 21)) = mword_of_int KernelSyms.memset)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtms) in "Hpc".
      assert (HMmsa0 : Mms !!! Regidx (mword_of_int 10 : mword 5) = pg).
      { rewrite /Mms upd_ne; [| vm_compute; discriminate].
        rewrite /M3a upd_eq.
        rewrite /Mli upd_ne; [| vm_compute; discriminate].
        rewrite /Mlui upd_ne; [| vm_compute; discriminate].
        rewrite Hmrs1 HR12s1. apply add_vec_zero_l. }
      assert (HMmss1 : Mms !!! Regidx (mword_of_int 9 : mword 5) = pg).
      { rewrite /Mms upd_ne; [| vm_compute; discriminate].
        rewrite /M3a upd_ne; [| vm_compute; discriminate].
        rewrite /Mli upd_ne; [| vm_compute; discriminate].
        rewrite /Mlui upd_ne; [| vm_compute; discriminate].
        rewrite Hmrs1. exact HR12s1. }
      assert (HMmsa1 : Mms !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 5 : mword 64)).
      { rewrite /Mms upd_ne; [| vm_compute; discriminate].
        rewrite /M3a upd_ne; [| vm_compute; discriminate].
        rewrite /Mli upd_eq. reflexivity. }
      assert (HMmsa2 : Mms !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int 4096 : mword 64)).
      { rewrite /Mms upd_ne; [| vm_compute; discriminate].
        rewrite /M3a upd_ne; [| vm_compute; discriminate].
        rewrite /Mli upd_ne; [| vm_compute; discriminate].
        rewrite /Mlui upd_eq. reflexivity. }
      assert (HMmsra : Mms !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.kalloc + 0x40)).
      { rewrite /Mms upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HMmssp : Mms !!! Regidx csp_rs1 = spr).
      { rewrite /Mms upd_ne; [| vm_compute; discriminate].
        rewrite /M3a upd_ne; [| vm_compute; discriminate].
        rewrite /Mli upd_ne; [| vm_compute; discriminate].
        rewrite /Mlui upd_ne; [| vm_compute; discriminate].
        rewrite Hmrcsp. exact HR12csp. }
      iApply (MemsetPage.wp_memset_page_sconf kt Mms (K - 4)%nat (mword_of_int 5 : mword 64) b p
                ltac:(lia)
                ltac:(rewrite HMmsa0; exact Hpv) HMmsa1 HMmsa2
                with "Hcg Htext Hpc [Hpage]").
      { iEval (rewrite HMmsa0). iExact "Hpage". }
      iIntros (CIDms Hsms mfp) "Hcg Hpc Hpage %Hpinsf".
      iEval (rewrite HMmsa0) in "Hpage".
      pose proof Hpinsf as Hpinsf_cs.
      unfold callee_saved in Hpinsf.
      destruct Hpinsf as (Hfsp & Hfs0 & Hfs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (Hpc40 : ret_pc (Mms !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kalloc + 0x40)).
      { rewrite HMmsra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc40) in "Hpc".
      assert (Hmfsp : mfp !!! Regidx csp_rs1 = spr) by (rewrite Hfsp HMmssp; reflexivity).
      iPoseProof (kai_40 with "Htext") as "Hi40".
      iPoseProof (kai_42 with "Htext") as "Hi42".
      iPoseProof (kai_44 with "Htext") as "Hi44".
      iPoseProof (kai_46 with "Htext") as "Hi46".
      iPoseProof (kai_48 with "Htext") as "Hi48".
      iPoseProof (kai_4a with "Htext") as "Hi4a".
      (* +0x40 c.mv a0,s1 (a0 := p) *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kalloc + 0x40)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mfp (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi40").
      iIntros (CIDg1 Hsg1) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (Q41 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp).
      assert (HspQ41 : Q41 !!! Regidx csp_rs1 = spr) by (rewrite /Q41 upd_ne; [ exact Hmfsp | vm_compute; discriminate ]).
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16". iEval (rewrite HspR1) in "Hr8". iEval (rewrite HspR1) in "Hg4".
      (* +0x42 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                Q41 (K - 4)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42 [Hr24]").
      { iEval (rewrite HspQ41). iExact "Hr24". }
      iIntros (CIDg2 Hsg2) "Hcg Hpc Hr24".
      iEval (rewrite HspQ41) in "Hr24".
      set (Q42 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> Q41).
      assert (HspQ42 : Q42 !!! Regidx csp_rs1 = spr) by (rewrite /Q42 upd_ne; [ exact HspQ41 | vm_compute; discriminate ]).
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x44)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                Q42 (K - 4)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi44 [Hr16]").
      { iEval (rewrite HspQ42). iExact "Hr16". }
      iIntros (CIDg3 Hsg3) "Hcg Hpc Hr16".
      iEval (rewrite HspQ42) in "Hr16".
      set (Q43 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q42).
      assert (HspQ43 : Q43 !!! Regidx csp_rs1 = spr) by (rewrite /Q43 upd_ne; [ exact HspQ42 | vm_compute; discriminate ]).
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kalloc + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                Q43 (K - 4)%nat (R1 !!! Regidx (mword_of_int 9 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi46 [Hr8]").
      { iEval (rewrite HspQ43). iExact "Hr8". }
      iIntros (CIDg4 Hsg4) "Hcg Hpc Hr8".
      iEval (rewrite HspQ43) in "Hr8".
      set (Q44 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q43).
      assert (HspQ44 : Q44 !!! Regidx csp_rs1 = spr) by (rewrite /Q44 upd_ne; [ exact HspQ43 | vm_compute; discriminate ]).
      assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* +0x48 c.addi16sp sp,32 -- the frame trade back (pop 4) *)
      set (Q45 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q44).
      assert (HQ45csp : Q45 !!! Regidx csp_rs1 = sp0).
      { rewrite /Q45 upd_eq. rewrite HspQ44. unfold spr, sp0. apply frame_cancel_32. }
      assert (Hwv : add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HspQ44. unfold spr, sp0. apply frame_cancel_32. }
      assert (Hpop : Q44 !!! Regidx csp_rs1 = pa_stk (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HspQ44. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iAssert (stack_own (KTR := kt) sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
      { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
        iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
        iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
        iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
        iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.kalloc + 0x48)) (mword_of_int 2 : mword 6) Q44 (K - 4)%nat 4 b Hpop
                with "Hcg Hpc Hi48 Hframe4").
      iIntros (CIDg5 Hsg5) "Hcg Hpc".
      assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q44) with Q45.
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.kalloc + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.kalloc + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a c.ret *)
      assert (HQ45ra : Q45 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Q45 upd_ne; [| vm_compute; discriminate].
        rewrite /Q44 upd_ne; [| vm_compute; discriminate].
        rewrite /Q43 upd_ne; [| vm_compute; discriminate].
        rewrite /Q42 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HQ45a0 : Q45 !!! Regidx (mword_of_int 10 : mword 5) = pg).
      { rewrite /Q45 upd_ne; [| vm_compute; discriminate].
        rewrite /Q44 upd_ne; [| vm_compute; discriminate].
        rewrite /Q43 upd_ne; [| vm_compute; discriminate].
        rewrite /Q42 upd_ne; [| vm_compute; discriminate].
        rewrite /Q41 upd_eq.
        rewrite Hfs1 HMmss1. apply add_vec_zero_l. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kalloc + 0x4a)) (mword_of_int 1 : mword 5) Q45 K b
                ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi4a").
      iIntros (CIDg6 Hsg6) "Hcg Hpc".
      assert (Hretf : ret_pc (Q45 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
        by (rewrite HQ45ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDrel CIDg6 n eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDg6 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! Q45 with "Hcg Hcnt Hpc [%] [Hpage Havail]").
      { (* callee_saved m Q45 *)
        assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                  c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                  c <> mword_of_int 9 -> c <> mword_of_int 10 ->
                  c <> mword_of_int 11 -> c <> mword_of_int 12 ->
                  c <> mword_of_int 14 -> c <> mword_of_int 15 ->
                  Q45 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N1 N2 N8 N9 N10 N11 N12 N14 N15.
          let peel := (repeat (rewrite upd_ne; [ | congruence ])) in
          rewrite /Q45 /Q44 /Q43 /Q42 /Q41; peel;
          rewrite (callee_saved_lookup Hpinsf_cs c Hcs);
          rewrite /Mms /M3a /Mli /Mlui; peel;
          rewrite (callee_saved_lookup Hrelpins_cs c Hcs);
          rewrite /R12 /R11 /R10 /R9 /R8 /R7 /R6; peel;
          rewrite (callee_saved_lookup Hacqpins_cs c Hcs);
          rewrite /mA /R4 /R3 /R2 /R1; peel;
          reflexivity. }
        unfold callee_saved.
        split.
        { rewrite /Q45 upd_eq.
          rewrite HspQ44. unfold regval_into_reg, spr. apply frame_cancel_32. }
        split.
        { rewrite /Q45 upd_ne; [| vm_compute; discriminate].
          rewrite /Q44 upd_ne; [| vm_compute; discriminate].
          rewrite /Q43 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        split.
        { rewrite /Q45 upd_ne; [| vm_compute; discriminate].
          rewrite /Q44 upd_eq.
          rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      { rewrite /kalloc_post HQ45a0. iRight. iFrame "Hpage Havail". iPureIntro. exact Hpv. }
  Qed.

End ProofKalloc.

End KallocProof.
