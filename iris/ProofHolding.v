(* ProofHolding.v: holding over the SIE-agnostic v2 bundle (stage 8,
   the spinlock layer's first function).

   holding(lk) = lk->locked && lk->cpu == mycpu().  The FAST path (lock
   free) touches no stack: the deep custody rides through untouched.
   The SLOW path is the push_off-shaped frame trade (k:=4) around a
   mycpu call, with the lk->cpu read going THROUGH THE LOCK INVARIANT
   (WpSconfLock's wp_cld_lkcpu_lockinv leaves) and the seqz chain deciding the
   return value.  Two variants: the EVIDENCE-FREE form (the owner word is
   unknown, so the answer is 0 or 1 -- what acquire's sanity check gets, its
   1 arm absorbed by panic) and the LOCKED/MINE form (the [locked] token
   refutes the fast path AND pins the owner word at mycpu(), so the
   answer is 1 -- release's check).

   Both lemmas are stated at [b = false] (SpecHolding.v): holding() [jal
   mycpu]s at +0x16, and [mycpu]'s own contract is pinned at the literal
   [false] (its [tp] read happens mid-body).  With no [wp_next] wrapper in
   the contract, every internal leaf call below -- each of which is STILL
   [b]-generic (WpSconfLock.v/WpSconfAlu.v et al. are unchanged) -- is made
   at the literal [false] and its own [wp_next false (...)] obligation is
   collapsed immediately with [rewrite wp_next_off], so NO fresh hart symbol
   is ever introduced: every resource stays about the ONE ambient [CID]
   from entry to return.  This is what makes the +0x12 [lk->cpu] read
   provable at all -- a [b]-generic statement would hand that leaf a
   [locked]/[Tc] credential about the entry hart while the leaf demands one
   about its own (potentially different, post-migration) ambient hart. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import HartTp WpNext IntrDefs.
Require Import StackOwn CalleeSaved.
Require Import WpSmodeIntr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfLock.
Require Import WpLock.
Require Import KernelRvcDecode CodeMycpu SpecMycpu.
Require Import CodeHolding WpHoldingInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecHolding.
Require Import CodeHoldingAux.
Require Import CodeMycpuAux.
Import Defs.




Module HoldingProof (Mycpu : MYCPU) : HOLDING.

Section ProofHolding.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_holding_lockinv_s_sconf (Φ : mval -> iProp Σ)
      (γl : gname) (lka : mword 64) (R Tc Dc : iProp Σ)
      (m : regfile) (n : nat) (p : mword 64)
    : wp_holding_lockinv_s_sconf_body Φ γl lka R Tc Dc m n p.
  Proof.
    cbv beta delta [wp_holding_lockinv_s_sconf_body].
    intros pcE lk ret_tgt Hlka Hn Href.
    assert (Hlkeq : lk = lka).
    { rewrite -Hlka.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      symmetry. apply kv_addv_zero. }
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc #Hlock HTc Hcont".
    iPoseProof (hi_00 with "Htext") as "Hi00".
    iPoseProof (hi_02 with "Htext") as "Hi02".
    (* ---- 0x00: c.lw a5,0(a0) through the lock invariant ---- *)
    iApply (wp_clw_lockopen_s_sconf Φ γl lka R Tc Dc pcE (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 0) m n false
              Hlka ltac:(vm_compute; discriminate) ltac:(rdok) Href
              with "Hcg Hpc Hi00 Hlock HTc [-]").
    iIntros (lockv). iApply wp_next_off_intro.
    iIntros "HTc Hcg Hpc".
    set (H1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m) with H1.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    assert (Ha5H1 : H1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv)
      by (rewrite /H1; apply upd_eq).
    (* ---- 0x02: c.bnez a5 : the free/locked split ---- *)
    destruct (neq_vec (sign_extend' 64 lockv) zero_reg) eqn:Hlv.
    2:{ (* ===== FAST path: lock free -> return 0 ===== *)
      iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                H1 n false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Ha5H1; exact Hlv)
                with "Hcg Hpc Hi02 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.holding + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc04) in "Hpc".
      (* ---- 0x04: c.li a0,0 ---- *)
      iPoseProof (hi_04 with "Htext") as "Hi04".
      iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x04)) (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) H1 n false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi04 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (H2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> H1).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> H1) with H2.
      assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.holding + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc06) in "Hpc".
      (* ---- 0x06: c.ret ---- *)
      assert (HraH2 : H2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H2 upd_ne; [| vm_compute; discriminate].
        rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
      iPoseProof (hi_06 with "Htext") as "Hi06".
      iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x06)) (mword_of_int 1 : mword 5) H2 n false
                ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi06 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hra_final : ret_pc (H2 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
        by (rewrite HraH2; reflexivity).
      iEval (rewrite Hra_final) in "Hpc".
      iApply ("Hcont" $! H2 with "HTc Hcg Hpc [%]").
      split.
      - assert (HH2w : H2 = apply_writes
          [ ((mword_of_int 10 : mword 5), regval_into_reg (mword_of_int 0 : mword 64));
            ((mword_of_int 15 : mword 5), regval_into_reg (sign_extend' 64 lockv)) ] m) by reflexivity.
        rewrite HH2w. apply callee_saved_apply_writes. repeat constructor.
      - left. rewrite /H2. apply upd_eq. }
    (* ===== SLOW path: locked -> compare lk->cpu against mycpu ===== *)
    iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              H1 n false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Ha5H1; exact Hlv)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi02 [-]").
    iApply wp_next_off_intro.
    iNext.
    iIntros "Hcg Hpc".
    assert (Htgt08 : add_vec (mword_of_int (KernelSyms.holding + 0x02) : mword 64)
               (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.holding + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt08) in "Hpc".
    (* the frame trade (k := 4) *)
    set (spdh := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    assert (HspH1 : H1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /H1 upd_ne; [reflexivity | vm_compute; discriminate]).
    set (S0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> H1).
    assert (HcspS0 : S0 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S0 upd_eq HspH1; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spdh).
    { rewrite /spdh. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (H1 !!! Regidx csp_rs1) 4).
    { rewrite HspH1. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (his_08 with "Htext") as "Hi08".
    iApply (wp_caddi_sp_push_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x08)) (mword_of_int 32 : mword 6) H1 n 4 false
              ltac:(lia) Hpush
              with "Hcg Hpc Hi08 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite HspH1) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> H1) with S0.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.holding + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spdh. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spdh. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spdh. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x0a/0x0c/0x0e: c.sdsp ra/s0/s1 ---- *)
    iPoseProof (his_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              S0 (n - 4)%nat vr24 false
              with "Hcg Hpc Hi0a [Hr24] [-]").
    { iEval (rewrite HcspS0 -Hb1). iExact "Hr24". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    iPoseProof (his_0c with "Htext") as "Hi0c".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              S0 (n - 4)%nat vr16 false
              with "Hcg Hpc Hi0c [Hr16] [-]").
    { iEval (rewrite HcspS0 -Hb2). iExact "Hr16". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    iPoseProof (his_0e with "Htext") as "Hi0e".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              S0 (n - 4)%nat vr8 false
              with "Hcg Hpc Hi0e [Hr8] [-]").
    { iEval (rewrite HcspS0 -Hb3). iExact "Hr8". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.addi4spn s0,sp,8 ---- *)
    iPoseProof (his_10 with "Htext") as "Hi10".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x10)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              S0 (n - 4)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (S0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> S0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (S0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> S0) with S2.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.holding + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- 0x12: c.ld a5,16(a0) : a5 := lk->cpu ---- *)
    assert (Ha0S2 : S2 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /S2 upd_ne; [| vm_compute; discriminate].
      rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    iPoseProof (his_12 with "Htext") as "Hi12".
    assert (Hacpu : add_vec (S2 !!! Regidx (mword_of_int 10 : mword 5))
                      (sign_extend' 64 (mword_of_int 16 : mword 12)) = lock_cpu lka)
      by (rewrite Ha0S2 Hlkeq; reflexivity).
    iApply (wp_cld_lkcpu_lockopen_s_sconf Φ γl lka R Tc Dc (mword_of_int (KernelSyms.holding + 0x12))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 16 : mword 12) S2 (n - 4)%nat false
              Hacpu ltac:(vm_compute; discriminate) ltac:(rdok) Href
              with "Hcg Hpc Hi12 Hlock HTc [-]").
    iIntros (cpuv). iApply wp_next_off_intro.
    iIntros "HTc Hcg Hpc".
    set (S3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg cpuv]> S2).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg cpuv]> S2) with S3.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.holding + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.mv s1,a5 ---- *)
    iPoseProof (his_14 with "Htext") as "Hi14".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              S3 (n - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (S4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (S3 !!! Regidx (mword_of_int 15 : mword 5)))]> S3).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (S3 !!! Regidx (mword_of_int 15 : mword 5)))]> S3) with S4.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.holding + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: jal ra,mycpu ---- *)
    assert (HcspS4 : S4 !!! Regidx csp_rs1 = spdh).
    { rewrite /S4 upd_ne; [| vm_compute; discriminate].
      rewrite /S3 upd_ne; [| vm_compute; discriminate].
      rewrite /S2 upd_ne; [| vm_compute; discriminate].
      exact HcspS0. }
    iPoseProof (his_16 with "Htext") as "Hi16".
    iApply (Mycpu.wp_call_mycpu_sconf_cs Φ (mword_of_int (KernelSyms.holding + 0x16)) (mword_of_int 0xd2c : mword 21) S4 (n - 4)%nat p
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi16 [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    set (C := mo) in *.
    destruct Hmo as [Hcs Hmo_a0].
    (* [Hcs : callee_saved S4 C] is kept WHOLE rather than destructured: with a
       real function call in the middle, the s2..s11 conjuncts of the OUTER
       [callee_saved m S10] fact do not factor through a per-register name --
       [cs_through]/[callee_saved_lookup] (CalleeSaved.v) are the tools built
       for exactly this "one sub-call in the middle" shape. *)
    assert (Hs1val : C !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg cpuv).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S4 upd_eq. reflexivity. }
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc1a : ret_pc (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4)
                    = (mword_of_int (KernelSyms.holding + 0x1a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a: sub a0,s1,a0 ---- *)
    iPoseProof (his_1a with "Htext") as "Hi1a".
    iApply (wp_sub_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x1a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5))) C (n - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi1a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))]> C).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))]> C) with S5.
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.holding + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: sltiu a0,a0,1 : a0 := (lk->cpu == mycpu) = 0 ---- *)
    iPoseProof (his_1e with "Htext") as "Hi1e".
    iApply (wp_sltiu_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x1e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 1 : mword 12)
              (zero_extend' 64 (bool_to_bit (zopz0zI_u (S5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))
              S5 (n - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (zero_extend' 64 (bool_to_bit (zopz0zI_u (S5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> S5).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (zero_extend' 64 (bool_to_bit (zopz0zI_u (S5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> S5) with S6.
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.holding + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* the return value is 0 or 1 -- whichever way the compare went *)
    assert (Ha0S6 : S6 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)
                 \/ S6 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite /S6 upd_eq /S5 upd_eq Hs1val.
      destruct (eq_vec (add_vec zero_reg cpuv) (C !!! Regidx (mword_of_int 10 : mword 5))) eqn:Hcmp.
      - right. apply seqz_sub_eq. exact Hcmp.
      - left. apply seqz_sub_neq. exact Hcmp. }
    (* ---- 0x22/0x24/0x26: c.ldsp ra/s0/s1 ---- *)
    assert (HcspS6 : S6 !!! Regidx csp_rs1 = spdh).
    { rewrite /S6 upd_ne; [| vm_compute; discriminate].
      rewrite /S5 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HcspS4. }
    assert (HraS0 : S0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hs0S0 : S0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hs1S0 : S0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    iEval (rewrite HcspS0 HraS0) in "Hr24".
    iEval (rewrite HcspS0 Hs0S0) in "Hr16".
    iEval (rewrite HcspS0 Hs1S0) in "Hr8".
    iPoseProof (his_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              S6 (n - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [Hr24] [-]").
    { iEval (rewrite HcspS6). iExact "Hr24". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    set (S7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> S6).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> S6) with S7.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.holding + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    assert (HcspS7 : S7 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S7 upd_ne; [exact HcspS6 | vm_compute; discriminate]).
    iPoseProof (his_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              S7 (n - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hr16] [-]").
    { iEval (rewrite HcspS7). iExact "Hr16". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    set (S8 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> S7).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> S7) with S8.
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.holding + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HcspS8 : S8 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S8 upd_ne; [exact HcspS7 | vm_compute; discriminate]).
    iPoseProof (his_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              S8 (n - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hr8] [-]").
    { iEval (rewrite HcspS8). iExact "Hr8". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    set (S9 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> S8).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> S8) with S9.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.holding + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 -- the frame pop ---- *)
    assert (HcspS9 : S9 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S9 upd_ne; [exact HcspS8 | vm_compute; discriminate]).
    set (S10 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> S9).
    assert (Hwv : add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspS9 /spdh /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HS10sp : S10 !!! Regidx csp_rs1 = sp0).
    { rewrite /S10 upd_eq. exact Hwv. }
    assert (Hpop : S9 !!! Regidx csp_rs1
                   = pa_stk (add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspS9. symmetry. exact Hspd4. }
    iPoseProof (his_28 with "Htext") as "Hi28".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HcspS6). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspS7). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspS8). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x28)) (mword_of_int 2 : mword 6) S9 (n - 4)%nat 4 false Hpop
              with "Hcg Hpc Hi28 Hframe4 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((n - 4) + 4)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> S9) with S10.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.holding + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret ---- *)
    assert (HS10ra : S10 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /S10 upd_ne; [| vm_compute; discriminate].
      rewrite /S9 upd_ne; [| vm_compute; discriminate].
      rewrite /S8 upd_ne; [| vm_compute; discriminate].
      rewrite /S7. apply upd_eq. }
    iPoseProof (his_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x2a)) (mword_of_int 1 : mword 5) S10 n false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (S10 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HS10ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! S10 with "HTc Hcg Hpc [%]").
    split.
    - (* [sp]/[s0]/[s1] are saved-then-restored ACROSS the [mycpu] call (their
         mid-call value is the wrong one), so each is discharged on its own;
         [s2..s11] never move, and factor cleanly through [Hcs] via
         [cs_through] (CalleeSaved.v's tool for exactly this "one sub-call in
         the middle" shape). *)
      unfold callee_saved.
      split; [ rewrite HS10sp; reflexivity | ].
      split.
      { rewrite /S10 upd_ne; [| vm_compute; discriminate].
        rewrite /S9 upd_ne; [| vm_compute; discriminate].
        rewrite /S8 upd_eq. reflexivity. }
      split.
      { rewrite /S10 upd_ne; [| vm_compute; discriminate].
        rewrite /S9 upd_eq. reflexivity. }
      repeat split; cs_through Hcs C.
    - rewrite /S10 upd_ne; [| vm_compute; discriminate].
      rewrite /S9 upd_ne; [| vm_compute; discriminate].
      rewrite /S8 upd_ne; [| vm_compute; discriminate].
      rewrite /S7 upd_ne; [| vm_compute; discriminate].
      exact Ha0S6.
  Qed.

  Lemma wp_holding_lockinv_locked_s_sconf (Φ : mval -> iProp Σ)
      (γl : gname) (lka : mword 64) (R Dc : iProp Σ)
      (m : regfile) (n : nat) (p : mword 64)
    : wp_holding_lockinv_locked_s_sconf_body Φ γl lka R Dc m n p.
  Proof.
    cbv beta delta [wp_holding_lockinv_locked_s_sconf_body].
    intros pcE lk ret_tgt held_cpu Hlka Hn Href.
    assert (Hlkeq : lk = lka).
    { rewrite -Hlka.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      symmetry. apply kv_addv_zero. }
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc #Hlock Htok Hcont".
    iPoseProof (hi_00 with "Htext") as "Hi00".
    iPoseProof (hi_02 with "Htext") as "Hi02".
    (* ---- 0x00: c.lw a5,0(a0) through the lock invariant ---- *)
    iApply (wp_clw_lockopen_locked_s_sconf Φ γl lka R Dc pcE (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 0) m n false
              Hlka ltac:(vm_compute; discriminate) ltac:(rdok) Href
              with "Hcg Hpc Hi00 Hlock Htok [-]").
    iIntros (lockv). iApply wp_next_off_intro.
    iIntros "%Hlv Htok Hcg Hpc".
    set (H1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m) with H1.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    assert (Ha5H1 : H1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv)
      by (rewrite /H1; apply upd_eq).
    (* the lock token pins the word nonzero: the branch is always taken *)
    (* ===== SLOW path: locked -> compare lk->cpu against mycpu ===== *)
    iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              H1 n false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Ha5H1; exact Hlv)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi02 [-]").
    iApply wp_next_off_intro.
    iNext.
    iIntros "Hcg Hpc".
    assert (Htgt08 : add_vec (mword_of_int (KernelSyms.holding + 0x02) : mword 64)
               (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.holding + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt08) in "Hpc".
    (* the frame trade (k := 4) *)
    set (spdh := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    assert (HspH1 : H1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /H1 upd_ne; [reflexivity | vm_compute; discriminate]).
    set (S0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> H1).
    assert (HcspS0 : S0 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S0 upd_eq HspH1; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spdh).
    { rewrite /spdh. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (H1 !!! Regidx csp_rs1) 4).
    { rewrite HspH1. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (his_08 with "Htext") as "Hi08".
    iApply (wp_caddi_sp_push_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x08)) (mword_of_int 32 : mword 6) H1 n 4 false
              ltac:(lia) Hpush
              with "Hcg Hpc Hi08 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite HspH1) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> H1) with S0.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.holding + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spdh. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spdh. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spdh. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x0a/0x0c/0x0e: c.sdsp ra/s0/s1 ---- *)
    iPoseProof (his_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              S0 (n - 4)%nat vr24 false
              with "Hcg Hpc Hi0a [Hr24] [-]").
    { iEval (rewrite HcspS0 -Hb1). iExact "Hr24". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    iPoseProof (his_0c with "Htext") as "Hi0c".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              S0 (n - 4)%nat vr16 false
              with "Hcg Hpc Hi0c [Hr16] [-]").
    { iEval (rewrite HcspS0 -Hb2). iExact "Hr16". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    iPoseProof (his_0e with "Htext") as "Hi0e".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              S0 (n - 4)%nat vr8 false
              with "Hcg Hpc Hi0e [Hr8] [-]").
    { iEval (rewrite HcspS0 -Hb3). iExact "Hr8". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.addi4spn s0,sp,8 ---- *)
    iPoseProof (his_10 with "Htext") as "Hi10".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x10)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              S0 (n - 4)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (S0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> S0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (S0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> S0) with S2.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.holding + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- 0x12: c.ld a5,16(a0) : a5 := lk->cpu ---- *)
    assert (Ha0S2 : S2 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /S2 upd_ne; [| vm_compute; discriminate].
      rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    iPoseProof (his_12 with "Htext") as "Hi12".
    assert (Hacpu : add_vec (S2 !!! Regidx (mword_of_int 10 : mword 5))
                      (sign_extend' 64 (mword_of_int 16 : mword 12)) = lock_cpu lka)
      by (rewrite Ha0S2 Hlkeq; reflexivity).
    iApply (wp_cld_lkcpu_lockopen_locked_s_sconf Φ γl lka R Dc (mword_of_int (KernelSyms.holding + 0x12))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 16 : mword 12) S2 (n - 4)%nat false
              Hacpu ltac:(vm_compute; discriminate) ltac:(rdok) Href
              with "Hcg Hpc Hi12 Hlock Htok [-]").
    iApply wp_next_off_intro.
    iIntros "Htok Hcg Hpc".
    set (S3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mycpu_ret cid_word)]> S2).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mycpu_ret cid_word)]> S2) with S3.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.holding + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.mv s1,a5 ---- *)
    iPoseProof (his_14 with "Htext") as "Hi14".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              S3 (n - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (S4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (S3 !!! Regidx (mword_of_int 15 : mword 5)))]> S3).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (S3 !!! Regidx (mword_of_int 15 : mword 5)))]> S3) with S4.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.holding + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: jal ra,mycpu ---- *)
    assert (HcspS4 : S4 !!! Regidx csp_rs1 = spdh).
    { rewrite /S4 upd_ne; [| vm_compute; discriminate].
      rewrite /S3 upd_ne; [| vm_compute; discriminate].
      rewrite /S2 upd_ne; [| vm_compute; discriminate].
      exact HcspS0. }
    iPoseProof (his_16 with "Htext") as "Hi16".
    iApply (Mycpu.wp_call_mycpu_sconf_cs Φ (mword_of_int (KernelSyms.holding + 0x16)) (mword_of_int 0xd2c : mword 21) S4 (n - 4)%nat p
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi16 [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    set (C := mo) in *.
    destruct Hmo as [Hcs Hmo_a0].
    (* [Hcs : callee_saved S4 C] kept WHOLE -- see the note at the sibling
       (evidence-free) lemma. *)
    assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret cid_word)
      by (rewrite /C Hmo_a0; exact (f_equal mycpu_ret (rget_tp S4))).
    assert (Hs1val : C !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (mycpu_ret cid_word)).
    { rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /S4 upd_eq. reflexivity. }
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc1a : ret_pc (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4)
                    = (mword_of_int (KernelSyms.holding + 0x1a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a: sub a0,s1,a0 ---- *)
    iPoseProof (his_1a with "Htext") as "Hi1a".
    iApply (wp_sub_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x1a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5))) C (n - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi1a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))]> C).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))]> C) with S5.
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.holding + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: sltiu a0,a0,1 : a0 := (lk->cpu == mycpu) = 1 ---- *)
    iPoseProof (his_1e with "Htext") as "Hi1e".
    iApply (wp_sltiu_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x1e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 1 : mword 12)
              (zero_extend' 64 (bool_to_bit (zopz0zI_u (S5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))
              S5 (n - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (S6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (zero_extend' 64 (bool_to_bit (zopz0zI_u (S5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> S5).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (zero_extend' 64 (bool_to_bit (zopz0zI_u (S5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> S5) with S6.
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.holding + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* the return value is 1: lk->cpu = mycpu, by the token's construction *)
    assert (Hmine' : eq_vec (add_vec zero_reg (mycpu_ret cid_word))
                       (C !!! Regidx (mword_of_int 10 : mword 5)) = true).
    { rewrite add_vec_zero_l Ha0C. apply eq_vec_true_iff. reflexivity. }
    assert (Ha0S6 : S6 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite /S6 upd_eq /S5 upd_eq.
      rewrite Hs1val. apply seqz_sub_eq. exact Hmine'. }
    (* ---- 0x22/0x24/0x26: c.ldsp ra/s0/s1 ---- *)
    assert (HcspS6 : S6 !!! Regidx csp_rs1 = spdh).
    { rewrite /S6 upd_ne; [| vm_compute; discriminate].
      rewrite /S5 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HcspS4. }
    assert (HraS0 : S0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hs0S0 : S0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hs1S0 : S0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /S0 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    iEval (rewrite HcspS0 HraS0) in "Hr24".
    iEval (rewrite HcspS0 Hs0S0) in "Hr16".
    iEval (rewrite HcspS0 Hs1S0) in "Hr8".
    iPoseProof (his_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              S6 (n - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [Hr24] [-]").
    { iEval (rewrite HcspS6). iExact "Hr24". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    set (S7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> S6).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> S6) with S7.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.holding + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    assert (HcspS7 : S7 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S7 upd_ne; [exact HcspS6 | vm_compute; discriminate]).
    iPoseProof (his_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              S7 (n - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hr16] [-]").
    { iEval (rewrite HcspS7). iExact "Hr16". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    set (S8 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> S7).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> S7) with S8.
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.holding + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HcspS8 : S8 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S8 upd_ne; [exact HcspS7 | vm_compute; discriminate]).
    iPoseProof (his_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              S8 (n - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hr8] [-]").
    { iEval (rewrite HcspS8). iExact "Hr8". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    set (S9 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> S8).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> S8) with S9.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.holding + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 -- the frame pop ---- *)
    assert (HcspS9 : S9 !!! Regidx csp_rs1 = spdh)
      by (rewrite /S9 upd_ne; [exact HcspS8 | vm_compute; discriminate]).
    set (S10 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> S9).
    assert (Hwv : add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspS9 /spdh /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HS10sp : S10 !!! Regidx csp_rs1 = sp0).
    { rewrite /S10 upd_eq. exact Hwv. }
    assert (Hpop : S9 !!! Regidx csp_rs1
                   = pa_stk (add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspS9. symmetry. exact Hspd4. }
    iPoseProof (his_28 with "Htext") as "Hi28".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HcspS6). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspS7). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspS8). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x28)) (mword_of_int 2 : mword 6) S9 (n - 4)%nat 4 false Hpop
              with "Hcg Hpc Hi28 Hframe4 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((n - 4) + 4)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (S9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> S9) with S10.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.holding + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret ---- *)
    assert (HS10ra : S10 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /S10 upd_ne; [| vm_compute; discriminate].
      rewrite /S9 upd_ne; [| vm_compute; discriminate].
      rewrite /S8 upd_ne; [| vm_compute; discriminate].
      rewrite /S7. apply upd_eq. }
    iPoseProof (his_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.holding + 0x2a)) (mword_of_int 1 : mword 5) S10 n false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (S10 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HS10ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! S10 with "Hcg Hpc [%] Htok").
    split.
    - unfold callee_saved.
      split; [ rewrite HS10sp; reflexivity | ].
      split.
      { rewrite /S10 upd_ne; [| vm_compute; discriminate].
        rewrite /S9 upd_ne; [| vm_compute; discriminate].
        rewrite /S8 upd_eq. reflexivity. }
      split.
      { rewrite /S10 upd_ne; [| vm_compute; discriminate].
        rewrite /S9 upd_eq. reflexivity. }
      repeat split; cs_through Hcs C.
    - rewrite /S10 upd_ne; [| vm_compute; discriminate].
      rewrite /S9 upd_ne; [| vm_compute; discriminate].
      rewrite /S8 upd_ne; [| vm_compute; discriminate].
      rewrite /S7 upd_ne; [| vm_compute; discriminate].
      exact Ha0S6.
  Qed.

End ProofHolding.

End HoldingProof.
