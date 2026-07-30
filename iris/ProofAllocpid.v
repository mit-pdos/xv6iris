(* ProofAllocpid.v -- the whole-function WP for allocpid().

     int allocpid() {
       int pid;
       acquire(&pid_lock);
       pid = nextpid;
       nextpid = nextpid + 1;
       release(&pid_lock);
       return pid;
     }

   Twenty-one instructions @ 0x800019d0.  Structurally killed() with a store
   added: a 32-byte ra/s0/s1 frame, acquire, one [c.lw] / [addiw] / [c.sw]
   on <nextpid>, release, and the parked value moved into a0.

   The counter's value is never named by the contract (SpecAllocpid.v says
   why), so [nextpid_res]'s existential is opened right after acquire and
   closed with whatever the [c.sw] wrote -- the whole lock story is two
   lines. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpMmodeLeafBase WpAuipc.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import ProcGeom.
Require Import SpecAcquire SpecRelease.
Require Import SpecAllocpid.
Require Import WpAllocpidDecode.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Notation API := KernelSyms.allocpid.

(* [c.mv rd,rs] is modelled as [add zero, rs]. *)
Lemma apid_addv_zero_l (X : mword 64) : add_vec (zero_reg : mword 64) X = X.
Proof.
  assert (Hu : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite Hu.
  assert (HZ : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite HZ Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

Lemma apid_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (Hu : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !Hu. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
             = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
             = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* the two auipc/addi relocations *)
Lemma apid_lock_reloc1 :
  add_vec (add_vec (mword_of_int (API + 0x0a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))
          (sign_extend' 64 (mword_of_int 2414 : mword 12)) = alp_pid_lock.
Proof. rewrite /alp_pid_lock. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma apid_lock_reloc2 :
  add_vec (add_vec (mword_of_int (API + 0x26) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))
          (sign_extend' 64 (mword_of_int 2386 : mword 12)) = alp_pid_lock.
Proof. rewrite /alp_pid_lock. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma apid_next_reloc :
  add_vec (add_vec (mword_of_int (API + 0x16) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))
          (sign_extend' 64 (mword_of_int 2062 : mword 12)) = alp_nextpid.
Proof. rewrite /alp_nextpid. apply bv_eq; vm_compute; reflexivity. Qed.

(* a zero displacement is the identity on the base *)
Lemma apid_off0 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X.
Proof.
  replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  apply kv_addv_zero.
Qed.

(* the numeric side conditions, mword-free (the zify-hook rule) *)
Lemma apid_K4 (av : nat) : (14 <= av)%nat -> (4 <= av)%nat.
Proof. lia. Qed.
Lemma apid_K10 (av : nat) : (14 <= av)%nat -> (10 <= av - 4)%nat.
Proof. lia. Qed.
Lemma apid_Kback (av : nat) : (14 <= av)%nat -> ((av - 4) + 4)%nat = av.
Proof. lia. Qed.

Module AllocpidProof (Acquire : ACQUIRE) (Release : RELEASE) : ALLOCPID.

Section ProofAllocpid.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  Notation ai_ra := (mword_of_int 1 : mword 5).
  Notation ai_s0 := (mword_of_int 8 : mword 5).
  Notation ai_s1 := (mword_of_int 9 : mword 5).
  Notation ai_a0 := (mword_of_int 10 : mword 5).
  Notation ai_a4 := (mword_of_int 14 : mword 5).
  Notation ai_a5 := (mword_of_int 15 : mword 5).

  Lemma wp_allocpid_sconf (γ : gname) (Φ : mval -> iProp Σ) (γp : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    : wp_allocpid_sconf_body γ Φ γp m av n eb p C.
  Proof.
    cbv beta delta [wp_allocpid_sconf_body].
    intros pcE ret_tgt Htp Hn Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hislock #Hpanic Hcont".
    (* ===================== PROLOGUE ===================== *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspM1 : M1 !!! Regidx csp_rs1 = spd) by (rewrite /M1 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (apdi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE (mword_of_int 32 : mword 6) m av 4 (apid_K4 av Hav) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (API + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (v1) "Hb1". iDestruct "S2c" as (v2) "Hb2".
    iDestruct "S3c" as (v3) "Hb3". iDestruct "S4c" as (v4) "Hb4".
    assert (Hslot : forall (k u : nat), (k + u = 4)%nat -> (u < 4)%nat ->
              pa_stk sp0 k = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))).
    { intros k u Hku Hu. rewrite -Hspd4.
      destruct u as [|[|[|[|]]]]; try lia; destruct k as [|[|[|[|[|]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite add_vec_off2;
        f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1a := Hslot 1%nat 3%nat ltac:(lia) ltac:(lia)).
    assert (Hb2a := Hslot 2%nat 2%nat ltac:(lia) ltac:(lia)).
    assert (Hb3a := Hslot 3%nat 1%nat ltac:(lia) ltac:(lia)).
    iPoseProof (apdi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (API + 0x02)) (mword_of_int 3 : mword 6) ai_ra M1 (av - 4)%nat v1
              with "Hcg Hpc Hi02 [Hb1] [-]").
    { iEval (rewrite HcspM1 -Hb1a). iExact "Hb1". }
    iIntros "Hcg Hpc Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (API + 0x02) : mword 64) 2 = mword_of_int (API + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (apdi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (API + 0x04)) (mword_of_int 2 : mword 6) ai_s0 M1 (av - 4)%nat v2
              with "Hcg Hpc Hi04 [Hb2] [-]").
    { iEval (rewrite HcspM1 -Hb2a). iExact "Hb2". }
    iIntros "Hcg Hpc Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (API + 0x04) : mword 64) 2 = mword_of_int (API + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (apdi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (API + 0x06)) (mword_of_int 1 : mword 6) ai_s1 M1 (av - 4)%nat v3
              with "Hcg Hpc Hi06 [Hb3] [-]").
    { iEval (rewrite HcspM1 -Hb3a). iExact "Hb3". }
    iIntros "Hcg Hpc Hb3".
    assert (Hp08 : add_vec_int (mword_of_int (API + 0x06) : mword 64) 2 = mword_of_int (API + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    assert (HraM1 : M1 !!! Regidx ai_ra = m !!! Regidx ai_ra) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0M1 : M1 !!! Regidx ai_s0 = m !!! Regidx ai_s0) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1M1 : M1 !!! Regidx ai_s1 = m !!! Regidx ai_s1) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspM1 HraM1) in "Hb1".
    iEval (rewrite HcspM1 Hs0M1) in "Hb2".
    iEval (rewrite HcspM1 Hs1M1) in "Hb3".
    (* +0x08 addi4spn s0,sp,32 *)
    iPoseProof (apdi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (API + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) ai_s0
              M1 (av - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx ai_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx ai_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hp0a : add_vec_int (mword_of_int (API + 0x08) : mword 64) 2 = mword_of_int (API + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a auipc a0,0x11 ; +0x0e addi a0,a0,-1682 : a0 := &pid_lock *)
    iPoseProof (apdi_0a with "Htext") as "Hi0a".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (API + 0x0a)) ai_a0 (mword_of_int 0x11 : mword 20) A1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx ai_a0 := regval_into_reg
        (add_vec (mword_of_int (API + 0x0a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> A1).
    change (<[Regidx ai_a0 := regval_into_reg
        (add_vec (mword_of_int (API + 0x0a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> A1) with A2.
    assert (Hp0e : add_vec_int (mword_of_int (API + 0x0a) : mword 64) 4 = mword_of_int (API + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    iPoseProof (apdi_0e with "Htext") as "Hi0e".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (API + 0x0e)) ai_a0 ai_a0 (mword_of_int 2414 : mword 12) A2 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx ai_a0 := regval_into_reg
        (add_vec (A2 !!! Regidx ai_a0) (sign_extend' 64 (mword_of_int 2414 : mword 12)))]> A2).
    change (<[Regidx ai_a0 := regval_into_reg
        (add_vec (A2 !!! Regidx ai_a0) (sign_extend' 64 (mword_of_int 2414 : mword 12)))]> A2) with A3.
    assert (Hp12 : add_vec_int (mword_of_int (API + 0x0e) : mword 64) 4 = mword_of_int (API + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    assert (HA3a0 : A3 !!! Regidx ai_a0 = alp_pid_lock).
    { rewrite /A3 upd_eq /A2 upd_eq. exact apid_lock_reloc1. }
    (* +0x12 jal ra,acquire *)
    iPoseProof (apdi_12 with "Htext") as "Hi12".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (API + 0x12)) ai_ra (mword_of_int 2093606 : mword 21)
              A3 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (A4 := <[Regidx ai_ra := regval_into_reg (add_vec_int (mword_of_int (API + 0x12) : mword 64) 4)]> A3).
    change (<[Regidx ai_ra := regval_into_reg (add_vec_int (mword_of_int (API + 0x12) : mword 64) 4)]> A3) with A4.
    assert (Hjacq : add_vec (mword_of_int (API + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 2093606 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    assert (HA4ra : A4 !!! Regidx ai_ra = add_vec_int (mword_of_int (API + 0x12) : mword 64) 4) by (rewrite /A4 upd_eq; reflexivity).
    assert (HA4a0 : A4 !!! Regidx ai_a0 = alp_pid_lock)
      by (rewrite /A4 upd_ne; [exact HA3a0 | vm_compute; discriminate]).
    assert (HA4csp : A4 !!! Regidx csp_rs1 = spd).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspM1. }
    assert (HA4rest : forall r : mword 5, is_cs_idx r = true ->
                        r <> csp_rs1 -> r <> ai_s0 -> r <> ai_s1 ->
                        A4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    assert (HA4tp : A4 !!! Regidx (mword_of_int 4 : mword 5) = cid_word)
      by (rewrite (HA4rest (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Htp).
    iApply (Acquire.wp_acquire_sconf γ Φ γp "nextpid"%string nextpid_res A4 n eb p C (av - 4)%nat
              HA4tp Hn (apid_K10 av Hav)
              with "Hcg Hcpu Htext Hpc [Hislock] Hpanic [-]").
    { iEval (rewrite HA4a0). iExact "Hislock". }
    iIntros (ms macq) "%Hmsf Hcg Hpc %Hcsacq Hlocked HR Hcpu Hpay".
    assert (Hp16 : ret_pc (A4 !!! Regidx ai_ra) = mword_of_int (API + 0x16))
      by (rewrite HA4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    iDestruct "HR" as (nv) "Hnp".
    assert (Hacq_csp : macq !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcsacq csp_rs1 ltac:(vm_compute; reflexivity)). exact HA4csp. }
    assert (Hacq_tp : macq !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite (callee_saved_lookup Hcsacq (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)). exact HA4tp. }
    assert (Hacq_rest : forall r : mword 5, is_cs_idx r = true ->
                          r <> csp_rs1 -> r <> ai_s0 -> r <> ai_s1 ->
                          macq !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup Hcsacq r Hr). exact (HA4rest r Hr Ncsp N8 N9). }
    (* +0x16 auipc a5,0x9 ; +0x1a addi a5,a5,-2034 : a5 := &nextpid *)
    iPoseProof (apdi_16 with "Htext") as "Hi16".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (API + 0x16)) ai_a5 (mword_of_int 9 : mword 20) macq (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx ai_a5 := regval_into_reg
        (add_vec (mword_of_int (API + 0x16) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))]> macq).
    change (<[Regidx ai_a5 := regval_into_reg
        (add_vec (mword_of_int (API + 0x16) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))]> macq) with B1.
    assert (Hp1a : add_vec_int (mword_of_int (API + 0x16) : mword 64) 4 = mword_of_int (API + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    iPoseProof (apdi_1a with "Htext") as "Hi1a".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (API + 0x1a)) ai_a5 ai_a5 (mword_of_int 2062 : mword 12) B1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx ai_a5 := regval_into_reg
        (add_vec (B1 !!! Regidx ai_a5) (sign_extend' 64 (mword_of_int 2062 : mword 12)))]> B1).
    change (<[Regidx ai_a5 := regval_into_reg
        (add_vec (B1 !!! Regidx ai_a5) (sign_extend' 64 (mword_of_int 2062 : mword 12)))]> B1) with B2.
    assert (Hp1e : add_vec_int (mword_of_int (API + 0x1a) : mword 64) 4 = mword_of_int (API + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    assert (HB2a5 : B2 !!! Regidx ai_a5 = alp_nextpid).
    { rewrite /B2 upd_eq /B1 upd_eq. exact apid_next_reloc. }
    (* +0x1e c.lw s1,0(a5) : pid = nextpid *)
    iPoseProof (apdi_1e with "Htext") as "Hi1e".
    assert (Hnaddr : add_vec (B2 !!! Regidx ai_a5) (sign_extend' 64 (mword_of_int 0 : mword 12)) = alp_nextpid)
      by (rewrite HB2a5; apply apid_off0).
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (API + 0x1e)) ai_s1 ai_a5
              (mword_of_int 0 : mword 12) B2 (av - 4)%nat (nv : mword 32) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [Hnp] [-]").
    { iEval (rewrite Hnaddr). iExact "Hnp". }
    iIntros "Hcg Hpc Hnp". iEval (rewrite Hnaddr) in "Hnp".
    set (B3 := <[Regidx ai_s1 := regval_into_reg (sign_extend' 64 (nv : mword 32))]> B2).
    change (<[Regidx ai_s1 := regval_into_reg (sign_extend' 64 (nv : mword 32))]> B2) with B3.
    assert (Hp20 : add_vec_int (mword_of_int (API + 0x1e) : mword 64) 2 = mword_of_int (API + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HB3s1 : B3 !!! Regidx ai_s1 = sign_extend' 64 (nv : mword 32)) by (rewrite /B3 upd_eq; reflexivity).
    (* +0x20 addiw a4,s1,1 *)
    iPoseProof (apdi_20 with "Htext") as "Hi20".
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (API + 0x20)) ai_a4 ai_s1 (mword_of_int 1 : mword 12) B3 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 [-]").
    iIntros "Hcg Hpc".
    set (B4 := <[Regidx ai_a4 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (B3 !!! Regidx ai_s1) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> B3).
    change (<[Regidx ai_a4 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (B3 !!! Regidx ai_s1) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> B3) with B4.
    assert (Hp24 : add_vec_int (mword_of_int (API + 0x20) : mword 64) 4 = mword_of_int (API + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    assert (HB4a5 : B4 !!! Regidx ai_a5 = alp_nextpid).
    { rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate]. exact HB2a5. }
    (* +0x24 c.sw a4,0(a5) : nextpid = pid + 1 *)
    iPoseProof (apdi_24 with "Htext") as "Hi24".
    assert (Hnaddr2 : add_vec (B4 !!! Regidx ai_a5) (sign_extend' 64 (mword_of_int 0 : mword 12)) = alp_nextpid)
      by (rewrite HB4a5; apply apid_off0).
    iApply (wp_csw_s_sconf γ Φ (mword_of_int (API + 0x24)) ai_a4 ai_a5
              (mword_of_int 0 : mword 12) B4 (av - 4)%nat (nv : mword 32)
              with "Hcg Hpc Hi24 [Hnp] [-]").
    { iEval (rewrite Hnaddr2). iExact "Hnp". }
    iIntros "Hcg Hpc Hnp". iEval (rewrite Hnaddr2) in "Hnp".
    assert (Hp26 : add_vec_int (mword_of_int (API + 0x24) : mword 64) 2 = mword_of_int (API + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* the lock's resource is whole again -- the counter's value is existential *)
    iAssert nextpid_res with "[Hnp]" as "HR".
    { rewrite /nextpid_res. iExists (trunc32 (B4 !!! Regidx ai_a4)). iExact "Hnp". }
    (* +0x26 auipc a0,0x11 ; +0x2a addi a0,a0,-1710 : a0 := &pid_lock *)
    iPoseProof (apdi_26 with "Htext") as "Hi26".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (API + 0x26)) ai_a0 (mword_of_int 0x11 : mword 20) B4 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26 [-]").
    iIntros "Hcg Hpc".
    set (B5 := <[Regidx ai_a0 := regval_into_reg
        (add_vec (mword_of_int (API + 0x26) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> B4).
    change (<[Regidx ai_a0 := regval_into_reg
        (add_vec (mword_of_int (API + 0x26) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> B4) with B5.
    assert (Hp2a : add_vec_int (mword_of_int (API + 0x26) : mword 64) 4 = mword_of_int (API + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    iPoseProof (apdi_2a with "Htext") as "Hi2a".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (API + 0x2a)) ai_a0 ai_a0 (mword_of_int 2386 : mword 12) B5 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [-]").
    iIntros "Hcg Hpc".
    set (B6 := <[Regidx ai_a0 := regval_into_reg
        (add_vec (B5 !!! Regidx ai_a0) (sign_extend' 64 (mword_of_int 2386 : mword 12)))]> B5).
    change (<[Regidx ai_a0 := regval_into_reg
        (add_vec (B5 !!! Regidx ai_a0) (sign_extend' 64 (mword_of_int 2386 : mword 12)))]> B5) with B6.
    assert (Hp2e : add_vec_int (mword_of_int (API + 0x2a) : mword 64) 4 = mword_of_int (API + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    assert (HB6a0 : B6 !!! Regidx ai_a0 = alp_pid_lock).
    { rewrite /B6 upd_eq /B5 upd_eq. exact apid_lock_reloc2. }
    (* +0x2e jal ra,release *)
    iPoseProof (apdi_2e with "Htext") as "Hi2e".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (API + 0x2e)) ai_ra (mword_of_int 2093714 : mword 21)
              B6 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2e [-]").
    iIntros "Hcg Hpc".
    set (B7 := <[Regidx ai_ra := regval_into_reg (add_vec_int (mword_of_int (API + 0x2e) : mword 64) 4)]> B6).
    change (<[Regidx ai_ra := regval_into_reg (add_vec_int (mword_of_int (API + 0x2e) : mword 64) 4)]> B6) with B7.
    assert (Hjrel : add_vec (mword_of_int (API + 0x2e) : mword 64) (sign_extend' 64 (mword_of_int 2093714 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HB7ra : B7 !!! Regidx ai_ra = add_vec_int (mword_of_int (API + 0x2e) : mword 64) 4) by (rewrite /B7 upd_eq; reflexivity).
    assert (HB7a0 : B7 !!! Regidx ai_a0 = alp_pid_lock)
      by (rewrite /B7 upd_ne; [exact HB6a0 | vm_compute; discriminate]).
    assert (Hlka : add_vec (B7 !!! Regidx ai_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = alp_pid_lock)
      by (rewrite HB7a0; apply apid_off0).
    assert (HB7s1 : B7 !!! Regidx ai_s1 = sign_extend' 64 (nv : mword 32)).
    { rewrite /B7 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate]. exact HB3s1. }
    assert (HB7csp : B7 !!! Regidx csp_rs1 = spd).
    { rewrite /B7 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. exact Hacq_csp. }
    assert (HB7tp : B7 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /B7 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. exact Hacq_tp. }
    assert (HB7rest : forall r : mword 5, is_cs_idx r = true ->
                        r <> csp_rs1 -> r <> ai_s0 -> r <> ai_s1 ->
                        B7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> mword_of_int 14) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /B7 upd_ne; [| congruence].
      rewrite /B6 upd_ne; [| congruence].
      rewrite /B5 upd_ne; [| congruence].
      rewrite /B4 upd_ne; [| congruence].
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      exact (Hacq_rest r Hr Ncsp N8 N9). }
    iApply (Release.wp_release_sconf γ Φ γp alp_pid_lock "nextpid"%string nextpid_res B7 n eb p C (av - 4)%nat
              Hlka HB7tp (apid_K10 av Hav)
              with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay [-]").
    iIntros (mrel) "Hcg Hpc %Hcsrel Hcpu".
    assert (Hp32 : ret_pc (B7 !!! Regidx ai_ra) = mword_of_int (API + 0x32))
      by (rewrite HB7ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    assert (Hrel_csp : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcsrel csp_rs1 ltac:(vm_compute; reflexivity)). exact HB7csp. }
    assert (Hrel_s1 : mrel !!! Regidx ai_s1 = sign_extend' 64 (nv : mword 32)).
    { rewrite (callee_saved_lookup Hcsrel ai_s1 ltac:(vm_compute; reflexivity)). exact HB7s1. }
    assert (Hrel_rest : forall r : mword 5, is_cs_idx r = true ->
                          r <> csp_rs1 -> r <> ai_s0 -> r <> ai_s1 ->
                          mrel !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup Hcsrel r Hr). exact (HB7rest r Hr Ncsp N8 N9). }
    (* ===================== EPILOGUE ===================== *)
    (* +0x32 c.mv a0,s1 *)
    iPoseProof (apdi_32 with "Htext") as "Hi32".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (API + 0x32)) ai_a0 ai_s1 mrel (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi32 [-]").
    iIntros "Hcg Hpc".
    set (E0 := <[Regidx ai_a0 := regval_into_reg (add_vec zero_reg (mrel !!! Regidx ai_s1))]> mrel).
    change (<[Regidx ai_a0 := regval_into_reg (add_vec zero_reg (mrel !!! Regidx ai_s1))]> mrel) with E0.
    assert (Hp34 : add_vec_int (mword_of_int (API + 0x32) : mword 64) 2 = mword_of_int (API + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    assert (HE0csp : E0 !!! Regidx csp_rs1 = spd)
      by (rewrite /E0 upd_ne; [exact Hrel_csp | vm_compute; discriminate]).
    iPoseProof (apdi_34 with "Htext") as "Hi34".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (API + 0x34)) (mword_of_int 3 : mword 6) ai_ra
              E0 (av - 4)%nat (m !!! Regidx ai_ra) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi34 [Hb1] [-]").
    { iEval (rewrite HE0csp). iExact "Hb1". }
    iIntros "Hcg Hpc Hb1".
    set (E1 := <[Regidx ai_ra := regval_into_reg (m !!! Regidx ai_ra)]> E0).
    change (<[Regidx ai_ra := regval_into_reg (m !!! Regidx ai_ra)]> E0) with E1.
    assert (Hp36 : add_vec_int (mword_of_int (API + 0x34) : mword 64) 2 = mword_of_int (API + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    assert (HE1csp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact HE0csp | vm_compute; discriminate]).
    iPoseProof (apdi_36 with "Htext") as "Hi36".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (API + 0x36)) (mword_of_int 2 : mword 6) ai_s0
              E1 (av - 4)%nat (m !!! Regidx ai_s0) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi36 [Hb2] [-]").
    { iEval (rewrite HE1csp). iExact "Hb2". }
    iIntros "Hcg Hpc Hb2".
    set (E2 := <[Regidx ai_s0 := regval_into_reg (m !!! Regidx ai_s0)]> E1).
    change (<[Regidx ai_s0 := regval_into_reg (m !!! Regidx ai_s0)]> E1) with E2.
    assert (Hp38 : add_vec_int (mword_of_int (API + 0x36) : mword 64) 2 = mword_of_int (API + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp38) in "Hpc".
    assert (HE2csp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1csp | vm_compute; discriminate]).
    iPoseProof (apdi_38 with "Htext") as "Hi38".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (API + 0x38)) (mword_of_int 1 : mword 6) ai_s1
              E2 (av - 4)%nat (m !!! Regidx ai_s1) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi38 [Hb3] [-]").
    { iEval (rewrite HE2csp). iExact "Hb3". }
    iIntros "Hcg Hpc Hb3".
    set (E3 := <[Regidx ai_s1 := regval_into_reg (m !!! Regidx ai_s1)]> E2).
    change (<[Regidx ai_s1 := regval_into_reg (m !!! Regidx ai_s1)]> E2) with E3.
    assert (Hp3a : add_vec_int (mword_of_int (API + 0x38) : mword 64) 2 = mword_of_int (API + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    assert (HE3csp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2csp | vm_compute; discriminate]).
    (* +0x3a c.addi16sp sp,32 *)
    assert (Hup : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite /spd /sp0; apply apid_frame_cancel).
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE3csp; exact Hup).
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HE3csp; symmetry; exact Hspd4).
    iPoseProof (apdi_3a with "Htext") as "Hi3a".
    iAssert (stack_own sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1". { iExists _. iEval (rewrite Hb1a -HE0csp). iExact "Hb1". }
      iSplitL "Hb2". { iExists _. iEval (rewrite Hb2a -HE1csp). iExact "Hb2". }
      iSplitL "Hb3". { iExists _. iEval (rewrite Hb3a -HE2csp). iExact "Hb3". }
      iSplitL "Hb4". { iExists v4. iExact "Hb4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (API + 0x3a)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 Hpop
              with "Hcg Hpc Hi3a Hframe4 [-]").
    iIntros "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by (apply apid_Kback; exact Hav).
    iEval (rewrite Hnk) in "Hcg".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hp3c : add_vec_int (mword_of_int (API + 0x3a) : mword 64) 2 = mword_of_int (API + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3c) in "Hpc".
    (* +0x3c c.ret *)
    assert (HE4ra : E4 !!! Regidx ai_ra = m !!! Regidx ai_ra).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (apdi_3c with "Htext") as "Hi3c".
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (API + 0x3c)) ai_ra E4 av
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi3c [-]").
    iIntros "Hcg Hpc".
    assert (Hretfin : ret_pc (E4 !!! Regidx ai_ra) = ret_tgt) by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    assert (HE4csp : E4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /E4 upd_eq; exact Hwv).
    assert (HE4s0 : E4 !!! Regidx ai_s0 = m !!! Regidx ai_s0).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2. apply upd_eq. }
    assert (HE4s1 : E4 !!! Regidx ai_s1 = m !!! Regidx ai_s1).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3. apply upd_eq. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> ai_s0 -> r <> ai_s1 ->
                     E4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      exact (Hrel_rest r Hr Ncsp N8 N9). }
    iApply ("Hcont" $! E4 with "[%] Hcg Hcpu Hpc").
    unfold callee_saved.
    split; [exact HE4csp|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [exact HE4s0|]. split; [exact HE4s1|].
    repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofAllocpid.

End AllocpidProof.
