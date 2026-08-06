(* ProofMyproc.v: myproc() over the SIE-agnostic sconf/sie_cap bundle.

   myproc() @ 0x80001904 returns a0 = the current process (the value the
   [cur_proc] resource holds in cpus[cpuid].proc), read under push_off/pop_off:
   the standard 32-byte frame (ra/s0/s1) + jal push_off + the mycpu-style a5
   materialization of &cpus[cpuid] (mv a5,tp / sext.w / slli 7 / auipc a4 /
   addi a4 (=pid_lock) / add a5,a4) + c.ld a5,48(a5) (the c->proc field, since
   cpus = pid_lock+48) + s1:=a5 + jal pop_off + a0:=s1 + epilogue.

   Prologue/epilogue are byte-identical to acquire's (same frame); the a5 chain
   is byte-identical to mycpu's, so its value equals [mycpu_a5], and the c.ld
   address reconciles to [mycpu_ret cid_word] = [a_cpu_proc cid_word].  A
   functor over PUSHOFF (push_off / pop_off). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import KernelRvcDecode WpAuipc.
Require Import ProcGeom.
Require Import CodeMyproc.
Require Import CpuOwn.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import SpecPushOff.
Require Import SpecMyproc.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure address / value reconciliation lemmas.                            *)
(* ===================================================================== *)




(* the a4 pid_lock constant (auipc a4,0x11 at myproc+0x14 then addi a4,-1488) *)
Definition mp_A4C : mword 64 :=
  add_vec (add_vec (mword_of_int (KernelSyms.myproc + 0x14) : mword 64)
                   (auipc_off (mword_of_int 0x11 : mword 20)))
          (sign_extend' 64 (mword_of_int 0xa2e : mword 12)).

(* the c.ld's +48 displacement, in the leaf's [sign_extend' 64 imm] form. *)
Definition mp_L48 : mword 64 :=
  sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"000"))).

(* mycpu_ret's constant tower (= &cpus). *)
Definition mp_CPUSC : mword 64 :=
  add_vec (add_vec (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14)
                   (auipc_off (mword_of_int 0x11 : mword 20)))
          (sign_extend' 64 (mword_of_int 0xa84 : mword 12)).

Local Lemma mycpu_ret_split (tp0 : mword 64) :
  mycpu_ret tp0 = add_vec mp_CPUSC (mycpu_a5 tp0).
Proof. reflexivity. Qed.

(* THE reconciliation: the c.ld address form over [tp0] equals mycpu_ret tp0.
   [pid_lock + shift] + 48 = [cpus + shift] with cpus = pid_lock + 48, by
   assoc/comm; the constant parts both [vm_compute] to &cpus. *)
Local Lemma mp_load_reconcile (tp0 : mword 64) :
  add_vec (add_vec (mycpu_a5 tp0) mp_A4C) mp_L48 = mycpu_ret tp0.
Proof.
  rewrite mycpu_ret_split.
  rewrite po_addv_assoc.
  assert (Hc : add_vec mp_A4C mp_L48 = mp_CPUSC)
    by (unfold mp_A4C, mp_L48, mp_CPUSC; apply bv_eq; vm_compute; reflexivity).
  rewrite Hc. apply add_vec64_comm.
Qed.

(* the noff cell round trip: pop_off's [-1] store of push_off's [+1] store of
   [noffv] is exactly [noffv] (exact mod 2^32).  Structure copied from
   kfree_nv1_cancel_pure (a bits-keyed pure fact); re-proved self-contained
   here rather than importing the kfree proof file. *)
Local Lemma mp_nv1_cancel (noffv : mword 32) :
  sign_extend' 64 (subrange_vec_dec (add_vec
     (sign_extend' 64 (autocast (T := mword) (subrange_vec_dec
        (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32))
     (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
  = sign_extend' 64 noffv.
Proof.
  set (a5 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)).
  set (store := (autocast (T := mword) (subrange_vec_dec a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)).
  assert (H1 : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64) = (mword_of_int 1 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (H63 : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)) : mword 64) = (mword_of_int (-1) : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Hstore : store = add_vec noffv (mword_of_int 1 : mword 32)).
  { unfold store. change (Z.sub (Z.mul 4 8) 1) with 31. rewrite autocast_id.
    rewrite <- trunc32_subrange. unfold a5. rewrite trunc32_sext.
    rewrite <- trunc32_subrange. rewrite trunc32_add. rewrite trunc32_sext. rewrite H1. reflexivity. }
  f_equal.
  rewrite <- trunc32_subrange. rewrite trunc32_add. rewrite trunc32_sext. rewrite H63.
  fold a5. fold store. rewrite Hstore.
  apply bv_eq.
  assert (avu : forall x y : mword 32, bv_unsigned (add_vec x y) = bv_wrap 32 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  rewrite !avu.
  change (bv_unsigned (mword_of_int 1 : mword 32)) with 1.
  change (bv_unsigned (mword_of_int (-1) : mword 32)) with (bv_modulus 32 - 1).
  rewrite bv_wrap_add_idemp_l.
  rewrite <- Z.add_assoc.
  replace (1 + (bv_modulus 32 - 1)) with (bv_modulus 32) by lia.
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* the pop_off storeval (over noff1) reduces to noffv (as mword 32). *)
Local Lemma noff_push_pop_id (noffv : mword 32) :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec
        (sign_extend' 64 (autocast (T := mword) (subrange_vec_dec
           (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
           (Z.sub (Z.mul 4 8) 1) 0) : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = noffv.
Proof.
  change (Z.sub (Z.mul 4 8) 1) with 31 at 1.
  rewrite autocast_id.
  rewrite <- trunc32_subrange.
  rewrite mp_nv1_cancel.
  apply trunc32_sext.
Qed.

(* generic register-map peel over the proof's [set]-chain (hit-first, per the
   register-lookup perf rule); stops at an opaque map variable. *)
Local Ltac mp_gpeel :=
  repeat first
    [ rewrite upd_eq
    | rewrite upd_ne; [| vm_compute; discriminate]
    | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
(* peel a callee-saved s-register across pop_off (H2) then push_off (H1). *)
Local Ltac mp_scs_tac H2 H1 := mp_gpeel; rewrite H2; mp_gpeel; rewrite H1; mp_gpeel; reflexivity.


Module MyprocProof (PushOff : PUSHOFF) : MYPROC.

Section ProofMyproc.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_myproc_sconf (Φ : mval -> iProp Σ)
      (m : regfile) (av n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool)
    : wp_myproc_sconf_body Φ m av n eb p C b.
  Proof.
    cbv beta delta [wp_myproc_sconf_body].
    intros pcE ret_tgt Hpos Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hown #Htext Hpc Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbmatch. symmetry in Hbmatch.
    iPoseProof (mpi_00 with "Htext") as "Hi00".
    iPoseProof (mpi_02 with "Htext") as "Hi02".
    iPoseProof (mpi_04 with "Htext") as "Hi04".
    iPoseProof (mpi_06 with "Htext") as "Hi06".
    iPoseProof (mpi_08 with "Htext") as "Hi08".
    (* ---- 0x00: c.addi sp,-32 -- the frame push (k := 4) ---- *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd)
      by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x02/0x04/0x06: c.sdsp ra/s0/s1 ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 b
              with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 b
              with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 b
              with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.myproc + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ---- 0x0a: jal ra,push_off ---- *)
    iPoseProof (mpi_0a with "Htext") as "Hi0a".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2093758 : mword 21)
              A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.myproc + 0x0a) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.myproc + 0x0a) : mword 64) 4)]> A1) with A2.
    assert (Hpcpo : add_vec (mword_of_int (KernelSyms.myproc + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2093758 : mword 21))
                    = mword_of_int KernelSyms.push_off) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcpo) in "Hpc".
    assert (HcspA2 : A2 !!! Regidx csp_rs1 = spd).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspA0. }
    (* [Hown] was introduced at the function's ENTRY hart; the six plain
       instructions above each moved to a FRESH hart (CID1..CID6), so
       push_off wants it at CID6. *)
    iDestruct (cpu_own_transport CID CID6 n eb p C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* the noff/intena cells + counting token ride inside cpu_own *)
    iApply (PushOff.wp_push_off_sconf Φ A2 (av - 4)%nat n eb p C b
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hown Htext Hpc [-]").
    iIntros (CIDpo Hspo ms MP1) "%Hmsf Hcg Hown Hpay Hpc %Hmp1".
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc0e : ret_pc (add_vec_int (mword_of_int (KernelSyms.myproc + 0x0a) : mword 64) 4)
                    = (mword_of_int (KernelSyms.myproc + 0x0e) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* ---- the a5 chain: mv a5,tp / sext.w / slli 7 / auipc a4 / addi a4 / add a5,a4 ----
       This interior runs entirely under [sie_cap_gpr ... false p] (push_off's
       exit index), so every leaf below collapses via [wp_next_off] -- the
       hart stays [CIDpo] throughout, exactly like mycpu()'s own interrupts-off
       tp read. *)
    iPoseProof (mpi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x0e)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              MP1 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (HtpMP1 : rget MP1 (mword_of_int 4 : mword 5) = cid_word) by (exact (rget_tp MP1)).
    iEval (rewrite HtpMP1) in "Hcg".
    set (B1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg cid_word)]> MP1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg cid_word)]> MP1) with B1.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    iPoseProof (mpi_10 with "Htext") as "Hi10".
    iApply (wp_caddiw_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              B1 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (B1 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (B1 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B1) with B2.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    iPoseProof (mpi_12 with "Htext") as "Hi12".
    iApply (wp_cslli_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x12)) (Regidx (mword_of_int 15 : mword 5)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              B2 (av - 4)%nat false
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (B2 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> B2).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (B2 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> B2) with B3.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* the shift value equals mycpu_a5 of this hart's id *)
    assert (HB3a5 : B3 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /B3 upd_eq /B2 upd_eq /B1 upd_eq. unfold mycpu_a5. reflexivity. }
    (* ---- 0x14: auipc a4,0x11 ---- *)
    iPoseProof (mpi_14 with "Htext") as "Hi14".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x14)) (mword_of_int 14 : mword 5) (mword_of_int 0x11 : mword 20)
              B3 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.myproc + 0x14) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> B3).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.myproc + 0x14) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> B3) with B4.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.myproc + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* ---- 0x18: addi a4,a4,-1488 ---- *)
    iPoseProof (mpi_18 with "Htext") as "Hi18".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x18)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0xa2e : mword 12)
              B4 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (B4 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 2606 : mword 12)))]> B4).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (B4 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 2606 : mword 12)))]> B4) with B5.
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.myproc + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.myproc + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (HB5a4 : B5 !!! Regidx (mword_of_int 14 : mword 5) = mp_A4C).
    { rewrite /B5 upd_eq /B4 upd_eq. reflexivity. }
    assert (HB5a5 : B5 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate]. exact HB3a5. }
    (* ---- 0x1c: c.add a5,a5,a4 ---- *)
    iPoseProof (mpi_1c with "Htext") as "Hi1c".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              B5 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (B6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (B5 !!! Regidx (mword_of_int 15 : mword 5)) (B5 !!! Regidx (mword_of_int 14 : mword 5)))]> B5).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (B5 !!! Regidx (mword_of_int 15 : mword 5)) (B5 !!! Regidx (mword_of_int 14 : mword 5)))]> B5) with B6.
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.myproc + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* the c.ld address reconciles to a_cpu_proc cid_word = mycpu_ret cid_word *)
    assert (HB6a5 : B6 !!! Regidx (mword_of_int 15 : mword 5)
                    = add_vec (mycpu_a5 cid_word) mp_A4C).
    { rewrite /B6 upd_eq HB5a4 HB5a5. reflexivity. }
    assert (Hpa : add_vec (rget B6 (mword_of_int 15 : mword 5))
                    (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"000"))))
                  = mycpu_ret cid_word).
    { rgne. rewrite HB6a5. change (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"000")))) with mp_L48.
      rewrite mp_load_reconcile. reflexivity. }
    (* ---- 0x1e: c.ld a5,48(a5) -- read the current-proc field ---- *)
    (* expose c->proc from cpu_own for the read, then refold *)
    iDestruct (cpu_own_set_proc (S n) eb p p C with "Hown") as "(Hcur & Hown)".
    iEval (rewrite /cpu_proc_half /a_cpu_proc) in "Hcur".
    iPoseProof (mpi_1e with "Htext") as "Hi1e".
    iApply (wp_cld_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x1e)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"000")))
              B6 (av - 4)%nat p false (dqm := DfracOwn (1/2))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [Hcur] [-]").
    { iEval (rewrite Hpa). iExact "Hcur". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcur".
    iEval (rewrite Hpa) in "Hcur".
    iSpecialize ("Hown" with "Hcur").
    set (B7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg p]> B6).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg p]> B6) with B7.
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* ---- 0x20: c.mv s1,a5 ---- *)
    iPoseProof (mpi_20 with "Htext") as "Hi20".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x20)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              B7 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (B7 !!! Regidx (mword_of_int 15 : mword 5)))]> B7).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (B7 !!! Regidx (mword_of_int 15 : mword 5)))]> B7) with B8.
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* s1 now holds p *)
    assert (HB7a5 : B7 !!! Regidx (mword_of_int 15 : mword 5) = p) by (rewrite /B7 upd_eq; reflexivity).
    (* ---- 0x22: jal ra,pop_off ---- *)
    iPoseProof (mpi_22 with "Htext") as "Hi22".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x22)) (mword_of_int 1 : mword 5) (mword_of_int 2093856 : mword 21)
              B8 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B9 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.myproc + 0x22) : mword 64) 4)]> B8).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.myproc + 0x22) : mword 64) 4)]> B8) with B9.
    assert (Hpcpp : add_vec (mword_of_int (KernelSyms.myproc + 0x22) : mword 64) (sign_extend' 64 (mword_of_int 2093856 : mword 21))
                    = mword_of_int KernelSyms.pop_off) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcpp) in "Hpc".
    assert (HB9ra : B9 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.myproc + 0x26))
      by (rewrite /B9 upd_eq; apply bv_eq; vm_compute; reflexivity).
    iApply (PushOff.wp_pop_off_sconf Φ B9 (av - 4)%nat n eb p C
              ltac:(lia)
              with "Hcg Hown Hpay Htext Hpc [-]").
    rewrite -Hbmatch.
    iIntros (CIDpp Hspp MP2) "Hcg Hown Hpc %Hmp2".
    iEval (rewrite HB9ra) in "Hpc".
    assert (Hpc26 : ret_pc (mword_of_int (KernelSyms.myproc + 0x26) : mword 64)
                    = (mword_of_int (KernelSyms.myproc + 0x26) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- 0x26: c.mv a0,s1 ---- *)
    iPoseProof (mpi_26 with "Htext") as "Hi26".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x26)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              MP2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CIDe1 Hse1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (MP2 !!! Regidx (mword_of_int 9 : mword 5)))]> MP2).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (MP2 !!! Regidx (mword_of_int 9 : mword 5)))]> MP2) with C1.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* a0 = p: s1 (through pop_off, callee-saved) still holds p *)
    assert (Hs1MP2 : MP2 !!! Regidx (mword_of_int 9 : mword 5) = p).
    { destruct Hmp2 as (_ & _ & Hs1_2 & _). rewrite Hs1_2.
      rewrite /B9 upd_ne; [| vm_compute; discriminate].
      rewrite /B8 upd_eq HB7a5. apply add_vec_zero_l. }
    assert (Ha0C1 : C1 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /C1 upd_eq Hs1MP2. apply add_vec_zero_l. }
    (* ---- 0x28/0x2a/0x2c: c.ldsp ra/s0/s1 (restore) ---- *)
    assert (HcspC1 : C1 !!! Regidx csp_rs1 = spd).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      destruct Hmp2 as (Hsp2 & _). rewrite Hsp2.
      rewrite /B9 upd_ne; [| vm_compute; discriminate].
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B7 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      destruct Hmp1 as (Hsp1 & _). rewrite Hsp1. exact HcspA2. }
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    iPoseProof (mpi_28 with "Htext") as "Hi28".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x28)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              C1 (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [Hr24] [-]").
    { iEval (rewrite HcspC1). iExact "Hr24". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C1) with E1.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.myproc + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact HcspC1 | vm_compute; discriminate]).
    iPoseProof (mpi_2a with "Htext") as "Hi2a".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x2a)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hr16] [-]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.myproc + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    iPoseProof (mpi_2c with "Htext") as "Hi2c".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x2c)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hr8] [-]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.myproc + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* ---- 0x2e: c.addi16sp sp,32 -- the frame pop ---- *)
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 upd_eq HcspE3. exact Hsp0up. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspE3. exact Hsp0up. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspE3. symmetry. exact Hspd4. }
    iPoseProof (mpi_2e with "Htext") as "Hi2e".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HcspC1). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x2e)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi2e Hframe4 [-]").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.myproc + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.myproc + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* ---- 0x30: c.ret ---- *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (mpi_30 with "Htext") as "Hi30".
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.myproc + 0x30)) (mword_of_int 1 : mword 5) E4 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    assert (Hra_final : ret_pc (rget E4 (mword_of_int 1 : mword 5)) = ret_tgt).
    { rgne. rewrite HE4ra. reflexivity. }
    iEval (rewrite Hra_final) in "Hpc".
    (* [Hown] rode unchanged (at [CIDpp]) across the 6 plain epilogue
       instructions; transport it to the final hart [CIDe6] before handing
       everything back to [Hcont]. *)
    iDestruct (cpu_own_transport CIDpp CIDe6 n eb p C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iSpecialize ("Hcont" $! CIDe6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! ms E4 with "[%] Hcg Hown Hpc [%]").
    { exact Hmsf. }
    (* callee_saved m E4  /\  E4!!!a0 = p *)
    destruct Hmp1 as (Hsp1 & Hs01 & Hs11 & Hs21 & Hs31 & Hs41 & Hs51 & Hs61 & Hs71 & Hs81 & Hs91 & Hs101 & Hs111).
    destruct Hmp2 as (Hsp2 & Hs02 & Hs12 & Hs22 & Hs32 & Hs42 & Hs52 & Hs62 & Hs72 & Hs82 & Hs92 & Hs102 & Hs112).
    (* each conjunct proved order-independently as an assert (the s-register
       peel goes through E4/E3/E2/E1/C1, pop_off (H*2), B9..B1, push_off (H*1),
       A2/A1/A0 back to m; s0/s1 land at the ldsp restore, a0 at c.mv a0,s1). *)
    assert (Ca0 : E4 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate]. exact Ha0C1. }
    assert (Csp : E4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite HE4sp Hspm; reflexivity).
    assert (Cs0 : E4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (mp_gpeel; reflexivity).
    assert (Cs1 : E4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (mp_gpeel; reflexivity).
    assert (Cs2 : E4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (mp_scs_tac Hs22 Hs21).
    assert (Cs3 : E4 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (mp_scs_tac Hs32 Hs31).
    assert (Cs4 : E4 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (mp_scs_tac Hs42 Hs41).
    assert (Cs5 : E4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (mp_scs_tac Hs52 Hs51).
    assert (Cs6 : E4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (mp_scs_tac Hs62 Hs61).
    assert (Cs7 : E4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (mp_scs_tac Hs72 Hs71).
    assert (Cs8 : E4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (mp_scs_tac Hs82 Hs81).
    assert (Cs9 : E4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (mp_scs_tac Hs92 Hs91).
    assert (Cs10 : E4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (mp_scs_tac Hs102 Hs101).
    assert (Cs11 : E4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (mp_scs_tac Hs112 Hs111).
    split; [ unfold callee_saved; repeat split; assumption | exact Ca0 ].
  Qed.

End ProofMyproc.

End MyprocProof.
