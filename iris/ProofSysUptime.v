(* ProofSysUptime.v -- sys_uptime() over the SIE-agnostic sconf world.

   sys_uptime() @ 0x80002a74 is the whole of xv6's tick syscall:

     acquire(&tickslock);  xticks = ticks;  release(&tickslock);  return xticks;

   On the standard 32-byte frame (ra/s0/s1), a0 := &tickslock is materialized
   twice by an auipc/addi pair, the counter is read with a full-width [lw]
   INSIDE the critical section (the value is carried to the epilogue in the
   callee-saved s1), and the [uint] return type is realized by the slli/srli
   32-bit pair -- so the returned a0 is the zero-extension of the 32-bit tick
   value read.  Nothing about that value is known: the lock protects
   [ticks_res] (TicksInv.v), the counter cell at an ARBITRARY value, so the
   read hands back an existential [t] and re-closing the resource is immediate.

   A functor over ACQUIRE / RELEASE.

   THE SIE INDEX: [b] is threaded generically end-to-end (a plain function
   that merely calls acquire then release nets no SIE change), except for the
   stretch strictly between acquire's return and release's call, which is
   pinned at literal [false] (acquire disables; release requires disabled
   entry).  Acquire and release's own [n]/[eb] match this function's, so
   release hands back [cpu_own n eb p C outb] for [outb := match n with O =>
   eb | S _ => false end]; [CpuOwn.cpu_own_eb_agree] derives [outb = b] from the
   entry resources (ghost agreement between [sie_arm]'s and [intr_count]'s
   eighths -- see the porting guide's "Derive the SIE index rather than
   stating it"), so the fact is in hand by the time release returns. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import StackOwn CalleeSaved.
Require Import VcGen.
Require Import WpLock.
Require Import KernelRvcDecode WpAuipc.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import CodeSysUptime.
Require Import TicksInv.
Require Import SpecAcquire SpecRelease.
Require Import SpecSysUptime.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* the shift amount both halves of the (uint) cast use. *)
Notation su_sh32 := (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0).

(* ===================================================================== *)
(* The C [(uint)] cast: [x << 32 >> 32] keeps the low 32 bits and clears  *)
(* the top half -- i.e. it is [zero_extend' 64 (trunc32 x)].  (Sibling of *)
(* [slli32_srli32] in WpMemsetArray.v, which states the same round trip   *)
(* as an identity under the [x < 2^32] hypothesis memset's count enjoys;  *)
(* here the shifted value is a SIGN-extended [lw] result, so the cast     *)
(* genuinely changes it.  A third user should move both to RiscvExtras.)  *)
(* ===================================================================== *)
Lemma su_uint_cast (x : mword 64) :
  shift_bits_right (shift_bits_left x su_sh32) su_sh32 = zero_extend' 64 (trunc32 x).
Proof.
  assert (Hl : shift_bits_left x su_sh32 = shiftl x 32).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  assert (Hr : forall y : mword 64, shift_bits_right y su_sh32 = shiftr y 32).
  { intro y. unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hl. rewrite Hr. apply bv_eq.
  unfold shiftl, shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left, MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned. rewrite bv_shiftl_unsigned.
  assert (H32 : bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 32)) = 32).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite H32.
  assert (Hze : bv_unsigned (zero_extend' 64 (trunc32 x)) = bv_unsigned (trunc32 x)).
  { cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec to_word get_word
         MachineWord.MachineWord.zero_extend].
    rewrite bv_zero_extend_unsigned. reflexivity.
    first [ lia | vm_compute; discriminate | done ]. }
  rewrite Hze. rewrite trunc32_unsigned.
  unfold bv_wrap.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 2 ^ 64)
    by (unfold bv_modulus; f_equal).
  assert (Hm32 : bv_modulus 32 = 2 ^ 32) by (unfold bv_modulus; f_equal).
  rewrite Hm64. rewrite Hm32.
  rewrite Z.shiftl_mul_pow2; [| lia].
  rewrite Z.shiftr_div_pow2; [| lia].
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by (vm_compute; reflexivity).
  rewrite Z.mul_mod_distr_r; [| lia | lia].
  rewrite Z.div_mul; [reflexivity | lia].
Qed.

(* the cast applied to a sign-extended 32-bit load: back to the plain value. *)
Lemma su_uint_cast_sext (t : mword 32) :
  shift_bits_right (shift_bits_left (sign_extend' 64 t) su_sh32) su_sh32 = zero_extend' 64 t.
Proof. rewrite su_uint_cast. rewrite trunc32_sext. reflexivity. Qed.

(* two one-liners copied self-contained (they live inside WpWakeup's section;
   requiring that file here would be a heavy edge for two trivialities). *)
Lemma su_eq_vec_refl {k} (x : mword k) : eq_vec x x = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.



Module SysUptimeProof (Acquire : ACQUIRE) (Release : RELEASE) : SYSUPTIME.

Section ProofSysUptime.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.


  Lemma wp_sys_uptime_sconf (Φ : mval -> iProp Σ) (γl : gname)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) (b : bool)
    : wp_sys_uptime_sconf_body Φ γl m n eb p C av b.
  Proof.
    cbv beta delta [wp_sys_uptime_sconf_body].
    intros pcE ret_tgt Htp Hn Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hlock #Hpanic Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbeq.
    iDestruct (is_tickslock_lock with "Hlock") as "#Hlk".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    iPoseProof (sui_00 with "Htext") as "Hi00".
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
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
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SU + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
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
    (* +0x02/+0x04/+0x06: c.sdsp ra/s0/s1 *)
    iPoseProof (sui_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (SU + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 b
              with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (SU + 0x02) : mword 64) 2 = mword_of_int (SU + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (sui_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (SU + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 b
              with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (SU + 0x04) : mword 64) 2 = mword_of_int (SU + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (sui_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (SU + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 b
              with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (SU + 0x06) : mword 64) 2 = mword_of_int (SU + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (sui_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (SU + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (SU + 0x08) : mword 64) 2 = mword_of_int (SU + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ===================== a0 := &tickslock ===================== *)
    (* +0x0a: auipc a0,0x15 *)
    iPoseProof (sui_0a with "Htext") as "Hi0a".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (SU + 0x0a)) (mword_of_int 10 : mword 5) (mword_of_int 0x15 : mword 20)
              A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (SU + 0x0a) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> A1).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (SU + 0x0a) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> A1) with A2.
    assert (Hpc0e : add_vec_int (mword_of_int (SU + 0x0a) : mword 64) 4 = mword_of_int (SU + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e: addi a0,a0,1786 *)
    iPoseProof (sui_0e with "Htext") as "Hi0e".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (SU + 0x0e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x6fa : mword 12)
              A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (A2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x6fa : mword 12)))]> A2).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (A2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x6fa : mword 12)))]> A2) with A3.
    assert (Hpc12 : add_vec_int (mword_of_int (SU + 0x0e) : mword 64) 4 = mword_of_int (SU + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* +0x12: jal ra,acquire *)
    iPoseProof (sui_12 with "Htext") as "Hi12".
    iApply (wp_jal_s_sconf Φ (mword_of_int (SU + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 2089346 : mword 21)
              A3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (A4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SU + 0x12) : mword 64) 4)]> A3).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SU + 0x12) : mword 64) 4)]> A3) with A4.
    assert (Hjacq : add_vec (mword_of_int (SU + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 2089346 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    (* register facts at acquire's entry *)
    assert (HA4ra : A4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (SU + 0x12) : mword 64) 4)
      by (rewrite /A4 upd_eq; reflexivity).
    assert (HA4a0 : A4 !!! Regidx (mword_of_int 10 : mword 5) = a_tickslock).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_eq. rewrite /A2 upd_eq.
      rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity. }
    assert (HA4csp : A4 !!! Regidx csp_rs1 = spd).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspA0. }
    (* ===================== acquire(&tickslock) ===================== *)
    iDestruct (cpu_own_transport CID CID8 n eb p C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf Φ γl "time"%string ticks_res A4
              n eb p C (av - 4)%nat b
              ltac:(exact Hn)
              ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlk] Hpanic [-]").
    { iEval (rewrite HA4a0). iExact "Hlk". }
    iIntros (CID9 Hs9 ms MA) "%Hms Hcg Hpc %HcsA Htok HR Hcnt Hpay".
    assert (Hpc16 : ret_pc (A4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (SU + 0x16))
      by (rewrite HA4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* the protected resource: the counter cell at an arbitrary value *)
    iDestruct "HR" as (t) "Hticks".
    assert (HMAcsp : MA !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)). exact HA4csp. }
    (* ===================== a5 := ticks ===================== *)
    (* +0x16: auipc a5,0x7 *)
    iPoseProof (sui_16 with "Htext") as "Hi16".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (SU + 0x16)) (mword_of_int 15 : mword 5) (mword_of_int 0x7 : mword 20)
              MA (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (SU + 0x16) : mword 64) (auipc_off (mword_of_int 0x7 : mword 20)))]> MA).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (SU + 0x16) : mword 64) (auipc_off (mword_of_int 0x7 : mword 20)))]> MA) with B0.
    assert (Hpc1a : add_vec_int (mword_of_int (SU + 0x16) : mword 64) 4 = mword_of_int (SU + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* +0x1a: lw a5,1982(a5) -- the read, under the lock *)
    assert (Haddrt : add_vec (B0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 0x7be : mword 12)) = a_ticks).
    { rewrite /B0 upd_eq. rewrite /a_ticks. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (sui_1a with "Htext") as "Hi1a".
    iApply (wp_lw_s_sconf Φ (mword_of_int (SU + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 0x7be : mword 12) B0 (av - 4)%nat t false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [Hticks] [-]").
    { iEval (rewrite Haddrt). iExact "Hticks". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hticks".
    iEval (rewrite Haddrt) in "Hticks".
    set (B1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (t : mword 32))]> B0).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (t : mword 32))]> B0) with B1.
    assert (Hpc1e : add_vec_int (mword_of_int (SU + 0x1a) : mword 64) 4 = mword_of_int (SU + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* +0x1e: c.mv s1,a5 -- carry the value across release in s1 *)
    iPoseProof (sui_1e with "Htext") as "Hi1e".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (SU + 0x1e)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              B1 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (B1 !!! Regidx (mword_of_int 15 : mword 5)))]> B1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (B1 !!! Regidx (mword_of_int 15 : mword 5)))]> B1) with B2.
    assert (Hpc20 : add_vec_int (mword_of_int (SU + 0x1e) : mword 64) 2 = mword_of_int (SU + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    assert (HB2s1 : B2 !!! Regidx (mword_of_int 9 : mword 5) = sign_extend' 64 (t : mword 32)).
    { rewrite /B2 upd_eq. rewrite add_vec_zero_l. rewrite /B1 upd_eq. reflexivity. }
    (* ===================== a0 := &tickslock (again) ===================== *)
    (* +0x20: auipc a0,0x15 *)
    iPoseProof (sui_20 with "Htext") as "Hi20".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (SU + 0x20)) (mword_of_int 10 : mword 5) (mword_of_int 0x15 : mword 20)
              B2 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (SU + 0x20) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> B2).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (SU + 0x20) : mword 64) (auipc_off (mword_of_int 0x15 : mword 20)))]> B2) with B3.
    assert (Hpc24 : add_vec_int (mword_of_int (SU + 0x20) : mword 64) 4 = mword_of_int (SU + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* +0x24: addi a0,a0,1764 *)
    iPoseProof (sui_24 with "Htext") as "Hi24".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (SU + 0x24)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x6e4 : mword 12)
              B3 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (B3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x6e4 : mword 12)))]> B3).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (B3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x6e4 : mword 12)))]> B3) with B4.
    assert (Hpc28 : add_vec_int (mword_of_int (SU + 0x24) : mword 64) 4 = mword_of_int (SU + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* +0x28: jal ra,release *)
    iPoseProof (sui_28 with "Htext") as "Hi28".
    iApply (wp_jal_s_sconf Φ (mword_of_int (SU + 0x28)) (mword_of_int 1 : mword 5) (mword_of_int 2089460 : mword 21)
              B4 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi28 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SU + 0x28) : mword 64) 4)]> B4).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (SU + 0x28) : mword 64) 4)]> B4) with B5.
    assert (Hjrel : add_vec (mword_of_int (SU + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2089460 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HB5ra : B5 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (SU + 0x28) : mword 64) 4)
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a0 : B5 !!! Regidx (mword_of_int 10 : mword 5) = a_tickslock).
    { rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_eq. rewrite /B3 upd_eq.
      rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity. }
    assert (HB5csp : B5 !!! Regidx csp_rs1 = spd).
    { rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate].
      exact HMAcsp. }
    (* ===================== release(&tickslock) ===================== *)
    iDestruct (ticks_res_intro t with "Hticks") as "HR".
    iApply (Release.wp_release_sconf Φ γl a_tickslock "time"%string ticks_res B5
              n eb p C (av - 4)%nat
              ltac:(rewrite HB5a0; apply addv_sext0)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlk] [Htok] [HR] Hcnt Hpay [-]").
    { iExact "Hlk". }
    { iExact "Htok". }
    { iExact "HR". }
    iIntros (CID10 Hs10 MR) "Hcg Hpc %HcsR Hcnt".
    (* the SIE index release hands back is [outb := match n with O => eb |
       S _ => false end]; [Hbeq] identifies it with [b], derived up front. *)
    rewrite Hbeq in Hs10.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcnt".
    assert (Hpc2c : ret_pc (B5 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (SU + 0x2c))
      by (rewrite HB5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    (* ===================== the (uint) return cast ===================== *)
    assert (HMRs1 : MR !!! Regidx (mword_of_int 9 : mword 5) = sign_extend' 64 (t : mword 32)).
    { rewrite (callee_saved_lookup HcsR (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate]. exact HB2s1. }
    assert (HMRcsp : MR !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup HcsR csp_rs1 ltac:(vm_compute; reflexivity)). exact HB5csp. }
    (* +0x2c: slli a0,s1,0x20 *)
    iPoseProof (sui_2c with "Htext") as "Hi2c".
    iApply (wp_slli_s_sconf Φ (mword_of_int (SU + 0x2c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 32 : mword 6)
              (shift_bits_left (MR !!! Regidx (mword_of_int 9 : mword 5)) su_sh32)
              MR (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi2c [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (C0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_left (MR !!! Regidx (mword_of_int 9 : mword 5)) su_sh32)]> MR).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_left (MR !!! Regidx (mword_of_int 9 : mword 5)) su_sh32)]> MR) with C0.
    assert (Hpc30 : add_vec_int (mword_of_int (SU + 0x2c) : mword 64) 4 = mword_of_int (SU + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* +0x30: c.srli a0,a0,0x20 *)
    iPoseProof (sui_30 with "Htext") as "Hi30".
    iEval (rewrite creg_c2) in "Hi30".
    iApply (wp_csrli_s_sconf Φ (mword_of_int (SU + 0x30)) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              (mword_of_int 32 : mword 6) C0 (av - 4)%nat b
              creg_c2 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (C1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_right (C0 !!! Regidx (mword_of_int 10 : mword 5)) su_sh32)]> C0).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_right (C0 !!! Regidx (mword_of_int 10 : mword 5)) su_sh32)]> C0) with C1.
    assert (Hpc32 : add_vec_int (mword_of_int (SU + 0x30) : mword 64) 2 = mword_of_int (SU + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc32) in "Hpc".
    (* a0 is now the zero-extension of the tick value *)
    assert (HC1a0 : C1 !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (t : mword 32)).
    { rewrite /C1 upd_eq. rewrite /C0 upd_eq. rewrite HMRs1. apply su_uint_cast_sext. }
    assert (HC1csp : C1 !!! Regidx csp_rs1 = spd).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate]. exact HMRcsp. }
    (* ===================== EPILOGUE ===================== *)
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    (* the leaves' storeval is [rget A0 rs2], let-bound outside their own
       [wp_next] -- [rgne] peels it to the CID-free [!!!] lookup before the
       plain map-chain facts [HraA0]/[Hs0A0]/[Hs1A0] can rewrite it. *)
    iEval (rgne) in "Hr24". iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rgne) in "Hr16". iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rgne) in "Hr8". iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    (* +0x32/+0x34/+0x36: c.ldsp ra/s0/s1 *)
    iPoseProof (sui_32 with "Htext") as "Hi32".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (SU + 0x32)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              C1 (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [Hr24] [-]").
    { iEval (rewrite HC1csp). iExact "Hr24". }
    iIntros (CID13 Hs13) "Hcg Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C1) with E1.
    assert (Hpc34 : add_vec_int (mword_of_int (SU + 0x32) : mword 64) 2 = mword_of_int (SU + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    assert (HE1csp : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact HC1csp | vm_compute; discriminate]).
    iPoseProof (sui_34 with "Htext") as "Hi34".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (SU + 0x34)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [Hr16] [-]").
    { iEval (rewrite HE1csp). iExact "Hr16". }
    iIntros (CID14 Hs14) "Hcg Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc36 : add_vec_int (mword_of_int (SU + 0x34) : mword 64) 2 = mword_of_int (SU + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    assert (HE2csp : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HE1csp | vm_compute; discriminate]).
    iPoseProof (sui_36 with "Htext") as "Hi36".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (SU + 0x36)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 [Hr8] [-]").
    { iEval (rewrite HE2csp). iExact "Hr8". }
    iIntros (CID15 Hs15) "Hcg Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc38 : add_vec_int (mword_of_int (SU + 0x36) : mword 64) 2 = mword_of_int (SU + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    (* +0x38: c.addi16sp sp,32 -- the frame pop *)
    assert (HE3csp : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HE2csp | vm_compute; discriminate]).
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 upd_eq HE3csp. exact Hsp0up. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE3csp. exact Hsp0up. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE3csp. symmetry. exact Hspd4. }
    iPoseProof (sui_38 with "Htext") as "Hi38".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HC1csp). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HE1csp). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HE2csp). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (SU + 0x38)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi38 Hframe4 [-]").
    iIntros (CID16 Hs16) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc3a : add_vec_int (mword_of_int (SU + 0x38) : mword 64) 2 = mword_of_int (SU + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3a) in "Hpc".
    (* +0x3a: c.ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (sui_3a with "Htext") as "Hi3a".
    iApply (wp_cret_s_sconf Φ (mword_of_int (SU + 0x3a)) (mword_of_int 1 : mword 5) E4 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi3a [-]").
    iIntros (CID17 Hs17) "Hcg Hpc".
    assert (Hretfin : ret_pc (E4 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== return ===================== *)
    assert (HE4a0 : E4 !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (t : mword 32)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate]. exact HC1a0. }
    assert (HE4csp : E4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite HE4sp Hspm; reflexivity).
    assert (HE4s0 : E4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2. apply upd_eq. }
    assert (HE4s1 : E4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3. apply upd_eq. }
    (* every other callee-saved register (tp, s2..s11) threads untouched: the
       peel goes through E4..E1/C1/C0, release, B5..B0, acquire, A4..A0. *)
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                     E4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N4 : r <> mword_of_int 4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence].
      rewrite /C0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsR r Hr).
      rewrite /B5 upd_ne; [| congruence].
      rewrite /B4 upd_ne; [| congruence].
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      rewrite /B0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CID10 CID17 n eb p C b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID17 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 t with "[%] Hcg Hcnt Hpc").
    split; [| exact HE4a0].
    unfold callee_saved.
    split; [exact HE4csp|].
    split; [exact HE4s0|].
    split; [exact HE4s1|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofSysUptime.

End SysUptimeProof.
