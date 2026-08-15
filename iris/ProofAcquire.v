(* ProofAcquire.v: acquire over the SIE-agnostic v2 bundle (stage 8).
   The amoswap spin loop is the Löb piece: the c.bnez-taken back edge
   hands the step's later out, which strips the IH.  The main lemma
   (next) composes push_off (the flip: the interrupts-off region BEGINS
   here) + the holding-not-mine check + the loop + lk->cpu := mycpu.  *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
From Stdlib Require Import FunctionalExtensionality.
Require Import SmodeCore.
Require Import HartTp WpNext.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfLock.
Require Import WpLock CpuOwn WpAmo KernelRvcDecode.
Require Import SpecMycpu SpecHolding.
Require Import PanicStub.
Require Import SpecPushOff.
Require Import CodeAcquire.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecAcquire.
Require Import ProcGeom.
Import Defs.

(* ---- the sext.w round-trip on the amoswap result (acquire +0x20) ---- *)
Lemma aq_wrap_signed (n : N) (b : bv n) : bv_wrap n (bv_signed b) = bv_unsigned b.
Proof.
  unfold bv_signed, bv_swrap, bv_wrap.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned b + bv_half_modulus n - bv_half_modulus n) with (bv_unsigned b) by lia.
  apply Z.mod_small. apply bv_unsigned_in_range.
Qed.

Lemma aq_loaded_sext (x : mword 32) : amoswap_loaded x = sign_extend' 64 x.
Proof. unfold amoswap_loaded. f_equal; try (exact (autocast_id 32 x)). Qed.

Lemma aq_subrange_sext (x : mword 32) :
  subrange_vec_dec (sign_extend' 64 x) 31 0 = x.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec.
  unfold to_word_idx, to_word, get_word.
  rewrite MachineWord.cast_idx_refl.
  unfold MachineWord.slice.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0.
  rewrite Z.shiftr_0_r.
  unfold sign_extend', Operators_mwords.sign_extend, Operators_mwords.exts_vec,
    SailStdpp.Values.to_word, to_word, get_word, MachineWord.sign_extend.
  rewrite bv_sign_extend_unsigned.
  rewrite bv_wrap_bv_wrap; [| vm_compute; intro Hc; discriminate Hc].
  apply aq_wrap_signed.
Qed.

Lemma aq_sextw_round (x : mword 32) :
  sign_extend' 64 (subrange_vec_dec (add_vec (amoswap_loaded x)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)
  = sign_extend' 64 x.
Proof.
  replace (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))) with (mword_of_int 0 : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite kv_addv_zero.
  rewrite aq_loaded_sext.
  rewrite aq_subrange_sext.
  reflexivity.
Qed.


Module AcquireGenProof (Mycpu : MYCPU) (Holding : HOLDING) (PushOff : PUSHOFF) : ACQUIRE_GEN.

Section ProofAcquire.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The amoswap spin loop (KernelSyms.acquire+0x1a..0x22) over the funnel leaves: a      *)
  (* genuine Löb loop -- the c.bnez back edge hands its step's later out. *)
  (* ------------------------------------------------------------------- *)
  (* Entirely within the interrupts-OFF region push_off has already opened
     (b = false throughout: no hart ever moves here), so this private helper
     -- unlike the sealed [wp_acquire_gen_sconf] below -- is stated directly
     at literal [false], with no [wp_next] binder at all (the "M-mode /
     interrupts-off" convention).  Every leaf call below is at [b := false]
     and closes its own [wp_next false (...)] obligation with [rewrite
     wp_next_off], after which the surviving proof script is BYTE-IDENTICAL
     to the pre-port shape -- the one new line per leaf, per the porting
     guide's "consumer side" recipe. *)
  Lemma wp_acquire_lock_loop_sconf `{CID0 : CpuId}
      (γl : gname) (s : string) (R Tc Dc : iProp Σ)
      (M0 : regfile) (n : nat) (a5v lk : mword 64) (p : mword 64) :
    let a4one : mword 64 := add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) in
    M0 !!! Regidx (mword_of_int 14 : mword 5) = a4one ->
    M0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk ->
    (⊢ Tc -∗ Dc -∗ False) ->
    sie_cap_gpr (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) n false p -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.acquire + 0x1a)) -∗
    lock_openable γl lk s R Dc -∗
    Tc -∗
    ( Tc -∗
      sie_cap_gpr (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0) n false p -∗
      pc_is (mword_of_int (KernelSyms.acquire + 0x24)) -∗
      locked_pre γl cpu_id -∗ R -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros a4one HM0a4 HM0s1 Href.
    assert (Ha4any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 14 : mword 5) = a4one).
    { intro w. rewrite upd_ne; [ exact HM0a4 | vm_compute; discriminate ]. }
    assert (Hs1any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { intro w. rewrite upd_ne; [ exact HM0s1 | vm_compute; discriminate ]. }
    assert (HAlk2 : add_vec (add_vec zero_reg lk) (zeros' 64) = lk).
    { rewrite add_vec_zero_l.
      replace (zeros' 64 : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    set (v1 := add_vec zero_reg a4one).
    assert (Hst1 : amoswap_stored v1 = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.acquire + 0x22) : mword 64)
              (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.acquire + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iIntros "Hcg #Htext Hpc #Hlock HTc Hcont".
    iPoseProof (aqi_1a with "Htext") as "#Hj1a".
    iPoseProof (aqi_1c with "Htext") as "#Hj1c".
    iPoseProof (aqi_20 with "Htext") as "#Hj20".
    iPoseProof (aqi_22 with "Htext") as "#Hj22".
    iRevert "Hcg Hpc HTc Hcont".
    iLöb as "IH" forall (a5v).
    iIntros "Hcg Hpc HTc Hcont".
    (* ---- +0x1a: c.mv a5,a4 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquire + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hj1a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite (Ha4any a5v) upd_upd) in "Hcg".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.acquire + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: amoswap.w.aq a5,a5,(s1) through the invariant ---- *)
    assert (HPAlk : add_vec ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                              !!! Regidx (mword_of_int 9 : mword 5)) (zeros' 64) = lk)
      by (rewrite (Hs1any v1); exact HAlk2).
    assert (HSTZ : neq_vec (sign_extend' 64 (amoswap_stored
                     ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                        !!! Regidx (mword_of_int 15 : mword 5)))) zero_reg = true)
      by (rewrite upd_eq Hst1; vm_compute; reflexivity).
    iApply (wp_amoswap_lockopen_s_sconf γl lk s R Tc Dc (mword_of_int (KernelSyms.acquire + 0x1c)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 9)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0) n false
              HPAlk HSTZ
              ltac:(vm_compute; discriminate) ltac:(rdok) Href
              with "Hcg Hpc Hj1c Hlock HTc").
    iIntros (w). iApply wp_next_off_intro.
    iIntros "HTc Hcg Hpc Hpay".
    iEval (rewrite upd_upd) in "Hcg".
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.acquire + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- +0x20: sext.w a5 ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.acquire + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (amoswap_loaded w)]> M0) n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hj20").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite upd_eq upd_upd) in "Hcg".
    assert (Hroundw : sign_extend' 64 (subrange_vec_dec
        (add_vec (amoswap_loaded w) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)
        = sign_extend' 64 w) by (apply aq_sextw_round).
    iEval (rewrite Hroundw) in "Hcg".
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iDestruct "Hpay" as "[(%Hw0 & Htokp & HRes) | %Hwnz]".
    - (* ---- w = 0: ACQUIRED -- c.bnez falls through ---- *)
      subst w.
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.acquire + 0x22)) (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0) n false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite upd_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hj22").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      iApply ("Hcont" with "HTc Hcg Hpc Htokp HRes").
    - (* ---- w <> 0: c.bnez TAKEN back; Löb ---- *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.acquire + 0x22)) (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 w)]> M0) n false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite upd_eq; exact Hwnz)
                ltac:(rewrite Htgt; vm_compute; reflexivity)
                with "Hcg Hpc Hj22").
      iApply wp_next_off_intro.
      iNext.
      iIntros "Hcg Hpc".
      iEval (rewrite Htgt) in "Hpc".
      iApply ("IH" $! (sign_extend' 64 w)
                with "Hcg Hpc HTc Hcont").
  Qed.

  (* THE FRESH TIER, and the only thing proved here: [Hfresh : s ∉ lks] is
     exactly what the held-set insert consumes, and nothing in the run below
     looks at a rank.  The BELOW tier is a corollary (next lemma); see
     SpecAcquire.v's header for why the order is policy rather than a proof
     obligation.  [Hfresh] now does DOUBLE DUTY: it also decides the
     [if(holding(lk)) panic] check, so neither tier carries a panic
     credential any more. *)
  Lemma wp_acquire_gen_fresh_sconf
      (γl : gname) (s : string) (R Tc Dc : iProp Σ)
      (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string)
    : wp_acquire_gen_fresh_sconf_body γl s R Tc Dc m n eb p av b lks.
  Proof.
    cbv beta delta [wp_acquire_gen_fresh_sconf_body wp_acquire_gen_pre_body].
    intros pcE lk0 ret_tgt Hpos Hav Hfresh Href Hrefpre.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hown #Htext Hpc #Hlock HTc Hcont".
    (* THE ENTRY BOUND, taken before push_off raises the level: after the push
       the bundle offers only [size lks <= S n], one too weak to add a rank.
       It is pure, so it survives the push in the Coq context. *)
    iDestruct (cpu_own_size_le with "Hown") as "[%Hszlks Hown]".
    iPoseProof (aqi_00 with "Htext") as "Hi00".
    iPoseProof (aqi_02 with "Htext") as "Hi02".
    iPoseProof (aqi_04 with "Htext") as "Hi04".
    iPoseProof (aqi_06 with "Htext") as "Hi06".
    iPoseProof (aqi_08 with "Htext") as "Hi08".
    iPoseProof (aqi_0a with "Htext") as "Hi0a".
    iPoseProof (aqi_0c with "Htext") as "Hi0c".
    (* ---- 0x00: c.addi sp,-32 -- the frame trade (k := 4) ---- *)
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
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquire + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 b
              with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquire + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 b
              with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.acquire + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 b
              with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.acquire + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.acquire + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquire + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.acquire + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- 0x0c: jal ra,push_off ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquire + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fffba : mword 21)
              A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquire + 0x0c) : mword 64) 4)]> A2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquire + 0x0c) : mword 64) 4)]> A2) with A3.
    assert (Hpcpo : add_vec (mword_of_int (KernelSyms.acquire + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fffba : mword 21))
                    = mword_of_int KernelSyms.push_off) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcpo) in "Hpc".
    (* ---- push_off(): the flip -- the interrupts-off region begins.
       [Hown : cpu_own n eb p C b] was introduced at this function's ENTRY
       hart; the seven plain instructions above each threaded through a
       FRESH, universally quantified hart (CID1..CID7), so push_off wants it
       at CID7.  [cpu_own_transport] moves it there, no case split on [b]. ---- *)
    assert (HcspA3 : A3 !!! Regidx csp_rs1 = spd).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    iDestruct (cpu_own_transport CID CID7 n eb p b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (PushOff.wp_push_off_sconf A3 (av - 4)%nat n eb p b _
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hown Htext Hpc").
    iIntros (CIDpo Hspo ms mp) "%Hmsf Hcg Hown Hpay Hpc %Hmp".
    destruct Hmp as (Hcspp & Hs0p & Hs1p & Hs2p & Hs3p & Hs4p & Hs5p & Hs6p & Hs7p & Hs8p & Hs9p & Hs10p & Hs11p).
    (* ===== from here on b = false LITERALLY (push_off's own flip) and the
       hart is pinned at CIDpo for the rest of the function: every remaining
       [wp_next false (...)] collapses with [wp_next_off], so the proof below
       reads exactly as it did before this port, plus that one new line per
       leaf ("consumer side" recipe). ===== *)
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc10 : ret_pc (add_vec_int (mword_of_int (KernelSyms.acquire + 0x0c) : mword 64) 4)
                    = (mword_of_int (KernelSyms.acquire + 0x10) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.mv a0,s1 ---- *)
    iPoseProof (aqi_10 with "Htext") as "Hi10".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.acquire + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mp (trap_res b + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 9 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 9 : mword 5)))]> mp) with B1.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* s1 still carries the lock base through push_off *)
    assert (Hs1mp : mp !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk0).
    { rewrite Hs1p /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_eq /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HB1a0 : B1 !!! Regidx (mword_of_int 10 : mword 5) = add_vec zero_reg (add_vec zero_reg lk0)).
    { rewrite /B1 upd_eq Hs1mp. reflexivity. }
    (* ---- 0x12: jal ra,holding ---- *)
    iPoseProof (aqi_12 with "Htext") as "Hi12".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.acquire + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff88 : mword 21)
              B1 (trap_res b + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquire + 0x12) : mword 64) 4)]> B1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.acquire + 0x12) : mword 64) 4)]> B1) with B2.
    assert (Hpchd : add_vec (mword_of_int (KernelSyms.acquire + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff88 : mword 21))
                    = mword_of_int KernelSyms.holding) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpchd) in "Hpc".
    (* ---- holding(): not mine -> a0 := 0 ---- *)
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5) = add_vec zero_reg (add_vec zero_reg lk0))
      by (rewrite /B2 upd_ne; [exact HB1a0 | vm_compute; discriminate]).
    assert (HcspB2 : B2 !!! Regidx csp_rs1 = spd).
    { rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hcspp. exact HcspA3. }
    assert (Hlkb : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk0).
    { rewrite HB2a0 !add_vec_zero_l.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* THE EVIDENCE THAT KILLS THE PANIC ARM.  holding() decides its answer
       by reading [lk->cpu] inside the lock invariant, and the invariant's
       held state keeps [lk_in i s] beside that word (WpLock.v).  So this
       hart's own held-set authority -- which is sitting inside [cpu_own],
       and which [Hfresh] says omits [s] -- refutes [i = cpu_id]: the word is
       not this hart's [struct cpu], and holding() returns 0.  The authority
       is handed over and comes straight back; [cpu_own] is rebuilt at the
       SAME set, so nothing else in this proof notices. *)
    iDestruct (cpu_own_locks_swap with "Hown") as "[Hlks [%Hsz0 Hownback0]]".
    iApply (Holding.wp_holding_lockinv_s_sconf γl lk0 s R Tc Dc B2 (trap_res b + (av - 4))%nat p lks
              Hlkb ltac:(lia) Hfresh Href
              with "Hcg Htext Hpc Hlock HTc Hlks").
    iIntros (mh) "HTc Hlks Hcg Hpc %Hmh".
    iDestruct ("Hownback0" $! lks ltac:(exact Hsz0) with "Hlks") as "Hown".
    destruct Hmh as [Hcsh Ha0h].
    destruct Hcsh as (Hcsph & Hs0h & Hs1h & Hs2h & Hs3h & Hs4h & Hs5h & Hs6h & Hs7h & Hs8h & Hs9h & Hs10h & Hs11h).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc16 : ret_pc (add_vec_int (mword_of_int (KernelSyms.acquire + 0x12) : mword 64) 4)
                    = (mword_of_int (KernelSyms.acquire + 0x16) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: c.li a4,1 ---- *)
    iPoseProof (aqi_16 with "Htext") as "Hi16".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.acquire + 0x16)) (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) mh (trap_res b + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi16").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mh).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mh) with B3.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* ---- 0x18: c.bnez a0 -- holding()'s answer decides which arm runs ---- *)
    iPoseProof (aqi_18 with "Htext") as "Hi18".
    assert (HB3a0v : B3 !!! Regidx (mword_of_int 10 : mword 5)
                     = mh !!! Regidx (mword_of_int 10 : mword 5))
      by (rewrite /B3 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Htgt34 : add_vec (mword_of_int (KernelSyms.acquire + 0x18) : mword 64)
              (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.acquire + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    (* holding() returned 0 -- PROVABLY, [Ha0h] -- so the [c.bnez] at +0x18
       falls through and the [jal panic] at +0x3c is DEAD CODE.  There is no
       second arm to close and no panic credential in this contract; see
       SpecAcquire.v's header. *)
    (* ===== holding() said 0: the c.bnez falls through to the loop ===== *)
    assert (Ha0B3 : neq_vec (B3 !!! Regidx (mword_of_int 10 : mword 5)) zero_reg = false).
    { rewrite HB3a0v Ha0h. vm_compute. reflexivity. }
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.acquire + 0x18)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              B3 (trap_res b + (av - 4))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rgne; exact Ha0B3)
              with "Hcg Hpc Hi18").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.acquire + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a..0x22: the test-and-set loop ---- *)
    assert (HB3a4 : B3 !!! Regidx (mword_of_int 14 : mword 5)
                    = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (rewrite /B3; apply upd_eq).
    assert (HB3s1 : B3 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk0).
    { rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs1h /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      exact Hs1mp. }
    assert (Hupd_id : forall (f : regfile) (k : regidx), <[k := regval_into_reg (f !!! k)]> f = f).
    { intros f k. apply functional_extensionality; intro j.
      unfold insert, regfile_insert, rf_upd, regval_into_reg, lookup_total, regfile_lookup_total.
      case_bool_decide as Heq; [subst; reflexivity | reflexivity]. }
    iApply (wp_acquire_lock_loop_sconf γl s R Tc Dc B3 (trap_res b + (av - 4))%nat (B3 !!! Regidx (mword_of_int 15 : mword 5)) lk0 p
              HB3a4 HB3s1 Href
              with "[Hcg] Htext Hpc Hlock HTc").
    { rewrite (Hupd_id B3 (Regidx (mword_of_int 15 : mword 5))). iExact "Hcg". }
    iIntros "HTc Hcg Hpc Htokp HRes".
    set (B8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> B3).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> B3) with B8.
    (* ---- 0x24: jal ra,mycpu ---- *)
    assert (HcspB8 : B8 !!! Regidx csp_rs1 = spd).
    { rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hcsph. exact HcspB2. }
    iPoseProof (aqi_24 with "Htext") as "Hi24".
    iApply (Mycpu.wp_call_mycpu_sconf_cs (mword_of_int (KernelSyms.acquire + 0x24)) (mword_of_int 0xcdc : mword 21) B8 (trap_res b + (av - 4))%nat p
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi24").
    iIntros (mo) "Hcg Hpc %Hmo".
    set (Cm := mo) in *.
    destruct Hmo as [Hcso Hmo_a0].
    destruct Hcso as (Hcspo & Hs0o & Hs1o & Hs2o & Hs3o & Hs4o & Hs5o & Hs6o & Hs7o & Hs8o & Hs9o & Hs10o & Hs11o).
    assert (Ha0C : Cm !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret cid_word)
      by (rewrite Hmo_a0; exact (f_equal mycpu_ret (rget_tp B8))).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc28 : ret_pc (add_vec_int (mword_of_int (KernelSyms.acquire + 0x24) : mword 64) 4)
                    = (mword_of_int (KernelSyms.acquire + 0x28) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.sd a0,16(s1) : lk->cpu := mycpu ---- *)
    assert (Hs1C : Cm !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk0).
    { rewrite Hs1o /B8 upd_ne; [| vm_compute; discriminate].
      exact HB3s1. }
    assert (Hpacpu : add_vec (Cm !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = lock_cpu lk0).
    { rewrite Hs1C add_vec_zero_l. reflexivity. }
    iPoseProof (aqi_28 with "Htext") as "Hi28".
    (* [wp_csd_lkcpu_lockopen_s_sconf] (WpSconfLock.v) demands the dead-state
       refutation at ITS OWN ambient hart -- [h0 := cpu_id], resolved where
       the leaf is APPLIED, i.e. [CIDpo] here (the hart push_off's own
       migration handed back).  With [Hrefpre] now ∀-hart (SpecAcquire.v's
       Fix 1), instantiating it at the ambient [cpu_id] gives exactly the
       credential this leaf wants, at no cost to [AcquireOfGen] below
       ([lock_refute_False] is hart-generic already). *)
    (* THE SET-ADDING INSTRUCTION.  The hart's held-lock set is hidden inside
       [cpu_own] (IntrDefs.cpu_hart), so it is opened HERE, handed to the
       leaf, and put back with [lock_rank s] in it.  The set is now an INDEX
       of [cpu_own], so it is NAMED here rather than opened existentially --
       [cpu_own_locks_swap] takes the authority out at [lks] and puts back the
       one the leaf returns.  The [s ∉ lks] obligation is [Hfresh],
       the caller's own premise; the predecessor derived it from the cpu field
       instead (see WpLock.v's owner-field block). *)
    iDestruct (cpu_own_locks_swap with "Hown") as "[Hlks [%Hsz Hownback]]".
    iApply (wp_csd_lkcpu_lockopen_s_sconf γl lk0 s R Dc (mword_of_int (KernelSyms.acquire + 0x28))
              (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 16 : mword 12) Cm (trap_res b + (av - 4))%nat false lks
              Hpacpu Ha0C Hfresh (Hrefpre cpu_id)
              with "Hcg Hpc Hi28 Hlock Htokp Hlks").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Htok Hlks".
    (* [size ({[rank s]} ∪ lks) = S (size lks) <= S n] -- the entry bound plus
       the freshness premise.  [size_add] is proved at an abstract rank so no
       [set_solver] meets [lock_rank] here. *)
    iDestruct ("Hownback" $! ({[s]} ∪ lks)
                 ltac:(exact (size_add_le s lks n Hfresh Hszlks)) with "Hlks") as "Hown".
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.acquire + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a/0x2c/0x2e: c.ldsp ra/s0/s1 ---- *)
    assert (HcspC : Cm !!! Regidx csp_rs1 = spd) by (rewrite Hcspo; exact HcspB8).
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    iPoseProof (aqi_2a with "Htext") as "Hi2a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquire + 0x2a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              Cm (trap_res b + (av - 4))%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hr24]").
    { iEval (rewrite HcspC). iExact "Hr24". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> Cm).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> Cm) with E1.
    assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.acquire + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact HcspC | vm_compute; discriminate]).
    iPoseProof (aqi_2c with "Htext") as "Hi2c".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquire + 0x2c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (trap_res b + (av - 4))%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hr16]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.acquire + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    iPoseProof (aqi_2e with "Htext") as "Hi2e".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.acquire + 0x2e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (trap_res b + (av - 4))%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [Hr8]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* ---- 0x30: c.addi16sp sp,32 -- the frame trade back ---- *)
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
    iPoseProof (aqi_30 with "Htext") as "Hi30".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HcspC). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.acquire + 0x30)) (mword_of_int 2 : mword 6) E3 (trap_res b + (av - 4))%nat 4 false Hpop
              with "Hcg Hpc Hi30 Hframe4").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((trap_res b + (av - 4)) + 4)%nat = (trap_res b + av)%nat) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc32 : add_vec_int (mword_of_int (KernelSyms.acquire + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.acquire + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc32) in "Hpc".
    (* ---- 0x32: c.ret ---- *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (aqi_32 with "Htext") as "Hi32".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.acquire + 0x32)) (mword_of_int 1 : mword 5) E4 (trap_res b + av)%nat false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi32").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (E4 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    (* [Hcont]'s [wp_next] is indexed at the ENTRY [b] (acquire is
       UNBALANCED, per SpecAcquire.v's comment); the composed chain
       Hs1..Hs7 (the seven pre-push_off leaf hops) plus [Hspo] (push_off's
       own conditional equality) gets us there via [wp_next_chain], with no
       case split on [b]. *)
    iSpecialize ("Hcont" $! CIDpo with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! ms E4 with "[%] HTc Hcg Hpc [%] Htok HRes Hown Hpay").
    { exact Hmsf. }
    (* [s0]/[s1] never surface as separate goals below: each is restored by
       an epilogue [ldsp] as the LITERAL value [m !!! reg] (the leaf's own
       [wval] argument), so [E4 !!! 8 = m !!! 8] / [E4 !!! 9 = m !!! 9] are
       convertible outright and [repeat split] -- which is [constructor 1],
       i.e. tries [eq_refl] on each leaf -- discharges them silently before
       ever producing a bullet (the gotcha recorded in durable-notes.md's
       "repeat split CLOSES a convertible equality" entry).  Only [sp]
       (a real computation, not a bare reload) and [s2..s11] (threaded
       through the push_off/holding/mycpu sub-calls) reach the tactic. *)
    unfold callee_saved. repeat split.
    + rewrite HE4sp. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs2o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs2h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs2p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs3o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs3h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs3p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs4o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs4h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs4p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs5o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs5h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs5p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs6o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs6h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs6p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs7o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs7h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs7p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs8o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs8h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs8p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs9o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs9h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs9p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs10o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs10h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs10p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs11o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs11h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs11p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
  Qed.

  (* THE BELOW TIER, as a corollary: the contract is antitone in its held-set
     precondition and [locks_below lks s] implies [s ∉ lks]. *)
  Lemma wp_acquire_gen_sconf
      (γl : gname) (s : string) (R Tc Dc : iProp Σ)
      (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string)
    : wp_acquire_gen_sconf_body γl s R Tc Dc m n eb p av b lks.
  Proof.
    exact (wp_acquire_gen_pre_weaken γl s R Tc Dc m n eb p av b lks
             (s ∉ lks) (locks_below lks s) (locks_below_not_elem lks s)
             (wp_acquire_gen_fresh_sconf γl s R Tc Dc m n eb p av b lks)).
  Qed.

End ProofAcquire.

End AcquireGenProof.

(* The static-kernel-lock instance: no credential, no disposal.  This is the
   verbatim statement the thirteen [ACQUIRE] consumers were written against. *)
Module AcquireOfGen (G : ACQUIRE_GEN) : ACQUIRE.

Section OfGen.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* The [Tc := emp] / [Dc := False] instantiation is PREMISE-AGNOSTIC, so it
     is done once, at the FRESH tier, and the BELOW tier follows by the same
     weakening as at the generic level.  Doing it the other way round would
     make this fifteen-line script a cross-product. *)
  Lemma wp_acquire_fresh_sconf
      (γl : gname) (s : string) (R : iProp Σ)
      (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool)
      (lks : gset string)
    : wp_acquire_fresh_sconf_body γl s R m n eb p av b lks.
  Proof.
    cbv beta delta [wp_acquire_fresh_sconf_body wp_acquire_pre_body].
    intros pcE lk0 ret_tgt Hpos Hav Hfresh.
    iIntros "Hcg Hown #Htext Hpc #Hlock Hcont".
    iApply (G.wp_acquire_gen_fresh_sconf γl s R emp%I False%I m n eb p av b lks
              Hpos Hav Hfresh (lock_refute_False _) (fun i => lock_refute_False _)
              with "Hcg Hown Htext Hpc [] []").
    { iApply (is_lock_openable with "Hlock"). }
    { done. }
    iIntros (CIDg Hsg ms mfin) "%Hms _ Hcg Hpc %Hcs Htok HRes Hown Hpay".
    iSpecialize ("Hcont" $! CIDg with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! ms mfin with "[//] Hcg Hpc [//] Htok HRes Hown Hpay").
  Qed.

  Lemma wp_acquire_sconf
      (γl : gname) (s : string) (R : iProp Σ)
      (m : regfile)
      (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool)
      (lks : gset string)
    : wp_acquire_sconf_body γl s R m n eb p av b lks.
  Proof.
    exact (wp_acquire_pre_weaken γl s R m n eb p av b lks
             (s ∉ lks) (locks_below lks s) (locks_below_not_elem lks s)
             (wp_acquire_fresh_sconf γl s R m n eb p av b lks)).
  Qed.

End OfGen.

End AcquireOfGen.
