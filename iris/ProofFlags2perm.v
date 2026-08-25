(* ProofFlags2perm.v -- the whole-function WP for flags2perm() (kernel/exec.c),
   a sixteen-instruction leaf with the standard 2-slot ra/s0 frame, one branch
   and no callees.  The contract is SpecFlags2perm.v; the decode facts are the
   generated CodeFlags2perm.v ([fpi_<off>]).

     +0x00  c.addi     sp,sp,-16      the 2-slot frame push
     +0x02  c.sdsp     ra,8(sp)
     +0x04  c.sdsp     s0,0(sp)
     +0x06  c.addi4spn s0,sp,16
     +0x08  c.mv       a5,a0          keep the raw flags in a5
     +0x0a  slliw      a0,a0,0x3      a0 = sext32(flags << 3)
     +0x0e  c.andi     a0,a0,8        a0 = 8 * bit0(flags)
     +0x10  c.andi     a5,a5,2
     +0x12  c.beqz     a5,+0x18       skip the [| PTE_W] when bit1 is clear
     +0x14  ori        a0,a0,4
     +0x18  c.ldsp     ra,8(sp)
     +0x1a  c.ldsp     s0,0(sp)
     +0x1c  c.addi     sp,sp,16
     +0x1e  c.jr       ra

   THE PROOF IS [b]-GENERIC, so every leaf's [wp_next] obligation is met with
   [iIntros (CIDk Hsk)] rather than collapsed: the hart may move at any step.
   Nothing this function holds is per-hart except [sie_cap_gpr] itself, which
   each leaf hands back at the hart it landed on, so the only bookkeeping is
   the guard chain (discharged by [wp_next_chain] at the return) and the rule
   that any [rget]-shaped fact must be stated FOR ALL HARTS -- the hart a fresh
   [assert] resolves to need not be the one the use site's resource is at
   (durable-notes; ProofInitlock.v is the same shape).

   THE BRANCH AND THE SHARED EPILOGUE.  The two arms of the [c.beqz] reconverge
   at +0x18, so the epilogue is proved ONCE, as a [wp_next]-quantified "TAIL"
   assertion built just before the branch and consumed by whichever arm runs.
   It is quantified over the register map [MM] the arm arrives with, plus three
   pure facts about it (sp is still the pushed frame pointer, a0 is the answer,
   and nothing callee-saved moved); the [wp_next] wrapper is what lets the arm
   supply it at ITS hart, exactly as ProofUvmunmap.v's "TAIL" does.

   THE ARITHMETIC IS FOUR PURE LEMMAS AT THE TOP OF THE FILE, deliberately kept
   out of the WP context: [z_land_pow2] (masking with a single bit reads that
   bit), [f2p_shift_bit] (the slliw result's bit 3 is the source's bit 0),
   [f2p_andi8] / [f2p_andi2] (the two [andi]s, as literals in the two bits) and
   [f2p_bz_taken] / [f2p_bz_fall] (the branch condition read as bit 1). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import HartTp WpNext IntrDefs.
Require Import StackOwn CalleeSaved.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecFlags2perm.
Require Import CodeFlags2perm.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  THE PURE ARITHMETIC.  Stated here, where the context is two           *)
(*  hypotheses wide, and never inside the WP (durable-notes).             *)
(* ===================================================================== *)

(* masking with a one-bit constant reads that bit *)
Local Lemma z_land_pow2 (z k : Z) : 0 <= k ->
  Z.land z (2 ^ k) = if Z.testbit z k then 2 ^ k else 0.
Proof.
  intros Hk.
  destruct (Z.testbit z k) eqn:Hb; apply Z.bits_inj'; intros n Hn;
    rewrite Z.land_spec (Z.pow2_bits_eqb k n Hk).
  - destruct (Z.eqb_spec k n); [subst; rewrite Hb; reflexivity | apply andb_false_r].
  - rewrite Z.bits_0.
    destruct (Z.eqb_spec k n); [subst; rewrite Hb; reflexivity | apply andb_false_r].
Qed.

(* a signed wrap is invisible below the width, exactly as an unsigned one is *)
Local Lemma zbit_swrap_low (n : N) (z i : Z) :
  0 <= i < Z.of_N n -> Z.testbit (bv_swrap n z) i = Z.testbit z i.
Proof.
  intros Hi.
  rewrite -(bv_wrap_spec_low n (bv_swrap n z) i Hi).
  rewrite bv_wrap_swrap.
  apply bv_wrap_spec_low. exact Hi.
Qed.

(* [slliw a0,a0,3]: bit 3 of the result is bit 0 of the argument.  Both the
   32-bit truncation the W-form does and the sign extension back to 64 are
   invisible at bit 3, which is why flags2perm needs no range premise on its
   [int] argument. *)
Local Lemma f2p_shift_bit (fl : mword 64) :
  Z.testbit (bv_unsigned
     (sign_extend' 64 (shift_bits_left (subrange_vec_dec fl 31 0 : mword 32)
                         (mword_of_int 3 : mword 5)) : mword 64)) 3
  = Z.testbit (bv_unsigned fl) 0.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  rewrite (bv_wrap_spec_low 64 _ 3 ltac:(lia)).
  unfold bv_signed.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite (zbit_swrap_low 32 _ 3 ltac:(lia)).
  cbv [shift_bits_left Operators_mwords.shiftl SailStdpp.Values.with_word to_word get_word].
  unfold MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  match goal with
  | |- context [ Z.shiftl _ ?k ] => replace k with 3 by (vm_compute; reflexivity)
  end.
  rewrite (bv_wrap_spec_low 32 _ 3 ltac:(lia)).
  rewrite (Z.shiftl_spec _ 3 3 ltac:(lia)).
  change (3 - 3) with 0.
  rewrite subrange_31_0_unsigned.
  replace 4294967296 with (2 ^ 32) by (vm_compute; reflexivity).
  rewrite Z.mod_pow2_bits_low; [reflexivity | lia].
Qed.

(* +0x0e [c.andi a0,a0,8] on the slliw result: 8 * bit0(fl) *)
Local Lemma f2p_andi8 (fl : mword 64) :
  and_vec (sign_extend' 64 (shift_bits_left (subrange_vec_dec fl 31 0 : mword 32)
                              (mword_of_int 3 : mword 5)) : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))
  = (mword_of_int (if Z.testbit (bv_unsigned fl) 0 then 8 else 0) : mword 64).
Proof.
  apply bv_eq. rewrite and_vec64_unsigned.
  replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)) : mword 64))
    with (2 ^ 3) by (vm_compute; reflexivity).
  rewrite (z_land_pow2 _ 3 ltac:(lia)).
  rewrite f2p_shift_bit.
  destruct (Z.testbit (bv_unsigned fl) 0); vm_compute; reflexivity.
Qed.

(* +0x10 [c.andi a5,a5,2] on the raw argument: 2 * bit1(fl) *)
Local Lemma f2p_andi2 (fl : mword 64) :
  and_vec fl (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))
  = (mword_of_int (if Z.testbit (bv_unsigned fl) 1 then 2 else 0) : mword 64).
Proof.
  apply bv_eq. rewrite and_vec64_unsigned.
  replace (bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)) : mword 64))
    with (2 ^ 1) by (vm_compute; reflexivity).
  rewrite (z_land_pow2 _ 1 ltac:(lia)).
  destruct (Z.testbit (bv_unsigned fl) 1); vm_compute; reflexivity.
Qed.

(* +0x14 [ori a0,a0,4] -- applied to the four-valued andi result, so a plain
   case split closes it. *)
Local Lemma f2p_ori4 (c : Z) : c = 0 \/ c = 8 ->
  or_vec (mword_of_int c : mword 64) (sign_extend' 64 (mword_of_int 4 : mword 12))
  = (mword_of_int (c + 4) : mword 64).
Proof. intros [-> | ->]; apply bv_eq; vm_compute; reflexivity. Qed.

(* the [c.beqz a5] condition, read as bit 1 of the argument *)
Local Lemma f2p_bz_taken (fl : mword 64) :
  Z.testbit (bv_unsigned fl) 1 = false ->
  eq_vec (and_vec fl (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = true.
Proof. intro H. rewrite f2p_andi2. rewrite H. vm_compute. reflexivity. Qed.

Local Lemma f2p_bz_fall (fl : mword 64) :
  Z.testbit (bv_unsigned fl) 1 = true ->
  eq_vec (and_vec fl (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false.
Proof. intro H. rewrite f2p_andi2. rewrite H. vm_compute. reflexivity. Qed.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]).  Written
   name-free (durable-notes: an Ltac body cannot mention a hypothesis by
   literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module Flags2permProof : FLAGS2PERM.

Section ProofFlags2perm.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_flags2perm_sconf
      (mm : regfile) (K : nat) (b : bool) (p : mword 64)
    : wp_flags2perm_sconf_body mm K b p.
  Proof.
    cbv beta delta [wp_flags2perm_sconf_body].
    intros pcE fl ret_tgt HK.
    
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec (mm !!! Regidx csp_rs1 : mword 64)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    (* the two frame cells, and the entry values the epilogue restores *)
    pose (vra := (mm !!! Regidx (mword_of_int 1 : mword 5) : mword 64)).
    pose (vs0 := (mm !!! Regidx (mword_of_int 8 : mword 5) : mword 64)).
    iIntros "Hcg #Htext Hpc Hcont".
    (* ===== PROLOGUE ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* +0x00 c.addi sp,sp,-16 *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) mm K 2 b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (fpi_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm)
      with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vr8) "Hras". iDestruct "S2" as (vr0) "Hs0s".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hras". iEval (rewrite -Hb2) in "Hs0s".
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (KernelSyms.flags2perm + 0x02))
      by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* the four register reads this proof needs, ALL HARTS (durable-notes) *)
    assert (Hrg1 : forall (CIDx : CpuId) (M : regfile),
              rget (CID := CIDx) M (mword_of_int 1 : mword 5) = M !!! Regidx (mword_of_int 1 : mword 5))
      by (intros CIDx M; rgne; reflexivity).
    assert (Hrg8 : forall (CIDx : CpuId) (M : regfile),
              rget (CID := CIDx) M (mword_of_int 8 : mword 5) = M !!! Regidx (mword_of_int 8 : mword 5))
      by (intros CIDx M; rgne; reflexivity).
    assert (Hrg10 : forall (CIDx : CpuId) (M : regfile),
              rget (CID := CIDx) M (mword_of_int 10 : mword 5) = M !!! Regidx (mword_of_int 10 : mword 5))
      by (intros CIDx M; rgne; reflexivity).
    assert (Hrg15 : forall (CIDx : CpuId) (M : regfile),
              rget (CID := CIDx) M (mword_of_int 15 : mword 5) = M !!! Regidx (mword_of_int 15 : mword 5))
      by (intros CIDx M; rgne; reflexivity).
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x02))
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vr8 b with "Hcg Hpc [] [Hras]").
    { iApply (fpi_02 with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hras". }
    iIntros (CID2 Hs2) "Hcg Hpc Hras".
    iEval (rewrite HspR1) in "Hras".
    iEval (rewrite Hrg1) in "Hras".
    assert (HR1ra : R1 !!! Regidx (mword_of_int 1 : mword 5) = vra)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : R1 !!! Regidx (mword_of_int 8 : mword 5) = vs0)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HR1ra) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.flags2perm + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x04))
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vr0 b with "Hcg Hpc [] [Hs0s]").
    { iApply (fpi_04 with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hs0s". }
    iIntros (CID3 Hs3) "Hcg Hpc Hs0s".
    iEval (rewrite HspR1) in "Hs0s".
    iEval (rewrite Hrg8) in "Hs0s".
    iEval (rewrite HR1s0) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.flags2perm + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fpi_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1)
      with R2.
    assert (HspR2 : R2 !!! Regidx csp_rs1 = spr)
      by (rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]).
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = fl).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.flags2perm + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.mv a5,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x08))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              R2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fpi_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rewrite Hrg10) in "Hcg".
    iEval (rewrite HR2a0) in "Hcg".
    iEval (rewrite add_vec_zero_l) in "Hcg".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg fl]> R2).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg fl]> R2) with R3.
    assert (HspR3 : R3 !!! Regidx csp_rs1 = spr)
      by (rewrite /R3 upd_ne; [exact HspR2 | vm_compute; discriminate]).
    assert (HR3a0 : R3 !!! Regidx (mword_of_int 10 : mword 5) = fl)
      by (rewrite /R3 upd_ne; [exact HR2a0 | vm_compute; discriminate]).
    assert (HR3a5 : R3 !!! Regidx (mword_of_int 15 : mword 5) = fl)
      by (rewrite /R3 upd_eq; reflexivity).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.flags2perm + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a slliw a0,a0,3 *)
    set (wsl := sign_extend' 64 (shift_bits_left (subrange_vec_dec fl 31 0 : mword 32)
                                   (mword_of_int 3 : mword 5)) : mword 64).
    assert (Hsl : forall CIDx : CpuId,
              sign_extend' 64 (shift_bits_left
                (subrange_vec_dec (rget (CID := CIDx) R3 (mword_of_int 10 : mword 5)) 31 0 : mword 32)
                (mword_of_int 3 : mword 5)) = wsl).
    { intros CIDx. rewrite Hrg10. rewrite HR3a0. reflexivity. }
    iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x0a))
              (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 3 : mword 5) wsl R3 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) (Hsl _)
              with "Hcg Hpc []").
    { iApply (fpi_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg wsl]> R3).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg wsl]> R3) with R4.
    assert (HspR4 : R4 !!! Regidx csp_rs1 = spr)
      by (rewrite /R4 upd_ne; [exact HspR3 | vm_compute; discriminate]).
    assert (HR4a0 : R4 !!! Regidx (mword_of_int 10 : mword 5) = wsl)
      by (rewrite /R4 upd_eq; reflexivity).
    assert (HR4a5 : R4 !!! Regidx (mword_of_int 15 : mword 5) = fl)
      by (rewrite /R4 upd_ne; [exact HR3a5 | vm_compute; discriminate]).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x0a) : mword 64) 4
                    = mword_of_int (KernelSyms.flags2perm + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.andi a0,a0,8 -- the [flags & 1] test, as a shift-and-mask *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x0e))
              (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 6)
              R4 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iEval (rewrite -creg_c2); iApply (fpi_0e with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rewrite Hrg10) in "Hcg".
    iEval (rewrite HR4a0) in "Hcg".
    iEval (rewrite /wsl f2p_andi8) in "Hcg".
    set (w8 := (mword_of_int (if Z.testbit (bv_unsigned fl) 0 then 8 else 0) : mword 64)).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
              (mword_of_int (if Z.testbit (bv_unsigned fl) 0 then 8 else 0) : mword 64)]> R4)
      with (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg w8]> R4).
    set (R5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg w8]> R4).
    assert (HspR5 : R5 !!! Regidx csp_rs1 = spr)
      by (rewrite /R5 upd_ne; [exact HspR4 | vm_compute; discriminate]).
    assert (HR5a0 : R5 !!! Regidx (mword_of_int 10 : mword 5) = w8)
      by (rewrite /R5 upd_eq; reflexivity).
    assert (HR5a5 : R5 !!! Regidx (mword_of_int 15 : mword 5) = fl)
      by (rewrite /R5 upd_ne; [exact HR4a5 | vm_compute; discriminate]).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.flags2perm + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.andi a5,a5,2 *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x10))
              (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
              R5 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iEval (rewrite -creg_c7); iApply (fpi_10 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rewrite Hrg15) in "Hcg".
    iEval (rewrite HR5a5) in "Hcg".
    set (R6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec fl (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> R5).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec fl (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> R5) with R6.
    assert (HspR6 : R6 !!! Regidx csp_rs1 = spr)
      by (rewrite /R6 upd_ne; [exact HspR5 | vm_compute; discriminate]).
    assert (HR6a0 : R6 !!! Regidx (mword_of_int 10 : mword 5) = w8)
      by (rewrite /R6 upd_ne; [exact HR5a0 | vm_compute; discriminate]).
    assert (HR6a5 : R6 !!! Regidx (mword_of_int 15 : mword 5)
                    = and_vec fl (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (rewrite /R6 upd_eq; reflexivity).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.flags2perm + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* nothing below sp/s0/a0/a5 has moved -- the fact the epilogue's
       [callee_saved] obligation is discharged from, in either arm. *)
    assert (Hthr6 : forall c : mword 5,
              c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) ->
              c <> (mword_of_int 10 : mword 5) -> c <> (mword_of_int 15 : mword 5) ->
              R6 !!! Regidx c = mm !!! Regidx c).
    { intros c N2 N8 N10 N15.
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }

    (* ================================================================= *)
    (*  THE SHARED EPILOGUE (+0x18 .. +0x1e), proved once.  Quantified    *)
    (*  over the hart so either arm of the branch can supply it at ITS    *)
    (*  hart, and over the arriving register map [MM].                    *)
    (* ================================================================= *)
    iAssert (wp_next b p (fun (CIDt : CpuId) =>
               ∀ MM : regfile,
               ⌜ MM !!! Regidx csp_rs1 = spr
                 /\ MM !!! Regidx (mword_of_int 10 : mword 5)
                      = (mword_of_int (f2p fl) : mword 64)
                 /\ (forall c : mword 5,
                       c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) ->
                       c <> (mword_of_int 10 : mword 5) -> c <> (mword_of_int 15 : mword 5) ->
                       MM !!! Regidx c = mm !!! Regidx c) ⌝ -∗
               sie_cap_gpr KT1 MM (K - 2)%nat b p -∗
               pc_is (mword_of_int (KernelSyms.flags2perm + 0x18)) -∗
               WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hras Hs0s]" as "TAIL".
    { iIntros (CIDt Hst) "%MM %Hpre Hcg Hpc".
      destruct Hpre as (HMMsp & HMMa0 & HMMthr).
      (* +0x18 c.ldsp ra,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x18))
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
                MM (K - 2)%nat vra b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hras]").
      { iApply (fpi_18 with "Htext"). }
      { iEval (rewrite HMMsp). iExact "Hras". }
      iIntros (CIDu Hsu) "Hcg Hpc Hras".
      iEval (rewrite HMMsp) in "Hras".
      set (N1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg vra]> MM).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg vra]> MM) with N1.
      assert (HspN1 : N1 !!! Regidx csp_rs1 = spr)
        by (rewrite /N1 upd_ne; [exact HMMsp | vm_compute; discriminate]).
      assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x18) : mword 64) 2
                      = mword_of_int (KernelSyms.flags2perm + 0x1a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      (* +0x1a c.ldsp s0,0(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x1a))
                (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
                N1 (K - 2)%nat vs0 b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hs0s]").
      { iApply (fpi_1a with "Htext"). }
      { iEval (rewrite HspN1). iExact "Hs0s". }
      iIntros (CIDv Hsv) "Hcg Hpc Hs0s".
      iEval (rewrite HspN1) in "Hs0s".
      set (N2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg vs0]> N1).
      change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg vs0]> N1) with N2.
      assert (HspN2 : N2 !!! Regidx csp_rs1 = spr)
        by (rewrite /N2 upd_ne; [exact HspN1 | vm_compute; discriminate]).
      assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x1a) : mword 64) 2
                      = mword_of_int (KernelSyms.flags2perm + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      (* rebuild the two-slot frame *)
      iEval (rewrite Hb1) in "Hras". iEval (rewrite Hb2) in "Hs0s".
      iAssert (stack_own (KTR := KT1) sp0 2) with "[Hras Hs0s]" as "Hframe".
      { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
        iSplitL "Hras"; [iExists _; iExact "Hras"|].
        iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|].
        done. }
      assert (Hwv : add_vec (N2 !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
      { rewrite HspN2. unfold spr, sp0. apply frame_cancel_16. }
      assert (Hpop : N2 !!! Regidx csp_rs1
                     = pa_stk (add_vec (N2 !!! Regidx csp_rs1)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
      { rewrite Hwv HspN2. unfold spr, sp0, pa_stk, add_vec_int.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite -Hwv) in "Hframe".
      (* +0x1c c.addi sp,sp,16 *)
      iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x1c))
                (mword_of_int 16 : mword 6) N2 (K - 2)%nat 2 b Hpop
                with "Hcg Hpc [] Hframe").
      { iApply (fpi_1c with "Htext"). }
      iIntros (CIDw Hsw) "Hcg Hpc".
      assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      set (N3 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (N2 !!! Regidx csp_rs1)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> N2).
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (N2 !!! Regidx csp_rs1)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> N2) with N3.
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x1c) : mword 64) 2
                      = mword_of_int (KernelSyms.flags2perm + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* +0x1e c.jr ra *)
      assert (HN3ra : N3 !!! Regidx (mword_of_int 1 : mword 5) = vra).
      { rewrite /N3 upd_ne; [| vm_compute; discriminate].
        rewrite /N2 upd_ne; [| vm_compute; discriminate].
        rewrite /N1 upd_eq. reflexivity. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x1e))
                (mword_of_int 1 : mword 5) N3 K b ltac:(vm_compute; discriminate)
                with "Hcg Hpc []").
      { iApply (fpi_1e with "Htext"). }
      iIntros (CIDx Hsx) "Hcg Hpc".
      assert (Hretf : forall CIDy : CpuId,
                ret_pc (rget (CID := CIDy) N3 (mword_of_int 1 : mword 5)) = ret_tgt).
      { intros CIDy. rewrite Hrg1. rewrite HN3ra. reflexivity. }
      iEval (rewrite Hretf) in "Hpc".
      iSpecialize ("Hcont" $! CIDx with "[%]"); [wp_next_chain|].
      (* the two facts the contract owes *)
      assert (HN3thr : forall c : mword 5,
                c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) ->
                c <> (mword_of_int 1 : mword 5) ->
                N3 !!! Regidx c = MM !!! Regidx c).
      { intros c N2c N8c N1c.
        rewrite /N3 upd_ne; [| congruence].
        rewrite /N2 upd_ne; [| congruence].
        rewrite /N1 upd_ne; [reflexivity | congruence]. }
      iApply ("Hcont" $! N3 with "Hcg Hpc [%] [%]").
      { unfold callee_saved.
        split.
        { rewrite /N3 upd_eq. unfold regval_into_reg. rewrite Hwv. reflexivity. }
        split.
        { rewrite /N3 upd_ne; [| vm_compute; discriminate].
          rewrite /N2 upd_eq. reflexivity. }
        repeat split;
          (rewrite HN3thr; [ apply HMMthr | .. ];
           vm_compute; first [reflexivity | discriminate]). }
      { rewrite HN3thr; [ exact HMMa0 | .. ]; vm_compute; discriminate. } }

    (* ================================================================= *)
    (*  +0x12 c.beqz a5 -- the [flags & 2] test.                          *)
    (* ================================================================= *)
    destruct (Z.testbit (bv_unsigned fl) 1) eqn:Hbit1.
    - (* bit1 SET: the branch falls through and the [ori] runs *)
      assert (Hbz : forall CIDy : CpuId,
                eq_vec (rget (CID := CIDy) R6 (mword_of_int 15 : mword 5)) zero_reg = false).
      { intros CIDy. rewrite Hrg15. rewrite HR6a5. exact (f2p_bz_fall fl Hbit1). }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x12))
                (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                R6 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) (Hbz _)
                with "Hcg Hpc []").
      { iApply (fpi_12 with "Htext"). }
      iIntros (CID9 Hs9) "Hcg Hpc".
      assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x12) : mword 64) 2
                      = mword_of_int (KernelSyms.flags2perm + 0x14))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp14) in "Hpc".
      (* +0x14 ori a0,a0,4 *)
      set (w12 := (mword_of_int ((if Z.testbit (bv_unsigned fl) 0 then 8 else 0) + 4) : mword 64)).
      assert (Hor : forall CIDy : CpuId,
                or_vec (rget (CID := CIDy) R6 (mword_of_int 10 : mword 5))
                  (sign_extend' 64 (mword_of_int 4 : mword 12)) = w12).
      { intros CIDy. rewrite Hrg10. rewrite HR6a0. rewrite /w8 /w12.
        apply f2p_ori4. destruct (Z.testbit (bv_unsigned fl) 0); [right | left]; reflexivity. }
      iApply (wp_ori_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x14))
                (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 4 : mword 12) w12 R6 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) (Hor _)
                with "Hcg Hpc []").
      { iApply (fpi_14 with "Htext"). }
      iIntros (CID10 Hs10) "Hcg Hpc".
      set (R7 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg w12]> R6).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg w12]> R6) with R7.
      assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.flags2perm + 0x14) : mword 64) 4
                      = mword_of_int (KernelSyms.flags2perm + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp18) in "Hpc".
      iSpecialize ("TAIL" $! CID10 with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! R7 with "[%] Hcg Hpc").
      split; [| split].
      + rewrite /R7 upd_ne; [exact HspR6 | vm_compute; discriminate].
      + rewrite /R7 upd_eq. unfold regval_into_reg, w12, f2p.
        rewrite Hbit1. reflexivity.
      + intros c N2c N8c N10c N15c.
        rewrite /R7 upd_ne; [| congruence].
        apply Hthr6; assumption.
    - (* bit1 CLEAR: the branch is taken, straight to the epilogue *)
      assert (Hbz : forall CIDy : CpuId,
                eq_vec (rget (CID := CIDy) R6 (mword_of_int 15 : mword 5)) zero_reg = true).
      { intros CIDy. rewrite Hrg15. rewrite HR6a5. exact (f2p_bz_taken fl Hbit1). }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.flags2perm + 0x12))
                (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                R6 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) (Hbz _)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fpi_12 with "Htext"). }
      iNext.
      iIntros (CID9 Hs9) "Hcg Hpc".
      assert (Htgt18 : add_vec (mword_of_int (KernelSyms.flags2perm + 0x12) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.flags2perm + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt18) in "Hpc".
      iSpecialize ("TAIL" $! CID9 with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! R6 with "[%] Hcg Hpc").
      split; [| split].
      + exact HspR6.
      + rewrite HR6a0. unfold w8, f2p. rewrite Hbit1.
        rewrite Z.add_0_r. reflexivity.
      + exact Hthr6.
  Qed.

End ProofFlags2perm.

End Flags2permProof.
