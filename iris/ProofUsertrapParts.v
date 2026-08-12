(* ProofUsertrapParts.v -- usertrap()'s pure obligations, kept out of the
   whole-function proof for the reason ProofPrepareReturnParts.v and
   ProofKerneltrapParts.v are: a bitvector argument inside a syscall-altitude
   WP goal is a 40-minute error message when it goes wrong
   (claude-notes/durable-notes.md).

   FIRST OBLIGATION: THE PANIC ARM IS DEAD.

       if ((r_sstatus() & SSTATUS_SPP) != 0)
         panic("usertrap: not from user mode");

   compiled as [csrr a5,sstatus / andi a5,a5,256 / c.bnez a5 -> +0x84].  The
   trap came from USER mode, so [UserExec.trap_mstatus_ok]'s [SPP <> 1] pins
   the bit clear and the masked word is zero, so the [c.bnez] falls through and
   the arm is refuted from the contract's premises.  That is what keeps [panic]
   -- and with it printk's panic path -- out of usertrap's cone, exactly as
   kerneltrap's three panic arms keep it out of that one.

   THIS IS THE MIRROR OF ProofKerneltrapParts' [kt_spp_bit] /
   [kt_spp_set_neq], which prove the OPPOSITE polarity: kerneltrap's
   [if ((sstatus & SPP) == 0) panic] needs the mask NONZERO from SPP = 1, and
   usertrap's [!= 0] needs it ZERO from SPP = 0.  The two pairs belong
   together, and the honest place for all four is beside [sstatus_read] in
   WpGprCsrwC.v; they are split only because neither function's parts file may
   import the other's.  Hoist them together whenever something else has to
   touch that file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import MstatusBits.
Require Import WpGprCsrwCommon WpGprCsrwC.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* the offset base, as ProofPrepareReturnParts does for [PRR] *)
Notation UT := KernelSyms.usertrap (only parsing).

Section UsertrapParts.

  (* the mirror of [ProofKerneltrapParts.kt_spp_bit]: a CLEAR SPP is a clear
     bit 8 of the word.  Same script, read at 'b"0". *)
  Lemma ut_spp_bit (w : mword 64) :
    _get_Sstatus_SPP w = ('b"0" : mword 1) ->
    Z.testbit (bv_unsigned w) 8 = false.
  Proof.
    intro HS.
    apply (f_equal bv_unsigned) in HS.
    unfold _get_Sstatus_SPP, subrange_vec_dec in HS.
    rewrite autocast_refl in HS.
    unfold to_word_idx, to_word, get_word in HS.
    rewrite MachineWord.MachineWord.cast_idx_refl in HS.
    unfold MachineWord.MachineWord.slice in HS.
    rewrite bv_extract_unsigned in HS.
    change (bv_unsigned ('b"0" : mword 1)) with 0 in HS.
    apply (f_equal (fun z => Z.testbit z 0)) in HS.
    change (Z.testbit 0 0) with false in HS.
    rewrite <- HS.
    unfold bv_wrap, bv_modulus.
    rewrite (Z.mod_pow2_bits_low _ (Z.of_N (MachineWord.MachineWord.Z_idx (8 - 8 + 1))));
      [| vm_compute; reflexivity].
    rewrite Z.shiftr_spec; [| lia]. reflexivity.
  Qed.

  (* SPP = 0 in the trapped mstatus makes [andi a5,a5,256] ZERO, so the
     "not from user mode" [c.bnez] falls through and the panic is dead. *)
  Lemma ut_spp_clear_eq (ms : mword 64) :
    _get_Mstatus_SPP ms = ('b"0" : mword 1) ->
    eq_vec (and_vec (sstatus_read ms)
              (sign_extend' 64 (mword_of_int 256 : mword 12))) zero_reg = true.
  Proof.
    intro HSPP.
    assert (Hb8 : Z.testbit (bv_unsigned (sstatus_read ms)) 8 = false).
    { apply ut_spp_bit. unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
      rewrite WpGprCsrwC.sSPP_lower. exact HSPP. }
    assert (Hmask : bv_unsigned (sign_extend' 64 (mword_of_int 256 : mword 12) : mword 64) = 256)
      by (vm_compute; reflexivity).
    apply eq_vec_true_iff. apply bv_eq.
    rewrite WpGprCsrwC.and_vec_unsigned Hmask.
    change (bv_unsigned (zero_reg : mword 64)) with 0.
    apply Z.bits_inj_0. intro n.
    destruct (Z_lt_le_dec n 0) as [Hn | Hn].
    { apply Z.testbit_neg_r. lia. }
    rewrite Z.land_spec.
    destruct (Z.eq_dec n 8) as [-> | Hne].
    - rewrite Hb8. reflexivity.
    - replace (Z.testbit 256 n) with false; [apply andb_false_r |].
      change 256 with (2 ^ 8). symmetry.
      rewrite Z.pow2_bits_eqb; [| lia].
      apply Z.eqb_neq. lia.
  Qed.

  (* the same fact in the form the BRANCH LEAF consumes.
     [WpSconfBtype.wp_cbnez_fall_s_sconf] wants [neq_vec _ zero_reg = false],
     so stating it here saves the walk a polarity step at the one site that
     needs it -- and keeps [ut_spp_clear_eq] itself in [kt_spp_set_neq]'s
     [eq_vec] spelling, which is the twin's. *)
  Lemma ut_spp_clear_neq (ms : mword 64) :
    _get_Mstatus_SPP ms = ('b"0" : mword 1) ->
    neq_vec (and_vec (sstatus_read ms)
              (sign_extend' 64 (mword_of_int 256 : mword 12))) zero_reg = false.
  Proof. intro H. unfold neq_vec. rewrite (ut_spp_clear_eq ms H). reflexivity. Qed.

End UsertrapParts.
