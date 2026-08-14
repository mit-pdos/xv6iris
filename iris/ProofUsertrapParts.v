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

   IT IS ONE READING OF [WpGprCsrwC.sstatus_spp_mask].  kerneltrap's
   [if ((sstatus & SPP) == 0) panic] needs the mask NONZERO from SPP = 1 and
   usertrap's [!= 0] needs it ZERO from SPP = 0, so what was two
   near-identical lemma pairs -- one in each parts file, split only because
   neither may import the other's -- is one hypothesis-free equation beside
   [sstatus_read], of which [ut_spp_clear_eq] and
   [ProofKerneltrapParts.kt_spp_set_neq] are the two instances. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpGprCsrwCommon WpGprCsrwC.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* the offset base, as ProofPrepareReturnParts does for [PRR] *)
Notation UT := KernelSyms.usertrap (only parsing).

Section UsertrapParts.

  (* SPP = 0 in the trapped mstatus makes [andi a5,a5,256] ZERO, so the
     "not from user mode" [c.bnez] falls through and the panic is dead.
     One instance of [WpGprCsrwC.sstatus_spp_mask], which is the
     hypothesis-free form both handlers read at their own polarity. *)
  Lemma ut_spp_clear_eq (ms : mword 64) :
    _get_Mstatus_SPP ms = ('b"0" : mword 1) ->
    eq_vec (and_vec (sstatus_read ms)
              (sign_extend' 64 (mword_of_int 256 : mword 12))) zero_reg = true.
  Proof.
    intro HSPP.
    rewrite WpGprCsrwC.sstatus_spp_mask HSPP. reflexivity.
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
