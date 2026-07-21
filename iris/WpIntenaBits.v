(* WpIntenaBits.v: the pure intena-bit fact -- the value push_off stores
   (and pop_off reads back) as intena IS the SIE bit of the saved
   sstatus view.  Iris-free (vanilla rewrite scope): the testbit chase
   below relies on it. *)
Require Import SailStdpp.Operators_mwords SailStdpp.MachineWord SailStdpp.Values SailStdpp.TypeCasts.
From stdpp Require Import bitvector.definitions.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvExtras WpGprCsrwCommon WpGprCsrwC.
From Stdlib Require Import ZArith Lia.

(* the value the srli/andi chain computes from the saved sstatus view
   (spelled operationally, as the instructions compute it) *)
Definition po_intena_val (ms : mword 64) : mword 32 :=
  (autocast (T := mword)
     (subrange_vec_dec
        (and_vec (shift_bits_right (sstatus_read ms)
                    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32).

(* the value pop_off reads back as intena IS the SIE bit of the saved
   sstatus view -- the pure fact that converts push_off's ⌜SIE ms⌝-keyed
   payload into pop_off's intenav-keyed input disjunct. *)