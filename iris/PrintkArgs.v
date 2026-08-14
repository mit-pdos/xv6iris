(* PrintkArgs.v -- the vocabulary a CALLER of printk speaks: how it describes
   its varargs, what resource each description costs, where the ABI puts them,
   and the address of pr.lock.

   Split out of SpecPrintk.v because it is not about printk's weakest
   precondition at all -- it is the shared language in which printk's callers
   state their obligations, and panic (SpecPanic.v) needs it while sitting
   BELOW printk's spec in the dependency order.  SpecPrintk.v [Require Export]s
   this file, so nothing that used these names through it changes.

   A variadic call has no types at the call site, so the caller DESCRIBES its
   arguments: [descs] says, for each vararg in order, whether it is an
   integer-ish value ([PkANum] -- %d/%u/%x/%p/%c and the long forms), a null
   [char *] ([PkANull], which printk prints as "(null)"), or a [char *] to a
   string it owns ([PkAStr dq s]).  The description must MATCH the format
   string --

       pk_kinds f = map pk_desc_kind descs

   -- which is the honest statement of C's unchecked contract: a "%s" whose
   argument is not a string is undefined behaviour, and here it is simply
   unprovable. *)
From Stdlib Require Import ZArith Bool List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Export PrintkFmt.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ---------------------------------------------------------------------- *)
(* The caller's description of one vararg.                                 *)
(* ---------------------------------------------------------------------- *)
Inductive pk_arg_desc :=
  | PkANum                                (* an integer/char/pointer value *)
  | PkANull                               (* a null char* -- printed "(null)" *)
  | PkAStr (dq : dfrac) (s : string).     (* a char* to [s], owned at [dq] *)

Definition pk_desc_kind (d : pk_arg_desc) : pk_kind :=
  match d with
  | PkANum => PkNum
  | PkANull => PkStr
  | PkAStr _ _ => PkStr
  end.

(* WHAT THE DESCRIPTION COSTS.  Hart-free -- the string points-to is memory,
   which is shared -- so this takes no [CpuId] and a description crosses a
   migration untouched. *)
Definition pk_desc_res `{!riscvGS Σ} `{GEN : GenId} (v : mword 64) (d : pk_arg_desc) : iProp Σ :=
  match d with
  | PkANum => True
  (* a [char *] to a real string is NOT null -- the caller has to say so.
     [v ↦ₛ{dq} s] alone does not imply it: nothing in the points-to rules out
     address 0, and printk's %s arm needs the [beqz] to fall through. *)
  | PkANull => ⌜v = zero_reg⌝
  | PkAStr dq s => ⌜nonul s = true⌝ ∗ ⌜eq_vec v zero_reg = false⌝ ∗ v ↦ₛ{dq} s
  end.

(* Vararg [j] is the entry value of a(j+1) = x(11+j): the ABI passes the first
   seven in registers, and printk's prologue spills them into its own frame.
   An eighth would live in the CALLER's frame, which is why printk's contract
   caps [length descs] at 7. *)
Definition pk_vararg (m : regfile) (j : nat) : mword 64 :=
  m !!! Regidx (mword_of_int (11 + Z.of_nat j) : mword 5).

(* [static struct { struct spinlock lock; } pr;] -- the lock is the FIRST
   field, so the object's address IS the lock's.  ([SpecPrintk.pr_lock] is
   the same address and [SpecPrintk.pr_res] the empty resource this lock
   protects, so the two [is_lock]s are the same proposition.) *)
Definition pk_pr_lock : mword 64 := mword_of_int KernelSyms.pr.
