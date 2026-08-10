(* Feasibility: does the parsing-layer conversion reduce to a LITERAL? *)
From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import String Ascii NArith ZArith.
From Stdlib Require Import Uint63.

Definition char63_of_ascii (a : ascii) : char63 :=
  Uint63.of_Z (Z.of_N (N_of_ascii a)).

Fixpoint pstr (s : String.string) : PrimString.string :=
  match s with
  | EmptyString => PrimString.make 0%uint63 0%uint63
  | String a s' => PrimString.cat (PrimString.make 1%uint63 (char63_of_ascii a)) (pstr s')
  end.

(* the conversion, forced at elaboration time exactly as the proofmode's
   `eval vm_compute in (INamed <$> Hs)` sites already do *)
Definition n1 : PrimString.string :=
  ltac:(let x := eval vm_compute in (pstr "Hi_csrw_ss") in exact x).
Definition n2 : PrimString.string :=
  ltac:(let x := eval vm_compute in (pstr "Hi_csrw_sscratch_trapframe_slot") in exact x).
Definition cmp := PrimString.compare n1 n2.

(* correctness of the bridge, checked by the kernel *)
Definition ok1 : PrimString.compare n1 "Hi_csrw_ss"%pstring = Eq := eq_refl.
Definition ok2 : PrimString.compare n2 "Hi_csrw_sscratch_trapframe_slot"%pstring = Eq := eq_refl.
Definition ok3 : PrimString.compare n1 n2 = Lt := eq_refl.
