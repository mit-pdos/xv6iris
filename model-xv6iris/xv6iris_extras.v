(* ====================================================================== *)
(* xv6iris_extras.v -- THE ROCQ REALISATIONS OF THE SAIL PLATFORM HOOKS.    *)
(*                                                                          *)
(* HAND-WRITTEN.  Everything else in this directory except riscv_extras.v   *)
(* is generated; `make model-gen` does not touch this file, it only passes  *)
(* it to sail as a second `--coq-lib`.                                      *)
(*                                                                          *)
(* WHAT IT IS FOR.  Sail's Rocq backend emits a bare `Axiom` for every `val`*)
(* it sees declared with no Sail body and no `coq:` extern binding          *)
(* (pretty_print_coq.ml's [find_unimplemented], under `--coq-undef-axioms`).*)
(* SIX of the platform hooks used to land in that set, so every `Print      *)
(* Assumptions` in the tree carried six dangling axioms that no file        *)
(* anywhere declared, named, or could document.  The pinned sail-riscv fork *)
(* (the `xv6` branch) now gives all six a `coq:` binding, so sail emits     *)
(* NOTHING for them, and declares them as `Axiom`s in its own               *)
(* `handwritten_support/riscv_extras.v` so the model still compiles for a   *)
(* consumer that supplies nothing else.  THIS FILE IS THAT CONSUMER'S       *)
(* OVERRIDE: it is passed as a SECOND `--coq-lib`, sail emits the lib       *)
(* requires in order, so what is defined here wins over the fork's axioms.  *)
(* Same contract sail-riscv's `riscv_extras.v` already had for              *)
(* [print_string], [get_time_ns] and [sys_enable_experimental_extensions].  *)
(*                                                                          *)
(* WHY IT IS A SEPARATE FILE.  Not because riscv_extras.v could not hold    *)
(* these -- it holds the fork's own axioms for the same six hooks, stated   *)
(* monad-polymorphically (`forall {Mon} `{base.MRet Mon}`) precisely because*)
(* that file is shared by the rv32 and rv64 builds and so cannot name [M].  *)
(* This file can, and does: [M] is defined by the GENERATED [rv64d_types.v] *)
(* when it instantiates the [Defs] functor                                  *)
(* (`SailStdpp/ConcurrencyInterfaceBuiltins.v`: `Module Defs (A : Arch) (I :*)
(* InterfaceT A)`) against this model's [Arch], and naming it directly keeps*)
(* the definitions readable and keeps [ResvAxioms]'s equations provable by  *)
(* [reflexivity].  Requiring rv64d_types from a lib is legal precisely      *)
(* because sail emits the lib requires AFTER the types module in the main   *)
(* file and NOT AT ALL in the types file (sail_plugin_coq.ml:233,           *)
(* `base_imports @ (types_module :: libs)`), so there is no cycle.  The     *)
(* OTHER reason it is separate is that it is ours: a regen overwrites       *)
(* riscv_extras.v from the fork and never touches this file.                *)
(*                                                                          *)
(* WHAT IS DEFINED OUTRIGHT, AND WHY THAT IS NOT AN ASSUMPTION.  The three  *)
(* [M]-valued hooks have NO observable effect on the state this model       *)
(* actually carries: the LR/SC reservation set is platform state outside    *)
(* [regstate] / [mstate], and the HTIF terminal is not modelled at all.     *)
(* [returnm tt] is therefore an exact realisation, not a simplifying one,   *)
(* and it is a strict refinement of the axioms it replaces (both old        *)
(* `ResvAxioms` term axioms are now proved by [reflexivity]; see            *)
(* `iris/ResvAxioms.v`).                                                    *)
(*                                                                          *)
(* WHAT STAYS AN ASSUMPTION, AND WHY IT IS DECLARED HERE INSTEAD.  The two  *)
(* reservation PREDICATES are a different matter.  Sail declares them       *)
(* `pure`, so within one Rocq evaluation each is a FIXED function -- the    *)
(* model cannot express a reservation set that changes -- and the honest    *)
(* reading of the spec is "an arbitrary but fixed platform predicate".      *)
(* [resv_matches] / [resv_is_valid] below say exactly that, and every       *)
(* proof that reads one destructs it both ways (design note: the content    *)
(* of the reservation is never assumed, only the two hooks' nil effect).    *)
(* They are the ONLY assumptions this file introduces, they carry this      *)
(* project's name rather than sail's, and they are what the audit in        *)
(* `iris/SystemAssumptions.v` now expects to see.                           *)
(*                                                                          *)
(* THE ALTERNATIVE, IF YOU EVER WANT A ZERO-AXIOM AUDIT: realise both       *)
(* predicates concretely (e.g. [fun _ => false]).  The proofs go through    *)
(* unchanged, because they already handle both branches -- but the theorem  *)
(* then describes one particular platform (there, one whose SC always       *)
(* fails) instead of every platform, which is a genuine weakening and not   *)
(* worth two audit lines.  DO NOT do it by accident.                        *)
(*                                                                          *)
(* [plat_term_read] IS DELIBERATELY NOT OVERRIDDEN HERE.  Its result is     *)
(* CONSUMED by the model, so any realisation fabricates an input byte.      *)
(* Leaving it to the fork's `Axiom` keeps the term irreducible, so a        *)
(* development that reaches a terminal read gets STUCK LOUDLY instead of    *)
(* proceeding on invented data.  Same reasoning for [get_16_random_bits]    *)
(* (the Zkr seed CSR, illegal at U) and the softfloat [riscv_f*] family,    *)
(* which have no `coq:` binding at all and are still generated into rv64d.v:*)
(* nothing in the tree steps one, and none of them is in the audit baseline.*)
(* ====================================================================== *)
From Stdlib Require Import ZArith.
Require Import SailStdpp.Base.
Require Import rv64d_types.

(* ---- LR/SC reservation: the two effectful hooks ----------------------   *)
(* Both are the identity on sregs / mem / mdev, so [returnm tt] is exact.   *)

Definition load_reservation {n} (addr : mword n) (width : Z) : M unit :=
  returnM tt.

Definition cancel_reservation (_ : unit) : M unit :=
  returnM tt.

(* ---- LR/SC reservation: the two predicates ---------------------------   *)
(* Arbitrary but fixed, per the note above.  These two [Parameter]s are     *)
(* the whole assumed content of this file.                                  *)

Parameter resv_matches : forall (n : Z), mword n -> bool.
Parameter resv_is_valid : bool.

Definition match_reservation {n} (addr : mword n) : bool := resv_matches n addr.

Definition valid_reservation (_ : unit) : bool := resv_is_valid.

(* ---- HTIF terminal output --------------------------------------------   *)
(* The terminal is not part of the modelled state, so a write to it moves   *)
(* nothing this development can observe.                                    *)

Definition plat_term_write (_ : mword 8) : M unit :=
  returnM tt.
