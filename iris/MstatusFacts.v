(* MstatusFacts.v -- [mstatus_kernel_facts]: the mstatus field contract the
   xv6 kernel runs under, spelled ONCE.

   These eleven facts are what every S-mode WP in the tree assumes about
   mstatus ([IntrDefs.sconf_ms_facts] is the same set minus the SIE pin) and
   what M-mode kernel code preserves: the reset mstatus 0xA00000000 has all of
   them, [start()] writes only MPP, MRET writes only MIE/MPIE/MPP/MPRV, and
   the legalizer never touches the rest.  Before this predicate existed
   [InstrBytes.mmode_config] pinned only three of them (MIE / MPRV / SXL), so
   the M-mode boot contract's postcondition could not tell the S-mode side
   what it needs -- SEVEN of these are NOT derivable from those three (verified
   at a hostile mstatus; see claude-notes/completed/crash.md, M6c).

   HOME: a file of its own, with MINIMAL imports (Stdlib + Sail + the model),
   because [InstrBytes] must require it and MstatusBits.v -- the obvious
   neighbour, and where the per-field transform theory lives -- requires
   [stdpp bitvector.tactics], whose zify hook would then reach the bottom of
   the tree and break [lia] on every downstream goal mentioning [bv_unsigned]
   (durable-notes: the hook arrives transitively).

   The MPP conjunct is stated here as the BIT DISEQUALITY (MPP is not the
   reserved 'b"10"); its boolean form
   [WpGprCsrwCommon.have_nom_val (_get_Mstatus_MPP ms) = true], which
   [sconf_ms_facts] uses, is derived in IntrDefs.v
   ([sconf_ms_facts_of_kernel]) -- [have_nom_val] lives above this file. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.

(* the eleven facts, in [sconf_ms_facts]'s order with the SIE pin in front *)
Definition mstatus_kernel_facts (ms : mword 64) : Prop :=
  _get_Mstatus_SIE ms = ('b"0" : mword 1) /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  _get_Mstatus_SXL ms = ('b"10" : mword 2) /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false /\
  _get_Mstatus_XS ms = extStatus_map_forwards Off /\
  _get_Mstatus_FS ms = extStatus_map_forwards Off /\
  _get_Mstatus_VS ms = extStatus_map_forwards Off /\
  _get_Mstatus_SD ms = ('b"0" : mword 1) /\
  eq_vec (_get_Mstatus_MPP ms) ('b"10") = false /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false.

(* The three facts [mmode_config] pinned before the widening are the MPRV and
   SXL conjuncts (MIE is separate -- it is about M-mode interrupt delivery,
   not the S-mode contract), projected here so consumers that only want them
   need not destructure the eleven. *)
Lemma mstatus_kernel_MPRV (ms : mword 64) :
  mstatus_kernel_facts ms -> eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false.
Proof. intros (_ & H & _). exact H. Qed.

Lemma mstatus_kernel_SXL (ms : mword 64) :
  mstatus_kernel_facts ms -> _get_Mstatus_SXL ms = ('b"10" : mword 2).
Proof. intros (_ & _ & H & _). exact H. Qed.

Lemma mstatus_kernel_SIE (ms : mword 64) :
  mstatus_kernel_facts ms -> _get_Mstatus_SIE ms = ('b"0" : mword 1).
Proof. intros (H & _). exact H. Qed.
