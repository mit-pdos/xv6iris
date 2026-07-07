(* WpGprCsrw.v -- split into Common/A/B for build parallelism; this shim re-exports everything. *)
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
Local Open Scope Z_scope.

Require Export WpGprCsrwCommon WpGprCsrwA WpGprCsrwB.

(* Demonstration: each ONE register-generic csrw WP serves any source reg. *)
Section WpCsrwGprNewDemo.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  (* csrw medeleg, x5  and  csrw mepc, x28  (source register generalized) *)
  Definition wp_csrw_medeleg_x5 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_csrw_medeleg_gpr E Φ pc (mword_of_int 5).
  Definition wp_csrw_mepc_x28 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_csrw_mepc_gpr E Φ pc (mword_of_int 28).
  Definition wp_csrw_satp_x5 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_csrw_satp_gpr E Φ pc (mword_of_int 5).
  Goal gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 5 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpCsrwGprNewDemo.
