(* MemAmo4.v -- mode-neutral width-4 ATOMIC (op.W) memory leaf lemmas.

   The width-4 atomic read-modify-write core, factored out of the S-mode
   op tower (WpAmo.v).  Everything is privilege-GENERIC: the access
   privilege enters ONLY through the pmpCheck grant, supplied by the caller
   as a hypothesis [Hpmp] (S the supervisor grant, U the user grant).  The
   effective-address transform [Htea] and address translation [Htr] are
   likewise hypotheses, and [pa] is an ABSTRACT Variable (identity for the
   kernel, real Sv39 [u_pa] for U-mode).  The AMO read kind is
   Read_RISCV_reserved_acquire and the write kind Write_RISCV_conditional. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec.
Require Import WpGpr.
Local Open Scope Z_scope.
Import Defs.

(* pmaCheck for an aligned RAM AMO with atomic support (res_or_con = true). *)

Lemma exec_effectivePrivilege_amo_nm (op : amoop) (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Atomic (op, Data, Data)) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege.
  rewrite H. rewrite andb_false_r. apply exec_returnm.
Qed.









Section ExecAmoGS4.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable w : mword 32.
  Variable s : mstate.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable pa : mword 64.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s = Some (Virtaddr a, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte w j).

End ExecAmoGS4.

(* ===================================================================== *)
(* AMOSWAP.W gpr-walk core: translate MISSES at s and FILLS -> s'; the AMO *)
(* read+write body runs at s'.  State-threading twin of ExecAmoGS4.        *)
(* ===================================================================== *)
Section ExecAmoGS4Walk.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable w : mword 32.
  Variable s s' : mstate.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable pa : mword 64.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s = Some (Virtaddr a, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte w j).

End ExecAmoGS4Walk.
