(* ProofFileinit.v -- the whole-function WP for xv6's fileinit() over the
   SIE-agnostic sconf world.

     void fileinit(void) { initlock(&ftable.lock, "ftable"); }

   fileinit is a thin initlock wrapper, so it is an INSTANCE of the shape proved
   once in WpInitlockWrapper.v: all this file supplies is fileinit's thirteen
   instructions (WpFileinitDecode.fii_code) and the three relocations -- a1 =
   &"ftable" (auipc 0x3 / addi +1468), a0 = &ftable (auipc 0x1e / addi +1212),
   and the jal displacement to initlock. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import SmodeCore.
Require Import KernelDataInv.
Require Import SpecInitlock WpInitlockWrapper.
Require Import WpFileinitDecode.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecFileinit.
Local Open Scope Z_scope.
Import Defs.

Module FileinitProof (Initlock : INITLOCK) : FILEINIT.

Module ILW := InitlockWrapperProof Initlock.

Section ProofFileinit.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_fileinit_sconf (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64)
    : wp_fileinit_sconf_body Φ m K vlock vname vcpu b p.
  Proof.
    cbv beta delta [wp_fileinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    (* &"ftable" is proof-local: the spec speaks of the lock's NAME, not of the
       address the image happens to keep the literal at. *)
    pose (name := (mword_of_int ftable_name_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hlock Hname Hcpu Hcont".
    (* the "ftable" string literal (6 chars + NUL), read out of the data image *)
    assert (Hftable : forall j bt, cstring_bytes "ftable"%string !! j = Some bt ->
                        KernelData.kernel_data !! (ftable_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 7 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string ftable_name_str "ftable"%string name eq_refl ltac:(unfold text_end, ftable_name_str; lia) Hftable
                  with "Hkdata") as "#Hstr".
    iApply (ILW.wp_initlock_wrapper_sconf Φ m K FI
              (mword_of_int 3) (mword_of_int 30) (mword_of_int 1468) (mword_of_int 1212)
              (mword_of_int 2083804) lk name "ftable"%string vlock vname vcpu b p HK
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Htext [] Hpc Hstr Hlock Hname Hcpu Hcont").
    iApply (fii_code with "Htext").
  Qed.

End ProofFileinit.

End FileinitProof.
