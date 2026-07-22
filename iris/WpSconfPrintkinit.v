(* WpSconfPrintkinit.v -- the whole-function WP for xv6's printkinit() over the
   SIE-agnostic sconf world.

     void printkinit(void) { initlock(&pr.lock, "pr"); }

   printkinit is a thin initlock wrapper, so it is an INSTANCE of the shape
   proved once in WpInitlockWrapper.v: all this file supplies is printkinit's
   thirteen instructions (WpPrintkinitDecode.pki_code), the three relocations
   -- a1 = &"pr" (auipc 0x6 / addi +1982), a0 = &pr (auipc 0x12 / addi -1402),
   and the jal displacement to initlock -- and the "pr" literal itself, read out
   of the kernel's data image. *)
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
Require Import WpPrintkinitDecode.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecPrintkinit.
Local Open Scope Z_scope.
Import Defs.

Module PrintkinitProof (Initlock : INITLOCK) : PRINTKINIT.

Module ILW := InitlockWrapperProof Initlock.

Section WpSconfPrintkinit.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_printkinit_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64)
    : wp_printkinit_sconf_body γ root_ppn Φ m K vlock vname vcpu.
  Proof.
    cbv beta delta [wp_printkinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK Hretm.
    (* &"pr" is proof-local: the spec speaks of the lock's NAME, not of the
       address the image happens to keep the literal at. *)
    pose (name := (mword_of_int pr_name_str : mword 64)).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext #Hkdata Hpc Hlock Hname Hcpu Hcont".
    (* the "pr" string literal (2 chars + NUL), read out of the data image *)
    assert (Hpr : forall j b, cstring_bytes "pr"%string !! j = Some b ->
                    KernelData.kernel_data !! (pr_name_str + Z.of_nat j)%Z = Some b).
    { intros j b Hj.
      do 3 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string pr_name_str "pr"%string name eq_refl Hpr
                  with "Hkdata") as "#Hstr".
    iApply (ILW.wp_initlock_wrapper_sconf γ root_ppn Φ m K PK
              (mword_of_int 6) (mword_of_int 18) (mword_of_int 1982) (mword_of_int 2694)
              (mword_of_int 782) lk name "pr"%string vlock vname vcpu HK Hretm
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Htext [] Hpc Hstr Hlock Hname Hcpu Hcont").
    iApply (pki_code with "Htext").
  Qed.

End WpSconfPrintkinit.

End PrintkinitProof.
