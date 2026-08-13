(* ProofPrintkinit.v -- the whole-function WP for xv6's printkinit() over the
   SIE-agnostic sconf world.

     void printkinit(void) { initlock(&pr.lock, "pr"); }

   printkinit is a thin initlock wrapper, so it is an INSTANCE of the shape
   proved once in WpInitlockWrapper.v: all this file supplies is printkinit's
   thirteen instructions (CodePrintkinit.v, bundled as [pkni_code] below), the
   three relocations
   -- a1 = &"pr" (auipc 0x6 / addi +1968), a0 = &pr (auipc 0x12 / addi -1304),
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
Require Import SpecInitlock SpecInitlockWrapper WpInitlockWrapper.
Require Import KernelText CodePrintkinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecPrintkinit.
Local Open Scope Z_scope.
Import Defs.

Section CodePrintkinitBundle.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* printkinit's thirteen instructions (CodePrintkinit.v), in the
     thin-initlock-wrapper pattern (SpecInitlockWrapper.v) that its
     whole-function proof instantiates. *)
  Lemma pkni_code :
    kernel_text -∗ ilw_code KernelSyms.printkinit (mword_of_int 6) (mword_of_int 18)
                            (mword_of_int 2012) (mword_of_int 2788) (mword_of_int 724).
  Proof.
    iIntros "#Ht". rewrite /ilw_code.
    iSplitR; [iApply (pkni_00 with "Ht")|].
    iSplitR; [iApply (pkni_02 with "Ht")|].
    iSplitR; [iApply (pkni_04 with "Ht")|].
    iSplitR; [iApply (pkni_06 with "Ht")|].
    iSplitR; [iApply (pkni_08 with "Ht")|].
    iSplitR; [iApply (pkni_0c with "Ht")|].
    iSplitR; [iApply (pkni_10 with "Ht")|].
    iSplitR; [iApply (pkni_14 with "Ht")|].
    iSplitR; [iApply (pkni_18 with "Ht")|].
    iSplitR; [iApply (pkni_1c with "Ht")|].
    iSplitR; [iApply (pkni_1e with "Ht")|].
    iSplitR; [iApply (pkni_20 with "Ht")|].
    iApply (pkni_22 with "Ht").
  Qed.

End CodePrintkinitBundle.

Module PrintkinitProof (Initlock : INITLOCK) : PRINTKINIT.

Module ILW := InitlockWrapperProof Initlock.

Section ProofPrintkinit.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_printkinit_sconf
      (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64)
    : wp_printkinit_sconf_body m K vlock vname vcpu b p.
  Proof.
    cbv beta delta [wp_printkinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    (* &"pr" is proof-local: the spec speaks of the lock's NAME, not of the
       address the image happens to keep the literal at. *)
    pose (name := (mword_of_int pr_name_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hlock Hname Hcpu Hcont".
    (* the "pr" string literal (2 chars + NUL), read out of the data image *)
    assert (Hpr : forall j bt, cstring_bytes "pr"%string !! j = Some bt ->
                    KernelData.kernel_data !! (pr_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 3 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string pr_name_str "pr"%string name eq_refl ltac:(unfold text_end, pr_name_str; lia) Hpr
                  with "Hkdata") as "#Hstr".
    iApply (ILW.wp_initlock_wrapper_sconf m K KernelSyms.printkinit
              (mword_of_int 6) (mword_of_int 18) (mword_of_int 2012) (mword_of_int 2788)
              (mword_of_int 724) lk name "pr"%string vlock vname vcpu b p HK
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Htext [] Hpc Hstr Hlock Hname Hcpu Hcont").
    iApply (pkni_code with "Htext").
  Qed.

End ProofPrintkinit.

End PrintkinitProof.
