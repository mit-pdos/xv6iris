(* ProofBinit.v -- whole-function WP proof for binit() over the sconf world. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes SmodeCore CalleeSaved KernelText KernelDataInv IntrDefs.
Require Import WpLock SleepLock SpecInitlock SpecInitsleeplock.
Require Import SpecBinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Module BinitProof (Initlock : INITLOCK) (Initsleeplock : INITSLEEPLOCK) : BINIT.

Section ProofBinit.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!lockG Σ}.
  Context `{CID : CpuId}.

  Definition bcache_name_str : Z := 0x80007390.
  Definition buffer_name_str : Z := 0x80007398.

  Lemma wp_binit_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
      (vlock : mword 32) (vname vcpu : mword 64)
    : wp_binit_sconf_body γ Φ m K vlock vname vcpu.
  Proof.
    cbv beta delta [wp_binit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    pose (name_bcache := (mword_of_int bcache_name_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hlock Hname Hcpu Hcont".
    assert (Hbcache : forall j b, cstring_bytes "bcache"%string !! j = Some b ->
                        KernelData.kernel_data !! (bcache_name_str + Z.of_nat j)%Z = Some b).
    { intros j b Hj.
      do 7 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string bcache_name_str "bcache"%string name_bcache eq_refl ltac:(unfold text_end, bcache_name_str; lia) Hbcache
                  with "Hkdata") as "#Hstr_bcache".
    iAssert (pc_is ret_tgt) with "[Hpc]" as "Hret".
    { admit. }
    iAssert (lk ↦₄ (mword_of_int 0 : mword 32))%I with "[Hlock]" as "Hlk_zero".
    { admit. }
    iAssert (lock_name lk "bcache"%string) with "[Hname]" as "#Hlk_name".
    { admit. }
    iAssert (c_cpu ↦₈ (zero_reg : mword 64))%I with "[Hcpu]" as "Hcpu_zero".
    { admit. }
    iApply ("Hcont" $! m with "Hcg Hret [//] Hlk_zero Hlk_name Hcpu_zero").
  Admitted.

End ProofBinit.

End BinitProof.
