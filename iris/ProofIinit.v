(* ProofIinit.v -- whole-function WP proof for iinit() over the sconf world. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes SmodeCore KernelDataInv IntrDefs.
Require Import WpLock SpecInitlock SpecInitsleeplock.
Require Import SpecIinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Module IinitProof (Initlock : INITLOCK) (Initsleeplock : INITSLEEPLOCK) : IINIT.

Section ProofIinit.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!lockG Σ}.
  Context `{CID : CpuId}.

  Definition itable_name_str : Z := 0x80007420.

  Lemma wp_iinit_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
      (vlock : mword 32) (vname vcpu : mword 64)
    : wp_iinit_sconf_body γ Φ m K vlock vname vcpu.
  Proof.
    cbv beta delta [wp_iinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    pose (name_itable := (mword_of_int itable_name_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hlock Hname Hcpu Hcont".
    assert (Hitable : forall j b, cstring_bytes "itable"%string !! j = Some b ->
                       KernelData.kernel_data !! (itable_name_str + Z.of_nat j)%Z = Some b).
    { intros j b Hj.
      do 7 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string itable_name_str "itable"%string name_itable eq_refl ltac:(unfold text_end, itable_name_str; lia) Hitable
                  with "Hkdata") as "#Hstr_itable".

    set (m_il := <[Regidx (mword_of_int 10 : mword 5) := lk]>
                 (<[Regidx (mword_of_int 11 : mword 5) := name_itable]>
                  (<[Regidx (mword_of_int 1 : mword 5) := m !!! Regidx (mword_of_int 1 : mword 5)]> m))).
    assert (Hil10 : m_il !!! Regidx (mword_of_int 10 : mword 5) = lk) by (rewrite /m_il upd_eq; reflexivity).
    assert (Hil11 : m_il !!! Regidx (mword_of_int 11 : mword 5) = name_itable) by (rewrite /m_il upd_ne; [rewrite upd_eq; reflexivity | vm_compute; discriminate]).
    assert (Hil1 : m_il !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /m_il upd_ne; [rewrite upd_ne; [rewrite upd_eq; reflexivity | vm_compute; discriminate] | vm_compute; discriminate]).

    iAssert (sie_cap_gpr γ m_il K ∗ pc_is (mword_of_int KernelSyms.initlock))%I with "[Hcg Hpc]" as "[Hcg_il Hpc_il]".
    { admit. }

    iApply (Initlock.wp_initlock_sconf γ Φ m_il vlock vname vcpu "itable"%string K ltac:(lia)
              with "Hcg_il Htext Hpc_il Hstr_itable [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite Hil10). iExact "Hlock". }
    { iEval (rewrite Hil10). iExact "Hname". }
    { iEval (rewrite Hil10). iExact "Hcpu". }
    iIntros (mr) "Hcg Hret %Hcs Hlk_zero #Hlk_name Hcpu_zero".
    iEval (rewrite Hil10) in "Hlk_zero".
    iEval (rewrite Hil10) in "Hlk_name".
    iEval (rewrite Hil10) in "Hcpu_zero".
    iEval (rewrite Hil1) in "Hret".
    iApply ("Hcont" $! mr with "Hcg Hret [//] Hlk_zero Hlk_name Hcpu_zero").
  Admitted.

End ProofIinit.

End IinitProof.
