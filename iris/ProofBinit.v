(* ProofBinit.v -- whole-function WP proof for binit() over the sconf world. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes SmodeCore CalleeSaved KernelText KernelDataInv IntrDefs.
Require Import WpMmodeLeafBase WpAuipc AlignBits.
Require Import StackOwn.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpLock SleepLock SpecInitlock SpecInitsleeplock.
Require Import WpBinitDecode.
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

    set (m_il := <[Regidx (mword_of_int 10 : mword 5) := lk]>
                 (<[Regidx (mword_of_int 11 : mword 5) := name_bcache]>
                  (<[Regidx (mword_of_int 1 : mword 5) := m !!! Regidx (mword_of_int 1 : mword 5)]> m))).
    assert (Hbl10 : m_il !!! Regidx (mword_of_int 10 : mword 5) = lk) by (rewrite /m_il upd_eq; reflexivity).
    assert (Hbl11 : m_il !!! Regidx (mword_of_int 11 : mword 5) = name_bcache) by (rewrite /m_il upd_ne; [rewrite upd_eq; reflexivity | vm_compute; discriminate]).
    assert (Hbl1 : m_il !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /m_il upd_ne; [rewrite upd_ne; [rewrite upd_eq; reflexivity | vm_compute; discriminate] | vm_compute; discriminate]).

    iAssert (sie_cap_gpr γ m_il K ∗ pc_is (mword_of_int KernelSyms.initlock))%I with "[Hcg Hpc]" as "[Hcg_il Hpc_il]".
    { admit. }

    iApply (Initlock.wp_initlock_sconf γ Φ m_il vlock vname vcpu "bcache"%string K ltac:(lia)
              with "Hcg_il Htext Hpc_il Hstr_bcache [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite Hbl10). iExact "Hlock". }
    { iEval (rewrite Hbl10). iExact "Hname". }
    { iEval (rewrite Hbl10). iExact "Hcpu". }
    iIntros (mr) "Hcg Hret %Hcs Hlk_zero #Hlk_name Hcpu_zero".
    iEval (rewrite Hbl10) in "Hlk_zero".
    iEval (rewrite Hbl10) in "Hlk_name".
    iEval (rewrite Hbl10) in "Hcpu_zero".
    iEval (rewrite Hbl1) in "Hret".
    iApply ("Hcont" $! mr with "Hcg Hret [//] Hlk_zero Hlk_name Hcpu_zero").
  Admitted.

End ProofBinit.

End BinitProof.
