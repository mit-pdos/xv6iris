(* ProofTrapinit.v -- the whole-function WP for xv6's trapinit() over the
   SIE-agnostic sconf world.

     void trapinit(void) { initlock(&tickslock, "time"); }

   trapinit is a thin initlock wrapper, so it is an INSTANCE of the shape
   proved once in WpInitlockWrapper.v: all this file supplies is trapinit's
   thirteen instructions (CodeTrapinit.v, bundled as [tri_code] below) and the
   three relocations
   -- a1 = &"time" (auipc 0x5 / addi -472), a0 = &tickslock (auipc 0x16 /
   addi -576), and the jal displacement to initlock. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import KernelDataInv.
Require Import SpecInitlock SpecInitlockWrapper WpInitlockWrapper.
Require Import KernelText CodeTrapinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecTrapinit.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section CodeTrapinitBundle.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* trapinit's thirteen instructions (CodeTrapinit.v), in the
     thin-initlock-wrapper pattern.  The five immediates are exactly what the
     whole-function proof needs to know about trapinit's code. *)
  Lemma tri_code :
    kernel_text -∗ ilw_code KernelSyms.trapinit (mword_of_int 5) (mword_of_int 22)
                            (mword_of_int 3642) (mword_of_int 3506) (mword_of_int 2090748).
  Proof.
    iIntros "#Ht". rewrite /ilw_code.
    iSplitR; [iApply (tri_00 with "Ht")|].
    iSplitR; [iApply (tri_02 with "Ht")|].
    iSplitR; [iApply (tri_04 with "Ht")|].
    iSplitR; [iApply (tri_06 with "Ht")|].
    iSplitR; [iApply (tri_08 with "Ht")|].
    iSplitR; [iApply (tri_0c with "Ht")|].
    iSplitR; [iApply (tri_10 with "Ht")|].
    iSplitR; [iApply (tri_14 with "Ht")|].
    iSplitR; [iApply (tri_18 with "Ht")|].
    iSplitR; [iApply (tri_1c with "Ht")|].
    iSplitR; [iApply (tri_1e with "Ht")|].
    iSplitR; [iApply (tri_20 with "Ht")|].
    iApply (tri_22 with "Ht").
  Qed.

End CodeTrapinitBundle.

Module TrapinitProof (Initlock : INITLOCK) : TRAPINIT.

Module ILW := InitlockWrapperProof Initlock.

Section ProofTrapinit.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_trapinit_sconf
      (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64)
    : wp_trapinit_sconf_body m K vlock vname vcpu b p.
  Proof.
    cbv beta delta [wp_trapinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    (* &"time" is proof-local: the spec speaks of the lock's NAME, not of the
       address the image happens to keep the literal at. *)
    pose (name := (mword_of_int time_name_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hlock Hname Hcpu Hcont".
    (* the "time" string literal (4 chars + NUL), read out of the data image *)
    assert (Htime : forall j bt, cstring_bytes "time"%string !! j = Some bt ->
                      KernelData.kernel_data !! (time_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 5 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string_all time_name_str "time"%string name eq_refl ltac:(unfold text_end, time_name_str; lia)
                                                                            ltac:(vm_compute; discriminate) Htime
                  with "Hkdata") as "#Hstr".
    iApply (ILW.wp_initlock_wrapper_sconf KT1 m K KernelSyms.trapinit
              (mword_of_int 5) (mword_of_int 22) (mword_of_int 3642) (mword_of_int 3506)
              (mword_of_int 2090748) lk name "time"%string vlock vname vcpu b p HK
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Htext [] Hpc Hstr Hlock Hname Hcpu Hcont").
    iApply (tri_code with "Htext").
  Qed.

End ProofTrapinit.

End TrapinitProof.
