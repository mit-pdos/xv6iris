(* LinkPrintk.v -- instantiates the Printk proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet.

   printk gained [acquire]/[release] as callees with upstream d80e61c5: the
   [panicking] flag is gone, so pr.lock is now taken unconditionally.

   Also proves [SpecPrintk]'s WEAK COROLLARY -- the [PRINTK_GEN] module type
   -- as a one-shot corollary of [Printk.wp_printk_sconf] instead of assuming
   it (formerly the deleted LinkPrintkGen.v's [Axiom]):

     - [n := 0], [bs := []] -- the general path always leaves the interrupt
       level net-zero and makes no trace claim, which is exactly [n]/[bs] at
       their trivial instances.
     - [γl] and [uart_sent_sub γd []] come out of [printk_env] itself.
     - [panic_wp_any] comes from [LinkPanicStub.panic_wp_any_holds] directly
       -- the SAME assumed axiom [Hpanic : panic_wp] already traces to, so
       this adds no new name to [Print Assumptions].
     - the postcondition WEAKENS (drops the trace claim and the return-value
       fact), which is a plain [wp_next] reindex -- no new hart-transport
       needed since both sides share the caller's ambient [CID]. *)
From Stdlib Require Import ZArith String.
Require Import Stdlib.micromega.Lia.
From stdpp Require Import list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock DiskPtsto WpUart PanicStub.
Require Import LinkConsputc LinkPrintint LinkAcquire LinkRelease ProofPrintk.
Require Import LinkPanicStub.
Require Import SpecPrintk.

Module Printk := PrintkProof Consputc Printint Acquire Release.

Module PrintkGen : PRINTK_GEN.
  Lemma wp_printk_gen_sconf `{!riscvGS Σ, !sieG Σ, !lockG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γpr : gname) (γd : uart_names) (γv : disk_names)
      (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
      {dqf : dfrac} (f : string) (descs : list pk_arg_desc) (b : bool)
      (lks : gset nat) :
    wp_printk_gen_sconf_body γpr γd γv m0 K eb pj C dqf f descs b lks.
  Proof.
    rewrite /wp_printk_gen_sconf_body /=.
    intros HK Hlen Hnonul Hkinds Hdlen Hbelow.
    iIntros "Hcap Htext Hkdata Hpc Hpanic Hcpu Hpenv Hfmt Hdescs Hcont".
    iDestruct "Hpenv" as "(#Hprlk & #Hdoff & #Hdev & [%γl #Htxl] & #Hsub0)".
    iAssert (panic_wp_any) as "#Hpa".
    { iApply panic_wp_any_holds. }
    iApply (Printk.wp_printk_sconf γpr γl γd γv m0 K [] 0%nat eb C
              (dqf := dqf) f descs b pj lks
              ltac:(rewrite /printk_stack; lia)
              Hlen Hnonul Hkinds Hdlen ltac:(lia)
              with "Hcap Hcpu Htext Hkdata Hpc Hpa Hfmt Hdescs Hprlk Hdev Htxl Hsub0").
    all: try lkbelow.
    iIntros (CID2 Hpin).
    iDestruct ("Hcont" $! CID2 Hpin) as "Hcont2".
    iIntros (mf cs) "Hcap2 Hcpu2 Hpc2 %Hpost Hfmt2 Hdescs2 Hsub2".
    iApply ("Hcont2" $! mf with "Hcap2 Hpc2 [%] Hcpu2 Hfmt2 Hdescs2").
    { destruct Hpost as (Hcs & Hra & _). done. }
  Qed.
End PrintkGen.

(* [printk_gen_contract]'s only role right now is a hypothesis threaded by
   the fs.c error arms (SpecBalloc.v and friends) -- none of it is composed
   into the boot chain yet, so nothing needs a witness that it holds.  When
   one does, it is [fun CIDp => PrintkGen.wp_printk_gen_sconf (CID := CIDp)]. *)
