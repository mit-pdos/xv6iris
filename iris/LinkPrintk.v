(* LinkPrintk.v -- instantiates the Printk proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet.

   printk gained [acquire]/[release] as callees with upstream d80e61c5: the
   [panicking] flag is gone, so pr.lock is now taken unconditionally.  At
   163d39b the character sink became [prputc] -- uartputc_sync at the SECOND
   16550 -- so [Consputc] left this functor's argument list and [Prputc] took
   its place.  consputc keeps its own Spec/Proof/Link for the console's path.

   Also proves [SpecPrintk]'s WEAK COROLLARY -- the [PRINTK_GEN] module type
   -- as a one-shot corollary of [Printk.wp_printk_sconf] instead of assuming
   it (formerly the deleted LinkPrintkGen.v's [Axiom]):

     - [n := 0] -- the general path always leaves the interrupt level
       net-zero, which is exactly [n] at its trivial instance.  There is no
       [bs] to instantiate any more: nothing tracks the second port's wire, so
       printk's full contract carries no trace claim either
       ([SpecPrputc.v]).
     - the credentials come straight out of [printk_env], which is now
       pr.lock's [is_lock] and [SpecPrputc.prputc_env] and nothing else.
     - there is NO panic credential to supply: acquire's
       [if(holding(lk)) panic] arm is refuted (SpecAcquire.v), so nothing in
       the printk cone asks for one and this file no longer reaches
       a panic credential at all.
     - the postcondition WEAKENS (drops the return-value fact), which is a
       plain [wp_next] reindex -- no new hart-transport needed since both
       sides share the caller's ambient [CID]. *)
From Stdlib Require Import ZArith String.
Require Import Stdlib.micromega.Lia.
From stdpp Require Import list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpLock DiskPtsto.
Require Import UartNames.
Require Import LinkPrputc LinkPrintint LinkAcquire LinkRelease ProofPrintk.
Require Import SpecPrintk.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.

Module Printk := PrintkProof Prputc Printint Acquire Release.

Module PrintkGen : PRINTK_GEN.
  Lemma wp_printk_gen_sconf `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      {kt : ktier} (γpr : gname) (γd : uart_names) (γv : disk_names)
      (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64)
      {dqf : dfrac} (f : string) (descs : list pk_arg_desc) (b : bool)
      (lks : gset string) :
    wp_printk_gen_sconf_body kt γpr γd γv m0 K eb pj dqf f descs b lks.
  Proof.
    rewrite /wp_printk_gen_sconf_body /=.
    intros HK Hlen Hnonul Hkinds Hdlen Hbelow.
    iIntros "Hcap Htext Hkdata Hpc Hcpu Hpenv Hfmt Hdescs Hcont".
    iDestruct "Hpenv" as "(#Hprlk & #Hpre)".
    iApply (Printk.wp_printk_sconf kt γpr m0 K 0%nat eb
              (dqf := dqf) f descs b pj lks
              ltac:(lia)
              Hlen Hnonul Hkinds Hdlen ltac:(lia)
              with "Hcap Hcpu Htext Hkdata Hpc Hfmt Hdescs Hprlk Hpre").
    all: try lkbelow.
    iIntros (CID2 Hpin).
    iDestruct ("Hcont" $! CID2 Hpin) as "Hcont2".
    iIntros (mf) "Hcap2 Hcpu2 Hpc2 %Hpost Hfmt2 Hdescs2".
    iApply ("Hcont2" $! mf with "Hcap2 Hpc2 [%] Hcpu2 Hfmt2 Hdescs2").
    { destruct Hpost as (Hcs & Hra & _). done. }
  Qed.
End PrintkGen.

(* [printk_gen_contract]'s only role right now is a hypothesis threaded by
   the fs.c error arms (SpecBalloc.v and friends) -- none of it is composed
   into the boot chain yet, so nothing needs a witness that it holds.  When
   one does, it is [fun CIDp => PrintkGen.wp_printk_gen_sconf (CID := CIDp)]. *)
