(* LinkPrputc.v -- instantiates the Prputc proof against its callee's proof.
   Sealed, so this is the only place the two ever meet.

   AND IT IS THE ONLY PLACE THAT NAMES uartputc_sync's ARGUMENT ORDER.
   [ProofPrputc.v] takes the callee's contract as an INLINE hypothesis --
   the premises it actually consumes, spelled out -- rather than as
   [SpecUartPutc.wp_uartputc_sconf_body], precisely so that the port-indexed
   spelling that lane settles on costs one adapter here and nothing in the
   body.  [up_adapt] below is that adapter.  It instantiates uartputc_sync at

     - the PORT [Uart1] (its contract gained a [uart_id] parameter at
       XV6_REV 163d39b, with a0 pinned to [UartsFields.uart_index i]);
     - the trace [bs := []], the empty [UartTxInv.uart_sent_sub] ProofPrputc
       minted from nothing;

   and DROPS the [uart_sent_sub γ1 ([] ++ [sb])] that comes back.  That drop
   is the whole of the owner's ruling in one line: the second port's wire is
   unconstrained, so what uartputc_sync proves about the byte is thrown away
   here and never appears above.  (Iris is affine; dropping a persistent
   witness costs nothing.) *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes WpMmodeLeafBase WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import DevModel UartsFields.
Require Import DiskPtsto WpUart.
Require Import IntrDefs LockRank CpuOwn.
Require Import UartTxInv.
Require Import SpecUartPutc SpecPrputc.
Require Import LinkUartPutc ProofPrputc.
From Kernel Require KernelSyms.
Require Import Xv6G.
Require Import TsoCtx.

Module Prputc : PRPUTC.

Section LinkPrputc.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context {kt : ktier}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).

  Lemma up_adapt `{CID0 : CpuId} (γl1 : gname) (γ1 : uart_names)
      (m0 : regfile) (K : nat) (n : nat) (eb : bool) (b : bool) (p : mword 64)
      (lks : gset string) :
    (18 <= K)%nat ->
    m0 !!! Regidx a0_idx = (mword_of_int (uart_index Uart1) : mword 64) ->
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    locks_below lks "uart1" ->
    sie_cap_gpr kt m0 K b p -∗
    cpu_own n eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int KernelSyms.uartputc_sync : mword 64) -∗
    uart_inv Uart1 γ1 -∗
    uart_base_word Uart1 -∗
    is_txlock_at Uart1 γl1 γ1 -∗
    uart_sent_sub γ1 [] -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
      sie_cap_gpr kt mf K b p -∗
      cpu_own n eb p b lks -∗
      pc_is (ret_pc (m0 !!! Regidx ra_idx)) -∗
      ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = m0 !!! Regidx ra_idx ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Ha0 Hn Hbelow.
    iIntros "Hcg Hcpu #Htext Hpc #Huinv #Hbase #Htxl #Hsub Hcont".
    iApply (UartPutc.wp_uartputc_sconf kt Uart1 (CID := CID0) γl1 γ1 m0 K []
              n eb b p lks HK Ha0 Hn Hbelow
              with "Hcg Hcpu Htext Hpc Huinv Hbase Htxl Hsub").
    iIntros (CID1 Hs1 mf) "Hcg Hcpu Hpc %Hcs _".
    iSpecialize ("Hcont" $! CID1 with "[%]"); [exact Hs1|].
    iApply ("Hcont" $! mf with "Hcg Hcpu Hpc [%]"). exact Hcs.
  Qed.

End LinkPrputc.

  Definition wp_prputc_sconf `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      {kt : ktier} (m0 : regfile) (K : nat)
      (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string)
      : wp_prputc_sconf_body kt m0 K n eb b p lks :=
    (* eta-expanded so the adapter's own [CID0] stays genuinely polymorphic
       per application (ProofConsputc.v's identical fix), rather than being
       eagerly specialized to THIS definition's [CID]. *)
    wp_prputc_sconf_gen
      (fun `(CID0 : CpuId) γl1' γ1' m' K' n' eb' b' p' lks' =>
         up_adapt (kt := kt) (CID0 := CID0) γl1' γ1' m' K' n' eb' b' p' lks')
      m0 K n eb b p lks.

End Prputc.
