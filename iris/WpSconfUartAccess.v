(* WpSconfUartAccess.v -- call-site-specialized S-mode UART device-access leaves
   over the sconf accessor forms.

   These are single-instruction leaf WPs built on the general UART device leaves
   [Uart.wp_lb_uart_s_sconf] / [Uart.wp_sb_uart_s_sconf]: they pre-discharge the
   constant PTE/geometry premises (the caller supplies only that the base
   register already holds the concrete UART register address [uart_pa off]) and
   package the transmitter-token protocol.  The reuse pattern for any device-MMIO
   S-mode instruction while holding [dev_inv] + the transmitter token:
     - [wp_uart_lsr_read_s_sconf]  : LSR poll load (offset 5)
     - [wp_uart_thr_write_s_sconf] : THR write (offset 0)

   A functor over UART so a function proof (e.g. UartPutc) instantiates it against
   the sealed [Uart] instance; the leaves live here, out of the whole-function
   proof file. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import DevModel WpUart.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import SpecUart.
Require Import WpUartPutcSync.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Module UartAccessProof (Uart : UART).
Section WpSconfUartAccess.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{CID : CpuId}.

  (* The LSR poll load (offset 5).  Takes [dev_inv] + the transmitter token;
     hands back the token and -- IF the read byte says THRE was set -- the
     [uart_out_lb] bound that makes the observation survive to a later THR
     write ([uart_tx_ready_persists], WpUart.v). *)
  Lemma wp_uart_lsr_read_s_sconf (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ) (pc : mword 64) (rd rs1 : mword 5)
      (m : regfile) (n : nat) (l : list (bv 8)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    m !!! Regidx rs1 = uart_pa 5 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc false (LOAD (mword_of_int 0 : mword 12, Regidx rs1, Regidx rd, true, 1)) -∗
    dev_inv γd -∗ uart_tx_own γd l -∗
    ( ∀ b : bv 8,
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (lsr_ldval_of b)]> m) n -∗
      pc_is (add_vec_int pc 4) -∗
      uart_tx_own γd l -∗
      (⌜ lsr_thre_clear b = false ⌝ -∗ uart_out_lb γd l) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Haddr) "Hcg Hpc Hinstr #Hdinv Hown Hcont".
    iApply (Uart.wp_lb_uart_s_sconf γ γd 5 Φ pc false true rd rs1 (mword_of_int 0 : mword 12)
              m n (uart_tx_own γd l)
              (fun b => uart_tx_own γd l ∗ (⌜ lsr_thre_clear b = false ⌝ -∗ uart_out_lb γd l))%I
              ltac:(unfold uart_size; lia) Hrd Hrdsp
              ltac:(rewrite Haddr; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hinstr Hdinv Hown [] [Hcont]").
    - iIntros (u b u') "%Hread Hg Hown".
      rewrite uart_read_lsr in Hread. injection Hread as <- <-.
      iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
      destruct (uart_thre u) eqn:Hthre.
      + iDestruct (uart_tx_poll_thre γd u l Hthre with "Hown Htx Hout")
          as "(Hown & Htx & Hout & #Hlb & %Hfacts)".
        iModIntro. iFrame "Hs Hout Htx Hdl Hown". iIntros (_). iExact "Hlb".
      + iModIntro. iFrame "Hs Hout Htx Hdl Hown".
        iIntros (Hc). rewrite (uart_nothre_beqz u Hthre) in Hc. discriminate.
    - iIntros (b) "Hcg Hpc [Hown Hlb]".
      iApply ("Hcont" $! b with "Hcg Hpc Hown Hlb").
  Qed.

  (* The THR write (offset 0).  The caller brings the transmitter token, the
     out-bound the poll handed back, and the frozen DLAB fact;
     [uart_tx_ready_persists] turns them into [uart_write_thr_acc]'s two
     premises at the write's own state, so the byte provably lands in the FIFO.
     Postcondition: the grown token plus a permanent [uart_sent] record. *)
  Lemma wp_uart_thr_write_s_sconf (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ) (pc : mword 64) (rs2 rs1 : mword 5)
      (m : regfile) (n : nat) (l : list (bv 8)) :
    m !!! Regidx rs1 = uart_pa 0 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc false (STORE (mword_of_int 0 : mword 12, Regidx rs2, Regidx rs1, 1)) -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_out_lb γd l -∗ uart_dlab_off γd -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      uart_tx_own γd (l ++ [autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8]) -∗
      uart_sent γd (l ++ [autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8]) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Haddr) "Hcg Hpc Hinstr #Hdinv Hown #Hlb #Hoff Hcont".
    set (sb := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8).
    iApply (Uart.wp_sb_uart_s_sconf γ γd 0 Φ pc false rs2 rs1 (mword_of_int 0 : mword 12)
              m n (uart_tx_own γd l)
              (uart_tx_own γd (l ++ [sb]) ∗ uart_sent γd (l ++ [sb]))%I
              ltac:(unfold uart_size; lia)
              ltac:(rewrite Haddr; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hinstr Hdinv Hown [] [Hcont]").
    - iIntros (u u') "%Hwrite Hg Hown".
      iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
      iDestruct (uart_tx_ready_persists γd u l with "Hown Hlb Hoff Htx Hout Hdl") as %[Hempty Hdlab].
      iDestruct (uart_tx_own_agree with "Htx Hown") as %Haccu.
      assert (Hroom : (length (u_tx u) < uart_fifo_depth)%nat).
      { rewrite Hempty. cbn [length]. unfold uart_fifo_depth. lia. }
      assert (Hacc' : uart_acc u' = l ++ [sb]).
      { rewrite (uart_write_thr_acc u sb u' Hdlab Hroom Hwrite) Haccu. reflexivity. }
      iMod (uart_tx_own_update γd u l u' with "Htx Hown") as "[Htx Hown]".
      iMod (uart_sent_update γd u u' with "Hs") as "[Hs Hsent]".
      { rewrite Haccu Hacc'. by apply prefix_app_r. }
      iDestruct (uart_out_auth_stable γd u u' (uart_write_out _ _ _ _ Hwrite) with "Hout") as "Hout".
      iDestruct (uart_dlab_auth_stable γd u u' (uart_write_dlab_0 _ _ _ Hwrite) with "Hdl") as "Hdl".
      iEval (rewrite Hacc') in "Hown". iEval (rewrite Hacc') in "Hsent".
      iModIntro. rewrite /uart_ghosts. iFrame "Hs Hout Htx Hdl Hown Hsent".
    - iIntros "Hcg Hpc [Hown Hsent]".
      iApply ("Hcont" with "Hcg Hpc Hown Hsent").
  Qed.

End WpSconfUartAccess.
End UartAccessProof.
