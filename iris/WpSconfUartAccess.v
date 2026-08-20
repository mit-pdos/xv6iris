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
Require Import RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import DevModel DiskPtsto WpUart.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import SpecUart.
Require Import WpSmodeUart.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The LSR poll's read value and branch test, as functions of the byte   *)
(*  the device returned.  The device state is shared, so a poll cannot    *)
(*  name the byte in advance: everything downstream is phrased in terms   *)
(*  of [b] and only re-connected to the UART inside a leaf's ghost step.  *)
(* ===================================================================== *)

(* the value the [lbu] leaf writes back for a read byte [b] *)
(* the vmem level hands back the value itself now, not the split accumulator *)
Definition lsr_ldval_of (b : mword (8*1)) : mword 64 := extend_value true b.

(* THE POLL'S BRANCH TEST: [andi a5,a5,32] then [c.beqz a5].
   True = THRE clear = branch taken = spin again. *)
Definition lsr_thre_clear (b : bv 8) : bool :=
  eq_vec (and_vec (lsr_ldval_of b) (sign_extend' 64 (mword_of_int 32 : mword 12))) zero_reg.

(* THRE clear really does take the branch, so the two cases of the poll are
   exactly [uart_thre u]. *)
Lemma uart_nothre_beqz (u : uart_state) :
  uart_thre u = false -> lsr_thre_clear (uart_lsr u) = true.
Proof.
  intro H. unfold lsr_thre_clear, lsr_ldval_of, uart_lsr. rewrite H.
  destruct (uart_rx_ready u); vm_compute; reflexivity.
Qed.

Module UartAccessProof (Uart : UART).
Section WpSconfUartAccess.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context {kt : ktier}.
  (* ==================================================================== *)
  (* THE READ-SIDE SIDE CONDITION [SrcOk] ON EVERY LEAF IN THIS SECTION.   *)
  (* Read once; each leaf below carries a three-line pointer back here.    *)
  (*                                                                      *)
  (* WHAT IT IS.  These leaves take their operands out of CALLER-CHOSEN    *)
  (* registers, spelled [rget m rs] -- a lookup in [tp_pin m] (HartTp.v),  *)
  (* which is [m] with tp's slot overwritten by THIS HART's id.  So the    *)
  (* value depends on the ambient hart at exactly one register, rs = tp,   *)
  (* and agrees at every other ([HartTp.rget_hart_indep]).  Those operands *)
  (* are computed from the ENTRY map, at the hart we came from, and appear *)
  (* again inside the [wp_next] lambda, where every resource is about the  *)
  (* hart we resume on.  Today the funnel's sigma-callback is instantiated  *)
  (* at the entry hart so the two coincide; once that callback moves       *)
  (* inside [WpNext.wp_next] -- so an instruction can execute on the hart  *)
  (* a trap returned to -- the obligation arrives at the REBOUND hart      *)
  (* while the caller's premise was stated at the ENTRY hart, and they     *)
  (* agree only away from tp.  [IntrDefs.SrcOk rs] is that side condition. *)
  (*                                                                      *)
  (* WHY A CLASS AND NOT A PREMISE.  These leaves have no premise slot     *)
  (* whose MEANING could be widened for free: a store writes no register   *)
  (* at all, and a load's [rd_ok] slot is about the DESTINATION, not the   *)
  (* source.  An ordinary premise would change ARITY at every reference,   *)
  (* each of which would need a positional [ltac:(...)] in the right       *)
  (* place.  An implicit instance argument shifts no positional argument,  *)
  (* so the family converts with ZERO call-site churn -- and it cannot be  *)
  (* [ops_ok] either, whose source conjuncts are guarded on [b = true]     *)
  (* while an address has to be hart-independent at [b = true] as well.    *)
  (* Multi-source leaves take ONE CLASS ARGUMENT PER SOURCE; they resolve  *)
  (* independently, so there is no combinatorial blow-up.                  *)
  (*                                                                      *)
  (* THE PREMISES STAY SPELLED [rget m rs].  Respelling them hart-free as  *)
  (* [m !!! Regidx rs] was MEASURED (on [WpSconfMem.wp_csdsp_s_sconf]) and *)
  (* rejected: it breaks 99 consumer files, because callers normalise with *)
  (* [rget]-shaped rewrites that then have nothing to match.  So the class *)
  (* carries the side condition, the spelling does not move, and the       *)
  (* reconciliation happens INSIDE each proof in one line, via             *)
  (* [IntrDefs.src_ok_rget_indep].                                         *)
  (*                                                                      *)
  (* THAT LINE IS ALSO THE LEAF'S WIRING CHECK, so do not delete it as an  *)
  (* unused hypothesis: it names the register the premise reads, so a      *)
  (* class attached to the wrong parameter fails to typecheck HERE instead  *)
  (* of shelving silently at a consumer's [Qed] -- an unresolved instance  *)
  (* inside an [iApply] is SHELVED, not reported.                          *)
  (* ==================================================================== *)

  Context `{GEN : GenId} `{CID : CpuId}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* The LSR poll load (offset 5).  Takes [dev_inv] + the transmitter token;
     hands back the token and -- IF the read byte says THRE was set -- the
     [uart_out_lb] bound that makes the observation survive to a later THR
     write ([uart_tx_ready_persists], WpUart.v). *)
  (* generalized over the DISPLACEMENT: gcc emits the LSR read either as
     [lbu a5,0(a4)] off a base register already holding UART0+5
     (uartputc_sync) or as [lbu a5,5(a5)] off one holding UART0 (uartintr).
     The [imm = 0] restatement below keeps the original callers unchanged. *)
  Lemma wp_uart_lsr_read_ea_s_sconf (γd : uart_names) (γv : disk_names) (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (l : list (bv 8)) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    add_vec (rget m rs1) (sign_extend' 64 imm) = uart_pa 5 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ bt : bv 8,
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (lsr_ldval_of bt)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      uart_tx_own γd l -∗
      (⌜ lsr_thre_clear bt = false ⌝ -∗ uart_out_lb γd l) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Haddr) "Hcg Hpc Hinstr #Hdinv Hown Hcont".
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Haddr_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = uart_pa 5)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Haddr).
    iApply (Uart.wp_lb_uart_s_sconf kt (CID:=CID) γd γv 5 pc false true rd rs1 imm
              m n (uart_tx_own γd l)
              (fun bt => uart_tx_own γd l ∗ (⌜ lsr_thre_clear bt = false ⌝ -∗ uart_out_lb γd l))%I b p
              ltac:(unfold uart_size; lia) Hrd Hrdok
              ltac:(rewrite Haddr; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hinstr Hdinv Hown [] [Hcont]").
    - iIntros (u bt u') "%Hread Hg Hown".
      rewrite uart_read_lsr in Hread. injection Hread as <- <-.
      iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
      destruct (uart_thre u) eqn:Hthre.
      + iDestruct (uart_tx_poll_thre γd u l Hthre with "Hown Htx Hout")
          as "(Hown & Htx & Hout & #Hlb & %Hfacts)".
        iModIntro. iFrame "Hs Hout Htx Hdl Hown". iIntros (_). iExact "Hlb".
      + iModIntro. iFrame "Hs Hout Htx Hdl Hown".
        iIntros (Hc). rewrite (uart_nothre_beqz u Hthre) in Hc. discriminate.
    - iEval (rewrite /wp_next). iIntros (CID1 Hs1 bt) "Hcg Hpc [Hown Hlb]".
      iSpecialize ("Hcont" $! CID1 with "[]"); [iPureIntro; exact Hs1|].
      iApply ("Hcont" $! bt with "Hcg Hpc Hown Hlb").
  Qed.

  (* the original, zero-displacement form (uartputc_sync's call site).
     [SrcOk rs1] rides along to the [_ea] form.  The [exact] below is a DIRECT
     application, so an instance attached to the wrong parameter is reported
     here ("Cannot infer the implicit parameter ... SrcOk ...") rather than
     shelved -- which is why this wrapper needs no consuming [assert]. *)
  Lemma wp_uart_lsr_read_s_sconf (γd : uart_names) (γv : disk_names) (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1}
      (m : regfile) (n : nat) (l : list (bv 8)) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    rget m rs1 = uart_pa 5 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (LOAD (mword_of_int 0 : mword 12, Regidx rs1, Regidx rd, true, 1)) -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ bt : bv 8,
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (lsr_ldval_of bt)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      uart_tx_own γd l -∗
      (⌜ lsr_thre_clear bt = false ⌝ -∗ uart_out_lb γd l) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrd Hrdok Haddr.
    exact (wp_uart_lsr_read_ea_s_sconf γd γv pc rd rs1 (mword_of_int 0 : mword 12)
             m n l b Hrd Hrdok
             ltac:(rewrite Haddr; apply bv_eq; vm_compute; reflexivity)).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* A UART register read with NO ghost obligation at all.                *)
  (* ------------------------------------------------------------------ *)
  (* No read moves any of the three tracked TX quantities: only the RHR read
     advances the device, and it pops the RECEIVE FIFO, which appears in
     neither [uart_acc] nor [u_out] nor [uart_dlab] ([DevModel.uart_read_stable]).
     So a driver that merely wants the byte needs no transmitter token and no
     [uart_out_lb] -- this one leaf serves uartintr's ISR acknowledge and both
     of uartgetc's accesses (the rx-ready poll and the RHR pop), at ANY of the
     eight register offsets and with the displacement in the INSTRUCTION
     ([lbu a5,5(a5)] off a base register holding UART0, which is how gcc emits
     them) rather than pre-added into the base. *)

  (* the constant Sv39 geometry of the UART page, at every register offset:
     the address is canonical, its vpn is [uart_vpn], and the leaf ppn
     recomposes to the address.  Discharged by an eight-way case split, since
     each offset is then a closed term. *)
  Local Lemma uart_geom_ok (off : Z) :
    (0 <= off < uart_size)%Z ->
    let a8 := sign_extend' 64 (subrange_vec_dec (uart_pa off) (xlen - 0 - 1) 0) in
    neq_vec (bits_of_virtaddr (Virtaddr a8))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false
    /\ autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)
         (Z.sub 39 1) pagesize_bits) = uart_vpn
    /\ zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off.
  Proof.
    unfold uart_size. intro Hoff.
    assert (Hc : off = 0 \/ off = 1 \/ off = 2 \/ off = 3 \/
                 off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
    destruct Hc as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst off; cbn zeta;
      (split; [vm_compute; reflexivity
              | split; [apply bv_eq; vm_compute; reflexivity
                       | apply bv_eq; vm_compute; reflexivity]]).
  Qed.

  Lemma wp_uart_read_free_s_sconf (γd : uart_names) (γv : disk_names)
      (off : Z) (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    (0 <= off < uart_size)%Z ->
    uint rd <> 0 ->
    rd_ok rd ->
    add_vec (rget m rs1) (sign_extend' 64 imm) = uart_pa off ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    dev_inv γd γv -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ bt : bv 8,
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (lsr_ldval_of bt)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hoff Hrd Hrdok Haddr) "Hcg Hpc Hinstr #Hdinv Hcont".
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Haddr_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = uart_pa off)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Haddr).
    destruct (uart_geom_ok off Hoff) as (Hg1 & Hg2 & Hg3).
    iApply (Uart.wp_lb_uart_s_sconf kt (CID:=CID) γd γv off pc false true rd rs1 imm
              m n emp%I (fun _ => emp%I) b p
              Hoff Hrd Hrdok
              ltac:(rewrite Haddr; exact Hg1)
              ltac:(rewrite Haddr; exact Hg2)
              ltac:(rewrite Haddr; exact Hg3)
              with "Hcg Hpc Hinstr Hdinv [] [] [Hcont]").
    - done.
    - iIntros (u bt u') "%Hread Hg _".
      destruct (uart_read_stable u off bt u' Hread) as (Ha & Ho & Hd).
      iModIntro. iSplitL "Hg"; [| done].
      iApply (uart_ghosts_stable γd u u' Ha Ho Hd with "Hg").
    - iEval (rewrite /wp_next). iIntros (CID1 Hs1 bt) "Hcg Hpc _".
      iSpecialize ("Hcont" $! CID1 with "[]"); [iPureIntro; exact Hs1|].
      iApply ("Hcont" $! bt with "Hcg Hpc").
  Qed.

  (* The THR write (offset 0).  The caller brings the transmitter token, the
     out-bound the poll handed back, and the frozen DLAB fact;
     [uart_tx_ready_persists] turns them into [uart_write_thr_acc]'s two
     premises at the write's own state, so the byte provably lands in the FIFO.
     Postcondition: the grown token plus a permanent [uart_sent] record. *)
  Lemma wp_uart_thr_write_s_sconf (γd : uart_names) (γv : disk_names) (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2}
      (m : regfile) (n : nat) (l : list (bv 8)) (b : bool) :
    (* the stored byte reads [rs2] at the hart we ENTER on, so it must be
       bound OUTSIDE the [wp_next] lambda (which rebinds [CID], and would
       silently re-read [rs2] -- i.e. [tp] -- at the RESUMING hart). *)
    let sb : mword 8 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 1 8) 1) 0) in
    rget m rs1 = uart_pa 0 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (STORE (mword_of_int 0 : mword 12, Regidx rs2, Regidx rs1, 1)) -∗
    dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_out_lb γd l -∗ uart_dlab_off γd -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      uart_tx_own γd (l ++ [sb]) -∗
      uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sb.
    iIntros (Haddr) "Hcg Hpc Hinstr #Hdinv Hown #Hlb #Hoff Hcont".
    (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Haddr_all : forall hh : CpuId, rget (CID := hh) m rs1 = uart_pa 0)
      by (intros hh; rewrite (src_ok_rget_indep m rs1 hh CID); exact Haddr).
    assert (Hsb_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iApply (Uart.wp_sb_uart_s_sconf kt (CID:=CID) γd γv 0 pc false rs2 rs1 (mword_of_int 0 : mword 12)
              m n (uart_tx_own γd l)
              (uart_tx_own γd (l ++ [sb]) ∗ uart_sent γd (l ++ [sb]))%I b p
              ltac:(unfold uart_size; lia)
              ltac:(rewrite Haddr; vm_compute; reflexivity)
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
    - iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc [Hown Hsent]".
      iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hown Hsent").
      iPureIntro. exact Hs1.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block.  x14/x15        *)
  (* (a4/a5) are the registers uartputc_sync / uartintr actually hold the  *)
  (* UART base in.                                                        *)
  (* ------------------------------------------------------------------- *)
  Definition uacc_srcok_pos_a4 : SrcOk (mword_of_int 14 : mword 5) := _.
  Definition uacc_srcok_pos_a5 : SrcOk (mword_of_int 15 : mword 5) := _.
  Fail Definition uacc_srcok_neg : SrcOk Rtp := _.

End WpSconfUartAccess.
End UartAccessProof.
