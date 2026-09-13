(* ProofUartintr.v -- the whole-function WP for xv6's uartintr().

     void uartintr(int uid)

   The contract is SpecUartintr.v; the 47 instruction facts are
   CodeUartintr.v ([uii2_<off>]).  Structure of the proof:

   - [ui_tail] is the epilogue at +0x76 (three restores, frame pop, ret).
   - [ui_rx] is the receive drain at +0x46: an iLoeb, because the device may
     keep supplying bytes.  Its body is [WpUartgetc.wp_uartgetc_inline] --
     uartgetc, which gcc inlines and which never had a symbol -- followed by
     the `u->rx` dispatch.
   - [ui_rx_setup] is the preamble at +0x2e that rebuilds `&uarts[uid]` in s1
     and materialises the two MMIO pointers out of it; BOTH arms of the THRE
     test reach it (the wakeup arm jumps back from +0x74), so it is a lemma
     rather than a continuation.
   - the whole function is then the prologue, the port arithmetic, the base
     load, the ISR acknowledge, the LSR read and its branch.

   ONE PROOF, PARAMETRIC IN THE PORT (XV6_REV 163d39b).  Everything the
   handler reaches it reaches through `&uarts[uid]`: the MMIO window is the
   LOADED word `uarts[uid].base` ([SpecUartPutc.uart_base_word i]), the sleep
   channel is the ELEMENT, and the receive hook is the LOADED word
   `uarts[uid].rx` ([UartTxInv.uart_rx_word i]).  The proof splits on the port
   at exactly one instruction, the `c.beqz a5` at +0x58 that tests the hook:
   at [Uart0] the snapshot says the word is [KernelSyms.consoleintr], so the
   branch falls through and the `c.jalr a5` at +0x5a is an ordinary call; at
   [Uart1] the snapshot says 0, the branch is provably TAKEN, and +0x5a is
   unreachable -- the call is REFUTED, not proved.

   THE INDIRECT CALL.  [WpSconfCtl.wp_cjalr_s_sconf]'s target is
   [ret_pc (rget m rs1)] -- a VALUE, not a symbol.  Rewriting a5 by the
   persistent snapshot turns it into [ret_pc (mword_of_int
   KernelSyms.consoleintr)], and [consoleintr] is even, so [ret_pc] is the
   identity there ([uix_ret_consoleintr]) and the goal is literally the one a
   `jal consoleintr` produces.  [Consoleintr.wp_consoleintr_sconf] then applies
   unchanged.  Same idiom as [ProofFileread]'s `devsw[major].read` and
   [ProofSyscall]'s `syscalls[num]`.

   THE TWO BACK EDGES, AND WHY THE LOOP HEAD IS +0x46.  gcc emits the drain
   with the base reload INSIDE the loop, and the two exits from the hook test
   rejoin at different places: the null-hook arm branches straight back to
   +0x46 and the call arm falls to a `c.j` back to +0x40, which recomputes a4
   and a3 from s1 before reaching +0x46 again.  Per port only ONE of them is
   live, so a single Loeb at +0x46 -- with a4 and a3 pinned in the invariant --
   serves both, and the two instructions at +0x40/+0x42 appear once at the
   loop's entry and once on the call arm.  That is also why the uartgetc block
   is stated from +0x46 over the two POINTER registers rather than from +0x40
   over the element: a block starting at +0x40 could not serve the port-1 back
   edge, which lands in its middle.

   THERE IS NO LOCK.  uartintr READS ISR, READS LSR, and -- if THRE is set --
   calls [wakeup(&uarts[uid])].  Those reads are ghost-free
   ([DevModel.uart_read_stable]: no UART read moves [uart_acc], [u_out] or
   DLAB), so the handler needs neither the transmitter token nor [is_txlock].
   The RECEIVE side is not free: the RHR read POPS, which is what
   [uart_rx_writer] pays for, AT BOTH PORTS.

   THE SIE INDEX.  uartintr's contract is [b]-GENERIC, and with no lock there
   is no unbalanced stretch: the WHOLE function runs at [b], every leaf hands
   back a FRESH hart ([wp_next]), and both [cpu_own] and the caller's
   obligation are re-anchored with [cpu_own_transport] / [ui_ret_cont_shift]
   at each crossing.

   A functor over WAKEUP / CONSOLEINTR / UART. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpLock ProcGeom CpuOwn.
Require Import IntrDefs HartTp WpNext.
Require Import DevModel DiskPtsto WpUart.
Require Import SpecUart WpSconfUartAccess WpUartgetc.
Require Import PowerBoot.      (* [pa_of_z] *)
Require Import UartsFields.
Require Import UartTxInv.
Require Import SpecUartPutc.   (* [uart_base_word]: the .data word the MMIO
                                  address is LOADED from *)
Require Import SchedCtx.
Require Import FdSlots.
Require Import SpecWakeup SpecConsoleintr.
Require Import CodeUartintr.
Require Import SpecUartintr.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Local Open Scope Z_scope.

Local Notation Rra  := (mword_of_int 1 : mword 5).
Local Notation Rs0  := (mword_of_int 8 : mword 5).
Local Notation Rs1  := (mword_of_int 9 : mword 5).
Local Notation Ra0  := (mword_of_int 10 : mword 5).
Local Notation Ra3  := (mword_of_int 13 : mword 5).
Local Notation Ra4  := (mword_of_int 14 : mword 5).
Local Notation Ra5  := (mword_of_int 15 : mword 5).
Local Notation Rs2  := (mword_of_int 18 : mword 5).
Local Notation Rs3  := (mword_of_int 19 : mword 5).
Local Notation Rs4  := (mword_of_int 20 : mword 5).
Local Notation Rs5  := (mword_of_int 21 : mword 5).
Local Notation Rs6  := (mword_of_int 22 : mword 5).
Local Notation Rs7  := (mword_of_int 23 : mword 5).
Local Notation Rs8  := (mword_of_int 24 : mword 5).
Local Notation Rs9  := (mword_of_int 25 : mword 5).
Local Notation Rs10 := (mword_of_int 26 : mword 5).
Local Notation Rs11 := (mword_of_int 27 : mword 5).

(* ===================================================================== *)
(*  THE INDEX ARITHMETIC.  Everything the prologue and the join compute    *)
(*  out of the port index is a closed function of the port, so each step   *)
(*  is one [destruct i] and a [vm_compute].  Proved here, outside the WP   *)
(*  scripts, so no script ever splits on [i] for arithmetic -- the ONE     *)
(*  split that remains is the hook test at +0x58.                         *)
(* ===================================================================== *)
Section UartintrIdx.
Local Open Scope Z_scope.

(* +0x0c / +0x2e / +0x5e   slli a5,<idx>,2 *)
Lemma uix_slli2 (i : uart_id) :
  shift_bits_left (mword_of_int (uart_index i) : mword 64)
    (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (4 * uart_index i).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x10 / +0x32 / +0x62   c.add a5,<idx> *)
Lemma uix_add5 (i : uart_id) :
  add_vec (mword_of_int (4 * uart_index i) : mword 64)
          (mword_of_int (uart_index i) : mword 64)
  = mword_of_int (5 * uart_index i).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x12 / +0x34 / +0x64   c.slli a5,3 *)
Lemma uix_slli3 (i : uart_id) :
  shift_bits_left (mword_of_int (5 * uart_index i) : mword 64)
    (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (uart_stride * uart_index i).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x1c   c.add a5,a4 -- the ELEMENT, with the array base on the RIGHT *)
Lemma uix_elt_l (i : uart_id) :
  add_vec (mword_of_int (uart_stride * uart_index i) : mword 64)
          (mword_of_int KernelSyms.uarts : mword 64)
  = mword_of_int (uart_f_base i).
Proof.
  unfold uart_f_base, uart_elt.
  destruct i; apply bv_eq; vm_compute; reflexivity.
Qed.

(* +0x3e / +0x6e   c.add s1,a5 / c.add a0,a5 -- base on the LEFT *)
Lemma uix_elt_r (i : uart_id) :
  add_vec (mword_of_int KernelSyms.uarts : mword 64)
          (mword_of_int (uart_stride * uart_index i) : mword 64)
  = mword_of_int (uart_f_base i).
Proof.
  unfold uart_f_base, uart_elt.
  destruct i; apply bv_eq; vm_compute; reflexivity.
Qed.

(* +0x0a   c.mv s1,a0 writes [add_vec zero_reg x] *)
Lemma uix_zadd_idx (i : uart_id) :
  add_vec zero_reg (mword_of_int (uart_index i) : mword 64)
  = (mword_of_int (uart_index i) : mword 64).
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* an [imm = 0] displacement is the identity at an address the proof cannot
   compute (the port is abstract) *)
Lemma uix_imm0 (x : mword 64) :
  add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
Proof.
  replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
    with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  apply kv_addv_zero.
Qed.

(* the loaded [base] word IS the port's MMIO window *)
Lemma uix_pa0 (i : uart_id) : (Z_to_bv 64 (uart_base i) : mword 64) = uart_pa i 0.
Proof. destruct i; reflexivity. Qed.

Lemma uix_pa2 (i : uart_id) :
  add_vec (uart_pa i 0) (sign_extend' 64 (mword_of_int 2 : mword 12)) = uart_pa i 2.
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma uix_pa5 (i : uart_id) :
  add_vec (uart_pa i 0) (sign_extend' 64 (mword_of_int 5 : mword 12)) = uart_pa i 5.
Proof. destruct i; apply bv_eq; vm_compute; reflexivity. Qed.

(* the element's two immutable fields, as the two [ld] displacements name
   them: [base] at +0 and [rx] at +8 *)
Lemma uix_fbase (i : uart_id) :
  add_vec (mword_of_int (uart_f_base i) : mword 64)
          (sign_extend' 64 (mword_of_int 0 : mword 12))
  = pa_of_z (uart_f_base i).
Proof. apply uix_imm0. Qed.

Lemma uix_frx (i : uart_id) :
  add_vec (mword_of_int (uart_f_base i) : mword 64)
          (sign_extend' 64 (mword_of_int 8 : mword 12))
  = pa_of_z (uart_f_rx i).
Proof.
  unfold pa_of_z, uart_f_rx, uart_f_base, uart_elt.
  destruct i; apply bv_eq; vm_compute; reflexivity.
Qed.

(* THE HOOK TEST AT +0x58, decided by the snapshot and by nothing else. *)
Lemma uix_hook_nz :
  eq_vec (Z_to_bv 64 (uart_rx_hook Uart0) : mword 64) (zero_reg : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma uix_hook_z :
  eq_vec (Z_to_bv 64 (uart_rx_hook Uart1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

(* ...and the call it licenses: [consoleintr] is even, so [ret_pc] -- the
   [c.jalr]'s own bit-0 clear -- is the identity on it and the goal is
   character-for-character what a `jal consoleintr` produces. *)
Lemma uix_ret_hook0 :
  ret_pc (Z_to_bv 64 (uart_rx_hook Uart0) : mword 64)
  = (mword_of_int KernelSyms.consoleintr : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

End UartintrIdx.

(* the 4-slot frame geometry *)
Lemma ui_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 4%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 4%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_assoc H. reflexivity.
Qed.

(* ===================================================================== *)
(* [ui_regs] / [ui_ret_cont] live ABOVE the section on purpose: a constant
   defined INSIDE a section carrying [Context `{GEN : GenId} `{CID : CpuId}] is applied at
   that section variable at every use, and would then BEAT the [fun CID =>]
   binder of the [wp_next] it contains (porting guide, "a section-defined
   constant silently beats the wp_next lambda").  [CID0] is the anchor the
   obligation is stated at, and [ui_ret_cont_shift] moves it.               *)
(* ===================================================================== *)

(* every callee-saved register uartintr never touches.  s2 IS one of them
   now: 163d39b's handler keeps the element pointer in s1 and needs no third
   callee-saved register, so the spill slot at +0 is dead and s2 rides
   through untouched.  NO tp conjunct: [HartTp.tp_pin] makes the slot
   unobservable, so a statement about it is vacuous. *)
Definition ui_regs (m0 M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs2 = m0 !!! Regidx Rs2 /\
  M !!! Regidx Rs3 = m0 !!! Regidx Rs3 /\
  M !!! Regidx Rs4 = m0 !!! Regidx Rs4 /\
  M !!! Regidx Rs5 = m0 !!! Regidx Rs5 /\
  M !!! Regidx Rs6 = m0 !!! Regidx Rs6 /\
  M !!! Regidx Rs7 = m0 !!! Regidx Rs7 /\
  M !!! Regidx Rs8 = m0 !!! Regidx Rs8 /\
  M !!! Regidx Rs9 = m0 !!! Regidx Rs9 /\
  M !!! Regidx Rs10 = m0 !!! Regidx Rs10 /\
  M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

Lemma ui_regs_cs (m0 M M' : regfile) (spd : mword 64) :
  callee_saved M M' -> ui_regs m0 M spd -> ui_regs m0 M' spd.
Proof.
  intros Hcs (H2 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  unfold ui_regs.
  repeat first
    [ split
    | rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 18) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 19) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 20) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 21) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity))
    | rewrite (callee_saved_lookup Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity))
    | assumption ].
Qed.

Section UiCont.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.

  (* the frame the prologue spilled.  THREE saves over a FOUR-slot frame:
     163d39b's uartintr pushes 32 bytes and writes only ra/s0/s1, so the
     lowest slot is never touched and rides through EXISTENTIALLY -- which
     is exactly what the frame pop needs to hand [stack_own] back. *)
  Definition ui_frame `{XI : CurCtx} (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈[KT1] (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈[KT1] (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈[KT1] (m0 !!! Regidx Rs1) ∗
     (∃ w : mword 64, pa_stk sp0 4 ↦₈[KT1] w))%I.

  (* the caller's continuation, named once *)
  Definition ui_ret_cont `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (γu : uart_names) (m0 : regfile)
      (av lvl : nat) (eb : bool) (pme : mword 64) (b : bool) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
       ∀ mf : regfile,
         ⌜ callee_saved m0 mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap mf)) ⌝ -∗
         sie_cap_gpr KT1 mf av b pme -∗
         cpu_own lvl eb pme b lks -∗
         pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         (∃ (k' : nat) (hl' : option (list mobs)),
            uart_rx_writer γu k' hl') -∗
         WP (Loop : expr riscv_lang)))%I.

  (* re-anchor it at a hart reached mid-block.  Through the named definition
     [wp_next_shift]'s direct idiom cannot infer [K], so unfold first. *)
  Lemma ui_ret_cont_shift `{GEN : GenId} `{XI : CurCtx} (CIDa CIDb : CpuId)
      (γu : uart_names) (m0 : regfile)
      (av lvl : nat) (eb : bool) (pme : mword 64) (b : bool) (lks : gset string) :
    (b = false \/ pme = zero_reg -> (CIDb : CPU) = (CIDa : CPU)) ->
    ui_ret_cont (CID0 := CIDa) γu m0 av lvl eb pme b lks -∗
    ui_ret_cont (CID0 := CIDb) γu m0 av lvl eb pme b lks.
  Proof. intros Hs. rewrite /ui_ret_cont. exact (wp_next_shift Hs). Qed.

End UiCont.

Module UartintrProof (Wakeup : WAKEUP) (Consoleintr : CONSOLEINTR) (Uart : UART) : UARTINTR.

Module UAcc := UartAccessProof Uart.
Module UG := UartgetcProof Uart.

Section ProofUartintr.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.


  (* ------------------------------------------------------------------ *)
  (*  THE EPILOGUE: +0x76 -> return.                                      *)
  (* ------------------------------------------------------------------ *)
  Lemma ui_tail `{CID0 : CpuId} (γu : uart_names)
      (m0 M : regfile) (av lvl : nat) (eb : bool) (pme : mword 64)
      (sp0 : mword 64) (b : bool) (lks : gset string) :
    ui_regs m0 M (pa_stk sp0 4) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    (uartintr_stack <= av)%nat ->
    kernel_text -∗
    sie_cap_gpr KT1 M (av - 4) b pme -∗
    cpu_own lvl eb pme b lks -∗
    pc_is (mword_of_int (KernelSyms.uartintr + 0x76)) -∗
    ui_frame sp0 m0 -∗
    (∃ (k' : nat) (hl' : option (list mobs)), uart_rx_writer γu k' hl') -∗
    ui_ret_cont γu m0 av lvl eb pme b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hregs Hsp0 Hav.
    destruct Hregs as (Hsp & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Ht Hcg Hcnt Hpc Hfr Htok Hcont".
    rewrite /ui_frame. iDestruct "Hfr" as "(H1 & H2 & H3 & H4)".
    set (spd := pa_stk sp0 4).
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (apply ui_slot_bridge; pcw).
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (apply ui_slot_bridge; pcw).
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (apply ui_slot_bridge; pcw).
    assert (P78 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x76) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x78)) by pcw.
    assert (P7a : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x7a)) by pcw.
    assert (P7c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x7c)) by pcw.
    assert (P7e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x7e)) by pcw.
    (* +0x76 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartintr + 0x76)) (mword_of_int 3 : mword 6) Rra
              M (av - 4)%nat (m0 !!! Regidx Rra) b (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [H1]").
    { iApply (uii2_76 with "Ht"). }
    { iEval (rewrite Hsp Hb1). iExact "H1". }
    iIntros (CID1 Hs1) "Hcg Hpc H1". iEval (rewrite Hsp Hb1) in "H1".
    set (E1 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M) with E1.
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact Hsp | reg_neq]).
    iEval (rewrite P78) in "Hpc".
    (* +0x78 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartintr + 0x78)) (mword_of_int 2 : mword 6) Rs0
              E1 (av - 4)%nat (m0 !!! Regidx Rs0) b (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [H2]").
    { iApply (uii2_78 with "Ht"). }
    { iEval (rewrite HE1sp Hb2). iExact "H2". }
    iIntros (CID2 Hs2) "Hcg Hpc H2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    iEval (rewrite P7a) in "Hpc".
    (* +0x7a c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uartintr + 0x7a)) (mword_of_int 1 : mword 6) Rs1
              E2 (av - 4)%nat (m0 !!! Regidx Rs1) b (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [H3]").
    { iApply (uii2_7a with "Ht"). }
    { iEval (rewrite HE2sp Hb3). iExact "H3". }
    iIntros (CID3 Hs3) "Hcg Hpc H3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    iEval (rewrite P7c) in "Hpc".
    (* +0x7c c.addi16sp sp,32 -- the frame pop.  The lowest slot was never
       written; it goes back existentially, exactly as it arrived. *)
    iAssert (stack_own (KTR := KT1) sp0 4) with "[H1 H2 H3 H4]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "H1"; [by iExists _|].
      iSplitL "H2"; [iExists _; iEval (rewrite -Hb2 -HE1sp); iExact "H2"|].
      iSplitL "H3"; [iExists _; iEval (rewrite -Hb3 -HE2sp); iExact "H3"|].
      iSplitL "H4"; [iExact "H4"|]. done. }
    assert (Hpopv : add_vec (E3 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE3sp /spd. unfold pa_stk, add_vec_int. rewrite add_vec_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 4%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4%nat)
      by (rewrite Hpopv HE3sp; reflexivity).
    iEval (rewrite -Hpopv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uartintr + 0x7c)) (mword_of_int 2 : mword 6)
              E3 (av - 4)%nat 4%nat b Hpop with "Hcg Hpc [] Hframe").
    { iApply (uii2_7c with "Ht"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hav4 : ((av - 4) + 4)%nat = av) by (lia).
    iEval (rewrite Hav4) in "Hcg".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    iEval (rewrite P7e) in "Hpc".
    (* +0x7e c.ret *)
    assert (HE4ra : E4 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    assert (HE4rg : forall (CID' : CpuId), rget (CID := CID') E4 Rra = m0 !!! Regidx Rra).
    { intros CID'; rgne. exact HE4ra. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uartintr + 0x7e)) Rra E4 av b ltac:(nz)
              with "Hcg Hpc []").
    { iApply (uii2_7e with "Ht"). }
    iIntros (CID5 Hs5) "Hcg Hpc". iEval (rewrite HE4rg) in "Hpc".
    (* ---- callee_saved m0 E4 ---- *)
    assert (Hpeel : forall r : mword 5,
              r <> csp_rs1 -> r <> Rra -> r <> Rs0 -> r <> Rs1 ->
              E4 !!! Regidx r = M !!! Regidx r).
    { intros r N2 N1 N8 N9.
      rewrite /E4 upd_ne; [| congruence]. rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence]. rewrite /E1 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CID0 CID5 lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /ui_ret_cont.
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "[%] Hcg Hcnt Hpc Htok").
    split; [| intro r; apply rf_to_gmap_dom].
    unfold callee_saved.
    split; [rewrite /E4 upd_eq Hpopv; symmetry; exact Hsp0|].
    split; [rewrite /E4 upd_ne; [| reg_neq]; rewrite /E3 upd_ne; [| reg_neq];
            rewrite /E2 upd_eq; reflexivity|].
    split; [rewrite /E4 upd_ne; [| reg_neq]; rewrite /E3 upd_eq; reflexivity|].
    split; [rewrite (Hpeel (mword_of_int 18) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H18|].
    split; [rewrite (Hpeel (mword_of_int 19) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H19|].
    split; [rewrite (Hpeel (mword_of_int 20) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H20|].
    split; [rewrite (Hpeel (mword_of_int 21) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H21|].
    split; [rewrite (Hpeel (mword_of_int 22) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H22|].
    split; [rewrite (Hpeel (mword_of_int 23) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H23|].
    split; [rewrite (Hpeel (mword_of_int 24) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H24|].
    split; [rewrite (Hpeel (mword_of_int 25) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H25|].
    split; [rewrite (Hpeel (mword_of_int 26) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H26|].
    rewrite (Hpeel (mword_of_int 27) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact H27.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE RECEIVE DRAIN: +0x46 -> +0x76  (iLoeb).                         *)
  (* ------------------------------------------------------------------ *)
  (* [while(1){ c = uartgetc(u); if (c == -1) break; if (u->rx) u->rx(c); }].
     Unbounded: nothing stops the device from supplying another byte, so this
     is a Loeb loop and not an induction.  Its body is uartgetc (inlined --
     WpUartgetc.v) and the hook dispatch.

     THE HART IS PART OF THE LOOP STATE: the loop runs at [b], so every
     iteration ends on a fresh hart, and both [sie_cap_gpr] / [cpu_own] and
     the caller's obligation have to be re-anchored there before the back
     edge.  Hence the leading [∀ CIDk : CpuId] in the invariant.

     a4 AND a3 ARE PART OF IT TOO.  gcc reloads `u->base` and recomputes
     `u->base + 5` after every hook call, so the loop's entry state pins both
     -- and the arm that skipped the call re-enters with them unchanged.  *)
  Lemma ui_rx (i : uart_id) (γu : uart_names) (γv : disk_names)
      (γs : list gname) (m0 : regfile) (av lvl : nat) (eb : bool)
      (pme : mword 64) (sp0 : mword 64) (b : bool) (lks : gset string) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    length γs = NPROC ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (uartintr_stack <= av)%nat ->
    locks_below lks "cons" ->
    ⊢ ∀ (CIDe : CpuId) (M : regfile),
      ⌜ ui_regs m0 M (pa_stk sp0 4) ⌝ -∗
      ⌜ M !!! Regidx Rs1 = (mword_of_int (uart_f_base i) : mword 64) ⌝ -∗
      ⌜ M !!! Regidx Ra4 = uart_pa i 0 ⌝ -∗
      ⌜ M !!! Regidx Ra3 = uart_pa i 5 ⌝ -∗
      kernel_text -∗ uart_inv i γu -∗ procs_inv γs -∗
      uart_dlab_off γu -∗ uart_base_word i -∗ uart_rx_word i -∗
      ui_rx_caps i γu γv -∗
      sie_cap_gpr KT1 (CID := CIDe) M (av - 4) b pme -∗
      cpu_own (CID := CIDe) lvl eb pme b lks -∗
      pc_is (mword_of_int (KernelSyms.uartintr + 0x46)) -∗
      ui_frame sp0 m0 -∗
      (∃ (k : nat) (hl : option (list mobs)), uart_rx_writer γu k hl) -∗
      ui_ret_cont (CID0 := CIDe) γu m0 av lvl eb pme b lks -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp0 Hlen Hlvl Hav Hbelow.
    iIntros (CIDe M) "%Hregs %Hs1 %Ha4 %Ha3 #Ht #Huinv #Hpinv #Hdlab #Hbw #Hrw #Hcaps".
    iIntros "Hcg Hcnt Hpc Hfr Htok Hcont".
    (* the two back edges: the null-hook arm's, and the call arm's *)
    assert (Jb46 : add_vec (mword_of_int (KernelSyms.uartintr + 0x58) : mword 64)
                     (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 247 : mword 8) ('b"0"))))
                   = mword_of_int (KernelSyms.uartintr + 0x46)) by pcw.
    assert (Jb40 : add_vec (mword_of_int (KernelSyms.uartintr + 0x5c) : mword 64)
                     (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                   = mword_of_int (KernelSyms.uartintr + 0x40)) by pcw.
    assert (P42 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x42)) by pcw.
    assert (P46 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x46)) by pcw.
    assert (P58 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x58)) by pcw.
    assert (P5a : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x5a)) by pcw.
    assert (P5c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x5c)) by pcw.
    iAssert (∀ (CIDk : CpuId) (M1 : regfile),
      ⌜ ui_regs m0 M1 (pa_stk sp0 4) ⌝ -∗
      ⌜ M1 !!! Regidx Rs1 = (mword_of_int (uart_f_base i) : mword 64) ⌝ -∗
      ⌜ M1 !!! Regidx Ra4 = uart_pa i 0 ⌝ -∗
      ⌜ M1 !!! Regidx Ra3 = uart_pa i 5 ⌝ -∗
      sie_cap_gpr KT1 (CID := CIDk) M1 (av - 4) b pme -∗
      cpu_own (CID := CIDk) lvl eb pme b lks -∗
      pc_is (mword_of_int (KernelSyms.uartintr + 0x46)) -∗
      ui_frame sp0 m0 -∗
      (∃ (k : nat) (hl : option (list mobs)), uart_rx_writer γu k hl) -∗
      ui_ret_cont (CID0 := CIDk) γu m0 av lvl eb pme b lks -∗
      WP (Loop : expr riscv_lang))%I with "[]" as "Loop".
    { iLöb as "IH".
      iIntros (CIDk M1) "%Hregs1 %Hls1 %Hla4 %Hla3 Hcg Hcnt Hpc Hfr Htok Hcont".
      iDestruct "Htok" as (k hl) "[Htok Hhi]".
      iDestruct "Hhi" as (hh) "[Hhi %Hhle]".
      assert (Hlsr : forall (CID' : CpuId), rget (CID := CID') M1 Ra3 = uart_pa i 5)
        by (intros CID'; rgne; exact Hla3).
      assert (Hrhr : forall (CID' : CpuId), rget (CID := CID') M1 Ra4 = uart_pa i 0)
        by (intros CID'; rgne; exact Hla4).
      (* +0x46 .. +0x52 : uartgetc, inlined, with the zext.b absorbed *)
      iApply (UG.wp_uartgetc_inline i γu M1 (av - 4)%nat Ra3 Ra4
                (mword_of_int 21 : mword 8) k hl
                (mword_of_int (KernelSyms.uartintr + 0x46)) (mword_of_int (KernelSyms.uartintr + 0x4a))
                (mword_of_int (KernelSyms.uartintr + 0x4c)) (mword_of_int (KernelSyms.uartintr + 0x4e))
                (mword_of_int (KernelSyms.uartintr + 0x52)) (mword_of_int (KernelSyms.uartintr + 0x56))
                (mword_of_int (KernelSyms.uartintr + 0x76)) b
                (Hlsr _) (Hrhr _) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc [] [] [] [] [] Huinv Hdlab Htok [Hcnt Hfr Hcont Hhi]").
      { iApply (uii2_46 with "Ht"). }
      { iEval (rewrite -UG.ug_cr7). iApply (uii2_4a with "Ht"). }
      { iApply (uii2_4c with "Ht"). }
      { iApply (uii2_4e with "Ht"). }
      { iApply (uii2_52 with "Ht"). }
      iIntros (CIDg Hsg).
      iSplit.
      - (* the FIFO was empty: leave the loop, with the token *)
        iIntros (bt) "_ Hcg Hpc Htok".
        assert (Hrx : ui_regs m0 (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> M1)
                        (pa_stk sp0 4)).
        { destruct Hregs1 as (A2 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
          unfold ui_regs. split_and!; (rewrite upd_ne; [| reg_neq]); assumption. }
        iDestruct (cpu_own_transport CIDk CIDg lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (ui_ret_cont_shift CIDk CIDg γu m0 av lvl eb pme b lks
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply (ui_tail γu m0 (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> M1)
                  av lvl eb pme sp0 b lks Hrx Hsp0 Hav
                  with "Ht Hcg Hcnt Hpc Hfr [Htok Hhi] Hcont").
        iExists k, hl. rewrite /uart_rx_writer. iFrame "Htok".
        iExists hh. iFrame "Hhi". by iPureIntro.
      - (* a byte came out.  What happens to it is decided by the PORT, and
           by nothing at run time: [uart_rx_word] says what `u->rx` holds. *)
        iIntros (bt c) "_ Hcg Hpc Hh".
        iDestruct "Hh" as (h) "(%Hlast & %Hanch & #Htg & #Hlbh & Htok)".
        (* THE ORDER THE STORE NEEDS: the ring's mark is at or before the
           popper's anchor, and the byte just popped is strictly after that
           anchor, so the mark is strictly before the byte. *)
        assert (Hhext : ObsTrace.ohist_ext hh h)
          by exact (ObsTrace.ohist_ext_le_ext hh hl h Hhle Hanch).
        destruct i.
        + (* ---------------- Uart0: the hook is [consoleintr] ------------ *)
          iAssert (dev_inv γu γv ∗ console_caps γu)%I as "[#Hdinv #Hccaps]";
            [iExact "Hcaps"|].
          set (H0 := <[Regidx Ra0 := regval_into_reg (lsr_ldval_of c)]>
                     (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> M1)).
          change (<[Regidx Ra0 := regval_into_reg (lsr_ldval_of c)]>
                  (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> M1)) with H0.
          assert (HH0s1 : H0 !!! Regidx Rs1 = (mword_of_int (uart_f_base Uart0) : mword 64)).
          { rewrite /H0 upd_ne; [| reg_neq]. rewrite upd_ne; [exact Hls1 | reg_neq]. }
          assert (HH0regs : ui_regs m0 H0 (pa_stk sp0 4)).
          { destruct Hregs1 as (A2 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
            unfold ui_regs. split_and!;
              (rewrite /H0 upd_ne; [| reg_neq]); (rewrite upd_ne; [| reg_neq]); assumption. }
          (* --- +0x56  c.ld a5,8(s1) : the receive hook, out of `.data` --- *)
          assert (Hldrx : forall (CID' : CpuId),
                    add_vec (rget (CID := CID') H0 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = pa_of_z (uart_f_rx Uart0)).
          { intros CID'; rgne. rewrite HH0s1. apply uix_frx. }
          iEval (rewrite /uart_rx_word -(Hldrx CIDg)) in "Hrw".
          iApply (wp_cld_s_sconf (CID := CIDg) (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uartintr + 0x56))
                    Ra5 Rs1 (mword_of_int 8 : mword 12)
                    H0 (av - 4)%nat (Z_to_bv 64 (uart_rx_hook Uart0)) b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hrw]").
          { iApply (uii2_56 with "Ht"). }
          { iExact "Hrw". }
          iIntros (CIDh Hsh) "Hcg Hpc _". iEval (rewrite P58) in "Hpc".
          set (H1 := <[Regidx Ra5 := regval_into_reg (Z_to_bv 64 (uart_rx_hook Uart0) : mword 64)]> H0).
          change (<[Regidx Ra5 := regval_into_reg (Z_to_bv 64 (uart_rx_hook Uart0) : mword 64)]> H0) with H1.
          assert (HH1a5 : rget (CID := CIDh) H1 Ra5 = (Z_to_bv 64 (uart_rx_hook Uart0) : mword 64)).
          { rgne. rewrite /H1 upd_eq. reflexivity. }
          (* --- +0x58  c.beqz a5 : the hook is NOT null here --- *)
          iApply (wp_cbeqz_fall_s_sconf (CID := CIDh) (mword_of_int (KernelSyms.uartintr + 0x58))
                    (mword_of_int 247 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    H1 (av - 4)%nat b UG.ug_cr7 ltac:(nz)
                    ltac:(rewrite HH1a5; exact uix_hook_nz)
                    with "Hcg Hpc []").
          { iApply (uii2_58 with "Ht"). }
          iIntros (CIDi Hsi) "Hcg Hpc". iEval (rewrite P5a) in "Hpc".
          (* --- +0x5a  c.jalr a5 : the INDIRECT call.  The leaf's target is a
                 VALUE; the snapshot turns it into [consoleintr]'s address, and
                 [ret_pc] is the identity there because that address is even. *)
          iApply (wp_cjalr_s_sconf (CID := CIDi) (mword_of_int (KernelSyms.uartintr + 0x5a))
                    Ra5 Rra H1 (av - 4)%nat b ltac:(nz) ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (uii2_5a with "Ht"). }
          iIntros (CIDj Hsj) "Hcg Hpc".
          iEval (rewrite (_ : rget (CID := CIDi) H1 Ra5 = (Z_to_bv 64 (uart_rx_hook Uart0) : mword 64));
                 [| exact HH1a5]) in "Hpc".
          iEval (rewrite uix_ret_hook0) in "Hpc".
          set (H2 := <[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5a) : mword 64) 2)]> H1).
          change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5a) : mword 64) 2)]> H1) with H2.
          assert (HH2ra : H2 !!! Regidx Rra
                          = add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5a) : mword 64) 2)
            by (rewrite /H2 upd_eq; reflexivity).
          (* a0 holds the byte, zero-extended by the [lbu] that popped it *)
          assert (HH2a0 : H2 !!! Regidx Ra0
                          = (extend_value (n := 8) true (c : mword 8) : mword 64)).
          { rewrite /H2 upd_ne; [| reg_neq]. rewrite /H1 upd_ne; [| reg_neq].
            rewrite /H0 upd_eq. reflexivity. }
          assert (HcsH2 : callee_saved M1 H2).
          { rewrite /H2 /H1 /H0.
            apply callee_saved_insert_r; [vm_compute; reflexivity|].
            apply callee_saved_insert_r; [vm_compute; reflexivity|].
            apply callee_saved_insert_r; [vm_compute; reflexivity|].
            apply callee_saved_insert_r; [vm_compute; reflexivity|].
            apply callee_saved_refl. }
          assert (HH2regs : ui_regs m0 H2 (pa_stk sp0 4))
            by exact (ui_regs_cs m0 M1 H2 (pa_stk sp0 4) HcsH2 Hregs1).
          iDestruct (cpu_own_transport CIDk CIDj lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (Consoleintr.wp_consoleintr_sconf γu γv H2 γs pme lvl (av - 4)%nat eb b lks
                    h c hh
                    ltac:(lia) HH2a0 Hlast Hhext
                    Hlen ltac:(lia) Hbelow
                    with "Hcg Hcnt Ht Hpc Hpinv Hdinv Hccaps Htg Hlbh Hhi").
          all: try lkbelow.
          iIntros (CIDc Hsc Mf) "[%Hcsf %Hdomf] Hcg Hcnt Ht2 Hpc Hhi".
          iEval (rewrite HH2ra) in "Hpc".
          assert (P5cr : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5a) : mword 64) 2)
                         = mword_of_int (KernelSyms.uartintr + 0x5c)) by pcw.
          iEval (rewrite P5cr) in "Hpc".
          assert (HcsMf : callee_saved M1 Mf) by (apply (callee_saved_trans M1 H2 Mf HcsH2 Hcsf)).
          assert (HMfs1 : Mf !!! Regidx Rs1 = (mword_of_int (uart_f_base Uart0) : mword 64)).
          { rewrite (callee_saved_lookup Hcsf (mword_of_int 9) ltac:(vm_compute; reflexivity)).
            exact HH0s1. }
          assert (HMfregs : ui_regs m0 Mf (pa_stk sp0 4))
            by exact (ui_regs_cs m0 M1 Mf (pa_stk sp0 4) HcsMf Hregs1).
          (* --- +0x5c  c.j -> +0x40 : the base and the LSR pointer are
                 caller-saved, so gcc rebuilds them from s1 --- *)
          iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uartintr + 0x5c))
                    (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                    Mf (av - 4)%nat b ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
          { iApply (uii2_5c with "Ht"). }
          iIntros (CIDz Hsz). iNext. iIntros "Hcg Hpc". iEval (rewrite Jb40) in "Hpc".
          (* --- +0x40  c.ld a4,0(s1) --- *)
          assert (Hldb : forall (CID' : CpuId),
                    add_vec (rget (CID := CID') Mf Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = pa_of_z (uart_f_base Uart0)).
          { intros CID'; rgne. rewrite HMfs1. apply uix_fbase. }
          iEval (rewrite /uart_base_word (uix_pa0 Uart0) -(Hldb CIDz)) in "Hbw".
          iApply (wp_cld_s_sconf (CID := CIDz) (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uartintr + 0x40))
                    Ra4 Rs1 (mword_of_int 0 : mword 12) Mf (av - 4)%nat (uart_pa Uart0 0) b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hbw]").
          { iApply (uii2_40 with "Ht"). }
          { iExact "Hbw". }
          iIntros (CIDy Hsy) "Hcg Hpc _". iEval (rewrite P42) in "Hpc".
          set (N0 := <[Regidx Ra4 := regval_into_reg (uart_pa Uart0 0)]> Mf).
          change (<[Regidx Ra4 := regval_into_reg (uart_pa Uart0 0)]> Mf) with N0.
          assert (HN0a4 : N0 !!! Regidx Ra4 = uart_pa Uart0 0)
            by (rewrite /N0 upd_eq; reflexivity).
          (* --- +0x42  addi a3,a4,5 --- *)
          iApply (wp_addi4_s_sconf (CID := CIDy) (mword_of_int (KernelSyms.uartintr + 0x42))
                    Ra3 Ra4 (mword_of_int 5 : mword 12) N0 (av - 4)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (uii2_42 with "Ht"). }
          iIntros (CIDw Hsw) "Hcg Hpc". iEval (rewrite P46) in "Hpc".
          iEval (rgne) in "Hcg".
          iEval (rewrite HN0a4 (uix_pa5 Uart0)) in "Hcg".
          set (N1 := <[Regidx Ra3 := regval_into_reg (uart_pa Uart0 5)]> N0).
          change (<[Regidx Ra3 := regval_into_reg (uart_pa Uart0 5)]> N0) with N1.
          (* --- back to the loop head --- *)
          iDestruct (cpu_own_transport CIDc CIDw lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (ui_ret_cont_shift CIDk CIDw γu m0 av lvl eb pme b lks
                       ltac:(wp_next_chain) with "Hcont") as "Hcont".
          iApply ("IH" $! CIDw N1 with "[%] [%] [%] [%] Hcg Hcnt Hpc Hfr [Htok Hhi] Hcont").
          5: { iExists (S k), (Some h). rewrite /uart_rx_writer. iFrame "Htok".
               iDestruct "Hhi" as (hh' cse) "(Hhi & %Hle' & _ & _ & _)".
               iExists hh'. iFrame "Hhi". by iPureIntro. }
          * destruct HMfregs as (A2 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
            unfold ui_regs. split_and!;
              (rewrite /N1 upd_ne; [| reg_neq]); (rewrite /N0 upd_ne; [| reg_neq]); assumption.
          * rewrite /N1 upd_ne; [| reg_neq]. rewrite /N0 upd_ne; [| reg_neq]. exact HMfs1.
          * rewrite /N1 upd_ne; [| reg_neq]. exact HN0a4.
          * rewrite /N1 upd_eq. reflexivity.
        + (* ---------------- Uart1: the hook is NULL, the call is dead ---- *)
          set (H0 := <[Regidx Ra0 := regval_into_reg (lsr_ldval_of c)]>
                     (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> M1)).
          change (<[Regidx Ra0 := regval_into_reg (lsr_ldval_of c)]>
                  (<[Regidx Ra5 := regval_into_reg (rx_masked bt)]> M1)) with H0.
          assert (HH0s1 : H0 !!! Regidx Rs1 = (mword_of_int (uart_f_base Uart1) : mword 64)).
          { rewrite /H0 upd_ne; [| reg_neq]. rewrite upd_ne; [exact Hls1 | reg_neq]. }
          assert (HH0a4 : H0 !!! Regidx Ra4 = uart_pa Uart1 0).
          { rewrite /H0 upd_ne; [| reg_neq]. rewrite upd_ne; [exact Hla4 | reg_neq]. }
          assert (HH0a3 : H0 !!! Regidx Ra3 = uart_pa Uart1 5).
          { rewrite /H0 upd_ne; [| reg_neq]. rewrite upd_ne; [exact Hla3 | reg_neq]. }
          assert (HH0regs : ui_regs m0 H0 (pa_stk sp0 4)).
          { destruct Hregs1 as (A2 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
            unfold ui_regs. split_and!;
              (rewrite /H0 upd_ne; [| reg_neq]); (rewrite upd_ne; [| reg_neq]); assumption. }
          (* --- +0x56  c.ld a5,8(s1) --- *)
          assert (Hldrx : forall (CID' : CpuId),
                    add_vec (rget (CID := CID') H0 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = pa_of_z (uart_f_rx Uart1)).
          { intros CID'; rgne. rewrite HH0s1. apply uix_frx. }
          iEval (rewrite /uart_rx_word -(Hldrx CIDg)) in "Hrw".
          iApply (wp_cld_s_sconf (CID := CIDg) (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uartintr + 0x56))
                    Ra5 Rs1 (mword_of_int 8 : mword 12)
                    H0 (av - 4)%nat (Z_to_bv 64 (uart_rx_hook Uart1)) b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hrw]").
          { iApply (uii2_56 with "Ht"). }
          { iExact "Hrw". }
          iIntros (CIDh Hsh) "Hcg Hpc _". iEval (rewrite P58) in "Hpc".
          set (H1 := <[Regidx Ra5 := regval_into_reg (Z_to_bv 64 (uart_rx_hook Uart1) : mword 64)]> H0).
          change (<[Regidx Ra5 := regval_into_reg (Z_to_bv 64 (uart_rx_hook Uart1) : mword 64)]> H0) with H1.
          assert (HH1a5 : rget (CID := CIDh) H1 Ra5 = (Z_to_bv 64 (uart_rx_hook Uart1) : mword 64)).
          { rgne. rewrite /H1 upd_eq. reflexivity. }
          assert (HH1s1 : H1 !!! Regidx Rs1 = (mword_of_int (uart_f_base Uart1) : mword 64))
            by (rewrite /H1 upd_ne; [exact HH0s1 | reg_neq]).
          assert (HH1a4 : H1 !!! Regidx Ra4 = uart_pa Uart1 0)
            by (rewrite /H1 upd_ne; [exact HH0a4 | reg_neq]).
          assert (HH1a3 : H1 !!! Regidx Ra3 = uart_pa Uart1 5)
            by (rewrite /H1 upd_ne; [exact HH0a3 | reg_neq]).
          assert (HH1regs : ui_regs m0 H1 (pa_stk sp0 4)).
          { destruct HH0regs as (A2 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
            unfold ui_regs. split_and!; (rewrite /H1 upd_ne; [| reg_neq]); assumption. }
          (* --- +0x58  c.beqz a5 : PROVABLY TAKEN.  +0x5a is unreachable at
                 this port -- the call is refuted, not proved. --- *)
          iApply (wp_cbeqz_taken_s_sconf (CID := CIDh) (mword_of_int (KernelSyms.uartintr + 0x58))
                    (mword_of_int 247 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    H1 (av - 4)%nat b UG.ug_cr7 ltac:(nz)
                    ltac:(rewrite HH1a5; exact uix_hook_z)
                    ltac:(rewrite Jb46; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (uii2_58 with "Ht"). }
          iNext. iIntros (CIDz Hsz) "Hcg Hpc". iEval (rewrite Jb46) in "Hpc".
          iDestruct (cpu_own_transport CIDk CIDz lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (ui_ret_cont_shift CIDk CIDz γu m0 av lvl eb pme b lks
                       ltac:(wp_next_chain) with "Hcont") as "Hcont".
          iApply ("IH" $! CIDz H1 with "[%] [%] [%] [%] Hcg Hcnt Hpc Hfr [Htok Hhi] Hcont").
          5: { iExists (S k), (Some h). rewrite /uart_rx_writer. iFrame "Htok".
               iExists hh. iFrame "Hhi". iPureIntro.
               exact (ObsTrace.ohist_le_of_ext hh h Hhext). }
          * exact HH1regs.
          * exact HH1s1.
          * exact HH1a4.
          * exact HH1a3. }
    iApply ("Loop" $! CIDe M with "[%] [%] [%] [%] Hcg Hcnt Hpc Hfr Htok Hcont");
      [exact Hregs | exact Hs1 | exact Ha4 | exact Ha3].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE JOIN: +0x2e (rebuild the element pointer) -> the drain.         *)
  (* ------------------------------------------------------------------ *)
  (* Both arms of the THRE test arrive here: the arm that found the
     transmitter busy falls through from +0x2c, and the arm that woke the
     writers jumps back from +0x74.  What it does is recompute
     `&uarts[uid]` -- gcc kept only the INDEX in s1 across the wakeup call --
     and materialise the two MMIO pointers the drain reads through. *)
  Lemma ui_rx_setup `{CID0 : CpuId} (i : uart_id) (γu : uart_names) (γv : disk_names)
      (γs : list gname)
      (m0 M : regfile) (av lvl : nat) (eb : bool) (pme : mword 64)
      (sp0 : mword 64) (b : bool) (lks : gset string) :
    ui_regs m0 M (pa_stk sp0 4) ->
    M !!! Regidx Rs1 = (mword_of_int (uart_index i) : mword 64) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    length γs = NPROC ->
    (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
    (uartintr_stack <= av)%nat ->
    locks_below lks "cons" ->
    kernel_text -∗ uart_inv i γu -∗ procs_inv γs -∗
    uart_dlab_off γu -∗ uart_base_word i -∗ uart_rx_word i -∗
    ui_rx_caps i γu γv -∗
    sie_cap_gpr KT1 M (av - 4)%nat b pme -∗
    cpu_own lvl eb pme b lks -∗
    pc_is (mword_of_int (KernelSyms.uartintr + 0x2e)) -∗
    ui_frame sp0 m0 -∗
    (∃ (k : nat) (hl : option (list mobs)), uart_rx_writer γu k hl) -∗
    ui_ret_cont γu m0 av lvl eb pme b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hregs Hidx Hsp0 Hlen Hlvl Hav Hbelow.
    iIntros "#Ht #Huinv #Hpinv #Hdlab #Hbw #Hrw #Hcaps Hcg Hcnt Hpc Hfr Htok Hcont".
    assert (P32 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x32)) by pcw.
    assert (P34 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x34)) by pcw.
    assert (P36 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x36)) by pcw.
    assert (P3a : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x3a)) by pcw.
    assert (P3e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x3e)) by pcw.
    assert (P40 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x40)) by pcw.
    assert (P42 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x42)) by pcw.
    assert (P46 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x46)) by pcw.
    assert (Huarts : add_vec (add_vec (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64)
                                (auipc_off (mword_of_int 10 : mword 20)))
                       (sign_extend' 64 (mword_of_int 2164 : mword 12))
                     = (mword_of_int KernelSyms.uarts : mword 64)) by pcw.
    (* +0x2e  slli a5,s1,2 *)
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.uartintr + 0x2e)) Ra5 Rs1 (mword_of_int 2 : mword 6)
              (mword_of_int (4 * uart_index i)) M (av - 4)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite Hidx; apply uix_slli2)
              with "Hcg Hpc []").
    { iApply (uii2_2e with "Ht"). }
    iIntros (CID1 Hs1) "Hcg Hpc". iEval (rewrite P32) in "Hpc".
    set (S0 := <[Regidx Ra5 := regval_into_reg (mword_of_int (4 * uart_index i) : mword 64)]> M).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (4 * uart_index i) : mword 64)]> M) with S0.
    assert (HS0a5 : S0 !!! Regidx Ra5 = (mword_of_int (4 * uart_index i) : mword 64))
      by (rewrite /S0 upd_eq; reflexivity).
    assert (HS0s1 : S0 !!! Regidx Rs1 = (mword_of_int (uart_index i) : mword 64))
      by (rewrite /S0 upd_ne; [exact Hidx | reg_neq]).
    (* +0x32  c.add a5,s1 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartintr + 0x32)) Ra5 Rs1
              S0 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_32 with "Ht"). }
    iIntros (CID2 Hs2) "Hcg Hpc". iEval (rewrite P34) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    iEval (rewrite HS0a5 HS0s1 (uix_add5 i)) in "Hcg".
    set (S1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> S0).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> S0) with S1.
    assert (HS1a5 : S1 !!! Regidx Ra5 = (mword_of_int (5 * uart_index i) : mword 64))
      by (rewrite /S1 upd_eq; reflexivity).
    (* +0x34  c.slli a5,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.uartintr + 0x34)) (Regidx Ra5) Ra5 (mword_of_int 3 : mword 6)
              S1 (av - 4)%nat b eq_refl ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_34 with "Ht"). }
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite P36) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rewrite HS1a5 (uix_slli3 i)) in "Hcg".
    set (S2 := <[Regidx Ra5 := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> S1).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> S1) with S2.
    assert (HS2a5 : S2 !!! Regidx Ra5 = (mword_of_int (uart_stride * uart_index i) : mword 64))
      by (rewrite /S2 upd_eq; reflexivity).
    (* +0x36  auipc s1,0xa  /  +0x3a  addi s1,s1,2164 : s1 := &uarts *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartintr + 0x36)) Rs1 (mword_of_int 10 : mword 20)
              S2 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_36 with "Ht"). }
    iIntros (CID4 Hs4) "Hcg Hpc". iEval (rewrite P3a) in "Hpc".
    set (S3 := <[Regidx Rs1 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> S2).
    change (<[Regidx Rs1 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x36) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> S2) with S3.
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartintr + 0x3a)) Rs1 Rs1 (mword_of_int 2164 : mword 12)
              S3 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_3a with "Ht"). }
    iIntros (CID5 Hs5) "Hcg Hpc". iEval (rewrite P3e) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rewrite /S3 upd_eq Huarts) in "Hcg".
    set (S4 := <[Regidx Rs1 := regval_into_reg (mword_of_int KernelSyms.uarts : mword 64)]> S3).
    change (<[Regidx Rs1 := regval_into_reg (mword_of_int KernelSyms.uarts : mword 64)]> S3) with S4.
    assert (HS4s1 : S4 !!! Regidx Rs1 = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /S4 upd_eq; reflexivity).
    assert (HS4a5 : S4 !!! Regidx Ra5 = (mword_of_int (uart_stride * uart_index i) : mword 64)).
    { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [exact HS2a5 | reg_neq]. }
    (* +0x3e  c.add s1,a5 : s1 := &uarts[uid] *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartintr + 0x3e)) Rs1 Ra5
              S4 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_3e with "Ht"). }
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rewrite P40) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    iEval (rewrite HS4s1 HS4a5 (uix_elt_r i)) in "Hcg".
    set (S5 := <[Regidx Rs1 := regval_into_reg (mword_of_int (uart_f_base i) : mword 64)]> S4).
    change (<[Regidx Rs1 := regval_into_reg (mword_of_int (uart_f_base i) : mword 64)]> S4) with S5.
    assert (HS5s1 : S5 !!! Regidx Rs1 = (mword_of_int (uart_f_base i) : mword 64))
      by (rewrite /S5 upd_eq; reflexivity).
    (* +0x40  c.ld a4,0(s1) : the MMIO base, out of `.data` *)
    assert (Hldb : forall (CID' : CpuId),
              add_vec (rget (CID := CID') S5 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
              = pa_of_z (uart_f_base i)).
    { intros CID'; rgne. rewrite HS5s1. apply uix_fbase. }
    (* a COPY of the persistent snapshot, respelled at the leaf's address:
       [Hbw] itself is handed on to the drain, which loads the same word
       again after every hook call. *)
    iAssert (uart_base_word i) as "#Hbw2"; [iExact "Hbw"|].
    iEval (rewrite /uart_base_word (uix_pa0 i) -(Hldb CID6)) in "Hbw2".
    iApply (wp_cld_s_sconf (CID := CID6) (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uartintr + 0x40))
              Ra4 Rs1 (mword_of_int 0 : mword 12) S5 (av - 4)%nat (uart_pa i 0) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hbw2]").
    { iApply (uii2_40 with "Ht"). }
    { iExact "Hbw2". }
    iIntros (CID7 Hs7) "Hcg Hpc _". iEval (rewrite P42) in "Hpc".
    set (S6 := <[Regidx Ra4 := regval_into_reg (uart_pa i 0)]> S5).
    change (<[Regidx Ra4 := regval_into_reg (uart_pa i 0)]> S5) with S6.
    assert (HS6a4 : S6 !!! Regidx Ra4 = uart_pa i 0) by (rewrite /S6 upd_eq; reflexivity).
    assert (HS6s1 : S6 !!! Regidx Rs1 = (mword_of_int (uart_f_base i) : mword 64))
      by (rewrite /S6 upd_ne; [exact HS5s1 | reg_neq]).
    (* +0x42  addi a3,a4,5 *)
    iApply (wp_addi4_s_sconf (CID := CID7) (mword_of_int (KernelSyms.uartintr + 0x42))
              Ra3 Ra4 (mword_of_int 5 : mword 12) S6 (av - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_42 with "Ht"). }
    iIntros (CID8 Hs8) "Hcg Hpc". iEval (rewrite P46) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rewrite HS6a4 (uix_pa5 i)) in "Hcg".
    set (S7 := <[Regidx Ra3 := regval_into_reg (uart_pa i 5)]> S6).
    change (<[Regidx Ra3 := regval_into_reg (uart_pa i 5)]> S6) with S7.
    (* ---- the loop's register invariant at entry ---- *)
    assert (HS7s1 : S7 !!! Regidx Rs1 = (mword_of_int (uart_f_base i) : mword 64))
      by (rewrite /S7 upd_ne; [exact HS6s1 | reg_neq]).
    assert (HS7a4 : S7 !!! Regidx Ra4 = uart_pa i 0)
      by (rewrite /S7 upd_ne; [exact HS6a4 | reg_neq]).
    assert (HS7a3 : S7 !!! Regidx Ra3 = uart_pa i 5) by (rewrite /S7 upd_eq; reflexivity).
    assert (HS7regs : ui_regs m0 S7 (pa_stk sp0 4)).
    { destruct Hregs as (B2 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
      unfold ui_regs. split_and!;
        (rewrite /S7 upd_ne; [| reg_neq]); (rewrite /S6 upd_ne; [| reg_neq]);
        (rewrite /S5 upd_ne; [| reg_neq]); (rewrite /S4 upd_ne; [| reg_neq]);
        (rewrite /S3 upd_ne; [| reg_neq]); (rewrite /S2 upd_ne; [| reg_neq]);
        (rewrite /S1 upd_ne; [| reg_neq]); (rewrite /S0 upd_ne; [| reg_neq]); assumption. }
    iDestruct (cpu_own_transport CID0 CID8 lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (ui_ret_cont_shift CID0 CID8 γu m0 av lvl eb pme b lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iPoseProof (ui_rx i γu γv γs m0 av lvl eb pme sp0 b lks Hsp0 Hlen Hlvl Hav Hbelow) as "Rx".
    iApply ("Rx" $! CID8 S7 with "[%] [%] [%] [%] Ht Huinv Hpinv Hdlab Hbw Hrw Hcaps Hcg Hcnt Hpc Hfr Htok Hcont");
      [exact HS7regs | exact HS7s1 | exact HS7a4 | exact HS7a3].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE WHOLE FUNCTION.                                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_uartintr_sconf (i : uart_id) (γu : uart_names) (γv : disk_names)
      (γs : list gname)
      (m : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (b : bool)
      (k : nat) (hl : option (list mobs)) (lks : gset string)
    : wp_uartintr_sconf_body i γu γv γs m av lvl eb pme b k hl lks.
  Proof.
    cbv beta delta [wp_uartintr_sconf_body].
    intros pcE ret_tgt Ha0 Hlen Hlvl Hav Hbelow.
    iIntros "Hcg Hcnt #Ht Hpc #Hbw #Hrw #Hdlab #Huinv #Hpinv #Hcaps Htok Hcont".
    iAssert (ui_ret_cont γu m av lvl eb pme b lks) with "[Hcont]" as "Hcont".
    { iExact "Hcont". }
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    set (spd := pa_stk sp0 4%nat).
    assert (P02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x02)) by pcw.
    assert (P04 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x04)) by pcw.
    assert (P06 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x06)) by pcw.
    assert (P08 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x08)) by pcw.
    assert (P0a : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x0a)) by pcw.
    assert (P0c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x0c)) by pcw.
    assert (P10 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x10)) by pcw.
    assert (P12 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x12)) by pcw.
    assert (P14 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x14)) by pcw.
    assert (P18 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x18)) by pcw.
    assert (P1c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x1c)) by pcw.
    assert (P1e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x1e)) by pcw.
    assert (P20 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x20)) by pcw.
    assert (P24 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x24)) by pcw.
    assert (P28 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x28)) by pcw.
    assert (P2c : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x2c)) by pcw.
    assert (P2e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x2e)) by pcw.
    assert (Huarts14 : add_vec (add_vec (mword_of_int (KernelSyms.uartintr + 0x14) : mword 64)
                                  (auipc_off (mword_of_int 10 : mword 20)))
                         (sign_extend' 64 (mword_of_int 2198 : mword 12))
                       = (mword_of_int KernelSyms.uarts : mword 64)) by pcw.
    (* ============ PROLOGUE ============ *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4%nat b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (uii2_00 with "Ht"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd)
      by (rewrite /A0 upd_eq Hpush Hspm; reflexivity).
    iEval (rewrite P02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & _)".
    iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
    iDestruct "F3" as (v3) "H3".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1)
      by (apply ui_slot_bridge; pcw).
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2)
      by (apply ui_slot_bridge; pcw).
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3)
      by (apply ui_slot_bridge; pcw).
    (* the three spilled values, in the [rget] spelling the store leaf uses *)
    assert (HA0ra : forall (CID' : CpuId), rget (CID := CID') A0 Rra = m !!! Regidx Rra).
    { intros CID'; rgne. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    assert (HA0s0 : forall (CID' : CpuId), rget (CID := CID') A0 Rs0 = m !!! Regidx Rs0).
    { intros CID'; rgne. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    assert (HA0s1 : forall (CID' : CpuId), rget (CID := CID') A0 Rs1 = m !!! Regidx Rs1).
    { intros CID'; rgne. rewrite /A0 upd_ne; [reflexivity | reg_neq]. }
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartintr + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (av - 4)%nat v1 b with "Hcg Hpc [] [H1]").
    { iApply (uii2_02 with "Ht"). }
    { iEval (rewrite HcspA0 Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1". iEval (rewrite HcspA0 Hb1 HA0ra) in "H1".
    iEval (rewrite P04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartintr + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (av - 4)%nat v2 b with "Hcg Hpc [] [H2]").
    { iApply (uii2_04 with "Ht"). }
    { iEval (rewrite HcspA0 Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2". iEval (rewrite HcspA0 Hb2 HA0s0) in "H2".
    iEval (rewrite P06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uartintr + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (av - 4)%nat v3 b with "Hcg Hpc [] [H3]").
    { iApply (uii2_06 with "Ht"). }
    { iEval (rewrite HcspA0 Hb3). iExact "H3". }
    iIntros (CID4 Hs4) "Hcg Hpc H3". iEval (rewrite HcspA0 Hb3 HA0s1) in "H3".
    iEval (rewrite P08) in "Hpc".
    iAssert (ui_frame sp0 m) with "[H1 H2 H3 F4]" as "Hfr".
    { rewrite /ui_frame. iFrame "H1 H2 H3". iExact "F4". }
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uartintr + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_08 with "Ht"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (HA1csp : A1 !!! Regidx csp_rs1 = spd)
      by (rewrite /A1 upd_ne; [exact HcspA0 | reg_neq]).
    assert (HA1a0 : A1 !!! Regidx Ra0 = (mword_of_int (uart_index i) : mword 64)).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [exact Ha0 | reg_neq]. }
    assert (HA1regs : ui_regs m A1 spd).
    { unfold ui_regs. split_and!;
        first [ exact HA1csp
              | (rewrite /A1 upd_ne; [| reg_neq]); (rewrite /A0 upd_ne; [| reg_neq]); reflexivity ]. }
    iEval (rewrite P0a) in "Hpc".
    (* ============ THE PORT ARITHMETIC ============ *)
    (* +0x0a c.mv s1,a0 : the INDEX is kept, because gcc rebuilds the element
       pointer after the wakeup call rather than spilling it *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uartintr + 0x0a)) Rs1 Ra0
              A1 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_0a with "Ht"). }
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rewrite P0c) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rewrite HA1a0 (uix_zadd_idx i)) in "Hcg".
    set (A2 := <[Regidx Rs1 := regval_into_reg (mword_of_int (uart_index i) : mword 64)]> A1).
    change (<[Regidx Rs1 := regval_into_reg (mword_of_int (uart_index i) : mword 64)]> A1) with A2.
    assert (HA2s1 : A2 !!! Regidx Rs1 = (mword_of_int (uart_index i) : mword 64))
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2a0 : A2 !!! Regidx Ra0 = (mword_of_int (uart_index i) : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1a0 | reg_neq]).
    assert (HA2regs : ui_regs m A2 spd).
    { destruct HA1regs as (D2 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
      unfold ui_regs. split_and!; (rewrite /A2 upd_ne; [| reg_neq]); assumption. }
    (* +0x0c slli a5,a0,2 *)
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.uartintr + 0x0c)) Ra5 Ra0 (mword_of_int 2 : mword 6)
              (mword_of_int (4 * uart_index i)) A2 (av - 4)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HA2a0; apply uix_slli2)
              with "Hcg Hpc []").
    { iApply (uii2_0c with "Ht"). }
    iIntros (CID7 Hs7) "Hcg Hpc". iEval (rewrite P10) in "Hpc".
    set (A3 := <[Regidx Ra5 := regval_into_reg (mword_of_int (4 * uart_index i) : mword 64)]> A2).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (4 * uart_index i) : mword 64)]> A2) with A3.
    assert (HA3a5 : A3 !!! Regidx Ra5 = (mword_of_int (4 * uart_index i) : mword 64))
      by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a0 : A3 !!! Regidx Ra0 = (mword_of_int (uart_index i) : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]).
    (* +0x10 c.add a5,a0 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartintr + 0x10)) Ra5 Ra0
              A3 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_10 with "Ht"). }
    iIntros (CID8 Hs8) "Hcg Hpc". iEval (rewrite P12) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    iEval (rewrite HA3a5 HA3a0 (uix_add5 i)) in "Hcg".
    set (A4 := <[Regidx Ra5 := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> A3).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> A3) with A4.
    assert (HA4a5 : A4 !!! Regidx Ra5 = (mword_of_int (5 * uart_index i) : mword 64))
      by (rewrite /A4 upd_eq; reflexivity).
    (* +0x12 c.slli a5,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.uartintr + 0x12)) (Regidx Ra5) Ra5 (mword_of_int 3 : mword 6)
              A4 (av - 4)%nat b eq_refl ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_12 with "Ht"). }
    iIntros (CID9 Hs9) "Hcg Hpc". iEval (rewrite P14) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rewrite HA4a5 (uix_slli3 i)) in "Hcg".
    set (A5 := <[Regidx Ra5 := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> A4).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> A4) with A5.
    assert (HA5a5 : A5 !!! Regidx Ra5 = (mword_of_int (uart_stride * uart_index i) : mword 64))
      by (rewrite /A5 upd_eq; reflexivity).
    (* +0x14 auipc a4,0xa / +0x18 addi a4,a4,2198 : a4 := &uarts *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartintr + 0x14)) Ra4 (mword_of_int 10 : mword 20)
              A5 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_14 with "Ht"). }
    iIntros (CID10 Hs10) "Hcg Hpc". iEval (rewrite P18) in "Hpc".
    set (A6 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x14) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> A5).
    change (<[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.uartintr + 0x14) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> A5) with A6.
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartintr + 0x18)) Ra4 Ra4 (mword_of_int 2198 : mword 12)
              A6 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_18 with "Ht"). }
    iIntros (CID11 Hs11) "Hcg Hpc". iEval (rewrite P1c) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rewrite /A6 upd_eq Huarts14) in "Hcg".
    set (A7 := <[Regidx Ra4 := regval_into_reg (mword_of_int KernelSyms.uarts : mword 64)]> A6).
    change (<[Regidx Ra4 := regval_into_reg (mword_of_int KernelSyms.uarts : mword 64)]> A6) with A7.
    assert (HA7a4 : A7 !!! Regidx Ra4 = (mword_of_int KernelSyms.uarts : mword 64))
      by (rewrite /A7 upd_eq; reflexivity).
    assert (HA7a5 : A7 !!! Regidx Ra5 = (mword_of_int (uart_stride * uart_index i) : mword 64)).
    { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [exact HA5a5 | reg_neq]. }
    (* +0x1c c.add a5,a4 : a5 := &uarts[uid] *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartintr + 0x1c)) Ra5 Ra4
              A7 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (uii2_1c with "Ht"). }
    iIntros (CID12 Hs12) "Hcg Hpc". iEval (rewrite P1e) in "Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    iEval (rewrite HA7a5 HA7a4 (uix_elt_l i)) in "Hcg".
    set (A8 := <[Regidx Ra5 := regval_into_reg (mword_of_int (uart_f_base i) : mword 64)]> A7).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int (uart_f_base i) : mword 64)]> A7) with A8.
    assert (HA8a5 : A8 !!! Regidx Ra5 = (mword_of_int (uart_f_base i) : mword 64))
      by (rewrite /A8 upd_eq; reflexivity).
    (* +0x1e c.ld a5,0(a5) : the MMIO base, out of `.data` *)
    assert (Hldb : forall (CID' : CpuId),
              add_vec (rget (CID := CID') A8 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
              = pa_of_z (uart_f_base i)).
    { intros CID'; rgne. rewrite HA8a5. apply uix_fbase. }
    iAssert (uart_base_word i) as "#Hbw2"; [iExact "Hbw"|].
    iEval (rewrite /uart_base_word (uix_pa0 i) -(Hldb CID12)) in "Hbw2".
    iApply (wp_cld_s_sconf (CID := CID12) (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uartintr + 0x1e))
              Ra5 Ra5 (mword_of_int 0 : mword 12) A8 (av - 4)%nat (uart_pa i 0) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hbw2]").
    { iApply (uii2_1e with "Ht"). }
    { iExact "Hbw2". }
    iIntros (CID13 Hs13) "Hcg Hpc _". iEval (rewrite P20) in "Hpc".
    set (A9 := <[Regidx Ra5 := regval_into_reg (uart_pa i 0)]> A8).
    change (<[Regidx Ra5 := regval_into_reg (uart_pa i 0)]> A8) with A9.
    assert (HA9a5 : A9 !!! Regidx Ra5 = uart_pa i 0) by (rewrite /A9 upd_eq; reflexivity).
    (* ============ the ISR acknowledge: lbu a4,2(a5) ============ *)
    assert (HA9ad2 : forall (CID' : CpuId),
              add_vec (rget (CID := CID') A9 Ra5) (sign_extend' 64 (mword_of_int 2 : mword 12))
              = uart_pa i 2).
    { intros CID'; rgne. rewrite HA9a5. apply uix_pa2. }
    iApply (UAcc.wp_uart_read_free_s_sconf_at i γu 2 (mword_of_int (KernelSyms.uartintr + 0x20)) Ra4 Ra5
              (mword_of_int 2 : mword 12) A9 (av - 4)%nat b
              ltac:(unfold uart_size; lia) ltac:(nz) ltac:(nz) ltac:(rdok) (HA9ad2 _)
              with "Hcg Hpc [] Huinv").
    { iApply (uii2_20 with "Ht"). }
    iIntros (CID14 Hs14 bisr) "Hcg Hpc". iEval (rewrite P24) in "Hpc".
    set (B0 := <[Regidx Ra4 := regval_into_reg (lsr_ldval_of bisr)]> A9).
    change (<[Regidx Ra4 := regval_into_reg (lsr_ldval_of bisr)]> A9) with B0.
    assert (HB0a5 : B0 !!! Regidx Ra5 = uart_pa i 0)
      by (rewrite /B0 upd_ne; [exact HA9a5 | reg_neq]).
    (* ============ the LSR read -- a STABLE observation ============ *)
    assert (HB0ad5 : forall (CID' : CpuId),
              add_vec (rget (CID := CID') B0 Ra5) (sign_extend' 64 (mword_of_int 5 : mword 12))
              = uart_pa i 5).
    { intros CID'; rgne. rewrite HB0a5. apply uix_pa5. }
    iApply (UAcc.wp_uart_read_free_s_sconf_at i γu 5 (mword_of_int (KernelSyms.uartintr + 0x24)) Ra5 Ra5
              (mword_of_int 5 : mword 12) B0 (av - 4)%nat b
              ltac:(unfold uart_size; lia) ltac:(nz) ltac:(nz) ltac:(rdok) (HB0ad5 _)
              with "Hcg Hpc [] Huinv").
    { iApply (uii2_24 with "Ht"). }
    iIntros (CID15 Hs15 blsr) "Hcg Hpc". iEval (rewrite P28) in "Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg (lsr_ldval_of blsr)]> B0).
    change (<[Regidx Ra5 := regval_into_reg (lsr_ldval_of blsr)]> B0) with B1.
    (* +0x28 andi a5,a5,32 *)
    assert (HB1a5 : forall (CID' : CpuId), rget (CID := CID') B1 Ra5 = lsr_ldval_of blsr).
    { intros CID'; rgne. rewrite /B1 upd_eq. reflexivity. }
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uartintr + 0x28)) Ra5 Ra5 (mword_of_int 32 : mword 12)
              (and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12)))
              B1 (av - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rewrite HB1a5; reflexivity) with "Hcg Hpc []").
    { iApply (uii2_28 with "Ht"). }
    iIntros (CID16 Hs16) "Hcg Hpc".
    iEval (rewrite upd_upd) in "Hcg".
    iEval (rewrite P2c) in "Hpc".
    set (B2 := <[Regidx Ra5 := regval_into_reg
        (and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> B0).
    change (<[Regidx Ra5 := regval_into_reg
        (and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12)))]> B0) with B2.
    assert (HB2a5 : forall (CID' : CpuId), rget (CID := CID') B2 Ra5
                    = and_vec (lsr_ldval_of blsr) (sign_extend' 64 (mword_of_int 32 : mword 12))).
    { intros CID'; rgne. rewrite /B2 upd_eq. reflexivity. }
    assert (HB2s1 : B2 !!! Regidx Rs1 = (mword_of_int (uart_index i) : mword 64)).
    { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq].
      rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
      rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
      rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [exact HA2s1 | reg_neq]. }
    assert (HB2a0 : B2 !!! Regidx Ra0 = (mword_of_int (uart_index i) : mword 64)).
    { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B0 upd_ne; [| reg_neq].
      rewrite /A9 upd_ne; [| reg_neq]. rewrite /A8 upd_ne; [| reg_neq].
      rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
      rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]. }
    assert (HB2regs : ui_regs m B2 spd).
    { destruct HA2regs as (D2 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
      unfold ui_regs. split_and!;
        (rewrite /B2 upd_ne; [| reg_neq]); (rewrite /B0 upd_ne; [| reg_neq]);
        (rewrite /A9 upd_ne; [| reg_neq]); (rewrite /A8 upd_ne; [| reg_neq]);
        (rewrite /A7 upd_ne; [| reg_neq]); (rewrite /A6 upd_ne; [| reg_neq]);
        (rewrite /A5 upd_ne; [| reg_neq]); (rewrite /A4 upd_ne; [| reg_neq]);
        (rewrite /A3 upd_ne; [| reg_neq]); assumption. }
    (* ============ +0x2c c.bnez a5 : the THRE test ============ *)
    destruct (lsr_thre_clear blsr) eqn:Hthre.
    - (* the transmitter is still busy: fall straight through to the join *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.uartintr + 0x2c)) (mword_of_int 25 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 B2 (av - 4)%nat b UG.ug_cr7 ltac:(nz)
                ltac:(rewrite HB2a5; unfold neq_vec; rewrite -/(lsr_thre_clear blsr) Hthre; reflexivity)
                with "Hcg Hpc []").
      { iApply (uii2_2c with "Ht"). }
      iIntros (CIDF HsF) "Hcg Hpc". iEval (rewrite P2e) in "Hpc".
      iDestruct (cpu_own_transport CID CIDF lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (ui_ret_cont_shift CID CIDF γu m av lvl eb pme b lks
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ui_rx_setup i γu γv γs m B2 av lvl eb pme sp0 b lks
                HB2regs HB2s1 Hspm Hlen Hlvl Hav Hbelow
                with "Ht Huinv Hpinv Hdlab Hbw Hrw Hcaps Hcg Hcnt Hpc Hfr [Htok] Hcont").
      by iExists k, hl.
    - (* THRE: wake the writers, then join *)
      assert (Jtx : add_vec (mword_of_int (KernelSyms.uartintr + 0x2c) : mword 64)
                      (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 25 : mword 8) ('b"0"))))
                    = mword_of_int (KernelSyms.uartintr + 0x5e)) by pcw.
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.uartintr + 0x2c)) (mword_of_int 25 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 B2 (av - 4)%nat b UG.ug_cr7 ltac:(nz)
                ltac:(rewrite HB2a5; unfold neq_vec; rewrite -/(lsr_thre_clear blsr) Hthre; reflexivity)
                ltac:(rewrite Jtx; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (uii2_2c with "Ht"). }
      iNext. iIntros (CIDX HsX) "Hcg Hpc". iEval (rewrite Jtx) in "Hpc".
      assert (P62 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x5e) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x62)) by pcw.
      assert (P64 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x64)) by pcw.
      assert (P66 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x66)) by pcw.
      assert (P6a : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x6a)) by pcw.
      assert (P6e : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x6a) : mword 64) 4 = mword_of_int (KernelSyms.uartintr + 0x6e)) by pcw.
      assert (P70 : add_vec_int (mword_of_int (KernelSyms.uartintr + 0x6e) : mword 64) 2 = mword_of_int (KernelSyms.uartintr + 0x70)) by pcw.
      assert (P74 : ret_pc (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x70) : mword 64) 4) = mword_of_int (KernelSyms.uartintr + 0x74)) by pcw.
      assert (Huarts66 : add_vec (add_vec (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64)
                                    (auipc_off (mword_of_int 10 : mword 20)))
                           (sign_extend' 64 (mword_of_int 2116 : mword 12))
                         = (mword_of_int KernelSyms.uarts : mword 64)) by pcw.
      (* +0x5e slli a5,a0,2 *)
      iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.uartintr + 0x5e)) Ra5 Ra0 (mword_of_int 2 : mword 6)
                (mword_of_int (4 * uart_index i)) B2 (av - 4)%nat b
                ltac:(nz) ltac:(rdok)
                ltac:(rgne; rewrite HB2a0; apply uix_slli2)
                with "Hcg Hpc []").
      { iApply (uii2_5e with "Ht"). }
      iIntros (CIDW1 HsW1) "Hcg Hpc". iEval (rewrite P62) in "Hpc".
      set (T0 := <[Regidx Ra5 := regval_into_reg (mword_of_int (4 * uart_index i) : mword 64)]> B2).
      change (<[Regidx Ra5 := regval_into_reg (mword_of_int (4 * uart_index i) : mword 64)]> B2) with T0.
      assert (HT0a5 : T0 !!! Regidx Ra5 = (mword_of_int (4 * uart_index i) : mword 64))
        by (rewrite /T0 upd_eq; reflexivity).
      assert (HT0a0 : T0 !!! Regidx Ra0 = (mword_of_int (uart_index i) : mword 64))
        by (rewrite /T0 upd_ne; [exact HB2a0 | reg_neq]).
      (* +0x62 c.add a5,a0 *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartintr + 0x62)) Ra5 Ra0
                T0 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (uii2_62 with "Ht"). }
      iIntros (CIDW2 HsW2) "Hcg Hpc". iEval (rewrite P64) in "Hpc".
      iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
      iEval (rewrite HT0a5 HT0a0 (uix_add5 i)) in "Hcg".
      set (T1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> T0).
      change (<[Regidx Ra5 := regval_into_reg (mword_of_int (5 * uart_index i) : mword 64)]> T0) with T1.
      assert (HT1a5 : T1 !!! Regidx Ra5 = (mword_of_int (5 * uart_index i) : mword 64))
        by (rewrite /T1 upd_eq; reflexivity).
      (* +0x64 c.slli a5,3 *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.uartintr + 0x64)) (Regidx Ra5) Ra5 (mword_of_int 3 : mword 6)
                T1 (av - 4)%nat b eq_refl ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (uii2_64 with "Ht"). }
      iIntros (CIDW3 HsW3) "Hcg Hpc". iEval (rewrite P66) in "Hpc".
      iEval (rgne) in "Hcg". iEval (rewrite HT1a5 (uix_slli3 i)) in "Hcg".
      set (T2 := <[Regidx Ra5 := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> T1).
      change (<[Regidx Ra5 := regval_into_reg (mword_of_int (uart_stride * uart_index i) : mword 64)]> T1) with T2.
      assert (HT2a5 : T2 !!! Regidx Ra5 = (mword_of_int (uart_stride * uart_index i) : mword 64))
        by (rewrite /T2 upd_eq; reflexivity).
      (* +0x66 auipc a0,0xa / +0x6a addi a0,a0,2116 : a0 := &uarts *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.uartintr + 0x66)) Ra0 (mword_of_int 10 : mword 20)
                T2 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (uii2_66 with "Ht"). }
      iIntros (CIDW4 HsW4) "Hcg Hpc". iEval (rewrite P6a) in "Hpc".
      set (T3 := <[Regidx Ra0 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> T2).
      change (<[Regidx Ra0 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.uartintr + 0x66) : mword 64) (auipc_off (mword_of_int 10 : mword 20)))]> T2) with T3.
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.uartintr + 0x6a)) Ra0 Ra0 (mword_of_int 2116 : mword 12)
                T3 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (uii2_6a with "Ht"). }
      iIntros (CIDW5 HsW5) "Hcg Hpc". iEval (rewrite P6e) in "Hpc".
      iEval (rgne) in "Hcg". iEval (rewrite /T3 upd_eq Huarts66) in "Hcg".
      set (T4 := <[Regidx Ra0 := regval_into_reg (mword_of_int KernelSyms.uarts : mword 64)]> T3).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int KernelSyms.uarts : mword 64)]> T3) with T4.
      assert (HT4a0 : T4 !!! Regidx Ra0 = (mword_of_int KernelSyms.uarts : mword 64))
        by (rewrite /T4 upd_eq; reflexivity).
      assert (HT4a5 : T4 !!! Regidx Ra5 = (mword_of_int (uart_stride * uart_index i) : mword 64)).
      { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_ne; [exact HT2a5 | reg_neq]. }
      (* +0x6e c.add a0,a5 : a0 := &uarts[uid], the wait channel *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uartintr + 0x6e)) Ra0 Ra5
                T4 (av - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (uii2_6e with "Ht"). }
      iIntros (CIDW6 HsW6) "Hcg Hpc". iEval (rewrite P70) in "Hpc".
      iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
      iEval (rewrite HT4a0 HT4a5 (uix_elt_r i)) in "Hcg".
      set (T5 := <[Regidx Ra0 := regval_into_reg (mword_of_int (uart_f_base i) : mword 64)]> T4).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int (uart_f_base i) : mword 64)]> T4) with T5.
      (* +0x70 jal ra,wakeup *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uartintr + 0x70)) Rra (mword_of_int 5564 : mword 21)
                T5 (av - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (uii2_70 with "Ht"). }
      iIntros (CIDW7 HsW7) "Hcg Hpc".
      set (T6 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x70) : mword 64) 4)]> T5).
      change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uartintr + 0x70) : mword 64) 4)]> T5) with T6.
      assert (Hjwk : add_vec (mword_of_int (KernelSyms.uartintr + 0x70) : mword 64)
                       (sign_extend' 64 (mword_of_int 5564 : mword 21)) = mword_of_int KernelSyms.wakeup) by pcw.
      iEval (rewrite Hjwk) in "Hpc".
      assert (HT6ra : T6 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.uartintr + 0x70) : mword 64) 4)
        by (rewrite /T6 upd_eq; reflexivity).
      assert (HcsB2T6 : callee_saved B2 T6).
      { rewrite /T6 /T5 /T4 /T3 /T2 /T1 /T0.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      iDestruct (cpu_own_transport CID CIDW7 lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (Wakeup.wp_wakeup_sconf T6 γs pme lvl (av - 4)%nat eb b lks
                ltac:(lia)
                ltac:(intro r; apply rf_to_gmap_dom)
                Hlen
                ltac:(lia)
                ltac:(lkbelow)
                with "Hcg Hcnt Ht Hpc Hpinv").
      all: try lkbelow.
      iIntros (CIDW8 HsW8 Mw) "[%Hcsw %Hdomw] Hcg Hcnt Ht2 Hpc".
      iEval (rewrite HT6ra P74) in "Hpc".
      assert (HcsMw : callee_saved B2 Mw) by (apply (callee_saved_trans B2 T6 Mw HcsB2T6 Hcsw)).
      assert (HregsW : ui_regs m Mw spd)
        by exact (ui_regs_cs m B2 Mw spd HcsMw HB2regs).
      assert (HMws1 : Mw !!! Regidx Rs1 = (mword_of_int (uart_index i) : mword 64)).
      { rewrite (callee_saved_lookup HcsMw (mword_of_int 9) ltac:(vm_compute; reflexivity)).
        exact HB2s1. }
      (* +0x74 c.j -> the join *)
      assert (Jrel : add_vec (mword_of_int (KernelSyms.uartintr + 0x74) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.uartintr + 0x2e)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uartintr + 0x74))
                (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0")))
                Mw (av - 4)%nat b ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (uii2_74 with "Ht"). }
      iIntros (CIDW9 HsW9). iNext. iIntros "Hcg Hpc". iEval (rewrite Jrel) in "Hpc".
      iDestruct (cpu_own_transport CIDW8 CIDW9 lvl eb pme b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (ui_ret_cont_shift CID CIDW9 γu m av lvl eb pme b lks
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ui_rx_setup i γu γv γs m Mw av lvl eb pme sp0 b lks
                HregsW HMws1 Hspm Hlen Hlvl Hav Hbelow
                with "Ht Huinv Hpinv Hdlab Hbw Hrw Hcaps Hcg Hcnt Hpc Hfr [Htok] Hcont").
      by iExists k, hl.
  Qed.

End ProofUartintr.
End UartintrProof.
