(* WpUart.v -- reasoning about the UART + PLIC device fabric (DevModel.v).

   Contents:
   §1  device-fabric ghost bridges: agreement/update of the [uart_frag]/
       [plic_frag] halves against [dev_interp].  (The per-hart register
       machinery [reg_pointsto_at]/[reg_valid_at]/[reg_update_at]/
       [gregs_interp_acc_at] the wire step rides on lives in RiscvPtsto.v;
       the invariant owning the wires themselves is [wire_inv], WireInv.v.)
   §2  MMIO transaction leaves: [dev_read]/[dev_write] reductions for the
       UART registers xv6 touches, and the [exec]-level towers
       (read_ram/write_ram -> checked_mem_read/write -> mem_read/
       mem_write_value) for a 1-byte device access in Machine mode --
       the device twins of WpLoad.v / WpGprStore.v's RAM towers.
   §3  the DEVICE THREADS: [wp_uart_loop] / [wp_disk_loop] /
       [wp_plic_loop] -- the three device execution contexts, each running
       forever under ITS OWN invariant ([uart_inv] / [disk_inv] /
       [plic_inv]), plus, for the wire, the wire invariant [wire_inv] (every
       hart's [sig_seip]/[sig_meip] pin, WireInv.v).  [dev_inv] is retained
       as the persistent BUNDLE of the three, which is what every
       client-facing spec in the tree takes.  This is the shape of every
       future driver-vs-device proof: CPU-side WPs and a device loop share
       one sub-invariant, and a CPU-side proof opens only the sub-invariant
       of the device it touches.
   §4  the interrupt chain, as pure facts: UART rx-avail raises the level
       ([uart_irq]), the gateway latches it ([plic_latch]), the latched
       source drives the hart's EIP wire ([plic_eip_uart]), and a high
       [sig_seip] wire makes the S-mode dispatch fire
       ([s_dispatch_seip_fires], against WpIntrCore's [s_dispatch]). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap own mono_nat.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import DevModel PlicPlan.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
(* re-import the model AFTER Base so the model's names (read_kind/Read_plain/
   write_kind/...) win over SailStdpp's homonyms -- same order as WpLoad.v. *)
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang ObsTrace RiscvPtsto RiscvExec RiscvTryStep RiscvExtras RiscvFetchExec.
Require Import WireInv WpVirtio.
(* the disk's DMA lease is now carried in the KEYED driver protocol
   ([virtio_proto], VirtioProto.v) rather than as the bare [virtio_lease];
   these two are required AFTER SailStdpp.Base/Values above, exactly like
   WpVirtio, so their (RiscvPtsto-mirroring) elaboration is unaffected. *)
Require Import RiscvModelBytes.   (* [nth_byte] *)
Require Import DiskPtsto VirtioQueue VirtioProto.
(* A6.48 ruling 4: the disk loop is the payer of the DMA completion's log
   append, so it names the message and the store gate. *)
Require Import TsoMemPa.
Require Import PermInv.
Require Export UartNames.  (* [uart_names]: split out for the build DAG *)
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Require Import TsoCtxStore.
Require Import ConsLog.  (* [log_ok] / [read_ok] / [cons_echo] and the log laws *)
Require Import TsoCtx.  (* [rel_cells] / [rel_pre_cells] *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1  device-fabric ghost bridges.                                       *)
(* ===================================================================== *)

Section DevGhost.
  Context `{!riscvGS Σ}.

  Lemma dev_interp_agree d i u p :
    dev_interp d -∗ uart_frag i u -∗ plic_frag p -∗ ⌜duart d i = u /\ dplic d = p⌝.
  Proof using .
    iIntros "(Hua & Hpa & _) Hu Hp".
    iDestruct (uarts_auth_acc _ i with "Hua") as "[Hui _]".
    iDestruct (uart_agree with "Hui Hu") as %->.
    iDestruct (plic_agree with "Hpa Hp") as %->.
    done.
  Qed.


  (* ... and the per-device halves of that agreement, for the proofs that hold
     only ONE device's fragment (each device thread opens only its own
     invariant, so it never has the other devices' fragments to hand). *)
  Lemma dev_interp_agree_uart d i u :
    dev_interp d -∗ uart_frag i u -∗ ⌜duart d i = u⌝.
  Proof using .
    iIntros "(Hua & _ & _) Hu".
    iDestruct (uarts_auth_acc _ i with "Hua") as "[Hui _]".
    by iDestruct (uart_agree with "Hui Hu") as %->.
  Qed.

  Lemma dev_interp_agree_plic d p :
    dev_interp d -∗ plic_frag p -∗ ⌜dplic d = p⌝.
  Proof using .
    iIntros "(_ & Hpa & _) Hp".
    by iDestruct (plic_agree with "Hpa Hp") as %->.
  Qed.

  (* uart-only update (the plic component rides along) *)
  Lemma dev_interp_update_uart d i u u' :
    dev_interp d -∗ uart_frag i u ==∗ dev_interp (set_duart d i u') ∗ uart_frag i u'.
  Proof using .
    iIntros "(Hua & Hpa & Hva) Hu".
    iDestruct (uarts_auth_acc _ i with "Hua") as "[Hui Hback]".
    iMod (uart_update with "Hui Hu") as "[Hui $]".
    iDestruct ("Hback" with "Hui") as "Hua".
    rewrite /set_duart /dev_interp /=. by iFrame "Hua Hpa Hva".
  Qed.

  Lemma dev_interp_update_plic d p p' :
    dev_interp d -∗ plic_frag p ==∗ dev_interp (set_dplic d p') ∗ plic_frag p'.
  Proof using .
    iIntros "(Hua & Hpa & Hva) Hp".
    iMod (plic_update with "Hpa Hp") as "[$ $]".
    rewrite /set_dplic /dev_interp /=. by iFrame "Hua Hva".
  Qed.
End DevGhost.

(* ===================================================================== *)
(* §2  MMIO transaction leaves.                                           *)
(* ===================================================================== *)

(* PORT [i]'s registers live at [uart_base i + off]; xv6's console driver
   uses off 0..5 of [Uart0].  Everything in this section is stated at an
   arbitrary port -- the leaves are the fabric's, not the console's -- and
   the two ports' bases are literals, so a proof splits on [i] and computes.
   [uart_base_lo]/[uart_base_hi] are the only board facts any of it needs. *)
Definition uart_pa (i : uart_id) (off : Z) : Arch.pa :=
  Z_to_bv 64 (uart_base i + off).

Lemma uart_base_lo (i : uart_id) : 0x10000000 <= uart_base i.
Proof. destruct i; cbn; lia. Qed.
Lemma uart_base_hi (i : uart_id) : uart_base i + uart_size <= 0x1000a008.
Proof. destruct i; cbn; unfold uart_size; lia. Qed.

Lemma uint_uart_pa i off :
  0 <= off < uart_size -> uint (uart_pa i off) = uart_base i + off.
Proof.
  intros Hoff. unfold uart_size in Hoff.
  pose proof (uart_base_lo i). pose proof (uart_base_hi i).
  unfold uart_size in *.
  unfold uart_pa, uint, MachineWord.word_to_N. unfold get_word.
  rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small.
  2:{ assert (Hm : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
      rewrite Hm. lia. }
  apply Z2N.id. lia.
Qed.

(* A UART REGISTER IS IN THE DEVICE PMA CLASS: the whole window sits inside
   the platform's MMIO band ([RiscvPtsto.mmio_base, + mmio_size)), which is
   what [RiscvFetchExec.pma_allows_io] asks of its appliers.  (It used to be
   the strictly weaker "the access does not wrap", which was all the
   all-addresses [pma_allows_all] needed; the real table grants R/W here and
   nothing outside its three regions.) *)
Lemma uart_pa_access_io i off n :
  0 <= off < uart_size -> 1 <= n <= 4096 ->
  pma_io_access (uart_pa i off) n.
Proof.
  intros Hoff Hn.
  apply (pma_access_io _ _ (uart_base i) (uart_base i + uart_size));
    [ rewrite (uint_uart_pa i off Hoff); lia
    | rewrite (uint_uart_pa i off Hoff); lia
    | destruct i; reflexivity | destruct i; reflexivity | exact Hn ].
Qed.

Lemma dev_addr_uart i off :
  0 <= off < uart_size -> dev_addr (uart_pa i off) = true.
Proof.
  intros Hoff. unfold dev_addr. apply Z.ltb_lt.
  rewrite (uint_uart_pa i off Hoff).
  pose proof (uart_base_hi i). unfold uart_size, dev_bound in *. lia.
Qed.

(* one UART MMIO transaction, at the fabric level *)
(* the bus decodes port [i]'s window to port [i] -- what makes the leaves
   below say which chip answered *)
Lemma uart_decode_pa (i : uart_id) (off : Z) :
  0 <= off < uart_size -> uart_decode (uart_base i + off) = Some i.
Proof.
  intro Hoff. unfold uart_size in Hoff.
  assert (Hin : in_uart i (uart_base i + off) = true).
  { unfold in_uart, uart_size. apply andb_true_intro.
    split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
  destruct i.
  - unfold uart_decode. by rewrite Hin.
  - assert (E0 : in_uart Uart0 (uart_base Uart1 + off) = false).
    { unfold in_uart, uart_size. apply andb_false_intro2, Z.ltb_ge. cbn. lia. }
    unfold uart_decode. by rewrite E0 Hin.
Qed.

Lemma dev_read_uart (i : uart_id) (d : dev_state) (off : Z) (b : bv 8)
    (u' : uart_state) :
  0 <= off < uart_size ->
  uart_read (duart d i) off = Some (b, u') ->
  dev_read d (uart_pa i off) 1 = Some (b, set_duart d i u').
Proof.
  intros Hoff Hrd. unfold dev_read.
  rewrite (uint_uart_pa i off Hoff) (uart_decode_pa i off Hoff).
  replace (uart_base i + off - uart_base i) with off by lia.
  rewrite Hrd. reflexivity.
Qed.

Lemma dev_write_uart (i : uart_id) (d : dev_state) (off : Z) (b : bv 8)
    (u' : uart_state) :
  0 <= off < uart_size ->
  uart_write (duart d i) off b = Some u' ->
  dev_write d (uart_pa i off) 1 b = Some (set_duart d i u').
Proof.
  intros Hoff Hwr. unfold dev_write.
  rewrite (uint_uart_pa i off Hoff) (uart_decode_pa i off Hoff).
  replace (uart_base i + off - uart_base i) with off by lia.
  rewrite Hwr. reflexivity.
Qed.

(* the UART window is disjoint from the Sail-internal CLINT/SIG windows and
   (given the boot config) HTIF, so a UART access reaches the interpreter *)
Lemma uart_pa_not_in_clint i off :
  0 <= off < uart_size -> not_in_clint (uart_pa i off).
Proof.
  intros Hoff. right.
  rewrite (uint_uart_pa i off Hoff).
  assert (uint plat_clint_base + uint plat_clint_size = 34340864) as ->
    by (vm_compute; reflexivity).
  pose proof (uart_base_lo i). unfold uart_size in *. lia.
Qed.

Lemma uart_pa_not_in_sig i off :
  0 <= off < uart_size -> not_in_sig (uart_pa i off).
Proof.
  intros Hoff. right.
  rewrite (uint_uart_pa i off Hoff).
  assert (uint plat_sig_base + uint plat_sig_size = 201326624) as ->
    by (vm_compute; reflexivity).
  pose proof (uart_base_lo i). unfold uart_size in *. lia.
Qed.

(* every address is 1-byte aligned *)
Lemma is_aligned_paddr_1 (a : Arch.pa) : is_aligned_paddr (Physaddr a) 1 = true.
Proof. unfold is_aligned_paddr. rewrite Z.rem_1_r. reflexivity. Qed.

(* ---- the exec-level device towers (1-byte, Machine mode) ---- *)

(* read_ram at a device address: the MemRead outcome is serviced by the
   device -- the value comes from [dev_read], and the device state advances. *)
Lemma exec_read_dev_1 (pa : Arch.pa) (b : bv 8) (d' : dev_state) s :
  dev_addr pa = true ->
  dev_read s.(mdev) pa 1 = Some (b, d') ->
  exec (read_ram Read_plain (Physaddr pa) 1 false) s
    = Some ((b, default_meta), MState s.(sregs) s.(mem) d').
Proof.
  intros Hdev Hrd.
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead_dev; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  rewrite Hrd.
  reflexivity.
Qed.

(* write_ram at a device address: the MemWrite outcome is DELIVERED to the
   device as one transaction; the byte memory is untouched. *)
Lemma exec_write_dev_1 (pa : Arch.pa) (data : bv 8) (d' : dev_state) s :
  dev_addr pa = true ->
  dev_write s.(mdev) pa 1 data = Some d' ->
  exec (write_ram Write_plain (Physaddr pa) 1 data tt) s
    = Some (true, MState s.(sregs) s.(mem) d').
Proof.
  intros Hdev Hwr.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemWrite_dev; last exact Hdev.
  cbn [Interface.WriteReq.pa Interface.WriteReq.value].
  rewrite Hwr.
  reflexivity.
Qed.

(* pmaCheck for a 1-byte Load Data in a readable device PMA region *)
Lemma exec_pmaCheck_dev_load_1 (pa : Arch.pa) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr pa) 1 (Load Data) pbmt false) s = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Hread.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hread (exec_is_mag_applicable_load_data 1 s) (is_aligned_paddr_1 pa).
Qed.

(* pmaCheck for a 1-byte Store Data in a writable device PMA region *)
Lemma exec_pmaCheck_dev_store_1 (pa : Arch.pa) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr pa) 1 (Store Data) pbmt false) s = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Hwrite.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hwrite (exec_is_mag_applicable_store_data 1 s) (is_aligned_paddr_1 pa).
Qed.

(* ===================================================================== *)
(* §3  the device threads: [UartLoop i]/[DiskLoop]/[PlicLoop] each run     *)
(*     forever under their own invariant (+ the wire invariant, for the    *)
(*     wire thread).  ONE UART THREAD PER PORT, at that port's own         *)
(*     invariant and ghosts.                                               *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  The accepted-byte trace ghost.                                         *)
(*                                                                         *)
(*  [uart_acc u = u_out u ++ u_tx u] (DevModel.v) is every byte the UART    *)
(*  has accepted for transmission.  It grows ONLY when a CPU pushes to THR  *)
(*  and is left exactly alone by every autonomous device step, so it can be *)
(*  tracked by a MONOTONE ghost list: the invariant holds the authoritative *)
(*  copy, and a client keeps a persistent lower bound [uart_sent γo l] --   *)
(*  "the bytes [l] have been accepted, in that order".  That is the         *)
(*  strongest thing a driver can report at its return: its byte is by then  *)
(*  in the tx FIFO, and [u_out] alone would not yet mention it.             *)
(*                                                                         *)
(*  A monotone trace is only sound because nothing ever un-accepts a byte.  *)
(*  See the NOTE at [uart_write_thr_acc] (DevModel.v): a FIFO-clearing FCR  *)
(*  write WOULD shrink it, so no such write can be verified under [dev_inv].*)
(* ===================================================================== *)

(* [uart_names] moved to UartNames.v (build DAG; see that header). *)


Section DevLoops.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context `{!uartGhostG Σ}.
  Context `{!diskGhostG Σ}.

  Definition devN : namespace := nroot .@ "dev".

  (* ---- the accepted-byte trace: persistent history ---- *)
  Definition uart_sent_auth (γ : uart_names) (u : uart_state) : iProp Σ :=
    own γ.(un_acc) (●ML (uart_acc u : list (leibnizO (bv 8)))).
  Definition uart_sent (γ : uart_names) (l : list (bv 8)) : iProp Σ :=
    own γ.(un_acc) (◯ML (l : list (leibnizO (bv 8)))).

  (* ---- the transmitted prefix: carries a THRE observation forward ---- *)
  Definition uart_out_auth (γ : uart_names) (u : uart_state) : iProp Σ :=
    own γ.(un_out) (●ML (u_out u : list (leibnizO (bv 8)))).
  Definition uart_out_lb (γ : uart_names) (l : list (bv 8)) : iProp Σ :=
    own γ.(un_out) (◯ML (l : list (leibnizO (bv 8)))).

  (* ---- EXCLUSIVE ownership of the transmitter ----

     [uart_tx_own γ l] is the right to push bytes, and says the accepted trace
     is EXACTLY [l].  It is one half of a [ghost_var]; the invariant holds the
     other.  Two consequences make it do its job:

       - it is stable across DEVICE steps, because draining does not change
         [uart_acc] (that is the whole point of tracking the concatenation);
       - a THR push DOES change [uart_acc], so it needs both halves -- the
         invariant's and the owner's.  A hart without the token therefore
         cannot push at all, which is what pins the FIFO between a THRE poll
         and the write that follows it. *)
  Definition uart_tx_own (γ : uart_names) (l : list (bv 8)) : iProp Σ :=
    ghost_var γ.(un_tx) (1/2) l.
  Definition uart_tx_auth (γ : uart_names) (u : uart_state) : iProp Σ :=
    ghost_var γ.(un_tx) (1/2) (uart_acc u).

  (* ---- DLAB, freezable to a persistent fact ---- *)
  Definition uart_dlab_is (γ : uart_names) (dq : dfrac) (b : bool) : iProp Σ :=
    own γ.(un_dlab) (to_dfrac_agree dq (b : leibnizO bool)).
  Definition uart_dlab_auth (γ : uart_names) (u : uart_state) : iProp Σ :=
    uart_dlab_is γ (DfracOwn (1/2)) (uart_dlab u).
  (* the persistent form: DLAB is false and can never change again *)
  Definition uart_dlab_off (γ : uart_names) : iProp Σ :=
    uart_dlab_is γ DfracDiscarded false.

  Global Instance uart_sent_persistent γ l : Persistent (uart_sent γ l).
  Proof using . rewrite /uart_sent. apply _. Qed.
  Global Instance uart_sent_timeless γ l : Timeless (uart_sent γ l).
  Proof using . rewrite /uart_sent. apply _. Qed.
  (* the transmitted-prefix authority yields its own lower bound, exactly as
     [uart_ghosts_alloc] peels the accepted-trace one off [uart_sent_auth].
     A boot client needs it because [SpecMain]'s precondition asks for
     [uart_out_lb γ l0] beside the transmitter token, and the authority is on
     its way into [dev_inv_body] -- there is no other source. *)
  Lemma uart_out_auth_lb (γ : uart_names) (u : uart_state) :
    uart_out_auth γ u ⊢ uart_out_auth γ u ∗ uart_out_lb γ (u_out u).
  Proof using .
    rewrite /uart_out_auth /uart_out_lb {1}mono_list_auth_lb_op own_op.
    iIntros "[$ $]".
  Qed.

  Global Instance uart_out_lb_persistent γ l : Persistent (uart_out_lb γ l).
  Proof using . rewrite /uart_out_lb. apply _. Qed.
  Global Instance uart_out_lb_timeless γ l : Timeless (uart_out_lb γ l).
  Proof using . rewrite /uart_out_lb. apply _. Qed.
  Global Instance uart_dlab_off_persistent γ : Persistent (uart_dlab_off γ).
  Proof using . rewrite /uart_dlab_off /uart_dlab_is. apply _. Qed.
  Global Instance uart_dlab_is_timeless γ dq b : Timeless (uart_dlab_is γ dq b).
  Proof using . rewrite /uart_dlab_is. apply _. Qed.
  Global Instance uart_sent_auth_timeless γ u : Timeless (uart_sent_auth γ u).
  Proof using . rewrite /uart_sent_auth. apply _. Qed.
  Global Instance uart_out_auth_timeless γ u : Timeless (uart_out_auth γ u).
  Proof using . rewrite /uart_out_auth. apply _. Qed.

  (* -- accepted trace -- *)
  Lemma uart_sent_get γ u :
    uart_sent_auth γ u -∗ uart_sent_auth γ u ∗ uart_sent γ (uart_acc u).
  Proof using .
    iIntros "Ha". rewrite /uart_sent_auth /uart_sent.
    iEval (rewrite {1}mono_list_auth_lb_op) in "Ha".
    iDestruct "Ha" as "[$ $]".
  Qed.


  Lemma uart_sent_update γ u u' :
    uart_acc u `prefix_of` uart_acc u' ->
    uart_sent_auth γ u ==∗ uart_sent_auth γ u' ∗ uart_sent γ (uart_acc u').
  Proof using .
    iIntros (Hpre) "Ha". rewrite /uart_sent_auth.
    iMod (own_update _ _ (●ML (uart_acc u' : list (leibnizO (bv 8))))
            with "Ha") as "Ha"; [by apply mono_list_update|].
    iDestruct (uart_sent_get with "Ha") as "[$ $]". done.
  Qed.

  Lemma uart_sent_auth_stable γ u u' :
    uart_acc u' = uart_acc u -> uart_sent_auth γ u -∗ uart_sent_auth γ u'.
  Proof using . iIntros (Heq) "Ha". rewrite /uart_sent_auth Heq. done. Qed.

  (* -- transmitted prefix -- *)
  Lemma uart_out_get γ u :
    uart_out_auth γ u -∗ uart_out_auth γ u ∗ uart_out_lb γ (u_out u).
  Proof using .
    iIntros "Ha". rewrite /uart_out_auth /uart_out_lb.
    iEval (rewrite {1}mono_list_auth_lb_op) in "Ha".
    iDestruct "Ha" as "[$ $]".
  Qed.

  Lemma uart_out_prefix γ u l :
    uart_out_auth γ u -∗ uart_out_lb γ l -∗ ⌜ l `prefix_of` u_out u ⌝.
  Proof using .
    iIntros "Ha Hl". rewrite /uart_out_auth /uart_out_lb.
    by iDestruct (own_valid_2 with "Ha Hl") as %?%mono_list_both_valid_L.
  Qed.

  Lemma uart_out_update γ u u' :
    u_out u `prefix_of` u_out u' ->
    uart_out_auth γ u ==∗ uart_out_auth γ u' ∗ uart_out_lb γ (u_out u').
  Proof using .
    iIntros (Hpre) "Ha". rewrite /uart_out_auth.
    iMod (own_update _ _ (●ML (u_out u' : list (leibnizO (bv 8))))
            with "Ha") as "Ha"; [by apply mono_list_update|].
    iDestruct (uart_out_get with "Ha") as "[$ $]". done.
  Qed.

  Lemma uart_out_auth_stable γ u u' :
    u_out u' = u_out u -> uart_out_auth γ u -∗ uart_out_auth γ u'.
  Proof using . iIntros (Heq) "Ha". rewrite /uart_out_auth Heq. done. Qed.

  (* -- exclusive transmitter -- *)

  (* the owner's view of the accepted trace is the real one *)
  Lemma uart_tx_own_agree γ u l :
    uart_tx_auth γ u -∗ uart_tx_own γ l -∗ ⌜ uart_acc u = l ⌝.
  Proof using .
    iIntros "Ha Ho". rewrite /uart_tx_auth /uart_tx_own.
    by iDestruct (ghost_var_agree with "Ha Ho") as %?.
  Qed.

  (* pushing needs BOTH halves: this is what excludes a tokenless hart *)
  Lemma uart_tx_own_update γ u l u' :
    uart_tx_auth γ u -∗ uart_tx_own γ l ==∗
    uart_tx_auth γ u' ∗ uart_tx_own γ (uart_acc u').
  Proof using .
    iIntros "Ha Ho". rewrite /uart_tx_auth /uart_tx_own.
    iMod (ghost_var_update_2 (uart_acc u') with "Ha Ho") as "[$ $]";
      [apply Qp.half_half|]. done.
  Qed.

  Lemma uart_tx_auth_stable γ u u' :
    uart_acc u' = uart_acc u -> uart_tx_auth γ u -∗ uart_tx_auth γ u'.
  Proof using . iIntros (Heq) "Ha". rewrite /uart_tx_auth Heq. done. Qed.

  (* -- DLAB -- *)
  Lemma uart_dlab_agree γ u dq b :
    uart_dlab_auth γ u -∗ uart_dlab_is γ dq b -∗ ⌜ uart_dlab u = b ⌝.
  Proof using .
    iIntros "Ha Hb". rewrite /uart_dlab_auth /uart_dlab_is.
    by iDestruct (own_valid_2 with "Ha Hb") as %[_ ?]%dfrac_agree_op_valid_L.
  Qed.

  Lemma uart_dlab_auth_stable γ u u' :
    uart_dlab u' = uart_dlab u -> uart_dlab_auth γ u -∗ uart_dlab_auth γ u'.
  Proof using . iIntros (Heq) "Ha". rewrite /uart_dlab_auth Heq. done. Qed.

  (* MOVING DLAB NEEDS BOTH HALVES.  Only a write to the LCR can change DLAB,
     and this is the rule such a write's ghost step goes through: the invariant
     half and the caller's half are re-agreed together at the new value.  So a
     hart WITHOUT the caller half cannot move DLAB at all -- exclusion by ghost
     arithmetic, the same argument as [uart_tx_own]'s for the transmitter --
     which is what makes the frozen [uart_dlab_off] permanent.  The boot chain
     is the one holder: it threads the half through [uartinit]'s divisor-latch
     dance (DLAB on for the two divisor writes, off again at the final LCR
     write) and then freezes it. *)
  Lemma uart_dlab_update γ (u u' : uart_state) (b : bool) :
    uart_dlab_auth γ u -∗ uart_dlab_is γ (DfracOwn (1/2)) b ==∗
    uart_dlab_auth γ u' ∗ uart_dlab_is γ (DfracOwn (1/2)) (uart_dlab u').
  Proof using .
    iIntros "Ha Hb". rewrite /uart_dlab_auth /uart_dlab_is.
    iCombine "Ha Hb" as "H".
    iMod (own_update _ _ (to_dfrac_agree (DfracOwn (1/2)) (uart_dlab u' : leibnizO bool)
                          ⋅ to_dfrac_agree (DfracOwn (1/2)) (uart_dlab u' : leibnizO bool))
            with "H") as "H".
    { apply dfrac_agree_update_2. by rewrite dfrac_op_own Qp.half_half. }
    iDestruct "H" as "[$ $]". done.
  Qed.

  (* freeze a half into the permanent fact "DLAB is false" *)
  Lemma uart_dlab_freeze γ :
    uart_dlab_is γ (DfracOwn (1/2)) false ==∗ uart_dlab_off γ.
  Proof using .
    iIntros "H". rewrite /uart_dlab_is /uart_dlab_off /uart_dlab_is.
    iApply (own_update with "H"). apply dfrac_agree_persist.
  Qed.

  (* ---- THE PAYOFF ----

     This is what the whole ghost arrangement exists to prove, and it is worth
     stating on its own because it is the design's crux.

     A driver polls the LSR, sees THRE, and only then writes the byte.  For
     that write not to be silently dropped it needs the FIFO to still have
     room WHEN IT LANDS -- a fact about a LATER state, across which both the
     device thread and every other hart may have run.

     Given the transmitter token and the bound the poll handed back, the two
     premises of [uart_write_thr_acc] (DevModel.v) follow at ANY later opening
     of the invariant:

       - the token pins [uart_acc u2 = l], because the only transition that
         grows the accepted trace is a THR push and a push needs the token's
         half of the ghost_var, which we are holding;
       - [uart_out_lb] says the transmitted prefix has already reached [l],
         and the device can only ever extend it;
       - so by [uart_tx_still_empty] there is nothing left in the FIFO;
       - and the frozen [uart_dlab_off] says offset 0 really is THR.

     Note what is NOT needed: any assumption about the other harts' code.  A
     hart without the token simply cannot perform a push, so exclusion is by
     ghost arithmetic rather than by trusting anyone's proof. *)
  Lemma uart_tx_ready_persists γ (u2 : uart_state) (l : list (bv 8)) :
    uart_tx_own γ l -∗ uart_out_lb γ l -∗ uart_dlab_off γ -∗
    uart_tx_auth γ u2 -∗ uart_out_auth γ u2 -∗ uart_dlab_auth γ u2 -∗
    ⌜ u_tx u2 = [] /\ uart_dlab u2 = false ⌝.
  Proof using .
    iIntros "Hown Hlb Hoff Htxa Houta Hdla".
    iDestruct (uart_tx_own_agree with "Htxa Hown") as %Hacc2.
    iDestruct (uart_out_prefix with "Houta Hlb") as %Hpre.
    iDestruct (uart_dlab_agree with "Hdla Hoff") as %Hdlab.
    iPureIntro. split; [| exact Hdlab].
    exact (uart_tx_empty_of_out u2 l Hacc2 Hpre).
  Qed.

  (* and the poll side: seeing THRE at [u] while holding the token yields
     exactly the two things [uart_tx_ready_persists] wants carried forward *)
  Lemma uart_tx_poll_thre γ (u : uart_state) (l : list (bv 8)) :
    uart_thre u = true ->
    uart_tx_own γ l -∗ uart_tx_auth γ u -∗ uart_out_auth γ u -∗
    uart_tx_own γ l ∗ uart_tx_auth γ u ∗ uart_out_auth γ u ∗ uart_out_lb γ l ∗
    ⌜ u_tx u = [] /\ uart_acc u = l ⌝.
  Proof using .
    iIntros (Hthre) "Hown Htxa Houta".
    iDestruct (uart_tx_own_agree with "Htxa Hown") as %Hacc.
    assert (Htx : u_tx u = []).
    { unfold uart_thre in Hthre. by destruct (u_tx u). }
    (* THRE means the FIFO is empty, so the accepted trace IS the
       transmitted prefix: [uart_acc u = u_out u ++ [] = u_out u]. *)
    assert (Hout : u_out u = l).
    { rewrite -Hacc /uart_acc Htx. by rewrite app_nil_r. }
    iDestruct (uart_out_get with "Houta") as "[Houta Hlb]".
    rewrite Hout. iFrame "Hown Htxa Houta Hlb". done.
  Qed.

  (* the device invariant: the user halves of the device state, plus the four
     UART ghosts.  The interrupt-pin wires the PLIC drives live in their own
     invariant [wire_inv] (WireInv.v): the PLIC may flip a hart's
     external-interrupt pin at any time, so no CPU-side proof may pin it. *)
  (* the invariant's four ghost halves at a given UART state, bundled.  A
     device leaf hands this to its caller's ghost step while the invariant is
     open, and takes it back at the advanced state. *)
  Definition uart_ghosts (γ : uart_names) (u : uart_state) : iProp Σ :=
    (uart_sent_auth γ u ∗ uart_out_auth γ u ∗
     uart_tx_auth γ u ∗ uart_dlab_auth γ u)%I.

  Global Instance uart_ghosts_timeless γ u : Timeless (uart_ghosts γ u).
  Proof using . rewrite /uart_ghosts. apply _. Qed.

  (* DLAB off, read off the bundle without spending it: what the RHR pop
     needs to know that offset 0 really is the receive register and not the
     divisor latch. *)
  Lemma uart_ghosts_dlab_off (γ : uart_names) (u : uart_state) :
    uart_dlab_off γ -∗ uart_ghosts γ u -∗ ⌜ uart_dlab u = false ⌝.
  Proof using .
    iIntros "Hoff (_ & _ & _ & Hdl)".
    by iDestruct (uart_dlab_agree with "Hdl Hoff") as %Hd.
  Qed.

  (* a transition that moves no UART ghost quantity carries them all over *)
  Lemma uart_ghosts_stable γ u u' :
    uart_acc u' = uart_acc u ->
    u_out u' = u_out u ->
    uart_dlab u' = uart_dlab u ->
    uart_ghosts γ u -∗ uart_ghosts γ u'.
  Proof using .
    iIntros (Ha Ho Hd) "(Hs & Hout & Htx & Hdl)". rewrite /uart_ghosts.
    iDestruct (uart_sent_auth_stable _ u u' Ha with "Hs") as "$".
    iDestruct (uart_out_auth_stable _ u u' Ho with "Hout") as "$".
    iDestruct (uart_tx_auth_stable _ u u' Ha with "Htx") as "$".
    iDestruct (uart_dlab_auth_stable _ u u' Hd with "Hdl") as "$".
  Qed.

  (* ==================================================================== *)
  (*  THE RECEIVE SIDE: the token, the push counter, and the TAG COLUMN.   *)
  (*                                                                      *)
  (*  Every byte the environment pushes into the UART carries a            *)
  (*  persistent, application-chosen claim about the history it arrived at *)
  (*  ([RiscvPtsto.riscv_rx_tag], minted by the rx wand inside              *)
  (*  [wp_uart_loop]).  The invariant keeps those claims in a COLUMN        *)
  (*  aligned with [u_rx], so a hart that pops the FIFO gets a copy of the  *)
  (*  head's; and two counters pin the alignment arithmetically, so the     *)
  (*  FIFO-is-non-empty fact a poll observes survives to the pop.           *)
  (*                                                                      *)
  (*  EXACTLY ONE HART MAY SHORTEN THE FIFO, and that is a theorem, not a   *)
  (*  hope: the pop counter is a [ghost_var] whose other half is the        *)
  (*  RECEIVE TOKEN, and both the RHR pop and the FCR receive-flush need    *)
  (*  it.  The token lives in the PLIC invariant while the UART is          *)
  (*  unclaimed and leaves it at the claim.                                *)
  (* ==================================================================== *)

  (* the popper's half: [k] bytes have ever been removed from the FIFO, and
     [hl] is the history the LAST removed byte arrived at ([None] before the
     first pop).  THE ANCHOR RIDES WITH THE COUNT because the queued
     histories' order has to survive an EMPTY QUEUE: the column orders the
     bytes it still holds against each other and against [hl], so a pop that
     drains the FIFO leaves the order behind in the token instead of losing
     it (app-echo.md, lane CONS-CURSOR, C1). *)
  Definition uart_rx_tok (γ : uart_names) (k : nat)
      (hl : option (list mobs)) : iProp Σ :=
    ghost_var γ.(un_rxpop) (1/2) (k, hl).
  (* the invariant's half *)
  Definition uart_rx_popped (γ : uart_names) (k : nat)
      (hl : option (list mobs)) : iProp Σ :=
    ghost_var γ.(un_rxpop) (1/2) (k, hl).
  (* persistent: at least [n] bytes have ever been pushed *)
  Definition uart_rx_pushed_lb (γ : uart_names) (n : nat) : iProp Σ :=
    mono_nat_lb_own γ.(un_rxpush) n.

  (* THE CONSUMER'S HIGH-WATER MARK.  [uart_rx_hi γ q hh] is "the newest
     history the receive path's CONSUMER has taken delivery of is [hh]".
     The consumer is consoleintr, which files popped bytes in the console
     ring; one half of this lives in the PLIC payload beside the token (with
     the pure clause that it is at or before the anchor) and the other
     inside [ConsoleInv.cons_res].  The two halves ARE the link that makes
     "every byte already in the ring is older than the one I just popped" a
     theorem: without it the ring's own picture could be arbitrarily stale,
     and no amount of persistent evidence about either history decides which
     of the two came first. *)
  Definition uart_rx_hi (γ : uart_names) (q : Qp)
      (hh : option (list mobs)) : iProp Σ :=
    ghost_var γ.(un_rxhi) q hh.

  Global Instance uart_rx_pushed_lb_persistent γ n :
    Persistent (uart_rx_pushed_lb γ n).
  Proof using . rewrite /uart_rx_pushed_lb. apply _. Qed.
  Global Instance uart_rx_tok_timeless γ k hl : Timeless (uart_rx_tok γ k hl).
  Proof using . rewrite /uart_rx_tok. apply _. Qed.
  Global Instance uart_rx_hi_timeless γ q hh : Timeless (uart_rx_hi γ q hh).
  Proof using . rewrite /uart_rx_hi. apply _. Qed.

  Lemma uart_rx_tok_agree γ k k' hl hl' :
    uart_rx_popped γ k hl -∗ uart_rx_tok γ k' hl' -∗ ⌜k = k' /\ hl = hl'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq.
    iPureIntro. by injection Heq.
  Qed.
  Lemma uart_rx_tok_update γ k k' hl hl' :
    uart_rx_popped γ k hl -∗ uart_rx_tok γ k hl ==∗
      uart_rx_popped γ k' hl' ∗ uart_rx_tok γ k' hl'.
  Proof using .
    iIntros "H1 H2". iApply (ghost_var_update_halves with "H1 H2").
  Qed.

  Lemma uart_rx_hi_agree γ hh hh' :
    uart_rx_hi γ (1/2) hh -∗ uart_rx_hi γ (1/2) hh' -∗ ⌜hh = hh'⌝.
  Proof using .
    iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.
  Lemma uart_rx_hi_update γ hh hh' :
    uart_rx_hi γ (1/2) hh -∗ uart_rx_hi γ (1/2) hh ==∗
      uart_rx_hi γ (1/2) hh' ∗ uart_rx_hi γ (1/2) hh'.
  Proof using .
    iIntros "H1 H2". iApply (ghost_var_update_halves with "H1 H2").
  Qed.
  Lemma uart_rx_hi_alloc (hh : option (list mobs)) :
    ⊢ |==> ∃ γn : gname, ghost_var γn (1/2) hh ∗ ghost_var γn (1/2) hh.
  Proof using .
    iMod (ghost_var_alloc hh) as (γn) "H".
    iEval (rewrite -Qp.half_half) in "H".
    iDestruct (ghost_var_split with "H") as "[H1 H2]".
    iModIntro. iExists γn. iFrame.
  Qed.

  (* THE ONE-SHOT that says uartinit's FCR flush has run.  Its exclusive half
     is what the PLIC invariant holds until the boot chain deposits the
     token; the persistent lower bound is what plicinithart needs before it
     may enable the UART's interrupt source. *)
  Definition uart_preinit (γ : uart_names) : iProp Σ :=
    mono_nat_auth_own γ.(un_init) 1 0.
  Definition uart_inited (γ : uart_names) : iProp Σ :=
    mono_nat_lb_own γ.(un_init) 1.

  Global Instance uart_inited_persistent γ : Persistent (uart_inited γ).
  Proof using . rewrite /uart_inited. apply _. Qed.
  Global Instance uart_preinit_timeless γ : Timeless (uart_preinit γ).
  Proof using . rewrite /uart_preinit. apply _. Qed.

  Lemma uart_preinit_inited_False γ : uart_preinit γ -∗ uart_inited γ -∗ False.
  Proof using .
    iIntros "Ha Hlb".
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle].
    iPureIntro. lia.
  Qed.
  Lemma uart_preinit_fire γ : uart_preinit γ ==∗ uart_inited γ.
  Proof using .
    iIntros "Ha". rewrite /uart_preinit /uart_inited.
    iMod (mono_nat_own_update 1%nat with "Ha") as "[_ Hlb]"; [lia|].
    by iModIntro.
  Qed.

  (* THE COLUMN.  [hs !! j] is the history at which [u_rx u !! j] arrived, so
     the byte is that history's last event and the application's claim about
     it is [riscv_rx_tag] there.  [np] counts pushes and [nk] removals, and
     their difference IS the queue's length -- the arithmetic that turns a
     poll's data-ready into a pop's the-head-exists.

     ...AND IT IS ORDERED (app-echo.md, lane CONS-CURSOR, C1).  Four more
     clauses, and three pieces of vocabulary:

     * the CHAIN: [hs] is in trace order, STRICTLY -- an earlier slot's
       history is a proper prefix of a later one's.  That is what makes the
       queue a SEQUENCE of input bytes rather than a bag of them, and it is
       the only thing a reader further down the line can turn into "these
       bytes arrived in this order";
     * the ANCHOR [hl], the token's, strictly before every queued history --
       so the order does not die when the queue drains;
     * the TOP [ht], at or after the anchor and after everything queued.  It
       is an EXPLICIT existential and not [last hs] on purpose: the push has
       to know that its new history is after EVERY history the column holds,
       and one bound that dominates them all says so without a single
       [last]/[lookup] argument.  Its lower bound [obs_hist_lb] is the
       column's only non-persistent-by-accident conjunct, and it is what the
       push compares against the machine's own history.

     LOOP MUST BE OFF.  Under MCR bit 4 the transmitter's drain re-enters
     this UART's own receiver ([DevModel.uart_tx_pop]'s loopback arm) with no
     observation at all, so it would lengthen [u_rx] with no tag to file.
     The clause holds at power-on ([uart_mcr_reset] is OUT2 alone) and every
     transition but an MCR write preserves it.

     ...AND THE WIRE IS THE DRAINED SEQUENCE, which is the same clause read
     forward: [u_wire u = u_out u].  It is INDUCTIVE and not derivable
     pointwise -- the drain appends to [u_wire] only when LOOP is off
     ([ObsTrace.uart_tx_pop_wire]), and that LOOP is off is this column's
     own preceding clause, so the two have to be carried together.  The
     language's own step invariant is only the weaker
     [UartAccepted.out_wire_ok] ([u_wire] a SUBLIST of [u_out]), which is
     what a byte drained under LOOP would leave behind.  What the equality
     buys is the INDEX: the trace ledger's transmit wand is handed
     [obs_wire (open_seg h) = u_wire u], and a drained byte sits at accepted
     position [length (u_out u)] -- the two are the same position exactly
     because of this clause. *)
  (* the open segment of an OPTIONAL history: nothing before the first. *)
  Definition open_seg_o (o : option (list mobs)) : list mobs :=
    match o with Some g => open_seg g | None => [] end.

  Definition uart_col_ok (iu : uart_id) (u : uart_state) (hs : list (list mobs))
      (np nk : nat) (hl ht : option (list mobs)) : Prop :=
    np = (nk + length (u_rx u))%nat
    /\ length hs = length (u_rx u)
    /\ uart_loopback u = false
    /\ u_wire u = u_out u
    /\ (forall (j : nat) (b : bv 8) (h : list mobs),
          u_rx u !! j = Some b -> hs !! j = Some h -> obs_ends_in iu h b)
    /\ (forall (i j : nat) (hi hj : list mobs),
          hs !! i = Some hi -> hs !! j = Some hj -> (i < j)%nat ->
          hist_ext hi hj)
    /\ (forall (j : nat) (h : list mobs), hs !! j = Some h -> ohist_ext hl h)
    /\ ohist_le hl ht
    /\ (forall (j : nat) (h : list mobs),
          hs !! j = Some h -> ohist_le (Some h) ht)
    (* ...AND EVERY QUEUED BYTE KNOWS ITS INPUT NUMBER (relax-d2, lane K1).
       Four clauses, all read against [DevModel.u_recv] -- the cumulative
       list of bytes this receiver ACCEPTED -- which [ObsTrace.obs_wf]'s
       INPUT TIE identifies with the era's [ObsUartIn] trace:

         * the COUNT: pops plus queue IS what was accepted, so the pop
           counter is also "how many inputs have left the FIFO";
         * the PER-ENTRY NUMBER: the [j]th queued byte is input [nk+j+1],
           which is what a POP hands its caller and what finally tells the
           console boundary which keystroke it is filing;
         * the ANCHOR's number, [nk] -- unguarded, so [None] means zero,
           which is what makes "the last byte I popped was input [nk]"
           available even when the queue has drained;
         * the TOP's number, [np].  It is what carries the anchor's clause
           through an FCR RECEIVE FLUSH, where the anchor jumps to the top:
           a flush pops everything, so the popper's count becomes the push
           count and the two clauses stay each other's. *)
    /\ (nk + length (u_rx u))%nat = length (u_recv u)
    /\ (forall (j : nat) (hj : list mobs),
          hs !! j = Some hj ->
          length (obs_ins iu (open_seg hj)) = (nk + j + 1)%nat)
    /\ ins_len iu hl = nk
    /\ ins_len iu ht = np
    (* ...AND WHAT THE TOP'S ERA LOOKED LIKE.  Two clauses the FCR FLUSH
       spends and nothing else reads: the top's era stamp, and the wire as
       it stood at the top -- a prefix of what the transmitter has finished
       with.  At uartinit the transmitter has finished with NOTHING, so the
       second reads "no console output preceded the bytes the flush is
       about to discard", which is exactly [ConsLog.flush_lost]'s witness. *)
    /\ (forall g : list mobs, ht = Some g -> obs_boots g = S gen_id)
    /\ obs_wire iu (open_seg_o ht) `prefix_of` u_out u.

  (* the lower bound at an optional history: nothing at all when there is
     none, which is the boot state and the state after a flush that found an
     empty queue. *)
  Definition obs_hist_lb_o (o : option (list mobs)) : iProp Σ :=
    match o with Some g => obs_hist_lb g | None => emp end.

  Global Instance obs_hist_lb_o_persistent o : Persistent (obs_hist_lb_o o).
  Proof using . destruct o; apply _. Qed.
  Global Instance obs_hist_lb_o_timeless o : Timeless (obs_hist_lb_o o).
  Proof using . destruct o; apply _. Qed.

  (* the optional bound placed inside the run's own history: at [None] the
     witness is [[]] and the fact is free.  This is what turns the output
     claim's witness into a REAL prefix of the trace at the drain (lane
     OUT-FUPD). *)
  Lemma obs_hist_lb_o_prefix (o : option (list mobs)) (h : list mobs) :
    obs_auth h -∗ obs_hist_lb_o o -∗ ⌜default [] o `prefix_of` h⌝.
  Proof using .
    iIntros "Ha Ho". destruct o as [g|]; [| iPureIntro; apply prefix_nil].
    cbn [obs_hist_lb_o default].
    by iDestruct (obs_hist_lb_prefix with "Ha Ho") as %Hp.
  Qed.

  (* ==================================================================== *)
  (*  THE OUTPUT CLAIM (app-echo.md, lane OUT-FUPD).                       *)
  (*                                                                      *)
  (*  The application's own claim about the bytes THIS UART has ACCEPTED,  *)
  (*  read against an INPUT HISTORY -- a RESOURCE, so that it can say WHO   *)
  (*  may write.  AT THE CONSOLE PORT ONLY: xv6 drives                      *)
  (*  two 16550s, one the kernel's own (printk, panic) and one the console *)
  (*  under user-process control, and by the owner's ruling the theorem is *)
  (*  about the console's wire alone -- so the kernel port's invariant      *)
  (*  carries [emp] and a writer there owes no justification at all.        *)
  (*  ONE [match] rather than two invariant bodies, so [wp_uart_loop] and   *)
  (*  every device leaf stay one lemma.                                    *)
  (* ==================================================================== *)
  (* [out_res_at], [out_claim_at], [uart_out_claim] and their four laws
     lived here: the output claim's port indexing and the clause the
     invariant carried for it.  [chist_at] and [cons_claim_at] below are
     the successors -- ONE claim at ONE witness, where these were the first
     of two.

     THE ERA INDEX [k] IS EXPLICIT in the successor, and instantiated at
     [S gen_id] by the invariant's own clause.  Explicit, because the LINKS
     -- what the application supplies and what a writer spends -- are stated
     at a BOUND [k] and proved once for every era; instantiated by the
     invariant, because the port's claim is THIS era's and nothing else's,
     and threading a second index through [uart_inv] and its hundreds of
     carriers would say the same thing at a much greater cost.

     AND WHY THE WITNESS HISTORY IS EXISTENTIAL, which the successor keeps.
     The obvious form -- the claim at the receive column's TOP history -- is
     TRUE but NOT DISCHARGEABLE by any writer: a writer's view shift is
     handed the history as an opaque list, and nothing it holds orders ITS
     byte's history against the column's top.  Binding the witness instead
     promises "there is a REAL PREFIX of the run's history for which the
     boundary is good", the reality witnessed by the monotone lower bound
     [RiscvPtsto.obs_hist_lb].  A shift may then MOVE the witness forward --
     to its own byte's history, which it holds a bound on -- and the ledger
     reads the claim at a witness it can place inside the run's own history
     and lifts it there by the application's own input-monotonicity.
     NOTHING IS LOST: the claim is strongest at the empty witness, no writer
     can exhibit a witness that is not a real prefix, and no step of the
     invariant but the transmit store touches it. *)

  (* [in_res_at] lived here: the input log's port indexing, the output
     claim's twin. *)

  (* THE CONSOLE RESOURCE AT A PORT (redesign R2).  [Uart1] has no console
     discipline and claims nothing: the theorem is about the console's wire
     and the console's keyboard, and a kernel-port writer owes no
     justification at all.  NAMED [chist_at] and not [cons_res_at]: the
     console RING's own resource already has that name ([ConsoleInv], used
     across ProofConsoleread), and the two are different things. *)
  Definition chist_at (iu : uart_id) (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) : iProp Σ :=
    match iu with Uart0 => riscv_cons_res k ho H | Uart1 => emp end%I.

  Global Instance cons_res_at_timeless iu k ho H :
    Timeless (chist_at iu k ho H).
  Proof using . rewrite /chist_at. destruct iu; apply _. Qed.

  Lemma cons_res_at_uart1 (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) : ⊢ chist_at Uart1 k ho H.
  Proof using . done. Qed.

  (* [win_at] and its four lines lived here: the echo window token's port
     indexing.  It rode the PLIC payload rather than an invariant, because
     that is the one carrier that reaches consoleintr and comes back at
     every interrupt -- which is what the port's half of [uart_arm] does
     now. *)

  (* THE LOG'S HIGH-WATER HISTORY, in two halves, and the EXACT TWIN of
     [uart_rx_hi]: one half rides [uart_rx_writer] in the PLIC payload
     beside the receive token, the other sits in the port invariant's input
     claim.  The pair is the only thing that can tell the shift's caller
     that the byte it is about to log is NEWER than every byte already
     logged -- two persistent bounds on a run's history are comparable and
     no more.  It differs from [uart_rx_hi] in WHICH bytes it tracks: the
     ring's mark moves only when a byte is FILED, this one moves at every
     ACCEPTED byte, drops and erase characters included. *)
  Definition uart_log_hi (γ : uart_names) (q : Qp)
      (hg : option (list mobs)) : iProp Σ :=
    ghost_var γ.(un_loghi) q hg.

  (* THE CONSUMED SEQUENCE, in two halves: the port invariant's and the
     console ring's ([ConsoleInv.cons_deliv], spelled there as the same
     [ghost_var] at the same name because the two files are SIBLINGS --
     neither requires the other -- exactly as [ConsoleInv.cons_hi] is
     spelled beside [uart_rx_hi]).  It is what ties the boundary's [dl] to
     the ring's consumed count, without which a read cannot say where its
     window begins in the log. *)
  Definition uart_deliv (γ : uart_names) (q : Qp)
      (dv : list (list mobs * bv 8)) : iProp Σ :=
    ghost_var γ.(un_deliv) q dv.

  (* THE LOG'S EXACT MIRROR, in two halves: the port invariant's and the
     console ring's ([ConsoleInv.cons_logm], spelled there as the same
     [ghost_var] at the same name because the two files are SIBLINGS).
     A PAIR AND NOT A BOUND (lane CONS-IO milestone B, ruling F4): the
     ring's gap accumulator quantifies over the log entries ABOVE the
     ring's top, and a [mono_list] lower bound cannot exclude an entry that
     was appended after the bound was taken.  The pair says [L = pops]
     outright, which is what a read needs at the fire and what an append
     needs to reinstall the accumulator.  Only consoleintr moves it, and it
     holds cons.lock and the port invariant together when it does. *)
  Definition uart_logm (γ : uart_names) (q : Qp)
      (L : list LogEntryDefs.log_entry) : iProp Σ :=
    ghost_var γ.(un_logm) q L.

  (* THE DELIVERED COUNT, in two halves (relax-d2, lane K2): the port
     invariant's, pinned to [length (ch_dl H)], and the console ring's
     ([ConsoleInv.cons_dlcnt], the same [ghost_var] at the same name -- the
     two files are SIBLINGS, exactly as [uart_deliv]/[cons_deliv] are).

     WHY THE NUMBER AND NOT THE LIST.  The LIST's kernel half travels with
     the reader's LEASE, where the lag between the ring's consumed count
     and the boundary's [dl] is nobody's business; so the ring cannot read
     an upper bound on [dl] off it.  A full-ring drop needs exactly that
     bound -- the boundary is told "the log holds 128 echoed entries beyond
     the delivered ones", and the ring proves it from [cur + 128] echoed
     entries and [length dl <= cur].  The number is what makes the second
     half of that sentence sayable inside the ring. *)
  Definition uart_dlcnt (γ : uart_names) (q : Qp) (n : nat) : iProp Σ :=
    ghost_var γ.(un_dlcnt) q n.

  (* THE CONSOLEINTR ARM IN PROGRESS (redesign R2, option A).  A ghost_var
     PAIR: one half in the port invariant, one riding the PLIC payload
     beside the receive token.  consoleintr agrees the two at the arm's
     entry (so [None] is a PURE side condition it can prove), advances both,
     and returns them at [None] when the arm closes.

     WHY THE KERNEL OWNS IT.  consoleintr holds cons.lock for the whole arm,
     so two arms cannot overlap; but the application's echo obligation is
     persistent and its run is split across several fupds, so nothing in the
     obligation's own premises says that.  Today the application is lent an
     exclusive of its own to tell a first firing from a second, and refutes
     the second by fraction arithmetic.  This pair states the same exclusion
     where the fact actually lives -- in the kernel, about the kernel's own
     code. *)
  Definition uart_arm (γ : uart_names) (q : Qp)
      (a : option LogEntryDefs.cons_arm) : iProp Σ :=
    ghost_var γ.(un_arm) q a.

  Global Instance uart_arm_timeless γ q a : Timeless (uart_arm γ q a).
  Proof using . rewrite /uart_arm. apply _. Qed.

  Lemma uart_arm_agree (γ : uart_names) (q1 q2 : Qp) (a1 a2 : option LogEntryDefs.cons_arm) :
    uart_arm γ q1 a1 -∗ uart_arm γ q2 a2 -∗ ⌜a1 = a2⌝.
  Proof using . rewrite /uart_arm. iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2"). Qed.

  Lemma uart_arm_update (γ : uart_names) (a1 a2 a' : option LogEntryDefs.cons_arm) :
    uart_arm γ (1/2) a1 -∗ uart_arm γ (1/2) a2 ==∗
      uart_arm γ (1/2) a' ∗ uart_arm γ (1/2) a'.
  Proof using .
    rewrite /uart_arm. iIntros "H1 H2".
    iMod (ghost_var_update_halves a' with "H1 H2") as "[$ $]". done.
  Qed.

  (* THE KERNEL'S MIRROR OF THE LOG.  The application owns [riscv_cons_res];
     the kernel keeps a mono_list beside it so that the console ring can
     hold a PERSISTENT lower bound on the log and state its gap facts
     against that bound rather than against a resource it cannot see. *)
  Definition in_log_auth (γ : uart_names) (L : list LogEntryDefs.log_entry) : iProp Σ :=
    own γ.(un_log) (●ML (L : list (leibnizO LogEntryDefs.log_entry))).
  Definition in_log_lb (γ : uart_names) (L : list LogEntryDefs.log_entry) : iProp Σ :=
    own γ.(un_log) (◯ML (L : list (leibnizO LogEntryDefs.log_entry))).

  Global Instance in_log_lb_persistent γ L : Persistent (in_log_lb γ L).
  Proof using . rewrite /in_log_lb. apply _. Qed.
  Global Instance in_log_lb_timeless γ L : Timeless (in_log_lb γ L).
  Proof using . rewrite /in_log_lb. apply _. Qed.
  Global Instance uart_log_hi_timeless γ q hg : Timeless (uart_log_hi γ q hg).
  Proof using . rewrite /uart_log_hi. apply _. Qed.
  Global Instance uart_deliv_timeless γ q dv : Timeless (uart_deliv γ q dv).
  Proof using . rewrite /uart_deliv. apply _. Qed.
  Global Instance uart_logm_timeless γ q L : Timeless (uart_logm γ q L).
  Proof using . rewrite /uart_logm. apply _. Qed.
  Global Instance uart_dlcnt_timeless γ q n : Timeless (uart_dlcnt γ q n).
  Proof using . rewrite /uart_dlcnt. apply _. Qed.

  Lemma in_log_lb_get γ L : in_log_auth γ L -∗ in_log_auth γ L ∗ in_log_lb γ L.
  Proof using .
    rewrite /in_log_auth /in_log_lb. iIntros "Ha".
    iEval (rewrite {1}mono_list_auth_lb_op) in "Ha".
    iDestruct "Ha" as "[Ha Hlb]". iFrame "Ha Hlb".
  Qed.

  Lemma in_log_lb_valid γ L L' :
    in_log_auth γ L -∗ in_log_lb γ L' -∗ ⌜L' `prefix_of` L⌝.
  Proof using .
    rewrite /in_log_auth /in_log_lb. iIntros "Ha Hl".
    by iDestruct (own_valid_2 with "Ha Hl") as %?%mono_list_both_valid_L.
  Qed.

  Lemma in_log_auth_snoc γ L e :
    in_log_auth γ L ==∗ in_log_auth γ (L ++ [e]).
  Proof using .
    rewrite /in_log_auth. iIntros "Ha".
    iMod (own_update _ _
            (●ML ((L ++ [e]) : list (leibnizO LogEntryDefs.log_entry)))
            with "Ha") as "$"; [| done].
    apply mono_list_update. by exists [e].
  Qed.

  (* the log's TOP history: what the mark's two halves agree on.  Spelled
     by INDEX and not with [last], which [Stdlib.List.last] shadows in the
     files this vocabulary reaches ([ObsTrace.obs_ends_in_inj]'s note). *)
  Definition log_top (pops : list LogEntryDefs.log_entry) : option (list mobs) :=
    LogEntryDefs.le_hist <$> (pops !! (length pops - 1)%nat).

  (* THE CLAUSE THE INVARIANT CARRIES, AT ITS OWN MOVABLE WITNESS.  NOT the
     output claim's: [out_link] moves that witness at every store, and
     nothing can move the input claim along with it without an
     input-monotonicity law the application does not owe.  So the input
     side binds its own [o], moved only inside the shift's or the read's
     own view shift, where a bound on the byte's history is in hand. *)
  (* THE PORT'S ONE CLAIM (redesign R2), replacing [out_claim_at] and
     [in_claim_at].  The application's resource at ONE witness, the machine's
     accepted bytes tied to the history's own, the kernel's four halves
     against the history's fields, and the history's well-formedness -- which
     subsumes [log_ok] and adds the arm's.

     THE ARM'S HALF IS HERE, not beside it: it is a field of the history the
     resource is about, so keeping it anywhere else would need a second
     agreement to say the two describe the same arm. *)
  (* THE PORT'S ONE CLAIM (redesign R2), replacing [out_claim_at] and
     [in_claim_at].  The application's resource at ONE witness, the kernel's
     four log halves against the history's own fields, the arm's half, and
     the history's well-formedness -- which subsumes [log_ok] and adds the
     arm's.

     THE ARM'S HALF IS HERE and not beside it: it is a FIELD of the history
     the resource is about, so keeping it anywhere else would need a second
     agreement to say the two describe the same arm. *)
  (* THE LOG IS COMPLETE UP TO ITS TOP (relax-d2, lane K1).  Entry [j] of
     the console boundary's log is the [j+1]st byte the host typed at this
     port in this era -- equivalently, stated at the top alone (the log's
     chain makes the two the same): the log's LENGTH is the INPUT NUMBER of
     its last entry.  It is the boundary's half of K1: the kernel proves
     "input [n] is what I am filing now" at the arm's OPEN, and this clause
     is what carries that from one byte's close to the next byte's open.
     Read at [None] as zero, so an empty log satisfies it and the founding
     is free. *)
  (* ...UP TO THE FLUSH.  [ConsLog.flush_lost] is the one exception the
     hardware forces (uartinit's FCR clear), so the clause is stated AT THE
     LOG'S TOP with that offset: the top entry is input [length L + f], and
     [f] comes with its witness.  Two riders travel with it, and both are
     there for the TRANSPORT below: the top's era stamp and its trace
     shape, which are what turn "the top is a prefix of the byte being
     opened" into "its open SEGMENT is a prefix"
     ([ObsTrace.open_seg_prefix_of_boots]).  At an empty log the clause is
     vacuous -- which is also why an FCR flush, which moves no entry, leaves
     it alone. *)
  Definition cons_log_ins (iu : uart_id)
      (L : list LogEntryDefs.log_entry) : Prop :=
    match log_top L with
    | None => True
    | Some g =>
        obs_boots g = S gen_id /\ trace_shape g true
        /\ exists f : nat, ConsLog.flush_lost g f
             /\ (length L + f)%nat = length (obs_ins iu (open_seg g))
    end.

  (* the founding case, and the only step that moves it: a CLOSE files one
     entry, and the entry's own input number is what the clause becomes *)
  Lemma cons_log_ins_nil (iu : uart_id) : cons_log_ins iu [].
  Proof using . done. Qed.

  Lemma cons_log_ins_snoc (iu : uart_id) (L : list LogEntryDefs.log_entry)
      (e : LogEntryDefs.log_entry) (f : nat) :
    obs_boots (LogEntryDefs.le_hist e) = S gen_id ->
    trace_shape (LogEntryDefs.le_hist e) true ->
    ConsLog.flush_lost (LogEntryDefs.le_hist e) f ->
    (length L + 1 + f)%nat
      = length (obs_ins iu (open_seg (LogEntryDefs.le_hist e))) ->
    cons_log_ins iu (L ++ [e]).
  Proof using .
    intros Hb Hsh Hfl Hn.
    rewrite /cons_log_ins /log_top (ConsLog.cl_top_snoc L e) /=.
    split_and!; [exact Hb | exact Hsh |]. exists f. split; [exact Hfl |].
    rewrite length_app /=. lia.
  Qed.

  (* an empty TOP is an empty log *)
  Lemma log_top_nil (L : list LogEntryDefs.log_entry) :
    log_top L = None -> L = [].
  Proof using .
    rewrite /log_top. destruct L as [| e L]; [done |].
    intro Hx. exfalso.
    assert (Hlt : (length (e :: L) - 1 < length (e :: L))%nat)
      by (cbn [length]; lia).
    destruct (lookup_lt_is_Some_2 _ _ Hlt) as [y Hy].
    rewrite Hy /= in Hx. discriminate.
  Qed.

  (* ...and the witness travels forward inside one power cycle *)
  Lemma flush_lost_mono (g h : list mobs) (f : nat) :
    g `prefix_of` h -> obs_boots g = obs_boots h -> trace_shape h true ->
    ConsLog.flush_lost g f -> ConsLog.flush_lost h f.
  Proof using .
    intros Hp Hb Hsh [-> | (sf & Hsfp & Hw & Hn)]; [by left |].
    right. exists sf. split_and!; [| exact Hw | exact Hn].
    etrans; [exact Hsfp | exact (open_seg_prefix_of_boots g h Hp Hb Hsh)].
  Qed.

  (* ==================================================================== *)
  (*  WHAT K1 COSTS THE CALLER (relax-d2, lane K1).                        *)
  (*                                                                      *)
  (*  The byte the arm is about to open is the input RIGHT AFTER the one   *)
  (*  the log's mark [hg] names -- or, before anything has been logged at  *)
  (*  all, the first input the console ever saw, with everything before it *)
  (*  lost to uartinit's flush.  uartintr reads the disjunct off the PLIC  *)
  (*  payload's own clause and the pop's two input numbers; nothing below  *)
  (*  has to know which arm it is in.                                      *)
  (* ==================================================================== *)
  Definition k1_next (hg : option (list mobs)) (h : list mobs) : Prop :=
    (ins_len Uart0 hg + 1)%nat = length (obs_ins Uart0 (open_seg h))
    \/ (hg = None
         /\ exists f : nat, ConsLog.flush_lost h f
              /\ (1 + f)%nat = length (obs_ins Uart0 (open_seg h))).

  (* WHAT UARTINIT'S FLUSH LEFT BEHIND (relax-d2, lane K1).  The FCR clear
     discards every byte then in the FIFO, and those bytes are logged
     nowhere; what the kernel CAN say is that they all arrived before any
     console output, which is [ConsLog.flush_lost]'s witness.  Stated at the
     popper's ANCHOR and quantified over every later history of the era, so
     that the byte a later pop hands consoleintr gets the witness by
     application -- no transport at the use site. *)
  Definition uart_flushed (iu : uart_id) (hl : option (list mobs)) : Prop :=
    forall h' : list mobs,
      ohist_ext hl h' -> trace_shape h' true -> obs_boots h' = S gen_id ->
      ins_len iu hl = 0%nat
      \/ exists sf : list mobs,
           sf `prefix_of` open_seg h' /\ obs_wire iu sf = []
           /\ length (obs_ins iu sf) = ins_len iu hl.

  (* before the first pop there is nothing to have lost *)
  Lemma uart_flushed_none (iu : uart_id) : uart_flushed iu None.
  Proof using . intros h' _ _ _. by left. Qed.

  (* at the CONSOLE port it IS [ConsLog.flush_lost], by definition *)
  Lemma uart_flushed_cons (hl : option (list mobs)) (h' : list mobs) :
    uart_flushed Uart0 hl ->
    ohist_ext hl h' -> trace_shape h' true -> obs_boots h' = S gen_id ->
    ConsLog.flush_lost h' (ins_len Uart0 hl).
  Proof using . intros Hf Hx Hsh Hb. exact (Hf h' Hx Hsh Hb). Qed.

  (* ...and how the flush site builds it: the column's top knows its era and
     the wire as it stood there, and at uartinit the transmitter has
     finished with nothing. *)
  Lemma uart_flushed_intro (iu : uart_id) (hl : option (list mobs)) :
    (forall g : list mobs, hl = Some g -> obs_boots g = S gen_id) ->
    obs_wire iu (open_seg_o hl) = [] ->
    uart_flushed iu hl.
  Proof using .
    intros Hb Hw h' Hx Hsh Hbh. destruct hl as [g |]; [| by left].
    right. exists (open_seg g). cbn [open_seg_o] in Hw.
    split_and!; [| exact Hw | reflexivity].
    destruct Hx as [Hp _].
    apply (open_seg_prefix_of_boots g h' Hp); [| exact Hsh].
    rewrite (Hb g eq_refl) Hbh. reflexivity.
  Qed.

  (* ...AND WHAT IT BUYS: [ConsLog]'s K1 clause, at the boundary's own log. *)
  Lemma cons_log_ins_k1 (L : list LogEntryDefs.log_entry)
      (hg : option (list mobs)) (h : list mobs) :
    cons_log_ins Uart0 L ->
    hg = log_top L ->
    trace_shape h true ->
    obs_boots h = S gen_id ->
    (forall e, e ∈ L -> hist_ext (LogEntryDefs.le_hist e) h) ->
    k1_next hg h ->
    exists f : nat, ConsLog.flush_lost h f
      /\ (length L + 1 + f)%nat = length (obs_ins Uart0 (open_seg h)).
  Proof using .
    intros Hins -> Hsh Hbh Hbelow [Hl | (Htopn & f & Hfl & Hn)].
    - rewrite /cons_log_ins in Hins.
      destruct (log_top L) as [g |] eqn:Htop.
      + destruct Hins as (Hbg & Hsg & f & Hfl & Heq).
        (* the top entry is IN the log, hence strictly before [h] *)
        assert (Hin : exists e, L !! (length L - 1)%nat = Some e
                                /\ LogEntryDefs.le_hist e = g).
        { rewrite /log_top in Htop.
          destruct (L !! (length L - 1)%nat) as [e |] eqn:He;
            [| discriminate]. exists e. split; [reflexivity |].
          by injection Htop as <-. }
        destruct Hin as (e & He & <-).
        pose proof (Hbelow e (elem_of_list_lookup_2 _ _ _ He)) as [Hp _].
        exists f. split.
        * apply (flush_lost_mono _ h f Hp); [| exact Hsh | exact Hfl].
          rewrite Hbg Hbh. reflexivity.
        * cbn [ins_len] in Hl. lia.
      + rewrite (log_top_nil L Htop). cbn [length ins_len] in Hl |- *.
        exists 0%nat. split; [by left | lia].
    - assert (HL : L = []) by (apply log_top_nil; exact Htopn).
      rewrite HL. cbn [length]. exists f. split; [exact Hfl | lia].
  Qed.

  Definition cons_claim_at (iu : uart_id) (γ : uart_names) (u : uart_state)
      : iProp Σ :=
    (∃ (o : option (list mobs)) (H : LogEntryDefs.cons_hist),
       obs_hist_lb_o o ∗ chist_at iu (S gen_id) (default [] o) H ∗
       uart_log_hi γ (1/2) (log_top (LogEntryDefs.ch_log H)) ∗
       uart_deliv γ (1/2) (LogEntryDefs.ch_dl H) ∗
       (* ...AND ITS LENGTH, AS A NUMBER (relax-d2, lane K2): the half the
          console ring holds the partner of, so the ring can bound the
          delivered list from above without seeing it. *)
       uart_dlcnt γ (1/2) (length (LogEntryDefs.ch_dl H)) ∗
       in_log_auth γ (LogEntryDefs.ch_log H) ∗
       uart_logm γ (1/2) (LogEntryDefs.ch_log H) ∗
       uart_arm γ (1/2) (LogEntryDefs.ch_arm H) ∗
       (* BOTH PURE FACTS LAST, so every site that rebuilds the claim ends
          in one [iPureIntro; split] instead of threading them through the
          middle of the separating conjunction. *)
       ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ ∗
       ⌜ConsLog.cons_hist_ok H⌝ ∗
       ⌜cons_log_ins iu (LogEntryDefs.ch_log H)⌝)%I.

  Global Instance cons_claim_at_timeless iu γ u :
    Timeless (cons_claim_at iu γ u).
  Proof using . rewrite /cons_claim_at. apply _. Qed.

  (* the claim is about the ACCEPTED bytes, so a transition that leaves them
     alone carries it over -- [uart_out_claim_stable]'s twin *)
  Lemma cons_claim_at_stable (iu : uart_id) (γ : uart_names) (u u' : uart_state) :
    uart_acc u' = uart_acc u ->
    cons_claim_at iu γ u -∗ cons_claim_at iu γ u'.
  Proof using . iIntros (Ha) "H". by rewrite /cons_claim_at Ha. Qed.

  (* [in_claim_at] and its founding lived here: the clause the invariant
     carried for the input log. *)

  (* an INPUT event puts nothing on the wire, so the rider minted for a byte
     is a bound at its OWN post-arrival history as much as at the one
     before it *)
  Lemma obs_wire_open_seg_in (i j : uart_id) (h : list mobs) (b : bv 8) :
    obs_wire i (open_seg (h ++ [ObsUartIn j b])%list) = obs_wire i (open_seg h).
  Proof using .
    rewrite (open_seg_io h [ObsUartIn j b] ltac:(repeat constructor)).
    rewrite obs_wire_app. cbn [obs_wire]. by rewrite app_nil_r.
  Qed.

  (* ...and what an INPUT event does to the input projection: it is the
     event, so the open cycle's accepted list grows by exactly its byte. *)
  Lemma obs_ins_open_seg_in (i : uart_id) (h : list mobs) (b : bv 8) :
    obs_ins i (open_seg (h ++ [ObsUartIn i b])%list)
    = (obs_ins i (open_seg h) ++ [b])%list.
  Proof using .
    rewrite (open_seg_io h [ObsUartIn i b] ltac:(repeat constructor)).
    rewrite obs_ins_app. by rewrite obs_ins_in.
  Qed.

  Definition uart_col (iu : uart_id) (γ : uart_names) (u : uart_state)
      (hs : list (list mobs)) (np nk : nat)
      (hl ht : option (list mobs)) : iProp Σ :=
    (mono_nat_auth_own γ.(un_rxpush) 1 np ∗ uart_rx_popped γ nk hl ∗
     (* ...AND THE WIRE AS IT STOOD WHEN THE BYTE ARRIVED (lane CONS-IO,
        the coordinator's second C2 amendment).  A persistent lower bound on
        the transmitted prefix, minted at the rx arm where the trace
        coupling IS in hand and carried to whoever pops the byte: at a CPU
        MMIO step there is no trace authority at all, so the echo's store
        can get the fact "the transcript the discipline speaks of is inside
        what this UART has accepted" from nowhere else. *)
     (* ...AND THE ERA STAMP (lane CONS-IO milestone C).  The byte arrived
        in THIS era, and the number of that era is readable from the
        byte's own history: [ObsTrace.obs_wf]'s boot count at a live
        thread.  Minted at the rx push -- the one place the machine's
        history authority and the ambient generation meet -- and relayed
        with the tag to whoever pops the byte, so that consoleintr's shift
        can be paid at the CURRENT era's claim and at no other. *)
     ([∗ list] h ∈ hs, riscv_rx_tag h ∗ obs_hist_lb h ∗
                       uart_out_lb γ (obs_wire iu (open_seg h)) ∗
                       ⌜obs_boots h = S gen_id⌝ ∗
                       (* ...AND THAT THE MACHINE WAS ON.  With the era
                          stamp it is what makes one byte's open SEGMENT a
                          prefix of a later byte's
                          ([ObsTrace.open_seg_prefix_of_boots]), which is
                          how the flush's witness travels forward. *)
                       ⌜trace_shape h true⌝) ∗
     obs_hist_lb_o ht ∗
     ⌜uart_col_ok iu u hs np nk hl ht⌝)%I.

  (* THE COLUMN AS THE INVARIANT AND EVERY DEVICE LEAF CARRY IT: the
     receive column, and beside it the OUTPUT CLAIM.  They travel as one
     because they travel through the same places -- every leaf's ghost step
     already hands [uart_colE] over and takes it back, so the output side
     costs no third leg on any leaf's wand. *)
  (* THE COLUMN ALONE (redesign R2).  It used to bundle the output claim
     beside the receive column; the accepted bytes are a field of the
     history the port's ONE claim is about, so there is nothing left to
     pair it with. *)
  Definition uart_colE (iu : uart_id) (γ : uart_names) (u : uart_state) : iProp Σ :=
    (∃ hs np nk hl ht, uart_col iu γ u hs np nk hl ht)%I.

  (* the wire clause WITHOUT SPENDING the column: it is pure, so it comes
     out and the column goes back.  [uart_colE_split]/[uart_colE_intro] are
     GONE with the pairing they split: the column is all there is. *)
  Lemma uart_colE_wire_out_keep (iu : uart_id) (γ : uart_names) (u : uart_state) :
    uart_colE iu γ u -∗ ⌜u_wire u = u_out u⌝ ∗ uart_colE iu γ u.
  Proof using .
    iIntros "H".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iSplitR; [iPureIntro; exact (proj1 (proj2 (proj2 (proj2 Hok))))|].
    iExists hs, np, nk, hl, ht. iFrame "Ha Hk Hts Hht".
    iPureIntro. exact Hok.
  Qed.

  Global Instance uart_col_timeless iu γ u hs np nk hl ht :
    Timeless (uart_col iu γ u hs np nk hl ht).
  Proof using . rewrite /uart_col /uart_rx_popped. apply _. Qed.
  Global Instance uart_colE_timeless iu γ u : Timeless (uart_colE iu γ u).
  Proof using . rewrite /uart_colE. apply _. Qed.

  (* the clause the tx arm reads: the column exists only with LOOP off *)
  Lemma uart_colE_loopback (iu : uart_id) (γ : uart_names) (u : uart_state) :
    uart_colE iu γ u -∗ ⌜uart_loopback u = false⌝.
  Proof using .
    iIntros "H". iDestruct "H" as (hs np nk hl ht) "(_ & _ & _ & _ & %Hok)".
    iPureIntro. exact (proj1 (proj2 (proj2 Hok))).
  Qed.

  (* ...AND THE ONE THE LEDGER READS: the wire IS the drained sequence, so a
     client that knows [obs_wire (open_seg h) = u_wire u] knows the wire's
     length is [length (u_out u)] -- the accepted position the byte the
     drain popped sits at. *)
  Lemma uart_colE_wire_out (iu : uart_id) (γ : uart_names) (u : uart_state) :
    uart_colE iu γ u -∗ ⌜u_wire u = u_out u⌝.
  Proof using .
    iIntros "H". iDestruct "H" as (hs np nk hl ht) "(_ & _ & _ & _ & %Hok)".
    iPureIntro. exact (proj1 (proj2 (proj2 (proj2 Hok)))).
  Qed.

  (* a transition that touches neither the FIFO nor LOOP nor the transmit
     pair carries it over.  The two transmit facts are new with the
     wire/out clause and are a one-liner at every caller: no MMIO access
     moves either ([ObsTrace.uart_read_wire]/[uart_write_wire],
     [DevModel.uart_read_stable]/[uart_write_out]) and neither does an
     arrival ([uart_rx_push_wire]/[uart_rx_push_out]). *)
  (* ...AND THE ACCEPTED SEQUENCE IS UNTOUCHED TOO (lane OUT-FUPD): every
     MMIO access but the THR store leaves [uart_acc] alone
     ([DevModel.uart_read_stable]/[uart_write_out]'s first conjunct), which
     is what carries the output claim over. *)
  (* ...AND THE ACCEPTED INPUT IS UNTOUCHED TOO (relax-d2, lane K1): no MMIO
     access can make a byte arrive, so every leaf hands this over out of
     [DevModel.uart_read_recv]/[uart_write_recv]. *)
  Lemma uart_colE_stable (iu : uart_id) (γ : uart_names) (u u' : uart_state) :
    u_rx u' = u_rx u ->
    uart_loopback u' = uart_loopback u ->
    u_wire u' = u_wire u ->
    u_out u' = u_out u ->
    uart_acc u' = uart_acc u ->
    u_recv u' = u_recv u ->
    uart_colE iu γ u -∗ uart_colE iu γ u'.
  Proof using .
    iIntros (Hrx Hlb Hw Ho Hacc Hrc) "H".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iExists hs, np, nk, hl, ht. iFrame "Ha Hk Hts Hht". iPureIntro.
    rewrite /uart_col_ok Hrx Hlb Hw Ho Hrc. exact Hok.
  Qed.

  (* THE DRAIN, the one transition that moves the transmit pair: with LOOP
     off -- which is the column's own clause, so nothing has to be supplied
     -- the popped byte goes on the END of BOTH lists
     ([ObsTrace.uart_tx_pop_wire], [DevModel.uart_tx_pop_out]), and the
     receive side is untouched. *)
  Lemma uart_colE_tx_pop (iu : uart_id) (γ : uart_names) (u u' : uart_state) (b : bv 8) :
    uart_tx_pop u = Some (b, u') ->
    uart_colE iu γ u -∗ uart_colE iu γ u'.
  Proof using .
    iIntros (Hpop) "H".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & Hht & %Hok)".
    pose proof Hok as Hok'.
    destruct Hok' as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8 & _).
    destruct (uart_tx_pop_rx u b u' H3 Hpop) as [Hrxe Hlbe].
    iExists hs, np, nk, hl, ht. iFrame "Ha Hk Hts Hht". iPureIntro.
    rewrite /uart_col_ok Hrxe Hlbe (uart_tx_pop_recv u b u' Hpop).
    destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _
                     & R1 & R2 & R3 & R4 & R5 & R6).
    rewrite (uart_tx_pop_out u b u' Hpop).
    split_and!; try assumption.
    - rewrite (uart_tx_pop_wire u b u' Hpop) H3. by rewrite Hwo.
    - etrans; [exact R6 | by apply prefix_app_r].
  Qed.

  (* THE PUSH (the device thread's rx arm), AS AN ACCESSOR.  The order the
     new history has to satisfy is decided against the MACHINE'S OWN
     history, which is why this takes [obs_auth h] -- the history BEFORE the
     event -- reads the column's top out against it, and hands the auth
     straight back so the trace permit can move it.  The wand that comes out
     is the push itself, at the history the permit then produced. *)
  (* ON THE COLUMN HALF ALONE (lane OUT-FUPD): the output claim is LINEAR
     and the arrival does not touch [uart_acc], so the caller keeps it and
     carries it over with [uart_out_claim_stable] -- the push owes no
     monotonicity law and this accessor never sees the application. *)
  (* ...AND IT IS WHERE THE INPUT TIE IS SPENT (relax-d2, lane K1).  The new
     byte's INPUT NUMBER is decided here and nowhere else: [Htie] is
     [ObsTrace.obs_wf]'s input tie at the history BEFORE the event, which
     [RiscvExec.wp_uart_step] hands the thread, and it is the only thing
     that says how many bytes this receiver had already accepted.  The
     column files the number beside the tag, so every later reader of the
     FIFO -- uartgetc, uartintr, consoleintr -- gets it for free. *)
  Lemma uart_col_push_acc (iu : uart_id) (γ : uart_names) (u : uart_state) (h : list mobs) :
    obs_ins iu (open_seg h) = u_recv u ->
    (∃ hs np nk hl ht, uart_col iu γ u hs np nk hl ht) -∗ obs_auth h -∗
      obs_auth h ∗
      (∀ (u' : uart_state) (b : bv 8),
         ⌜u_rx u' = (u_rx u ++ [b])%list⌝ -∗
         ⌜uart_loopback u' = uart_loopback u⌝ -∗
         (* an arrival touches neither end of the transmit pair *)
         ⌜u_wire u' = u_wire u⌝ -∗ ⌜u_out u' = u_out u⌝ -∗
         ⌜u_recv u' = (u_recv u ++ [b])%list⌝ -∗
         riscv_rx_tag (h ++ [ObsUartIn iu b])%list -∗
         obs_hist_lb (h ++ [ObsUartIn iu b])%list -∗
         uart_out_lb γ (obs_wire iu (open_seg (h ++ [ObsUartIn iu b])%list)) -∗
         ⌜obs_boots (h ++ [ObsUartIn iu b])%list = S gen_id⌝ -∗
         (* ...AND WHAT THE ARRIVAL SAYS ABOUT THE ERA: the machine is ON,
            and the wire as it stands IS what the transmitter has finished
            with.  Both are the thread's own facts at this step, and both
            are what the FCR flush later reads off the column's top. *)
         ⌜trace_shape (h ++ [ObsUartIn iu b])%list true⌝ -∗
         ⌜obs_wire iu (open_seg (h ++ [ObsUartIn iu b])%list) = u_out u'⌝ ==∗
         (∃ hs np nk hl ht, uart_col iu γ u' hs np nk hl ht)).
  Proof using .
    intros Htie. iIntros "H Hauth".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & #Hht & %Hok)".
    (* the top is at or before the machine's current history *)
    iAssert (⌜ohist_le ht (Some h)⌝)%I as "%Htop".
    { destruct ht as [g|]; [| done]. cbn [obs_hist_lb_o].
      iDestruct (obs_hist_lb_prefix with "Hauth Hht") as %Hp.
      iPureIntro. exact Hp. }
    iFrame "Hauth".
    iIntros (u' b) "%Hrx %Hlbk %Hw %Ho %Hrc #Htg #Hlbn #Hwlb %Hbts %Hshn %Hrid".
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8
                     & R1 & R2 & R3 & R4 & R5 & R6).
    iMod (mono_nat_own_update (S np) with "Ha") as "[Ha _]"; [lia|].
    iModIntro.
    set (hn := (h ++ [ObsUartIn iu b])%list).
    (* every history the column holds is a prefix of [h], hence strictly
       before the new one *)
    assert (Hxall : forall (j : nat) (g : list mobs),
              hs !! j = Some g -> hist_ext g hn).
    { intros j g Hj.
      pose proof (H8 j g Hj) as Hg.
      assert (Hp : g `prefix_of` h).
      { destruct ht as [t|]; [| done]. cbn in Hg, Htop. by etrans. }
      exact (hist_ext_of_prefix g h hn Hp (hist_ext_snoc h (ObsUartIn iu b))). }
    iExists (hs ++ [hn])%list, (S np), nk, hl, (Some hn).
    iFrame "Ha Hk".
    iSplitL "Hts".
    { rewrite big_sepL_app. iFrame "Hts". cbn [big_opL].
      iSplitL; [| done]. iFrame "Htg Hlbn Hwlb". iPureIntro.
      split; [exact Hbts | exact Hshn]. }
    iSplitR; [iExact "Hlbn" |].
    (* the new byte's input number: the tie says the accepted list is the
       era's input trace, and an input event grows it by exactly this byte *)
    assert (Hnum : length (obs_ins iu (open_seg hn)) = S (length (u_recv u))).
    { rewrite /hn obs_ins_open_seg_in length_app Htie /=. lia. }
    iPureIntro. rewrite /uart_col_ok Hrx Hlbk Hw Ho Hrc !length_app H2 H3.
    cbn [length].
    split_and!; [lia | lia | reflexivity | exact Hwo | | | | | | lia | | exact R3
                | | intros g Hg; injection Hg as <-; exact Hbts | ].
    - (* the byte and its history still belong together *)
      intros j c g Hj Hg.
      destruct (decide (j < length (u_rx u))%nat) as [Hlt|Hge].
      + rewrite lookup_app_l in Hj; [| exact Hlt].
        rewrite lookup_app_l in Hg; [| by rewrite H2].
        exact (H4 j c g Hj Hg).
      + assert (Hj' : j = length (u_rx u)).
        { apply lookup_lt_Some in Hj. rewrite length_app in Hj.
          cbn [length] in Hj. lia. }
        subst j. rewrite lookup_app_r in Hj; [| lia].
        rewrite Nat.sub_diag in Hj. cbn in Hj. injection Hj as <-.
        rewrite lookup_app_r in Hg; [| lia].
        rewrite H2 Nat.sub_diag in Hg. cbn in Hg. injection Hg as <-.
        exact (obs_ends_in_snoc _ h b).
    - (* THE CHAIN *)
      intros i j gi gj Hi Hj Hij.
      destruct (decide (j < length hs)%nat) as [Hjlt | Hjge].
      + rewrite lookup_app_l in Hi; [| lia].
        rewrite lookup_app_l in Hj; [| lia].
        exact (H5 i j gi gj Hi Hj Hij).
      + assert (Hj' : j = length hs).
        { apply lookup_lt_Some in Hj. rewrite length_app in Hj.
          cbn [length] in Hj. lia. }
        subst j. rewrite lookup_app_r in Hj; [| lia].
        rewrite Nat.sub_diag in Hj. cbn in Hj. injection Hj as <-.
        rewrite lookup_app_l in Hi; [| lia].
        exact (Hxall i gi Hi).
    - (* THE ANCHOR is still strictly before every queued history *)
      intros j g Hj.
      destruct (decide (j < length hs)%nat) as [Hjlt | Hjge].
      + rewrite lookup_app_l in Hj; [| lia]. exact (H6 j g Hj).
      + assert (Hj' : j = length hs).
        { apply lookup_lt_Some in Hj. rewrite length_app in Hj.
          cbn [length] in Hj. lia. }
        subst j. rewrite lookup_app_r in Hj; [| lia].
        rewrite Nat.sub_diag in Hj. cbn in Hj. injection Hj as <-.
        exact (ohist_ext_of_le hl h hn
                 (ohist_le_trans hl ht (Some h) H7 Htop)
                 (hist_ext_snoc h (ObsUartIn iu b))).
    - (* the anchor is at or before the NEW top *)
      exact (ohist_le_trans hl ht (Some hn) H7
               (ohist_le_trans ht (Some h) (Some hn) Htop
                  (proj1 (hist_ext_snoc h (ObsUartIn iu b))))).
    - (* ...and so is everything queued *)
      intros j g Hj.
      destruct (decide (j < length hs)%nat) as [Hjlt | Hjge].
      + rewrite lookup_app_l in Hj; [| lia].
        exact (proj1 (Hxall j g Hj)).
      + assert (Hj' : j = length hs).
        { apply lookup_lt_Some in Hj. rewrite length_app in Hj.
          cbn [length] in Hj. lia. }
        subst j. rewrite lookup_app_r in Hj; [| lia].
        rewrite Nat.sub_diag in Hj. cbn in Hj. injection Hj as <-.
        cbn. reflexivity.
    - (* the PER-ENTRY INPUT NUMBER: the old ones are unmoved ([nk] did not
         change) and the new one is [np + 1] *)
      intros j g Hj.
      destruct (decide (j < length hs)%nat) as [Hjlt | Hjge].
      + rewrite lookup_app_l in Hj; [| lia]. exact (R2 j g Hj).
      + assert (Hj' : j = length hs).
        { apply lookup_lt_Some in Hj. rewrite length_app in Hj.
          cbn [length] in Hj. lia. }
        subst j. rewrite lookup_app_r in Hj; [| lia].
        rewrite Nat.sub_diag in Hj. cbn in Hj. injection Hj as <-.
        rewrite Hnum. lia.
    - (* ...and the TOP is the byte just pushed *)
      cbn [ins_len]. rewrite Hnum. lia.
    - (* ...and the wire at the new top IS the drained sequence *)
      cbn [open_seg_o]. rewrite Hrid Ho. reflexivity.
  Qed.

  (* THE POLL: a non-empty FIFO means at least one more byte has been pushed
     than the token's holder has removed. *)
  Lemma uart_col_poll (iu : uart_id) (γ : uart_names) (u : uart_state) (k : nat)
      (hl : option (list mobs)) :
    u_rx u <> [] ->
    uart_colE iu γ u -∗ uart_rx_tok γ k hl -∗
      uart_colE iu γ u ∗ uart_rx_tok γ k hl ∗ uart_rx_pushed_lb γ (S k).
  Proof using .
    iIntros (Hne) "H Htok".
    iDestruct "H" as (hs np nk hl0 ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iDestruct (uart_rx_tok_agree with "Hk Htok") as %[<- <-].
    pose proof Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8 & _).
    assert (Hle : (S nk <= np)%nat)
      by (destruct (u_rx u); [done | cbn [length] in H1; lia]).
    iDestruct (mono_nat_lb_own_get with "Ha") as "#Hlb".
    (* [uart_rx_tok] and [uart_rx_popped] are the same proposition, so the
       two halves must be placed by hand: [iFrame] would put the caller's
       token into the column's own slot. *)
    iSplitR "Htok".
    - iExists hs, np, nk, hl0, ht. iFrame "Ha Hk Hts Hht". iPureIntro.
      exact Hok.
    - iSplitL "Htok"; [iExact "Htok"|].
      rewrite /uart_rx_pushed_lb.
      iApply (mono_nat_lb_own_le (γ := γ.(un_rxpush)) (n := np) (S nk) Hle).
      iExact "Hlb".
  Qed.

  (* THE POP: the lower bound the poll minted refutes the empty FIFO, the
     head's tag comes out (persistent, so a copy stays), the token's count
     moves by one AND ITS ANCHOR MOVES TO THE POPPED HISTORY -- which the
     column's chain says strictly extends the one it replaces.  That pair of
     facts is what the console ring's own order is built out of. *)
  Lemma uart_col_pop (iu : uart_id) (γ : uart_names) (u u' : uart_state) (k : nat)
      (hl : option (list mobs)) (bt : bv 8) :
    (forall b rx', u_rx u = b :: rx' ->
       bt = b /\ u_rx u' = rx' /\ uart_loopback u' = uart_loopback u) ->
    (* an RHR read is a [uart_read]: it moves neither end of the transmit
       pair ([ObsTrace.uart_read_wire], [DevModel.uart_read_stable]) *)
    u_wire u' = u_wire u ->
    u_out u' = u_out u ->
    (* ...and so is the accepted sequence, which carries the output claim *)
    uart_acc u' = uart_acc u ->
    (* ...and so is the ACCEPTED INPUT: a pop consumes the FIFO, it does not
       un-receive the byte (relax-d2, lane K1) *)
    u_recv u' = u_recv u ->
    uart_colE iu γ u -∗ uart_rx_tok γ k hl -∗ uart_rx_pushed_lb γ (S k) ==∗
      uart_colE iu γ u' ∗
      (* THE ANCHOR'S INPUT NUMBER, on the way out (relax-d2, lane K1): the
         byte the popper filed LAST was input [k].  Read with the byte's own
         number below it says the two are adjacent, which is what the
         console boundary's log-completeness clause is proved from. *)
      ⌜ins_len iu hl = k⌝ ∗
      (∃ h, ⌜obs_ends_in iu h bt⌝ ∗ ⌜ohist_ext hl h⌝ ∗
            riscv_rx_tag h ∗ obs_hist_lb h ∗
            (* ...and the byte's own WIRE RIDER (lane CONS-IO), which is what
               the echo's store spends *)
            uart_out_lb γ (obs_wire iu (open_seg h)) ∗
            (* ...and its ERA STAMP (milestone C), which is what says the
               shift this byte pays for is the CURRENT era's *)
            ⌜obs_boots h = S gen_id⌝ ∗
            (* ...AND ITS INPUT NUMBER (relax-d2, lane K1): this byte is the
               [S k]th the host typed at this port in this era. *)
            ⌜length (obs_ins iu (open_seg h)) = S k⌝ ∗
            (* ...AND THAT THE MACHINE WAS ON AT IT (relax-d2, lane K1),
               which is what lets the flush's witness travel to this byte *)
            ⌜trace_shape h true⌝ ∗
            uart_rx_tok γ (S k) (Some h)).
  Proof using .
    iIntros (Hpop Hw Ho Hacc Hrc) "H Htok #Hlb".
    iDestruct "H" as (hs np nk hl0 ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iDestruct (uart_rx_tok_agree with "Hk Htok") as %[<- <-].
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8
                     & R1 & R2 & R3 & R4 & R5 & R6).
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hge].
    destruct (u_rx u) as [| b rx'] eqn:Hrx.
    { cbn [length] in H1. lia. }
    destruct (Hpop b rx' eq_refl) as (-> & Hrx' & Hlb').
    destruct hs as [| hh hs']; [cbn [length] in H2; discriminate|].
    iDestruct "Hts" as "[(#Hth & #Hlbh & #Hwlb & %Hbts & %Hshh) Hts]".
    assert (Hhead : obs_ends_in iu hh b) by exact (H4 0%nat b hh eq_refl eq_refl).
    assert (Hanch : ohist_ext hl0 hh) by exact (H6 0%nat hh eq_refl).
    (* the head's input number: the column filed it at the push *)
    assert (Hnum : length (obs_ins iu (open_seg hh)) = S nk)
      by (pose proof (R2 0%nat hh eq_refl) as Hh0; lia).
    iMod (uart_rx_tok_update γ nk (S nk) hl0 (Some hh) with "Hk Htok")
      as "[Hk Htok]".
    iModIntro. iSplitR "Htok".
    - iExists hs', np, (S nk), (Some hh), ht. iFrame "Ha Hk Hts Hht".
      iPureIntro.
      rewrite /uart_col_ok Hrx' Hlb' Hw Ho Hrc. cbn [length] in H1, H2, R1.
      split_and!; [lia | lia | exact H3 | exact Hwo | | | | | | lia | | | exact R4
                  | exact R5 | exact R6].
      + intros j c g Hj Hg. exact (H4 (S j) c g Hj Hg).
      + intros i j gi gj Hi Hj Hij.
        exact (H5 (S i) (S j) gi gj Hi Hj ltac:(lia)).
      + intros j g Hj. cbn.
        exact (H5 0%nat (S j) hh g eq_refl Hj ltac:(lia)).
      + exact (H8 0%nat hh eq_refl).
      + intros j g Hj. exact (H8 (S j) g Hj).
      + intros j g Hj. pose proof (R2 (S j) g Hj) as Hg. lia.
      + cbn [ins_len]. exact Hnum.
    - iSplitR; [iPureIntro; exact R3 |].
      iExists hh. iFrame "Htok".
      iSplitR; [iPureIntro; exact Hhead |].
      iSplitR; [iPureIntro; exact Hanch |].
      iFrame "Hth Hlbh Hwlb". iPureIntro.
      split_and!; [exact Hbts | exact Hnum | exact Hshh].
  Qed.

  (* THE FLUSH: an FCR write that clears the receive FIFO is a pop of
     EVERYTHING, and needs the token for exactly that reason.  THE ANCHOR
     BECOMES THE TOP: the flushed bytes are gone, but the next byte to
     arrive must still be known to be newer than them, and the top is the
     one bound that dominates every history the column held. *)
  Lemma uart_colE_flush (iu : uart_id) (γ : uart_names) (u u' : uart_state) (k : nat)
      (hl : option (list mobs)) :
    u_rx u' = [] ->
    uart_loopback u' = uart_loopback u ->
    (* an FCR write is a [uart_write]: it moves neither end of the transmit
       pair ([ObsTrace.uart_write_wire], [DevModel.uart_write_out]) *)
    u_wire u' = u_wire u ->
    u_out u' = u_out u ->
    (* the FCR write moves no accepted byte, so the output claim rides *)
    uart_acc u' = uart_acc u ->
    (* ...and it un-receives nothing either: the flushed bytes were accepted
       and are simply lost to the driver (relax-d2, lane K1) *)
    u_recv u' = u_recv u ->
    uart_colE iu γ u -∗ uart_rx_tok γ k hl ==∗
      uart_colE iu γ u' ∗
      (* ...AND WHAT THE DISCARDED BYTES WERE (relax-d2, lane K1): the new
         anchor's era, and the wire as it stood there.  A caller that also
         knows the transmitter has finished with nothing -- uartinit does --
         turns the pair into [uart_flushed], which is how the console
         boundary later accounts for the bytes this clear threw away. *)
      ∃ k' hl', uart_rx_tok γ k' hl'
                ∗ ⌜forall g : list mobs, hl' = Some g -> obs_boots g = S gen_id⌝
                ∗ ⌜obs_wire iu (open_seg_o hl') `prefix_of` u_out u⌝.
  Proof using .
    iIntros (Hrx Hlb Hw Ho Hacc Hrc) "H Htok".
    iDestruct "H" as (hs np nk hl0 ht) "(Ha & Hk & Hts & #Hht & %Hok)".
    iDestruct (uart_rx_tok_agree with "Hk Htok") as %[<- <-].
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8
                     & R1 & R2 & R3 & R4 & R5 & R6).
    iMod (uart_rx_tok_update γ nk np hl0 ht with "Hk Htok") as "[Hk Htok]".
    iModIntro. iSplitR "Htok";
      [| iExists np, ht; iFrame "Htok"; iPureIntro;
         split; [exact R5 | exact R6] ].
    iExists [], np, np, ht, ht. iFrame "Ha Hk Hht".
    iSplitR; [done|].
    iPureIntro. rewrite /uart_col_ok Hrx Hlb Hw Ho Hrc H3.
    cbn [length].
    split_and!; [lia | reflexivity | reflexivity | exact Hwo | | | | | | lia
                | intros j g Hj; done | exact R4 | exact R4 | exact R5 | exact R6].
    - intros j c g Hj. done.
    - intros i j gi gj Hi. done.
    - intros j g Hj. done.
    - destruct ht as [g|]; [cbn; reflexivity | exact I].
    - intros j g Hj. done.
  Qed.

  (* The PLIC half carries [plic_ok] (DevModel.v): every hart's S-context
     enable word names only the sources this machine has.  It is the loosest
     property that still lets a device-interrupt proof rule out a bogus
     enable bit, and it is per-hart-local enough that a hart running
     [plicinithart] concurrently with the others re-establishes it from its
     own write alone. *)
  (* The VIRTIO half carries the disk's DRIVER PROTOCOL ([virtio_proto],
     VirtioProto.v): the DMA lease -- ownership of every byte the device may
     write, plus the positive obligation that the queue its configuration
     names really does live inside those bytes -- held in the KEYED,
     per-request form, together with the resources the driver deposits at
     publish and withdraws at reclaim (the disk points-to auth, the receipts,
     the completed/published counters).  Unlike the other two halves this one
     is not merely a mirror of the device state -- it is what MAKES the device
     thread's DMA step justifiable, since the thread has to own what it
     overwrites.  It rides in [dev_inv] rather than in a separate invariant
     because the driver hands the lease over (and takes it back) at exactly
     the MMIO writes that already open this one.

     It also carries [virtio_isr_ok] (VirtioModel.v), the exact analogue of
     the PLIC's [plic_ok]: the interrupt-status register holds only the two
     bits the spec defines, which is what makes [virtio_disk_intr]'s 0x3
     acknowledgement provably drop the interrupt line ([virtio_ack_clears]). *)
  (* [uart_preinit] is the UART slot's PRE-STATE, which the allocation puts
     into the PLIC invariant's left arm: the receive token itself goes to the
     boot chain, which carries it to uartinit's FCR flush and deposits it
     afterwards ([uart_rx_tok_deposit]). *)
  (* THE BUNDLE IS THE CONSOLE PORT'S, and deliberately so.  The board has
     two 16550s; xv6 drives ONE of them (the console, [Uart0]) and nothing in
     the kernel names the other, so the bundle every client spec takes stays
     the console's and the second port's invariant is a separate, equally
     ordinary [uart_inv Uart1 γ1] that only adequacy and that port's own
     device thread hold.  "New specs take only the invariant(s) they use" --
     widening the bundle would put a resource nobody uses into 140 specs. *)
  Definition dev_inv_body (γ : uart_names) (γd : disk_names) : iProp Σ :=
    (∃ (u : uart_state) (p : plic_state) (v : virtio_state),
       uart_frag Uart0 u ∗ plic_frag p ∗ virtio_frag v ∗
       uart_ghosts γ u ∗ uart_colE Uart0 γ u ∗ cons_claim_at Uart0 γ u ∗
       uart_preinit γ ∗
       virtio_proto γd v ∗
       ⌜ plic_ok p ⌝ ∗ ⌜ virtio_isr_ok v ⌝)%I.

  Global Instance uart_frag_timeless i u : Timeless (uart_frag i u).
  Proof using . rewrite /uart_frag. apply _. Qed.
  Global Instance plic_frag_timeless p : Timeless (plic_frag p).
  Proof using . rewrite /plic_frag. apply _. Qed.
  Global Instance virtio_frag_timeless v : Timeless (virtio_frag v).
  Proof using . rewrite /virtio_frag. apply _. Qed.
  Global Instance dev_inv_body_timeless γ γd : Timeless (dev_inv_body γ γd).
  Proof using . rewrite /dev_inv_body. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THREE invariants, one per device thread.                           *)
  (*                                                                     *)
  (*  The device step relations are pairwise decoupled (RiscvLang §3c),   *)
  (*  so their Iris counterparts are too: each device's loop opens only   *)
  (*  its own half of the fabric, and a CPU-side proof opens only the     *)
  (*  half of the device it touches.  The namespaces are SUB-namespaces   *)
  (*  of [devN], so every existing [↑devN ⊆ E] side condition in a leaf   *)
  (*  statement keeps working unchanged (each [↑subN ⊆ ↑devN]).           *)
  (* ------------------------------------------------------------------ *)
  (* ONE NAMESPACE PER PORT: the two UART threads step decoupled halves of
     the fabric, so they must be able to open their invariants independently
     -- and a client holding both would otherwise be unable to. *)
  Definition uartN (i : uart_id) : namespace := devN .@ "uart" .@ i.
  Definition plicN : namespace := devN .@ "plic".
  Definition diskN : namespace := devN .@ "disk".

  (* ...AND THE INPUT CLAIM BESIDE THE COLUMN (lane CONS-IO).  It is not a
     conjunct of [uart_colE] because it does not travel where the column
     travels: no device leaf moves it, and every leaf's ghost step would
     have to carry it for nothing.  It sits here, where the two parties
     that DO move it -- consoleintr's shift and consoleread's receipt --
     open the invariant to reach it. *)
  Definition uart_inv_body (i : uart_id) (γ : uart_names) : iProp Σ :=
    (∃ u : uart_state, uart_frag i u ∗ uart_ghosts γ u ∗ uart_colE i γ u
       ∗ cons_claim_at i γ u)%I.

  (* ------------------------------------------------------------------ *)
  (*  THE PLIC INVARIANT'S PER-SOURCE SLOTS.                             *)
  (*                                                                     *)
  (*  Every interrupt source the PLIC can hand a hart owns a SLOT in the  *)
  (*  PLIC invariant, and a slot is a ONE-SHOT.  Before the source's      *)
  (*  device is initialized the slot holds the exclusive PRE-STATE and    *)
  (*  nothing else; the initialization takes it out and re-deposits the   *)
  (*  persistent post-state together with the source's PAYLOAD -- the     *)
  (*  resource a driver acquires by claiming that source.  The payload    *)
  (*  sits in the slot exactly while the source is NOT in service, so a   *)
  (*  claim takes it out and the matching completion puts it back, and    *)
  (*  the whole handshake is folded into [plic_claim]/[plic_complete]:    *)
  (*  their callers name only the payload.                                *)
  (*                                                                     *)
  (*  The three tables are CONCRETE, and they are indexed BY PORT.  BOTH    *)
  (*  16550s have a payload -- the receive token, THE EXCLUSIVE RIGHT TO    *)
  (*  POP that port's receive FIFO -- because uartintr drains the FIFO at   *)
  (*  BOTH ports: `while(1){c=uartgetc(u); if(c==-1)break; if(u->rx)        *)
  (*  u->rx(c);}` skips only the HOOK CALL where the hook is null, never    *)
  (*  the pop.  So the tables read through [DevModel.uart_of_irq] -- the    *)
  (*  model's own inverse of [uart_irq_id] -- and hand it the names         *)
  (*  [plic_unames] selects: the console's [γ] at [Uart0] and [γ1] at       *)
  (*  [Uart1].  Each port carries its own one-shot (the [un_init] field of  *)
  (*  its own [uart_names]).  The disk's slot is [emp] at every [p]: it is  *)
  (*  founded in its post-state at boot and survives every transition with  *)
  (*  nothing to prove.                                                     *)
  (*                                                                        *)
  (*  THE SECOND PORT'S PAYLOAD IS NOT A WEAKER ONE.  It is the SAME        *)
  (*  [plic_payload_uart] -- the pop token AND the consumer's high-water    *)
  (*  half under [ohist_le].  Port 1 has no consumer, so that half simply   *)
  (*  never moves: it is founded at [None], where [ohist_le None _] holds   *)
  (*  at every anchor ([ObsTrace.ohist_le_none]).  Free, not false -- and   *)
  (*  stating it any weaker would make [SpecUartintr]'s port-generic        *)
  (*  [uart_rx_writer] premise unsuppliable at [Uart1].                     *)
  (* ------------------------------------------------------------------ *)
  (* THE RIGHT TO POP, AND THE RIGHT TO STORE WHAT WAS POPPED.  The receive
     token alone is not a whole payload any more: the byte a hart pops has
     to be filed in the console ring, and the ring's own picture of "the
     newest byte I hold" must be known to be OLDER than the byte being
     filed.  So the payload carries the consumer's high-water half beside
     the token, with the pure clause that ties the two -- and that clause is
     re-established at every pop (the anchor moves forward) and at every
     store (the mark moves to the byte just filed). *)
  (* ...AND THE RIGHT TO LOG WHAT WAS POPPED (lane CONS-IO).  A third half,
     on the second's mould exactly: the LOG's high-water history, at or
     before the popper's anchor.  Where [uart_rx_hi] is re-established at
     every STORE, this one is re-established at every ACCEPTED byte -- so
     it is what licenses the shift on the arms that file nothing (a drop, a
     NUL, an erase) as much as on the store.  At [Uart1] there is no
     consumer and no log, so it never moves and stays at [None], exactly as
     the ring's mark does. *)
  (* THE ECHO WINDOW TOKEN was a FOURTH conjunct here until redesign R2 --
     the application's per-era exclusive, which consoleintr's shift took
     because the shift is persistent and its run was split across two
     fupds.  The arm's own half below does that work: it says WHICH arm is
     open, not merely that one may be, so a second open is refuted by the
     ghost rather than by a counting argument. *)
  (* ...AND AT THE CONSOLE PORT THE LOG'S MARK IS THE ANCHOR ITSELF
     (relax-d2, lane K1).  Between interrupts every popped byte has been
     FILED, so the newest logged history and the newest popped one are the
     same -- which, read against the column's [ins_len hl = nk], is what
     tells the next pop's arm WHICH input it is handling.  [Uart1] has no
     log and no consumer, so its half never moves and the old "at or
     before" is all that can be said there. *)
  (* ...OR NOTHING HAS BEEN LOGGED YET, and everything the popper has
     removed went to uartinit's flush ([uart_flushed]).  The disjunction is
     what makes the BOOT deposit provable: at that point the log is empty
     and the anchor may already be past the bytes the flush discarded. *)
  Definition uart_log_at (iu : uart_id) (hg hl : option (list mobs)) : Prop :=
    match iu with
    | Uart0 => hg = hl \/ (hg = None /\ uart_flushed Uart0 hl)
    | Uart1 => ohist_le hg hl
    end.

  Lemma uart_log_at_le (iu : uart_id) (hg hl : option (list mobs)) :
    uart_log_at iu hg hl -> ohist_le hg hl.
  Proof using .
    destruct iu; cbn; [| done].
    intros [-> | [-> _]]; [destruct hl; cbn; done | exact I].
  Qed.

  (* THE RELAY, BUILT (relax-d2, lane K1): uartintr turns the payload's own
     clause and the pop's two input numbers into the one fact consoleintr
     hands the boundary. *)
  Lemma k1_next_of_log_at (hg hl : option (list mobs)) (h : list mobs)
      (k : nat) :
    uart_log_at Uart0 hg hl ->
    ins_len Uart0 hl = k ->
    length (obs_ins Uart0 (open_seg h)) = S k ->
    ohist_ext hl h -> trace_shape h true -> obs_boots h = S gen_id ->
    k1_next hg h.
  Proof using .
    intros Hat Hanum Hnum Hx Hsh Hbh. cbn [uart_log_at] in Hat.
    destruct Hat as [-> | [-> Hfl]].
    - left. rewrite Hanum Hnum. lia.
    - right. split; [reflexivity |]. exists k. split.
      + rewrite -Hanum. exact (uart_flushed_cons hl h Hfl Hx Hsh Hbh).
      + lia.
  Qed.

  Definition uart_rx_writer (iu : uart_id) (γ : uart_names) (k : nat)
      (hl : option (list mobs)) : iProp Σ :=
    (uart_rx_tok γ k hl ∗
     (∃ hh : option (list mobs), uart_rx_hi γ (1/2) hh ∗ ⌜ohist_le hh hl⌝) ∗
     (∃ hg : option (list mobs), uart_log_hi γ (1/2) hg ∗ ⌜uart_log_at iu hg hl⌝) ∗
     (* THE ARM'S OTHER HALF (redesign R2), at [None]: between interrupts no
        consoleintr arm is in progress, and this payload is the one carrier
        that reaches consoleintr and comes back at every interrupt. *)
     uart_arm γ (1/2) None)%I.

  Definition plic_payload_uart (iu : uart_id) (γ : uart_names) : iProp Σ :=
    (∃ (k : nat) (hl : option (list mobs)), uart_rx_writer iu γ k hl)%I.

  (* WHICH PORT'S GHOSTS A TRACKED UART SOURCE NAMES.  The one place the two
     bundles are told apart; everything below is stated through it, so no
     slot lemma is written twice. *)
  Definition plic_unames (γ γ1 : uart_names) (i : uart_id) : uart_names :=
    match i with Uart0 => γ | Uart1 => γ1 end.

  Definition plic_payload (γ γ1 : uart_names) (i : N) : iProp Σ :=
    (match uart_of_irq i with
     | Some j => plic_payload_uart j (plic_unames γ γ1 j)
     | None => emp
     end)%I.
  Definition plic_preinit (γ γ1 : uart_names) (i : N) : iProp Σ :=
    (match uart_of_irq i with
     | Some j => uart_preinit (plic_unames γ γ1 j)
     | None => False
     end)%I.
  Definition plic_inited (γ γ1 : uart_names) (i : N) : iProp Σ :=
    (match uart_of_irq i with
     | Some j => uart_inited (plic_unames γ γ1 j)
     | None => emp
     end)%I.

  Definition plic_slot (γ γ1 : uart_names) (p : plic_state) (i : N) : iProp Σ :=
    (plic_preinit γ γ1 i
     ∨ (plic_inited γ γ1 i ∗
        if p_claimed p i then emp else plic_payload γ γ1 i))%I.

  (* THE SOURCES THE INVARIANT TRACKS.  Not [plic_srcs] (DevModel.v: all
     ninety-five real ids): under [plic_ok] a claim can only ever return one
     of the machine's own three ([PlicPlan.plic_enabled_srcs], and
     [plic_claim_ret] on top of it), so this list already covers every source
     a claim can hand a payload for -- and the big-op is a three-element cons
     instead of a ninety-five-element fold. *)
  Definition plic_tracked : list N :=
    [(uart_irq_id Uart0); (uart_irq_id Uart1); virtio_irq_id].

  Definition plic_slots (γ γ1 : uart_names) (p : plic_state) : iProp Σ :=
    ([∗ list] i ∈ plic_tracked, plic_slot γ γ1 p i)%I.

  (* ONE PORT'S SLOT, PORT-FREE: the shape the accessors and the two movers
     are stated at, so the second port costs no cloned lemma.  [cl] is that
     source's service bit. *)
  Definition plic_uslot (iu : uart_id) (γu : uart_names) (cl : bool) : iProp Σ :=
    (uart_preinit γu
     ∨ (uart_inited γu ∗ if cl then emp else plic_payload_uart iu γu))%I.

  Lemma plic_slot_to_uslot (γ γ1 : uart_names) (p : plic_state) (j : uart_id) :
    plic_slot γ γ1 p (uart_irq_id j) -∗
    plic_uslot j (plic_unames γ γ1 j) (p_claimed p (uart_irq_id j)).
  Proof using .
    rewrite /plic_slot /plic_uslot /plic_preinit /plic_inited /plic_payload
            uart_of_irq_id. iIntros "H". iExact "H".
  Qed.

  Lemma plic_uslot_to_slot (γ γ1 : uart_names) (p : plic_state) (j : uart_id) :
    plic_uslot j (plic_unames γ γ1 j) (p_claimed p (uart_irq_id j)) -∗
    plic_slot γ γ1 p (uart_irq_id j).
  Proof using .
    rewrite /plic_slot /plic_uslot /plic_preinit /plic_inited /plic_payload
            uart_of_irq_id. iIntros "H". iExact "H".
  Qed.

  (* A PAYLOAD-LESS SLOT IS FREE, at any state: both of its arms are [emp].
     This is what makes the big-op collapse to the two ports' slots. *)
  Lemma plic_slot_other (γ γ1 : uart_names) (p : plic_state) (i : N) :
    uart_of_irq i = None -> ⊢ plic_slot γ γ1 p i.
  Proof using .
    intros Hi.
    rewrite /plic_slot /plic_preinit /plic_inited /plic_payload Hi.
    iRight. iSplitR; [done|]. destruct (p_claimed p i); done.
  Qed.

  (* ...so the big-op IS the two UART slots, in both directions. *)
  Lemma plic_slots_eq (γ γ1 : uart_names) (p : plic_state) :
    plic_slots γ γ1 p ⊣⊢
      plic_uslot Uart0 γ  (p_claimed p (uart_irq_id Uart0)) ∗
      plic_uslot Uart1 γ1 (p_claimed p (uart_irq_id Uart1)).
  Proof using .
    rewrite /plic_slots /plic_tracked. iSplit.
    - iIntros "(H0 & H1 & _)".
      iSplitL "H0".
      + iApply (plic_slot_to_uslot γ γ1 p Uart0 with "H0").
      + iApply (plic_slot_to_uslot γ γ1 p Uart1 with "H1").
    - iIntros "(H0 & H1)".
      iSplitL "H0".
      + iApply (plic_uslot_to_slot γ γ1 p Uart0 with "H0").
      + iSplitL "H1".
        * iApply (plic_uslot_to_slot γ γ1 p Uart1 with "H1").
        * iSplitR; [| done].
          iApply (plic_slot_other γ γ1 p virtio_irq_id).
          vm_compute. reflexivity.
  Qed.

  (* THE UART SLOT, read and written.  [plic_uslot] is a definition, so the
     proofmode needs these three to see its disjunction; they are also where
     the PRE-STATE IS REFUTED, which is the whole content of "a caller
     holding [uart_inited] never meets the left arm". *)
  Lemma plic_uslot_cases (iu : uart_id) (γu : uart_names) (cl : bool) :
    plic_uslot iu γu cl -∗
      uart_preinit γu
      ∨ (uart_inited γu ∗ if cl then emp else plic_payload_uart iu γu).
  Proof using . rewrite /plic_uslot. iIntros "H". iExact "H". Qed.

  Lemma plic_uslot_intro (iu : uart_id) (γu : uart_names) (cl : bool) :
    uart_inited γu -∗
    (if cl then emp else plic_payload_uart iu γu) -∗
    plic_uslot iu γu cl.
  Proof using .
    iIntros "#Hin Hpay". rewrite /plic_uslot. iRight.
    iSplitR; [iExact "Hin"|]. iExact "Hpay".
  Qed.

  Lemma plic_uslot_elim (iu : uart_id) (γu : uart_names) (cl : bool) :
    uart_inited γu -∗ plic_uslot iu γu cl -∗
    (if cl then emp else plic_payload_uart iu γu).
  Proof using .
    iIntros "#Hin Hu".
    iDestruct (plic_uslot_cases with "Hu") as "[Hpre | [_ Hpay]]".
    - iDestruct (uart_preinit_inited_False with "Hpre Hin") as %[].
    - iExact "Hpay".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  TWO PURE FACTS THE MOVERS NEED AT EITHER PORT.                     *)
  (* ------------------------------------------------------------------ *)

  (* [PlicPlan.uart_irq_id_range] is stated at the console; a completion of
     the SECOND port's source must land as well. *)
  Lemma uart_irq_id_range_at (j : uart_id) :
    (1 <= Z.of_N (uart_irq_id j))%Z /\
    (Z.of_N (uart_irq_id j) < Z.of_nat plic_nsrc)%Z.
  Proof using . destruct j; unfold uart_irq_id, plic_nsrc; cbn; lia. Qed.

  (* ...and the port-generic twin of [PlicPlan.plic_claim_uart_of_ret]: the
     id a claim RETURNS identifies the source it took, at either port. *)
  Lemma plic_claim_uart_ret_at (p : plic_state) (c : nat) (i : N) (j : uart_id) :
    plic_ok p -> plic_best p c = Some i ->
    Z_to_bv 32 (Z.of_N i) = Z_to_bv 32 (Z.of_N (uart_irq_id j)) ->
    i = uart_irq_id j.
  Proof using .
    intros Hok Hbest Heq.
    destruct (plic_best_spec p c i Hbest) as [Hin Hcand].
    assert (Hen : plic_enabled p c i = true).
    { unfold plic_cand in Hcand.
      apply andb_prop in Hcand as [Hc _]. apply andb_prop in Hc as [_ Hc].
      exact Hc. }
    destruct (plic_enabled_srcs p c i Hok Hin Hen) as [E | [E | E]]; subst i;
      destruct j;
      first [ reflexivity
            | exfalso; apply (f_equal bv_unsigned) in Heq;
              vm_compute in Heq; discriminate ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  WHAT THE THREE PLIC TRANSITIONS DO TO THE SLOTS.                   *)
  (* ------------------------------------------------------------------ *)

  (* ANYTHING THAT LEAVES SERVICE ALONE leaves the slots alone: a latch, a
     priority write, an enable write, a threshold write.  ONE PREMISE PER
     TRACKED PORT -- both suppliers ([PlicPlan.plic_write_outside_claim],
     [plic_latch_claimed]) are already universally quantified over the
     source, so a caller pays two instantiations and nothing else. *)
  Lemma plic_slots_stable (γ γ1 : uart_names) (p p' : plic_state) :
    p_claimed p' (uart_irq_id Uart0) = p_claimed p (uart_irq_id Uart0) ->
    p_claimed p' (uart_irq_id Uart1) = p_claimed p (uart_irq_id Uart1) ->
    plic_slots γ γ1 p -∗ plic_slots γ γ1 p'.
  Proof using .
    intros H0 H1. rewrite !plic_slots_eq H0 H1. iIntros "$".
  Qed.

  (* A CLAIM TAKES THE PAYLOAD OUT of the slot it marks in service, and the
     handout is keyed by the id the claim RETURNS -- which is what lets a
     caller spend it without any fact about [plic_best].  The handout is
     quantified over the PORT, so devintr's two arms each instantiate it at
     their own and the other arm's premise is refuted by 10 <> 12. *)
  Lemma plic_slots_claim (γ γ1 : uart_names) (p : plic_state) (c : nat) :
    plic_ok p ->
    uart_inited γ -∗ uart_inited γ1 -∗ plic_slots γ γ1 p -∗
      plic_slots γ γ1 (snd (plic_claim p c)) ∗
      (∀ j : uart_id,
         ⌜ fst (plic_claim p c) = Z_to_bv 32 (Z.of_N (uart_irq_id j)) ⌝ -∗
         plic_payload_uart j (plic_unames γ γ1 j)).
  Proof using .
    intros Hok. iIntros "#Hin0 #Hin1 H".
    rewrite plic_slots_eq. iDestruct "H" as "[H0 H1]".
    destruct (plic_best p c) as [i|] eqn:Hbest; last first.
    { (* nothing to serve: the state is unchanged and the id is 0 *)
      assert (Hsnd : snd (plic_claim p c) = p)
        by (unfold plic_claim; rewrite Hbest; reflexivity).
      assert (Hfst : fst (plic_claim p c) = Z_to_bv 32 0)
        by (unfold plic_claim; rewrite Hbest; reflexivity).
      rewrite Hsnd Hfst plic_slots_eq.
      iSplitL "H0 H1"; [iFrame "H0 H1"|].
      iIntros (j Hv). exfalso.
      apply (f_equal bv_unsigned) in Hv. destruct j; vm_compute in Hv;
        discriminate. }
    destruct (plic_claim_serves p c i Hok Hbest) as [Hb Ha].
    assert (Hfst : fst (plic_claim p c) = Z_to_bv 32 (Z.of_N i))
      by (unfold plic_claim; rewrite Hbest; reflexivity).
    destruct (decide (i = uart_irq_id Uart0)) as [Hi0|Hn0].
    - (* THE CONSOLE'S SOURCE: it was out of service, so the payload was in
         the slot; it is in service now, so the slot is empty and the
         payload leaves.  The other port's service bit is untouched. *)
      rewrite Hi0 in Hb Ha.
      assert (Hcl1 : p_claimed (snd (plic_claim p c)) (uart_irq_id Uart1)
                     = p_claimed p (uart_irq_id Uart1)).
      { apply plic_claim_other_claimed. rewrite Hbest Hi0.
        injection 1 as Hc. vm_compute in Hc. discriminate Hc. }
      iDestruct (plic_uslot_elim with "Hin0 H0") as "Hpay".
      iEval (rewrite Hb) in "Hpay".
      rewrite plic_slots_eq Ha Hcl1.
      iSplitR "Hpay".
      { iSplitR "H1"; [| iExact "H1"].
        iApply (plic_uslot_intro Uart0 γ true with "Hin0"). done. }
      iIntros (j Hv). destruct j; [iExact "Hpay"|].
      exfalso. rewrite Hfst Hi0 in Hv.
      apply (f_equal bv_unsigned) in Hv. vm_compute in Hv. discriminate.
    - destruct (decide (i = uart_irq_id Uart1)) as [Hi1|Hn1].
      + (* THE SECOND PORT'S SOURCE: the identical move at the other slot *)
        rewrite Hi1 in Hb Ha.
        assert (Hcl0 : p_claimed (snd (plic_claim p c)) (uart_irq_id Uart0)
                       = p_claimed p (uart_irq_id Uart0)).
        { apply plic_claim_other_claimed. rewrite Hbest Hi1.
          injection 1 as Hc. vm_compute in Hc. discriminate Hc. }
        iDestruct (plic_uslot_elim with "Hin1 H1") as "Hpay".
        iEval (rewrite Hb) in "Hpay".
        rewrite plic_slots_eq Ha Hcl0.
        iSplitR "Hpay".
        { iSplitL "H0"; [iExact "H0"|].
          iApply (plic_uslot_intro Uart1 γ1 true with "Hin1"). done. }
        iIntros (j Hv). destruct j; [| iExact "Hpay"].
        exfalso. rewrite Hfst Hi1 in Hv.
        apply (f_equal bv_unsigned) in Hv. vm_compute in Hv. discriminate.
      + (* some other source: BOTH UART service bits are untouched, and the
           id the claim returns is neither port's *)
        assert (Hcl0 : p_claimed (snd (plic_claim p c)) (uart_irq_id Uart0)
                       = p_claimed p (uart_irq_id Uart0)).
        { apply plic_claim_other_claimed. rewrite Hbest. congruence. }
        assert (Hcl1 : p_claimed (snd (plic_claim p c)) (uart_irq_id Uart1)
                       = p_claimed p (uart_irq_id Uart1)).
        { apply plic_claim_other_claimed. rewrite Hbest. congruence. }
        rewrite plic_slots_eq Hcl0 Hcl1.
        iSplitL "H0 H1"; [iFrame "H0 H1"|].
        iIntros (j Hv). exfalso.
        assert (Hij : i = uart_irq_id j).
        { apply (plic_claim_uart_ret_at p c i j Hok Hbest).
          rewrite -Hfst. exact Hv. }
        destruct j; [exact (Hn0 Hij) | exact (Hn1 Hij)].
  Qed.

  (* ...and a completion puts it back, at whichever port's source it names. *)
  Lemma plic_slots_complete (γ γ1 : uart_names) (p : plic_state) (i : N) :
    uart_inited γ -∗ uart_inited γ1 -∗ plic_slots γ γ1 p -∗
    (∀ j : uart_id, ⌜ i = uart_irq_id j ⌝ -∗
       plic_payload_uart j (plic_unames γ γ1 j)) -∗
    plic_slots γ γ1 (plic_complete p i).
  Proof using .
    iIntros "#Hin0 #Hin1 H Hpay".
    destruct (decide (i = uart_irq_id Uart0)) as [Hi0|Hn0].
    - subst i. rewrite plic_slots_eq. iDestruct "H" as "[H0 H1]".
      assert (Hf : p_claimed (plic_complete p (uart_irq_id Uart0))
                     (uart_irq_id Uart0) = false)
        by exact (plic_complete_claimed_in p (uart_irq_id Uart0)
                    (proj1 (uart_irq_id_range_at Uart0))
                    (proj2 (uart_irq_id_range_at Uart0))).
      assert (Hcl1 : p_claimed (plic_complete p (uart_irq_id Uart0))
                       (uart_irq_id Uart1) = p_claimed p (uart_irq_id Uart1))
        by (apply plic_complete_claimed_ne; vm_compute; discriminate).
      rewrite plic_slots_eq Hf Hcl1.
      iSplitR "H1"; [| iExact "H1"].
      iApply (plic_uslot_intro Uart0 γ false with "Hin0").
      iApply ("Hpay" $! Uart0). done.
    - destruct (decide (i = uart_irq_id Uart1)) as [Hi1|Hn1].
      + subst i. rewrite plic_slots_eq. iDestruct "H" as "[H0 H1]".
        assert (Hf : p_claimed (plic_complete p (uart_irq_id Uart1))
                       (uart_irq_id Uart1) = false)
          by exact (plic_complete_claimed_in p (uart_irq_id Uart1)
                      (proj1 (uart_irq_id_range_at Uart1))
                      (proj2 (uart_irq_id_range_at Uart1))).
        assert (Hcl0 : p_claimed (plic_complete p (uart_irq_id Uart1))
                         (uart_irq_id Uart0) = p_claimed p (uart_irq_id Uart0))
          by (apply plic_complete_claimed_ne; vm_compute; discriminate).
        rewrite plic_slots_eq Hf Hcl0.
        iSplitL "H0"; [iExact "H0"|].
        iApply (plic_uslot_intro Uart1 γ1 false with "Hin1").
        iApply ("Hpay" $! Uart1). done.
      + (* a completion of anything else leaves both service bits alone *)
        iApply (plic_slots_stable γ γ1 p (plic_complete p i)
                  (plic_complete_claimed_ne p i (uart_irq_id Uart0)
                     ltac:(congruence))
                  (plic_complete_claimed_ne p i (uart_irq_id Uart1)
                     ltac:(congruence))).
        iExact "H".
  Qed.

  (* THE PLIC INVARIANT: the fabric, the plan, and one slot per tracked
     source.  The boot chain founds the UART's slot in its pre-state and
     moves it to its post-state in ONE fupd ([uart_rx_tok_deposit]), which is
     also where the receive token is parked; every later PLIC access carries
     [uart_inited] and therefore never meets the pre-state again. *)
  Definition plic_inv_body (γ γ1 : uart_names) : iProp Σ :=
    (∃ p : plic_state, plic_frag p ∗ ⌜ plic_ok p ⌝ ∗ plic_slots γ γ1 p)%I.

  Definition disk_inv_body (γd : disk_names) : iProp Σ :=
    (∃ v : virtio_state,
       virtio_frag v ∗ virtio_proto γd v ∗ ⌜ virtio_isr_ok v ⌝)%I.

  Global Instance uart_inv_body_timeless i γ : Timeless (uart_inv_body i γ).
  Proof using . rewrite /uart_inv_body. apply _. Qed.
  Global Instance plic_slot_timeless γ γ1 p i : Timeless (plic_slot γ γ1 p i).
  Proof using .
    rewrite /plic_slot /plic_preinit /plic_inited /plic_payload
            /uart_preinit /uart_inited.
    destruct (uart_of_irq i) as [j|]; [destruct j|];
      destruct (p_claimed p i); apply _.
  Qed.
  Global Instance plic_slots_timeless γ γ1 p : Timeless (plic_slots γ γ1 p).
  Proof using . rewrite /plic_slots. apply _. Qed.
  Global Instance plic_inv_body_timeless γ γ1 : Timeless (plic_inv_body γ γ1).
  Proof using . rewrite /plic_inv_body. apply _. Qed.
  Global Instance disk_inv_body_timeless γd : Timeless (disk_inv_body γd).
  Proof using . rewrite /disk_inv_body. apply _. Qed.

  Definition uart_inv (i : uart_id) (γ : uart_names) : iProp Σ :=
    inv (uartN i) (uart_inv_body i γ).
  Definition plic_inv (γ γ1 : uart_names) : iProp Σ :=
    inv plicN (plic_inv_body γ γ1).
  Definition disk_inv (γd : disk_names) : iProp Σ := inv diskN (disk_inv_body γd).

  Global Instance uart_inv_persistent i γ : Persistent (uart_inv i γ).
  Proof using . rewrite /uart_inv. apply _. Qed.
  Global Instance plic_inv_persistent γ γ1 : Persistent (plic_inv γ γ1).
  Proof using . rewrite /plic_inv. apply _. Qed.
  Global Instance disk_inv_persistent γd : Persistent (disk_inv γd).
  Proof using . rewrite /disk_inv. apply _. Qed.

  Lemma uart_inv_alloc E i γ : uart_inv_body i γ ={E}=∗ uart_inv i γ.
  Proof using . iIntros "Hbody". rewrite /uart_inv. by iApply inv_alloc. Qed.
  Lemma plic_inv_alloc E γ γ1 : plic_inv_body γ γ1 ={E}=∗ plic_inv γ γ1.
  Proof using . iIntros "Hbody". rewrite /plic_inv. by iApply inv_alloc. Qed.

  (* ==================================================================== *)
  (*  §2b  THE WRITER'S VIEW SHIFT (app-echo.md, lane OUT-FUPD).           *)
  (*                                                                      *)
  (*  "All UART output needs a fupd to justify outputting."  This is that  *)
  (*  fupd's vocabulary.  Every store to a transmit register takes ONE     *)
  (*  LINK from its caller and hands back the link's payload; a writer of  *)
  (*  a run of bytes takes a CHAIN, one link per byte, because the         *)
  (*  transmit lock is per BYTE and another hart's bytes can land inside   *)
  (*  a message -- so a message-shaped shift is a CONSEQUENCE of the       *)
  (*  chain and never a substitute for it ([out_chain_shift], one way      *)
  (*  only).                                                              *)
  (*                                                                      *)
  (*  THE MASK IS FORCED, not chosen.  The store's device node runs at ⊤   *)
  (*  ([HartSMem.Wobl_dev1] opens (⊤,∅) around the node) and the leaf      *)
  (*  opens THIS PORT's invariant there ([ProofUart.v], the UART WRITE     *)
  (*  node), so the ghost step -- which is where the link is invoked --    *)
  (*  runs at exactly [⊤ ∖ ↑uartN i].  A writer's shift may therefore open *)
  (*  any invariant of its own, the observation invariant included, and    *)
  (*  may not open this port's.                                            *)
  (*                                                                      *)
  (*  WHAT THE LINK PROVES.  Given a REAL history prefix [o] (its reality  *)
  (*  witnessed by [obs_hist_lb_o]) at which the accepted bytes so far are *)
  (*  good, the writer produces a real history prefix -- its own byte's,   *)
  (*  or the one it was handed -- at which they are still good with its    *)
  (*  byte appended.  Moving the witness is what lets an echo answer an    *)
  (*  input byte it holds a bound on: see [uart_out_claim]'s paragraph.    *)
  (* ==================================================================== *)
  (* ...AT THE ERA [k] (lane CONS-IO milestone C).  The index is the link's
     SECOND argument and it is what a stale writer cannot forge: a process
     of a dead era holds links at ITS era's number, and the port invariant
     only ever meets links at [S gen_id]. *)
  (* ==================================================================== *)
  (*  THE LINK FAMILY, OVER EVENTS (redesign R2).                          *)
  (*                                                                       *)
  (*  ONE wand per boundary event, where there were four link shapes       *)
  (*  ([out_link], [in_append], [echo_link], [read_link]) over two          *)
  (*  resources at two witnesses.  The application supplies it and the      *)
  (*  kernel fires it with the port invariant open, having proved the       *)
  (*  event's pure premise ([ConsLog.cons_ev_ok]) from its own state.       *)
  (*                                                                       *)
  (*  ONE WITNESS.  Two claims carried one each, which is what made [Htx]   *)
  (*  need a second; the resource is one now and so is the witness it is    *)
  (*  held at.                                                              *)
  (*                                                                       *)
  (*  [out_link] and its chain below are NOT a fifth shape: they are this   *)
  (*  wand at [EvOut] with the two premises a plain writer never reads      *)
  (*  dropped, which is what keeps the write path's ~30 producers at the    *)
  (*  arity they were proved at.  [cons_link_of_out_link] is the bridge.    *)
  (* ==================================================================== *)
  (* THE HISTORY'S OWN INVARIANT COMES WITH IT.  Every firing site holds
     [cons_claim_at], which carries [ConsLog.cons_hist_ok] as a pure
     conjunct, so handing it over costs the kernel nothing -- and it is
     what lets the application read the OPEN ARM at a byte it did not see
     opened: between two bytes of one arm an unrelated writer's [EvOut] may
     have moved the history, and [arm_ok] is what survives that. *)
  Definition cons_link (i : uart_id) (k : nat) (ev : ConsLog.cons_ev)
      (Φ : iProp Σ) : iProp Σ :=
    (∀ (o : option (list mobs)) (H : LogEntryDefs.cons_hist),
       obs_hist_lb_o o -∗ chist_at i k (default [] o) H -∗
       ⌜ConsLog.cons_hist_ok H⌝ -∗ ⌜ConsLog.cons_ev_ok H ev⌝
       ={⊤ ∖ ↑uartN i}=∗
       ∃ o' : option (list mobs),
         obs_hist_lb_o o' ∗
         chist_at i k (default [] o') (ConsLog.cons_step H ev) ∗ Φ)%I.

  (* the single link's monotonicity: strengthening the payload.  The echo
     chain's bridges and the arm's two spend rules are all this lemma. *)
  Lemma cons_link_mono (i : uart_id) (k : nat) (ev : ConsLog.cons_ev)
      (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ cons_link i k ev Φ -∗ cons_link i k ev Φ'.
  Proof using .
    iIntros "HΦ H" (o Hh) "Hlb Hres %Hok %Hev".
    iMod ("H" $! o Hh with "Hlb Hres [//] [//]") as (o'') "(Hlb'' & Hres' & HP)".
    iModIntro. iExists o''. iFrame "Hlb'' Hres'". by iApply "HΦ".
  Qed.

  (* THE ARM'S RUN, stoppable exactly where [in_run] was: at each
     byte the holder chooses to close the arm or to emit the next one.  The
     [∧] is Iris's additive conjunction, as it is today -- the choice is the
     KERNEL's, and it is what lets one law cover an arm that emits fewer
     bytes than it planned. *)
  Fixpoint cons_run (k : nat) (bs : list (bv 8)) (Φ : iProp Σ) : iProp Σ :=
    match bs with
    | [] => cons_link Uart0 k ConsLog.EvClose Φ
    | b :: bs' =>
        cons_link Uart0 k ConsLog.EvClose Φ
        ∧ cons_link Uart0 k (ConsLog.EvByte b) (cons_run k bs' Φ)
    end%I.

  (* ==================================================================== *)
  (*  THE LICENCE: “any holder of the supply may move the resource by any  *)
  (*  event”.                                                              *)
  (*                                                                       *)
  (*  WHY IT EXISTS.  The kernel's GENERIC SUPPLY -- what an arbitrary,     *)
  (*  unverified process runs its syscalls on ([UexecExecInst.xv6_ssupply])*)
  (*  -- must pay for [write(2)] on the console, for consoleintr's shift   *)
  (*  and for [read(2)] on fd 0, and under the resource claim none of      *)
  (*  those is free: the whole point of making the claim a resource is     *)
  (*  that it can say WHO may move it.  So the supply carries a licence,   *)
  (*  the application decides what a licence costs ([App]'s [al_sup]:      *)
  (*  whoever holds the application's supply holds one), and the generic   *)
  (*  routes build their links out of it.  For the trivial application the *)
  (*  claim is [emp] and the licence is free; for a constraining one the   *)
  (*  licence is what its supply's TAINT arm pays for, which is exactly    *)
  (*  how KILL-ARM's credential works.                                     *)
  (*                                                                       *)
  (*  ONE LICENCE (redesign R2), where lane OUT-FUPD's [cons_licence] and   *)
  (*  lane CONS-IO's [cons_licence] were two names for it: one resource      *)
  (*  admits one law.                                                      *)
  (*                                                                       *)
  (*  QUANTIFIED OVER THE ERA (lane CONS-IO milestone C): the licence is   *)
  (*  the GENERIC process's payment and the generic process is any era's,  *)
  (*  so the one persistent resource covers them all.                      *)
  (*                                                                       *)
  (*  PERSISTENT BY CONSTRUCTION, so it rides every context and every      *)
  (*  bundle that carries the supply.                                      *)
  (* ==================================================================== *)
  Definition cons_licence : iProp Σ :=
    (□ ∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
         (ev : ConsLog.cons_ev),
        riscv_cons_res k h H ==∗ riscv_cons_res k h (ConsLog.cons_step H ev))%I.

  Global Instance cons_licence_persistent : Persistent cons_licence.
  Proof using . rewrite /cons_licence. apply _. Qed.

  (* ...AND THE TAINT BUYS IT (lane SUP-ONE, survey R1).  ONE LAW where
     there were a Coq-level premise on [SystemAdequacy.init_boot_of_sup]
     ([app_sup ⊢ cons_licence]) and a hand proof at [UInitBoot] -- both
     spelling "the application's kill price pays for a boundary event".
     It is [RiscvPtsto.app_iface]'s own field [ai_lic], read at the
     machine's ambient interface, so it needs NO record equation and
     holds at every altitude: the generic supply therefore carries the
     TAINT alone where it carried a licence beside it. *)
  Lemma cons_licence_of_taint : app_taint -∗ cons_licence.
  Proof using .
    rewrite /cons_licence /riscv_cons_res /app_taint.
    iIntros "Ht". iApply (ai_lic riscvF_app_iface with "Ht").
  Qed.

  (* THE LICENCE AT ONE ERA, FOR THE PROCESS EVENTS (seccomp design §9,
     §10.2, lane S0): the [∀ k] of [cons_licence] instantiated, at the two
     events a process steps the claim by ([ConsLog.wild_ev]) and under the
     console log's two validity premises, as [cons_link] supplies them.
     The general licence buys it at every era by ignoring all three
     premises; the WILD credential ([RiscvPtsto.riscv_wild], the
     interface's [ai_wild_lic]) buys it at its own.  The read payment
     below has its era-k form at this; the echo arm's [cons_run] does not
     (its events are the interrupt's). *)
  Definition cons_licence_at (k : nat) : iProp Σ :=
    (□ ∀ (h : list mobs) (H : LogEntryDefs.cons_hist)
         (ev : ConsLog.cons_ev),
        ⌜ConsLog.wild_ev ev⌝ -∗
        ⌜ConsLog.cons_hist_ok H⌝ -∗ ⌜ConsLog.cons_ev_ok H ev⌝ -∗
        riscv_cons_res k h H ==∗ riscv_cons_res k h (ConsLog.cons_step H ev))%I.

  Global Instance cons_licence_at_persistent k :
    Persistent (cons_licence_at k).
  Proof using . rewrite /cons_licence_at. apply _. Qed.

  Lemma cons_licence_at_of_licence (k : nat) :
    cons_licence -∗ cons_licence_at k.
  Proof using .
    rewrite /cons_licence /cons_licence_at.
    iIntros "#Hlic !>" (h H ev _ _ _). iApply ("Hlic" $! k h H ev).
  Qed.

  Lemma cons_licence_at_of_wild (k : nat) :
    riscv_wild k -∗ cons_licence_at k.
  Proof using .
    rewrite /cons_licence_at /riscv_cons_res /riscv_wild.
    iIntros "Hw". iApply (ai_wild_lic riscvF_app_iface k with "Hw").
  Qed.

  (* A PROCESS BYTE REACHING THE WIRE (redesign R2).  The name and the
     shape every writer threads are unchanged; what moves underneath is the
     port's ONE claim, by [EvOut].  Keeping the name is what leaves the
     dozen files that only PASS an [out_link] along untouched. *)
  Definition out_link (i : uart_id) (k : nat) (b : bv 8) (Φ : iProp Σ) : iProp Σ :=
    (∀ (o : option (list mobs)) (H : LogEntryDefs.cons_hist),
       obs_hist_lb_o o -∗ chist_at i k (default [] o) H
       ={⊤ ∖ ↑uartN i}=∗
       ∃ o' : option (list mobs),
         obs_hist_lb_o o' ∗
         chist_at i k (default [] o') (ConsLog.cons_step H (ConsLog.EvOut b))
         ∗ Φ)%I.

  (* [EvOut]'s premise is [True], so the two are the same wand with one
     argument fewer -- which is what keeps every writer's application site
     unchanged. *)
  (* [EvOut]'s premises are [True] and an invariant the writer does not
     read, so the two are the same wand with two arguments fewer -- which
     is what keeps every writer's application site unchanged. *)
  Lemma cons_link_of_out_link (i : uart_id) (k : nat) (b : bv 8) (Φ : iProp Σ) :
    out_link i k b Φ -∗ cons_link i k (ConsLog.EvOut b) Φ.
  Proof using . iIntros "H" (o Hh) "Hlb Hres _ _". by iApply ("H" with "Hlb Hres"). Qed.

  (* THE CHAIN: one link per byte of a run, the payload at the end.  A
     [Fixpoint] and not a big-op, so that [out_chain_app] -- the loop
     bridge every multi-byte writer's invariant is stated over -- is a
     structural induction and not a rewrite. *)
  Fixpoint out_chain (i : uart_id) (k : nat) (bs : list (bv 8))
      (Φ : iProp Σ) : iProp Σ :=
    match bs with
    | [] => Φ
    | b :: bs' => out_link i k b (out_chain i k bs' Φ)
    end%I.

  (* THE STOPPABLE CHAIN, for a writer that may return SHORT (consolewrite's
     copy fault, and hence filewrite's console arm and the syscall row above
     it).  [Q k] is the payload after [k] bytes, and the writer may cash it
     at any prefix -- an additive conjunction, so the choice is the
     writer's and the caller owes both sides. *)
  Fixpoint out_run (i : uart_id) (k : nat) (bs : list (bv 8))
      (Q : nat -> iProp Σ) : iProp Σ :=
    match bs with
    | [] => Q 0%nat
    | b :: bs' => Q 0%nat ∧ out_link i k b (out_run i k bs' (fun j => Q (S j)))
    end%I.

  (* ---- the laws ---- *)

  (* THE STEP.  The store's ghost step in one line: the claim at [u], the
     head link, and the accepted sequence grown by exactly that byte
     ([DevModel.uart_write_thr_acc]). *)



  (* the single link's monotonicity, [out_chain_mono]'s base case, split
     out because the input side's run bridge needs it on ONE link *)
  Lemma out_link_mono (i : uart_id) (k : nat) (b : bv 8) (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ out_link i k b Φ -∗ out_link i k b Φ'.
  Proof using .
    iIntros "HΦ H" (o acc) "Hlb Hres".
    iMod ("H" $! o acc with "Hlb Hres") as (o') "(Hlb' & Hres' & HP)".
    iModIntro. iExists o'. iFrame "Hlb' Hres'". by iApply "HΦ".
  Qed.

  Lemma out_chain_mono (i : uart_id) (k : nat) (bs : list (bv 8))
      (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ out_chain i k bs Φ -∗ out_chain i k bs Φ'.
  Proof using .
    iIntros "HΦ H". iInduction bs as [| b bs] "IH" forall (Φ Φ'); [by iApply "HΦ"|].
    cbn [out_chain]. iIntros (o acc) "Hlb Hres".
    iMod ("H" $! o acc with "Hlb Hres") as (o') "(Hlb' & Hres' & Hrest)".
    iModIntro. iExists o'. iFrame "Hlb' Hres'".
    iApply ("IH" with "HΦ Hrest").
  Qed.

  (* THE MESSAGE-SHAPED CONSEQUENCE, DERIVED ONE WAY ONLY.  A chain gives a
     shift for the whole run; a shift for the whole run does NOT give a
     chain, because tx_lock is taken per byte and another hart's bytes may
     be accepted between two of ours. *)


  (* ---- WHAT THE LICENCE PAYS, on the write path ---- *)

  (* the licence pays ONE link, at the witness it was handed: a licensed
     writer moves no witness, because it claims nothing about the input *)
  Lemma out_link_of_licence (k : nat) (b : bv 8) (Φ : iProp Σ) :
    cons_licence -∗ Φ -∗ out_link Uart0 k b Φ.
  Proof using .
    iIntros "#Hlic HΦ" (o Hh) "#Hlb Hres".
    iMod ("Hlic" $! k (default [] o) Hh (ConsLog.EvOut b) with "Hres") as "Hres".
    iModIntro. iExists o. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma out_chain_of_licence (k : nat) (bs : list (bv 8)) (Φ : iProp Σ) :
    cons_licence -∗ Φ -∗ out_chain Uart0 k bs Φ.
  Proof using .
    iIntros "#Hlic HΦ". iInduction bs as [| b bs] "IH"; [iExact "HΦ"|].
    cbn [out_chain]. iApply (out_link_of_licence k b with "Hlic").
    by iApply "IH".
  Qed.

  (* ...and the stoppable chain at the TRIVIAL payload, which is what the
     generic supply's [write(16)] row needs *)
  Lemma out_run_of_licence (k : nat) (bs : list (bv 8)) :
    cons_licence -∗ out_run Uart0 k bs (fun _ => True%I).
  Proof using .
    iIntros "#Hlic". iInduction bs as [| b bs] "IH"; [done|].
    cbn [out_run]. iSplit; [done|].
    iApply (out_link_of_licence k b with "Hlic"). by iApply "IH".
  Qed.

  (* THE EVENT LINK STRAIGHT OFF THE LICENCE (redesign R2).  The supply
     moves by ANY event, so a licensed holder owes nothing beyond the pure
     premise the kernel has already discharged -- which is why the link's
     [⌜cons_ev_ok H ev⌝] argument is dropped on the floor here. *)
  Lemma cons_link_of_licence (k : nat) (ev : ConsLog.cons_ev) (Φ : iProp Σ) :
    cons_licence -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using .
    iIntros "#Hlic HΦ" (o H) "#Hlb Hres _ _".
    iMod ("Hlic" $! k (default [] o) H ev with "Hres") as "Hres".
    iModIntro. iExists o. by iFrame "Hlb Hres HΦ".
  Qed.

  (* ...and hence the whole arm, stop or continue, at every byte *)
  Lemma cons_run_of_licence (k : nat) (bs : list (bv 8)) (Φ : iProp Σ) :
    cons_licence -∗ Φ -∗ cons_run k bs Φ.
  Proof using .
    iIntros "#Hlic HΦ". iInduction bs as [| b bs] "IH";
      cbn [cons_run].
    - by iApply (cons_link_of_licence with "Hlic").
    - iSplit.
      + by iApply (cons_link_of_licence with "Hlic").
      + iApply (cons_link_of_licence with "Hlic"). by iApply "IH".
  Qed.

  (* the trivial application's licence: its claim is [emp], so every event
     is a no-op on nothing *)
  Lemma cons_licence_triv : riscv_cons_res = cons_res_triv -> ⊢ cons_licence.
  Proof using .
    intros Hc. rewrite /cons_licence Hc /cons_res_triv.
    iIntros "!>" (????) "_". by iModIntro.
  Qed.

  (* the KERNEL'S PORT owes nothing: [chist_at Uart1] is [emp], so every
     link is discharged out of the payload and the witness never moves *)
  Lemma out_link_triv (i : uart_id) (k : nat) (b : bv 8) (Φ : iProp Σ) :
    i = Uart1 -> Φ -∗ out_link i k b Φ.
  Proof using .
    intros ->. iIntros "HΦ" (o acc) "#Hlb _". iModIntro.
    iExists o. by iFrame "Hlb HΦ".
  Qed.

  Lemma out_chain_triv (i : uart_id) (k : nat) (bs : list (bv 8)) (Φ : iProp Σ) :
    i = Uart1 -> Φ -∗ out_chain i k bs Φ.
  Proof using .
    intros ->. iIntros "HΦ".
    iInduction bs as [| b bs] "IH"; [iExact "HΦ"|].
    cbn [out_chain]. iApply (out_link_triv Uart1 k b _ eq_refl).
    by iApply "IH".
  Qed.

  (* the stoppable chain's two projections *)
  Lemma out_run_stop (i : uart_id) (k : nat) (bs : list (bv 8))
      (Q : nat -> iProp Σ) :
    out_run i k bs Q -∗ Q 0%nat.
  Proof using . destruct bs; [by iIntros "$"| by iIntros "[$ _]"]. Qed.

  Lemma out_run_chain (i : uart_id) (k : nat) (bs : list (bv 8))
      (Q : nat -> iProp Σ) :
    out_run i k bs Q -∗ out_chain i k bs (Q (length bs)).
  Proof using .
    iIntros "H". iInduction bs as [| b bs] "IH" forall (Q); [iExact "H"|].
    cbn [out_run out_chain length]. iDestruct "H" as "[_ H]".
    iApply (out_chain_mono i k [b] with "[] H").
    iIntros "H". iApply ("IH" $! (fun j => Q (S j)) with "H").
  Qed.

  (* ==================================================================== *)
  (*  THE INPUT SIDE'S THREE VIEW SHIFTS (app-echo.md, lane CONS-IO).       *)
  (*                                                                      *)
  (*  ONE APPLICATION FUPD PER ACCEPTED INPUT and ONE PER READ, at the      *)
  (*  mask an open port invariant leaves -- [out_link]'s exactly, and for   *)
  (*  the same reason: both fire with [uartN Uart0] open.                   *)
  (* ==================================================================== *)

  (* [in_append] lived here -- the old two-step run's second half, which
     filed [(h, c, cs)] and proved [h] strictly above every history already
     logged.  The run is one arm over one claim now, that order fact is
     proved ONCE at the arm's open, and the close is [ConsLog.EvClose]. *)
  (* THE ECHO'S BYTES, one [EvByte] each: [out_chain]'s twin on the echo
     path.  There is no [echo_link] beside it any more -- the echo's byte
     IS [cons_link ... (EvByte b)], and the order fact and the wire rider a
     separate link once carried are proved ONCE at the arm's open.  The
     [h] argument went with it: the chain says nothing about the history,
     only the arm does. *)
  Fixpoint echo_chain (k : nat) (bs : list (bv 8)) (Φ : iProp Σ) : iProp Σ :=
    match bs with
    | [] => Φ
    | b :: bs' => cons_link Uart0 k (ConsLog.EvByte b) (echo_chain k bs' Φ)
    end%I.

  Lemma echo_chain_mono (k : nat) (bs : list (bv 8)) (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ echo_chain k bs Φ -∗ echo_chain k bs Φ'.
  Proof using .
    iIntros "HΦ H". iInduction bs as [| b bs] "IH" forall (Φ Φ');
      [by iApply "HΦ" |].
    cbn [echo_chain]. iApply (cons_link_mono with "[HΦ] H").
    iIntros "H". iApply ("IH" with "HΦ H").
  Qed.

  (* THE ECHO RUN: the bytes FIRST, the log entry LAST, and the run is
     STOPPABLE at every prefix.

     WHY IT IS STOPPABLE, and why the log entry comes last.  The kill-line
     arm calls consputc once per erased glyph and the count is the ring's
     content, which the shift's caller cannot name when the shift fires: it
     is an [iLöb], not a fuel induction.  So the caller commits to an UPPER
     BOUND [bs] (the pending window's length, in hand under cons.lock), the
     loop walks the run one triple at a time, and whichever exit fires
     closes the log at exactly the bytes that went out -- [pre].  A chain
     that had to be spent whole could not be given to that loop, and a log
     entry written before the loop would have to name a count nobody knows.

     WHY THE BYTES COME FIRST is the application's side of the same coin:
     the log entry and the accepted byte can never move in ONE fupd (the
     accepted sequence grows in the THR store's own ghost step), so one of
     the two intermediates has to be expressible, and it is this one --
     after the store the wire carries exactly the transcript the log will
     account for, with the entry owed; the other order leaves the log
     claiming an echo the wire has not seen. *)
  (* [in_run] and [in_link] lived here.  [cons_run] above is the successor:
     the same stoppable shape, over events, with the arm's position in the
     kernel's own ghost instead of a [pre] argument. *)

  (* THE READ.  [ws] is every input this call CONSUMED -- delivered or
     swallowed -- and [ConsLog.read_ok] is the kernel's whole pure account
     of it: the bytes are logged echoes, the delivered histories increase,
     and every input the reader did NOT get in between was dropped without
     an echo or edited away.  The log itself does not move. *)
  (* ...and it IS [ConsLog.EvRead] (redesign R2).  There is no [read_link]
     beside [cons_link] any more: the reader's contract names the event. *)

  (* ---- the laws ---- *)

  (* [in_run_stop], [in_run_step], [in_run_app] and [in_run_full] lived
     here; [cons_run_stop], [cons_run_step] and [cons_run_full] replace
     them. *)

  (* lane CONS-IO C4's INPUT LICENCE lived here, and lane OUT-FUPD's output
     licence above: [cons_licence] is both (redesign R2), and
     [in_append_of_licence], [echo_link_of_licence] and [in_run_of_licence]
     are all [cons_link_of_licence] / [cons_run_of_licence] -- because all
     of them were events on one resource. *)

  (* ==================================================================== *)
  (*  WHAT ROW 5'S CONSOLE ARM CARRIES IN (lane CONS-IO, milestone B, B4). *)
  (*                                                                      *)
  (*  The process does not know how many bytes it will consume -- the ring *)
  (*  decides, and two of consoleread's exits pop one it never delivers -- *)
  (*  so it hands in ONE link quantified over the window and is told which *)
  (*  window it got in the receipt ([SpecFileread.console_receipt]).  The  *)
  (*  [forall] is INSIDE, so this is one linear resource spent at one [ws], *)
  (*  not a box: the boundary's [dl] moves exactly once per console read.  *)
  (* ==================================================================== *)
  Definition cons_read_pay (k : nat)
      (R : list (list mobs * bv 8) -> iProp Σ) : iProp Σ :=
    (∀ ws : list (list mobs * bv 8),
       cons_link Uart0 k (ConsLog.EvRead ws) (R ws))%I.

  (* the generic process's, out of the licence the supply already carries
     ([UexecExecInst.xv6_ssupply]'s fourth conjunct): it claims nothing
     about the window and is told nothing *)
  Lemma cons_read_pay_triv_at (k : nat) :
    cons_licence_at k -∗ cons_read_pay k (fun _ => True%I).
  Proof using .
    iIntros "#Hlic" (ws o H) "#Hlb Hres %Hok %Hev".
    iMod ("Hlic" $! (default [] o) H (ConsLog.EvRead ws)
            with "[] [//] [//] Hres") as "Hres".
    { iPureIntro. exact I. }
    iModIntro. iExists o. by iFrame "Hlb Hres".
  Qed.

  Lemma cons_read_pay_triv (k : nat) :
    cons_licence -∗ cons_read_pay k (fun _ => True%I).
  Proof using .
    iIntros "#Hlic". iApply (cons_read_pay_triv_at with "[]").
    by iApply cons_licence_at_of_licence.
  Qed.

  (* the trivial application's: the claim is [emp] and both halves are free *)

  (* ==================================================================== *)
  (*  THE TWO ACCESSORS: the shift and the read, fired WITH THE PORT        *)
  (*  INVARIANT OPEN.  [uart_inv_body] is timeless, so consoleintr and      *)
  (*  consoleread open it inside a plain [|={⊤}=>] without a machine step   *)
  (*  of their own; the mask below is what that opening leaves.            *)
  (* ==================================================================== *)

  (* [in_claim_append] and [in_claim_read] lived here: the two halves of
     the old input claim's contract.  Both are gone -- the port carries
     ONE claim over one console history now, and the events that move it
     are [uart_inv_cons_close] and [uart_inv_cons_read] below. *)

  (* ...AND THE SAME WITH THE PORT INVARIANT OPENED HERE, which is the form
     consoleintr uses: it holds [uart_inv Uart0 γ] (out of [dev_inv]) and
     nothing else, and [uart_inv_body] is TIMELESS, so the whole append is
     one [|={E}=>] with no machine step of its own -- the shape
     [ProofMain]'s PLIC deposit already uses. *)
  (* AT [⊤] AND NOT AT AN ARBITRARY MASK: [in_append]'s own fupd is at
     [⊤ ∖ ↑uartN Uart0] -- what the STORE leaf's open port invariant leaves,
     which is what fixes it -- so the only mask this accessor can be stated
     at is the one whose opening produces exactly that. *)
  (* ---- CLOSING THE ARM (redesign R2), with the port invariant opened
     here.  This is [uart_inv_append]'s successor, and the difference is
     where the entry comes from: today the caller passes [h], [c], [cs] as
     arguments; here they come off the ARM, so what is filed is what
     actually went out ([take j cs]) and the caller cannot name anything
     else.  The [cons_echo] side condition is on the PARTIAL echo, which is
     what [ConsLog]'s [EvClose] premise asks and what [log_ok] needs. ---- *)
  Lemma uart_inv_cons_close (γ : uart_names) (h : list mobs) (c : bv 8)
      (cs : list (bv 8)) (j : nat) (hg : option (list mobs))
      (L : list LogEntryDefs.log_entry) (Φ : iProp Σ) :
    ConsLog.cons_echo c (take j cs) ->
    (* ---- K3 (relax-d2): A STORE ARM SENDS ITS BYTE.  The arm whose PLAN
       is the single glyph [echo_of c] closes only after that glyph went
       out, so the entry it files is ECHOED.  The erase arms plan a run of
       [consputc_bs] triples and may stop early; their plan is never one
       byte ([ConsLog.cons_bs_join_not_single]), so they discharge this
       vacuously. ---- *)
    (cs = [ConsLog.echo_of c] -> j = 1%nat) ->
    (* ---- K1 (relax-d2, lane K1): WHICH KEYSTROKE THIS IS.  The byte is
       the input right after the one the log's mark names, or -- before
       anything has been logged -- the first the console ever saw, with
       uartinit's flush accounting for the rest ([k1_next]).  The two
       riders are what transport the flush witness forward: the byte's era
       stamp and its trace shape, both of which the receive column files
       beside its tag. ---- *)
    trace_shape h true ->
    obs_boots h = S gen_id ->
    k1_next hg h ->
    uart_inv Uart0 γ -∗ uart_log_hi γ (1/2) hg -∗ uart_logm γ (1/2) L -∗
    uart_arm γ (1/2) (Some (h, c, cs, j)) -∗
    cons_link Uart0 (S gen_id) ConsLog.EvClose Φ
    ={⊤}=∗ uart_log_hi γ (1/2) (Some h) ∗
           uart_logm γ (1/2) ((L ++ [(h, c, take j cs)])%list) ∗
           (* THE ORDER FACT the console's own [log_ok] push needs, and the
              arm is where it comes from: [arm_ok] carries it from the open,
              so the close hands it back without a second derivation. *)
           ⌜forall e, e ∈ L -> hist_ext (LogEntryDefs.le_hist e) h⌝ ∗
           uart_arm γ (1/2) None ∗ Φ.
  Proof using .
    intros Hecho Hk3 Hsh Hbh Hnext. iIntros "#Hinv Hhi Hlm Hmine HΨ".
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol & Hcons)".
    iDestruct "Hcons" as (o H)
      "(#Hlb & Hres & Hhi0 & Hdv & Hdc0 & Hau & Hlm0 & Harm & %Hacc0 & %Hok
        & %Hins)".
    rewrite /uart_logm. iDestruct (ghost_var_agree with "Hlm Hlm0") as %->.
    rewrite /uart_log_hi. iDestruct (ghost_var_agree with "Hhi Hhi0") as %Hagr.
    iDestruct (uart_arm_agree with "Hmine Harm") as %Harmeq0.
    assert (Harmeq : LogEntryDefs.ch_arm H = Some (h, c, cs, j))
      by (symmetry; exact Harmeq0).
    iEval (rewrite Harmeq) in "Harm".
    assert (Hev : ConsLog.cons_ev_ok H ConsLog.EvClose).
    { cbn [ConsLog.cons_ev_ok]. exists (h, c, cs, j).
      split; [exact Harmeq |]. split; [exact Hecho | exact Hk3]. }
    (* the arm's own order fact, which is also what places the log's
       entries strictly before [h] for K1's transport *)
    assert (Hext : forall e, e ∈ LogEntryDefs.ch_log H ->
                     hist_ext (LogEntryDefs.le_hist e) h).
    { destruct Hok as [_ Harmok]. rewrite Harmeq /= in Harmok.
      destruct Harmok as (_ & _ & _ & Hx & _). exact Hx. }
    (* K1 AT THE CLOSE: the entry this arm files is input [length L + 1 + f]. *)
    destruct (cons_log_ins_k1 (LogEntryDefs.ch_log H) hg h
                Hins Hagr Hsh Hbh Hext Hnext) as (fk & Hfl & Hcnt).
    iEval (rewrite Hagr) in "Hhi".
    iMod ("HΨ" $! o H with "Hlb Hres [//] [%]") as (o') "(#Hlb' & Hres' & HΦ)";
      [exact Hev |].
    iMod (ghost_var_update_halves (Some h) with "Hhi Hhi0") as "[Hhi Hhi0]".
    iMod (in_log_auth_snoc γ (LogEntryDefs.ch_log H) (h, c, take j cs)
            with "Hau") as "Hau".
    iMod (ghost_var_update_halves
            ((LogEntryDefs.ch_log H ++ [(h, c, take j cs)])%list)
            with "Hlm Hlm0") as "[Hlm Hlm0]".
    iMod (uart_arm_update γ (Some (h, c, cs, j)) (Some (h, c, cs, j)) None
            with "Hmine Harm") as "[Hmine Harm]".
    iMod ("Hclose" with "[Hu Hg Hcol Hres' Hhi0 Hdv Hdc0 Hau Hlm0 Harm]") as "_".
    { iNext. iExists u. iFrame "Hu Hg Hcol".
      iExists o', (ConsLog.cons_step H ConsLog.EvClose).
      rewrite /ConsLog.cons_step Harmeq.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      iFrame "Hlb' Hres' Hdv Hdc0 Hau Hlm0 Harm".
      rewrite /log_top (ConsLog.cl_top_snoc (LogEntryDefs.ch_log H)
                          (h, c, take j cs)) /=.
      iFrame "Hhi0". iPureIntro. split_and!; [exact Hacc0 | |].
      - pose proof (ConsLog.cons_hist_ok_step H ConsLog.EvClose Hok Hev) as Hok'.
        by rewrite /ConsLog.cons_step Harmeq in Hok'.
      - exact (cons_log_ins_snoc Uart0 (LogEntryDefs.ch_log H)
                 (h, c, take j cs) fk Hbh Hsh Hfl Hcnt). }
    iModIntro. iFrame "Hhi Hlm Hmine HΦ". iPureIntro. exact Hext.
  Qed.

  (* ==================================================================== *)
  (*  OPENING AN ARM (redesign R2), with the port invariant opened here.    *)
  (*                                                                       *)
  (*  This is where option A pays.  The kernel proves [EvOpen]'s premises   *)
  (*  from its OWN state: "no arm is in progress" off its half of           *)
  (*  [uart_arm], the order fact off the log's mark against the claim's     *)
  (*  half and [ConsLog.log_ok]'s chain, and the wire rider off             *)
  (*  [uart_out_auth] against the transmitted-prefix bound -- the same two  *)
  (*  derivations [store_ob_of_cons_byte] does today, moved to the arm's    *)
  (*  entry where they belong.                                             *)
  (*                                                                       *)
  (*  A SECOND ARM CANNOT OPEN while this one is in progress: the caller    *)
  (*  holds its half at [Some ...] until the close, so the agreement below  *)
  (*  fails for anyone else.  That is cons.lock's exclusion, stated.        *)
  (* ==================================================================== *)
  (* ==================== K2 (relax-d2) ================================= *)
  (*  WHAT A DROP ARM PAYS.  [ConsLog.cons_drop_ok] asks an arm that echoes *)
  (*  nothing to say WHY, and the four reasons split in two: three are      *)
  (*  facts about the byte ([c = 0], [c = ^P], [c] is an erase character),  *)
  (*  which the switch's own guard hands the caller for free; the fourth is *)
  (*  a FULL RING, which is a fact about the LOG and the DELIVERED COUNT    *)
  (*  and can only be stated by the holder of the two ghost halves the ring *)
  (*  carries.  So the payment is a disjunction: a pure side condition, or  *)
  (*  the two halves with the count fact between them.                      *)
  (*  [Q] IS THE CALLER'S RESIDUE, and it is what makes the two arms one    *)
  (*  premise: the accessor gives [Q] back, so a caller that lent the ring's *)
  (*  two halves names the RING itself as [Q] and hands in the wand that     *)
  (*  re-seals it, while a caller whose guard already decided the byte takes *)
  (*  [Q := emp] and hands in nothing.  Without it the return would be the   *)
  (*  disjunction again, and the lender could not tell which arm came back.  *)
  Definition cons_drop_pay (γ : uart_names) (c : bv 8) (cs : list (bv 8))
      (Q : iProp Σ) : iProp Σ :=
    (⌜cs = [] -> bv_unsigned c = 0%Z \/ bv_unsigned c = 16%Z
                 \/ ConsLog.cons_erase c = true⌝ ∗ Q
     ∨ ∃ (L : list LogEntryDefs.log_entry) (n : nat),
         ⌜(128 + n <= ConsLog.echoed_count L)%nat⌝ ∗
         uart_logm γ (1/2) L ∗ uart_dlcnt γ (1/2) n ∗
         (uart_logm γ (1/2) L -∗ uart_dlcnt γ (1/2) n -∗ Q))%I.
  (* ==================================================================== *)

  (* ===================================================================== *)
  (*  K1 IS PROVED ABOVE, at [cons_log_ins_k1]: the boundary's own log      *)
  (*  clause, the mark's agreement with the log's top, and the one fact     *)
  (*  the caller relays ([k1_next]).  Lane K2's placeholder lemma stood     *)
  (*  here.                                                                 *)
  (* ===================================================================== *)
  (* DELETED (lane K1): [k1_log_complete], the last [Admitted] in this file. *)
  (* ===================================================================== *)
  Lemma uart_inv_cons_open (γ : uart_names) (h : list mobs) (c : bv 8)
      (cs : list (bv 8)) (hg : option (list mobs)) (Q Φ : iProp Σ) :
    ohist_ext hg h ->
    obs_ends_in Uart0 h c ->
    ConsLog.cons_echo c cs ->
    (* ---- K1 (relax-d2, lane K1): WHICH KEYSTROKE THIS IS.  The byte is
       the input right after the one the log's mark [hg] names, or -- before
       anything has been logged -- the first the console ever saw, with
       uartinit's flush accounting for the rest ([k1_next]).  uartintr reads
       the disjunct off the PLIC payload's clause and the pop's two input
       numbers; the two riders transport the flush witness forward.
       Everything else K1 needs is inside: the boundary's own
       [cons_log_ins] turns the mark's input number into the log's LENGTH
       ([cons_log_ins_k1]). ---- *)
    trace_shape h true ->
    obs_boots h = S gen_id ->
    k1_next hg h ->
    uart_inv Uart0 γ -∗
    uart_out_lb γ (obs_wire Uart0 (open_seg h)) -∗
    uart_log_hi γ (1/2) hg -∗
    uart_arm γ (1/2) None -∗
    (* ---- K2 (relax-d2): the drop arm's reason, in the caller's own terms
       -- see [cons_drop_pay].  The residue [Q] comes back. ---- *)
    cons_drop_pay γ c cs Q -∗
    cons_link Uart0 (S gen_id) (ConsLog.EvOpen h c cs) Φ
    ={⊤}=∗ uart_log_hi γ (1/2) hg ∗
           uart_arm γ (1/2) (Some (h, c, cs, 0%nat)) ∗
           (* ---- K2 ---- *) Q ∗ Φ.
  Proof using .
    intros Hx Hends Hecho Hsh Hbh Hnext.
    iIntros "#Hinv #Hwlb Hhi Hmine Hk2 HΨ".
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol & Hcons)".
    iDestruct "Hcons" as (o H)
      "(#Hlb & Hres & Hhi0 & Hdv & Hdc0 & Hau & Hlm0 & Harm & %Hacc0 & %Hok
        & %Hins)".
    (* the log's mark: the caller's half names the claim's own top *)
    rewrite /uart_log_hi.
    iDestruct (ghost_var_agree with "Hhi Hhi0") as %Hagr.
    (* no arm is in progress: the caller's half says so *)
    iDestruct (uart_arm_agree with "Hmine Harm") as %Hnone0.
    assert (Hnone : LogEntryDefs.ch_arm H = None) by (symmetry; exact Hnone0).
    iEval (rewrite Hnone) in "Harm".
    (* the order fact, off the mark and the log's chain *)
    pose proof Hok as Hok2. destruct Hok2 as [Hlog _].
    assert (Hbelow : forall e, e ∈ LogEntryDefs.ch_log H ->
                       hist_ext (LogEntryDefs.le_hist e) h).
    { apply (ConsLog.cl_log_ok_last_ext _ h Hlog).
      intros el Hel. rewrite Hagr /log_top Hel /= in Hx. exact Hx. }
    (* the wire rider, off the transmitted-prefix bound *)
    iDestruct "Hg" as "(Hsent & Hout & Htx & Hdl)".
    iDestruct (uart_out_prefix with "Hout Hwlb") as %Hpre.
    assert (Hwire : obs_wire Uart0 (open_seg h)
                    `prefix_of` LogEntryDefs.ch_acc H).
    { rewrite Hacc0 /uart_acc. etrans; [exact Hpre |]. by apply prefix_app_r. }
    (* ---- K2: the drop arm's reason, read at the CLAIM's own log and
       delivered list.  The pure arm is already in the boundary's terms; the
       resource arm's two halves agree with the invariant's, which is what
       turns the caller's [L]/[n] into [ch_log H]/[length (ch_dl H)]. ---- *)
    iAssert (⌜cs = [] -> ConsLog.cons_drop_ok c (LogEntryDefs.ch_log H)
                                               (LogEntryDefs.ch_dl H)⌝ ∗ Q ∗
             uart_logm γ (1/2) (LogEntryDefs.ch_log H) ∗
             uart_dlcnt γ (1/2) (length (LogEntryDefs.ch_dl H)))%I
      with "[Hk2 Hlm0 Hdc0]" as "(%Hdrop & HQ & Hlm0 & Hdc0)".
    { rewrite /cons_drop_pay. iDestruct "Hk2" as "[[%Hp HQ] | Hq]".
      - iFrame "HQ Hlm0 Hdc0".
        iPureIntro. intro Hnil. rewrite /ConsLog.cons_drop_ok.
        destruct (Hp Hnil) as [H0 | [H16 | Her]];
          [by left | right; by left | right; right; by left].
      - iDestruct "Hq" as (L n) "(%Hcnt & Hlm & Hdc & Hback)".
        iDestruct (ghost_var_agree with "Hlm Hlm0") as %HLeq.
        iDestruct (ghost_var_agree with "Hdc Hdc0") as %Hneq.
        subst L. subst n.
        rewrite ConsLog.echoed_count_eq in Hcnt.
        iFrame "Hlm0 Hdc0". iSplitR.
        + iPureIntro. intros _. rewrite /ConsLog.cons_drop_ok.
          right; right; right. exact Hcnt.
        + iApply ("Hback" with "Hlm Hdc"). }
    (* ---- K1 (relax-d2, lane K1): the log holds every earlier input of
       this era but the [f] uartinit's flush lost, so the entry this arm
       will file is input number [length (ch_log H) + 1 + f]. ---- *)
    pose proof (cons_log_ins_k1 (LogEntryDefs.ch_log H) hg h
                  Hins Hagr Hsh Hbh Hbelow Hnext) as Hk1.
    assert (Hev : ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs)).
    { cbn [ConsLog.cons_ev_ok]. split_and!;
        [exact Hnone | exact Hends | exact Hecho | exact Hbelow | exact Hwire
        | exact Hk1 | exact Hdrop]. }
    (* fire the event *)
    iMod ("HΨ" $! o H with "Hlb Hres [//] [%]") as (o') "(#Hlb' & Hres' & HΦ)";
      [exact Hev |].
    (* and move both halves with the history *)
    iMod (uart_arm_update γ None None (Some (h, c, cs, 0%nat))
            with "Hmine Harm") as "[Hmine Harm]".
    iMod ("Hclose" with "[Hu Hsent Hout Htx Hdl Hcol Hres' Hhi0 Hdv Hdc0 Hau Hlm0 Harm]")
      as "_".
    { iNext. iExists u. iFrame "Hu Hcol". iSplitL "Hsent Hout Htx Hdl";
        [rewrite /uart_ghosts; iFrame "Hsent Hout Htx Hdl" |].
      iExists o', (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
      cbn [ConsLog.cons_step LogEntryDefs.ch_acc LogEntryDefs.ch_log
           LogEntryDefs.ch_dl LogEntryDefs.ch_arm].
      iFrame "Hlb' Hres' Hhi0 Hdv Hdc0 Hau Hlm0 Harm". iPureIntro. split_and!.
      - exact Hacc0.
      - exact (ConsLog.cons_hist_ok_step H (ConsLog.EvOpen h c cs) Hok Hev).
      - exact Hins. }
    iModIntro. by iFrame "Hhi Hmine HQ HΦ".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ADVANCING THE ARM IS NOW STEPPING THE HISTORY.                       *)
  (*                                                                      *)
  (*  [uart_inv_arm_set] stood here and is GONE, and its going is the      *)
  (*  design working rather than a regression: the arm is a FIELD of the   *)
  (*  history the port's claim is about ([cons_claim_at] ties the          *)
  (*  invariant's half to [ch_arm H]), so there is no such thing as moving *)
  (*  the arm without moving the history.  What used to be that lemma is   *)
  (*  [cons_link Uart0 k (EvOpen h c cs)] and its [EvClose] twin, whose    *)
  (*  pure premise [ConsLog.cons_ev_ok] carries "no arm is in progress"    *)
  (*  and whose step advances both halves with the history.                *)
  (*                                                                      *)
  (*  [uart_arm_agree] and [uart_arm_update] stay: they are what the event *)
  (*  firing uses on the two halves once the invariant is open.            *)
  (* ------------------------------------------------------------------ *)

  (* WHAT A WOULD-BE SECOND ARM MEETS is not a lemma of its own: it is
     [uart_arm_agree] above.  Whoever holds the payload's half knows the
     invariant's value, so while an arm is open the invariant's half is
     [Some ...] and [cons_ev_ok]'s [EvOpen] premise -- "no arm is in
     progress" -- cannot be discharged.  That is the exclusion cons.lock
     provides, stated where the fact lives, and it replaces the fraction
     arithmetic the application does today. *)


  (* ...AND THE SAME WITH THE PORT INVARIANT OPENED HERE, which is the form
     consoleread uses at its FINAL RELEASE: it holds [uart_inv Uart0 γ] (a
     premise of its contract, out of fileread's [dev_inv]) and the ring's
     two halves, and [uart_inv_body] is TIMELESS, so the fire is one
     [|={⊤}=>] with no machine step.  [uart_inv_append]'s twin, and stated
     at [⊤] for its reason. *)
  (* ...AND IT IS THE ONE MOVER OF THE DELIVERED COUNT (relax-d2, lane K2).
     The reader holds cons.lock -- so it holds the ring's half of
     [uart_dlcnt] -- and opens the port invariant here, so both halves are
     in hand and the pair advances with [ch_dl].  The agreement [n = length
     dv] comes back out because the ring's own clause is stated against the
     reader's cursor, not against the boundary's list. *)
  Lemma uart_inv_cons_read (γ : uart_names) (dv ws : list (list mobs * bv 8))
      (L : list LogEntryDefs.log_entry) (n : nat) (Φ : iProp Σ) :
    ConsLog.read_ok L dv ws ->
    uart_inv Uart0 γ -∗ uart_deliv γ (1/2) dv -∗ uart_logm γ (1/2) L -∗
    (* ---- K2 ---- *) uart_dlcnt γ (1/2) n -∗
    cons_link Uart0 (S gen_id) (ConsLog.EvRead ws) Φ
      ={⊤}=∗ uart_deliv γ (1/2) (dv ++ ws) ∗ uart_logm γ (1/2) L ∗
             (* ---- K2 ---- *)
             ⌜n = length dv⌝ ∗ uart_dlcnt γ (1/2) (n + length ws)%nat ∗ Φ.
  Proof using .
    intros Hread. iIntros "#Hinv Hdv Hlm Hdc HΨ".
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol & Hcons)".
    iDestruct "Hcons" as (o H)
      "(#Hlb & Hres & Hhi0 & Hdv0 & Hdc0 & Hau & Hlm0 & Harm & %Hacc0 & %Hok
        & %Hins)".
    rewrite /uart_logm. iDestruct (ghost_var_agree with "Hlm Hlm0") as %->.
    rewrite /uart_deliv. iDestruct (ghost_var_agree with "Hdv Hdv0") as %->.
    (* K2: the count's two halves agree, so the caller's [n] IS the
       delivered list's length, and the pair moves with it *)
    rewrite /uart_dlcnt. iDestruct (ghost_var_agree with "Hdc Hdc0") as %->.
    iMod ("HΨ" $! o H with "Hlb Hres [//] [%]") as (o') "(#Hlb' & Hres' & HΦ)".
    { cbn [ConsLog.cons_ev_ok]. exact Hread. }
    iMod (ghost_var_update_halves
            ((LogEntryDefs.ch_dl H ++ ws)%list) with "Hdv Hdv0") as "[Hdv Hdv0]".
    iMod (ghost_var_update_halves
            ((length (LogEntryDefs.ch_dl H) + length ws)%nat)
            with "Hdc Hdc0") as "[Hdc Hdc0]".
    iMod ("Hclose" with "[Hu Hg Hcol Hres' Hhi0 Hdv0 Hdc0 Hau Hlm0 Harm]") as "_".
    { iNext. iExists u. iFrame "Hu Hg Hcol".
      iExists o', (ConsLog.cons_step H (ConsLog.EvRead ws)).
      cbn [ConsLog.cons_step LogEntryDefs.ch_acc LogEntryDefs.ch_log
           LogEntryDefs.ch_dl LogEntryDefs.ch_arm].
      rewrite length_app.
      iFrame "Hlb' Hres' Hhi0 Hdv0 Hdc0 Hau Hlm0 Harm". iPureIntro.
      split_and!; [exact Hacc0 | | exact Hins].
      by apply (ConsLog.cons_hist_ok_step H (ConsLog.EvRead ws) Hok Hread). }
    iModIntro. iFrame "Hdv Hlm Hdc HΦ". by iPureIntro.
  Qed.

  (* THE COLUMN ACROSS THE ONE TRANSITION THAT GROWS THE ACCEPTED SEQUENCE.
     The receive half is untouched (a THR write is neither an FCR flush nor
     an MCR loop-back change) and the output claim moves by the caller's
     link.  This is the whole of what [WpSconfUartAccess]'s THR leaf has to
     do with the column. *)
  (* THE COLUMN ACROSS A TRANSMIT STORE.  It no longer carries the
     application's claim -- that moves by [cons_claim_at_store] at the same
     transition -- so this is the column's own carry-over and nothing
     else. *)
  Lemma uart_colE_store (iu : uart_id) (γ : uart_names) (u u' : uart_state)
      (b : bv 8) :
    u_rx u' = u_rx u ->
    uart_loopback u' = uart_loopback u ->
    u_wire u' = u_wire u ->
    u_out u' = u_out u ->
    u_recv u' = u_recv u ->
    uart_colE iu γ u -∗ uart_colE iu γ u'.
  Proof using .
    iIntros (Hrx Hlb Hw Ho Hrc) "H".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iExists hs, np, nk, hl, ht. iFrame "Ha Hk Hts Hht". iPureIntro.
    rewrite /uart_col_ok Hrx Hlb Hw Ho Hrc. exact Hok.
  Qed.

  (* ==================================================================== *)
  (*  THE STORE OBLIGATION (lane CONS-IO): what the THR write leaf spends.  *)
  (*                                                                      *)
  (*  [out_link] was the leaf's premise while a process's own [write(2)]   *)
  (*  was the only mover of the accepted sequence.  The console ECHO moves *)
  (*  it too, and what it needs AT THE STORE the arm supplies: which byte  *)
  (*  is next ([uart_arm]'s half) and the pure premise of [EvByte].        *)
  (*  Neither can be handed down from above -- the claim lives inside the  *)
  (*  port invariant, and only the store's own device node opens it.       *)
  (*                                                                      *)
  (*  So the leaf's premise is the GHOST STEP ITSELF, and the two writers  *)
  (*  build it their own way ([store_ob_of_out_link] for the plain one,    *)
  (*  [store_ob_of_cons_byte] for the echo).  ONE leaf, ONE uartputc_sync, *)
  (*  ONE consputc -- and [out_link]'s own surface is untouched, which is  *)
  (*  what keeps the write path (and [cons_out_chain]) exactly as landed.  *)
  (* ==================================================================== *)
  (* ---- THE TRANSMIT STORE MOVES THE PORT'S CLAIM (redesign R2).  The
     accepted bytes are a FIELD of the history now, so the store steps the
     history by [EvOut] where it used to move the output claim's [acc]
     argument.  Same place, same shape; one resource instead of two. ---- *)
  Lemma cons_claim_at_store (iu : uart_id) (γ : uart_names) (u u' : uart_state)
      (b : bv 8) (Φ : iProp Σ) :
    uart_acc u' = (uart_acc u ++ [b])%list ->
    cons_link iu (S gen_id) (ConsLog.EvOut b) Φ -∗ cons_claim_at iu γ u
    ={⊤ ∖ ↑uartN iu}=∗ cons_claim_at iu γ u' ∗ Φ.
  Proof using .
    iIntros (Hacc) "HΨ Hcl".
    iDestruct "Hcl" as (o H)
      "(Hlb & Hres & Hhi & Hdv & Hdc & Hau & Hlm & Harm & %Hacc0 & %Hok
        & %Hins)".
    iMod ("HΨ" $! o H with "Hlb Hres [//] [%]") as (o') "(Hlb' & Hres' & HΦ)".
    { exact I. }
    iModIntro. iFrame "HΦ".
    iExists o', (ConsLog.cons_step H (ConsLog.EvOut b)).
    cbn [ConsLog.cons_step LogEntryDefs.ch_acc LogEntryDefs.ch_log
         LogEntryDefs.ch_dl LogEntryDefs.ch_arm].
    iFrame "Hlb' Hres' Hhi Hdv Hdc Hau Hlm Harm". iPureIntro. split_and!.
    - by rewrite Hacc0 Hacc.
    - by apply (ConsLog.cons_hist_ok_step H (ConsLog.EvOut b) Hok I).
    - exact Hins.
  Qed.

  Definition store_ob (i : uart_id) (γ : uart_names) (b : bv 8)
      (Φ : iProp Σ) : iProp Σ :=
    (∀ u u' : uart_state,
       ⌜u_rx u' = u_rx u⌝ -∗ ⌜uart_loopback u' = uart_loopback u⌝ -∗
       ⌜u_wire u' = u_wire u⌝ -∗ ⌜u_out u' = u_out u⌝ -∗
       ⌜uart_acc u' = (uart_acc u ++ [b])%list⌝ -∗
       ⌜u_recv u' = u_recv u⌝ -∗
       uart_out_auth γ u -∗ uart_colE i γ u -∗ cons_claim_at i γ u
       ={⊤ ∖ ↑uartN i}=∗
       uart_out_auth γ u ∗ uart_colE i γ u' ∗ cons_claim_at i γ u' ∗ Φ)%I.

  (* the per-byte chain of them, [out_chain]'s twin one level down *)
  Fixpoint store_chain (i : uart_id) (γ : uart_names) (bs : list (bv 8))
      (Φ : iProp Σ) : iProp Σ :=
    match bs with
    | [] => Φ
    | b :: bs' => store_ob i γ b (store_chain i γ bs' Φ)
    end%I.

  Lemma store_ob_mono (i : uart_id) (γ : uart_names) (b : bv 8)
      (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ store_ob i γ b Φ -∗ store_ob i γ b Φ'.
  Proof using .
    iIntros "HΦ H" (u u') "%H1 %H2 %H3 %H4 %H5 %H6 Hout Hcol Hin".
    iMod ("H" $! u u' with "[//] [//] [//] [//] [//] [//] Hout Hcol Hin")
      as "(Hout & Hcol & Hin & HP)".
    iModIntro. iFrame "Hout Hcol Hin". by iApply "HΦ".
  Qed.

  Lemma store_chain_mono (i : uart_id) (γ : uart_names) (bs : list (bv 8))
      (Φ Φ' : iProp Σ) :
    (Φ -∗ Φ') -∗ store_chain i γ bs Φ -∗ store_chain i γ bs Φ'.
  Proof using .
    iIntros "HΦ H". iInduction bs as [| b bs] "IH" forall (Φ Φ').
    - cbn [store_chain]. by iApply "HΦ".
    - cbn [store_chain]. iApply (store_ob_mono with "[HΦ] H").
      iIntros "H". by iApply ("IH" with "HΦ H").
  Qed.


  (* THE PLAIN WRITER'S: the port's claim steps by [EvOut] and the column
     carries over.  One link where there were two resources to move. *)
  Lemma store_ob_of_cons_link (i : uart_id) (γ : uart_names) (b : bv 8)
      (Φ : iProp Σ) : cons_link i (S gen_id) (ConsLog.EvOut b) Φ -∗ store_ob i γ b Φ.
  Proof using .
    iIntros "HΨ" (u u') "%H1 %H2 %H3 %H4 %H5 %H6 Hout Hcol Hin".
    iMod (cons_claim_at_store i γ u u' b Φ H5 with "HΨ Hin") as "[Hin HΦ]".
    iDestruct (uart_colE_store i γ u u' b H1 H2 H3 H4 H6 with "Hcol") as "Hcol".
    iModIntro. iFrame "Hout Hcol Hin HΦ".
  Qed.

  (* ...and the name every writer's leaf names, kept: [EvOut]'s premise is
     [True], so the two are one wand with an argument fewer. *)
  Lemma store_ob_of_out_link (i : uart_id) (γ : uart_names) (b : bv 8)
      (Φ : iProp Σ) : out_link i (S gen_id) b Φ -∗ store_ob i γ b Φ.
  Proof using .
    iIntros "H". iApply store_ob_of_cons_link. by iApply cons_link_of_out_link.
  Qed.

  Lemma store_chain_of_out_chain (i : uart_id) (γ : uart_names)
      (bs : list (bv 8)) (Φ : iProp Σ) :
    out_chain i (S gen_id) bs Φ -∗ store_chain i γ bs Φ.
  Proof using .
    iIntros "H". iInduction bs as [| b bs] "IH" forall (Φ); [by iFrame |].
    cbn [out_chain store_chain].
    iApply store_ob_of_cons_link. iApply cons_link_of_out_link.
    iApply (out_link_mono with "[] H"). iIntros "H". by iApply "IH".
  Qed.

  (* THE ECHO'S.  The order fact comes out of the log's mark against the
     claim's own half plus [ConsLog.log_ok]'s chain -- the same three lines
     as [in_claim_append] -- and the wire fact out of the byte's RIDER
     against the transmitted-prefix authority, plus [DevModel.uart_acc]'s
     definition ([u_out] is a prefix of the accepted sequence).  The mark is
     LENT, not moved: the append that moves it fires once per byte, at the
     arm's exit, and not per echoed byte. *)
  (* THE ECHO'S STORE (redesign R2).  The order fact and the wire rider it
     used to prove here are proved ONCE at the arm's open now, so what is
     left is the byte itself: the arm says which byte is next, the event
     steps the history, and both halves of the arm advance with it. *)
  Lemma store_ob_of_cons_byte (γ : uart_names) (b : bv 8) (h : list mobs)
      (c : bv 8) (cs : list (bv 8)) (j : nat) (Φ : iProp Σ) :
    cs !! j = Some b ->
    uart_arm γ (1/2) (Some (h, c, cs, j)) -∗
    cons_link Uart0 (S gen_id) (ConsLog.EvByte b) Φ -∗
    store_ob Uart0 γ b (uart_arm γ (1/2) (Some (h, c, cs, S j)) ∗ Φ).
  Proof using .
    intros Hlk. iIntros "Hmine HΨ" (u u') "%H1 %H2 %H3 %H4 %H5 %H6 Hout Hcol Hin".
    iDestruct "Hin" as (o H)
      "(#Hlb & Hres & Hhi0 & Hdv & Hdc0 & Hau & Hlm0 & Harm & %Hacc0 & %Hok
        & %Hins)".
    iDestruct (uart_arm_agree with "Hmine Harm") as %Harmeq0.
    assert (Harmeq : LogEntryDefs.ch_arm H = Some (h, c, cs, j))
      by (symmetry; exact Harmeq0).
    assert (Hev : ConsLog.cons_ev_ok H (ConsLog.EvByte b)).
    { cbn [ConsLog.cons_ev_ok]. exists (h, c, cs, j).
      split; [exact Harmeq | exact Hlk]. }
    iEval (rewrite Harmeq) in "Harm".
    iMod ("HΨ" $! o H with "Hlb Hres [//] [%]") as (o') "(#Hlb' & Hres' & HΦ)";
      [exact Hev |].
    iMod (uart_arm_update γ (Some (h, c, cs, j)) (Some (h, c, cs, j))
            (Some (h, c, cs, S j)) with "Hmine Harm") as "[Hmine Harm]".
    iDestruct (uart_colE_store Uart0 γ u u' b H1 H2 H3 H4 H6 with "Hcol") as "Hcol".
    iModIntro. iFrame "Hout Hcol HΦ Hmine".
    iExists o', (ConsLog.cons_step H (ConsLog.EvByte b)).
    rewrite /ConsLog.cons_step Harmeq.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    iFrame "Hlb' Hres' Hhi0 Hdv Hdc0 Hau Hlm0 Harm". iPureIntro. split_and!.
    - by rewrite Hacc0 H5.
    - pose proof (ConsLog.cons_hist_ok_step H (ConsLog.EvByte b) Hok Hev) as Hok'.
      by rewrite /ConsLog.cons_step Harmeq in Hok'.
    - exact Hins.
  Qed.

  (* THE ECHO'S CHAIN.  The arm's counter advances with the bytes, so the
     premise is per-byte: the n-th byte of what goes out is the (j+n)-th of
     the echo the arm chose.  The log's mark is not lent here any more --
     the order fact it justified is proved at the open. *)
  Lemma store_chain_of_echo_chain (γ : uart_names) (h : list mobs) (c : bv 8)
      (cs : list (bv 8)) (j : nat) (bs : list (bv 8)) (Φ : iProp Σ) :
    (forall (n : nat) (b : bv 8), bs !! n = Some b -> cs !! (j + n)%nat = Some b) ->
    uart_arm γ (1/2) (Some (h, c, cs, j)) -∗
    echo_chain (S gen_id) bs Φ -∗
    store_chain Uart0 γ bs
      (uart_arm γ (1/2) (Some (h, c, cs, (j + length bs)%nat)) ∗ Φ).
  Proof using .
    iIntros (Hbs) "Harm H".
    iInduction bs as [| b bs] "IH" forall (j Hbs Φ).
    - cbn [store_chain length]. rewrite Nat.add_0_r. iFrame "Harm H".
    - cbn [echo_chain store_chain length].
      assert (Hb : cs !! j = Some b).
      { pose proof (Hbs 0%nat b eq_refl) as Hb0. by rewrite Nat.add_0_r in Hb0. }
      iDestruct (store_ob_of_cons_byte γ b h c cs j
                   (echo_chain (S gen_id) bs Φ) Hb with "Harm H") as "H".
      iApply (store_ob_mono with "[] H"). iIntros "[Harm H]".
      iDestruct ("IH" $! (S j) with "[%] Harm H") as "H".
      { intros n b' Hn.
        replace (S j + n)%nat with (j + S n)%nat by lia.
        exact (Hbs (S n) b' Hn). }
      iApply (store_chain_mono with "[] H"). iIntros "[Harm $]".
      by replace (j + S (length bs))%nat with (S j + length bs)%nat by lia.
  Qed.

  (* ...and the shape the arms actually hold it in: the plan SPLIT at the
     position the arm has reached, which is what a loop that emits one
     triple at a time carries. *)
  Lemma store_chain_of_echo_split (γ : uart_names) (h : list mobs) (c : bv 8)
      (pre bs post : list (bv 8)) (Φ : iProp Σ) :
    uart_arm γ (1/2) (Some (h, c, (pre ++ bs ++ post)%list, length pre)) -∗
    echo_chain (S gen_id) bs Φ -∗
    store_chain Uart0 γ bs
      (uart_arm γ (1/2) (Some (h, c, (pre ++ bs ++ post)%list,
                               (length pre + length bs)%nat)) ∗ Φ).
  Proof using .
    iIntros "Harm H".
    iApply (store_chain_of_echo_chain γ h c _ (length pre) bs Φ
              with "Harm H").
    intros n b Hn.
    rewrite lookup_app_r; [| lia].
    replace (length pre + n - length pre)%nat with n by lia.
    by rewrite lookup_app_l; [| by eapply lookup_lt_Some].
  Qed.

  (* THE WHOLE ARM, run to the end: a holder that spends every byte of its
     plan is left with the licence to close.  [in_run_full]'s successor. *)
  Lemma cons_run_full (bs : list (bv 8)) (Φ : iProp Σ) :
    cons_run (S gen_id) bs Φ -∗
    echo_chain (S gen_id) bs (cons_link Uart0 (S gen_id) ConsLog.EvClose Φ).
  Proof using .
    iIntros "H". iInduction bs as [| b bs] "IH" forall (Φ);
      cbn [cons_run echo_chain]; [iExact "H" |].
    iDestruct "H" as "[_ H]".
    iApply (cons_link_mono with "[] H"). iIntros "H". by iApply "IH".
  Qed.

  (* ...and ONE STEP of it, for a loop that does not know how far it will
     go: spend the head, keep the choice at the tail. *)
  Lemma cons_run_step (bs cs : list (bv 8)) (Φ : iProp Σ) :
    cons_run (S gen_id) (bs ++ cs)%list Φ -∗
    echo_chain (S gen_id) bs (cons_run (S gen_id) cs Φ).
  Proof using .
    iIntros "H". iInduction bs as [| b bs] "IH";
      cbn [echo_chain]; [iExact "H" |].
    rewrite -app_comm_cons. cbn [cons_run].
    iDestruct "H" as "[_ H]".
    iApply (cons_link_mono with "[] H"). iIntros "H". by iApply "IH".
  Qed.

  (* the arm may always STOP where it stands *)
  Lemma cons_run_stop (bs : list (bv 8)) (Φ : iProp Σ) :
    cons_run (S gen_id) bs Φ -∗ cons_link Uart0 (S gen_id) ConsLog.EvClose Φ.
  Proof using .
    iIntros "H". destruct bs as [| b bs]; [iExact "H" |].
    cbn [cons_run]. by iDestruct "H" as "[H _]".
  Qed.

  Lemma disk_inv_alloc E γd : disk_inv_body γd ={E}=∗ disk_inv γd.
  Proof using . iIntros "Hbody". rewrite /disk_inv. by iApply inv_alloc. Qed.

  (* THE PERMIT CHANNEL IS ERA-LOCAL, so the bundle that carries it names the
     era's generation -- and it names it as the AMBIENT [gen_id], not as an
     explicit argument, so every client spec in the tree stays textually
     unchanged (a [GenId] instance is in scope wherever [dev_inv] is, and it
     is the same one for every thread of an era: they are all spawned at the
     generation [power_boot_res] is handed out at).  The section's own [GEN]
     is that instance -- [dev_inv] simply starts using it. *)

  (* The device invariant as a client-facing, duplicable proposition: the
     BUNDLE of the three per-device invariants.  Same name and same arguments
     as before the split, so every client spec in the tree is unchanged --
     what changed is only that a proof holding it destructs the bundle and
     opens the one sub-invariant it needs.  The device state is shared between
     the device threads and every CPU that touches UART/PLIC/virtio MMIO, so
     NO proof may hold [uart_frag]/[plic_frag]/[virtio_frag] across a step: a
     client threads [dev_inv] and borrows the fragment by opening the relevant
     half around the access. *)
  (* THE PLIC CONJUNCT IS ∃-PACKED OVER THE SECOND PORT'S NAMES, and that is
     what keeps this bundle at ARITY 2 now that [plic_inv] is keyed by both
     ports.  [dev_inv] is the CONSOLE bundle -- ~140 specs name it and none
     of them has any business naming [Uart1]'s ghosts -- so the bundle says
     only "the one PLIC invariant exists", which is all a client borrowing
     [plic_frag] needs.  Anything that must name the second port's names --
     the claim's payload, the completion's park, the second slot's deposit --
     takes the BARE [plic_inv γ γ1] as its own premise instead
     (SpecPlicinit/SpecPlicClaim/SpecPlicComplete/SpecDevintr), exactly as
     "new specs take only the invariant(s) they use" says. *)
  Definition dev_inv (γ : uart_names) (γd : disk_names) : iProp Σ :=
    (uart_inv Uart0 γ ∗ (∃ γ1 : uart_names, plic_inv γ γ1) ∗
     disk_inv γd ∗ perm_inv gen_id (dn_perm γd))%I.

  Global Instance dev_inv_persistent γ γd : Persistent (dev_inv γ γd).
  Proof using . rewrite /dev_inv. apply _. Qed.

  (* the three projections out of the bundle.  A leaf that borrows the fabric
     takes [dev_inv] (unchanged statement) and projects the ONE half it
     touches; the projections are wands out of a persistent premise, so a
     leaf holding [dev_inv] in its intuitionistic context keeps it. *)
  Lemma dev_inv_uart γ γd : dev_inv γ γd -∗ uart_inv Uart0 γ.
  Proof using . iIntros "(#H & _ & _ & _)". iExact "H". Qed.
  Lemma dev_inv_plic γ γd : dev_inv γ γd -∗ ∃ γ1 : uart_names, plic_inv γ γ1.
  Proof using . iIntros "(_ & #H & _ & _)". iExact "H". Qed.
  (* ...and the way IN, for the one construction site that knows [γ1]. *)
  Lemma dev_inv_intro γ γ1 γd :
    uart_inv Uart0 γ -∗ plic_inv γ γ1 -∗ disk_inv γd -∗
    perm_inv gen_id (dn_perm γd) -∗ dev_inv γ γd.
  Proof using .
    iIntros "#Hu #Hp #Hd #Hq". rewrite /dev_inv.
    iFrame "Hu Hd Hq". iExists γ1. iExact "Hp".
  Qed.
  Lemma dev_inv_disk γ γd : dev_inv γ γd -∗ disk_inv γd.
  Proof using . iIntros "(_ & _ & #H & _)". iExact "H". Qed.
  (* THE CRASH-PERMIT CHANNEL rides the SAME bundle (PermInv.v), which is why
     no client spec statement changed when it landed: every driver proof that
     already threads [dev_inv] can open [permN] to deposit its permit at
     enqueue and to collect its receipt after the wake. *)
  Lemma dev_inv_perm γ γd : dev_inv γ γd -∗ perm_inv gen_id (dn_perm γd).
  Proof using . iIntros "(_ & _ & _ & #H)". iExact "H". Qed.

  (* ... and the bundle allocation, at the EXISTING signature: the old
     ∃-triple body is split into the three per-device bodies. *)
  (* The permit body is a SEPARATE premise rather than a conjunct of
     [dev_inv_body]: that body carries a [Timeless] instance (it is what the
     three timeless per-device invariants are carved out of), and
     [perm_inv_body] is deliberately NOT timeless. *)
  (* THE ALLOCATION HANDS THE RECEIVE TOKEN OUT.  BOTH ports' slots are
     founded in their PRE-STATE ([uart_preinit]) and the disk's in its
     post-state with an [emp] payload, so each port's token itself goes to
     the boot chain, which threads it through uartinit's FCR flush and
     deposits it afterwards ([uart_rx_tok_deposit]).  The console's token
     travels as an argument here (it is also consoleinit's); the second
     port's never enters this lemma -- only its one-shot does.

     [γ1] IS AN ARGUMENT AND [plic_inv γ γ1] COMES BACK OUT, because the
     bundle ∃-packs it: the boot chain knows which names it minted and has
     to keep the concrete invariant for main's second deposit and for
     plic_claim/plic_complete. *)
  Lemma dev_inv_alloc E γ γ1 γd :
    dev_inv_body γ γd -∗ uart_preinit γ1 -∗
    perm_inv_body gen_id (dn_perm γd) -∗
    uart_rx_tok γ 0 None ={E}=∗
    dev_inv γ γd ∗ plic_inv γ γ1 ∗ uart_rx_tok γ 0 None.
  Proof using .
    iIntros "Hbody Hpre1 Hperm Htok". rewrite /dev_inv_body.
    iDestruct "Hbody" as (u p v)
      "(Hu & Hp & Hv & Hg & Hcol & Hcons & Hpre & Hproto & %Hpok & %Hvok)".
    iMod (uart_inv_alloc E Uart0 γ with "[Hu Hg Hcol Hcons]") as "#Huinv".
    { iExists u. iFrame "Hu Hg Hcol Hcons". }
    iMod (plic_inv_alloc E γ γ1 with "[Hp Hpre Hpre1]") as "#Hpinv".
    { iExists p. iFrame "Hp". iSplitR; [iPureIntro; exact Hpok|].
      rewrite plic_slots_eq.
      iSplitL "Hpre"; rewrite /plic_uslot; iLeft;
        [iExact "Hpre" | iExact "Hpre1"]. }
    iMod (disk_inv_alloc E γd with "[Hv Hproto]") as "#Hdinv".
    { iExists v. iFrame "Hv Hproto". iPureIntro. exact Hvok. }
    iMod (perm_inv_alloc E gen_id (dn_perm γd) with "Hperm") as "#Hqinv".
    iModIntro. rewrite /dev_inv.
    iSplitR "Htok".
    - iSplitR; [iExact "Huinv" |].
      iSplitR; [iExists γ1; iExact "Hpinv" |].
      iSplitR; [iExact "Hdinv" | iExact "Hqinv"].
    - iFrame "Hpinv Htok".
  Qed.

  (* THE DEPOSIT: the boot chain parks a port's token, in the ONE fupd that
     runs that port's slot one-shot -- out of the pre-state, into the
     post-state with the payload.  ONE LEMMA FOR BOTH PORTS ([j] selects the
     names): main runs it at [Uart0] between consoleinit and plicinit and at
     [Uart1] after uartinitone's FCR flush, and the [uart_inited] each mints
     is what every later PLIC access at that port carries, so no one meets a
     pre-state again.

     THE SLOT'S [if] IS THE ONE PLACE the pre-state's silence about [p] is
     felt.  The pre-state says nothing at all about the PLIC state -- no
     "the port is enabled nowhere" clause -- so [p_claimed p (uart_irq_id j)
     = false] is not available here, and the (unreachable: nothing has
     enabled the port's source yet, so no claim can have taken it)
     in-service branch parks [emp] and drops the token.  Nothing downstream
     is weakened by that: a claim hands out the payload only from an
     OUT-of-service slot, and this branch leaves the slot exactly as an
     in-service one must look. *)
  (* ...AND THE ECHO WINDOW TOKEN GOES IN WITH THEM (lane CONS-IO milestone
     F).  It is the era's, minted by the application's power-on step and
     carried here by the boot ([RiscvAdequacy.power_boot_res]); at [Uart1]
     it is [emp] and the second port's deposit pays nothing. *)
  Lemma plic_uslot_deposit (iu : uart_id) (γu : uart_names) (cl : bool)
      (k : nat) (hl hh hg : option (list mobs)) :
    ohist_le hh hl ->
    (* ...AND THE LOG'S MARK (lane CONS-IO), on the ring mark's mould -- at
       the CONSOLE port an EQUALITY (relax-d2, lane K1): parking the token
       is claiming that everything popped has been filed. *)
    uart_log_at iu hg hl ->
    plic_uslot iu γu cl -∗ uart_rx_tok γu k hl -∗ uart_rx_hi γu (1/2) hh -∗
    uart_log_hi γu (1/2) hg -∗ uart_arm γu (1/2) None
      ==∗ uart_inited γu ∗ plic_uslot iu γu cl.
  Proof using .
    iIntros (Hle Hleg) "Hu Htok Hhi Hlg Harm".
    iDestruct (plic_uslot_cases with "Hu") as "[Hpre | [#Hin Hrest]]".
    - iMod (uart_preinit_fire with "Hpre") as "#Hin".
      iModIntro. iSplitR; [iExact "Hin" |].
      iApply (plic_uslot_intro iu γu cl with "Hin").
      destruct cl; [done|].
      rewrite /plic_payload_uart /uart_rx_writer.
      iExists k, hl. iFrame "Htok".
      iSplitL "Hhi"; [iExists hh; iFrame "Hhi"; iPureIntro; exact Hle |].
      iSplitL "Hlg"; [iExists hg; iFrame "Hlg"; iPureIntro; exact Hleg |].
      iExact "Harm".
    - (* the deposit has already run: the slot's own payload is the token's
         partner, so this one is spare and is simply dropped *)
      iModIntro. iSplitR; [iExact "Hin" |].
      iApply (plic_uslot_intro iu γu cl with "Hin"). iExact "Hrest".
  Qed.

  Lemma uart_rx_tok_deposit E (γ γ1 : uart_names) (j : uart_id)
      (k : nat) (hl hh hg : option (list mobs)) :
    ↑plicN ⊆ E ->
    ohist_le hh hl ->
    uart_log_at j hg hl ->
    plic_inv γ γ1 -∗ uart_rx_tok (plic_unames γ γ1 j) k hl -∗
    uart_rx_hi (plic_unames γ γ1 j) (1/2) hh -∗
    uart_log_hi (plic_unames γ γ1 j) (1/2) hg -∗
    (* ...the arm's half, at [None] (redesign R2)... *)
    uart_arm (plic_unames γ γ1 j) (1/2) None
      ={E}=∗ uart_inited (plic_unames γ γ1 j).
  Proof using .
    iIntros (Hmask Hle Hleg) "#Hpinv Htok Hhi Hlg Harm".
    iInv "Hpinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (p) "(Hp & %Hpok & Hslots)".
    rewrite plic_slots_eq.
    destruct j; cbn [plic_unames];
      [ iDestruct "Hslots" as "[Hu Hw]" | iDestruct "Hslots" as "[Hw Hu]" ];
      (iMod (plic_uslot_deposit _ _ _ k hl hh hg Hle Hleg
               with "Hu Htok Hhi Hlg Harm")
         as "[#Hin Hu]";
       iMod ("Hclose" with "[Hp Hu Hw]") as "_";
       [ iNext; iExists p; iFrame "Hp"; iSplitR; [iPureIntro; exact Hpok|];
         rewrite plic_slots_eq; iFrame "Hu Hw"
       | iModIntro; iExact "Hin" ]).
  Qed.

  (* Allocate all four UART ghosts from an initial device state.  Hands back
     the invariant's halves (as [uart_inv_body]'s ghost conjuncts) together
     with the caller's own resources: the exclusive transmitter, the opening
     accepted-trace bound, and the caller's HALF of the DLAB agreement, at
     whatever the power-on DLAB happens to be.
     NOTE (2026-07-29): this allocation used to demand [uart_dlab u = false]
     and freeze the caller's half into the persistent [uart_dlab_off] on the
     spot.  It cannot: the UART thread runs from step 0, so [uart_frag] must
     already live in [uart_inv] when [uartinit] runs -- and [uartinit] SETS
     DLAB (the divisor-latch dance) before its final LCR write clears it
     again.  So the freeze moves OUT to the boot chain, which threads
     [uart_dlab_is γ (DfracOwn (1/2)) b] through the dance and mints
     [uart_dlab_off] with [uart_dlab_freeze] after the last LCR write.
     Power-on DLAB is therefore arbitrary, and no adequacy hypothesis
     constrains it. *)
  Lemma uart_ghosts_alloc (iu : uart_id) (u : uart_state) :
    u_rx u = [] ->
    (* ...AND NOTHING HAS BEEN RECEIVED (relax-d2, lane K1): the reset UART
       has accepted no input, which is the base case of the column's
       input-number clauses. *)
    u_recv u = [] ->
    uart_loopback u = false ->
    (* ...AND NOTHING HAS BEEN DRIVEN ON THE WIRE THAT IS NOT DRAINED: at
       power-on both lists are empty ([DevModel.uart0_state]), which is the
       base case of the column's wire/out clause. *)
    u_wire u = u_out u ->
    (* ...AND NOTHING HAS BEEN ACCEPTED: the port's output claim is founded
       here, at the empty witness history, out of the resource the boot
       carries -- the TRANSPORT's yield ([SystemAdequacy.app_xfer_boot_raw]
       hands the fresh era instance its claim at [[]]/[[]]).  At [Uart1]
       [chist_at] is [emp], so the second port's mint costs nothing
       ([cons_res_at_uart1]).  (lane OUT-FUPD) *)
    uart_acc u = [] ->
    (* ...AND THE INPUT LOG IS FOUNDED HERE TOO (lane CONS-IO), out of the
       transport's fourth yield [I [] [] []]: an empty log, nothing
       delivered, at the empty witness history.  At [Uart1] it is [emp]
       ([cons_res_at_uart1]). *)
    chist_at iu (S gen_id) []
      (LogEntryDefs.MkCH [] [] [] None) -∗
                |==> ∃ γ, uart_sent_auth γ u ∗ uart_out_auth γ u ∗
                uart_tx_auth γ u ∗ uart_dlab_auth γ u ∗
                uart_tx_own γ (uart_acc u) ∗ uart_sent γ (uart_acc u) ∗
                uart_dlab_is γ (DfracOwn (1/2)) (uart_dlab u) ∗
                (* the receive side: the column at an empty FIFO, the token
                   the boot chain carries, and the one-shot the PLIC
                   invariant's pre-deposit arm holds *)
                uart_colE iu γ u ∗ cons_claim_at iu γ u ∗ uart_rx_tok γ 0 None ∗
                uart_rx_hi γ (1/2) None ∗ uart_rx_hi γ (1/2) None ∗
                uart_log_hi γ (1/2) None ∗ uart_deliv γ (1/2) [] ∗
                (* ...AND THE LOG'S EXACT MIRROR, whose other half went into
                   [in_claim_at] above (lane CONS-IO milestone B): at the
                   console port it goes to the ring, at [Uart1] it is
                   dropped like the second high-water half. *)
                uart_logm γ (1/2) [] ∗
                (* ...AND THE DELIVERED COUNT'S RING HALF, at 0 (relax-d2,
                   lane K2): the number beside [uart_deliv]'s list, whose
                   other half is inside the port's claim. *)
                uart_dlcnt γ (1/2) 0%nat ∗
                (* ...AND THE ARM'S PAYLOAD HALF (redesign R2), at [None]:
                   the invariant's half is inside the port's claim above. *)
                uart_arm γ (1/2) None ∗
                uart_preinit γ.
  Proof using .
    intros Hrx Hrc Hlb Hwo Hacc0. iIntros "Hres".
    iMod (own_alloc (●ML (uart_acc u : list (leibnizO (bv 8))))) as (γa) "Ha";
      [apply mono_list_auth_valid|].
    iMod (own_alloc (●ML (u_out u : list (leibnizO (bv 8))))) as (γb) "Hb";
      [apply mono_list_auth_valid|].
    iMod (ghost_var_alloc (uart_acc u)) as (γc) "Hc".
    (* allocate DLAB at the state's OWN value; nothing is assumed about it *)
    iMod (own_alloc (to_dfrac_agree (DfracOwn 1) (uart_dlab u : leibnizO bool)))
      as (γd) "Hd"; [done|].
    (* peel the caller's permanent accepted-trace bound off the authority *)
    iEval (rewrite {1}mono_list_auth_lb_op) in "Ha".
    iDestruct "Ha" as "[Ha Hsent]".
    (* split the ghost_var into the invariant's half and the caller's token *)
    iEval (rewrite -Qp.half_half) in "Hc".
    iDestruct (ghost_var_split with "Hc") as "[Hc1 Hc2]".
    (* split the DLAB agree into the invariant's half and the caller's *)
    iEval (rewrite -Qp.half_half -dfrac_op_own dfrac_agree_op own_op) in "Hd".
    iDestruct "Hd" as "[Hd1 Hd2]".
    (* the receive side's three *)
    iMod (mono_nat_own_alloc 0%nat) as (γpu) "[Hpu _]".
    iMod (ghost_var_alloc (0%nat, @None (list mobs))) as (γpo) "Hpo".
    iEval (rewrite -Qp.half_half) in "Hpo".
    iDestruct (ghost_var_split with "Hpo") as "[Hpo1 Hpo2]".
    iMod (ghost_var_alloc (@None (list mobs))) as (γhi) "Hhi".
    iEval (rewrite -Qp.half_half) in "Hhi".
    iDestruct (ghost_var_split with "Hhi") as "[Hhi1 Hhi2]".
    iMod (mono_nat_own_alloc 0%nat) as (γin) "[Hin _]".
    (* the input log's three (lane CONS-IO): the log's high-water history
       in halves, the kernel's mono_list mirror, and the consumed
       sequence's halves *)
    iMod (ghost_var_alloc (@None (list mobs))) as (γlg) "Hlg".
    iEval (rewrite -Qp.half_half) in "Hlg".
    iDestruct (ghost_var_split with "Hlg") as "[Hlg1 Hlg2]".
    iMod (own_alloc (●ML (@nil (leibnizO LogEntryDefs.log_entry)))) as (γml) "Hml";
      [apply mono_list_auth_valid|].
    iMod (ghost_var_alloc (@nil (list mobs * bv 8))) as (γdv) "Hdv".
    iEval (rewrite -Qp.half_half) in "Hdv".
    iDestruct (ghost_var_split with "Hdv") as "[Hdv1 Hdv2]".
    iMod (ghost_var_alloc (@nil LogEntryDefs.log_entry)) as (γlm) "Hlm".
    iEval (rewrite -Qp.half_half) in "Hlm".
    iDestruct (ghost_var_split with "Hlm") as "[Hlm1 Hlm2]".
    (* the consoleintr arm, at [None] (redesign R2) *)
    iMod (ghost_var_alloc (@None LogEntryDefs.cons_arm)) as (γar) "Har".
    iEval (rewrite -Qp.half_half) in "Har".
    iDestruct (ghost_var_split with "Har") as "[Har1 Har2]".
    (* the delivered COUNT, at 0 (relax-d2, lane K2) *)
    iMod (ghost_var_alloc 0%nat) as (γdc) "Hdc".
    iEval (rewrite -Qp.half_half) in "Hdc".
    iDestruct (ghost_var_split with "Hdc") as "[Hdc1 Hdc2]".
    iModIntro.
    iExists (UartNames γa γb γc γd γpu γpo γhi γin γlg γml γdv γlm γar γdc).
    rewrite /uart_sent_auth /uart_out_auth /uart_tx_auth /uart_tx_own
            /uart_dlab_auth /uart_dlab_is /uart_sent /uart_colE /uart_col
            /uart_rx_tok /uart_rx_popped /uart_rx_hi /uart_preinit /=.
    iFrame "Ha Hb Hc1 Hd1 Hc2 Hsent Hd2".
    (* the column's own half of the pop counter and the caller's token are
       the SAME proposition, so the rest are placed by hand *)
    iSplitR "Hres Hlg1 Hml Hdv1 Hlm1 Hdc1 Hpo2 Hhi1 Hhi2 Hlg2 Hdv2 Hlm2 Hdc2
             Har1 Har2 Hin".
    { iExists [], 0%nat, 0%nat, None, None. iFrame "Hpu Hpo1".
      iSplitR; [done|]. iSplitR; [done|].
      iPureIntro. rewrite /uart_col_ok Hrx Hrc Hlb. cbn [length].
      split_and!; [done | done | done | exact Hwo | intros j b h Hj; done
                  | intros i j hi hj Hi; done | intros j h Hj; done
                  | exact I | intros j h Hj; done
                  | done | intros j hj Hj; done | done | done
                  | intros g Hg; done
                  | cbn [open_seg_o obs_wire]; apply prefix_nil ]. }
    iSplitL "Hres Hlg1 Hml Hdv1 Hlm1 Hdc1 Har1".
    { (* the port's ONE claim, founded at the empty history *)
      iExists None, (LogEntryDefs.MkCH [] [] [] None).
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      iSplitR; [done |].
      iFrame "Hres".
      rewrite /uart_log_hi /uart_deliv /uart_dlcnt /in_log_auth /uart_logm
              /uart_arm /=.
      iFrame "Hlg1 Hdv1 Hdc1 Hml Hlm1 Har1". iPureIntro. split_and!.
      - by rewrite Hacc0.
      - split; [split; [intros e He; inversion He
                       | intros i e1 e2 H1; done] | exact I].
      - exact (cons_log_ins_nil iu). }
    iSplitL "Hpo2"; [iExact "Hpo2" |].
    iSplitL "Hhi1"; [iExact "Hhi1" |].
    iSplitL "Hhi2"; [iExact "Hhi2" |].
    iSplitL "Hlg2"; [rewrite /uart_log_hi /=; iExact "Hlg2" |].
    iSplitL "Hdv2"; [rewrite /uart_deliv /=; iExact "Hdv2" |].
    iSplitL "Hlm2"; [rewrite /uart_logm /=; iExact "Hlm2" |].
    iSplitL "Hdc2"; [rewrite /uart_dlcnt /=; iExact "Hdc2" |].
    iSplitL "Har2"; [rewrite /uart_arm /=; iExact "Har2" | iExact "Hin"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE UART THREAD.  Opens [uartN] for the tx/rx arms and [plicN] for  *)
  (*  the latch arm -- never both, because no single UART transition      *)
  (*  touches both halves.                                               *)
  (* ------------------------------------------------------------------ *)
  (* THE TRACE PERMIT (claude-notes/completed/uart-trace.md).  [wp_uart_step]
     hands the UART thread [state_interp]'s half of the HISTORY ghost and
     wants it back at [h ++ κ]; the other half lives in the client's trace
     predicate ([obs_inv]), so the move is the CLIENT's step, and this is
     its shape: with the arm's own event (at the device state it leaves,
     [set_duart d u']), the two facts the machine layer knows about the
     history -- the power is on, and the open cycle's outputs ARE the
     device's [u_wire] -- and the device ghosts AFTER the step in hand, move
     the history by the event.  It runs inside [uartN] (hence the mask), so
     a client's trace predicate may relate the history to the device ghosts;
     [obsN] is disjoint from [uartN], so the predicate can be opened there.
     The rx arm is the ENVIRONMENT's byte: a client's trace property has to
     survive any input, which is why input assumptions are antecedents
     inside it.  [uart_obs_permit_triv] discharges the permit for the
     trivial predicate. *)
  (* THE TAG THE ARM PRODUCES (app-echo.md lane L5).  Only the rx arm carries
     a byte INTO the machine, so only the rx arm mints a tag: the ambient
     family read at the history the byte arrived at.  Every other arm --
     including the LOOPBACK drain, whose [κ] is empty and whose byte enters
     the receive FIFO with no observation at all -- produces nothing. *)
  Definition uart_tag_of (h κ : list mobs) : iProp Σ :=
    match κ with
    | [ObsUartIn _ _] => riscv_rx_tag (h ++ κ)%list
    | _ => emp
    end%I.

  Global Instance uart_tag_of_persistent h κ : Persistent (uart_tag_of h κ).
  Proof using .
    rewrite /uart_tag_of. destruct κ as [|k κ']; [apply _|].
    destruct k; destruct κ'; apply _.
  Qed.

  (* at the trivial family every arm's tag is free *)
  Lemma uart_tag_of_triv (h κ : list mobs) :
    riscv_rx_tag = rx_tag_triv -> ⊢ uart_tag_of h κ.
  Proof using .
    intros Htag. rewrite /uart_tag_of.
    destruct κ as [|k κ']; [done|].
    destruct k; destruct κ'; try done.
    rewrite Htag /rx_tag_triv. done.
  Qed.

  (* THE THREE THINGS THE OPEN INVARIANT HANDS OVER BESIDE THE STEP (lane
     OUT-FUPD).  The thread opens the port's invariant before it invokes the
     permit, so the column's own clauses are in hand there; two of them are
     what a trace ledger needs and cannot otherwise get:

       - the WIRE IS THE DRAINED SEQUENCE ([uart_colE_wire_out]), which is
         what makes the wire a PREFIX of [uart_acc];
       - the OUTPUT CLAIM at a witness history the invariant holds a
         monotone lower bound on ([uart_out_claim]), placed inside the run's
         own history here -- where [obs_auth] is -- and handed over as the
         pure pair [⌜ho `prefix_of` h⌝] / [⌜out_ok_at i ho (uart_acc ...)⌝].

     They ride EVERY arm rather than only the drain, because the permit is
     one wand; the arms that do not read them cost nothing. *)
  Definition uart_obs_permit (i : uart_id) (γ : uart_names) : iProp Σ :=
    (□ ∀ (h κ : list mobs) (d : dev_state) (u' : uart_state),
       ⌜uart_step i d κ (set_duart d i u')⌝ -∗ ⌜trace_shape h true⌝ -∗
       ⌜obs_wire i (open_seg h) = u_wire (duart d i)⌝ -∗
       (* ...AND THE INPUT TIE (relax-d2, lane K1), which the rx arm spends
          to give the byte it queues its INPUT NUMBER *)
       ⌜obs_ins i (open_seg h) = u_recv (duart d i)⌝ -∗
       ⌜u_wire (duart d i) = u_out (duart d i)⌝ -∗
       (* ...AND THE ERA STAMP (lane CONS-IO milestone C): the history the
          ledger is stepped at belongs to THIS era, and the era's number is
          [S gen_id].  It is [ObsTrace.obs_wf]'s boot count at a live UART
          thread ([RiscvExec.wp_uart_step] hands it over), and it is what
          makes the ledger's per-era state addressable without any
          comparison of histories inside a link. *)
       ⌜obs_boots h = S gen_id⌝ -∗
       (* THE PORT'S ONE CLAIM (redesign R2), taken linearly and given
          back.  It used to be two -- the output claim at the accepted
          bytes and the input claim -- read at two witnesses; the ledger
          reads what the user typed against what came out, and that is one
          reading of one resource now. *)
       cons_claim_at i γ (duart d i) -∗
       uart_ghosts γ u' -∗ obs_auth h ={⊤ ∖ ↑uartN i}=∗
       cons_claim_at i γ (duart d i) ∗
       uart_ghosts γ u' ∗ obs_auth (h ++ κ)%list ∗ uart_tag_of h κ)%I.

  Lemma uart_obs_permit_triv (i : uart_id) (γ : uart_names) :
    riscv_obs_pred = obs_pred_triv ->
    (* the trivial application claims nothing of its input, so the tag the rx
       arm owes is [True] and the permit can mint it out of nothing *)
    riscv_rx_tag = rx_tag_triv ->
    obs_inv -∗ uart_obs_permit i γ.
  Proof using .
    intros Heq Htag. iIntros "#Hoinv !>" (h κ d u')
      "%Hstep %Hsh %Hwire %Hrecv %Hwo %Hbts Hcl Hg Hauth".
    iInv "Hoinv" as "HP" "Hclose".
    iEval (rewrite Heq /obs_pred_triv) in "HP".
    iDestruct "HP" as (h') ">Hfrag".
    iDestruct (obs_agree with "Hauth Hfrag") as %<-.
    iMod (obs_update _ (h ++ κ)%list (ex_intro _ κ eq_refl)
            with "Hauth Hfrag") as "[Hauth Hfrag]".
    iMod ("Hclose" with "[Hfrag]") as "_".
    { iNext. rewrite Heq /obs_pred_triv. iExists (h ++ κ)%list. iExact "Hfrag". }
    iModIntro. iFrame "Hcl Hg Hauth". iApply uart_tag_of_triv. exact Htag.
  Qed.

  (* THE PERMIT FROM A LEDGER (uart-trace.md phase 4).  The client's trace
     predicate is [obs_ledger R], and its two wands are the whole
     obligation: at the tx arm, with the byte that reached the wire (NOT
     under LOOP, which emits nothing); at the rx arm, with the ENVIRONMENT's
     byte -- each with the device ghosts after the step and the two machine
     facts in hand, at a mask that lets the wand open the crash invariant
     too.  Coq-level hypotheses, so the system theorem can pass its own
     down; [R] timeless, so the ledger's later strips. *)
  Lemma uart_obs_permit_ledger (i : uart_id) (R : list mobs -> iProp Σ)
      (Tg : list mobs -> iProp Σ)
      (Cres : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ)
      (γ : uart_names)
      (HRt : forall h, Timeless (R h))
      (Heq : riscv_obs_pred = obs_ledger R)
      (* the tag family the record carries IS the client's, which is what
         lets the rx wand below discharge the permit's tag output *)
      (Htag : riscv_rx_tag = Tg)
      (* ...AND SO IS THE PORT'S CLAIM (redesign R2).  ONE resource at ONE
         witness, where there were two at two -- the second existed only
         because a writer's link moved the output's and not the input's, and
         both move together now.  Taken linearly and given back: the ledger
         step reads its own authority against its own ledger and puts it
         where it found it. *)
      (Hook : riscv_cons_res = Cres)
      (Htx : ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state)
                     (ho : list mobs) (H : LogEntryDefs.cons_hist),
               ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
               ⌜trace_shape h true⌝ -∗ ⌜obs_wire i (open_seg h) = u_wire u⌝ -∗
               ⌜u_wire u = u_out u⌝ -∗
               (* THE ERA STAMP (lane CONS-IO milestone C): the drained
                  history is this era's, and the era's number is [S gen_id]
                  -- which is the index the two claims below are read at. *)
               ⌜obs_boots h = S gen_id⌝ -∗
               ⌜ho `prefix_of` h⌝ -∗
               (* the accepted bytes are a FIELD of the history now, so the
                  tie the wand used to get by being handed [uart_acc u] is a
                  premise *)
               ⌜LogEntryDefs.ch_acc H = uart_acc u⌝ -∗
               (if i is Uart0 then Cres (S gen_id) ho H else emp) -∗
               uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
               (if i is Uart0 then Cres (S gen_id) ho H else emp) ∗
               uart_ghosts γ u' ∗ R (h ++ [ObsUartOut i b])%list))
      (Hrx : ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
               ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
               ⌜obs_boots h = S gen_id⌝ -∗
               uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN i ∖ ↑obsN}=∗
               uart_ghosts γ u' ∗ R (h ++ [ObsUartIn i b])%list ∗
               Tg (h ++ [ObsUartIn i b])%list)) :
    obs_inv -∗ uart_obs_permit i γ.
  Proof using .
    iIntros "#Hoinv". iPoseProof Htx as "#Htx". iPoseProof Hrx as "#Hrx".
    iIntros "!>" (h κ d u')
      "%Hstep %Hsh %Hwire %Hrecv %Hwo %Hbts Hcl Hg Hauth".
    (* THE CLAIM'S WITNESS, PLACED INSIDE THE RUN'S OWN HISTORY.  This is
       the only point where both the invariant's monotone bound and the
       machine's history authority are in hand, so it is where the pure
       [ho `prefix_of` h] the ledger's wand needs is produced (lane
       OUT-FUPD). *)
    iDestruct "Hcl" as (o0 CH)
      "(#Holb & Hres & Hlgh & Hdv & Hdc0 & Hau & Hlm0 & Harm & %Hacc0 & %Hlok
        & %Hlins)".
    iDestruct (obs_hist_lb_o_prefix o0 h with "Hauth Holb") as %Hopre.
    iInv "Hoinv" as "HP" "Hclose".
    iEval (rewrite Heq /obs_ledger) in "HP".
    iDestruct "HP" as (h') "[>Hfrag >HR]".
    iDestruct (obs_agree with "Hauth Hfrag") as %<-.
    remember (set_duart d i u') as d' eqn:Hd'.
    destruct Hstep as [b u0 Htx0 | b u0 Hrx0 | p' _ _ |].
    - (* a byte left the transmitter *)
      assert (u0 = u') as -> by
        (apply (f_equal (fun dd => duart dd i)) in Hd';
         by rewrite !set_duart_eq in Hd').
      destruct (uart_loopback (duart d i)) eqn:Hlb.
      + (* under LOOP nothing reached the wire: no event *)
        iMod ("Hclose" with "[Hfrag HR]") as "_".
        { iNext. rewrite Heq /obs_ledger. iExists h. iFrame. }
        iModIntro. rewrite app_nil_r.
        iSplitL "Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
        { iExists o0, CH. iFrame "Holb Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
          by iPureIntro. }
        iFrame "Hg Hauth"; try done.
      + iEval (rewrite /chist_at Hook) in "Hres".
        iMod ("Htx" $! h b (duart d i) _ (default [] o0) CH
                with "[//] [//] [//] [//] [//] [//] [//] [//] Hres Hg HR")
          as "(Hres & Hg & HR)".
        iMod (obs_update _ (h ++ [ObsUartOut i b])%list
                (ex_intro _ [ObsUartOut i b] eq_refl) with "Hauth Hfrag")
          as "[Hauth Hfrag]".
        iMod ("Hclose" with "[Hfrag HR]") as "_".
        { iNext. rewrite Heq /obs_ledger. iExists _. iFrame. }
        iModIntro.
        iSplitL "Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
        { iExists o0, CH. iFrame "Holb Hlgh Hdv Hdc0 Hau Hlm0 Harm".
          iSplitL "Hres"; [by iEval (rewrite /chist_at Hook) |].
          by iPureIntro. }
        iFrame "Hg Hauth"; try done.
    - (* a byte arrived from the outside world: the ONE arm with a tag *)
      assert (u0 = u') as -> by
        (apply (f_equal (fun dd => duart dd i)) in Hd';
         by rewrite !set_duart_eq in Hd').
      iMod ("Hrx" $! h b (duart d i) _ with "[//] [//] [//] Hg HR")
        as "(Hg & HR & Htg)".
      iMod (obs_update _ (h ++ [ObsUartIn i b])%list
              (ex_intro _ [ObsUartIn i b] eq_refl) with "Hauth Hfrag")
        as "[Hauth Hfrag]".
      iMod ("Hclose" with "[Hfrag HR]") as "_".
      { iNext. rewrite Heq /obs_ledger. iExists _. iFrame. }
      iModIntro.
      iSplitL "Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
      { iExists o0, CH. iFrame "Holb Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
        by iPureIntro. }
      iFrame "Hg Hauth". rewrite /uart_tag_of Htag. iExact "Htg".
    - (* the latch: silent *)
      iMod ("Hclose" with "[Hfrag HR]") as "_".
      { iNext. rewrite Heq /obs_ledger. iExists h. iFrame. }
      iModIntro. rewrite app_nil_r.
      iSplitL "Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
      { iExists o0, CH. iFrame "Holb Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
        by iPureIntro. }
      iFrame "Hg Hauth"; try done.
    - (* the stutter: silent *)
      iMod ("Hclose" with "[Hfrag HR]") as "_".
      { iNext. rewrite Heq /obs_ledger. iExists h. iFrame. }
      iModIntro. rewrite app_nil_r.
      iSplitL "Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
      { iExists o0, CH. iFrame "Holb Hres Hlgh Hdv Hdc0 Hau Hlm0 Harm".
        by iPureIntro. }
      iFrame "Hg Hauth"; try done.
  Qed.

  (* ONE THREAD PER PORT.  [γ] is THIS port's ghost bundle and its own
     invariant; [γp γp1] are the names the ONE PLIC invariant was allocated
     at, which the latch arm needs and does not otherwise read -- a latch
     sets a PENDING bit and no slot moves, at either port. *)
  Lemma wp_uart_loop (i : uart_id) (γ γp γp1 : uart_names) :
    gen_cert -∗ uart_inv i γ -∗ plic_inv γp γp1 -∗ uart_obs_permit i γ -∗
    mWP (UartLoop i : expr riscv_lang).
  Proof using .
    iIntros "#Hcert #Huinv #Hpinv #Hperm".
    iLöb as "IH".
    iApply (wp_uart_step with "Hcert").
    iIntros (gr m d h Hsh Hwire Hrecv Hbts) "(Hgr & Hmem & Hdev & Hoauth)".
    (* No invariant is opened until the arm is known: each arm then opens
       exactly the one half of the fabric it moves. *)
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    (* the observation list [κ] is the arm's own I/O event (RiscvLang §3b');
       no ghost here tracks it -- [uart_ghosts] mirrors the DEVICE state, and
       the wire trace is already pinned by [u_wire] ([uart_step_wire]) *)
    iNext. iIntros (κ d' Hstep).
    iMod "Hmask" as "_".
    pose proof Hstep as Hstep0.
    destruct Hstep as [b u' Htx0 | b u' Hrx | p' Hirq Hlatch |].
    - (* a byte leaves the tx FIFO: it moves from the head of [u_tx] to the
         tail of [u_out], so the accepted trace is UNCHANGED. *)
      iInv "Huinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (u) "(Hu & Hg & Hcol & Hcons)".
      iDestruct (dev_interp_agree_uart with "Hdev Hu") as %Hu.
      rewrite Hu in Htx0.
      iMod (dev_interp_update_uart _ i u u' with "Hdev Hu") as "[Hdev' Hu']".
      (* the accepted trace, the transmitter token and DLAB are all untouched;
         only the transmitted prefix grows, by exactly the drained byte. *)
      iEval (rewrite /uart_ghosts) in "Hg".
      iDestruct "Hg" as "(Hacc & Hout & Htx & Hdl)".
      iDestruct (uart_sent_auth_stable _ u u'
                   (uart_tx_pop_acc _ _ _ Htx0) with "Hacc") as "Hacc".
      iDestruct (uart_tx_auth_stable _ u u'
                   (uart_tx_pop_acc _ _ _ Htx0) with "Htx") as "Htx".
      iDestruct (uart_dlab_auth_stable _ u u'
                   (uart_tx_pop_dlab _ _ _ Htx0) with "Hdl") as "Hdl".
      iMod (uart_out_update _ u u' with "Hout") as "[Hout _]".
      { rewrite (uart_tx_pop_out _ _ _ Htx0). by apply prefix_app_r. }
      (* THE TRACE STEP: the client moves the history by the output event
         (nothing under LOOP -- the arm's own [κ]) *)
      iAssert (uart_ghosts γ u') with "[Hacc Hout Htx Hdl]" as "Hg".
      { rewrite /uart_ghosts. iFrame. }
      (* THE TWO CLAUSES THE PERMIT IS HANDED (lane OUT-FUPD), read off the
         column while the invariant is open: the wire IS the drained
         sequence, and the output claim at a witness history -- placed
         inside the machine's own history HERE, against [obs_auth], because
         that is the only place both are in hand. *)
      iDestruct (uart_colE_wire_out_keep i γ u with "Hcol") as "[%Hwo Hcol]".

      (* the tx arm's tag output is [emp] ([uart_tag_of] mints one only for
         an rx event), so the column takes nothing here.  The OUTPUT CLAIM
         is lent to the permit and comes straight back: the ledger reads its
         own authority against its own ledger and puts it where it found
         it. *)
      iMod ("Hperm" $! h _ d u'
              with "[//] [//] [//] [//] [] [//] [Hcons] Hg Hoauth")
        as "(Hcons & Hg & Hoauth & _)".
      { iPureIntro. rewrite Hu. exact Hwo. }
      { rewrite Hu. iExact "Hcons". }
      iEval (rewrite Hu) in "Hcons".

      (* THE COLUMN: with LOOP off ([uart_col]'s own clause, read off the
         state the invariant is at) the drain does not touch [u_rx] at all;
         under LOOP it would re-enter the receiver with no observation, which
         is why the clause is there. *)
      iDestruct (uart_colE_tx_pop i γ u u' _ Htx0 with "Hcol") as "Hcol".
      (* the claim is stated over the ACCEPTED bytes, and a tx drain moves
         the transmitted prefix only, so it carries over unchanged *)
      iDestruct (cons_claim_at_stable i γ u u'
                   (uart_tx_pop_acc _ _ _ Htx0) with "Hcons") as "Hcons".
      iMod ("Hclose" with "[Hu' Hg Hcol Hcons]") as "_".
      { iNext. iExists u'. iFrame. }
      iModIntro. iFrame "Hgr Hmem Hdev' Hoauth". iApply "IH".
    - (* a byte arrives from the outside world: rx only, trace untouched *)
      iInv "Huinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (u) "(Hu & Hg & Hcol & Hcons)".
      iDestruct (dev_interp_agree_uart with "Hdev Hu") as %Hu.
      rewrite Hu in Hrx.
      iMod (dev_interp_update_uart _ i u u' with "Hdev Hu") as "[Hdev' Hu']".
      (* rx touches neither the tx side nor LCR: every ghost is unchanged *)
      iDestruct (uart_ghosts_stable _ u u'
                   (uart_rx_push_acc _ b _ Hrx)
                   (uart_rx_push_out _ b _ Hrx)
                   (uart_rx_push_dlab _ b _ Hrx) with "Hg") as "Hg".
      (* THE TRACE STEP: the client moves the history by the input event *)
      (* the rx arm's tag is the application's claim about this byte, at the
         history it arrived at -- and it is what the column files beside the
         byte, so every later reader of the FIFO's head gets a copy. *)
      (* THE COLUMN'S ORDER IS DECIDED BEFORE THE EVENT.  The column holds a
         lower bound on the newest history it has seen; read against the
         machine's history AS IT IS NOW, that bound says every queued byte
         arrived at or before [h] -- and the byte about to arrive is at
         [h ++ [ObsUartIn b]], strictly after.  So the accessor is taken
         here, with the auth in hand and BEFORE the permit moves it. *)
      iDestruct (uart_colE_wire_out_keep i γ u with "Hcol") as "[%Hwo Hcol]".

      iDestruct (uart_col_push_acc i γ u h
                   ltac:(rewrite -Hu; exact Hrecv) with "Hcol Hoauth")
        as "[Hoauth Hpush]".
      iMod ("Hperm" $! h [ObsUartIn i b] d u'
              with "[//] [//] [//] [//] [] [//] [Hcons] Hg Hoauth")
        as "(Hcons & Hg & Hoauth & #Htg)".
      { iPureIntro. rewrite Hu. exact Hwo. }
      { rewrite Hu. iExact "Hcons". }
      iEval (rewrite Hu) in "Hcons".
      iDestruct (obs_auth_lb with "Hoauth") as "[Hoauth #Hlbn]".
      (* THE COLUMN: the byte goes on the tail of [u_rx] and its history --
         which ends with exactly this event -- on the tail of the column. *)
      destruct (uart_rx_push_rx u b u' Hrx) as [Hrxe Hlbe].
      pose proof (uart_rx_push_wire u b u' Hrx) as Hwe.
      pose proof (uart_rx_push_out u b u' Hrx) as Hoe.
      (* THE BYTE'S WIRE RIDER (lane CONS-IO, the second C2 amendment).  It
         is MINTED HERE and nowhere else: this is the one point in the
         machine where the trace coupling [obs_wire i (open_seg h) = u_wire
         u] and the transmitted-prefix authority are in the same hands.  An
         input event puts nothing on the wire, so the bound holds at the
         byte's OWN post-arrival history, which is the history its tag is
         filed at. *)
      assert (Hrider : obs_wire i (open_seg (h ++ [ObsUartIn i b])%list)
                       = u_out u').
      { rewrite obs_wire_open_seg_in Hwire Hu Hwo. by rewrite Hoe. }
      iDestruct "Hg" as "(Hgs & Hgo & Hgt & Hgd)".
      iDestruct (uart_out_get γ u' with "Hgo") as "[Hgo #Hwlb]".
      iEval (rewrite -Hrider) in "Hwlb".
      iAssert (uart_ghosts γ u') with "[Hgs Hgo Hgt Hgd]" as "Hg";
        [rewrite /uart_ghosts; iFrame "Hgs Hgo Hgt Hgd" |].
      (* the byte's ERA STAMP (milestone C): an input event is I/O, so it
         adds no boot to the history and the arrival inherits the stamp the
         step handed over. *)
      assert (Hbts' : obs_boots (h ++ [ObsUartIn i b])%list = S gen_id).
      { rewrite obs_boots_app (obs_boots_io [ObsUartIn i b]
                                 ltac:(repeat constructor)).
        rewrite Nat.add_0_r. exact Hbts. }
      iMod ("Hpush" $! u' b
              with "[//] [//] [//] [//] [%] Htg Hlbn Hwlb [//] [%] [%]")
        as "Hcol".
      { exact (uart_rx_push_recv u b u' Hrx). }
      { apply (trace_shape_io h [ObsUartIn i b] Hsh).
        repeat constructor. }
      { exact Hrider. }
      (* an arrival touches the rx FIFO only, so the port's claim -- stated
         over the ACCEPTED bytes -- carries over unchanged *)
      iDestruct (cons_claim_at_stable i γ u u'
                   (uart_rx_push_acc u b u' Hrx) with "Hcons") as "Hcons".

      iMod ("Hclose" with "[Hu' Hg Hcol Hcons]") as "_".
      { iNext. iExists u'. iFrame. }
      iModIntro. iFrame "Hgr Hmem Hdev' Hoauth". iApply "IH".
    - (* the gateway latches the UART's interrupt level.  This is the ONE
         UART transition that touches the PLIC, and it touches nothing else,
         so only [plicN] is opened. *)
      iInv "Hpinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (p) "(Hp & %Hpok & Harm)".
      iDestruct (dev_interp_agree_plic with "Hdev Hp") as %Hp.
      iMod (dev_interp_update_plic _ p p' with "Hdev Hp") as "[Hdev' Hp']".
      assert (Hlat : plic_latch p (uart_irq_id i) = Some p')
        by (rewrite <- Hp; exact Hlatch).
      (* the gateway sets a PENDING bit and touches no service bit, so every
         slot survives it -- whichever port's source was latched *)
      pose proof (plic_latch_claimed p p' (uart_irq_id i) Hlat) as Hcl'.
      iMod ("Hclose" with "[Hp' Harm]") as "_".
      { iNext. iExists p'. iFrame "Hp'".
        iSplitR;
          [iPureIntro; exact (plic_ok_latch p p' (uart_irq_id i) Hlat Hpok)|].
        iApply (plic_slots_stable _ _ p p' (Hcl' (uart_irq_id Uart0))
                  (Hcl' (uart_irq_id Uart1))).
        iExact "Harm". }
      (* silent: the history is unchanged *)
      rewrite app_nil_r.
      iModIntro. iFrame "Hgr Hmem Hdev' Hoauth". iApply "IH".
    - (* the totality stutter (RiscvLang §3c): nothing moved, so nothing has
         to be re-established and no invariant is opened at all. *)
      rewrite app_nil_r.
      iModIntro. iFrame "Hgr Hmem Hdev Hoauth". iApply "IH".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE DISK THREAD.  Opens [diskN] for the DMA/wild arms and [plicN]   *)
  (*  for the latch arm.                                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_disk_loop (γu γu1 : uart_names) γd :
    (* the disk names are the CANONICAL ones: the image gname is the AMBIENT
       ERA's, which is what identifies the auth [wp_disk_step] hands over with
       the fragments [virtio_proto] holds.  [disk_ghosts_alloc] exports this
       equation. *)
    dn_img γd = disk_img_name ->
    (* [crash_inv] is taken PERSISTENTLY and opened in exactly one arm: the
       DMA completion, where the durable image changes and the write permit
       deposited at enqueue re-establishes the crash predicate
       (claude-notes/design/crash.md).  [crashN] is disjoint from [diskN] and
       [plicN], so the two openings compose. *)
    gen_cert -∗ crash_inv -∗ perm_inv gen_id (dn_perm γd) -∗ disk_inv γd -∗
    plic_inv γu γu1 -∗
    mWP (DiskLoop : expr riscv_lang).
  Proof using .
    intros Himg.
    iIntros "#Hcert #Hcinv #Hqinv #Hvinv #Hpinv".
    iLöb as "IH".
    iApply (wp_disk_step with "Hcert").
    (* the fourth component is the ERA's image auth ([wp_disk_step] hands it
       over because a DMA completion is the one step that moves [v_disk]): the
       latch and stutter arms FRAME it, and the completion arm passes it
       through [virtio_proto_step] (claude-notes/design/crash.md). *)
    iIntros (gr m d n img log V Hn)
            "(Hgr & Hmem & Hdev & Hdur & Htie & Hsa & Htso)".
    (* THE PERMIT INVARIANT IS OPENED IN THE FIRST (⊤ -> ∅) LEG, before the
       arm is even known.  It has to be: [perm_inv_body] is NOT timeless (it
       holds the clients' view shifts), so the only [▷]-stripping opportunity
       in this rule is the one BETWEEN the legs -- the [iNext] two lines down.
       Opening it unconditionally costs nothing: three of the four arms hand
       it straight back.  [permN], [crashN] and [devN] are pairwise disjoint,
       so the openings compose ([solve_ndisj]). *)
    iInv "Hqinv" as "Hpbody" "Hpclose".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iNext. iIntros (d' W log') "%Hstep %Hlog".
    iMod "Hmask" as "_".
    destruct Hstep as [mv vnew Hview Hpop | mv h vnew Hview Hfetch
                      | mv h vnew Hview Hcap | h vnew w Hwrite
                      | h vnew w Hdisk | s vnew Hdrain
                      | mv w Hview Hstall | p' Hirq Hlatch |].
    - (* THE POP -- the device takes the next available-ring entry
         (tools/vtest/README.md finding 5).  This is the phase QEMU does
         strictly IN ORDER, and it is what xv6's reuse of
         [avail->ring[idx % NUM]] rests on.  It reads the ring and moves the
         pop index; it writes NO byte memory, produces no used-ring entry,
         raises no interrupt and moves no durable disk byte, so there is no
         permit to spend and no image to move. *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      (* A6.11: this arm's write set is [∅], so the log disjunct forces
         [log' = log] and the memory is untouched -- the bundle comes
         straight back ([RiscvExec.tso_interp_of_disk_idle] pays the disk
         agent's pinned view). *)
      destruct Hlog as [[_ ->] | [Hne _]]; [| exfalso; exact (Hne eq_refl)].
      rewrite (left_id_L (∅ : gmap Arch.pa (bv 8)) union).
      rewrite Hv in Hpop.
      iMod (dev_interp_update_virtio _ vs vnew with "Hdev Hv") as "[Hdev' Hv']".
      iDestruct (virtio_proto_pop_step γd vs m mv vnew Hview Hpop
                   with "Hmem Hlease") as "[Hmem Hlease]".
      iMod ("Hclose" with "[Hv' Hlease]") as "_".
      { iNext. iExists vnew. iFrame "Hv' Hlease".
        iPureIntro. exact (virtio_pop_step_isr_ok vs mv vnew Hvok Hpop). }
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      assert (Hdk : v_disk vnew = v_disk (dvirtio d))
        by (rewrite Hv; exact (virtio_pop_step_disk vs mv vnew Hpop)).
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
      rewrite <- Hdk in Hdview.
      iSplitL "Hdauth".
      { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
      iEval (rewrite <- Hdk) in "Htie".
      iFrame "Htie Hsa".
      iSplitL "Htso"; [iApply (tso_interp_of_disk_idle with "Htso") |].
      iApply "IH".
    - (* THE FETCH -- the device reads a popped head's descriptor chain and
         request header, once, through the same bus view the pop read the
         ring through.  Like the pop it writes no byte memory and moves no
         disk byte; what the invariant learns is that the request the device
         now holds is the one the driver pinned. *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      destruct Hlog as [[_ ->] | [Hne _]]; [| exfalso; exact (Hne eq_refl)].
      rewrite (left_id_L (∅ : gmap Arch.pa (bv 8)) union).
      rewrite Hv in Hfetch.
      iMod (dev_interp_update_virtio _ vs vnew with "Hdev Hv") as "[Hdev' Hv']".
      iDestruct (virtio_proto_fetch_step γd vs m mv h vnew Hview Hfetch
                   with "Hmem Hlease") as "[Hmem Hlease]".
      iMod ("Hclose" with "[Hv' Hlease]") as "_".
      { iNext. iExists vnew. iFrame "Hv' Hlease".
        iPureIntro. exact (virtio_fetch_step_isr_ok vs mv h vnew Hvok Hfetch). }
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      assert (Hdk : v_disk vnew = v_disk (dvirtio d))
        by (rewrite Hv; exact (virtio_fetch_step_disk vs mv h vnew Hfetch)).
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
      rewrite <- Hdk in Hdview.
      iSplitL "Hdauth".
      { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
      iEval (rewrite <- Hdk) in "Htie".
      iFrame "Htie Hsa".
      iSplitL "Htso"; [iApply (tso_interp_of_disk_idle with "Htso") |].
      iApply "IH".
    - (* THE CAPTURE: a write request's data enters the device's VOLATILE
         cache (claude-notes/completed/async-disk.md).  It reads the driver's
         buffer off the bus once -- which is the only reason this arm carries
         a memory view at all -- and moves NOTHING else: no byte memory (the
         step's [m' = m]), no used ring, no ISR, no consumed index, and NO
         DURABLE DISK BYTE.  So there is no permit to spend and [crashN] is
         NOT opened here: a power cycle between the capture and the drains
         loses the whole request, which is exactly what the client's
         still-unspent sequential permit says.  Both the era image auth and
         the FS tie are FRAMED. *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      destruct Hlog as [[_ ->] | [Hne _]]; [| exfalso; exact (Hne eq_refl)].
      rewrite (left_id_L (∅ : gmap Arch.pa (bv 8)) union).
      rewrite Hv in Hcap.
      iMod (dev_interp_update_virtio _ vs vnew with "Hdev Hv") as "[Hdev' Hv']".
      iDestruct (virtio_proto_capture_step γd vs m mv h vnew Hview Hcap
                   with "Hmem Hlease") as "[Hmem Hlease]".
      iMod ("Hclose" with "[Hv' Hlease]") as "_".
      { iNext. iExists vnew. iFrame "Hv' Hlease".
        iPureIntro. exact (virtio_capture_step_isr_ok vs mv h vnew Hvok Hcap). }
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      assert (Hdk : v_disk vnew = v_disk (dvirtio d))
        by (rewrite Hv; exact (virtio_capture_step_disk vs mv h vnew Hcap)).
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
      rewrite <- Hdk in Hdview.
      iSplitL "Hdauth".
      { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
      iEval (rewrite <- Hdk) in "Htie".
      iFrame "Htie Hsa".
      iSplitL "Htso"; [iApply (tso_interp_of_disk_idle with "Htso") |].
      iApply "IH".
    - (* ONE WRITE TRANSACTION into the driver's memory -- a read's data
         buffer, the status byte, or the used-ring element, whichever the
         request's phase calls for (VirtioModel section 6).  The ONLY thing
         that justifies it is the DMA lease inside the invariant:
         [virtio_proto_write_step] hands out the written bytes' OLD sealed
         cells and takes the new ones back sealed, because the write set
         provably lands inside the lease and misses the queue's control
         region.  It moves no disk byte and spends no permit -- the request
         stays pending until its index bump -- so [crashN] stays closed; the
         era image auth goes in only so the FILL can read the block's bytes
         off the slot's fragments, and comes straight back.

         THE APPEND IS PERFORMED HERE, by the disk loop, and not inside the
         protocol lemma (A6.48 ruling 4): [TsoCtxStore.ledger_store_ok] moves
         [gen_heap_interp] and [tso_interp_at] TOGETHER, and the loop is the
         one holder of both.  The device is an agent of the era log, so the
         transaction goes in as ONE message authored by [disk_agent]; the
         stamp the new cells come back with is hidden again at once -- the
         completion is what bounds it, from the log, when it publishes. *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      rewrite Hv in Hwrite.
      iMod (dev_interp_update_virtio _ vs vnew with "Hdev Hv") as "[Hdev' Hv']".
      iEval (rewrite -Himg Hv) in "Hdur".
      iDestruct (virtio_proto_write_step γd vs h vnew w Hwrite with "Hdur Hlease")
        as (old) "(%Hdomold & Hold & Hback)".
      iAssert (|==> gen_heap_interp (w ∪ m) ∗
                 tso_interp_of riscv_eraGS img (w ∪ m) log'
                   (vstep disk_agent (length log') log' V) ∗
                 phys_map w)%I
        with "[Hmem Htso Hold]" as ">(Hmem & Htso & Hnew)".
      { iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
        iDestruct (tso_interp_of_bound with "Htso") as %Hbnd.
        destruct Hlog as [[Hw Hl] | [Hne Hl]].
        - (* nothing written: the bundle comes straight back *)
          subst w log'. rewrite (left_id_L (∅ : gmap Arch.pa (bv 8)) union).
          iModIntro. iFrame "Hmem".
          iSplitL "Htso"; [iApply (tso_interp_of_disk_idle with "Htso") |].
          rewrite /phys_map big_sepM_empty. done.
        - (* the real append, at the [disk_agent] author *)
          subst log'.
          set (V' := vstep disk_agent
                       (length (log ++ [TsoMemPa.PWMsg w disk_agent])%list)
                       (log ++ [TsoMemPa.PWMsg w disk_agent])%list V).
          assert (Hpin' : forall h, (NCPU <= h)%nat ->
                    V' h = length (log ++ [TsoMemPa.PWMsg w disk_agent])%list).
          { intros h' Hh. rewrite /V' /vstep. case_decide as Hd; [done|].
            destruct (lt_dec h' NCPU) as [|Hge]; [lia|done]. }
          assert (Htvmono : forall c : CPU,
                    (V (hart_agent c) <= V' (hart_agent c))%nat).
          { intros c. rewrite /V' /vstep. case_decide as Hd.
            - exfalso. pose proof (fin_to_nat_lt c).
              rewrite /hart_agent /disk_agent in Hd. lia.
            - destruct (lt_dec (hart_agent c) NCPU) as [|Hge]; [lia|].
              exfalso. pose proof (fin_to_nat_lt c).
              rewrite /hart_agent in Hge. lia. }
          assert (Htvtop : forall c : CPU,
                    (V' (hart_agent c) <= length
                       (log ++ [TsoMemPa.PWMsg w disk_agent])%list)%nat).
          { intros c. rewrite /V' /vstep. case_decide as Hd; [lia|].
            destruct (lt_dec (hart_agent c) NCPU) as [|Hge].
            - rewrite length_app /=. have := Hbnd (hart_agent c). lia.
            - lia. }
          rewrite (tso_interp_of_at_gs riscv_eraGS img m log V
                     (gr 0%fin) d Hpin).
          iEval (rewrite /phys_map) in "Hold".
          iMod (TsoCtxStore.ledger_store_ok
                  (gs_of img m log V (gr 0%fin) d)
                  (gs_of img (w ∪ m)
                     (log ++ [TsoMemPa.PWMsg w disk_agent])%list V'
                     (gr 0%fin) d)
                  disk_agent old w Hdomold eq_refl eq_refl eq_refl
                  Htvmono Htvtop with "Hmem Htso Hold")
            as "(Hmem & Htso & _ & Hnew)".
          iModIntro. iFrame "Hmem".
          rewrite -(tso_interp_of_at_gs riscv_eraGS img (w ∪ m)
                      (log ++ [TsoMemPa.PWMsg w disk_agent])%list V'
                      (gr 0%fin) d Hpin').
          iFrame "Htso". rewrite /phys_map.
          iApply (big_sepM_impl with "Hnew"). iIntros "!>" (a b _) "H".
          iApply phys_ledger_at_ledger. iExact "H". }
      iDestruct ("Hback" with "Hnew") as "[Hdur Hlease']".
      iMod ("Hclose" with "[Hv' Hlease']") as "_".
      { iNext. iExists vnew. iFrame.
        iPureIntro. exact (virtio_write_step_isr_ok vs h vnew w Hvok Hwrite). }
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      assert (Hdk : v_disk vnew = v_disk vs)
        by exact (virtio_write_step_disk vs h vnew w Hwrite).
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
      iEval (rewrite Himg) in "Hdauth".
      rewrite <- Hdk in Hdview.
      iSplitL "Hdauth".
      { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
      iEval (rewrite Hv -Hdk) in "Htie".
      iFrame "Htie Hsa Htso".
      iApply "IH".
    - (* THE COMPLETION -- the used index, the last of a request's
         transactions and the one the driver waits for.  Two bytes into the
         lease, and the ghost moves that publish the request to the
         interrupt handler.

         IT DOES NOT MOVE THE DURABLE IMAGE (sector-atomic-disk.md stage 2):
         every sector of an OUT request landed at its own earlier drain, so
         the [wr] this arm gets back is [None] and the permit it spends is the
         request's trivial COMPLETION permit -- the LEAF of the sequential
         permit, where a client's receipt is delivered in both directions.
         The arm's SHAPE is direction-agnostic on purpose: the disk thread
         cannot tell a read from a write here.  The crash predicate is still
         re-established, because the permit's view shift is what delivers
         the client's receipt; the image it is run at is the one the machine
         already has. *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      rewrite Hv in Hdisk.
      iMod (dev_interp_update_virtio _ vs vnew with "Hdev Hv") as "[Hdev' Hv']".
      (* the protocol step is an ACCESSOR over the permit channel: it hands
         out the completing request's PENDING token and owes the SPENT one *)
      iMod (virtio_proto_step γd vs h vnew w Hdisk with "Hlease")
        as (kq wr old nc lo tf hist)
           "(%Hwr & %Hsnapw & %Hho & %Htf & %Hlo & Hold & Hrel & Hpend & Hback)".
      (* the post-completion image, in the form the tie must move to: the
         IDENTITY, because every sector landed at its own earlier step *)
      assert (Hpost : wr_apply None (v_disk (dvirtio d)) = v_disk vnew)
        by (rewrite Hv Hwr; reflexivity).
      (* THE CLIENT'S VIEW SHIFT, at the image the machine is moving FROM;
         it lands the crash predicate at [wr_apply wr] of it -- the identity.
         [state_interp]'s started-generations auth goes in at
         [n = gen_id + 1] (phase C2b/D1): the channel is held at THIS
         thread's [gen_id], so every permit in it was authored by this era.
         The permit is a mask-[∅] fupd and three invariants are open, so
         shrink the mask around it and restore. *)
      iInv "Hcinv" as "HP" "Hcclose".
      iMod (fupd_mask_subseteq ∅) as "Hmclose"; [set_solver|].
      iMod (perm_consume_kq gen_id (dn_perm γd) kq wr (v_disk (dvirtio d)) n
              with "Hpbody Hpend Hsa [//] Htie HP")
        as "(Hpbody & Hdone & Hsa & Htie & HP)".
      iMod "Hmclose" as "_".
      iEval (rewrite Hpost) in "Htie".
      iMod ("Hcclose" with "HP") as "_".
      (* ================================================================ *)
      (* THE INDEX BUMP'S APPEND (A6.48 ruling 4, A6.126 §6).  The write   *)
      (* set is exactly the index word's snapshot; it goes in as ONE       *)
      (* message authored by [disk_agent] through the RELEASE-WINDOW gate  *)
      (* ([TsoCtxStore.ledger_store_rel_map_ok]), which re-mints the window     *)
      (* with its history extended by this append's position.  The record  *)
      (* the handler will read was written by the EARLIER transactions:    *)
      (* its sealed cells come out of the protocol and go back as          *)
      (* [ledger_le] at the append's position, their hidden stamps bounded  *)
      (* by the log's length BEFORE the append ([phys_map_ledger_le]).     *)
      (* ================================================================ *)
      iAssert (|==> gen_heap_interp (w ∪ m) ∗
                 tso_interp_of riscv_eraGS img (w ∪ m) log'
                   (vstep disk_agent (length log') log' V) ∗
                 (∃ q : nat,
                    ⌜forall k q' g, hist !! k = Some (q', g) -> (q' < q)%nat⌝ ∗
                    ([∗ map] a ↦ b ∈ old, ledger_le a b q) ∗
                    TsoCtx.rel_cells (used_idx_pa (v_cfg vs)) 2 (DfracOwn 1) disk_agent lo tf
                      (nth_byte (wrap16 0)) (nth_byte (wrap16 (S nc)))
                      (hist ++ [(q, nth_byte (wrap16 (S nc)))])))%I
        with "[Hmem Htso Hold Hrel]" as ">(Hmem & Htso & Hnew)".
      { iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
        iDestruct (tso_interp_of_bound with "Htso") as %Hbnd.
        destruct Hlog as [[Hw Hl] | [Hne Hl]].
        - (* the completion always writes the index word: never empty *)
          exfalso. subst w.
          assert (Hs : snap_of (used_idx_pa (v_cfg vs)) 2 (wrap16 (S nc))
                         !! pa_add (used_idx_pa (v_cfg vs)) 0 = Some (nth_byte (wrap16 (S nc)) 0))
            by (apply write_bytes_lookup; lia).
          rewrite <- Hsnapw in Hs. rewrite lookup_empty in Hs. discriminate Hs.
        - (* the real append, at the [disk_agent] author *)
          subst log'.
          set (V' := vstep disk_agent
                       (length (log ++ [TsoMemPa.PWMsg w disk_agent])%list)
                       (log ++ [TsoMemPa.PWMsg w disk_agent])%list V).
          assert (Hpin' : forall h, (NCPU <= h)%nat ->
                    V' h = length (log ++ [TsoMemPa.PWMsg w disk_agent])%list).
          { intros h' Hh. rewrite /V' /vstep. case_decide as Hd; [done|].
            destruct (lt_dec h' NCPU) as [|Hge]; [lia|done]. }
          assert (Htvmono : forall c : CPU,
                    (V (hart_agent c) <= V' (hart_agent c))%nat).
          { intros c. rewrite /V' /vstep. case_decide as Hd.
            - exfalso. pose proof (fin_to_nat_lt c).
              rewrite /hart_agent /disk_agent in Hd. lia.
            - destruct (lt_dec (hart_agent c) NCPU) as [|Hge]; [lia|].
              exfalso. pose proof (fin_to_nat_lt c).
              rewrite /hart_agent in Hge. lia. }
          assert (Htvtop : forall c : CPU,
                    (V' (hart_agent c) <= length
                       (log ++ [TsoMemPa.PWMsg w disk_agent])%list)%nat).
          { intros c. rewrite /V' /vstep. case_decide as Hd; [lia|].
            destruct (lt_dec (hart_agent c) NCPU) as [|Hge].
            - rewrite length_app /=. have := Hbnd (hart_agent c). lia.
            - lia. }
          rewrite (tso_interp_of_at_gs riscv_eraGS img m log V
                     (gr 0%fin) d Hpin).
          (* the window in minted form: minted now if this is the first completion *)
          iAssert (|==> tso_interp_at riscv_eraGS (gs_of img m log V (gr 0%fin) d) ∗
                     gen_heap_interp m ∗
                     TsoCtx.rel_cells (used_idx_pa (v_cfg vs)) 2 (DfracOwn 1) disk_agent lo tf
                       (nth_byte (wrap16 0)) (nth_byte (wrap16 nc)) hist)%I
            with "[Htso Hmem Hrel]" as ">(Htso & Hmem & Hrel)".
          { iDestruct "Hrel" as "[[%Hnil Hpre] | Hrel]"; last by iFrame.
            assert (Hnc0 : nc = 0%nat)
              by (destruct Hho as [Hlen _]; rewrite Hnil in Hlen; cbn in Hlen; lia).
            subst hist. rewrite Hnc0.
            iEval (rewrite /TsoCtx.rel_pre_cells) in "Hpre".
            iMod (TsoCtxStore.ledger_rpay_mint (gs_of img m log V (gr 0%fin) d)
                    (used_idx_pa (v_cfg vs)) 2 disk_agent lo tf (nth_byte (wrap16 0))
                    ltac:(lia) Htf Hlo with "Hmem Htso Hpre") as "(Hmem & Htso & Hcells)".
            iModIntro. iFrame "Htso Hmem". rewrite /TsoCtx.rel_cells.
            iApply (big_sepL_impl with "Hcells"). iIntros "!>" (k j _) "H".
            iExists (tf j). iExact "H". }
          (* every history position is a log position: under the append *)
          iAssert (⌜forall k q' g, hist !! k = Some (q', g) -> (q' < S (length log))%nat⌝)%I
            as %Hqgt.
          { rewrite /TsoCtx.rel_cells.
            iDestruct (big_sepL_lookup _ (seq 0 2) 0%nat 0%nat with "Hrel") as (tc) "Hc0";
              [reflexivity|].
            iDestruct (TsoCtxStore.ledger_rpay_ok with "Htso Hc0") as %Hok0.
            iPureIntro. intros k q' g Hk.
            destruct Hok0 as (_ & _ & _ & _ & H1b & _). cbn in H1b.
            destruct (H1b q' g (elem_of_list_lookup_2 _ _ _ Hk)) as (_ & i0 & mg & -> & Hlk & _).
            apply lookup_lt_Some in Hlk. lia. }
          (* THE RECORD'S CELLS: stamped by earlier appends, so under the log *)
          iDestruct (phys_map_ledger_le (gs_of img m log V (gr 0%fin) d) old
                       with "Hmem Htso Hold") as "(Hmem & Htso & Hold)".
          iEval (cbn [gs_of glog]) in "Hold".
          (* the append: the index word alone, through the window gate *)
          iMod (TsoCtxStore.ledger_store_rel_map_ok
                  (gs_of img m log V (gr 0%fin) d)
                  (gs_of img (w ∪ m)
                     (log ++ [TsoMemPa.PWMsg w disk_agent])%list V'
                     (gr 0%fin) d)
                  disk_agent ∅ w (used_idx_pa (v_cfg vs)) 2 (wrap16 nc) (wrap16 (S nc))
                  lo tf (nth_byte (wrap16 0)) hist
                  ltac:(cbn; lia) ltac:(rewrite Hsnapw; reflexivity)
                  ltac:(rewrite dom_empty_L Hsnapw !dom_snap_of difference_diag_L; reflexivity)
                  eq_refl eq_refl eq_refl
                  Htvmono Htvtop with "Hmem Htso [] Hrel")
            as "(Hmem & Htso & _ & _ & Hrel)"; [by rewrite big_sepM_empty|].
          iModIntro. iFrame "Hmem".
          rewrite -(tso_interp_of_at_gs riscv_eraGS img (w ∪ m)
                      (log ++ [TsoMemPa.PWMsg w disk_agent])%list V'
                      (gr 0%fin) d Hpin').
          iFrame "Htso". iEval (cbn [gs_of glog]) in "Hrel".
          iExists (S (length log)).
          iSplitR; [iPureIntro; exact Hqgt|].
          iSplitL "Hold".
          { iApply (big_sepM_impl with "Hold"). iIntros "!>" (a b _) "H".
            iApply (ledger_le_mono _ _ (length log)); [lia | iExact "H"]. }
          iEval (change (N.to_nat 2) with 2%nat) in "Hrel".
          rewrite /TsoCtx.rel_cells.
          iApply (big_sepL_mono with "Hrel"). iIntros (k j _) "H".
          iExists (S (length log)). iExact "H". }
      iDestruct "Hnew" as (q) "(%Hqgt & Hnew & Hrel)".
      iMod ("Hback" $! q with "[%] Hdone Hnew Hrel") as "Hlease'"; [exact Hqgt|].
      iMod ("Hclose" with "[Hv' Hlease']") as "_".
      { iNext. iExists vnew. iFrame.
        iPureIntro. exact (virtio_complete_step_isr_ok vs h vnew w Hvok Hdisk). }
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      assert (Hdk : v_disk vnew = v_disk (dvirtio d))
        by (rewrite Hv; exact (virtio_complete_step_disk vs h vnew w Hdisk)).
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
      rewrite <- Hdk in Hdview.
      iSplitL "Hdauth".
      { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
      iFrame "Htie Hsa Htso".
      iApply "IH".
    - (* ONE CACHED SECTOR DRAINS -- THE COMMIT INSTANT
         (claude-notes/completed/sector-atomic-disk.md, restated for the
         write cache).  A 512-byte sector is atomic and a 1024-byte block is
         not, so this is the ONLY step in the whole machine at which the
         durable image MOVES: the client's per-sector view shift runs here,
         on the crash predicate, at the instant those 512 bytes become
         durable.  A power cycle between two of these leaves a half-written
         block, which is exactly what real hardware does and what the FS
         layer must survive.

         THE STEP READS NOTHING OFF THE BUS -- the bytes are the device's
         own, out of its cache -- so this arm carries NO memory view and
         needs no DMA lease at all; the byte memory is untouched (the step's
         [m' = m]) and so are the used ring, the ISR and the consumed index.
         The request is still in flight until its completion, two arms up.

         The completion arm above still opens [crashN] too, but it spends the
         sequential permit's LEAF, which is indexed at [None] and is
         therefore the IDENTITY on the fixed auth ([wr_apply None dk = dk]) --
         that leaf is where a READ's client receipt lives and what keeps that
         arm direction-agnostic (sector-atomic-disk.md §6e). *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      (* A6.11: this arm's write set is [∅], so the log disjunct forces
         [log' = log] and the memory is untouched -- the bundle comes
         straight back ([RiscvExec.tso_interp_of_disk_idle] pays the disk
         agent's pinned view). *)
      destruct Hlog as [[_ ->] | [Hne _]]; [| exfalso; exact (Hne eq_refl)].
      rewrite (left_id_L (∅ : gmap Arch.pa (bv 8)) union).
      rewrite Hv in Hdrain.
      iMod (dev_interp_update_virtio _ vs vnew with "Hdev Hv") as "[Hdev' Hv']".
      iEval (rewrite -Himg Hv) in "Hdur".
      iMod (virtio_proto_drain_step γd vs s vnew Hdrain with "Hdur Hlease")
        as (kq wr i todo) "(%Hitd & %Hwr & Hpend & Hback)".
      assert (Hpost : wr_apply (wr_sector wr i) (v_disk (dvirtio d))
                      = v_disk vnew)
        by (rewrite Hv Hwr; reflexivity).
      iInv "Hcinv" as "HP" "Hcclose".
      iMod (fupd_mask_subseteq ∅) as "Hmclose"; [set_solver|].
      (* CONSUME AND RE-DEPOSIT (sector-atomic-disk.md §6e): the branch the
         device took is spent and the RESIDUAL obligation for the remaining
         sectors goes straight back into the same cell.  The request's cell
         only reaches the done state at its completion. *)
      iMod (perm_step_kq gen_id (dn_perm γd) kq wr todo i
              (v_disk (dvirtio d)) n Hitd
              with "Hpbody Hpend Hsa [//] Htie HP")
        as "(Hpbody & Hdone & Hsa & Htie & HP)".
      iMod "Hmclose" as "_".
      iEval (rewrite Hpost) in "Htie".
      iMod ("Hcclose" with "HP") as "_".
      iDestruct ("Hback" with "Hdone") as "(Hdur' & Hlease')".
      iMod ("Hclose" with "[Hv' Hlease']") as "_".
      { iNext. iExists vnew. iFrame.
        iPureIntro. exact (virtio_drain_step_isr_ok vs s vnew Hvok Hdrain). }
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur'" as (dmap') "[Hdauth' %Hdv']".
      iEval (rewrite Himg) in "Hdauth'".
      iSplitL "Hdauth'".
      { iExists dmap'. iFrame "Hdauth'". iPureIntro. exact Hdv'. }
      iFrame "Htie Hsa".
      iSplitL "Htso"; [iApply (tso_interp_of_disk_idle with "Htso") |].
      iApply "IH".
    - (* The queue the driver published is MALFORMED, so the device may write
         anything anywhere.  This case is REFUTED, not handled: the lease's
         positive well-formedness obligation says the device is never in that
         position.  If the obligation were the old conditional one -- "if a
         step happens its writes are bounded" -- there would be nothing to
         refute it with, and a driver that misconfigured the queue would be
         verifiable.  Needing this refutation is exactly the pressure that
         makes well-formedness a driver obligation.  (The [Idle] stutter below
         does NOT weaken this: it is a separate constructor, and a malformed
         queue still admits THIS one.) *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      rewrite Hv in Hstall.
      iDestruct (virtio_proto_not_stalled m vs mv γd Hview with "Hmem Hlease")
        as %Hns.
      exfalso. congruence.
    - (* the gateway latches the DISK's interrupt level -- the disk's own
         source, so this is the disk thread's business and not the UART's *)
      (* A6.11: this arm's write set is [∅], so the log disjunct forces
         [log' = log] and the memory is untouched -- the bundle comes
         straight back ([RiscvExec.tso_interp_of_disk_idle] pays the disk
         agent's pinned view). *)
      destruct Hlog as [[_ ->] | [Hne _]]; [| exfalso; exact (Hne eq_refl)].
      rewrite (left_id_L (∅ : gmap Arch.pa (bv 8)) union).
      iInv "Hpinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (p) "(Hp & %Hpok & Harm)".
      iDestruct (dev_interp_agree_plic with "Hdev Hp") as %Hp.
      iMod (dev_interp_update_plic _ p p' with "Hdev Hp") as "[Hdev' Hp']".
      assert (Hlat : plic_latch p virtio_irq_id = Some p')
        by (rewrite <- Hp; exact Hlatch).
      pose proof (plic_latch_claimed p p' virtio_irq_id Hlat) as Hcl'.
      iMod ("Hclose" with "[Hp' Harm]") as "_".
      { iNext. iExists p'. iFrame "Hp'".
        iSplitR;
          [iPureIntro; exact (plic_ok_latch p p' virtio_irq_id Hlat Hpok)|].
        iApply (plic_slots_stable _ _ p p' (Hcl' (uart_irq_id Uart0))
                  (Hcl' (uart_irq_id Uart1))). iExact "Harm". }
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
      iSplitL "Hdauth".
      { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
      (* a latch moves only the PLIC: the FS tie is FRAMED *)
      iFrame "Htie Hsa".
      iSplitL "Htso"; [iApply (tso_interp_of_disk_idle with "Htso") |].
      iApply "IH".
    - (* the totality stutter (RiscvLang §3c) *)
      (* A6.11: this arm's write set is [∅], so the log disjunct forces
         [log' = log] and the memory is untouched -- the bundle comes
         straight back ([RiscvExec.tso_interp_of_disk_idle] pays the disk
         agent's pinned view). *)
      destruct Hlog as [[_ ->] | [Hne _]]; [| exfalso; exact (Hne eq_refl)].
      rewrite (left_id_L (∅ : gmap Arch.pa (bv 8)) union).
      iMod ("Hpclose" with "[Hpbody]") as "_"; [iApply bi.later_intro; iExact "Hpbody"|].
      iModIntro. iFrame "Hgr Hmem Hdev".
      iSplitL "Hdur"; [iExact "Hdur"|].
      iFrame "Htie Hsa".
      iSplitL "Htso"; [iApply (tso_interp_of_disk_idle with "Htso") |].
      iApply "IH".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE WIRE THREAD.  [dev_seip d h] is [plic_eip (dplic d) (plic_sctx  *)
  (*  h)] and [dev_meip d h] the same at [plic_mctx h] -- one PLIC context *)
  (*  per pin, and one [plic_step] arm per pin.  Both are read              *)
  (*  off the PHYSICAL device state the lifting rule hands over, so this   *)
  (*  proof needs NO agreement against [plic_frag] and therefore never     *)
  (*  opens [plicN] at all -- the old proof opened the device invariant     *)
  (*  here only to close it again.  [plic_inv] is still taken, to keep the  *)
  (*  three loops' interfaces uniform and to record that the wire's value   *)
  (*  is the PLIC's.                                                       *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_plic_loop (γu γu1 : uart_names) :
    gen_cert -∗ plic_inv γu γu1 -∗ wire_inv -∗
    mWP (PlicLoop : expr riscv_lang).
  Proof using .
    iIntros "#Hcert #Hpinv #Hwinv".
    iLöb as "IH".
    iApply (wp_plic_step with "Hcert").
    iIntros (gr m d) "(Hgr & Hmem & Hdev)".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iNext. iIntros (gr' Hstep).
    iMod "Hmask" as "_".
    (* ONE ARM PER PIN: the PLIC drives hart [c]'s S pin from context 2c+1 and
       its M pin from context 2c, and both cells are borrowed from
       [wire_inv] -- whose contents are existential, which is exactly why the
       second arm costs nothing here. *)
    destruct Hstep as [c|c].
    - iInv "Hwinv" as ">Hwbody" "Hwclose".
      iDestruct "Hwbody" as (seip meip) "Hwires".
      iDestruct (gregs_interp_acc_at c with "Hgr") as "[Hrc Hback]".
      iDestruct (big_sepS_delete _ _ c with "Hwires") as "[[Hwc Hmc] Hwrest]";
        [ apply elem_of_fin_to_set |].
      iMod (reg_update_at c (gr c) sig_seip (seip c)
              (bool_to_bit (dev_seip d (fin_to_nat c))) with "Hrc Hwc")
        as "[Hrc' Hwc']".
      iDestruct ("Hback" with "Hrc'") as "Hgr'".
      set (seip' := fun c' : CPU =>
             if decide (c' = c) then bool_to_bit (dev_seip d (fin_to_nat c))
             else seip c').
      iMod ("Hwclose" with "[Hwc' Hmc Hwrest]") as "_".
      { iNext. iExists seip', meip.
        iApply (big_sepS_delete _ _ c); [ apply elem_of_fin_to_set |].
        iSplitL "Hwc' Hmc".
        { rewrite /seip' decide_True //. iFrame. }
        iApply (big_sepS_mono with "Hwrest").
        intros c' Hc'. apply elem_of_difference in Hc' as [_ Hne].
        rewrite /seip' decide_False; [ done | ].
        intros ->. apply Hne, elem_of_singleton. reflexivity. }
      iModIntro. iFrame "Hgr' Hmem Hdev". iApply "IH".
    - iInv "Hwinv" as ">Hwbody" "Hwclose".
      iDestruct "Hwbody" as (seip meip) "Hwires".
      iDestruct (gregs_interp_acc_at c with "Hgr") as "[Hrc Hback]".
      iDestruct (big_sepS_delete _ _ c with "Hwires") as "[[Hwc Hmc] Hwrest]";
        [ apply elem_of_fin_to_set |].
      iMod (reg_update_at c (gr c) sig_meip (meip c)
              (bool_to_bit (dev_meip d (fin_to_nat c))) with "Hrc Hmc")
        as "[Hrc' Hmc']".
      iDestruct ("Hback" with "Hrc'") as "Hgr'".
      set (meip' := fun c' : CPU =>
             if decide (c' = c) then bool_to_bit (dev_meip d (fin_to_nat c))
             else meip c').
      iMod ("Hwclose" with "[Hwc Hmc' Hwrest]") as "_".
      { iNext. iExists seip, meip'.
        iApply (big_sepS_delete _ _ c); [ apply elem_of_fin_to_set |].
        iSplitL "Hwc Hmc'".
        { rewrite /meip' decide_True //. iFrame. }
        iApply (big_sepS_mono with "Hwrest").
        intros c' Hc'. apply elem_of_difference in Hc' as [_ Hne].
        rewrite /meip' decide_False; [ done | ].
        intros ->. apply Hne, elem_of_singleton. reflexivity. }
      iModIntro. iFrame "Hgr' Hmem Hdev". iApply "IH".
  Qed.
End DevLoops.
