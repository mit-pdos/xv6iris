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
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap own.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel PlicPlan.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
(* re-import the model AFTER Base so the model's names (read_kind/Read_plain/
   write_kind/...) win over SailStdpp's homonyms -- same order as WpLoad.v. *)
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras RiscvFetchExec.
Require Import WireInv WpVirtio.
(* the disk's DMA lease is now carried in the KEYED driver protocol
   ([virtio_proto], VirtioProto.v) rather than as the bare [virtio_lease];
   these two are required AFTER SailStdpp.Base/Values above, exactly like
   WpVirtio, so their (RiscvPtsto-mirroring) elaboration is unaffected. *)
Require Import DiskPtsto VirtioProto.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1  device-fabric ghost bridges.                                       *)
(* ===================================================================== *)

Section DevGhost.
  Context `{!riscvGS Σ}.

  Lemma dev_interp_agree d u p :
    dev_interp d -∗ uart_frag u -∗ plic_frag p -∗ ⌜duart d = u /\ dplic d = p⌝.
  Proof.
    iIntros "(Hua & Hpa & _) Hu Hp".
    iDestruct (uart_agree with "Hua Hu") as %->.
    iDestruct (plic_agree with "Hpa Hp") as %->.
    done.
  Qed.


  (* ... and the per-device halves of that agreement, for the proofs that hold
     only ONE device's fragment (each device thread opens only its own
     invariant, so it never has the other devices' fragments to hand). *)
  Lemma dev_interp_agree_uart d u :
    dev_interp d -∗ uart_frag u -∗ ⌜duart d = u⌝.
  Proof.
    iIntros "(Hua & _ & _) Hu".
    by iDestruct (uart_agree with "Hua Hu") as %->.
  Qed.

  Lemma dev_interp_agree_plic d p :
    dev_interp d -∗ plic_frag p -∗ ⌜dplic d = p⌝.
  Proof.
    iIntros "(_ & Hpa & _) Hp".
    by iDestruct (plic_agree with "Hpa Hp") as %->.
  Qed.

  (* uart-only update (the plic component rides along) *)
  Lemma dev_interp_update_uart d u u' :
    dev_interp d -∗ uart_frag u ==∗ dev_interp (set_duart d u') ∗ uart_frag u'.
  Proof.
    iIntros "(Hua & Hpa & Hva) Hu".
    iMod (uart_update with "Hua Hu") as "[$ $]".
    rewrite /set_duart /dev_interp /=. by iFrame "Hpa Hva".
  Qed.

  Lemma dev_interp_update_plic d p p' :
    dev_interp d -∗ plic_frag p ==∗ dev_interp (set_dplic d p') ∗ plic_frag p'.
  Proof.
    iIntros "(Hua & Hpa & Hva) Hp".
    iMod (plic_update with "Hpa Hp") as "[$ $]".
    rewrite /set_dplic /dev_interp /=. by iFrame "Hua Hva".
  Qed.
End DevGhost.

(* ===================================================================== *)
(* §2  MMIO transaction leaves.                                           *)
(* ===================================================================== *)

(* the UART registers live at [uart_base + off]; xv6 uses off 0..5 *)
Definition uart_pa (off : Z) : Arch.pa := Z_to_bv 64 (uart_base + off).

Lemma uint_uart_pa off : 0 <= off < uart_size -> uint (uart_pa off) = uart_base + off.
Proof.
  intros Hoff. unfold uart_size in Hoff.
  unfold uart_pa, uint, MachineWord.word_to_N. unfold get_word.
  rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small.
  2:{ assert (Hm : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
      rewrite Hm. unfold uart_base in *. lia. }
  apply Z2N.id. unfold uart_base in *. lia.
Qed.

(* A UART REGISTER IS IN THE DEVICE PMA CLASS: the whole window sits inside
   the platform's MMIO band ([RiscvPtsto.mmio_base, + mmio_size)), which is
   what [RiscvFetchExec.pma_allows_io] asks of its appliers.  (It used to be
   the strictly weaker "the access does not wrap", which was all the
   all-addresses [pma_allows_all] needed; the real table grants R/W here and
   nothing outside its three regions.) *)
Lemma uart_pa_access_io off n :
  0 <= off < uart_size -> 1 <= n <= 4096 ->
  pma_io_access (uart_pa off) n.
Proof.
  intros Hoff Hn.
  apply (pma_access_io _ _ uart_base (uart_base + uart_size));
    [ rewrite (uint_uart_pa off Hoff); lia
    | rewrite (uint_uart_pa off Hoff); lia
    | reflexivity | reflexivity | exact Hn ].
Qed.

Lemma dev_addr_uart off : 0 <= off < uart_size -> dev_addr (uart_pa off) = true.
Proof.
  intros Hoff. unfold dev_addr. apply Z.ltb_lt.
  rewrite (uint_uart_pa off Hoff). unfold uart_base, uart_size, dev_bound in *. lia.
Qed.

(* one UART MMIO transaction, at the fabric level *)
Lemma dev_read_uart (d : dev_state) (off : Z) (b : bv 8) (u' : uart_state) :
  0 <= off < uart_size ->
  uart_read (duart d) off = Some (b, u') ->
  dev_read d (uart_pa off) 1 = Some (b, set_duart d u').
Proof.
  intros Hoff Hrd. unfold dev_read.
  rewrite (uint_uart_pa off Hoff).
  assert (Hin : in_uart (uart_base + off) = true).
  { unfold in_uart. apply andb_true_intro.
    split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
  rewrite Hin.
  replace (uart_base + off - uart_base) with off by lia.
  rewrite Hrd. reflexivity.
Qed.

Lemma dev_write_uart (d : dev_state) (off : Z) (b : bv 8) (u' : uart_state) :
  0 <= off < uart_size ->
  uart_write (duart d) off b = Some u' ->
  dev_write d (uart_pa off) 1 b = Some (set_duart d u').
Proof.
  intros Hoff Hwr. unfold dev_write.
  rewrite (uint_uart_pa off Hoff).
  assert (Hin : in_uart (uart_base + off) = true).
  { unfold in_uart. apply andb_true_intro.
    split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
  rewrite Hin.
  replace (uart_base + off - uart_base) with off by lia.
  rewrite Hwr. reflexivity.
Qed.

(* the UART window is disjoint from the Sail-internal CLINT/SIG windows and
   (given the boot config) HTIF, so a UART access reaches the interpreter *)
Lemma uart_pa_not_in_clint off : 0 <= off < uart_size -> not_in_clint (uart_pa off).
Proof.
  intros Hoff. right.
  rewrite (uint_uart_pa off Hoff).
  assert (uint plat_clint_base + uint plat_clint_size = 34340864) as ->
    by (vm_compute; reflexivity).
  unfold uart_base, uart_size in *. lia.
Qed.

Lemma uart_pa_not_in_sig off : 0 <= off < uart_size -> not_in_sig (uart_pa off).
Proof.
  intros Hoff. right.
  rewrite (uint_uart_pa off Hoff).
  assert (uint plat_sig_base + uint plat_sig_size = 201326624) as ->
    by (vm_compute; reflexivity).
  unfold uart_base, uart_size in *. lia.
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
  exec (pmaCheck (Physaddr pa) 1 (Load Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Hread.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread |- *.
  rewrite (is_aligned_paddr_1 pa). cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_returnM.
Qed.

(* pmaCheck for a 1-byte Store Data in a writable device PMA region *)
Lemma exec_pmaCheck_dev_store_1 (pa : Arch.pa) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr pa) 1 (Store Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Hwrite.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite (is_aligned_paddr_1 pa). cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §3  the device threads: [UartLoop]/[DiskLoop]/[PlicLoop] each run       *)
(*     forever under their own invariant (+ the wire invariant, for the    *)
(*     wire thread).                                                       *)
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

(*  The UART's ghost names travel together in ONE record, so [dev_inv] and
    every client-facing resource take a single [γ : uart_names] rather than a
    fistful of gnames:

      un_acc   mono_list over [uart_acc]  -- the persistent accepted-byte
               history.  Grows only on a THR push; a lower bound
               [uart_sent γ l] is a permanent record that [l] was accepted.
      un_out   mono_list over [u_out]     -- the transmitted prefix.  Its
               lower bound is what carries a THRE observation forward across
               later device steps (see [uart_tx_still_empty], DevModel.v).
      un_tx    ghost_var halves over the accepted trace -- EXCLUSIVE
               ownership of the transmitter (see [uart_tx_own] below).
      un_dlab  dfrac_agree over DLAB -- freezable to a persistent fact.       *)
Record uart_names := UartNames {
  un_acc  : gname;
  un_out  : gname;
  un_tx   : gname;
  un_dlab : gname;
}.

Class uartGhostG (Σ : gFunctors) := UartGhostG {
  uart_ghost_listG :: inG Σ (mono_listR (leibnizO (bv 8)));
  uart_ghost_txG :: ghost_varG Σ (list (bv 8));
  uart_ghost_dlabG :: inG Σ (dfrac_agreeR (leibnizO bool));
}.

Definition uartGhostΣ : gFunctors :=
  #[ GFunctor (mono_listR (leibnizO (bv 8)));
     ghost_varΣ (list (bv 8));
     GFunctor (dfrac_agreeR (leibnizO bool)) ].

Global Instance subG_uartGhostG Σ : subG uartGhostΣ Σ -> uartGhostG Σ.
Proof. solve_inG. Qed.

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
  Proof. rewrite /uart_sent. apply _. Qed.
  Global Instance uart_sent_timeless γ l : Timeless (uart_sent γ l).
  Proof. rewrite /uart_sent. apply _. Qed.
  (* the transmitted-prefix authority yields its own lower bound, exactly as
     [uart_ghosts_alloc] peels the accepted-trace one off [uart_sent_auth].
     A boot client needs it because [SpecMain]'s precondition asks for
     [uart_out_lb γ l0] beside the transmitter token, and the authority is on
     its way into [dev_inv_body] -- there is no other source. *)
  Lemma uart_out_auth_lb (γ : uart_names) (u : uart_state) :
    uart_out_auth γ u ⊢ uart_out_auth γ u ∗ uart_out_lb γ (u_out u).
  Proof.
    rewrite /uart_out_auth /uart_out_lb {1}mono_list_auth_lb_op own_op.
    iIntros "[$ $]".
  Qed.

  Global Instance uart_out_lb_persistent γ l : Persistent (uart_out_lb γ l).
  Proof. rewrite /uart_out_lb. apply _. Qed.
  Global Instance uart_out_lb_timeless γ l : Timeless (uart_out_lb γ l).
  Proof. rewrite /uart_out_lb. apply _. Qed.
  Global Instance uart_dlab_off_persistent γ : Persistent (uart_dlab_off γ).
  Proof. rewrite /uart_dlab_off /uart_dlab_is. apply _. Qed.
  Global Instance uart_dlab_is_timeless γ dq b : Timeless (uart_dlab_is γ dq b).
  Proof. rewrite /uart_dlab_is. apply _. Qed.
  Global Instance uart_sent_auth_timeless γ u : Timeless (uart_sent_auth γ u).
  Proof. rewrite /uart_sent_auth. apply _. Qed.
  Global Instance uart_out_auth_timeless γ u : Timeless (uart_out_auth γ u).
  Proof. rewrite /uart_out_auth. apply _. Qed.

  (* -- accepted trace -- *)
  Lemma uart_sent_get γ u :
    uart_sent_auth γ u -∗ uart_sent_auth γ u ∗ uart_sent γ (uart_acc u).
  Proof.
    iIntros "Ha". rewrite /uart_sent_auth /uart_sent.
    iEval (rewrite {1}mono_list_auth_lb_op) in "Ha".
    iDestruct "Ha" as "[$ $]".
  Qed.


  Lemma uart_sent_update γ u u' :
    uart_acc u `prefix_of` uart_acc u' ->
    uart_sent_auth γ u ==∗ uart_sent_auth γ u' ∗ uart_sent γ (uart_acc u').
  Proof.
    iIntros (Hpre) "Ha". rewrite /uart_sent_auth.
    iMod (own_update _ _ (●ML (uart_acc u' : list (leibnizO (bv 8))))
            with "Ha") as "Ha"; [by apply mono_list_update|].
    iDestruct (uart_sent_get with "Ha") as "[$ $]". done.
  Qed.

  Lemma uart_sent_auth_stable γ u u' :
    uart_acc u' = uart_acc u -> uart_sent_auth γ u -∗ uart_sent_auth γ u'.
  Proof. iIntros (Heq) "Ha". rewrite /uart_sent_auth Heq. done. Qed.

  (* -- transmitted prefix -- *)
  Lemma uart_out_get γ u :
    uart_out_auth γ u -∗ uart_out_auth γ u ∗ uart_out_lb γ (u_out u).
  Proof.
    iIntros "Ha". rewrite /uart_out_auth /uart_out_lb.
    iEval (rewrite {1}mono_list_auth_lb_op) in "Ha".
    iDestruct "Ha" as "[$ $]".
  Qed.

  Lemma uart_out_prefix γ u l :
    uart_out_auth γ u -∗ uart_out_lb γ l -∗ ⌜ l `prefix_of` u_out u ⌝.
  Proof.
    iIntros "Ha Hl". rewrite /uart_out_auth /uart_out_lb.
    by iDestruct (own_valid_2 with "Ha Hl") as %?%mono_list_both_valid_L.
  Qed.

  Lemma uart_out_update γ u u' :
    u_out u `prefix_of` u_out u' ->
    uart_out_auth γ u ==∗ uart_out_auth γ u' ∗ uart_out_lb γ (u_out u').
  Proof.
    iIntros (Hpre) "Ha". rewrite /uart_out_auth.
    iMod (own_update _ _ (●ML (u_out u' : list (leibnizO (bv 8))))
            with "Ha") as "Ha"; [by apply mono_list_update|].
    iDestruct (uart_out_get with "Ha") as "[$ $]". done.
  Qed.

  Lemma uart_out_auth_stable γ u u' :
    u_out u' = u_out u -> uart_out_auth γ u -∗ uart_out_auth γ u'.
  Proof. iIntros (Heq) "Ha". rewrite /uart_out_auth Heq. done. Qed.

  (* -- exclusive transmitter -- *)

  (* the owner's view of the accepted trace is the real one *)
  Lemma uart_tx_own_agree γ u l :
    uart_tx_auth γ u -∗ uart_tx_own γ l -∗ ⌜ uart_acc u = l ⌝.
  Proof.
    iIntros "Ha Ho". rewrite /uart_tx_auth /uart_tx_own.
    by iDestruct (ghost_var_agree with "Ha Ho") as %?.
  Qed.

  (* pushing needs BOTH halves: this is what excludes a tokenless hart *)
  Lemma uart_tx_own_update γ u l u' :
    uart_tx_auth γ u -∗ uart_tx_own γ l ==∗
    uart_tx_auth γ u' ∗ uart_tx_own γ (uart_acc u').
  Proof.
    iIntros "Ha Ho". rewrite /uart_tx_auth /uart_tx_own.
    iMod (ghost_var_update_2 (uart_acc u') with "Ha Ho") as "[$ $]";
      [apply Qp.half_half|]. done.
  Qed.

  Lemma uart_tx_auth_stable γ u u' :
    uart_acc u' = uart_acc u -> uart_tx_auth γ u -∗ uart_tx_auth γ u'.
  Proof. iIntros (Heq) "Ha". rewrite /uart_tx_auth Heq. done. Qed.

  (* -- DLAB -- *)
  Lemma uart_dlab_agree γ u dq b :
    uart_dlab_auth γ u -∗ uart_dlab_is γ dq b -∗ ⌜ uart_dlab u = b ⌝.
  Proof.
    iIntros "Ha Hb". rewrite /uart_dlab_auth /uart_dlab_is.
    by iDestruct (own_valid_2 with "Ha Hb") as %[_ ?]%dfrac_agree_op_valid_L.
  Qed.

  Lemma uart_dlab_auth_stable γ u u' :
    uart_dlab u' = uart_dlab u -> uart_dlab_auth γ u -∗ uart_dlab_auth γ u'.
  Proof. iIntros (Heq) "Ha". rewrite /uart_dlab_auth Heq. done. Qed.

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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof. rewrite /uart_ghosts. apply _. Qed.

  (* a transition that moves no UART ghost quantity carries them all over *)
  Lemma uart_ghosts_stable γ u u' :
    uart_acc u' = uart_acc u ->
    u_out u' = u_out u ->
    uart_dlab u' = uart_dlab u ->
    uart_ghosts γ u -∗ uart_ghosts γ u'.
  Proof.
    iIntros (Ha Ho Hd) "(Hs & Hout & Htx & Hdl)". rewrite /uart_ghosts.
    iDestruct (uart_sent_auth_stable _ u u' Ha with "Hs") as "$".
    iDestruct (uart_out_auth_stable _ u u' Ho with "Hout") as "$".
    iDestruct (uart_tx_auth_stable _ u u' Ha with "Htx") as "$".
    iDestruct (uart_dlab_auth_stable _ u u' Hd with "Hdl") as "$".
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
  Definition dev_inv_body (γ : uart_names) (γd : disk_names) : iProp Σ :=
    (∃ (u : uart_state) (p : plic_state) (v : virtio_state),
       uart_frag u ∗ plic_frag p ∗ virtio_frag v ∗
       uart_ghosts γ u ∗ virtio_proto γd v ∗
       ⌜ plic_ok p ⌝ ∗ ⌜ virtio_isr_ok v ⌝)%I.

  Global Instance uart_frag_timeless u : Timeless (uart_frag u).
  Proof. rewrite /uart_frag. apply _. Qed.
  Global Instance plic_frag_timeless p : Timeless (plic_frag p).
  Proof. rewrite /plic_frag. apply _. Qed.
  Global Instance virtio_frag_timeless v : Timeless (virtio_frag v).
  Proof. rewrite /virtio_frag. apply _. Qed.
  Global Instance dev_inv_body_timeless γ γd : Timeless (dev_inv_body γ γd).
  Proof. rewrite /dev_inv_body. apply _. Qed.

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
  Definition uartN : namespace := devN .@ "uart".
  Definition plicN : namespace := devN .@ "plic".
  Definition diskN : namespace := devN .@ "disk".

  Definition uart_inv_body (γ : uart_names) : iProp Σ :=
    (∃ u : uart_state, uart_frag u ∗ uart_ghosts γ u)%I.

  Definition plic_inv_body : iProp Σ :=
    (∃ p : plic_state, plic_frag p ∗ ⌜ plic_ok p ⌝)%I.

  Definition disk_inv_body (γd : disk_names) : iProp Σ :=
    (∃ v : virtio_state,
       virtio_frag v ∗ virtio_proto γd v ∗ ⌜ virtio_isr_ok v ⌝)%I.

  Global Instance uart_inv_body_timeless γ : Timeless (uart_inv_body γ).
  Proof. rewrite /uart_inv_body. apply _. Qed.
  Global Instance plic_inv_body_timeless : Timeless plic_inv_body.
  Proof. rewrite /plic_inv_body. apply _. Qed.
  Global Instance disk_inv_body_timeless γd : Timeless (disk_inv_body γd).
  Proof. rewrite /disk_inv_body. apply _. Qed.

  Definition uart_inv (γ : uart_names) : iProp Σ := inv uartN (uart_inv_body γ).
  Definition plic_inv : iProp Σ := inv plicN plic_inv_body.
  Definition disk_inv (γd : disk_names) : iProp Σ := inv diskN (disk_inv_body γd).

  Global Instance uart_inv_persistent γ : Persistent (uart_inv γ).
  Proof. rewrite /uart_inv. apply _. Qed.
  Global Instance plic_inv_persistent : Persistent plic_inv.
  Proof. rewrite /plic_inv. apply _. Qed.
  Global Instance disk_inv_persistent γd : Persistent (disk_inv γd).
  Proof. rewrite /disk_inv. apply _. Qed.

  Lemma uart_inv_alloc E γ : uart_inv_body γ ={E}=∗ uart_inv γ.
  Proof. iIntros "Hbody". rewrite /uart_inv. by iApply inv_alloc. Qed.
  Lemma plic_inv_alloc E : plic_inv_body ={E}=∗ plic_inv.
  Proof. iIntros "Hbody". rewrite /plic_inv. by iApply inv_alloc. Qed.
  Lemma disk_inv_alloc E γd : disk_inv_body γd ={E}=∗ disk_inv γd.
  Proof. iIntros "Hbody". rewrite /disk_inv. by iApply inv_alloc. Qed.

  (* The device invariant as a client-facing, duplicable proposition: the
     BUNDLE of the three per-device invariants.  Same name and same arguments
     as before the split, so every client spec in the tree is unchanged --
     what changed is only that a proof holding it destructs the bundle and
     opens the one sub-invariant it needs.  The device state is shared between
     the device threads and every CPU that touches UART/PLIC/virtio MMIO, so
     NO proof may hold [uart_frag]/[plic_frag]/[virtio_frag] across a step: a
     client threads [dev_inv] and borrows the fragment by opening the relevant
     half around the access. *)
  Definition dev_inv (γ : uart_names) (γd : disk_names) : iProp Σ :=
    (uart_inv γ ∗ plic_inv ∗ disk_inv γd)%I.

  Global Instance dev_inv_persistent γ γd : Persistent (dev_inv γ γd).
  Proof. rewrite /dev_inv. apply _. Qed.

  (* the three projections out of the bundle.  A leaf that borrows the fabric
     takes [dev_inv] (unchanged statement) and projects the ONE half it
     touches; the projections are wands out of a persistent premise, so a
     leaf holding [dev_inv] in its intuitionistic context keeps it. *)
  Lemma dev_inv_uart γ γd : dev_inv γ γd -∗ uart_inv γ.
  Proof. iIntros "(#H & _ & _)". iExact "H". Qed.
  Lemma dev_inv_plic γ γd : dev_inv γ γd -∗ plic_inv.
  Proof. iIntros "(_ & #H & _)". iExact "H". Qed.
  Lemma dev_inv_disk γ γd : dev_inv γ γd -∗ disk_inv γd.
  Proof. iIntros "(_ & _ & #H)". iExact "H". Qed.

  (* ... and the bundle allocation, at the EXISTING signature: the old
     ∃-triple body is split into the three per-device bodies. *)
  Lemma dev_inv_alloc E γ γd : dev_inv_body γ γd ={E}=∗ dev_inv γ γd.
  Proof.
    iIntros "Hbody". rewrite /dev_inv_body.
    iDestruct "Hbody" as (u p v) "(Hu & Hp & Hv & Hg & Hproto & %Hpok & %Hvok)".
    iMod (uart_inv_alloc E γ with "[Hu Hg]") as "#Huinv".
    { iExists u. iFrame "Hu Hg". }
    iMod (plic_inv_alloc E with "[Hp]") as "#Hpinv".
    { iExists p. iFrame "Hp". iPureIntro. exact Hpok. }
    iMod (disk_inv_alloc E γd with "[Hv Hproto]") as "#Hdinv".
    { iExists v. iFrame "Hv Hproto". iPureIntro. exact Hvok. }
    iModIntro. rewrite /dev_inv. iFrame "Huinv Hpinv Hdinv".
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
  Lemma uart_ghosts_alloc (u : uart_state) :
    ⊢ |==> ∃ γ, uart_sent_auth γ u ∗ uart_out_auth γ u ∗
                uart_tx_auth γ u ∗ uart_dlab_auth γ u ∗
                uart_tx_own γ (uart_acc u) ∗ uart_sent γ (uart_acc u) ∗
                uart_dlab_is γ (DfracOwn (1/2)) (uart_dlab u).
  Proof.
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
    iModIntro. iExists (UartNames γa γb γc γd).
    rewrite /uart_sent_auth /uart_out_auth /uart_tx_auth /uart_tx_own
            /uart_dlab_auth /uart_dlab_is /uart_sent /=.
    iFrame "Ha Hb Hc1 Hd1 Hc2 Hsent Hd2".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE UART THREAD.  Opens [uartN] for the tx/rx arms and [plicN] for  *)
  (*  the latch arm -- never both, because no single UART transition      *)
  (*  touches both halves.                                               *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_uart_loop γ Φ :
    gen_cert -∗ uart_inv γ -∗ plic_inv -∗
    WP (UartLoop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hcert #Huinv #Hpinv".
    iLöb as "IH".
    iApply (wp_uart_step with "Hcert").
    iIntros (gr m d) "(Hgr & Hmem & Hdev)".
    (* No invariant is opened until the arm is known: each arm then opens
       exactly the one half of the fabric it moves. *)
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iNext. iIntros (d' Hstep).
    iMod "Hmask" as "_".
    destruct Hstep as [b u' Htx0 | b u' Hrx | p' Hirq Hlatch |].
    - (* a byte leaves the tx FIFO: it moves from the head of [u_tx] to the
         tail of [u_out], so the accepted trace is UNCHANGED. *)
      iInv "Huinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (u) "(Hu & Hg)".
      iDestruct (dev_interp_agree_uart with "Hdev Hu") as %Hu.
      rewrite Hu in Htx0.
      iMod (dev_interp_update_uart _ u u' with "Hdev Hu") as "[Hdev' Hu']".
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
      iMod ("Hclose" with "[Hu' Hacc Hout Htx Hdl]") as "_".
      { iNext. iExists u'. rewrite /uart_ghosts. iFrame. }
      iModIntro. iFrame "Hgr Hmem Hdev'". iApply "IH".
    - (* a byte arrives from the outside world: rx only, trace untouched *)
      iInv "Huinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (u) "(Hu & Hg)".
      iDestruct (dev_interp_agree_uart with "Hdev Hu") as %Hu.
      rewrite Hu in Hrx.
      iMod (dev_interp_update_uart _ u u' with "Hdev Hu") as "[Hdev' Hu']".
      (* rx touches neither the tx side nor LCR: every ghost is unchanged *)
      iDestruct (uart_ghosts_stable _ u u'
                   (uart_rx_push_acc _ b _ Hrx)
                   (uart_rx_push_out _ b _ Hrx)
                   (uart_rx_push_dlab _ b _ Hrx) with "Hg") as "Hg".
      iMod ("Hclose" with "[Hu' Hg]") as "_".
      { iNext. iExists u'. iFrame. }
      iModIntro. iFrame "Hgr Hmem Hdev'". iApply "IH".
    - (* the gateway latches the UART's interrupt level.  This is the ONE
         UART transition that touches the PLIC, and it touches nothing else,
         so only [plicN] is opened. *)
      iInv "Hpinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (p) "(Hp & %Hpok)".
      iDestruct (dev_interp_agree_plic with "Hdev Hp") as %Hp.
      iMod (dev_interp_update_plic _ p p' with "Hdev Hp") as "[Hdev' Hp']".
      iMod ("Hclose" with "[Hp']") as "_".
      { iNext. iExists p'. iFrame "Hp'". iPureIntro.
        apply (plic_ok_latch p p' uart_irq_id);
          [ rewrite <- Hp; exact Hlatch | exact Hpok ]. }
      iModIntro. iFrame "Hgr Hmem Hdev'". iApply "IH".
    - (* the totality stutter (RiscvLang §3c): nothing moved, so nothing has
         to be re-established and no invariant is opened at all. *)
      iModIntro. iFrame "Hgr Hmem Hdev". iApply "IH".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE DISK THREAD.  Opens [diskN] for the DMA/wild arms and [plicN]   *)
  (*  for the latch arm.                                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_disk_loop γd Φ :
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
    gen_cert -∗ crash_inv -∗ disk_inv γd -∗ plic_inv -∗
    WP (DiskLoop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Himg.
    iIntros "#Hcert #Hcinv #Hvinv #Hpinv".
    iLöb as "IH".
    iApply (wp_disk_step with "Hcert").
    (* the fourth component is the ERA's image auth ([wp_disk_step] hands it
       over because a DMA completion is the one step that moves [v_disk]): the
       latch and stutter arms FRAME it, and the completion arm passes it
       through [virtio_proto_step] (claude-notes/design/crash.md). *)
    iIntros (gr m d) "(Hgr & Hmem & Hdev & Hdur)".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iNext. iIntros (d' m' Hstep).
    iMod "Hmask" as "_".
    destruct Hstep as [mv vnew w Hview Hdisk | mv w Hview Hstall
                      | p' Hirq Hlatch |].
    - (* the disk completes a queued request.  This is the only step that
         touches the byte memory, and the ONLY thing that justifies it is the
         DMA lease inside the invariant: [virtio_proto_step] consumes the
         lease's ownership of the written bytes and hands the same lease back,
         because the write set provably lands inside it and misses the queue's
         control region (VirtioModel.virtio_dma_ok). *)
      iInv "Hvinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (vs) "(Hv & Hlease & %Hvok)".
      iDestruct (dev_interp_agree_virtio with "Hdev Hv") as %Hv.
      rewrite Hv in Hdisk.
      iMod (dev_interp_update_virtio _ vs vnew with "Hdev Hv") as "[Hdev' Hv']".
      (* the auth [wp_disk_step] handed over is at the ERA's gname; the
         fragments this invariant holds are at [dn_img γd] -- the same map,
         by [Himg]. *)
      iEval (rewrite -Himg Hv) in "Hdur".
      iMod (virtio_proto_step γd vs m mv vnew w Hview Hdisk
              with "Hmem Hdur Hlease") as "(Hmem' & Hdur' & Hperm & Hlease')".
      (* THE COMMIT INSTANT: the image has just changed, so the crash
         predicate is re-established here, by the permit the enqueuer
         deposited in the OUT slot (the identity, for a read or until the log
         lands).  This is the only opening of [crashN] in the tree. *)
      iInv "Hcinv" as "HP" "Hcclose".
      iMod ("Hperm" with "HP") as "HP".
      iMod ("Hcclose" with "HP") as "_".
      iMod ("Hclose" with "[Hv' Hlease']") as "_".
      { iNext. iExists vnew. iFrame.
        iPureIntro. exact (virtio_req_step_isr_ok vs mv vnew w Hvok Hdisk). }
      iModIntro. iFrame "Hgr Hmem' Hdev'".
      iDestruct "Hdur'" as (dmap') "[Hdauth' %Hdv']".
      iEval (rewrite Himg) in "Hdauth'".
      iSplitL "Hdauth'".
      { iExists dmap'. iFrame "Hdauth'". iPureIntro. exact Hdv'. }
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
      iInv "Hpinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (p) "(Hp & %Hpok)".
      iDestruct (dev_interp_agree_plic with "Hdev Hp") as %Hp.
      iMod (dev_interp_update_plic _ p p' with "Hdev Hp") as "[Hdev' Hp']".
      iMod ("Hclose" with "[Hp']") as "_".
      { iNext. iExists p'. iFrame "Hp'". iPureIntro.
        apply (plic_ok_latch p p' virtio_irq_id);
          [ rewrite <- Hp; exact Hlatch | exact Hpok ]. }
      iModIntro. iFrame "Hgr Hmem Hdev'".
      iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
      iSplitL "Hdauth".
      { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
      iApply "IH".
    - (* the totality stutter (RiscvLang §3c) *)
      iModIntro. iFrame "Hgr Hmem Hdev".
      iSplitL "Hdur"; [iExact "Hdur"|]. iApply "IH".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE WIRE THREAD.  [dev_seip d h] is [plic_eip (dplic d) h], read    *)
  (*  off the PHYSICAL device state the lifting rule hands over, so this   *)
  (*  proof needs NO agreement against [plic_frag] and therefore never     *)
  (*  opens [plicN] at all -- the old proof opened the device invariant     *)
  (*  here only to close it again.  [plic_inv] is still taken, to keep the  *)
  (*  three loops' interfaces uniform and to record that the wire's value   *)
  (*  is the PLIC's.                                                       *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_plic_loop Φ :
    gen_cert -∗ plic_inv -∗ wire_inv -∗
    WP (PlicLoop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hcert #Hpinv #Hwinv".
    iLöb as "IH".
    iApply (wp_plic_step with "Hcert").
    iIntros (gr m d) "(Hgr & Hmem & Hdev)".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iNext. iIntros (gr' Hstep).
    iMod "Hmask" as "_".
    destruct Hstep as [c].
    (* the PLIC drives hart [c]'s sig_seip wire, borrowed from [wire_inv] *)
    iInv "Hwinv" as ">Hwbody" "Hwclose".
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
  Qed.
End DevLoops.
